# Lean-slot operator guide

[ADR-008](../adrs/ADR-008-shared-lean-slot-control-plane.md) defines the normative lifecycle design.
[ADR-018](../adrs/ADR-018-chat-client-for-shared-lean-slots.md) makes admitted client identity
versioned inventory data. This guide is the operator's copy for the shared three-slot control plane.
The shipped public inventory admits **Codex, Claude Code, and Chat**; a private/downstream inventory
may admit a narrower set. A slot may be driven by one admitted client at a time, never by two writers.

---

## Host requirements — read this before a full swarm

A slot swarm is bounded by kernel resources, not only by the heavy-backend semaphore. Each
Lean server memory-maps thousands of `.olean` files across Mathlib and its dependencies, and a
full swarm does that in three slots simultaneously. Exhausting the host's file/vnode table
produces `ENFILE` ("Too many open files in system"), which halts unrelated work and reads
exactly like a broken toolchain — the failure this control plane's lifecycle rules exist to
prevent.

`slotctl doctor` reports the declared limits for the platform it is running on:

```bash
uv run python scripts/slotctl.py doctor
```

A shortfall is reported with the exact command to run. The current public inventory's macOS
floor is `1048576`; use the command printed by `doctor` rather than copying an old number from
this guide.

### Why this needs a boot-time job, not just the command above

`sysctl -w` writes to the **running kernel only**. It does not persist: the next reboot
silently restores the platform default, which was adequate for one slot and is not for three.
Nothing warns you — the swarm simply starts failing at a moment you did not choose.

⚠️ **`/etc/sysctl.conf` is not reliably honored on modern macOS.** Do not use it. The
supported mechanism is a `LaunchDaemon`, which runs as root at boot. Generate its value from
the current inventory/`doctor` output rather than preserving a stale literal. For example:

```bash
sudo tee /Library/LaunchDaemons/local.leanslots.maxvnodes.plist >/dev/null <<'PLIST'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>Label</key><string>local.leanslots.maxvnodes</string>
  <key>ProgramArguments</key>
  <array>
    <string>/usr/sbin/sysctl</string>
    <string>-w</string>
    <string>kern.maxvnodes=1048576</string>
  </array>
  <key>RunAtLoad</key><true/>
</dict>
</plist>
PLIST
```

Then set ownership and load it:

```bash
sudo chown root:wheel /Library/LaunchDaemons/local.leanslots.maxvnodes.plist && sudo chmod 644 /Library/LaunchDaemons/local.leanslots.maxvnodes.plist && sudo launchctl load -w /Library/LaunchDaemons/local.leanslots.maxvnodes.plist
```

**Why the ownership and mode matter.** `launchd` runs daemons in `/Library/LaunchDaemons` as
**root**. It therefore refuses to load a plist that any non-root user could modify — otherwise
an unprivileged edit would become root-privileged execution at boot. `root:wheel` with mode
`644` means only root can write it, while anyone may read it. A plist owned by your user
account, or group/world-writable, is rejected, and the usual symptom is that it silently never
runs. `-w` marks it enabled persistently.

Verify after the next reboot:

```bash
sysctl -n kern.maxvnodes
```

To remove it: `sudo launchctl unload -w /Library/LaunchDaemons/local.leanslots.maxvnodes.plist`
and delete the file.

### Other machines, other platforms

**This is a public repository, and the value above is right for one workstation, not for
every host.** The requirement is declared data, not code, in `config/lean-slots.public.json`.

How it adapts:

| situation | behavior |
|---|---|
| Platform has **no** declared entry (e.g. a Linux VM) | **Passes.** A macOS requirement must never fail a clone elsewhere. |
| Knob is declared but the running kernel does not expose it | **Passes.** Absent is not misconfigured. |
| You want a different value | Edit `minimum`. The remedy command is rederived from it, so the two cannot drift — a hand-written `remedy` naming a stale value is discarded rather than printed. |
| You want no host check at all | Export `LEAN_SLOT_SKIP_HOST_LIMITS=1`. Opting a machine out needs **no repository diff**. |

Entries are keyed by `platform.system()` (`Darwin`, `Linux`, …). Measure on the target host
before declaring a number; do not copy the reference workstation's value blindly.

Scale the value with **concurrent slots**, not with repository size: the load is per live Lean
server, and the semaphore caps that at three.

---

## One-time activation

From the primary `SK_EFT_Hawking` checkout — **always the primary**, never a worktree.
`slotctl` resolves its inventory, state root and lease directory from the current working
directory, so running it inside a slot addresses a different control plane and reports every
slot `FREE`.

```bash
uv run python scripts/slotctl.py config render --scope both           # Codex renderer
uv run python scripts/slotctl.py config render --client claude        # Claude renderer
uv run python scripts/slotctl.py supervisor start
uv run python scripts/slotctl.py doctor
```

The active workstation inventory uses `server.client_auth = "trusted-local"`: the MCP front
doors bind only to `127.0.0.1`, so an admitted client needs no token merely to connect.
Lease state, repository/worktree/endpoint identity, the no-build policy, and the global backend
limit remain enforced.

`server.allowed_clients` is the **lease/dispatch admission roster**. In the public inventory it
is currently `["codex", "claude", "chat"]`. A schema-1 inventory that predates this field has
the exact compatibility meaning `{codex, claude}`; missing data never implies Chat admission.
The controller and proxy enforce this same roster, so a caller cannot bypass admission by
skipping CLI parsing.

**Renderer support is a different capability from admission.** This repository has concrete
Codex and Claude configuration renderers. It intentionally has no Chat renderer in ADR-018.
`slotctl config render --client chat` must fail; the Chat bridge derives an admitted slot's
HTTP URL from the inventory instead of generating a third workspace client configuration.

**Claude** entries are written into the workspace `.mcp.json` as a named block: the renderer
adds `skeft_wt{1,2,3}` (HTTP), removes the legacy per-slot stdio servers, and leaves every
other project's servers untouched in their original order. The pre-activation block is
snapshotted **once** and restored by `config render --client claude --rollback`, which is the
supported way back to the legacy stdio path.

**Codex** configuration is gitignored and generated in this repository and at the workspace
root. `config render` refuses to overwrite a locally modified generated file unless `--force`
is explicit.

Bearer authentication is banked for a future shared-user deployment. To use it, select
`server.client_auth = "bearer"` in that deployment's inventory and obtain the selected admitted
client's environment through `slotctl session env --client <client>`. Token rotation is invalid
in trusted-local mode and must never occur while leases are active.

Changing the admission roster, `server.client_auth`, **or editing anything under
`scripts/lean_slots/`** requires a front-door restart so the proxies load the new policy:
`supervisor stop`, then `supervisor start`. A versioned file edit is not instant process
revocation. The supervisor fingerprints loaded implementation/inventory so a stale proxy is
reported rather than silently called current.

⚠️ A proxy running stale code is reported by `doctor` as stale **while its port is still open
and serving**. Restart the supervisor before treating a roster/policy edit as effective.

**Restart a rendered client after the first render** so its endpoint configuration attaches.
The direct Chat bridge does not depend on a Chat renderer and therefore does not acquire this
configuration-restart requirement merely by becoming an admitted lease client.

---

## Per-task orchestrator flow

✅ **The lease lifecycle is drivable from inside a live session. No per-wave restart.** Acquire,
prepare, dispatch, absorb and release all work against a session that attached while the slot was
idle — which means an admitted orchestration session can run the whole thing unattended.

Until 2026-08-15 the front door answered `initialize` without minting an `Mcp-Session-Id`, so a
client that attached to an idle slot held no session any later backend had issued. ADR-008 S-Q
fixed the proxy; do not reinstate the old "prepare before client start" workaround.

The one thing that still needs a rendered-client restart is changing *which configured endpoints
exist*. That is a configuration change, not a per-wave step.

⚠️ **The port trap.** A client config/bridge points at the **proxy** (`127.0.0.1:876N`); the
lean-lsp backend listens on `1876N`. Probing the backend directly can look like a lease/auth
failure while merely bypassing the front door. Diagnose against the proxy port and include the
`?client=<name>` query hint. Under `trusted-local` that nonsecret hint is the routing identity,
not the lease authority.

The flow is identical for all admitted lease clients; product-specific launch mechanics differ.
Every nondiscovery tool call is rejected unless the slot holds an `ACTIVE` lease whose `client`
matches the endpoint identity.

```bash
# Acquire and prepare IMMEDIATELY before dispatching this slot's worker/task,
# never as a batch up front — a slot prepared early goes stale when the base advances.
uv run python scripts/slotctl.py acquire --slot 2 --client claude --base-ref main
uv run python scripts/slotctl.py prepare --slot 2

# Dispatch through the admitted endpoint with exact worktree/task scope.
# A task running longer than the lease timeout needs the same OWNER session to heartbeat:
uv run python scripts/slotctl.py heartbeat --slot 2

# After committed work is independently ready for project integration:
uv run python scripts/slotctl.py ready  --slot 2
uv run python scripts/slotctl.py absorb --slot 2
```

`LEAN_SLOT_OWNER_SESSION` is the product-neutral explicit owner identity. The same opaque owner
session must be supplied on acquire/prepare/heartbeat/ready/release and, when separately
authorized, absorb. **`ready` does not transfer ownership.** Admitting `client=chat` therefore
does not grant Chat integration authority; the caller/control plane must carry a separately
reviewed same-owner integration continuation before a real mutating Chat task can be integrated.

`prepare` resets the worktree to the base and installs a `.lake` matching the published
successful-build epoch.

`absorb` is the serialized integration path: ancestry audit, orchestrator-only rebase when
required, fast-forward, authoritative build, epoch publication, cache rewarm, and release. It
never cherry-picks, and it quarantines rather than discards work on any unexpected state.

For a no-change task, use `release` after confirming the worktree is clean with no unabsorbed
commits:

```bash
uv run python scripts/slotctl.py release --slot 2
```

An explicitly resolved quarantine may also be released by its owning session once the worktree
is clean and its HEAD is contained in the integration/base refs. The controller never resets or
deletes quarantined work.

### Spawning a Codex worker from a Claude lead

The lead acquires the lease with `--client codex`, then launches the session. `codex exec` reads
`.codex/config.toml` from the working directory, so it picks up the rendered endpoints:

```bash
codex exec --skip-git-repo-check --sandbox read-only "$(cat <<'PROMPT'
<the task>
PROMPT
)" < /dev/null > "$SCRATCH/codex_<slug>.md" 2>&1 &
```

⚠️ **`< /dev/null` is required** — without it `codex exec` blocks on stdin.
Drop `--sandbox read-only` only when the worker must actually commit and that mutation is
already admitted.

A raw transcript is large and must not be read wholesale into the lead context; harvest the
project-native deliverable mechanically.

The slot endpoints are shared. A request identifying as Chat, Codex, or Claude against a lease
held by a different client is refused at dispatch.

---

## Client removal / rollback

Removing an admitted client is **quiescent and restart-bound**, not a file-edit revocation.
Use this canonical sequence from ADR-018:

1. Run the read-only prospective check while the client is still admitted:

   ```bash
   uv run python scripts/slotctl.py session removal-preflight --client chat
   ```

   It fails/red if any live lease records that client. The check does not mutate, reclaim,
   quarantine, release, or invalidate a lease; the legitimate owner retains normal cleanup.
2. Quiesce the client completely. No live lease for that client may remain.
3. **Bearer mode only:** revoke the client's credential while it is still admitted:

   ```bash
   uv run python scripts/slotctl.py session revoke-token --client chat
   ```

   This deletes only the project-owned `Inventory.client_token_path(client)`, is idempotent,
   emits no token, and refuses a live client lease. Trusted-local mode has no credential step.
4. Edit `server.allowed_clients` in the versioned inventory.
5. Restart front doors: `slotctl supervisor stop` then `slotctl supervisor start`.
6. Run `slotctl doctor` and prove controller/proxy negative controls deny the removed identity.

If an operator creates the invalid intermediate state "roster no longer admits client C while a
live lease still records C", `doctor` reports the lease/admission mismatch red. It does **not**
turn that report into revocation or strand owner cleanup.

In bearer mode, later re-admission must create/use a fresh token. A credential removed during
the procedure above must never silently become valid again.

---

## Recovery and diagnostics

```bash
uv run python scripts/slotctl.py status
uv run python scripts/slotctl.py status --json
uv run python scripts/slotctl.py doctor
uv run python scripts/slotctl.py reclaim --slot 2
uv run python scripts/slotctl.py supervisor status
```

Heartbeat expiry or a dead owner never authorizes deleting work. Dirty files or unabsorbed
commits move the slot to `QUARANTINED`; resolve them deliberately in the named worktree and
rerun diagnostics.

Leases are owned by the driving **session**, not by the shell that ran `acquire` — resolved
from `LEAN_SLOT_OWNER_SESSION` if set, else a supported client's native session variable, else
a verified parent PID. Reclaiming a stale session-owned lease requires
`--confirm-owner-gone` only after the operator verifies the driving session has ended, and the
heartbeat threshold still applies.

⚠️ **A slot number is workspace-wide capacity, not per-client.** A slot held by another
repository against the same number — including a downstream/private overlay — is unavailable
here, and the public controller refuses to reclaim it on repository-role mismatch. Capacity
returns when its owner resolves it.

The shared runtime state defaults to `<workspace>/.lean-slots/` and may be overridden for tests
or alternate layouts with `LEAN_SLOT_STATE_DIR`.
