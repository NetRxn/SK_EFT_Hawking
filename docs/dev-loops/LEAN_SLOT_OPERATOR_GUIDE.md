# Lean-slot operator guide

[ADR-008](../adrs/ADR-008-shared-lean-slot-control-plane.md) defines the normative design.
This guide is the operator's copy for the shared three-slot control plane, which **Codex and
Claude Code both use**. A slot may be driven by either client, never by two writers at once.

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

A shortfall is reported with the exact command to run, e.g. on macOS:

```bash
sudo sysctl -w kern.maxvnodes=786432
```

### Why this needs a boot-time job, not just the command above

`sysctl -w` writes to the **running kernel only**. It does not persist: the next reboot
silently restores the platform default, which was adequate for one slot and is not for three.
Nothing warns you — the swarm simply starts failing at a moment you did not choose.

⚠️ **`/etc/sysctl.conf` is not reliably honored on modern macOS.** Do not use it. The
supported mechanism is a `LaunchDaemon`, which runs as root at boot:

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
    <string>kern.maxvnodes=786432</string>
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
every host.** The requirement is declared data, not code, in `config/lean-slots.public.json`:

```json
"host_limits": [
  {"platform": "Darwin", "sysctl": "kern.maxvnodes", "minimum": 786432,
   "why": "...", "remedy": "sudo sysctl -w kern.maxvnodes=786432"}
]
```

How it adapts:

| situation | behavior |
|---|---|
| Platform has **no** declared entry (e.g. a Linux VM) | **Passes.** Linux has no vnode ceiling; a macOS requirement must never fail a clone elsewhere. |
| Knob is declared but the running kernel does not expose it | **Passes.** Absent is not misconfigured. |
| You want a different value | Edit `minimum`. The remedy command is rederived from it, so the two cannot drift — a hand-written `remedy` naming a stale value is discarded rather than printed. |
| You want no host check at all | Export `LEAN_SLOT_SKIP_HOST_LIMITS=1`. Opting a machine out needs **no repository diff**. |

Entries are keyed by `platform.system()` (`Darwin`, `Linux`, …), so a Linux host is configured
by adding a `Linux` entry. There the analogous pressure is on file descriptors rather than
vnodes — `fs.file-max` system-wide, plus the per-process `RLIMIT_NOFILE` that `ulimit -n`
reports, which a LaunchDaemon equivalent (a `systemd` unit or `/etc/security/limits.d` entry)
would set. Measure on the target host before declaring a number; do not copy this one.

Scale the value with **concurrent slots**, not with repository size: the load is per live Lean
server, and the semaphore caps that at three.

---

## One-time activation

From the primary `SK_EFT_Hawking` checkout — **always the primary**, never a worktree.
`slotctl` resolves its inventory, state root and lease directory from the current working
directory, so running it inside a slot addresses a different control plane and reports every
slot `FREE`.

```bash
uv run python scripts/slotctl.py config render --scope both          # Codex
uv run python scripts/slotctl.py config render --client claude       # Claude
uv run python scripts/slotctl.py supervisor start
uv run python scripts/slotctl.py doctor
```

The active workstation inventory uses `server.client_auth = "trusted-local"`: the MCP front
doors bind only to `127.0.0.1`, so a normal launch of either client needs no token or shell
bootstrap. Lease state, repository/worktree/endpoint identity, the no-build policy, and the
global backend limit remain enforced.

**Claude** entries are written into the workspace `.mcp.json` as a named block: the renderer
adds `skeft_wt{1,2,3}` (HTTP), removes the legacy per-slot stdio servers, and leaves every
other project's servers untouched in their original order. The pre-activation block is
snapshotted **once** and restored by `config render --client claude --rollback`, which is the
supported way back to the legacy stdio path.

**Codex** configuration is gitignored and generated in this repository and at the workspace
root. `config render` refuses to overwrite a locally modified generated file unless `--force`
is explicit.

Bearer authentication is banked for a future shared-user deployment. To use it, select
`server.client_auth = "bearer"` in that deployment's inventory, render configuration, and run
`eval "$(uv run python scripts/slotctl.py session env --client codex --rotate-token)"` in the
launching shell. Token rotation is invalid in trusted-local mode and must never occur while
leases are active.

Changing `server.client_auth` — **or editing anything under `scripts/lean_slots/`** — requires
a front-door restart so the proxies load the new code: `supervisor stop`, then
`supervisor start`. The supervisor fingerprints the loaded proxy implementation and inventory,
so a plain `supervisor start` fails closed rather than silently reusing stale policy.

⚠️ A proxy running stale code is reported by `doctor` as `proxy=False` **while its port is
still open and serving**. If a `prepare` fails with an unhealthy proxy, restart the supervisor
before investigating anything else.

**Restart the client after the first render** so the endpoints attach — MCP servers are
attached at session start, and for Claude the plugin cache is a content-hashed snapshot, so a
restart is what activates both.

---

## Per-task orchestrator flow

Identical for both clients; only `--client` differs. The endpoints are **lease-gated**: every
tool call is rejected unless the slot holds an `ACTIVE` lease whose `client` matches the one in
the endpoint URL. A dispatch without a lease yields a connected server whose every call fails
closed.

```bash
# Acquire and prepare IMMEDIATELY before dispatching this slot's worker, per task,
# never as a batch up front — a slot prepared early goes stale when main advances.
uv run python scripts/slotctl.py acquire --slot 2 --client claude --base-ref main
uv run python scripts/slotctl.py prepare --slot 2

# Dispatch the worker at mcp__skeft_wt2__* (Claude) or lean_wt2_worker (Codex),
# with its exact absolute worktree path and one bounded task.
# A worker running longer than the lease timeout (900s in the shipped inventory)
# needs its heartbeat refreshed by the LEAD — workers do not touch the controller:
uv run python scripts/slotctl.py heartbeat --slot 2

# After the worker commits and reports success:
uv run python scripts/slotctl.py ready  --slot 2
uv run python scripts/slotctl.py absorb --slot 2
```

`prepare` resets the worktree to the base and installs a `.lake` matching the published
successful-build epoch — a stronger freshness predicate than the HEAD stamp it replaced.

`absorb` is the serialized integration path: ancestry audit, orchestrator-only rebase when
required, fast-forward, authoritative build, epoch publication, cache rewarm, and release. It
never cherry-picks, and it quarantines rather than discards work on any unexpected state.

For a no-change task, use `release` after confirming the worktree is clean with no unabsorbed
commits:

```bash
uv run python scripts/slotctl.py release --slot 2
```

An explicitly resolved quarantine may also be released by its owning session once the worktree
is clean and its HEAD is contained in the base. The controller never resets or deletes
quarantined work.

### Spawning a Codex worker from a Claude lead

The lead acquires the lease with `--client codex`, then launches the session. `codex exec` reads
`.codex/config.toml` from the working directory, so it picks up the rendered endpoints:

```bash
codex exec --skip-git-repo-check --sandbox read-only "$(cat <<'PROMPT'
<the task>
PROMPT
)" < /dev/null > "$SCRATCH/codex_<slug>.md" 2>&1 &
```

⚠️ **`< /dev/null` is required** — without it `codex exec` blocks on stdin for roughly 90 minutes.
Drop `--sandbox read-only` only when the worker must actually commit.

A raw transcript is 1–2 MB and must never be read into the lead's context; harvest the deliverable
mechanically with `scripts/codex_dossier.py harvest`, per the codex-dossier protocol.

The endpoints are identical for both clients — only `?client=` and the lease's `client` field
differ. A Codex worker on a slot leased to Claude is refused at dispatch, and vice versa.

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
from `LEAN_SLOT_OWNER_SESSION` if set, else the client's own session variable, else a verified
parent PID. Reclaiming a stale session-owned lease requires `--confirm-owner-gone` after the
operator verifies that session has ended, and the heartbeat threshold still applies.

⚠️ **A slot number is workspace-wide capacity, not per-client.** A slot held by another
repository against the same number — including a downstream/private overlay — is unavailable
here, and the public controller refuses to reclaim it on repository-role mismatch. That is
correct: quarantine is fail-closed by design. Capacity returns when its owner resolves it.

The shared runtime state defaults to `<workspace>/.lean-slots/` and may be overridden for tests
or alternate layouts with `LEAN_SLOT_STATE_DIR`.
