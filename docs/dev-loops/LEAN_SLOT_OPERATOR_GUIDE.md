# Lean-slot operator guide

[ADR-008](../adrs/ADR-008-shared-lean-slot-control-plane.md) defines the normative design.
This guide is the operator's copy for the shared three-slot control plane, which **Codex and
Claude Code both use**. A slot may be driven by either client, never by two writers at once.

> **Observation and live admission:** The [lifecycle amendment](../adrs/ADR-008-shared-lean-slot-control-plane.md#2026-10-11-lifecycle-observation-amendment)
> is implemented and independently accepted for bounded source/test/evidence scope.
> ROOT canonical evidence records source integration and current project-gate outcomes;
> source review does not certify loaded runtime. `FREE` describes the lease only, and
> registry counts alone do not establish capacity. Keep unknown resources reserved
> and caches untouched. See the recovery section for existing API scope and separate
> ownership, quiescence, client-drain and live-loading gates.

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
sudo sysctl -w kern.maxvnodes=1048576
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

**The value above is the shipped reference-host floor, not a measurement of a current
machine.** Follow the selected inventory's doctor remedy and measure the target before
declaring its requirement. The requirement is data in `config/lean-slots.public.json`:

```json
"host_limits": [
  {"platform": "Darwin", "sysctl": "kern.maxvnodes", "minimum": 1048576,
   "why": "...", "remedy": "sudo sysctl -w kern.maxvnodes=1048576"}
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
`Inventory.load` selects an explicit `--inventory` path first, then `LEAN_SLOT_CONFIG`,
then the inventory beside the loaded controller module. The chosen config resolves its
repository root relative to the config location and derives the workspace/state root;
`LEAN_SLOT_STATE_DIR` can override that state root. CWD alone does not select authority.
A controller module or copied config loaded from a worktree can resolve a different
domain, so run the primary controller with its verified canonical inventory. A displayed
`FREE` state is lease evidence for that selected domain, not process absence.

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

A proxy uses changed `server.client_auth` or `scripts/lean_slots/` code only after a
verified front-door reload. `supervisor stop` followed by `supervisor start` is global:
ROOT must coordinate a window with every active owner and client request drained,
actual process ownership known and capable capacity/quiescence evidence sufficient
for safe operations. Existing root internal number APIs permit a conditional known
owned proxy replacement only under the gates in the observation section below.
This adds no targeted CLI verb. A source edit or configuration render does not reload
running proxies, and source integration alone does not authorize a reload.
The supervisor fingerprints the loaded implementation and inventory; a plain
`supervisor start` refuses stale reuse rather than silently activating the new policy.

⚠️ An unhealthy proxy observation does not establish stale code as its cause. If `prepare`
fails with an unhealthy proxy, first perform bounded authorized read-only diagnosis of
process identity, registration, port observations and physical-slot capacity. Distinguish a
verified stale fingerprint from unavailable observations or unknown current ownership.
Keep unknown or unobservable processes untouched and their physical numbers reserved;
do not blindly stop/start the supervisor or reset/replace a project cache. Even a verified
stale fingerprint permits a global reload only in the root-coordinated safe window above.
The observation correction below is implemented and accepted for bounded source scope.
ROOT canonical evidence records integration; loaded-runtime admission is separate and
unverified.

**Restart the client after the first render** so the endpoints attach — MCP servers are
attached at session start, and for Claude the plugin cache is a content-hashed snapshot, so a
restart is what activates both.

---

## Per-task orchestrator flow

✅ **The normal healthy lease lifecycle needs no routine client restart.** Acquire, prepare,
dispatch, absorb and release can use one live session that attached while the slot was idle,
provided the runtime is healthy/current and the lease, ownership and capacity gates hold.
This supports unattended normal work; it does not remove the coordinated reload window
for code/auth changes or authorize a restart when observations are unavailable. Follow the
read-only diagnosis and root-coordinated window requirements above when the runtime fails.

This was not always true, and the history is worth one line because the fix generalises. Until
2026-08-15 the front door answered `initialize` without minting an `Mcp-Session-Id`, so a client
that attached to an idle slot held no session any later backend had issued, and every call
returned `MCP error -32602` for the life of that session. The guide used to tell you to acquire
and prepare *before* starting the client. That was a workaround for our own defect written up as
an operating rule; [ADR-008 S-Q](../adrs/ADR-008-shared-lean-slot-control-plane.md) fixed the
proxy instead, and the rule is retired. **Do not reinstate it.**

The one thing that still needs a client restart is changing *which endpoints exist* — adding or
removing a slot in `.mcp.json` via `config render`. That is a configuration change, not a
per-wave step.

⚠️ **The port trap, which produced two independent wrong diagnoses in one session.** The client
config points at the **proxy** (`127.0.0.1:876N`); the lean-lsp backend listens on `1876N`.
Probing the backend directly returns `401 invalid_token`, which reads like a lease rejection and
is only the backend refusing a direct connection. Diagnose against the proxy port, and include
the `?client=<name>` query hint — under `trusted-local` auth that hint *is* the client identity,
so a probe without it is unauthenticated by construction.

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


## Observation failures and residual resources

The implemented, independently source-reviewed controller rejects `--slot` with
`supervisor start`, `stop` and `status` before inventory loading or action. These verbs
remain global. `supervisor probe --slot N` requires and uses that slot. No targeted
start/stop/status CLI is introduced. ROOT canonical evidence records source integration;
a running older proxy does not acquire this policy from changed source. Live loading
requires separate measured admission.

`FREE` means the lease record was removed after the normal clean/containment checks.
It does not mean the backend has stopped. Current nonfatal stop warnings must remain
visible. “Down”, a missing process JSON or the registered global count is not proof
of host absence when observation is denied. Preserve originals and source bytes;
never delete process registration, fabricate a signature, adopt/signal an unknown
PID, bypass the supervisor, force a dirty reset or create a fourth backend.

If observation is unavailable or a backend listener is unknown, keep its physical
number reserved and its project cache untouched. Root may collect bounded authorized
read-only process/listener identity evidence and inspect existing public logs. This
is diagnosis, not process-management authority. Repeat start/release/prepare cycles
and an all-slot restart are not a substitute for reliable observation. A global
code/config restart described earlier in this guide requires active owners to drain
and root to coordinate the window; a fresh source file does not mean a live proxy or
backend reloaded it.

For normal integration, acquire with the **actual branch name currently checked out
in primary** and a matching published epoch. Current `absorb` compares that branch
name with the lease's literal `base_ref`; a commit SHA may resolve for preparation
but is not a supported branch-name match for absorption. There is no retarget verb.
On mismatch, preserve exact work through the canonical recovery process; do not
spoof the primary branch or edit the lease. Fresh leases/slots require fresh current
runtime and integration evidence even when the preserved source bytes are identical.

The [LO-1–LO-6 design](../superpowers/specs/2026-10-11-lean-lifecycle-observation-design.md),
[plan](../superpowers/plans/2026-10-11-lean-lifecycle-observation.md) and
[native-domain design](../superpowers/specs/2026-10-12-lean-native-domain-census-design.md)
describe the implemented correction and its bounded source review. Capable Git identity
excludes only proven linked copies of a matching canonical primary domain; genuine
conflicts and same-primary aliases remain. Complete process ancestry traverses generic
intermediates without merging independent services under a nonproject manager. Stored
generic/reparented descendant reservations survive independently. Denied or incomplete
observations remain unavailable evidence and block unsafe admission.

A conditional known-owned proxy replacement requires target-slot then lifecycle lock,
reliable FREE and a complete capable current census, with both-role backend/project/
retained-descendant absence. Under the held lifecycle lock use existing unlocked
number internals; public wrappers would reacquire that nonreentrant lock. Freeze ROOT
dispatch/probes and account for actual completed owned requests. Recheck exact proxy
identity, listener and all-state TCP, native threads and state-directory membership
before and after the eligible operation. Unknown numbers remain reserved and untouched.

An idle session, closed backend endpoint, FREE lease or a socket-operation timeout
does not prove handler completion. TCP/thread samples are supplementary observations
at their timestamps: an outside HTTP request can race them, and daemon handler threads
are not joined by server close. Unaccounted activity blocks replacement. Replacing a
proxy loses its in-memory session map; S-Q backend rotation under a persistent proxy
does not guarantee active-client continuity through proxy replacement. Loaded-source
fingerprints, initialize/list/unleased denial, matching lease dispatch and subsequent
release/reconnect/recovery and paired epoch validation require separate measured gates.

Existing mathematical acceptance and broader project gates remain separate. Original
failed gates remain unwaived; their dated counts are historical evidence, not a standing
current-failure census. Bounded source review alone does not certify primary integration or live admission.
