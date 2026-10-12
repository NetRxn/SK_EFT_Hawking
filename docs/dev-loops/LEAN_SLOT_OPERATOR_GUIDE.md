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
The supervisor compares recorded launch-source/configuration inputs with current
expected inputs; this does not attest process-memory code. Earlier enumeration
was inventory-local and did not fully cover externally imported shared code. The
accepted SF implementation below covers that source contract and is present in the
primary checkout. Current project gates and separately measured native loading
remain open. A plain
`supervisor start` refuses detected stale reuse; an unchanged incomplete digest is
not proof that imported shared code is current.

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
never delete process registration, fabricate a signature, bypass the supervisor,
force a dirty reset or create a fourth backend. Ordinary lifecycle paths cannot
adopt/signal an unknown PID. The explicit owner-authorized stop-only exception below
requires its own complete fresh gates and does not authorize healthy reuse.

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
does not guarantee active-client continuity through proxy replacement. Expected and
recorded source fingerprints, separate loaded-code evidence, initialize/list/unleased
denial, matching lease dispatch and subsequent
release/reconnect/recovery and paired epoch validation require separate measured gates.

Existing mathematical acceptance and broader project gates remain separate. Original
failed gates remain unwaived; their dated counts are historical evidence, not a standing
current-failure census. Bounded source review alone does not certify primary integration or live admission.


## Shared-runtime fingerprint coverage

**WHOLE SOURCE IMPLEMENTATION ACCEPTED / SOURCE FINDINGS CLOSED / CURRENT PROJECT GATES AND NATIVE ADMISSION PENDING.** The
[SF design](../superpowers/specs/2026-10-12-shared-runtime-source-fingerprint-design.md)
and [plan](../superpowers/plans/2026-10-12-shared-runtime-source-fingerprint.md)
extend the existing fingerprint to mandatory actual imported package source,
launcher-route coherence and separate deterministic local/shared namespaces.
Missing, denied, incoherent, dynamic/unsupported or observed-drifting source is
unavailable. A launcher-defined shared-path override is accepted only when its
actual supported complete entry template and capable selected package agree with
loaded module origins; the environment value alone is not authority. Transparent
selected-cli fail-fast guards and source-defined default-inventory setdefault are
covered by the accepted bounded grammar, with exact aliases/order/captured effects.
Only literal or bounded selected-Path f-string guard messages are supported; dynamic
expressions and extra statements remain unsupported. Validation and actual Popen
must use one captured environment, preserving explicit inventory precedence and the
applicable backend-token addition; a later external selection change must not be
silently recaptured for launch. A bounded expanduser().resolve() template is supported
only for genuine recognized Path sources: bare tilde/tilde-slash consumes the same
valid capable captured HOME passed to Popen; absolute non-tilde no-op is independent
of HOME. Named-user, missing/invalid/unavailable home or unsupported transforms
refuse. No ambient user/home fallback, new environment API or child probe is added.
Actual home/path capability and alias/source reobservation remain required; no
home string or source digest grants process authority.

The admitted source contract covers mandatory imported shared source; do not use an
unchanged inventory-local legacy digest to certify that code. A source digest
describes expected/recorded launch inputs rather than running process memory or
completed client requests. No old process record may be
rewritten to make it current. This adds no lifecycle command and permits no reload,
unknown-PID adoption or signals. Follow the existing ownership/quiescence/drain and
separate loaded-code/MCP/lease/reconnect/paired-epoch gates above.


Supported parent indices must exist on the actual recognized Path; missing parents
give typed unavailable evidence before pending/Popen. Relevant loaded qualified
origins, including same-source aliases, are capped at 1024 before native observations.
The complete module-dictionary discovery cost remains proportional to that dictionary.
The accepted source implementation and its native assertion controls cover these
bounds. Current project gates and separately measured native admission remain open;
no process record rewrite, adoption or signal follows from source acceptance.


Supported source string/Path conversions and selected source-defined fallbacks retain
same-operand transform provenance. Aliases, conversions, literal joins, expansion and
resolution retain cumulative parent operations across the complete recipe, capped at
four; parents[index] consumes index + 1. Parent/join-derived operands can use their
own admitted expansion while retaining that cumulative budget. Inactive defaults and
selector fallbacks validate eagerly. These rules require typed source refusal before
pending/Popen with existing witnesses/records/reservations preserved. The complete source implementation, ROOT native assertion mutation/restoration
controls and independent whole source review are accepted, and the reviewed files
are present in the primary checkout. Current project gates, normal commit and
separately measured native admission remain open. Historical originals and
qualifying/invalid evidence remain retained.


## Owned-shutdown and orphan-stop procedure

**Scoped source and native recovery accepted (2026-10-12).**
The internal stop-only API and shutdown correction at `6db2cde` passed independent
whole-source review, 391 primary runner regressions and 26 meaningful mutation/restore
controls. Public slots 1/2/3 passed real diagnostics and warning-free release; 1/2
also passed fresh reconnect cycles. Canonical public and paired audits found FREE
leases, current front doors, absent backends and complete capacity without conflicts.
See the [re-review](../../papers/AutomatedReviews/2026-10-12-lean-runner-recovery/review-r4.md)
and [native admission](../../papers/AutomatedReviews/2026-10-12-lean-runner-recovery/native-admission-r1.json).
Historical candidate checkpoints below are retained; broader gates remain open.
There is no new CLI command.
[ADR-008 RR-1–RR-4](../adrs/ADR-008-shared-lean-slot-control-plane.md#owned-shutdown-and-operator-authorized-orphan-recovery)
and the [complete design](../superpowers/specs/2026-10-12-owned-lean-shutdown-and-orphan-recovery-design.md)
govern this extension. Whole-design review and ROOT intake accepted the contract.
ROOT must obtain bounded source acceptance before using it on native resources.
An existing explicit operator authorization suffices within its recorded scope;
routine recovery does not require repeatedly asking for the same permission.

A retained native zombie is still a present process. Shutdown may use a separate
native-state observation to recognize its terminal state while keeping generic
identity mismatch visible and its original signature intact. The child is never
signalled. Only independently exact live owned ancestors may receive the existing
bounded `SIGTERM` sequence, ordered by ancestry. Legacy `lstart` is coarse birth
evidence, not a race-free generation guarantee; missing native state, a bare
`<defunct>` command, a lost root, reparenting or ambiguous identity cannot justify
signalling. Require every retained PID actually absent and all normal quiescence
guards satisfied before removing registration. Retain timeout/refusal evidence.

For an unregistered backend, the internal API is
`Controller.recover_orphan_backend_stop(...)`; it has no CLI spelling. Keep
`supervisor start`, `stop` and `status` global, and `probe --slot N` unchanged.
The canonical primary controller and matching repository interpreter remain
mandatory. Both authority objects include `inventory_domain`, the existing canonical
`Supervisor._inventory_domain` digest; a same-path domain change invalidates approval
and retry. The reserved record retains bounded `admission_observations` and
`error_observations`, separately from original identities and signal-delivery receipts.
ROOT performs this sequence only after source acceptance:

1. Bind existing operator approval to the exact slot/domain, expected full root
   and family signatures and driving session, with separate `backend_target` and
   actual `lease_owner` identities. Bind both canonical inventories/roles/worktrees,
   shared state root/physical number and original dependency pin. Preserve original
   witnesses. Freeze
   dispatch/probes and account for completed requests; absent established TCP alone
   does not prove handler completion. Inspect clean work and containment using
   existing controller checks, preserving all quarantine/source evidence.
2. Acquire target-slot then the single lifecycle lock. Reobserve the configured
   project, unique complete family, exact expected identities, registry absence,
   unique correct listener, all-state TCP and capacity/domain evidence. Refuse an
   ACTIVE or other transitional lease. Allow only FREE or this session's matching
   QUARANTINED lease, with clean contained work. Resolve a different-role owner only
   through its genuine declared pairing to the target, same shared state root and
   physical number. Use that actual owner's unchanged `_lease_for_command` and
   work/containment checks; verify clean paired target path and recorded dependency
   SHA without replacing the pin with a later primary HEAD. Backend family/listener/
   record authority stays with the target. A legitimate paired quarantine alone is
   not a conflict; arbitrary foreign roles and opposing active backends are refused.
   FREE uses target containment with no synthesized owner. Opposing ownership, ambiguous roots,
   foreign listeners, unavailable evidence and any drift block the operation.
3. Before the first signal, exclusively publish and sync the existing process-path
   reservation marked `operator_stop_only`, phase `uncertain_residual`. This is
   explicit stop authority, never a reconstructed launch record: no runtime
   fingerprint, token or `running` claim. Stop only the guarded family. Preserve
   the durable record on interruption or failure; do not erase or restamp it.
4. A deliberate retry uses the same API, an exact expected residual SHA-256 and
   matching original target/lease-owner authorities and owner/authorization scope.
   Recheck pairing, both worktrees, shared state root/number and unchanged dependency
   pin. Repeat all fresh gates and preserve original signatures. Managed, foreign,
   unknown or unmatched existing records
   are refusals. Ordinary start/prepare/status cannot convert this record into
   healthy managed service or silently resume recovery.
5. Declare stopped only after actual every-PID absence and endpoint/project/registry/
   capacity quiescence. Then use the actual lease-owner controller's normal release of a clean contained
   quarantine, current authoritative build/epoch, acquire/prepare, matching native
   MCP diagnostics, no-change release, and subsequent reconnect/capacity checks.
   Measure each affected slot; FREE alone is never pool restoration.

The recovery API neither starts/reloads services nor changes leases, caches, branches
or epochs. No raw signals, process-group signals, `SIGKILL` or nonchild `waitpid`
are substitutes. Proxy replacement, if separately necessary, retains the existing
coordinated request-drain and LO-5 gates. The finding/plan separate source correction
from native acceptance and leave broader failed project/paper gates unwaived.

While a stop-only residual exists, ordinary acquisition/release refuses before
changing the original FREE state or quarantined lease bytes, including the actual
paired owner. Retry uses the original authorization and exact current residual hash;
a failed ordinary lease operation does not mint new authority. Normal lease actions
resume after complete recovery. Legacy managed release warnings remain unchanged.
The combined retained/root/discovered shutdown graph is limited to 4096 identities;
absent retained identities still count. Observed parent drift before a signal refuses.

R3 preserves legacy lease behavior when bounded readable process provenance has no
origin/recovery fields. This does not loosen status, prepare, capacity or stop record
validation. Explicit malformed origins and opaque provenance refuse; recovery
reservations cover every declared role at the physical slot, including reverse
paired acquisition. Passive post-SIGTERM timeout retains typed diagnostic evidence.


### R4: bounded fresh-guard shutdown progress

The accepted R3 source and its bounded controls are distinct from native pool
acceptance. A populated normal release reached the ten-second stop deadline after
one delivered SIGTERM; FREE did not mean backend absence. R4 corrects the source
progress and observation costs; implementation review, ROOT execution and native
normal-release acceptance remain pending.

Keep initial identity/ancestry refusals unchanged. Only after a successful SIGTERM
in this invocation may a temporary exit-related refusal enter bounded passive
re-observation and later resume the pending target. Resumption requires the entire
retained family to satisfy the original classification again, followed by durable
persistence, fresh whole-family state/PPID comparison and the final exact live-target
check. While any required descendant is reparented, mismatched, unqualified terminal
or unavailable, no further signal is authorized. An exact live parent alone does
not bypass its descendants. An eligible native Z remains present and never receives
a signal; actual absence may permit fresh parent progress. Root absence with
survivors never permits chasing them. Delivery receipts contain only this attempt's
successful signals and do not prove termination or historical parent identity.

A shutdown-only family observation may batch bounded generic/native selected and
complete-census commands within one classification. Preserve original full generic
signatures and native PID/PPID/birth/STAT/command. Require capable known-observer
censuses, complete parsing, no extra/duplicate selected rows, selected/census and
cross-format coherence; absence needs all capable views. Generic observe_process
and ordinary readers retain their existing semantics. Never reuse a batch across
a durable write, signal or passive retry. Reject oversized requests/output rather
than truncating; the combined identity bound remains 4096, including absent IDs.

The same absolute ten-second budget includes every observation, persistence and
wait. Retain a bounded first refusal phase/target/typed observations alongside the
last passive observations in timeout diagnostics, without new probes after expiry.
Unregistration still requires actual absence of every retained PID and all existing
endpoint/project/registry/capacity checks. Ownership, exact retry hash, lease/pin/
domain preservation, stop-only provenance and all broader gates are unchanged.

R4 controls use production methods, real isolated JSON and external OS seams:
five/six-PID asynchronous exit chains with a synthetic 0.035-second cost per ps
command (pilot-informed, not a native guarantee), persistent refusal/no-extra-signal
negatives, nested terminal transitions, fresh evidence after persistence/signals,
malformed/denied/partial/duplicate/extra/oversized batches, and first-cause retention.
Preserve all nineteen prior mutation intents and add focused sole-guard controls.
