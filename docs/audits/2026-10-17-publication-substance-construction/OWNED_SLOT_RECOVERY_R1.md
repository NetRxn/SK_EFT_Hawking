# Owned slot recovery and reset responsibility

**Completed 6 November 2026. wt2 and wt3 are available for fresh task admission.**
Both passed the existing acquire, prepare, actual Codex MCP probe and normal
release sequence. The final controller doctor passes every check. All three
slots are clean and unleased at authoritative primary `2fbbfd95a396cadfd89961dea226d84c4f281675`,
with healthy proxies, stopped backends and no reserved physical capacity.

[Actual public readback](OWNED_SLOT_RECOVERY_R1.json) and
[complete evidence custody](OWNED_SLOT_RECOVERY_EVIDENCE_R1.json) preserve the
operations, original lease bytes, saved Git refs and native results. Both native
probes exposed the expected 21 Lean tools, withheld `lean_build`, completed an
active diagnostic dispatch and closed their sessions successfully. Validation
was sequential; it does not claim a simultaneous scientific swarm or publication
acceptance. New work still acquires/prepares immediately before its actual task.

## Correction to the earlier assessment

The earlier [automatic-path assessment](LEAN_LANE_DISPOSITION_R1.md) accurately
identified normal CLI restrictions, but ROOT incorrectly treated them as the
limit of orchestrator recovery. ADR-008 S-B assigns reset authority to the
primary orchestrator; `/reset-slot` documents the branch-reset pattern. The
operator explicitly clarified that saved work may be reset manually by the
orchestrator. No controller feature or configuration change was needed.

ROOT verified clean ownership and complete quiescence, verified exact named
local and remote preservation refs, and archived the original state. Under the
existing integration, target-slot and lifecycle locks, existing guarded stop
helpers retired only confirmed-quiescent process records. ROOT reset the saved
branches with `checkout -B --no-overwrite-ignore`, atomically archived the old
lease records unchanged, then validated fresh normal lifecycle operations.
No dirty reset, owner-ended fiction, forged lease, cache replacement during the
manual phase, global restart or unrelated main merge occurred. The subsequent
normal prepares installed the existing successful-build epoch through the
controller. Old BP work remains preserved for scientific review/integration;
freeing its capacity does not close that scientific obligation.

## Standing responsibility

The user assigned one reset/recovery go-to to the team: **ROOT while ROOT owns
publication orchestration**. Executor and other agents route `/reset-slot` and
manual recovery requests through that owner. A handoff explicitly names the
successor. The owner preserves work, reconciles other owners and active requests,
checks actual quiescence, performs the appropriate recovery and records readback.
Routine authorized recovery does not require repeated user permission. Unknown,
dirty or actively peer-owned work still requires reconciliation before action.

Executor has been notified of both recovered lanes and this standing ownership.
Availability and assignment are separate: the lanes remain free until concrete
approved tasks are ready. The full publication objective and original scientific
acceptance requirements remain unchanged.
