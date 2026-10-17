# Round 50 durable checkpoint specification re-review R2

Verdict: **PASS for the corrected bounded specification and intent.** R1 CP-R1 and CP-R2 are resolved at specification level. No remaining BLOCKER, MAJOR or MINOR finding was identified in this re-review. No material specification blocker remains before ROOT's owner-first implementation package under the existing plan. This verdict does not accept implementation, establish native feasibility, authorize a live checkpoint, or close broader project/scientific/main gates.

## Evidence and scope

Assignment: `round50-slot-durable-checkpoint-spec-review-packet-r2.json`; source base `db72be9d79eb8729eb95d481ddea05e6261fdeb4`. Directly re-read the complete corrected CP amendment and checkpoint design, unchanged implementation plan, and new operator proposal section. Re-inspected the actual controller constructor/prepare/release, proxy dispatch reader and supervisor owned-stop/pause seams relevant to the corrections. Earlier governing-authority orientation and source analysis remain applicable; the packet binds unchanged authorities and source modules. No unrelated historical audit was repeated.

Current proposal hashes were independently read using SHA-256 and match the packet:

| Input | SHA-256 |
|---|---|
| `docs/adrs/ADR-008-shared-lean-slot-control-plane.md` | `37ae43f1f69aa9230e3ddba57b342b926a62b921413d5119ecc29e67cf08bd54` |
| `docs/superpowers/specs/2026-10-16-durable-lean-checkpoints-design.md` | `33d72c42172996fb9c09fd89d698dc88898b0e70d872d56d25184a708bb82c90` |
| `docs/superpowers/plans/2026-10-16-durable-lean-checkpoints.md` | `92d8fd6778619960ed1c72c427318bb85b72f5fdf7999f4ec3fcf13579245b05` |
| `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md` | `571782ccc34d12c16852ac90a48ba857b7267de9c15e25799b341827d5ef1cae` |
| Preserved R1 report | `3520f143051d2adf2e3ec7eebac8147cfebca70bf784298fe7873cd52a010f44` |

Both canonical continuity checks, at entry and immediately before this sole report write, returned exit 0, `fresh=true`, `changed=[]`. R2 report creation changes its previously missing owned state, so a later packet check is expected to report owned-output drift. No postwrite fresh PASS is claimed and no packet was refreshed. Read-only file inspection, SHA-256 reads and these adapter checks were the only operations besides the assigned report write. No tests, native observations, network, database, Lean/MCP, controller lifecycle commands, Git mutation, source/runtime edits or subagents were used.

## Resolution of R1 findings

**CP-R1 resolved:** ADR CP-7 lines 1032–1048 and design lines 98–119 now bind the newly acquired lease generation/current bytes and destination manifest, require durable quarantine before any source mutation, retain dispatch denial through restoration/conflict/interruption/recovery, prohibit unconditional restart on failure, and define a journal-bound successful canonical restoration before ACTIVE. Resulting source/current dependency/epoch and pre-dispatch loaded-code/session/tool-policy gates precede reactivation; the bounded actual matching proof smoke follows it, with immediate quarantine on failure. This order avoids requiring an authorized proof request from a quarantined lease while preserving the pre-dispatch guards.

The corrected mechanism matches the actual source issue: current prepare sets ACTIVE (`controller.py:537–540`), and actual proxy authorization reads ACTIVE (`proxy.py:113–119`) independently of lifecycle locks. The repaired test matrix reaches that real proxy reader during paused restore/conflict (`design:155–164`), with omitted-quarantine/reactivation mutants (`166–171`). No native denial behavior was measured in this re-review.

**CP-R2 resolved:** ADR CP-2 lines 987–1001 and design lines 51–64 require actual durable source bytes in the protected WIP tree or copied source payload; hash-only nontracked source refuses. The same text covers destination enumeration/reobservation, retained ignored/nontracked file/directory collisions, and refusal before overwrite for reset, same-base restore and changed-base merge. Destination-owner bytes and checkpoints remain protected, with ordinary source-safe ownership resolution instead of automatic removal. The actual-Git and sole-mutant requirements now include omitted source copies and both recorded/current target collisions (`design:159–171`).

Implementation must apply this existing before-reset requirement at the first relevant source-writing reset, including canonical preparation in a resumed path; checking only the later restore/merge would be too late. A checkpoint-aware preflight can precede the unchanged ordinary prepare call. Likewise, copied-source restoration must honor the destination refusal rather than treating the copy as overwrite authority. These are consequences of the corrected requirement, not additional mechanisms or a new specification finding.

## Stop-only bootstrap and unchanged lifecycle

CP-8 now explicitly requires binding validation before Controller construction or state-directory creation (`ADR:1049–1061`, `design:123–143`), addressing the actual constructor effect (`controller.py:65–67`). It explicitly excludes `process_state`, `paused_backend`, `activating_from` and `_assert_backend_owned_or_stopped` in the candidate transaction; the first enters SF status while the other helpers reach SF and/or automatic starts. The low-level `_stop_backend_unlocked` → `_stop` → `_stop_owned` route uses validated metadata, RR identity, quiescence and global census (`supervisor.py:1563–1564, 1184–1228`). That remains a source-feasibility inference to test through the real candidate entry route, not measured native feasibility.

The candidate exception is narrow and proposal-only. Explicit inventory selection cannot replace exact imported-candidate/canonical-source/domain/owner bindings. Candidate health/start/reload/release remains forbidden; SF mismatch remains visible and canonical start/health refusal remains intact. Canonical release remains a separate command after locks are dropped. Existing release still accepts its supported states, checks cleanliness/containment, restores the counterpart, unlinks the lease and reconciles resources (`controller.py:725–757`). No rescue-ref expansion or READY_TO_ABSORB bypass is proposed. Reobserve capacity after release because counterpart restoration may start a backend; FREE is lease state only.

The new operator section (`LEAN_SLOT_OPERATOR_GUIDE.md:617–631`) clearly marks the feature unimplemented/unavailable pending admission, names the separate gates, preserves the canonical-primary rule for existing commands, and provides no premature live usage command.

## Intent and remaining acceptance boundary

The correction preserves continuous frontier growth/integration/growth: completed ready work absorbs normally, unfinished long proofs retain their full original contracts, exact source/evidence/failures/ancestry and independent acceptance obligations. No WIP, checkpoint, helper or free lease becomes proof acceptance. Fresh epochs/pins and ancestry-preserving changed-base merge remain required; old native/MCP/build/scientific observations remain historical. The journal remains transaction recovery state, with existing leases, process reservations, locks and planner ownership retained.

The unchanged plan's coherent implementation package and production-reader/mutant matrix are adequate for this specification boundary. Implementation must prove stable lease generation and expected byte transitions, durable publication/ref/source protection, complete ignored/nontracked classification, drift refusal and no later-owner overwrite using the actual readers. The isolated native pilot still owes the actual CLI/import/Git/evidence route, known-owned backend/descendants, independently completed requests, both-role absence/global census, interruption/recovery, unchanged canonical release and counterpart accounting. No unit fixture or source review substitutes for it. Measure enumeration/copy cost on that isolated slice before live use.

ROOT still owns filing/intake through the existing planner, source implementation assignment, independent implementation review, exact native pilot/activation, normally integrated canonical resume, current builds/gates, supported closure and ordinary reviewed Git delivery. This re-review removes the two specification objections only; it does not mark any of those later states complete.
