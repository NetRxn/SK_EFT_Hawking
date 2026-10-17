---
paper: infra
bundle: infra
bundle_target: infra
review_date: 2026-10-16
kind: targeted-infra
readiness_gates_version: 1
---

# Durable source checkpoints for long Lean work

### 1.1 — Unfinished source has no explicit durable checkpoint and resume route

- **Severity:** minor
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `scripts/lean_slots/controller.py`, `scripts/lean_slots/state.py`, `scripts/lean_slots/cli.py`, `scripts/lean_slots/supervisor.py`, `tests/test_lean_slots.py`, `tests/test_codex_lean_slot_policy.py`, `docs/adrs/ADR-008-shared-lean-slot-control-plane.md`, `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md`, `docs/superpowers/specs/2026-10-16-durable-lean-checkpoints-design.md`, `docs/superpowers/plans/2026-10-16-durable-lean-checkpoints.md`
- **Observed:** At design base db72be9d, ordinary release correctly requires clean contained source; prepare resets only after ordinary admission. No explicit transaction preserves unfinished source, ignored evidence and original contracts through slot reuse and changed dependency restoration. A backend pause retains the lease. A WIP commit or preservation ref does not satisfy ordinary containment. This is an enabling capability gap, not a defect in the existing refusal.
- **Evidence:** `scripts/lean_slots/controller.py:495`, `:725`, `:759`; `scripts/lean_slots/state.py:195`; `scripts/lean_slots/supervisor.py:549`, `:1184`, `:1563`. Low-level known-owned stop is source-feasible without candidate SF health, while general pause/activation paths can require SF or restart. Source inspection does not establish a usable native bootstrap.
- **Expected:** Implement the independently reviewed ADR-008 CP transaction within existing controller/state/CLI and narrow supervisor seams. Preserve actual source bytes through immutable ref/copies/manifests before any clean reset, durably retain complete original evidence/contracts, deny dispatch throughout checkpoint/resume source mutation and conflict, preserve later-owner/destination bytes, and use unchanged canonical release/acquire/prepare containment. Keep full proof acceptance separate and current epochs/pins mandatory.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py tests/test_lean_runtime_fingerprint.py tests/test_lean_lifecycle_observation.py tests/test_lean_slot_checkpoints.py -q`
- **Verification status:** The named command is the source-test gate, not native or whole acceptance. Nonclosable until coherent production-reader tests, sole mutants, independent implementation review, the full isolated native route pilot and exact ROOT activation have meaningful evidence.
- **Limits:** No additional slot pool, reservation ledger, unknown-process signaling, manual lease/pin/cache edits, dirty reset or current live checkpoint authority. Candidate bootstrap remains the separately gated CP-8 stop-only exception. Completed READY_TO_ABSORB work uses normal absorption; source/unit/pilot success is distinct from live admission, scientific acceptance and reviewed main delivery.

### 1.2 — Abrupt holder death strands directory locks before checkpoint recovery

- **Severity:** major
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `scripts/lean_slots/state.py`, `scripts/lean_slots/checkpoints.py`, `scripts/lean_slots/controller.py`, `tests/test_lean_slot_checkpoints.py`, `docs/adrs/ADR-008-shared-lean-slot-control-plane.md`
- **Observed:** Actual native child `os._exit(71)` while holding one or both production directory locks leaves their owner directories intact. Ordinary reacquisition refuses after native observations establish that the measured holder PIDs are absent; exception unwinding alone removes the lock. Recovery needs those locks before reaching its transaction reconciliation, so the existing scoped tests do not establish abrupt-death recovery.
- **Evidence:** ROOT's local `round50-checkpoint-abrupt-lock-native-measure-r1` receipt; independent `round50-checkpoint-crash-recovery-design-review-r1` and ROOT intake; `round50-checkpoint-native-lock-primitives-r1` report with actual Darwin/Linux NO-REPLACE publication/retirement, legacy races and inherited-flock/Git-helper controls. These are retained ignored local evidence, not portable product acceptance. The premature-retirement negative admits legacy mkdir while the sidecar is still held.
- **Expected:** Implement the independently reviewed CP-3/CP-6 compatible complete facade and stable sidecar protocol. Prove mutator launch/completion across parent death, exception and timeout before retirement; preserve ambiguous legacy directories and later-owner identity. Complete every original CP-1 through CP-8 obligation and the staged whole native pilots before live use.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py tests/test_lean_runtime_fingerprint.py tests/test_lean_lifecycle_observation.py tests/test_lean_slot_checkpoints.py -q`
- **Verification status:** OPEN. The command is a source-test gate; implementation, actual production seeded mutants, whole abrupt-death recovery/native matrix, independent review, closure and reviewed main delivery remain required. No live directory retirement or manual deletion is authorized by this finding.


### 1.3 — Pending resume can admit ordinary proof dispatch after transaction death

- **Severity:** major
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `scripts/lean_slots/proxy.py`, `scripts/lean_slots/supervisor.py`, `scripts/lean_slots/checkpoints.py`, `scripts/lean_slots/controller.py`, `scripts/lean_slots/state.py`, `tests/test_lean_slot_checkpoints.py`, `tests/test_lean_lifecycle_observation.py`, `docs/adrs/ADR-008-shared-lean-slot-control-plane.md`
- **Observed:** In the measured CP candidate, a real checkpoint child exits after ACTIVE, during smoke, or after smoke before completed journal persistence. With the long-lived ROOT lease owner still alive, an actual ordinary production HTTP LeaseGate request reaches the peer with HTTP200 despite the pending journal. The before-ACTIVE control denies with HTTP403. Exception cleanup does not close actual process-death windows. Transaction backend/census observations were Host modeled; post-death HTTP handler, client, peer and process exit/wait were actual.
- **Evidence:** Local `round50-checkpoint-CP7-fixed-audit-ROOT-intake-r1` retains the fixed run's raw three intended failures and one passing denial, exact case journals/leases/responses and implementation hashes. Later byte-exact source recovery is separately qualified where applicable. These observations are not whole native A or actual Lean evidence.
- **Expected:** Implement independently reviewed CP-7 pending/completed admission in existing lease/journal readers: atomic ACTIVE plus pending context, exact internal live transaction diagnostic smoke, durable positive completed journal before completed lease admission, and actual LeaseGate denial until validated completion. Keep required ACTIVE-then-smoke ordering, ordinary never-resumed/S-Q/auth/SF behavior, current epochs/pins, lock/recovery/owner guards and later-owner non-replay.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py tests/test_lean_runtime_fingerprint.py tests/test_lean_lifecycle_observation.py tests/test_lean_slot_checkpoints.py -q`
- **Verification status:** OPEN. Independent amendment review, coherent implementation, production positive/negative/sole-mutant controls, complete isolated native A then B, supported closure, current gates and normal reviewed main delivery remain required. No live CP use or broad gate waiver is granted.


### 1.4 — Scheduler-only observation drift prevents owned shutdown progress

- **Severity:** minor
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `scripts/lean_slots/state.py`, existing lifecycle/slot tests, ADR-008 R4.
- **Observed:** Fixed native case005 has exact PID/PPID/birth/full command and rooted family in four capable views, but native selected Rsl differs from census Ssl. Full-row comparison refuses before the first signal for that family, so its intended conflict target is unreached. New cases030/034 independently expose the same bounded R/S witness shape; earlier missing raw cause remains UNKNOWN.
- **Evidence:** Ignored local current-failure005 review and fixed raw pilot, observation-readiness spec review and corrected specification confirmation retain exact source/row/hash bindings. These are scoped observation evidence, not whole native acceptance.
- **Expected:** Implement selected R4-S1 through S4 in the existing observers: bounded entire-pass resampling only for same-suffix R/S drift, once-per-invocation absolute fallback preserving earlier budget, original strict final coherence and valid witnessed absence. No generic retry or weakened signal/identity/graph predicate.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py tests/test_lean_runtime_fingerprint.py tests/test_lean_lifecycle_observation.py tests/test_lean_slot_checkpoints.py -q`
- **Verification status:** OPEN. Require production-seam red/coherent-positive/persistent-negative controls, all invalidated current-source gates, full native workflows, sole controls and independent whole acceptance. Source tests do not close this finding.

### 1.5 — Native positive fixture exposes readiness before its planned family exists

- **Severity:** minor
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `tests/fixtures/lean_checkpoint_native_peer.py`, existing native checkpoint controls.
- **Observed:** Actual case058 ordinary absorb rewarms root3195, then immediately enters counterpart restoration. Leaf3241 appears under middle3198 after the shutdown graph has durably retained root/middle. Complete selected/census views agree; the production new-descendant guard correctly refuses before signaling that new family. Earlier completed checkpoint/auth components do not complete the required later absorb workflow.
- **Evidence:** Ignored local current-failure058 independent review binds complete raw views129-132, launch/self-record/PPID chain and empty new-family delivery receipt. Earlier stopped family2593 has distinct signals and is not this receipt.
- **Expected:** Implement R4-F1/F2: bounded fresh owned recursive startup acknowledgment before positive fixture listener readiness; retain an independent deliberately late-child negative after durable graph freeze. Preserve the production new-descendant guard and descriptor policy exactly.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py tests/test_lean_runtime_fingerprint.py tests/test_lean_lifecycle_observation.py tests/test_lean_slot_checkpoints.py -q`
- **Verification status:** OPEN. Require actual slow-child listener absence, exact fresh generation/identity/parent controls, unchanged ordinary absorb rewarm/restore success, deliberate late-child no-signal refusal and full current native/gate review. No production refusal waiver or whole workflow acceptance follows from this plan.

### 1.6 — A missing retained intermediate ancestor escapes typed shutdown refusal

- **Severity:** minor
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `scripts/lean_slots/state.py`, `tests/test_lean_lifecycle_observation.py`, `tests/test_lean_slots.py`
- **Observed:** In the bounded R/S-discrepancy branch, a live retained child can report an independently absent retained intermediate parent while the root remains live. The ancestry walk checks retained membership but indexes the missing native row before proving complete-map presence. This raises `KeyError` rather than the required typed unavailable result. No unsafe signal or authority bypass is asserted.
- **Evidence:** Independent whole-current24-source review `round50-checkpoint-observation-readiness-whole-implementation-review-r8/report.json`, finding `OR-IMPL-R8-1`, exact state.py hash `00776674971ed4148503dc76876f56e885112e32b472944ba8ca4532b356a974`, unchecked lookup at line1287. The review contains a complete static missing-middle witness; runtime reproduction remains required.
- **Expected:** Before native ancestor access, require independently present, exact and live retained ancestry using the original predicate. Missing ancestry is immediate typed refusal on the first pass; preserve first-cause/absolute-budget behavior after a previously delivered signal. Do not swallow arbitrary exceptions, synthesize rows, resample this defect, weaken guards or repair registry state.
- **Verify:** `uv run python -m pytest tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py -q`
- **Verification status:** OPEN. Require actual old-source red and corrected green at the production four-view seam, Supervisor stop and post-first-signal boundaries, then exact-current full named/native/sole and independent review gates. Existing prior-source native passes do not certify corrected source.

### 1.7 — Startup acknowledgment publishes its final name before complete bytes

- **Severity:** minor
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `tests/fixtures/lean_checkpoint_native_peer.py`, `tests/test_lean_slots.py`, ADR-008 R4-F1/F2.
- **Observed:** Current native campaign independently records JSONDecodeError at distinct recursive-startup boundaries. The fixture exclusively creates the final ACK name before writing/fsyncing its JSON, so a strict concurrent reader can acquire incomplete data. Exact transient bytes and syscall ordering in those historical failures were not instrumented; char0 is not measured empty bytes. Product targets beyond those startup failures are unreached, not passed.
- **Evidence:** Frozen current R2 cases005/012 and independent startup-publication design review bind identical backend log SHA41a3f2bcb68dc00d9cbfa516137f70717d1a360e0e4d9fc8e47d401c0673c760, literal fixture hash99dc74beafc1a30536a3041ce6894697fff628bf891c643b728bae2f9d815c44 and verified immutable embedded artifacts. Additional current failures remain separate terminal campaign evidence. Static source establishes early name visibility; no unsafe production signal is asserted.
- **Expected:** Implement the independently reviewed R4-F1-A complete private staging and atomic native NO-REPLACE publication, strict one-link bounded stable reader, original absolute deadline/cancellation and exact owned recursive readiness/cleanup. Preserve every original production refusal and all CP/R4 gates; do not retry malformed JSON or weaken file trust.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py tests/test_lean_runtime_fingerprint.py tests/test_lean_lifecycle_observation.py tests/test_lean_slot_checkpoints.py -q`
- **Verification status:** OPEN. Requires deterministic actual-helper old red/current green, exact ACK-filesystem capability/collision pilot, full strict negative/owned cleanup controls, independent whole review and exact-current full named/native/sole/A→B→live gates. Source, focused controls and design recommendations are distinct from whole acceptance/closure/main delivery.
