# Lean runner recovery source findings

Review date: 2026-10-12. Source baseline:
`33be8dbe04d3477788b2696633970c76fc72365f`.
Scope: existing controller shutdown and explicitly authorized restoration of the
affected public slot pool. **OPEN; candidate correction implemented, source verification and native
recovery acceptance pending.** No scientific/apex/whole-project claim or gate waiver.

Native provenance: ROOT's primary-local packet
`.codex/continuity/round38-runner-recovery-public-native-witness-r1.json`, SHA-256
`c96021871dd6e39aa69a2fccb407466bd0b51d59867a31f267f3bae246fa333b`,
recorded `2026-10-12T16:00:38.769584+00:00`, with the managed-family observation at
`2026-10-12T15:51:31.734296+00:00`. This is historical evidence supplied by the
controller; the author performed no native probes or process mutation. The prior
build/lease/probe success reported by ROOT is not final stopped-resource acceptance.

## Findings

### 1 — RR1: A retained exited child prevents guarded owned-parent shutdown

- **Severity:** major
- **Status:** open
- **Lane:** infra
- **Target:** `scripts/lean_slots/supervisor.py`
- **Location:** `scripts/lean_slots/supervisor.py:1124–1175` (`Supervisor._stop`), `scripts/lean_slots/state.py` (native shutdown-state observation)
- **Gate:** safe owned backend release/recovery; source and native acceptance remain separate
- **Verify:** `.venv/bin/python -m pytest tests/test_lean_lifecycle_observation.py -q -k rr1`

The source persists full `lstart + command` signatures and then signals reversed
numeric PID order. It refuses a changed descendant command before reaching an
otherwise exact live owned parent. Numeric PID order does not establish ancestry.
The generic observer is correctly strict; it must not be weakened to make shutdown
progress. No native `STAT` terminal witness exists in the generic row model.

The bound native witness has managed root PID 32001 and child 32051 both exact/live;
retained lake child 34174 has native `Z`, PPID 32051, and matching original/current
`lstart` of 10:45:22. Its command became `<defunct>`, producing generic mismatch.
Retained 34560 and 34561 were actually absent. The normal no-change release returned
success with a visible stop warning after partial signalling; FREE did not establish
backend absence. This record does not invent individual historical signal receipts.

Required correction: ADR-008 RR-1/RR-2, a shutdown-only genuine terminal observer,
unchanged generic identity semantics, original signatures retained, independently
guarded live-parent SIGTERM, ancestry ordering and bounded passive exit/reaping
observation. A zombie is never signalled or counted absent. Coarse legacy `lstart`
does not prove atomic generation identity. Root-absent/reparented/unrelated mismatch
and genuine ambiguity remain refusals. Preserve all final every-PID/project/endpoint/
registry/capacity quiescence checks. Closure additionally requires the plan's
meaningful production mutation/restoration controls and ROOT's fresh native managed
stop witness; a scoped synthetic pass cannot establish native recovery.

### 2 — RR2: Identified orphan backend families lack a guarded stop-only recovery route

- **Severity:** major
- **Status:** open
- **Lane:** infra
- **Target:** `scripts/lean_slots/controller.py`
- **Location:** `scripts/lean_slots/controller.py` (recovery entry), `scripts/lean_slots/supervisor.py` (record validation/capacity/stop), `scripts/lean_slots/state.py` (exclusive publication)
- **Gate:** owner-authorized pool restoration with preserved work and residual reservations
- **Verify:** `.venv/bin/python -m pytest tests/test_lean_lifecycle_observation.py -q -k rr2`

The source's unknown-resource refusal is necessary for ordinary lifecycle safety.
The bound native slice nevertheless identifies unregistered fixed-project families:
slot 1 root 21045 → 21057, and slot 2 root 29534 → 29545 → 30261 → 30305 →
42005/42139. Their configured listeners 18761/18762 belong only to their respective
families in that observation; no established backend TCP was reported. These samples
are not proof of drained handlers or authority for later signals. ROOT reports same-session clean contained quarantines, including a declared paired
downstream owner for one public backend target, and preserved clean contained
work while the orphan backend targets are public.
The actual global lease authority and target backend authority must therefore be
resolved separately; recovery must recheck both under locks. The operator explicitly confirmed shutdown
repair and restoration of slots 1 and 2 are in scope.

Required correction: ADR-008 RR-3/RR-4, the explicitly named internal
`Controller.recover_orphan_backend_stop` route, under target-slot then one lifecycle
lock. Bind fresh exact full family identities, unique configured project/listener,
current authorized owner, permitted lease, clean/containment and request-drain gates.
Resolve the actual `lease_owner` separately from `backend_target`, validating its
genuine declared pairing to the target, canonical identities, shared state root and
physical number. Invoke that owner's unchanged `_lease_for_command` and work checks;
validate clean paired target path and original dependency pin without advancing it.
Keep target family/listener/process-record checks under the target inventory. Bind
both roles/worktrees/pin in approval, residual and retry. A valid same-session paired
quarantine is not an opposing active backend, and arbitrary foreign ownership still
refuses. Do not weaken role equality or rewrite the lease.
Before signals exclusively publish a complete durable `uncertain_residual` record
marked `operator_stop_only`; never manufacture managed launch/fingerprint/token
provenance. Initial managed/foreign/unknown registration refuses. Deliberate retry
requires the exact stop-only residual hash and unchanged owner/scope/original
signatures, target/lease-owner pair and dependency pin plus fresh gates. No ordinary
healthy reuse or automatic adoption.

Keep global supervisor CLI behavior unchanged. The API stops resources only; normal
release by the actual lease-owner controller, then build/acquire/prepare/probe/release
paths restore usable slots after actual
quiescence. Closure requires the plan's RR2 positive/negative and meaningful mutation
controls, independent whole source review and ROOT's distinct fresh native cycles
for the affected slots. Until then failures and capacity reservations remain visible,
and wider test/paper/wave gates remain failed or open as previously recorded.

The RR2 verification includes `test_rr2_paired_lease_authority`: a populated public
orphan/declared downstream same-session quarantine positive with exact lease and
worktree preservation, foreign/unpaired/wrong-owner/state-root/number/pin/opposing
backend/retry-authority negatives, and a sole production pairing-guard red followed
by exact-restoration green. This is required future evidence, not a test result.

Both Verify commands are exact future commands from the canonical primary after
accepted integration, using its matching environment. The RR tests now exist in the candidate but have not been executed by the author;
zero selected tests is not a pass. Before integration ROOT uses that same primary
interpreter against the accepted candidate. The design author executed neither.

Candidate R2 addresses whole-source review RRI1–RRI4: preserve exact original
lease authority through attempted ordinary acquire/release, guard final observed
parent/rooted ancestry, enforce/validate the complete retained family bound before
effects, repair the R1 oracles and add the promised edge controls. These are source
changes and unexecuted controls; RR1/RR2 remain OPEN pending ROOT tests/mutations,
independent whole review and separately measured native recovery.

R3 follows the actual R2 selected result (84 passed, 1 failed) and four-module result
(328 passed, 25 failed, 1 skipped). Its narrow provenance and diagnostic corrections
and genuine fixture repairs are source-present only. New malformed-origin and
reverse-paired controls extend the preserved RRI1–RRI4 contract. No R3 test, source
acceptance, native recovery or finding closure is claimed.


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
