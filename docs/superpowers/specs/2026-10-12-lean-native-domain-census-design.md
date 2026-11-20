# Lean native domain census

Status: source implementation and whole bounded source/test/evidence review accepted. ROOT canonical evidence records documentation/source integration and current gates; bounded source review alone does not certify those outcomes. Native admission and runtime loading remain unverified. This extends the existing lifecycle observation design and ADR-008 LO1–LO6 without changing physical capacity or CLI scope.

## ND1 — Git checkout identity

Resolve inventory roots using bounded ordinary read-only Git commands. Normalize common directory and Git directory relative to the command working directory. Require successful, complete, unambiguous observations and matching top-level root before excluding a secondary linked checkout. Its common directory must match a capable, known canonical primary in the resolved family. Neither a directory name, equal config bytes nor the common directory's parent alone proves identity.

Retain independent primary same-role conflicts and substantive server, project, port and runtime-root differences. Preserve same-primary filename and dependency aliases. A config located in a linked checkout but explicitly resolving the primary is an alias and undergoes normal domain comparison. Unknown, denied, non-Git, malformed, mismatched or timed-out identities make the family incomplete and reserve capacity. Do not silently ignore them.

## ND2 — Complete ancestry

Use the complete capable process census to validate ancestry before selecting project roots. A matching project row is a root only if it has no other matching project ancestor anywhere in its parent chain. Generic intermediate commands do not sever the chain. Distinct project services sharing only a nonproject orchestrator or init remain distinct.

Relevant cycles, self-parenting, duplicate PIDs, missing required intermediate rows or incomplete/denied census are unavailable evidence. Do not collapse arbitrary common ancestors, omit rows or infer managed ownership from process text. Retain the existing stored generic and reparented descendant evidence independently of current ancestry. Preserve physical role conflicts, unmapped-heavy-process refusal and unknown-resource reservations.

## Controls

NC1: Create real temporary repositories with ordinary Git init and worktree add. Exercise actual inventory enumeration, status and census. A proven linked copy is excluded, primary roles occur once and an otherwise free physical slot remains available alongside occupied slots. No mocked inventory verdict. A sole production mutant restoring the old declared-only filter must fail a native assertion; restoration must pass.

NC2: An independent same-role primary with a conflicting domain blocks admission, reset and cache effects. Supported same-primary override/dependency filename aliases, including an alias stored in a linked tree but resolving the primary, remain accepted. A sole suppression of genuine conflict must fail a native assertion.

NC3: At only the external Git subprocess seam, inject permission failure, nonzero with stderr, timeout, truncated/extra/ambiguous fields, mismatched top-level, outside common directory, non-Git identity and incomplete canonical counterpart. Actual observer/status/doctor/CLI/census must show unavailable/incomplete/reserved with no effects; valid observations must pass. A sole fail-as-absence or malformed-success mutant must fail a native assertion.

NC4: Populate a complete process census with one project wrapper/MCP tree, generic Lake and Lean intermediates and several project workers. Actual census must count one ancestry tree, preserve exact physical occupancy and bounded remaining availability, with effects and state bytes checked. The old project-only direct-parent root mutant must fail an assertion.

NC5: Two unrelated project service roots sharing a nonproject manager/init and having their own children remain two, incomplete and refused, without adoption or signals. A sole common-ancestor collapse mutant must fail an assertion.

NC6: Cycles, self-parenting, duplicate PID, missing relevant chain and denied/incomplete census must not yield one safe tree. Preserve selected/census coherence, capability witnesses and stored reparented descendants. A sole cycle/missing-chain ignore or retained-descendant drop must fail an assertion.

NC7: After coherent ND1/ND2 correction, rerun all original lifecycle controls against corrected production source, with baseline green, meaningful assertion red and exact restoration green. Run the focused/full lifecycle suites and static original API checks. New controls supplement the original whole contract. Import, syntax, collection and harness failures do not count as mutant evidence.

## Preservation and admission

Keep typed present/absent/mismatch/unavailable observations; quiescence before reset/cache; durable pre-spawn reservation and owned-handle rollback/reap; shared physical capacity; global CLI start/stop/status; literal branch absorption and nonfatal post-unlink warnings. Historical frozen evidence and genuine pre-reconciliation documents remain immutable. ROOT reconciles the current architecture documents for independent integration review.

Source correction does not establish persistent proxy loading. After whole source acceptance, independent documentation/integration review and primary source integration, obtain fresh capable read-only native evidence. Evaluate an eligible known-owned physical slot only through existing internal Supervisor APIs and shared locks, under target-slot then one lifecycle lock, with reliable FREE, completed owned client/RPC receipts, a complete capable both-role census, backend/project/retained-descendant absence and before/after non-target preservation. Existing unlocked internals avoid lifecycle-lock reacquisition. Freeze ROOT dispatch/probes; recheck exact proxy identity, all-state TCP/listener, native threads and state-directory membership before and after. Passive snapshots do not serialize outside HTTP requests, and daemon handlers are not joined by server close; unaccounted activity blocks replacement. Proxy replacement loses its in-memory sessions and does not inherit S-Q backend-rotation continuity. Unknown quarantined resources remain reserved and untouched. Global restart still requires every owner drained and known. No new CLI verbs or scoped supervisor semantics.
