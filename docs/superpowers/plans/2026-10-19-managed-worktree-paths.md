# Implementation plan — managed-worktree path portability

Status: specification accepted and implementation authored under the lead’s deliberate successor.
Whole nonauthor source/control review is accepted at its declared scope. The October25
combined six-module run passes221 tests with one existing skip, including the full Phase6i
file. On October25 the existing writer recorded findings1.1/1.2 fixed after both
declared Verify commands passed. Full merge qualification and main integration remain pending.
Parent: publication inherited-main failure reconciliation, PREFIX_CONTEXT + CACHE_CONTEXT.
Owning [design](../specs/2026-10-19-managed-worktree-paths-design.md).
Canonical [findings 1.1/1.2](../../../papers/AutomatedReviews/2026-10-19-managed-worktree-paths/infra.md).

## P1. Accept or repair the specification

Publication lead independently challenges the complete design against ADR-012 P10 and the
existing canonical workspace owner. Use the actual baseline red receipts and current
source/history; do not accept a helper-name scan as evidence. Return corrections to this
specification author. Record a concrete accepted result before the implementation successor.
No source code, tests, closures or Git integration in this step.

## P2. Assign one coherent implementation package

The lead names an accepted owner and a fresh continuity packet for the isolated candidate,
including protected source/branch state, exact paths and nonauthor acceptance reviewer.
Do not assume the current specification assignment permits implementation. Keep source and
regression controls together so normalization cannot land without its missing-file refusals.
No Lean lane or cache/acquisition controller is required.

Prospective paths: existing `scripts/orchestrate.py::target_files`,
`tests/test_orchestrate.py`, `tests/test_phase6i_wave1.py` (cache function and controls),
`tests/test_architecture_claims.py` (new ADR sentence/runtime pin); extend the existing resolver
tests only if needed for the different managed layout. No new resolver/check/gate/ledger.
The ADR clarification and these finding/spec/plan files travel with the reviewed repair.

## P3. Implement the two consumer corrections

1. Normalize one exact leading logical repository prefix within the existing target parser.
   Resolve the resulting candidate inside the active checkout. Preserve canonical containment,
   file-existence, all-target enumeration/dedup, legacy contained spellings, file-conflict
   queuing and lane strength. Do not redirect to the canonical sibling or relax a guard.
2. Replace the cache test's ad hoc workspace parent walk with already imported
   `find_workspace()`. Keep checkout-local source state and the unchanged real missing/empty
   assertion and successful-state drift distinction. Remove a now-unused old root definition.
   Preserve the unrelated later-primary tmp_path extractor change on integration.
3. Bind the new ADR sentence to runtime results in the existing architecture-claims tests;
   pin sentence plus behavior, not just a helper name in source text.

## P4. Prove the repair without weakening the measurements

Record exact interpreter, candidate HEAD/source hashes and imports from the active candidate.
Use the prepared existing Python environment without dependency install/sync. Keep default
pytest selection semantics and record any broader run's actual scope.

Required controls are the design D3 table, including a canonical sibling with a distinct active
copy, mixed prefix/unprefixed/ranges/multipath dedup and missing/traversal/escape refusal;
cache nonempty, missing, empty, success-drift, null-path and state-root controls. Call the
existing cache invariant for its negative controls instead of implementing another validator.
The current two original failure identities must be red with old behavior and green after
repair in the actual differently named managed checkout. Their green alone is insufficient.

Run at least the complete orchestrator file, resolver tests, existing architecture claim pins
and the entire Phase6i file with its new controls. Report the known separate missing-citation
red if still present; repair ownership remains with its own task. Do not skip that assertion,
reduce registry coverage, forge a success record or raise a ceiling.

Use the existing seed journal for real production-artifact mutation, only in the allocated
checkout; preserve exact bytes/metadata and durable red/restore receipts. Do not seed the shared
literature cache or mutate another worker's candidate. If a production control cannot be run
within the allocated isolation, retain it as owed and return the concrete missing condition.

## P5. Author repair, independent verification, recorded closure

A genuinely nonauthor reviewer independently reads the whole source/test/docs diff and actual
red/green/restore receipts. Challenge canonical-sibling routing, active import witnesses,
existence/containment/multiplicity, file/lane composition and successful-state-only drift.
Return mandatory corrections to the author; an accepted specification or self-test is not this
review. Root runs appropriate existing change-scoped checks and required integrated gates.
Close only through the existing writer after the acceptance bar is actually met. Do not run
any closure writer or change a ratchet in this specification task.

## P6. Integrate at the first accepted repair checkpoint

The lead composes a reviewed ordinary Git checkpoint against the current integration base,
preserving NJL/ADW and accepted later-primary work. Inspect the final combined diff and qualify
that exact head; an isolated branch pass is not merged-main evidence. Follow the user's
minimum cadence of integrating completed milestones instead of retaining publication work
indefinitely in a worktree. Merge only after the existing required gate/review boundary.
Scientific bundle readiness and final human publication review remain independent.

## Termination evidence

This specification handback ends after complete findings/design/plan, narrow ADR clarification,
actual FIRST/FINAL and protected-state evidence. Implementation completion later requires exact
source/control receipts, independent review, supported closure and reviewed Git integration.
Do not report either later state from this proposed plan.


## Historical October19 author checkpoint — before independent source review

The following paragraph preserves the author handback before the accepted independent
review in SCOPED_REVIEW.md; its pending-review statements describe that earlier checkpoint.

P1 and P2 were accepted by the publication lead before implementation. P3 is implemented in
the existing consumers; P4 has actual candidate import/source witnesses, original two old-red
and fixed-green results, canonical/managed layout and refusal controls, and journaled
production red/restore evidence. The path-control group passes. The full four-file run retains
the separately owned missing-citation failure; its assertion and population are unchanged.
P5 and P6 remain owed. The author has not recorded closure, changed shared registries, run
native/controller work, pushed or merged. This progress record is not independent acceptance.
