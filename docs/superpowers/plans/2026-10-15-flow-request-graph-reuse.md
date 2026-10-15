# Flow request graph reuse — implementation plan

Status: **Design accepted; source and isolated tests implemented, pending independent implementation review and full verification.**

Authority: ADR-019 D1–D6 and `docs/superpowers/specs/2026-10-15-flow-request-graph-reuse-design.md`.

## Global constraints

Preserve current cache/read-set/imported-code invalidation and configured PG synchronization
through the existing cache owner; add no independent PG writer. Verification uses the existing
`--no-pg-sync` browser fixture or disabled PG sync for test-client runs; policy tests intercept
scheduling without connecting or writing to PG. No Lean build or dependency extraction is added
to the route; legitimate full graph reconstruction on cache miss and standalone fallbacks remain.
Preserve P1 downgrade failure `None` versus evaluated `{}`, complete findings/gates, coverage,
unknown states and non-verdict rendering. No parallel cache, new planner, epoch, registry,
validation check or source manifest writer. No timeout/cap/floor/threshold/assertion relaxation.
ADR-018 remains a separate accepted source-path decision; do not modify its readers' semantics.
A scoped test success does not waive other failures or confer merged-wave/publication acceptance.

## Ordered work and file ownership

| Task | Files | Deliverable and exit condition |
|---|---|---|
| A — independent design review | ADR-019, this spec/plan, DASHBOARD amendment and routed finding | Fresh-context adversarial assessment and intent comparison; all mandatory design issues resolved before code. |
| B — coherent request reuse | `scripts/provenance_dashboard.py`, `scripts/dashboard_flow.py`, `scripts/bundle_readiness.py` | One owner connects borrowed graph through paper loading/aggregation and existing board injection, orders actual reader imports, preserves failure boundaries and standalone APIs. Gate-only wiring is incomplete. |
| C — safety and consumer tests with B | `tests/test_dashboard_flow.py`, `tests/test_readiness_cannot_measure.py`, `tests/test_dashboard_graph_cache.py`, `tests/test_template_contract.py`; existing producer guard in `tests/test_d5_bundles_readiness.py` | Behavioral tests of the real route/aggregate seam, first-request import state, complete populations, no extra fallback, graph immutability and cannot-measure paths. Existing no-argument test doubles remain meaningful; update only signatures needed for the real optional API. |
| D — actual candidate verification | Existing tests, including `tests/e2e/test_operator_panes.py` unchanged | Finding Verify passes with original browser timeout/assertions; public-safe source-bound timing/caller receipt if performance figures are reported. Snapshot watched artifacts/status before and after; use the existing fixture and seed journal. |
| E — independent implementation review and normal closure | Owning docs and the existing closure writer | Reconcile actual diff, implementation/tests, errors and evidence; then lead runs applicable broader gates and existing closure process. Merged-wave acceptance remains its own terminal step. |

B and C form one coherent package, because an unconnected input or a test that replaces the route
would leave the actual consumer unguarded. Do not split the same source files between concurrent
workers. Planner grouping/caps are evidence about routing, not authorization to execute a wave.

## Source and test obligations

Implement ADR-019's keyword-only optional `graph` while preserving `review_info` position and
omitted-input fallback. Use the same object, not a graph reconstructed from gate nodes. Check
explicit bad/empty injected input at the helper boundary and carry unknown, never healthy-empty,
into aggregation. Retain the real gate evaluator and current finding/metadata readers.

Move actual reader imports before acquisition without pre-running the reader functions. Exercise
import failures at the actual pane boundary. Do not edit `_graph_fingerprint` to suppress newly
loaded modules or stamp a post-render key. Inspect normal imports for cycles/side effects before
hoisting them; if this cannot be kept bounded, return the concrete issue to design review.

Existing obligations selected from current tests:

- `test_dashboard_flow.py`: empty-gate unmeasured, empty findings/roster refusal, complete coverage,
  uncapped overlay, undeclared status and live-board consistency. Extend with full route reuse.
- `test_readiness_cannot_measure.py`: whole evaluation failure returns None, GREEN withheld,
  individual evaluator crashes blocked and healthy results unchanged. Extend both input modes.
- `test_d5_bundles_readiness.py::TestProducerDemotesGreenOnBlockedP1`: retain the producer call and
  real helper behavior; an AST call alone cannot establish injected-runtime correctness.
- `test_dashboard_graph_cache.py`: retain real newly-filed-finding-to-served-graph test, ledger and
  directory invalidation, stable-cache and missing-read-set cases; add actual import-order and
  supplied-object tests without weakening the production-seeded assertions.
- `test_template_contract.py`: retain real per-tab panel markers, render population and retired
  redirect while adding error-boundary checks for early Flow preparation.
- `tests/e2e/test_operator_panes.py::test_a_non_verdict_cell_is_not_painted_as_a_verdict`: unchanged
  actual browser verification at the existing 30-second navigation timeout, all current assertions.
  Also retain the flow-roster/caveats and tab-reachability checks in applicable broader verification.

Before relying on a new seam test, demonstrate it fails on the original disconnected path or a
controlled regression of that production seam. Use journalled restoration for any production
artifact mutation. No new validation check is planned, so check-registration sites are not added;
if review expands scope to one, derive its registrations via architecture-change before building.

## Routing, evidence and closure

The open finding lives at `papers/AutomatedReviews/2026-10-15-flow-request-graph-reuse/infra.md`.
Run the existing read-only `scripts/orchestrate.py --lane infra --json` after filing it and inspect
its exact finding ID, targets, Verify and dispatch/queue disposition. Do not create a second queue
or treat a capped/overlapping group as dispatched. No finding is closed in this design package.

The source-only review may establish the proposed connection, not a browser speedup. Ask the lead
for a public-safe exact-candidate execution receipt before adding numerical latency claims. Preserve
complete commands, stdout/stderr, return codes and source hashes when the later verification runs.
The finding declares one pytest invocation covering all safety nodes and the unchanged browser
node with `-m ''`; the closure writer's `cwd=PROJECT_ROOT` supplies the checkout. Do not add a
`cd` override or require an inherited `REPO` variable. Prove that selected tests executed rather
than being skipped or deselected; keep actual PG writes disabled during verification.
After independent review and actual verification, closure goes through `scripts/close_finding.py`;
never hand-edit `review_finding_supersessions.json`, declare a waiver or mark a paper stage green.

## Current completion boundary

A is complete at the design level. B and C are implemented with isolated behavioral evidence,
including a real-route controlled-disconnection failure and restored green run. D and E remain
outstanding: the entire finding Verify, unchanged browser obligation, production-seeded invalidation,
independent implementation review, normal closure and broader gates are not satisfied by these
focused tests. No commit, closure or runtime deployment is claimed here.
