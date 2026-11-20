# ADR-019 — Reuse the current graph within a Flow request

Status: **Implementation independently reviewed and finding closed after required scoped verification; broader gates and merged-wave acceptance pending.**

## Context and source evidence

The dashboard already owns a read-set-aware graph cache. The Flow board already accepts
`by_bundle` and `gate_nodes` inputs. Reuse these contracts rather than introduce another cache.

Source inspection on 2026-10-15 at `996c84324ebf939af8854e5226771de344b452d9` establishes:

- `scripts/provenance_dashboard.py:689` calls `get_cached_graph()` from `load_paper_claims`.
  `index` loads those claims before importing the Attention label resolver and the selected pane.
  `_graph_fingerprint` includes both captured data reads and currently imported repository code.
  Importing additional readers after the lookup can legitimately change the next lookup's key.
- `index:1403` invokes `flow_board()` without its existing injected inputs.
  `scripts/dashboard_flow.py:222` therefore constructs a graph for `load_gate_nodes`.
- `dashboard_flow.load_aggregate` calls `aggregate_by_bundle`; its
  `_blocked_p1_gates_by_paper` helper constructs another graph and evaluates the P1 downgrade.
  This evaluation prevents finding-only aggregation from issuing GREEN over a blocked gate.
- The selected pane runs synchronously before `render_template`. Standalone fallbacks are useful;
  the cache rebuild is legitimate on changed inputs. These are distinct causes, not a claim that
  every graph build is redundant.

These are historical call-path observations at the named base, not a timing measurement of this candidate.
A public execution receipt with exact source identity, command, streams and graph-build caller
counts is required before publishing latency figures or claiming a speedup. No numeric browser
or profiler result is asserted here. The finding's existing browser verification remains binding.

## Decisions

**D1 — One request borrows one current graph.** For a Flow request, the app obtains the graph
through `get_cached_graph`, then supplies that same object to paper-claim loading and aggregation.
Pass its complete `ReadinessGate` population through the existing `flow_board(gate_nodes=...)`
input, and the resulting aggregation through `by_bundle=...`. No filtered replacement graph,
new retained graph, time-to-live cache, epoch, global output memo or direct `_GRAPH_CACHE` read.
Other tabs and standalone callers retain their current behavior.

**D2 — Extend the existing aggregation chain.** Add a keyword-only optional `graph` argument
through `dashboard_flow.load_aggregate`, `bundle_readiness.aggregate_by_bundle` and
`_blocked_p1_gates_by_paper`. Add the same optional borrowed input to `load_paper_claims` so the
route need not look up the graph again. `None` means use the existing standalone loader; a
supplied object is never replaced using truthiness. Retain `review_info` and its positional
compatibility. The helper still runs `evaluate_all_gates` against the full graph, preserving its
exception handling and P1 selection; do not replace evaluation with a hand-derived verdict map.
Supplied graph absence, malformed structure or no Paper population must not become a successful
empty downgrade map. Report inability to evaluate through the existing `None`/UNVERIFIED path.
A successfully evaluated population with no blocked P1 gates can still return `{}`.

**D3 — Make import ordering honest without weakening the key.** Resolve the existing Attention
label import before the common graph lookup. For Flow, resolve its readers before acquiring the
borrowed graph, including the imports used by aggregation, freshness and manuscript measurement.
Prefer moving the actual existing imports to their owning module's import phase over maintaining
a second list of names to prewarm. Do not execute data loading, validation runs, writers or graph
builds merely to import them. Preserve pane-import failure as an explicit pane error. A newly
loaded reader, changed file, new review directory, unavailable read set or unlistable directory
must still invalidate through the existing fingerprint. Never overwrite the stored key after
rendering to make it match code the graph was not built against.

**D4 — Preserve truth and ownership.** Borrowed inputs are read-only; no graph mutation or
readiness semantics change. Keep the complete finding extraction, lane overlay, coverage,
freshness checks, roster, caveats and non-verdict vocabulary. Empty gate nodes still mean
unmeasured, not green. Empty roster/findings still raise. An evaluator crash remains blocked;
an uncomputable aggregate downgrade remains `None`, withholding GREEN. No metadata backfill,
closure, stage change, Lean dependency extraction, Lean build or manuscript compilation on this
route. Legitimate full graph reconstruction on a cache miss remains available. Preserve the
existing configured PG synchronization through `get_cached_graph`: its default follows
`PG_SYNC_ENABLED`, and an enabled policy schedules the existing sync after a successful rebuild.
Add no independent PG writer and do not force synchronization off in the product as part of reuse.
Browser verification uses the existing `--no-pg-sync` fixture; test-client verification disables
PG sync, and policy tests intercept scheduling without connecting or writing to PG.

**D5 — Verify the actual consumer and its failure directions.** Extend existing route/cache and
readiness tests, retain production-seeded cache invalidation, and run the unchanged
`tests/e2e/test_operator_panes.py::test_a_non_verdict_cell_is_not_painted_as_a_verdict` at its
existing 30-second navigation timeout. A lower build count does not certify CSS, full coverage,
readiness or browser latency. No timeout, population floor, threshold, cap or assertion relaxation.

**D6 — Review and close through the existing process.** Route the finding through
`scripts/orchestrate.py`; only the existing closure writer closes it after actual verification
and independent implementation review. A plan, successful focused tests or a local commit is
not merged-wave acceptance.

## Overlap reconciliation

ADR-012 continues to own finding routing, closure and the operator panes; this extends its input
injection seams. ADR-011's evidence-kind and cannot-measure guards remain unchanged. ADR-018
continues to own source-tree-relative modification paths; request reuse passes the existing
freshness reader through unchanged and neither supersedes that publication change nor reuses its
ADR number. ADR-008's resource controller and ADR-017's continuity contract gain no new role.
The validation topology and reviewer/execution rosters already cover this infra-lane work. No
new check, gate, reviewer, plugin surface, registry or routing ledger is proposed.

## Plan, alternatives and consequences

The specification is `docs/superpowers/specs/2026-10-15-flow-request-graph-reuse-design.md`;
the task map is `docs/superpowers/plans/2026-10-15-flow-request-graph-reuse.md`. Implement the
route and aggregation connection as one coherent change after review; a gate-only injection
leaves the independent aggregation build in place.

Rejected: increasing browser timeouts; removing readiness evaluation; serving empty gates;
filtering imported code out of the fingerprint; stamping a new key after consumption; another
cache; a fixed roster of files to invalidate. Reusing cached gate-node metadata as the aggregate's
verdict would also change its evaluator contract, so retain actual evaluation for this bounded fix.

Expected benefit is avoiding independent reconstruction when the route already holds a current
graph. A legitimately cold or changed tree can still require a full build. Reader imports may
have startup cost; their ordering must not move failures outside the pane's error boundary.
Borrowing a graph does not make all later filesystem reads an atomic snapshot or certify a whole
repository. Those limits remain explicit in the spec and verification.

## Implementation status

The three-module connection and isolated behavioral tests are present. The real route/cache/board/
aggregate seam has a controlled-disconnection negative control. Independent implementation review
and the complete finding Verify passed, including the unchanged browser and production-seeded
invalidation checks. The supported writer closed the finding. Broader verification remains red
on existing publication debt; the stale architecture census was regenerated through its owner.
Merged-wave acceptance remains open. No latency improvement is claimed.
