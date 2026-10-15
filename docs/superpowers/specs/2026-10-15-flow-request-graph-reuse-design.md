# Flow request graph reuse — design specification

Status: **Design accepted; implementation present, pending independent implementation review and full verification.**

Governing decisions: `docs/adrs/ADR-019-flow-request-graph-reuse.md` D1–D6.
The scope is the public dashboard's Flow GET path, its existing aggregation helper and their tests.

## Pre-change coverage and gap

`get_cached_graph` already owns rebuilding, locking, captured reads and imported-code fingerprints.
`flow_board` already accepts `by_bundle`, `finding_nodes`, `gate_nodes` and `freshness_findings`.
`load_aggregate` already uses read-only review resolution and `load_freshness` writes no metadata.
`aggregate_by_bundle` already withholds GREEN when P1 gates cannot be computed. The pre-change gap
was that `index` did not supply the graph it has acquired to these consumers; the aggregate's
helper had no graph input. Late reader imports could additionally change the key for a later request.

Both review layers were checked: `docs/architecture/VALIDATION_GATE_TOPOLOGY.md` describes runtime
gates and limits, while `QA_QI_INFRASTRUCTURE_MAP.md` §§1.5/3 and the plugin README distinguish
execution from fresh-context review. Existing `infra` routing and the dashboard template/browser
obligation apply. This proposal adds no gate, reviewer or secondary planner.

## Request data flow (D1–D3)

1. Preserve the retired `?tab=papers` redirect. Resolve the selected tab early without changing
   the default. Import the existing always-used Attention label resolver before common graph
   consumption. For Flow, import its actual reader dependencies before the graph lookup.
2. Acquire the Flow graph with the existing `get_cached_graph` API, under its current lock and
   invalidation rules and configured PG synchronization policy. Keep the object only in this
   request. A graph-build failure is not an empty graph. An enabled `PG_SYNC_ENABLED` policy may
   still schedule the existing sync after a successful rebuild; add no independent PG writer.
   No Lean build or dependency extraction is introduced by graph reuse.
3. Let `load_paper_claims(*, graph=None)` use the borrowed object for this request; omitted input
   retains its existing cache lookup. Other shared loaders retain their existing behavior.
4. Obtain the Flow aggregate with `load_aggregate(graph=graph)`, forwarding the exact same object
   to `aggregate_by_bundle(..., graph=graph)` and `_blocked_p1_gates_by_paper(graph=graph)`.
   `aggregate_by_bundle` retains `review_info` in its current positional slot; new input is
   keyword-only. `graph is None` chooses the fallback, not `graph or build_graph_json()`.
5. Invoke `flow_board(by_bundle=aggregate, gate_nodes=all_gate_nodes)` where `all_gate_nodes` is
   the complete `ReadinessGate` population of that same graph. Do not pass a capped or per-bundle
   slice. Retain the existing full finding loader and freshness reader; reuse does not authorize
   deleting the lane overlay, unclassified population, caveats or manuscript measurements.
6. Preserve the lazy pane error boundary, including preparation/import failures. Do not render an
   empty board, label a failed pane healthy because HTTP status is 200, or leak traceback text.
   Do not build the Attention or Loops data when Flow is selected.

Only request-local references are introduced. No Flask-global retained output, cache key API,
version marker, copied registry or planner is needed. The app supplies `by_bundle` using the
existing board injection rather than making the board import Flask or acquire a cache itself.

## Aggregation semantics (D2, D4)

The optional full graph is a reader input, not a precomputed readiness answer. Continue calling
`readiness_gates.evaluate_all_gates(graph)` and applying the existing blocked-P1 filter. Preserve
all review-kind, claims-review presence, finding-count and source/bundle attribution rules.
The evaluator returns blocked results for individual evaluator exceptions; that remains intact.
A failure of graph acquisition or whole evaluation returns `None` from the downgrade helper,
and the aggregate withholds GREEN with its existing UNVERIFIED reason.

The new injection must not widen the accepted input to an empty/partial surrogate. Reject a
supplied object missing the `nodes`/`links` collections or without Paper nodes through the same
unknown path; do not silently rebuild over that explicit input. The production route passes the
entire graph unchanged, and route tests must prove object identity and population completeness.
Structural checks alone cannot prove an arbitrary external caller supplied the entire corpus;
completeness is a caller contract, guarded at this production seam, not a new graph validator.
A populated, successfully evaluated graph with no blocked P1 gates returns `{}` normally.
Do not change standalone fallback semantics beyond the shared error handling already present.

`flow_board(gate_nodes=[])` remains meaningful: its submission cells are unmeasured. It must not
be confused with omitted `gate_nodes`, which invokes the existing standalone loader. The other
standalone entry points continue to build/evaluate when no graph is supplied.

## Imports and cache validity (D3)

Current source imports `dashboard_attention` after paper loading. Flow's lazy imports reach
`bundle_readiness`, `qi_register`, `check_bundle_source_freshness`, `bundle_json` and
`validation.checks.bundles_readiness`; those modules provide the actual downstream operations.
Move the relevant existing imports to their owning module's ordinary import phase so selecting
Flow makes its readers loaded before borrowing the graph. These names document current source
paths, not a new hand-maintained prewarm allowlist. Verify transitive imports for cycles and
side effects; importing must not run the checks or invoke writers. Keep other panes' data lazy.

Leave `_record_build_reads`, `_loaded_repo_module_sources`, `_graph_fingerprint`, the lock and
cache-publication logic intact. Newly introduced dynamic reader imports remain in the fingerprint
and may legitimately cause a later miss. A stable import closure plus unchanged inputs should
reuse the graph; no absolute claim that every warm navigation builds zero graphs is made.
Do not relabel a snapshot as current by resetting its fingerprint after the route returns.

## Verification contract (D4–D6)

Extend the existing test modules rather than create a parallel harness. Add route tests using the
real `index` and real flow/aggregation path with instrumented graph construction: require that
paper claims and aggregate evaluation see the same full object, that gate injection has the
complete node IDs, and that neither standalone fallback is called for a supplied graph. Rendered
content must include the flow board, coverage and non-verdict cells; HTTP200 alone is insufficient.

Use fresh-process/isolated import state for the first Flow request and stable subsequent request,
so prior imports from the test session cannot make a late-import defect invisible. Record keys
and caller counts around requests. Do not mock `get_cached_graph`, `flow_board` or the aggregate
to return success in the test intended to prove their integration. Narrow dependency fixtures
may control corpus inputs; retain an actual-corpus route/browser leg as the independent backstop.

Exercise both input modes: supplied and omitted graph. Include blocked P1, healthy evaluation,
whole-evaluation failure, individual evaluator exception, explicit empty/malformed graph, empty
gate list, empty findings, empty roster, unrecognized stage values and unattributed findings.
For the supplied failure case assert no rebuilding, `None` at the helper and non-GREEN aggregate;
for the healthy case assert behavior unchanged. Compare the full aggregate result with the
standalone result over the same controlled artifact inputs, ignoring only documented volatile
fields if any are actually present. Assert the borrowed graph is not modified.

Retain `tests/test_dashboard_graph_cache.py::TestTheSeam::test_a_newly_filed_finding_reaches_the_dashboard_graph`
and its production-seeded invalidation through the existing seed journal. Extend existing cache
tests for imported-reader source edits and legitimate first imports, unavailable read set,
unlistable directory, changed ledger and new review directories. Do not seed tracked artifacts
without the journal, weaken its restore assertions, or substitute only a key-comparison test for
the served-graph assertion. Extend `tests/test_dashboard_flow.py`,
`tests/test_readiness_cannot_measure.py` and the existing template contract for the new seam.

Run the finding's exact Verify command after implementation in a suitably prepared candidate.
Use one pytest invocation for all declared safety nodes and the unchanged browser node, with
`-m ''` clearing the default marker exclusions. The closure writer supplies `cwd=PROJECT_ROOT`;
the command must not override that checkout with `cd` or depend on an inherited `REPO` variable.
Record that every selected node actually executed; skip/deselection is not verification.
Its browser leg is the unchanged
`tests/e2e/test_operator_panes.py::test_a_non_verdict_cell_is_not_painted_as_a_verdict`:
`wait_until="load"`, the existing 30-second navigation timeout, all present non-verdict kinds and
the non-vacuity assertion remain. Use the existing `--no-pg-sync` browser fixture and disable PG
sync for test-client verification. Confirm enabled/disabled scheduling policy at its boundary
without a PG connection or write; this does not change the product's configured synchronization.
No timeout, test cap, threshold, floor, skip or assertion relaxation is part of this repair.

A public performance receipt must name the actual candidate, configuration, command, raw result,
request boundaries and graph callers. Instrumented test-client time is not browser TTFB. Neither
a unit suite nor fewer builds establishes that the browser test passes. Applicable broader gates,
independent review, closure-writer evidence and merged-wave acceptance remain separate.

## Boundaries and review questions

The approved source connection and isolated tests are now present; independent implementation
review and full verification remain pending. This specification grants no Lean build, canonical
regeneration, PG operation, metadata rewrite, review closure or stage promotion. ADR-018's source
modification semantics remain untouched.

Independent review must resolve: whether the optional graph seam is the narrowest compatible
extension; whether all imports affecting first-request behavior occur before the borrow without
moving errors outside their boundary; whether failure and empty-input tests can fire through the
actual consumer; and whether any claim exceeds the source evidence. Live readers still run at
different instants; this is not a filesystem transaction or a new scientific-readiness authority.
