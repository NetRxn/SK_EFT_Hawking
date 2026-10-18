---
paper: infra
bundle: infra
bundle_target: infra
review_date: 2026-10-15
kind: targeted-infra
readiness_gates_version: 1
---

# Flow request repeats full graph construction across existing reader seams

ADR-019 implementation is independently reviewed. The required scoped verification passes in
the built checkout, including the unchanged browser and production-seeded cache checks. The
supersession ledger supplies closure status; broader gates and merged-wave acceptance remain separate.

### 1.1 — MAJOR — Flow does not reuse the current graph across its gate and aggregation readers

- **Severity:** major
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `scripts/provenance_dashboard.py`, `scripts/dashboard_flow.py`, `scripts/bundle_readiness.py`, `tests/test_dashboard_flow.py`, `tests/test_readiness_cannot_measure.py`, `tests/test_dashboard_graph_cache.py`, `tests/test_template_contract.py`
- **Verify:** `.venv/bin/python -m pytest -m '' tests/test_dashboard_flow.py tests/test_readiness_cannot_measure.py tests/test_d5_bundles_readiness.py::TestProducerDemotesGreenOnBlockedP1 tests/test_dashboard_graph_cache.py tests/test_template_contract.py tests/e2e/test_operator_panes.py::test_a_non_verdict_cell_is_not_painted_as_a_verdict -q`
- **Observed:** Source inspection at `996c84324ebf939af8854e5226771de344b452d9` on 2026-10-15 shows `index` loading paper claims through `get_cached_graph` and then invoking `flow_board()` without injected inputs. `load_gate_nodes` calls `build_graph_json()`; independently `load_aggregate` reaches `_blocked_p1_gates_by_paper`, which builds another graph before evaluating the P1 downgrade. These synchronous operations precede rendering. The cache may also rebuild legitimately after the route imports additional readers following its lookup.
- **Evidence:** `scripts/provenance_dashboard.py:407,488,689,1309,1395,1403`; `scripts/dashboard_flow.py:222,233,696`; `scripts/bundle_readiness.py:444,487,503`. At that base the existing gate-node and by-bundle injections were present but unused at this route. `_graph_fingerprint` includes imported repository modules, so moving imports is distinct from bypassing invalidation. No public exact-candidate timing receipt is attached; source proves the calls, not their latency or a browser result. Obtain a public-safe command/streams/source-bound measurement before publishing such figures.
- **Expected:** A Flow request holding a current complete graph supplies it to its consumers through existing injection seams. Independent standalone calls retain their loaders. Full gate evaluation, P1 downgrade, complete findings/coverage and unmeasured/error states remain intact. The actual non-verdict browser test above must finish with its original 30-second navigation timeout and every current assertion unchanged.
- **Fix:** Implemented ADR-019 D1–D5 extends optional graph input through the existing aggregation chain and paper-claim loader; supplies complete gate nodes and aggregate to `flow_board`; orders actual reader imports before acquiring the graph. Keep real evaluation, reject empty/malformed supplied surrogates as unverified, preserve None versus evaluated-empty mapping, and add meaningful route/cache/failure tests. Gate-only injection leaves the aggregation rebuild unresolved.
- **Verification limits:** The Verify command is executed by the closure writer; its recorded result is scoped to that run. It runs in the checkout supplied by the closure writer (`cwd=PROJECT_ROOT`) without an environment-dependent directory override. The single invocation clears marker exclusions; every selected test must execute, not skip or deselect. Use the existing `--no-pg-sync` browser fixture and disabled PG sync for test-client verification; test configured scheduling without connecting or writing to PG. The added isolated checks exercise the real route/cache/board/aggregate path, including controlled disconnection; they do not substitute for this complete command. Never increase timeout, alter wait_until, skip kinds, cap findings/gates, relax thresholds/assertions, suppress imported-code fingerprints or replace errors with empty panels. Broader gates and independent implementation review remain required.
- **Cache:** Retain the sole dashboard cache and its actual read-set, imported-source and ancestor-directory key, including forced misses on unavailable observations. Preserve the cache owner's configured PG synchronization and add no independent PG writer. Legitimate graph reconstruction remains available; graph reuse adds no Lean build or dependency extraction. No new retained cache, metadata writer, stage mutation or closure is part of this repair.
