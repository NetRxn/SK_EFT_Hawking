# Canonical module backing IDs are rejected by the existing resolver

### 1.1 — REQUIRED — Resolve existing canonical module IDs without declaration fallback

- **Severity:** major
- **Lane:** `infra`
- **Location:** `scripts/build_graph.py` existing declaration/module lookups and their canonicalizer/edge consumers
- **Verify:** `.venv/bin/python -B -m pytest tests/test_chain_canonicalize.py tests/test_d5_reviews.py::TestChainBackingTargetsResolve -q`

At f997cff0 the existing resolver rejects fourteen links that already name
exact module IDs present in its own current node set. The shared module helper
prepends another namespace/prefix. Its declaration-first caller can also
misinterpret an explicit module ID as a short declaration name. The complete
explicit-ID pilot and source call chain are recorded in
docs/audits/2026-10-25-njl-qualification-dependencies/CHAIN_RESOLUTION_SPEC.md.

Repair the existing shared module lookup and typed-ID dispatch in both the
canonicalizer and graph-edge path under the established closed BACKED_BY
target contract. Preserve unknown/typed-ID refusal, including unique and ambiguous declaration
suffix collisions with no declaration suggestions, and declaration/unprefixed
module compatibility, all historical review bytes, all original scientific
BUILD obligations and all required gates. Measure both canonical resolution
and actual graph edges; preserve the complete population before lowering the
existing ceiling. No new resolver, check, graph type or scientific result is
authorized.

Owner ROOT, NJL qualification dependency. Independent acceptance reviewer:
`njl_dependencies_whole_review`. Required acceptance: prior independent proposal
review, actual failing-before/passing-after controls, production fault and exact
restoration through the existing journal, complete affected tests, broad fast
qualification with all failures disclosed, and complete independent source and
evidence review before the existing closure writer. This finding is not any
original scientific or publication finding closure.
