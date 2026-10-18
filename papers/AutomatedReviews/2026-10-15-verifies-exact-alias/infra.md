# Exact Lean-name collisions bypass module-alias exclusion

### 1.1 — 🟡 REQUIRED — Exclude module aliases before every Lean lookup

- **Severity:** major
- **Lane:** `infra`
- **Location:** `scripts/build_graph.py::extract_verifies_edges`; `tests/test_verifies_alias_guard.py`
- **Verify:** `uv run python -m pytest -m '' tests/test_verifies_alias_guard.py -q -s`

An exact `lean:{raw}` match runs before the module-alias test. An imported Python
module alias such as `pi` can therefore fabricate a Lean coverage edge despite the
same exclusion applying to short lookup. Dotted exact matches have the same bypass.
The live guard also rejects mixed references even when a genuine reference supports
the emitted edge, and its attribution must honor complete earlier-index priority.

Repair the existing ordering and independent existential support assertion under the
accepted design and plan. Verify runs persistent collision, priority, ambiguity,
production-seed/mutant, frozen paired corpus and actual consumer controls, writes full
records under pytest tmp_path, and prints paths and hashes. Evidence is recorded by
the assigned author; passing focused checks is not whole-project acceptance.
Closure remains pending independent review, normal scoped commit/integration and the
single `close_finding.py` writer. Broader existing failures remain unwaived.
