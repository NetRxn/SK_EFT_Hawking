# D7 regression must recognize its current source-backed theorem

### 1.1 — 🟡 REQUIRED — Reconcile the D7 citation regression with the current manuscript

- **Severity:** minor
- **Lane:** `infra`
- **Location:** `tests/test_validate_public_surface.py`
- **Verify:** `.venv/bin/python -m pytest tests/test_validate_public_surface.py::TestTexQuoteReferencesAreExtracted -q`

The live D7 regression requires an escaped theorem-name prefix that the manuscript
no longer cites. The current manuscript gives
`analog_hawking_fourCycleFree_demarcation` in a verbatim theorem block, matching
the declaration in `lean/SKEFTHawking/AnalogHawkingDemarcation.lean`. The canonical
Python run at d63e07b9 fails this assertion while the obsolete quantum-advantage
name remains absent. The separate, longer simulability companion declaration
exists; this finding does not assert its nonexistence.

Repair the existing regression to recognize the actual current citation and
its source backing while retaining rejection of the obsolete phantom citation.
Use the existing prose-reference extraction and resolution mechanisms where
applicable. Do not alter the manuscript, Lean source, production validator,
registry or ceilings, or strengthen the physical interpretation. Four-cycle
freeness is a combinatorial screen and does not establish classical simulability.

Record the actual failing baseline, passing repaired class and meaningful
negative checks. Source mutations, if needed, use the existing seeded-mutation
journal in this isolated candidate and restore exact bytes. Closure requires
independent review, ordinary integration and the existing close_finding.py
writer executing Verify. This repair cannot close broader paper-corpus debt.
