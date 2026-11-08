---
kind: focused-computation-validation
target: D1
readiness_gates_version: 1
---

# D1 hierarchy table input binding

## Finding 1 — The numerical validator leaves the labelled hierarchy float

- **Severity:** required
- **Lane:** infra
- **Gate:** ComputationCorrectness
- **Location:** `scripts/validation/checks/physics.py`, `check_d1_hierarchy_table`
- **Observed:** On main-delivery draft ddc320ec the current check passes for the actual inline table. A scratch replay moves those same table bytes behind its direct canonical table input. The check selects the next tabular and reports all three BEC rows missing. The shared draft input closure resolves the intended generated file.
- **Expected:** The existing numerical evaluator checks the rows of the table attached to the hierarchy label and fails closed on missing, wrong or ambiguous inputs. The manuscript crossover evidence and all scientific comparisons remain enforced.
- **Fix:** Bound the reader to the labelled float and consume the existing canonical input closure for its generated table. Preserve the inline form for historical drafts and the current independent recomputation. Exercise the migrated table and exact adverse cases.
- **Verify:** `cd "$REPO" && uv run python -m pytest tests/test_d1_hierarchy_table.py -q && uv run python scripts/validate.py --check d1_hierarchy_table`
