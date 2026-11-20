# Native inventory and process census

These findings concern SOURCE accounting defects. The bounded source package is independently reviewed; actual integration, current source verification and closure are recorded separately through the existing process. The observations below describe the earlier source behavior.

Native eligibility, client RPC completion, known-owner identity, loaded runtime and matching-lease MCP admission remain separate pending gates in the [native-domain design](../../../docs/superpowers/specs/2026-10-12-lean-native-domain-census-design.md), [ADR-008](../../../docs/adrs/ADR-008-shared-lean-slot-control-plane.md) and [operator guide](../../../docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md). Passing source controls does not establish live quiescence, permit unknown process adoption or certify backend admission.

## Findings

### 1 — Linked checkouts are counted as primary inventory domains

- **Severity:** major
- **Lane:** infra
- **Gate:** ADR-008 lifecycle SOURCE integration
- **Location:** `scripts/lean_slots/supervisor.py`, `tests/test_lean_lifecycle_observation.py`
- **Observed:** `_role_inventories` excludes only configured physical worktree roots. An ordinary linked Git checkout carrying the same inventory resolves another repository domain and produces a conflict against its primary.
- **Expected:** Exclude a secondary checkout only after capable, bounded Git observations prove its relationship to a resolved canonical primary. Keep independent primary domains, supported aliases and unavailable identity evidence visible.
- **Fix:** Implement ND1 in the native-domain design and preserve the complete lifecycle observation contract.
- **Verify:** `.venv/bin/python3 -m pytest tests/test_lean_lifecycle_observation.py -q`

### 2 — Project-only parent matching miscounts one service tree

- **Severity:** major
- **Lane:** infra
- **Gate:** ADR-008 lifecycle SOURCE integration
- **Location:** `scripts/lean_slots/supervisor.py`, `tests/test_lean_lifecycle_observation.py`
- **Observed:** `capacity_census` chooses roots by direct parents within project-text rows. Generic Lake and Lean intermediates break that relation, so project workers below one service root are counted as additional roots.
- **Expected:** Follow full capable process ancestry before selecting project roots. Distinct project services sharing a nonproject ancestor remain distinct. Unavailable or malformed ancestry reserves capacity.
- **Fix:** Implement ND2 and the NC controls in the native-domain design, retaining unknown occupancy and stored descendant guards.
- **Verify:** `.venv/bin/python3 -m pytest tests/test_lean_lifecycle_observation.py -q`
