# The P9 operator panes have no consumer — 2026-08-13

**Found by** the pre-merge architecture-artifact sync audit, checking whether ADR-012's
recorded phase status matches what is on disk.

**What it is.** `scripts/dashboard_flow.py` (S2, the Flow board), `scripts/dashboard_attention.py`
(S3, Attention) and `scripts/dashboard_loops.py` (D20, the Loops pane) are **2,360 lines whose
only importers are their own test files.** `scripts/provenance_dashboard.py` — the application —
never imports them, no route serves them, and no template renders them. Their tests are green
because they exercise the modules directly.

⚠️ **This is the inverse of the drift this repo usually catches, and it is why every gate is
green.** The normal failure is a document claiming a thing that was never built. Here the thing
*was* built, to a high standard, with real tests — and the wire that makes it reachable was
never run. `validate.py` cannot see it: an unreferenced module is not a broken reference. The
D2 dashboard gates cannot see it either — a template-contract test needs a template, and a
browser test needs a route.

**Why it matters beyond the panes.** D15 states the dashboard "is the operator control surface,
and it ships with the loop." P10 hands the operator a queue that these three panes are the way
to read. Shipping P10 against unreachable panes puts the operator back where D12 says they must
not be: told that a surface exists, with no way to look at it.

## Measured 2026-08-13

| module | lines | importers outside its own test |
|---|---|---|
| `scripts/dashboard_flow.py` | 804 | **0** |
| `scripts/dashboard_attention.py` | 788 | **0** |
| `scripts/dashboard_loops.py` | 168 | **0** |

`grep -rn "dashboard_flow\|dashboard_attention\|dashboard_loops" scripts tests` returns only
`tests/test_dashboard_flow.py`, `tests/test_dashboard_attention.py`,
`tests/test_dashboard_loops.py` and the modules themselves. All three were added in
`3076d031`, a pr-review remediation commit — not in a phase commit of their own, which is how
they reached `main..HEAD` without the ADR ever recording them.

---

## Findings

### 1 — 🟠 Three operator panes are built, tested and unreachable

- **Severity:** major
- **Lane:** infra
- **Gate:** `bundle_readiness` (D15's control surface is a P10 precondition)
- **Location:** `scripts/provenance_dashboard.py`, `scripts/templates/dashboard.html`
- **Observed:** no import, route or template reference to any of the three modules. The app is
  5,693 lines and mentions "flow" only in a comment about stack traces, a legacy dossier flow
  and a v1 code path.
- **Evidence:** the importer table above, measured by grep across `scripts/` and `tests/`.
- **Expected:** each pane reachable from the dashboard, with the two gates D2 requires for
  dashboard work — a template-contract test (the server hands the template the keys it reads)
  and a real browser test driving the rendered page. `tests/e2e/` already boots the app on an
  ephemeral port, so the browser gate is infrastructure that exists and needs cases.
- **Fix:** wire the three panes as P9b/P9c completion. **Not a mechanical fix** — D15 pins the
  columns, feeds and stores and leaves *layout* to be iterated against real use, so this is a
  build with a judgment component, not an obvious repair.
- **Verify:** `uv run python -m pytest tests/e2e -m e2e -k "flow or attention or loops" -q`

### 2 — 🔵 A module with no consumer is invisible to every gate in the suite

- **Severity:** minor
- **Lane:** infra
- **Gate:** `architecture_inventory_fresh`
- **Location:** `scripts/validation/checks/`
- **Observed:** `doc_refs_resolve` catches prose naming a file that does not exist. Nothing
  catches a file that exists and nothing names — the mirror case. `module_census_fresh` walks
  and describes these three modules, so they are *documented*; being documented is not being
  reachable, and the census makes them look more integrated than they are.
- **Evidence:** all three appear in `docs/MODULE_CENSUS.md` with descriptions, and all three
  are dead to the application.
- **Expected:** a check that can distinguish a deliberate library from an orphan — probably
  an allowlisted-entrypoint reachability scan over `scripts/`, on the same shape as the Lean
  reachability ratchet, which already answers exactly this question for `.lean` files.
- **Fix:** design under the `architecture-change` skill; the Lean leg is the worked precedent.
  ⚠️ **A naive "is it imported anywhere" scan would flag every CLI entrypoint**, so the
  population predicate is the whole difficulty and must be measured before the check is built.
- **Verify:** `uv run python scripts/validate.py --check architecture_inventory_fresh`
