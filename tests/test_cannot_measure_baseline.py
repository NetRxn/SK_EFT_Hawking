"""ADR-009 §Deferred item 4 — freeze the "cannot measure ⇒ PASS" population.

THE PATTERN THIS RATCHETS
-------------------------
`QA_QI_INFRASTRUCTURE_MAP.md` §7 names the systemic defect: **absence of
measurement rendered as success.** A check that cannot reach its input returns
`passed=True`, and a green suite then carries no information — which is how the
2026-08-01 run reported 58 of 59 passing on a portfolio the concurrent audit found
unsubmittable.

Item 4 was filed as "add an `UNEVALUATED` result state". That remedy is DECLINED
(ADR-009 §Deferred item 4): `CheckResult.passed` is D2 contract item 5 — the
`--json` payload, `gate_precheck.py` and `pre-commit-sync.sh` all read it — so a
third state is a contract break. What CAN be closed is the *generator*: stop the
population growing silently.

MEASURED 2026-08-04 across the 59 checks — 60 cannot-measure return sites:
**35 FAIL (58%, already converted) and 25 PASS**, the latter collapsing to the
22 (check, kind) pairs frozen below.

WHY A BASELINE RATHER THAN A FIX
--------------------------------
The 22 are not uniformly defects, and converting them wholesale would be the
"unify by refactor" that ADR-009 H4 forbids:

* Some are legitimately *optional toolchain absent* — `notebook_exec` (nbclient),
  `bibitem_title_primary_source` (pdfminer), `bundle_figure_integrity` (kaleido),
  `notebook_stored_outputs_current`, `tracked_hypotheses_fresh`. Failing a build
  because an optional dependency is missing is its own defect.
* Three are **advisory by design**, dispositioned individually in §Deferred item 3
  and deliberately kept: `elaboration_knob_watchlist`, `paper_toolchain_pin_drift`,
  `inventory_index_autogen_fresh`.
* Eight are the **H4 `lean_deps.json` divergence**, marked `TODO(semantic-review)`
  in-tree and explicitly preserved so it stays visible rather than being erased.
* Two are annotated in-body as the **H1-silent** sites where a retargeted path
  anchor would go unnoticed: `accepted_findings_carry_rationale` (missing ledger)
  and `citation_primary_sources_present`'s duplicate-key guard.

So the honest move is to make the population explicit and *bounded*: every entry
is a decision on the record, and a NEW silent PASS fails this test until someone
adds it deliberately. Same idiom as `VACUOUS_STATEMENT_BASELINE`,
`NATIVE_DECIDE_DECL_CLOSURE_CEILING` and `COUNT_LITERAL_CEILING`.

THE BASELINE IS FROZEN HERE, NOT COMPUTED FROM PRODUCTION — the same reasoning as
`EXPECTED_CHECKS` in `test_validate_registry_contract.py` and `EXPECTED_SURFACE` in
`test_validate_public_surface.py`: a test that derives its expectation from the
thing under test asserts nothing.

⚠️ TWO LAYERS ARE OUT OF THIS TEST'S SCOPE — neither returns a `CheckResult`, so
this scanner cannot see them. Both were CLOSED by `5228ed6d` on 2026-08-04:
`readiness_gates.evaluate_all_gates` now records an evaluator exception as
`state='blocked'` (it was `'open'`, which `paper_aggregate_state` maps to YELLOW,
not RED), and `bundle_readiness._blocked_p1_gates_by_paper` now returns `None`
rather than `{}` so `aggregate_by_bundle` withholds GREEN when the gates could not
be computed. Their own guard is `tests/test_readiness_cannot_measure.py`.
(This paragraph described both as live defects until 2026-08-04 — audit finding
QI-20; the fix landed after this docstring was written.)

MUTATION-VERIFIED 2026-08-04, both directions:
  * add a new `except: return CheckResult(passed=True, ...)` to a check
        -> test_no_new_silent_pass FAILS
  * convert a baselined site to `passed=False` without updating the baseline
        -> test_baseline_has_no_stale_entries FAILS
Clean negative control: unmutated tree, both pass.
"""
from __future__ import annotations

import ast
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
CHECKS_DIR = SK_ROOT / "scripts" / "validation" / "checks"

#: Calls whose presence in an `if` test marks it as a missing-input guard.
_PRESENCE_CALLS = frozenset({
    "exists", "is_file", "is_dir", "lean_deps_present", "counts_present", "which",
})

#: (check name, branch kind) pairs that return `passed=True` when the check
#: could not measure. FROZEN 2026-08-04. Adding an entry is a decision: say in
#: the check's own body why absence is not a failure there.
CANNOT_MEASURE_PASS_BASELINE = frozenset({
    ('accepted_findings_carry_rationale', 'missing-input'),
    ('axiom_closure_allowlist', 'exception'),
    ('axiom_closure_allowlist', 'missing-input'),
    ('bibitem_title_primary_source', 'exception'),
    ('bundle_figure_integrity', 'exception'),
    ('count_literals', 'missing-input'),
    ('disclosure_consistency', 'missing-input'),
    ('elaboration_knob_watchlist', 'missing-input'),
    ('formula_grounding', 'missing-input'),
    ('inventory_index_autogen_fresh', 'exception'),
    ('lean_docstring_refs_resolve', 'missing-input'),
    ('nogo_substrate_integrity', 'missing-input'),
    ('notebook_exec', 'exception'),
    ('notebook_stored_outputs_current', 'exception'),
    ('numerical_literals', 'missing-input'),
    ('paper_toolchain_pin_drift', 'exception'),
    ('placeholder_not_cited', 'missing-input'),
    ('proxy_body_audit', 'missing-input'),
    ('review_severity_declared', 'missing-input'),
    ('tracked_hypotheses_fresh', 'exception'),
    ('tracked_hypothesis_ledger', 'missing-input'),
    ('vacuous_statement_audit', 'missing-input'),
})


def _returned_passed(node: ast.AST):
    """`return CheckResult(passed=<literal>, …)` → the literal, else None."""
    if not isinstance(node, ast.Return) or not isinstance(node.value, ast.Call):
        return None
    if getattr(node.value.func, "id", "") != "CheckResult":
        return None
    for kw in node.value.keywords:
        if kw.arg == "passed" and isinstance(kw.value, ast.Constant):
            return kw.value.value
    return None


def scan_cannot_measure_sites() -> dict[tuple[str, str], bool]:
    """Map (registered check name, branch kind) → the literal `passed` value.

    Two branch kinds, both syntactic so the scan cannot drift into judgement:
      * ``exception``     — a `return CheckResult(...)` inside an `except` handler.
      * ``missing-input`` — a `return CheckResult(...)` inside an `if` whose test
        calls one of `_PRESENCE_CALLS` (an artifact/toolchain availability probe).
    """
    found: dict[tuple[str, str], bool] = {}
    for path in sorted(CHECKS_DIR.glob("*.py")):
        tree = ast.parse(path.read_text())
        for fn in (n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)):
            name = next(
                (d.args[0].value for d in fn.decorator_list
                 if isinstance(d, ast.Call)
                 and getattr(d.func, "id", "") == "register_check"),
                None,
            )
            if not name:
                continue
            for handler in (n for n in ast.walk(fn) if isinstance(n, ast.ExceptHandler)):
                for node in ast.walk(handler):
                    val = _returned_passed(node)
                    if val is not None:
                        found[(name, "exception")] = val or found.get((name, "exception"), False)
            for branch in (n for n in ast.walk(fn) if isinstance(n, ast.If)):
                calls = {
                    getattr(c.func, "attr", "") or getattr(c.func, "id", "")
                    for c in ast.walk(branch.test) if isinstance(c, ast.Call)
                }
                if not (calls & _PRESENCE_CALLS):
                    continue
                for stmt in branch.body:
                    for node in ast.walk(stmt):
                        val = _returned_passed(node)
                        if val is not None:
                            key = (name, "missing-input")
                            found[key] = val or found.get(key, False)
    return found


def _pass_sites() -> set[tuple[str, str]]:
    return {k for k, v in scan_cannot_measure_sites().items() if v is True}


class TestCannotMeasureBaseline:

    def test_scanner_finds_the_population(self):
        """Guard the seam: if the scanner silently matched nothing, both
        assertions below would pass vacuously."""
        sites = scan_cannot_measure_sites()
        assert len(sites) >= 30, (
            f"the AST scan found only {len(sites)} cannot-measure sites across "
            f"{CHECKS_DIR}; it matched almost nothing, so the ratchet below is "
            f"vacuous. Did the check modules move, or `CheckResult` get aliased?"
        )
        assert any(v is False for v in sites.values()), (
            "no FAIL-on-cannot-measure site was found, yet the readiness family "
            "is known to fail on cannot-measure. The scan is not seeing real code."
        )

    def test_no_new_silent_pass(self):
        """FIRES on a seeded defect — a NEW check that returns PASS when it could
        not measure."""
        new = sorted(_pass_sites() - CANNOT_MEASURE_PASS_BASELINE)
        assert not new, (
            f"{len(new)} check(s) newly return `passed=True` on a branch where they "
            f"could not measure: {new}.\n"
            "This is the pattern QA_QI_INFRASTRUCTURE_MAP §7 exists to stop — a green "
            "verdict that carries no information. Prefer FAIL-on-cannot-measure (the "
            "readiness family is the template). If absence genuinely is not a failure "
            "here, say why in the check body and add the pair to "
            "CANNOT_MEASURE_PASS_BASELINE in the same commit."
        )

    def test_baseline_has_no_stale_entries(self):
        """FIRES in the other direction — a site converted to FAIL (good) that
        nobody removed from the baseline, which would leave the ratchet slack."""
        stale = sorted(CANNOT_MEASURE_PASS_BASELINE - _pass_sites())
        assert not stale, (
            f"{len(stale)} baselined site(s) no longer return PASS on cannot-measure: "
            f"{stale}.\nThat is progress — remove them from "
            "CANNOT_MEASURE_PASS_BASELINE so the ratchet tightens instead of leaving "
            "headroom for a new silent PASS to be filed in their place."
        )
