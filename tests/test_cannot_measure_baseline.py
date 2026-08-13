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

MEASURED 2026-08-04 across the 59 checks then registered (80 today) — 60 cannot-measure return sites:
**35 FAIL (58%, already converted) and 25 PASS**, the latter collapsing to the
22 (check, kind) pairs frozen below.

WHY A BASELINE RATHER THAN A FIX
--------------------------------
The 22 are not uniformly defects, and converting them wholesale would be the
"unify by refactor" that ADR-009 H4 forbids:

* Some are legitimately *optional toolchain absent* — `notebook_exec` (nbclient),
  `bibitem_title_primary_source` (pdfminer), `bundle_figure_integrity` (kaleido),
  `notebook_stored_outputs_current`. Failing a build because an optional dependency
  is missing is its own defect.

  ⚠️ `tracked_hypotheses_fresh` WAS on that list and did not belong there (removed
  2026-08-05, PR-review R4-I4). `render_tracked_hypotheses` is a first-party module
  in `scripts/`, not an optional dependency, and its handler was a bare
  `except Exception` returning PASS — so an import-time `AssertionError` from
  `constants.py`'s Aristotle-count assert greened the hypothesis-drift gate. An
  optional-toolchain exemption had been extended to a first-party import.
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
    # Added 2026-08-06 with the two post-QA-assessment guards. Both pass-on-absence
    # branches carry `measured=False`, so they stop counting as evidence rather than
    # manufacturing one — and in BOTH checks the substantive absence is a hard FAIL,
    # not a pass: `lean_zero_sorry` FAILS when counts.json exists but has lost the
    # `sorry_declarations` field (a dropped field must not read as zero), and
    # `gate_edge_types_are_emitted` FAILS on any undisclosed dead edge type. What
    # passes here is only the case where the FILE the check reads is absent entirely,
    # which is an environment fact, not a verdict about the tree.
    # The one branch where the DERIVATION itself is impossible: no generator script, so
    # there is nothing to compare the census against. A missing or hand-edited census is a
    # hard FAIL, not this.
    ('architecture_inventory_fresh', 'missing-input'),
    ('gate_edge_types_are_emitted', 'missing-input'),
    ('lean_zero_sorry', 'exception'),
    ('lean_zero_sorry', 'missing-input'),
    ('accepted_findings_carry_rationale', 'missing-input'),
    ('axiom_closure_allowlist', 'exception'),
    ('axiom_closure_allowlist', 'missing-input'),
    ('bibitem_title_primary_source', 'exception'),
    ('bundle_figure_integrity', 'exception'),
    ('count_literals', 'missing-input'),
    ('disclosure_consistency', 'missing-input'),
    ('elaboration_knob_watchlist', 'missing-input'),
    ('formula_grounding', 'missing-input'),
    # Added 2026-08-13 with `existential_witness_disclosure`. Same two inputs as
    # `formula_grounding` and `vacuous_statement_audit` above (formulas.py +
    # lean_deps.json) and the same reasoning: absence carries `measured=False`, so
    # it stops counting as evidence rather than manufacturing one. Its SUBSTANTIVE
    # empty case is a hard FAIL, not a pass — an empty population trips the seam
    # guard and reports UNVERIFIED.
    ('existential_witness_disclosure', 'missing-input'),
    # ('inventory_index_autogen_fresh', 'exception') REMOVED 2026-08-13 — the check
    # gained blocking narrative legs, so an unimportable/raising generator now warns
    # on one leg while the other two still measure and can fail. Removed rather than
    # left stale, so the ratchet tightens instead of holding a slot open.
    ('lean_docstring_refs_resolve', 'missing-input'),
    ('nogo_substrate_integrity', 'missing-input'),
    ('notebook_exec', 'exception'),
    ('notebook_stored_outputs_current', 'exception'),
    ('numerical_literals', 'missing-input'),
    ('paper_toolchain_pin_drift', 'exception'),
    ('placeholder_not_cited', 'missing-input'),
    ('proxy_body_audit', 'missing-input'),
    ('review_severity_declared', 'missing-input'),
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
        # ⚠️ RAISED 30 -> 54 on 2026-08-05 (PR-review pass 2, R2). Measured live
        # population: **54** (check, kind) pairs. A floor of 30 left **44 % headroom**
        # — a ratchet with slack cannot fire, which is the same defect the ratchets
        # themselves exist to prevent, sitting in the guard that protects them.
        # Zero headroom: if the population legitimately shrinks, LOWER this in the
        # same commit and say why.
        # ⚠️ RE-PINNED 54 -> 62, 2026-08-10. The population grew by 8 on this
        # branch and the floor was not moved with it — 13% headroom in the very
        # file whose subject is floors with headroom. Measured live: 62.
        assert len(sites) >= 62, (
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


# ══════════════════════════════════════════════════════════════════════════
# `measured=False` coverage — PR-review pass 2
# ══════════════════════════════════════════════════════════════════════════

import re as _re

#: A return whose own detail text says it skipped. If a check tells the reader it
#: could not measure, it must tell `--ci`'s coverage floor and `_memo` the same
#: thing — otherwise the floor counts it as evidence and the memo caches it.
#: ⚠️ WIDENED 2026-08-09. The list is a prose heuristic and it missed a live site:
#: `freshness.py`'s nbclient guard says "unavailable … skipping", and NONE of the
#: seven original words matched, so a branch that executed no notebook reported a
#: measurement and the scanner never looked at it. Every word added here is one a
#: real cannot-measure branch was found using — ⚠️ EXCEPT `cannot` and `no such`,
#: which have ZERO hits across the population THIS SCANNER SEES (`passed=True`
#: returns) and are
#: SPECULATIVE. Measured 2026-08-09 after round 4 called the claim out: `skipping`
#: 4 hits, `unavailable` 1, `cannot` 0, `no such` 0 (and the original `missing` is
#: now 0 too). Speculative entries are kept — they cost nothing and a heuristic
#: that only matches yesterday's wording is the reason this list needed widening —
#: but the sentence claiming all of them were observed was false and is corrected.
#:
#: ⚠️ THE REAL FIX IS STRUCTURAL, not lexical, and it is now possible: `Detail`
#: carries `measured`, so a future pass should require every cannot-measure branch
#: to construct `Detail(..., measured=False)` and assert on THAT rather than on
#: what the message happens to say. Tracked for goal 2; widening the list is the
#: stopgap that closes today's hole.
_SKIP_WORDS = _re.compile(
    r"SKIPPED|skipping|not found|absent|unavailable|not installed|missing"
    r"|unreadable|could not|cannot|no such", _re.IGNORECASE)


def _self_declared_skips():
    """(file, line, check, declares_measured_False) for every `passed=True` return
    whose text says it skipped."""
    out = []
    for path in sorted(CHECKS_DIR.glob("*.py")):
        src = path.read_text()
        tree = ast.parse(src)
        for fn in (n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)):
            name = next(
                (d.args[0].value for d in fn.decorator_list
                 if isinstance(d, ast.Call) and getattr(d.func, "id", "") == "register_check"),
                None)
            if not name:
                continue
            for node in ast.walk(fn):
                if not isinstance(node, ast.Return) or not isinstance(node.value, ast.Call):
                    continue
                if getattr(node.value.func, "id", "") != "CheckResult":
                    continue
                kws = {k.arg: k.value for k in node.value.keywords}
                p = kws.get("passed")
                if not (isinstance(p, ast.Constant) and p.value is True):
                    continue
                seg = ast.get_source_segment(src, node.value) or ""
                if not _SKIP_WORDS.search(seg):
                    continue
                m = kws.get("measured")
                declares = isinstance(m, ast.Constant) and m.value is False
                out.append((path.name, node.lineno, name, declares))
    return out


class TestSelfDeclaredSkipsDeclareMeasuredFalse:
    """⚠️ PR-review pass 2. `CheckResult.measured` exists because nothing could
    distinguish "measured and passed" from "could not measure, so said PASS" — a
    gap that made BOTH guards built on it blind (`--ci`'s floor could not fire;
    `_memo` cached a `SKIPPED — lake not found` verdict and replayed it after the
    toolchain returned).

    Annotating the sites is only half the fix. Without this test the next
    fail-open branch lands unannotated and the floor silently loses a check —
    which is precisely how the population being ratcheted here got out of step in
    the first place (the older AST scanner sees 21 (check,kind) pairs against 47
    literal `passed=True` returns).
    """

    def test_the_scan_finds_a_real_population(self):
        """Guard the seam: a scanner matching nothing makes the assertion below
        pass vacuously — the exact failure this file exists to prevent."""
        sites = _self_declared_skips()
        # ⚠️ RE-PINNED 15 -> 30, 2026-08-10. Live population is 30, so this sat
        # at **100% headroom**: half the corpus could vanish and it stayed green.
        #
        # ⚠️ RE-PINNED 30 -> 28, 2026-08-13, and the REASON is what makes it
        # legitimate. `inventory_index_autogen_fresh` gained two blocking narrative
        # legs, so its two `passed=True, measured=False` early returns — the whole
        # check was advisory — became warning Details inside a check that now
        # measures and can fail. Both sites were verified gone from that check
        # specifically, not merely absent from a smaller total. A population that
        # shrank because the code genuinely lost the sites is legitimate; one that
        # shrank because the scanner rotted is the defect this floor catches, and
        # the two are indistinguishable from the count alone.
        assert len(sites) >= 28, (
            f"only {len(sites)} self-declared skip sites found; the scan is not "
            f"seeing real code (did `CheckResult` get aliased, or the modules move?)")

    def test_every_self_declared_skip_declares_measured_False(self):
        """FIRES ON A SEEDED DEFECT: add a `return CheckResult(passed=True,
        details=[Detail(..., 'SKIPPED — no toolchain')])` without `measured=False`
        and this fails."""
        missing = [(f, ln, n) for f, ln, n, ok in _self_declared_skips() if not ok]
        assert not missing, (
            f"{len(missing)} check return(s) tell the READER they skipped but not "
            f"the coverage floor:\n"
            + "\n".join(f"  {f}:{ln}  {n}" for f, ln, n in missing)
            + "\n\nAdd `measured=False` to that CheckResult. A PASS that measured "
              "nothing must not count toward CI_MIN_CHECKS_RUN, and `_memo` must "
              "refuse to cache it.")
