"""ADR-009 D2 item 8 — the external surface of `validate` survives the split.

WHY THIS FILE EXISTS
--------------------
The Phase-2 domain split moves check bodies out of `scripts/validate.py`. Every
migration-contract item already written down (`--list` order, exit codes, `--json`
schema, `import validate` + `BUNDLE_CODES`) can be satisfied by a split that
nonetheless breaks nine test files and one production script, because they do not
go through any of those surfaces — they import check functions and private helpers
BY NAME:

    from validate import check_bundle_consistency          # test_bundle_consistency
    from validate import _parse_latex_number               # test_d1_hierarchy_table
    from validate import _tp_scan_lines, _tp_live_pins     # test_validate_toolchain_pin_drift
    from validate import _counts_is_stale, _tables_is_stale   # scripts/sync_manifest.py  ← NOT a test

That last one is the one that makes this a correctness concern rather than a test
-ergonomics one: the pre-commit sync path depends on `validate`'s *private*
surface. A split that drops it breaks committing, not just testing.

The failure is loud (`ImportError`) rather than silent, which is the good case —
but only for whichever consumer happens to be exercised first, and only if it is
exercised at all. This file asserts the whole surface at once, before anything
moves, so the extraction has a net rather than a discovery process.

MAINTENANCE
-----------
`EXPECTED_SURFACE` is frozen and deliberately verbose. It is NOT computed from
`validate`, because a test that derives its expectation from the thing under test
asserts nothing — the same reasoning as `EXPECTED_CHECKS` in
`test_validate_registry_contract.py`.

Measured 2026-08-03 by AST-scanning `tests/*.py` and `scripts/*.py` for
`from validate import ...` and `<alias>.<attr>` where the alias is a real
`import validate as <alias>`. REMOVING a name from this list is a real decision:
it means updating the consumer. Adding one is free.

⚠️ **THE FIRST MEASUREMENT MISSED 20 OF THE 53 NAMES**, and the reason is worth
keeping. That scan filtered on `node.module == "validate"`, but
`test_substrate_integrity_gates.py` still spelled its imports
`from scripts.validate import ...` at the time — so the entire file, and every
name it reaches, was invisible. The spelling was then fixed (it was loading
`validate.py` a second time under a second module identity), and the scan was not
re-run, so the frozen list stayed at 34 while the real surface was 54.

Fifteen of the twenty are internals of the not-yet-extracted `lean_substrate`
module — `_STRUCTURAL_NAME_RE`, `_TRIVIAL_BODY_RES`, `_thin_type_label`,
`_is_vacuous_identity_wrapper` and friends — so the omission would have bitten
precisely on the largest remaining extraction.

The lesson generalises: **a measurement is scoped by a predicate, and fixing the
thing the predicate keyed on invalidates the measurement.** Re-run the scan
(the snippet is in this file's git history) whenever an import spelling changes.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

import validate as v  # noqa: E402


#: Check functions imported BY NAME (not via `_CHECKS`) by ten test files.
EXPECTED_CHECK_FUNCTIONS = [
    "check_atlas_integrity",
    "check_axiom_count_prose_consistency",
    "check_bundle_consistency",
    "check_citation_primary_sources_present",
    "check_d1_hierarchy_table",
    "check_disclosure_consistency",
    "check_f_hierarchy_claims",
    "check_formula_grounding",
    "check_formula_identities",
    "check_formulas_to_theorems",
    "check_inventory_index_autogen_fresh",
    "check_lean_source",
    "check_notebook_isolation",
    "check_numerical_consistency",
    "check_paper_table_consistency",
    "check_paper_toolchain_pin_drift",
    "check_prose_theorem_reference_coverage",
    "check_proxy_body_audit",
    "check_theorem_count",
    "check_theorem_name_embedded_citations",
    "check_vacuous_statement_audit",
]

#: Private helpers, pure cores and module state reached from outside.
EXPECTED_PRIVATE = [
    "_CANONICAL_ORDER",
    "_CHECKS",
    "_HEDGE_CLAIM_RE",
    "_LEDGER_HEDGE_RE",
    "_NONTRIVIAL_MARKER_RE",
    "_OVERCLAIM_VERB_RE",
    "_PROSE_REF_WAIVERS",
    "_RECURRENCE_MIN_OVERLAP",
    "_STRUCTURAL_NAME_RE",
    "_THIN_HARD",
    "_TRACKED_PROP_NAME_RE",
    "_TRIVIAL_BODY_RES",
    "_VERIFY_CLAIM_RE",
    "_axiom_prose_findings",
    "_counts_is_stale",          # scripts/sync_manifest.py — production, not a test
    "_embedded_citation_pairs",
    "_extract_prose_lean_candidates",
    "_is_autogen_decl",
    "_is_prop_codomain",
    "_is_vacuous_identity_wrapper",
    "_paper_bibitems",
    "_parse_formula_lean_refs",
    "_parse_latex_number",
    "_prose_occurrence_disclaimed",
    "_recurrence_norm",
    "_resolve_prose_ref",
    "_strip_tex_comments",
    "_tables_is_stale",          # scripts/sync_manifest.py — production, not a test
    "_tex_name_pattern",
    "_thin_type_label",
    "_tp_live_pins",
    "_tp_scan_lines",
]

#: Reached DYNAMICALLY (`importlib.import_module` + `getattr` in the roster gate),
#: so no static import scan finds it. Easy to lose for exactly that reason.
EXPECTED_DYNAMIC = ["BUNDLE_CODES"]

EXPECTED_SURFACE = EXPECTED_CHECK_FUNCTIONS + EXPECTED_PRIVATE + EXPECTED_DYNAMIC


class TestExternalSurface:
    @pytest.mark.parametrize("name", EXPECTED_SURFACE)
    def test_name_is_reachable_on_validate(self, name):
        assert hasattr(v, name), (
            f"`validate.{name}` is gone. It is imported by name from outside the "
            f"module (see this file's docstring), so the Phase-2 split must "
            f"RE-EXPORT it from scripts/validate.py rather than leave it in its "
            f"new home only. ADR-009 D2 item 8."
        )

    def test_check_functions_are_callable(self):
        """`hasattr` alone would be satisfied by a stray string or a stub."""
        for name in EXPECTED_CHECK_FUNCTIONS:
            assert callable(getattr(v, name)), f"validate.{name} is not callable"

    def test_registry_and_order_are_the_real_containers(self):
        """`_CHECKS` and `_CANONICAL_ORDER` must be the live objects, not copies.

        After the split `_CHECKS` will be defined in the registry module and
        re-exported here. Re-export binds the same LIST — registration appends to
        it and `_apply_canonical_order` sorts it IN PLACE, so the binding stays
        valid. A future `_CHECKS = [...]` rebinding anywhere would silently give
        two registries, with `--list` and `run_checks` reading different ones.
        This asserts the identity that makes the re-export safe.
        """
        assert isinstance(v._CHECKS, list) and v._CHECKS, "_CHECKS is not a populated list"
        assert isinstance(v._CANONICAL_ORDER, tuple), "_CANONICAL_ORDER is not a tuple"
        try:
            from validation import _registry  # noqa: F401
        except ImportError:
            pytest.skip("registry not yet extracted (pre-Phase-2-split)")
        assert v._CHECKS is _registry._CHECKS, (
            "`validate._CHECKS` is not the same object as `validation._registry._CHECKS`. "
            "Registration appends to one and `run_checks`/`--list` iterate the other, so "
            "checks would silently vanish from the run. Re-export by binding, never by copy."
        )

    def test_no_check_derives_a_path_from___file__(self):
        """ADR-009 H1 — the hazard that makes the whole suite green while measuring
        nothing, asserted structurally because its symptom is silence.

        `PROJECT_ROOT` is `Path(__file__).resolve().parent.parent`. From
        `scripts/validate.py` that is the repo root; from
        `scripts/validation/checks/anything.py` it is `scripts/validation`. Nothing
        raises — every artifact lookup simply misses and each check takes its
        "absent" branch. Measured for the five sites that existed on 2026-08-03:
        three would have failed loudly, but two would have passed SILENTLY —
        `accepted_findings_carry_rationale` returns `passed=True` on a missing
        ledger, and `citation_primary_sources_present` downgrades its duplicate-key
        guard to an advisory warning inside an `except`.

        Phase 1 centralised the seven MODULE-LEVEL anchors and was recorded as
        having closed H1. It had not: five `Path(__file__)` derivations remained
        INSIDE check bodies, which is exactly where a module move relocates them.
        This test is what makes "H1 is closed" checkable instead of asserted.

        Exactly one use is legitimate — the bootstrap that puts `scripts/` and the
        repo root on `sys.path` before any sibling import can happen. It cannot
        itself come from `validate_helpers`, since that is what it makes importable.

        SCOPE GROWS WITH THE PACKAGE. This scans `validate.py` **and every**
        `validation/**/*.py`. Scanning only `validate.py` would have made the guard
        obsolete the moment the first check module landed — a guard whose coverage
        silently stops tracking the code it guards is this same defect class, one
        level up.
        """
        import ast
        scanned = [SK_ROOT / "scripts" / "validate.py"]
        scanned += sorted((SK_ROOT / "scripts" / "validation").rglob("*.py"))
        assert len(scanned) > 1, "no validation package modules found — scope is wrong"

        problems: list[str] = []
        for path in scanned:
            tree = ast.parse(path.read_text())
            used = [n.lineno for n in ast.walk(tree)
                    if isinstance(n, ast.Name) and n.id == "__file__"]
            # The ONE legitimate use: the sys.path bootstrap in `validate.py`. It
            # cannot come from `validate_helpers`, being what makes it importable.
            bootstrap = [
                n.lineno for n in tree.body
                if isinstance(n, ast.Assign)
                and any(getattr(t, "id", "") == "_BOOTSTRAP_SCRIPT_DIR" for t in n.targets)
            ]
            for ln in sorted(set(used) - set(bootstrap)):
                problems.append(f"{path.relative_to(SK_ROOT)}:{ln}")

        assert not problems, (
            f"`__file__` is used outside the sys.path bootstrap at: {problems}. "
            f"Any path derived from it retargets once the code lives under "
            f"`validation/checks/` — `parent.parent` becomes `scripts/validation` — "
            f"and the failure is SILENT for every check that treats a missing "
            f"artifact as PASS. Derive from `validate_helpers` instead "
            f"(`_H.LEAN_DIR`, `_H.DOCS_DIR`, `_H.SRC_DIR`, `_H.PAPERS_DIR`, …)."
        )

    def test_no_check_module_has_an_undefined_module_level_reference(self):
        """A moved check must not reference a name left behind in `validate.py`.

        This is the extraction's most likely mechanical failure and it is INVISIBLE
        to the test suite. A module-level constant — a compiled regex, a pattern
        list — sits above its check separated by a blank line, so a banner-walk that
        stops at the first non-comment line leaves it behind. The module still
        imports and `--list` still shows every registered check (80 today); the check raises `NameError`
        only when RUN, and `run_checks` converts that into
        `CheckResult(passed=False, error=...)` rather than a crash.

        It happened on the `papers_prose` split: `_COUNT_LITERAL_PATTERNS`,
        `_NUMERICAL_LITERAL_RE` and `_LATEX_FATAL_RE` were stranded. **The full
        4,986-test suite passed**; only the characterization harness caught it,
        because only it actually invokes every check. This test closes that gap
        statically, so the next module does not depend on a 6-minute capture to
        discover a one-line omission.

        Deliberately static (AST) rather than "import and call": several checks are
        minutes-long, and the failure is a missing NAME, which resolves statically.
        """
        import ast
        import builtins

        def bound_names(tree):
            out = set(dir(builtins))
            for n in ast.walk(tree):
                if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    out.add(n.name)
                elif isinstance(n, ast.Assign):
                    for t in n.targets:
                        out |= {x.id for x in ast.walk(t) if isinstance(x, ast.Name)}
                elif isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Name):
                    out.add(n.target.id)
                elif isinstance(n, (ast.Import, ast.ImportFrom)):
                    out |= {(a.asname or a.name).split(".")[0] for a in n.names}
                elif isinstance(n, ast.arg):
                    out.add(n.arg)
                elif isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
                    out.add(n.id)
                elif isinstance(n, ast.ExceptHandler) and n.name:
                    out.add(n.name)
                elif isinstance(n, ast.comprehension):
                    out |= {x.id for x in ast.walk(n.target) if isinstance(x, ast.Name)}
                elif isinstance(n, ast.Global):
                    out |= set(n.names)
            return out

        problems = {}
        modules = sorted((SK_ROOT / "scripts" / "validation").rglob("*.py"))
        assert modules, "no validation package modules found — scope is wrong"
        for path in modules:
            tree = ast.parse(path.read_text())
            bound = bound_names(tree)
            used = {n.id for n in ast.walk(tree)
                    if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)}
            missing = sorted(u for u in used - bound if not u.startswith("__"))
            if missing:
                problems[str(path.relative_to(SK_ROOT))] = missing

        assert not problems, (
            f"check module(s) reference names that are neither defined nor imported "
            f"there: {problems}. Almost certainly a module-level constant left behind "
            f"in validate.py by the extraction. The module imports fine and --list "
            f"still reports 59 — the check raises NameError only when RUN."
        )

    def test_no_check_module_aliases_a_path(self):
        """A check module must not bind a `validate_helpers` path at module level.

        `PAPERS_DIR = _H.PAPERS_DIR` in a check module is an import-time COPY — the
        same shape as `from validate import STRICT_MODE`, which H5 forbids for
        flags. Paths are never reassigned in production, so the copy looks harmless;
        it is not harmless for the tests that monkeypatch a temp tree to seed a
        defect.

        Found the hard way on 2026-08-03: `test_f_hierarchy_claims` patches
        `PAPERS_DIR` and asserts the check FAILS on a stale draft. Once
        `check_f_hierarchy_claims` moved into `checks/physics.py` and read a local
        alias, the patch no longer reached it — the real, correct draft was read and
        the check passed. It failed loudly only because that test asserts
        `not passed`; a positive-control test would have gone silently vacuous,
        which is this project's signature failure.

        The rule is therefore the same as for flags: ONE owner, reached by attribute
        at call time. `validate.py` itself is exempt — its aliases predate the split
        and shrink to nothing as checks move out.
        """
        import ast
        offenders = []
        for path in sorted((SK_ROOT / "scripts" / "validation").rglob("*.py")):
            tree = ast.parse(path.read_text())
            for node in tree.body:                      # module level only
                if not isinstance(node, ast.Assign):
                    continue
                val = node.value
                # `X = _H.SOMETHING` — a bare attribute copy off the helpers module
                if (isinstance(val, ast.Attribute)
                        and isinstance(val.value, ast.Name)
                        and val.value.id in ("_H", "validate_helpers")):
                    for t in node.targets:
                        offenders.append(
                            f"{path.relative_to(SK_ROOT)}:{node.lineno} "
                            f"{getattr(t, 'id', '?')} = _H.{val.attr}")
        assert not offenders, (
            f"check module(s) bind a path by value: {offenders}. That is an "
            f"import-time copy; a test monkeypatching the owner will not reach the "
            f"check, and the seeded defect goes unseen. Use `_H.<NAME>` at each use "
            f"site instead. (Deriving a NEW path from one — e.g. "
            f"`CACHE = _H.NOTEBOOKS_DIR / 'x.json'` — is a different expression and "
            f"is allowed, but note it freezes the same way if the base is patched.)"
        )

    def test_validate_is_loaded_exactly_once(self):
        """`validate.py` must have ONE module identity in the interpreter.

        `pythonpath = ["."]` makes `scripts/validate.py` importable both as
        `validate` (what nine test files use, via a `sys.path` insert) and as
        `scripts.validate`. Doing both loads the file TWICE into two distinct
        module objects — and `tests/test_substrate_integrity_gates.py` did exactly
        that until 2026-08-03.

        That was survivable only while every piece of shared state was per-module:
        two registries of 59 read identically to one registry of 59. Once `_CHECKS`
        moved to the shared `validation._registry` singleton, both copies appended
        to the same list — 118 checks, duplicate names, broken execution order.

        And it was never actually harmless: two identities also mean
        `validate.CheckResult` and `scripts.validate.CheckResult` are different
        classes (so `isinstance` across them is False), and two copies of any
        module-global — which is what `--strict` was before `validation._config`.

        Asserted on `sys.modules` rather than by grepping imports, so it catches
        any route to a second identity, including `importlib` by file path.
        """
        loaded = sorted(
            name for name, mod in sys.modules.items()
            if mod is not None
            and getattr(mod, "__file__", None)
            and Path(mod.__file__).name == "validate.py"
            and Path(mod.__file__).parent.name == "scripts"
        )
        assert loaded == ["validate"], (
            f"`scripts/validate.py` is loaded under {len(loaded)} module names: "
            f"{loaded}. Two identities means two registries, two sets of caches, "
            f"and result classes that fail `isinstance` across the boundary. "
            f"Import it as `validate` (add `scripts/` to sys.path), never as "
            f"`scripts.validate`."
        )

    def test_surface_has_no_unexpected_public_additions(self):
        """A cheap drift signal: new PUBLIC names on `validate` are usually a sign
        that something meant for a check module landed on the framework instead."""
        public = {
            n for n in dir(v)
            if not n.startswith("_") and not n.startswith("check_")
            and callable(getattr(v, n, None))
            and getattr(getattr(v, n), "__module__", "") == "validate"
        }
        expected = {
            # result types (dataclasses — callable, hence caught by the filter)
            "Detail", "CheckResult", "CheckSpec",
            # registry + runner + reporting + CLI
            "register_check", "run_checks", "print_results",
            "archive_results", "main",
        }
        unexpected = public - expected
        assert not unexpected, (
            f"unexpected public callables on `validate`: {sorted(unexpected)}. The "
            f"framework module's public surface is {sorted(expected)}; anything else "
            f"belongs in a check or helper module. If this is deliberate, add it here."
        )


class TestGraphTestNodeCoverage:
    """Every `def test_*` must reach the graph — ADR-009 §Deferred item 7.

    `extract_python_test_nodes` minted its id as `test:<module>::<function>` with
    the CLASS OMITTED and deduped on it, so two tests sharing a method name in
    different classes of one file collided and every one after the first was
    silently discarded — no log, no counter. Measured at the fix: **4,416
    `def test_*` produced 4,350 nodes; 66 tests were missing from the graph.**

    These nodes are the source of the VERIFIES edges that
    `ReadinessGate: ComputationCorrectness` reads as test-coverage evidence, so a
    dropped node is missing coverage in a gate. This asserts the invariant the
    id scheme has to preserve: one node per test function, no silent loss.
    """

    def test_every_test_function_becomes_a_node(self):
        import ast
        sys.path.insert(0, str(SK_ROOT / "scripts"))
        from build_graph import extract_python_test_nodes

        # ⚠️ rglob, matching the extractor (fixed 2026-08-04). Both sides used the
        # SAME non-recursive glob, so the equality held VACUOUSLY: 12 files and 30
        # `def test_*` under `tests/e2e/` were absent from both the count and the
        # nodes, and this assertion agreed that nothing was missing. A count test
        # that shares its scope bug with the code it checks confirms the bug.
        defs = 0
        for f in sorted((SK_ROOT / "tests").rglob("test_*.py")):
            try:
                tree = ast.parse(f.read_text())
            except SyntaxError:
                continue
            defs += sum(1 for n in ast.walk(tree)
                        if isinstance(n, ast.FunctionDef) and n.name.startswith("test_"))

        nodes = extract_python_test_nodes()
        assert len(nodes) == defs, (
            f"{defs} `def test_*` in tests/ but {len(nodes)} PythonTest nodes — "
            f"{defs - len(nodes)} silently dropped. Almost certainly a node-id "
            f"collision: the id must distinguish same-named methods in different "
            f"classes (ADR-009 §Deferred item 7)."
        )

    def test_node_ids_are_unique(self):
        sys.path.insert(0, str(SK_ROOT / "scripts"))
        from build_graph import extract_python_test_nodes
        nodes = extract_python_test_nodes()
        ids = [n["id"] for n in nodes]
        assert len(set(ids)) == len(ids), "duplicate PythonTest node ids"


# ── TODO-D37: the literal predicate's population composition is pinned ─────

class TestNumericalLiteralPopulationComposition:
    """`NUMERICAL_LITERAL_RE` described itself as matching "a literal with a
    physical unit". Measured 2026-08-09, that is false for 51 % of its own
    population: of 117 matches, 60 are dimensionless scientific notation.

    D37 offered narrowing the leg to require an adjacent unit. That was rejected
    as loosening — it would drop 60 matches at a stroke. These tests pin the
    composition so a future narrowing shows up as a failing test rather than as
    a quietly smaller corpus figure."""

    def _measure(self):
        import sys, pathlib, re
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "scripts"))
        from validation._tex import find_inline_numerical_literals
        import validate_helpers as _H
        unit_leg = times_leg = 0
        for tex in _H.all_paper_drafts():
            _body, matches = find_inline_numerical_literals(tex.read_text())
            for m in matches:
                if '\\times' in m.group(0):
                    times_leg += 1
                else:
                    unit_leg += 1
        return unit_leg, times_leg

    def test_the_times_ten_leg_carries_the_majority(self):
        """If this inverts, someone narrowed the leg — which is the change D37
        explicitly rejected. Re-read the D37 entry before adjusting."""
        unit_leg, times_leg = self._measure()
        assert times_leg > unit_leg * 3, (
            f"unit-leg={unit_leg} times-leg={times_leg}: the `\\times 10^` leg is "
            "supposed to dominate; a collapse here means the predicate was narrowed")

    def test_dimensionless_matches_are_in_scope_not_excluded(self):
        """A dimensionless computed value drifts exactly as a unit-bearing one
        does. The predicate must still see scientific notation with no unit."""
        import sys, pathlib
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "scripts"))
        from validation._tex import NUMERICAL_LITERAL_RE
        assert NUMERICAL_LITERAL_RE.search(r"$2.38\times10^{-5}$ the crossover"), \
            "dimensionless scientific notation must remain in scope (TODO-D37)"

    def test_ceiling_matches_the_live_population(self):
        from src.core.constants import NUMERICAL_LITERAL_CEILING
        unit_leg, times_leg = self._measure()
        assert unit_leg + times_leg <= NUMERICAL_LITERAL_CEILING


# ── TODO-D18: the TeX-quote form is extracted ─────────────────────────────

class TestTexQuoteReferencesAreExtracted:
    """`prose_theorem_reference_coverage` keyed on `\\texttt`, discovered preamble
    aliases and `\\verb`. The bare TeX quotation `` `name' `` has no macro to
    discover, so it was invisible — and D7 used exactly that form to cite
    `analog_hawking_quantum_advantage_demarcation`, a theorem that does not exist.

    Residue was MEASURED, not assumed: `\\verb` and `\\lean` were already covered
    by the alias fixpoint, so of 401 non-`\\texttt` Lean-ish references only ONE
    was genuinely unreachable."""

    def _tokens(self, src):
        import sys, pathlib
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "scripts"))
        from validation.checks.prose_lean_refs import _prose_verbatim_tokens
        return [t for t, _off in _prose_verbatim_tokens(src)]

    def test_the_exact_defect_d7_shipped_is_now_extracted(self):
        src = r"The biconditional `analog\_hawking\_quantum\_advantage\_demarcation' (Lean)."
        assert "analog_hawking_quantum_advantage_demarcation" in self._tokens(src)

    def test_ordinary_english_quotation_is_not_swept_in(self):
        """Gated on `\\_` or a dot. Without the gate every quoted English word
        becomes a candidate and the check drowns in prose."""
        src = r"the so-called `vestigial' phase and its `second sound' mode"
        assert self._tokens(src) == []

    def test_dotted_namespace_quote_is_extracted(self):
        src = r"see `AnalogHawkingDemarcation.analog\_hawking\_tree\_simulable\_demarcation'"
        toks = self._tokens(src)
        assert any(t.startswith("AnalogHawkingDemarcation.") for t in toks), toks

    def test_d7_no_longer_cites_a_nonexistent_theorem(self):
        import pathlib, re
        d7 = (pathlib.Path(__file__).resolve().parents[1]
              / "papers/D7/paper_draft.tex").read_text()
        assert "analog\\_hawking\\_quantum\\_advantage\\_demarcation" not in d7
        assert "analog\\_hawking\\_simulable\\_iff\\_fourCycleFree" in d7
