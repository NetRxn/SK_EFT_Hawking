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
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

import validate as v  # noqa: E402


#: Check functions imported BY NAME (not via `_CHECKS`) by nine test files.
EXPECTED_CHECK_FUNCTIONS = [
    "check_axiom_count_prose_consistency",
    "check_bundle_consistency",
    "check_citation_primary_sources_present",
    "check_d1_hierarchy_table",
    "check_f_hierarchy_claims",
    "check_formula_identities",
    "check_formulas_to_theorems",
    "check_inventory_index_autogen_fresh",
    "check_lean_source",
    "check_notebook_isolation",
    "check_numerical_consistency",
    "check_paper_table_consistency",
    "check_paper_toolchain_pin_drift",
    "check_prose_theorem_reference_coverage",
    "check_theorem_count",
    "check_theorem_name_embedded_citations",
]

#: Private helpers, pure cores and module state reached from outside.
EXPECTED_PRIVATE = [
    "_CANONICAL_ORDER",
    "_CHECKS",
    "_PROSE_REF_WAIVERS",
    "_RECURRENCE_MIN_OVERLAP",
    "_axiom_prose_findings",
    "_counts_is_stale",          # scripts/sync_manifest.py — production, not a test
    "_embedded_citation_pairs",
    "_extract_prose_lean_candidates",
    "_paper_bibitems",
    "_parse_latex_number",
    "_prose_occurrence_disclaimed",
    "_recurrence_norm",
    "_resolve_prose_ref",
    "_strip_tex_comments",
    "_tables_is_stale",          # scripts/sync_manifest.py — production, not a test
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
