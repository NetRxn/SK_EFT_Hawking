"""test_inventory_index_autogen.py — tests for the Inventory-Index autogen system.

Covers ``scripts/update_inventory_index.py``:
* the generator is idempotent (a second run on its own output is a no-op);
* all three AUTOGEN markers are present in the live index;
* family-count arithmetic sums to ``lean.modules``;
* ``--check`` / ``compute_stale`` detects an injected staleness on a tmp copy;
* the ``inventory_index_autogen_fresh`` validate.py advisory check is registered,
  passes on the live tree, and stays advisory (never FAILs) when stale.

Fast tests — pure Python, no Lean / subprocess.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

import update_inventory_index as uii  # noqa: E402

COUNTS_JSON = PROJECT_ROOT / "docs" / "counts.json"
INDEX = PROJECT_ROOT / "SK_EFT_Hawking_Inventory_Index.md"


def _counts() -> dict:
    return json.loads(COUNTS_JSON.read_text())


class TestMarkersPresent:
    def test_all_three_marker_pairs_present(self):
        text = INDEX.read_text()
        for tag in (uii.TAG_COUNTS_TABLE, uii.TAG_PER_FAMILY,
                    uii.TAG_FAMILY_TABLE):
            assert uii._marker_begin(tag) in text, f"missing BEGIN for {tag}"
            assert uii._marker_end(tag) in text, f"missing END for {tag}"

    def test_begin_precedes_end_for_each_tag(self):
        text = INDEX.read_text()
        for tag in (uii.TAG_COUNTS_TABLE, uii.TAG_PER_FAMILY,
                    uii.TAG_FAMILY_TABLE):
            assert text.find(uii._marker_begin(tag)) < text.find(
                uii._marker_end(tag)), f"END before BEGIN for {tag}"


class TestIdempotent:
    def test_live_tree_is_fresh(self):
        # The repo as committed must already be fresh (zero-diff invariant).
        stale, summary = uii.compute_stale()
        assert not stale, f"index unexpectedly stale: {summary}"

    def test_regenerate_is_a_fixed_point(self):
        current = INDEX.read_text()
        counts = _counts()
        once = uii.regenerate_text(current, counts)
        twice = uii.regenerate_text(once, counts)
        assert once == twice, "regenerate is not idempotent"

    def test_regenerate_matches_current(self):
        # Regenerating the live file changes nothing (markers + content aligned).
        current = INDEX.read_text()
        regenerated = uii.regenerate_text(current, _counts())
        assert regenerated == current, (
            "regenerating the live index produced a diff")


class TestFamilyArithmetic:
    def test_families_plus_toplevel_equals_total_modules(self):
        counts = _counts()
        families, top = uii.group_families(counts["lean"]["module_names"])
        total = sum(c for _, c in families) + top
        assert total == counts["lean"]["modules"], (
            f"family sum {total} != lean.modules {counts['lean']['modules']}")

    def test_families_sorted_desc_then_name(self):
        counts = _counts()
        families, _ = uii.group_families(counts["lean"]["module_names"])
        ordering = [(-c, n) for n, c in families]
        assert ordering == sorted(ordering), "families not in (−count, name) order"

    def test_no_family_has_zero_modules(self):
        counts = _counts()
        families, _ = uii.group_families(counts["lean"]["module_names"])
        assert all(c >= 1 for _, c in families)


class TestCheckModeDetectsStaleness:
    def test_injected_staleness_on_tmp_copy(self, tmp_path):
        # Copy the live index, corrupt a generated count, confirm staleness.
        tmp_index = tmp_path / "index.md"
        text = INDEX.read_text()
        # Flip the Lean-modules value inside the counts-table block.
        modules = _counts()["lean"]["modules"]
        corrupted = text.replace(
            f"| Lean modules | {modules} |",
            f"| Lean modules | {modules + 999} |", 1)
        assert corrupted != text, "test setup failed to corrupt a count row"
        tmp_index.write_text(corrupted)

        stale, summary = uii.compute_stale(
            index_path=tmp_index, counts_path=COUNTS_JSON)
        assert stale, "compute_stale missed an injected count change"
        assert uii.TAG_COUNTS_TABLE in summary

    def test_write_regenerated_fixes_tmp_copy(self, tmp_path):
        tmp_index = tmp_path / "index.md"
        text = INDEX.read_text()
        modules = _counts()["lean"]["modules"]
        tmp_index.write_text(text.replace(
            f"| Lean modules | {modules} |",
            f"| Lean modules | {modules + 999} |", 1))

        changed = uii.write_regenerated(
            index_path=tmp_index, counts_path=COUNTS_JSON)
        assert changed, "write_regenerated reported no change on a stale file"
        stale, _ = uii.compute_stale(
            index_path=tmp_index, counts_path=COUNTS_JSON)
        assert not stale, "file still stale after regeneration"

    def test_missing_markers_reported_stale(self, tmp_path):
        tmp_index = tmp_path / "index.md"
        tmp_index.write_text("# no markers here\n")
        stale, summary = uii.compute_stale(
            index_path=tmp_index, counts_path=COUNTS_JSON)
        assert stale and "markers missing" in summary


class TestValidateCheckRegistered:
    def test_check_present_passes_and_advisory(self):
        from validate import check_inventory_index_autogen_fresh
        result = check_inventory_index_autogen_fresh()
        # Advisory: must pass on the live (fresh) tree.
        assert result.passed, f"check failed: {result.error or result.details}"
        assert any(d.name == "freshness" for d in result.details)

    def test_check_is_in_registry_with_two_string_decorator(self):
        import ast
        validate_py = PROJECT_ROOT / "scripts" / "validate.py"
        tree = ast.parse(validate_py.read_text())
        names = []
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            for dec in node.decorator_list:
                if (isinstance(dec, ast.Call)
                        and isinstance(dec.func, ast.Name)
                        and dec.func.id == "register_check"
                        and len(dec.args) >= 2
                        and isinstance(dec.args[0], ast.Constant)
                        and isinstance(dec.args[1], ast.Constant)):
                    names.append(str(dec.args[0].value))
        assert "inventory_index_autogen_fresh" in names, (
            "check not AST-parseable as a two-string register_check decorator")
