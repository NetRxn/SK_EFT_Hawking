"""Tests for the DERIVED surface inventory — the census half of the end-to-end map.

The inventory exists because narrative counts rot. These tests exist because a *derived*
inventory that silently derives the wrong thing is worse than a hand-written one: it carries
the authority of being generated.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT))
sys.path.insert(0, str(SK_ROOT / "scripts"))


@pytest.fixture(scope="module")
def inv_mod():
    spec = importlib.util.spec_from_file_location(
        "_arch_inventory_test", SK_ROOT / "scripts" / "architecture_inventory.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


class TestDerivation:
    def test_checks_come_from_the_registry_not_a_literal(self, inv_mod):
        """SILENT ON CORRECT DATA, and pins the source: the count must equal the live
        registry, so it cannot be frozen at a number someone typed."""
        import validate
        assert len(inv_mod.checks()) == len(validate._CHECKS)

    def test_a_memoized_check_is_attributed_to_its_REAL_module(self, inv_mod):
        """FIRES ON THE SEEDED DEFECT: drop the `__memo_body__` unwrap and every memoized
        check is attributed to `_memo`, which is not where anyone would look for it."""
        mods = {c["module"] for c in inv_mod.checks()}
        assert "_memo" not in mods, f"memo wrapper leaked into the inventory: {mods}"

    def test_gates_come_from_the_gate_roster(self, inv_mod):
        import readiness_gates
        assert len(inv_mod.gates()) == len(readiness_gates.GATES)

    def test_dead_edge_types_are_DERIVED_by_set_difference(self, inv_mod):
        """The consequential row. Consumed-minus-emitted must be computed, never listed."""
        g = inv_mod.graph_types()
        expected = sorted(t for t in g["edges_consumed_by_gates"]
                          if t not in set(g["edges_emitted"]))
        assert g["edges_consumed_but_never_emitted"] == expected

    def test_the_live_tree_still_has_its_three_known_dead_edge_types(self, inv_mod):
        """A regression pin, both directions: if one gets an emitter this fails and the
        inventory's warning must be re-read; if a FOURTH appears it fails too."""
        assert inv_mod.graph_types()["edges_consumed_but_never_emitted"] == [
            "CONTRADICTS", "PRODUCES", "SUPPORTS"]


class TestFrontmatter:
    def test_a_folded_block_scalar_is_read_not_returned_as_a_caret(self, inv_mod, tmp_path):
        """⚠️ FIRES ON THE SEEDED DEFECT — this was a REAL defect in the first version.

        Five of eight agents write `description: >` with the text on following lines. A
        reader that takes only the key's own line recorded their purpose as the literal
        string `>`, blanking the majority of the population in a document whose whole job
        is to say what exists.
        """
        f = tmp_path / "a.md"
        f.write_text("---\nname: x\ndescription: >\n  first line\n  second line\n---\nbody\n")
        fm = inv_mod._frontmatter(f)
        assert fm["description"] == "first line second line"

    def test_a_plain_scalar_still_works(self, inv_mod, tmp_path):
        f = tmp_path / "b.md"
        f.write_text("---\nname: y\ndescription: one liner\nmodel: opus\n---\n")
        fm = inv_mod._frontmatter(f)
        assert fm["description"] == "one liner" and fm["model"] == "opus"

    def test_every_live_agent_has_a_real_purpose_string(self, inv_mod):
        """The live-corpus form of the defect above."""
        for a in inv_mod.agents_and_commands()["agents"]:
            assert len(a["description"]) > 20, a


class TestRenderIsDeterministic:
    def test_two_renders_of_one_collection_are_identical(self, inv_mod):
        """The freshness check compares text, so any nondeterminism (a timestamp, a set
        iteration order) would make it fail at random and get switched off."""
        inv = inv_mod.collect()
        assert inv_mod.render(inv) == inv_mod.render(inv)

    def test_the_rendered_doc_carries_no_date(self, inv_mod):
        """A date would dirty the file on every run and turn the gate into noise."""
        text = inv_mod.render(inv_mod.collect())
        import re
        assert not re.search(r"\b20\d\d-\d\d-\d\d\b", text)


class TestTheFreshnessCheck:
    """`architecture_inventory_fresh` — the gate that stops the census drifting from the
    system it describes."""

    @pytest.fixture
    def check(self):
        import validate
        return validate.check_architecture_inventory_fresh

    def test_the_live_tree_is_fresh(self, check):
        """SILENT ON CORRECT DATA. If this fails, run
        `uv run python scripts/architecture_inventory.py --write`."""
        res = check()
        assert res.passed is True, [d.message for d in res.details]

    def test_a_HAND_EDIT_to_the_census_FAILS(self, check, monkeypatch, tmp_path):
        """⚠️ FIRES ON THE SEEDED DEFECT — and was production-seeded: appending one HTML
        comment to the real SURFACE_INVENTORY.md turned the check red naming the first
        divergent line."""
        docs = tmp_path / "architecture"
        docs.mkdir(parents=True)
        (docs / "SURFACE_INVENTORY.md").write_text("# hand-written nonsense\n")
        import validate_helpers
        monkeypatch.setattr(validate_helpers, "DOCS_DIR", tmp_path)
        assert check().passed is False

    def test_a_MISSING_census_FAILS_rather_than_skipping(self, check, monkeypatch, tmp_path):
        """An absent census is not a fresh one — the absence-as-success shape."""
        (tmp_path / "architecture").mkdir(parents=True)
        import validate_helpers
        monkeypatch.setattr(validate_helpers, "DOCS_DIR", tmp_path)
        res = check()
        assert res.passed is False and res.measured is True

    def test_an_absent_GENERATOR_is_unmeasurable_not_clean(self, check, monkeypatch,
                                                           tmp_path):
        """The one genuine cannot-measure branch: no generator, no derivation."""
        import validate_helpers
        monkeypatch.setattr(validate_helpers, "SCRIPT_DIR", tmp_path)
        res = check()
        assert res.measured is False
