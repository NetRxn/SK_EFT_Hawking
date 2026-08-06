"""Tests for the two guards added after the 2026-08-06 holistic QA assessment.

`lean_zero_sorry` closes Pipeline Invariant #4, which had no suite gate at all.
`gate_edge_types_are_emitted` closes the class the assessment found: a readiness gate
querying an edge type no extractor emits, so it returns a verdict it did not compute.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT))
sys.path.insert(0, str(SK_ROOT / "scripts"))


class TestLeanZeroSorry:
    @pytest.fixture
    def check(self):
        import validate
        return validate.check_lean_zero_sorry

    def _counts(self, monkeypatch, tmp_path, lean: dict | None):
        docs = tmp_path / "docs"; docs.mkdir()
        if lean is not None:
            (docs / "counts.json").write_text(json.dumps({"lean": lean}))
        import validate_helpers
        monkeypatch.setattr(validate_helpers, "COUNTS_JSON_PATH", docs / "counts.json")

    def test_a_sorry_FAILS(self, check, monkeypatch, tmp_path):
        """FIRES ON THE SEEDED DEFECT. Production-seeded too: writing
        sorry_declarations=1 into the real docs/counts.json turns the check red."""
        self._counts(monkeypatch, tmp_path, {"sorry_declarations": 1, "sorry_theorems": 1})
        assert check().passed is False

    def test_zero_sorry_passes(self, check, monkeypatch, tmp_path):
        """SILENT ON CORRECT DATA."""
        self._counts(monkeypatch, tmp_path,
                     {"sorry_declarations": 0, "total_declarations": 40668})
        res = check()
        assert res.passed is True and res.measured is True

    def test_the_FIELD_GOING_MISSING_fails_rather_than_reading_as_zero(
            self, check, monkeypatch, tmp_path):
        """⚠️ The whole point. `lean.get('sorry_declarations', 0)` would make a dropped
        field indistinguishable from a clean tree — the absence-as-success shape."""
        self._counts(monkeypatch, tmp_path, {"total_declarations": 40668})
        assert check().passed is False

    def test_an_absent_counts_file_is_UNMEASURABLE_not_clean(
            self, check, monkeypatch, tmp_path):
        self._counts(monkeypatch, tmp_path, None)
        res = check()
        assert res.measured is False


class TestGateEdgeTypesAreEmitted:
    @pytest.fixture
    def check(self):
        import validate
        return validate.check_gate_edge_types_are_emitted

    def test_the_live_tree_has_only_DISCLOSED_dead_edge_types(self, check):
        """SILENT ON CORRECT DATA — passes today with PRODUCES/SUPPORTS/CONTRADICTS
        disclosed, and goes red the moment a gate queries a fourth."""
        assert check().passed is True

    def test_an_undisclosed_dead_edge_type_FAILS(self, check, monkeypatch):
        """FIRES ON THE SEEDED DEFECT, and it fired for real: CONTRADICTS was found by
        this check on its first production run, undisclosed, and failed the suite until
        it was recorded with its evidence."""
        import validation.checks.graph_atlas as mod
        monkeypatch.setattr(mod, "GATE_EDGE_TYPES_WITHOUT_EMITTERS", {})
        assert check().passed is False

    def test_a_STALE_disclosure_also_fails(self, check, monkeypatch):
        """The other direction: an edge type listed as dead that IS now emitted must be
        removed, or the ratchet stops biting on the ones that remain."""
        import validation.checks.graph_atlas as mod
        stale = dict(mod.GATE_EDGE_TYPES_WITHOUT_EMITTERS)
        stale["CLAIMS"] = "not actually dead — CLAIMS is emitted"
        monkeypatch.setattr(mod, "GATE_EDGE_TYPES_WITHOUT_EMITTERS", stale)
        assert check().passed is False

    def test_both_populations_are_DERIVED_not_hand_listed(self, check):
        """A hand-listed side is how the NEXT gate ships unguarded."""
        res = check()
        d = next(x for x in res.details if x.name == "populations_derived")
        assert "read from the AST, neither hand-listed" in d.message
