"""The extraction-scope hash and the Aristotle gauntlet's refresh.

Both fixes close the same shape of defect: a cache or a check reading a view of the tree
that predates the change it is supposed to judge.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT))
sys.path.insert(0, str(SK_ROOT / "scripts"))


class TestExtractionScopeHash:
    """`compute_lean_hash` must cover the ROOT AGGREGATE, which alone decides scope."""

    @pytest.fixture
    def mod(self):
        import extract_lean_deps
        return extract_lean_deps

    def test_an_aggregate_only_edit_MOVES_the_hash(self, mod, tmp_path, monkeypatch):
        """⚠️ FIRES ON THE SEEDED DEFECT — drop the aggregate from the digest and this
        fails. `lean/SKEFTHawking.lean` sits one level ABOVE the hashed subtree and is what
        ExtractDeps imports, so adding or removing an import there changes the extracted
        population without touching any file under `SKEFTHawking/`."""
        lean = tmp_path / "lean"
        (lean / "SKEFTHawking").mkdir(parents=True)
        (lean / "SKEFTHawking" / "A.lean").write_text("theorem a : True := trivial\n")
        agg = lean / "SKEFTHawking.lean"
        agg.write_text("import SKEFTHawking.A\n")
        monkeypatch.setattr(mod, "LEAN_DIR", lean / "SKEFTHawking")
        monkeypatch.setattr(mod, "LEAN_ROOT", lean)

        before = mod.compute_lean_hash()
        agg.write_text("import SKEFTHawking.A\nimport SKEFTHawking.B\n")
        assert mod.compute_lean_hash() != before, (
            "an import added to the root aggregate — i.e. the extraction scope changed — "
            "did not move the hash")

    def test_reverting_the_aggregate_RESTORES_the_hash(self, mod, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — the hash must be a pure function of content."""
        lean = tmp_path / "lean"
        (lean / "SKEFTHawking").mkdir(parents=True)
        (lean / "SKEFTHawking" / "A.lean").write_text("theorem a : True := trivial\n")
        agg = lean / "SKEFTHawking.lean"
        agg.write_text("import SKEFTHawking.A\n")
        monkeypatch.setattr(mod, "LEAN_DIR", lean / "SKEFTHawking")
        monkeypatch.setattr(mod, "LEAN_ROOT", lean)

        before = mod.compute_lean_hash()
        agg.write_text("import SKEFTHawking.A\n-- probe\n")
        agg.write_text("import SKEFTHawking.A\n")
        assert mod.compute_lean_hash() == before

    def test_a_DELETED_aggregate_also_moves_the_hash(self, mod, tmp_path, monkeypatch):
        """Absence must be a value, not a no-op: deleting the file that defines the
        extraction scope must not read as 'nothing changed'."""
        lean = tmp_path / "lean"
        (lean / "SKEFTHawking").mkdir(parents=True)
        (lean / "SKEFTHawking" / "A.lean").write_text("theorem a : True := trivial\n")
        agg = lean / "SKEFTHawking.lean"
        agg.write_text("import SKEFTHawking.A\n")
        monkeypatch.setattr(mod, "LEAN_DIR", lean / "SKEFTHawking")
        monkeypatch.setattr(mod, "LEAN_ROOT", lean)

        before = mod.compute_lean_hash()
        agg.unlink()
        assert mod.compute_lean_hash() != before

    def test_the_subtree_is_still_covered(self, mod, tmp_path, monkeypatch):
        """The aggregate is an ADDITION — the prior rglob guarantee must survive."""
        lean = tmp_path / "lean"
        sub = lean / "SKEFTHawking" / "Nested"
        sub.mkdir(parents=True)
        (lean / "SKEFTHawking.lean").write_text("import SKEFTHawking.Nested.A\n")
        (sub / "A.lean").write_text("theorem a : True := trivial\n")
        monkeypatch.setattr(mod, "LEAN_DIR", lean / "SKEFTHawking")
        monkeypatch.setattr(mod, "LEAN_ROOT", lean)

        before = mod.compute_lean_hash()
        (sub / "A.lean").write_text("theorem a : True := trivial\ntheorem b : True := trivial\n")
        assert mod.compute_lean_hash() != before


class TestGauntletRefreshesBeforeJudging:
    """The gauntlet's kernel-purity leg must read the POST-graft axiom closure."""

    def test_step_2_regenerates_rather_than_only_building(self):
        """⚠️ FIRES ON THE SEEDED DEFECT: restore `lake build SKEFTHawking.ExtractDeps` as
        the refresh and this fails.

        That command compiles the `.olean` and stops — `ExtractDeps.lean` streams its JSON
        to stdout, and only `scripts/extract_lean_deps.py` writes `lean_deps.json`. So
        building alone left step 3 judging kernel purity against the PRE-graft closure,
        which is the one thing the step exists to prevent.
        """
        import inspect
        import src.core.aristotle_submit as A
        src = inspect.getsource(A.run_verification_gauntlet)
        assert "_refresh_lean_deps()" in src, "the gauntlet no longer refreshes lean_deps"
        assert '"SKEFTHawking.ExtractDeps"' not in src, (
            "the gauntlet is back to compiling the .olean instead of regenerating the JSON")

    def test_a_failed_refresh_FAILS_the_gauntlet(self, monkeypatch):
        """A refresh that raises must not fall through to a stale read — that is exactly
        the pre-graft-view bug, and a silent fallback would reinstate it."""
        import inspect
        import src.core.aristotle_submit as A
        src = inspect.getsource(A.run_verification_gauntlet)
        assert "res.kernel_pure = False" in src and "return res" in src, (
            "a failed ExtractDeps refresh must fail the gauntlet, not continue")
