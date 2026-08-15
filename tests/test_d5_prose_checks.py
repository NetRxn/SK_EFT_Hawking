"""D5 both-directions tests for `spelled_out_census_figures` (I1 Stage-13 finding 7.2).

`count_literals` matches DIGITS, so a census figure written in words is invisible to it —
and this corpus writes them in words routinely, because spelling a number out is house
style in prose. Measured: I1's intro said "seventeen invariants" while its own enumeration
had fifteen items, and no check could see it.

The discriminator is the NOUN, not the number word. "three orders of magnitude" is a
physical result and must never fire; "three stages" counts this project's own machinery
and goes stale when the machinery changes. A test for each direction, plus the empty-walk
seam — because every assertion here is "total <= ceiling", which no drafts satisfies
perfectly.
"""
from __future__ import annotations

import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate_helpers as _H  # noqa: E402
from validation.checks import papers_prose as pp  # noqa: E402


def _corpus(tmp_path, drafts: dict[str, str]) -> Path:
    root = tmp_path / "root"
    for name, body in drafts.items():
        p = root / "papers" / name / "paper_draft.tex"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(body, encoding="utf-8")
    return root


def _patch(monkeypatch, root):
    monkeypatch.setattr(_H, "PROJECT_ROOT", root)
    monkeypatch.setattr(_H, "PAPERS_DIR", root / "papers")


class TestSpelledOutCensusFigures:
    def test_a_spelled_census_figure_over_the_ceiling_FAILS(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        _patch(monkeypatch, _corpus(tmp_path, {
            "D1": "The pipeline has fourteen stages and seventeen invariants.\n"}))
        monkeypatch.setattr(pp, "check_spelled_out_census_figures",
                            pp.check_spelled_out_census_figures)
        import src.core.constants as C
        monkeypatch.setattr(C, "SPELLED_CENSUS_CEILING", 1)
        r = pp.check_spelled_out_census_figures()
        assert r.passed is False, "two spelled-out census figures passed a ceiling of 1"
        assert any("EXCEEDS" in (d.message or "") for d in r.details)

    def test_a_PHYSICAL_result_spelled_out_does_NOT_fire(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA, and this is the discriminator.

        "three orders of magnitude" is a measured result, not a census of this project's
        machinery. A check that flagged it would be style policing, and the first person
        to hit it would widen the ceiling to make it stop — which is how a ratchet dies.
        """
        _patch(monkeypatch, _corpus(tmp_path, {
            "D1": "The ratio spans three orders of magnitude, some four decades in all.\n"}))
        import src.core.constants as C
        monkeypatch.setattr(C, "SPELLED_CENSUS_CEILING", 0)
        r = pp.check_spelled_out_census_figures()
        assert r.passed is True, [
            (d.name, d.message) for d in r.details if not d.passed]

    def test_an_EMPTY_PAPER_WALK_fails_rather_than_reading_as_clean(
            self, tmp_path, monkeypatch):
        """⚠️ THE SEAM. Every other assertion is `total <= ceiling`, which a corpus of no
        drafts satisfies perfectly — so a moved PAPERS_DIR would read as a corpus somebody
        had cleaned up."""
        _patch(monkeypatch, _corpus(tmp_path, {}))
        r = pp.check_spelled_out_census_figures()
        assert r.passed is False and r.measured is False
        assert any("asserted nothing" in (d.message or "") for d in r.details)

    def test_the_live_ceiling_has_ZERO_headroom(self):
        """PRODUCTION. A ceiling left standing above an improved corpus stops ratcheting
        silently — the defect recorded three times in `reviews.py`."""
        import re
        r = pp.check_spelled_out_census_figures()
        msg = next(d for d in r.details if d.name == "summary").message
        n = int(re.match(r"(\d+) spelled-out", msg).group(1))
        from src.core.constants import SPELLED_CENSUS_CEILING as CEIL
        assert n == CEIL, (
            f"{n} spelled-out census figures against a ceiling of {CEIL}. If the corpus "
            f"improved, LOWER the ceiling in the same commit. ⚠️ If it grew, do NOT raise "
            f"it — bind the new figure to a macro or name the mechanism instead.")
