"""ADR-009 §Deferred item 3 — the three always-pass checks that were defects.

Eight checks were structurally incapable of returning `passed=False`.
`readiness_submission_gate` was §Deferred item 2. Of the seven that remained, four are
**honestly advisory with a stated reason** and stay that way (see the ADR's
disposition table); three were not, and are fixed here:

* `paper_latex_compiles` — computed `all_pass` from its failure list and then
  returned `passed=True`, discarding it. Measured at the fix: **20/21 drafts clean,
  D3 failing with 2 fatal `! Undefined control sequence`** — reported as a passing
  ⚠ WARN for as long as the check existed.
* `count_literals` / `numerical_literals` — both WARN-only "until the retrofit
  completes", a condition written when the corpus had 15 papers. It has 64. The
  target receded faster than it was approached, so neither could ever fail. They
  are now RATCHETS: existing debt frozen, any NEW literal fails.

Each test below runs BOTH directions, per D5: fires on a seeded defect, silent on
correct data. The literal tests drive synthetic drafts through the real check
rather than asserting on the live corpus, so they cannot be broken by remediation
legitimately changing the counts.
"""
from __future__ import annotations

import shutil
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

import validate_helpers as _H  # noqa: E402
from validation import _config as _cfg  # noqa: E402
from validation.checks import papers_prose as pp  # noqa: E402


def _papers(tmp_path: Path, drafts: dict[str, str]) -> Path:
    root = tmp_path / "papers"
    for code, body in drafts.items():
        d = root / code
        d.mkdir(parents=True)
        (d / "paper_draft.tex").write_text(body)
    return root


class TestCountLiteralRatchet:
    """A count literal is a hardcoded "N theorems" that should be a counts.tex macro."""

    CLEAN = r"\documentclass{article}\begin{document}No counts here.\end{document}"
    #: three matches: "48 theorems", "12 modules", "3 sorry"
    DIRTY = (r"\documentclass{article}\begin{document}"
             r"We prove 48 theorems across 12 modules with 3 sorry."
             r"\end{document}")

    def test_at_the_ceiling_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA. Frozen debt must not fail — a ratchet that
        fires on the existing corpus is just a broken build."""
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": self.DIRTY}))
        monkeypatch.setitem(__import__("src.core.constants", fromlist=["x"]).__dict__,
                            "COUNT_LITERAL_CEILING", 3)
        r = pp.check_count_literals()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_above_the_ceiling_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — one new literal past the frozen count."""
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": self.DIRTY}))
        monkeypatch.setitem(__import__("src.core.constants", fromlist=["x"]).__dict__,
                            "COUNT_LITERAL_CEILING", 2)
        r = pp.check_count_literals()
        assert r.passed is False, "count_literals is WARN-only again — the ratchet is off"
        assert any(d.name == "ratchet" and not d.passed for d in r.details)

    def test_a_clean_corpus_passes(self, tmp_path, monkeypatch):
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": self.CLEAN}))
        monkeypatch.setitem(__import__("src.core.constants", fromlist=["x"]).__dict__,
                            "COUNT_LITERAL_CEILING", 0)
        assert pp.check_count_literals().passed is True


class TestNumericalLiteralRatchet:
    CLEAN = r"\documentclass{article}\begin{document}Nothing dimensional.\end{document}"
    #: two matches: a nK value and a µm value, both outside \input{tables/}
    DIRTY = (r"\documentclass{article}\begin{document}"
             r"We measure 5.78 nK and a healing length of 1.334 \mu m."
             r"\end{document}")

    def test_at_the_ceiling_passes(self, tmp_path, monkeypatch):
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": self.DIRTY}))
        monkeypatch.setitem(__import__("src.core.constants", fromlist=["x"]).__dict__,
                            "NUMERICAL_LITERAL_CEILING", 99)
        assert pp.check_numerical_literals().passed is True

    def test_above_the_ceiling_fails(self, tmp_path, monkeypatch):
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": self.DIRTY}))
        monkeypatch.setitem(__import__("src.core.constants", fromlist=["x"]).__dict__,
                            "NUMERICAL_LITERAL_CEILING", 0)
        r = pp.check_numerical_literals()
        assert r.passed is False, "numerical_literals is WARN-only again"
        assert any(d.name == "ratchet" and not d.passed for d in r.details)


@pytest.mark.skipif(shutil.which("pdflatex") is None, reason="pdflatex not installed")
class TestLatexCompileVerdict:
    """End-to-end through the real check — tiny documents, so pdflatex is fast."""

    GOOD = "\\documentclass{article}\n\\begin{document}ok\\end{document}\n"
    BAD = "\\documentclass{article}\n\\begin{document}\\thisIsNotACommand\\end{document}\n"

    def _run(self, tmp_path, monkeypatch, drafts):
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, drafts))
        monkeypatch.setattr(pp, "BUNDLE_CODES", tuple(drafts))
        monkeypatch.setattr(_cfg, "FORCE_LATEX", True)
        return pp.check_paper_latex_compiles()

    def test_a_clean_draft_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch, {"D1": self.GOOD})
        assert r.passed is True, [(d.name, d.message) for d in r.details]

    def test_a_draft_with_fatal_errors_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. This is the assertion the check never made:
        it collected the failure, printed it as a warning, and returned True."""
        r = self._run(tmp_path, monkeypatch, {"D1": self.BAD})
        assert r.passed is False, (
            "a draft with fatal LaTeX errors reported PASS — the verdict is being "
            "discarded again (ADR-009 §Deferred item 3)")
        # ...and rendered as a FAILURE, not a ⚠. The original emitted
        # `passed=False, warning=True`, which print_results shows with a warning
        # glyph — a failing item that reads as advisory, one layer down from the
        # verdict bug itself.
        d1 = next(d for d in r.details if d.name == "compile:D1")
        assert d1.passed is False and not d1.warning

    def test_one_bad_draft_fails_the_whole_check(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch, {"D1": self.GOOD, "D2": self.BAD})
        assert r.passed is False

    def test_an_unforced_run_still_compiles_and_still_fails_on_a_bad_draft(
            self, tmp_path, monkeypatch):
        """⚠️ REPLACES `test_skipped_when_not_forced_still_passes`, deliberately.

        That test asserted *"the slow gate must stay a pass — a default full run
        is unaffected by this change, which is what makes it safe to land
        mid-remediation."* True when written, and the right call for landing item
        3 without collateral. But it froze the escape hatch in place: a default
        `validate.py` reported `paper_latex_compiles` green over **D3's two fatal
        errors**, because the default was not to compile at all.

        Re-measured before removing it, not assumed: pdflatex × 21 bundle drafts
        is **16.6 s**, and with the per-draft content-hash cache an unchanged
        corpus is ~0 s. The premise was cost; the cost is not there.

        So the contract is now the opposite one — WITHOUT `--force-latex` the
        check still compiles, and still fails on a bad draft."""
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": self.BAD}))
        monkeypatch.setattr(pp, "BUNDLE_CODES", ("D1",))
        monkeypatch.setattr(pp, "LATEX_COMPILE_CACHE", "nonexistent/.cache.json")
        monkeypatch.setattr(_cfg, "FORCE_LATEX", False)
        r = pp.check_paper_latex_compiles()
        assert r.passed is False, (
            "an unforced run passed over a draft with fatal LaTeX errors. The "
            "slow gate is back, and with it the false PASS over D3.")
        assert any(d.name == "compile:D1" for d in r.details), (
            "the check reported a verdict without naming the draft it compiled")
