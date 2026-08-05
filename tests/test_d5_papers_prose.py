"""D5 both-directions tests for `validation/checks/papers_prose.py` — audit QI-27.

Covers `paper_provenance` and `axiom_count_prose_consistency`.
(`paper_latex_compiles`, `count_literals` and `numerical_literals` were
mutation-verified under ADR-009 §Deferred item 3 in `test_always_pass_dispositions.py`;
`paper_toolchain_pin_drift`'s pure core `_tp_scan_lines` is covered by
`test_validate_toolchain_pin_drift.py`, mutation-verified here under QI-27.)

`axiom_count_prose_consistency` is the check ADR-009 §Deferred item 5 holds up as the
MODEL the literal checks should be raised to: it compares prose against COMPUTED TRUTH
(`docs/counts.json` → `lean.axioms`) rather than merely counting literals. Its whole
value is in the exclusions — the historical-attribution window, the preceding-negation
guard, the per-wave delta qualifiers, the word-numeral plurals — because each one is a
place a careless tightening would flag correct prose. Every exclusion is a leg here.

MUTATION-VERIFIED 2026-08-04 — 9 mutations, all CAUGHT, clean negative control.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate_helpers as _H  # noqa: E402
from validation.checks import papers_prose as pp  # noqa: E402


def _papers(tmp_path: Path, drafts: dict[str, str]) -> Path:
    root = tmp_path / "papers"
    for code, body in drafts.items():
        d = root / code
        d.mkdir(parents=True, exist_ok=True)
        (d / "paper_draft.tex").write_text(body)
    return root


def _lean(tmp_path: Path, files: dict[str, str]) -> Path:
    root = tmp_path / "SKEFTHawking"
    root.mkdir(parents=True, exist_ok=True)
    for rel, body in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(body)
    return root


class TestPaperProvenance:
    """Every `\\texttt{theorem_name}` in a draft resolves to a real Lean theorem;
    figures exist; no placeholder bibliography."""

    def _run(self, tmp_path, monkeypatch, drafts, lean_files=None):
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, drafts))
        monkeypatch.setattr(_H, "LEAN_DIR", _lean(tmp_path, lean_files or {}))
        return pp.check_paper_provenance()

    def test_a_resolving_reference_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch,
                      {"D1": r"See \texttt{real_theorem} for the bound."},
                      {"M.lean": "theorem real_theorem : True := trivial\n"})
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_nonexistent_theorem_reference_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — a paper citing a theorem that does not exist."""
        r = self._run(tmp_path, monkeypatch,
                      {"D1": r"See \texttt{ghost_theorem} for the bound."},
                      {"M.lean": "theorem real_theorem : True := trivial\n"})
        assert r.passed is False, (
            "a draft citing a nonexistent Lean theorem passed — the paper→Lean "
            "reference chain is unenforced")
        assert any("Not in Lean" in (d.message or "") for d in r.details)

    def test_a_theorem_in_a_subdirectory_resolves(self, tmp_path, monkeypatch):
        """QI-01 at this call site. `glob` covered 1,373 of 2,039 files, hiding 5,469
        theorem names — and this check FAILS on a reference it cannot resolve, so a
        draft citing a theorem in `QuantumNetwork/` would have been reported as citing
        a nonexistent one. No draft did, which is why it never fired."""
        r = self._run(tmp_path, monkeypatch,
                      {"D1": r"See \texttt{deep_theorem} for the bound."},
                      {"Pkg/Nested/M.lean": "theorem deep_theorem : True := trivial\n"})
        assert r.passed is True, (
            "a theorem in a SUBDIRECTORY read as missing — the name scan is "
            "non-recursive again (audit QI-01)")

    def test_a_single_word_texttt_is_not_treated_as_a_theorem(self, tmp_path, monkeypatch):
        """The `'_' in r` filter. `\\texttt{sorry}` or `\\texttt{lake}` is prose
        formatting, not a theorem reference; without the filter every such use would
        be reported as a missing theorem."""
        r = self._run(tmp_path, monkeypatch,
                      {"D1": r"Run \texttt{lake} with zero \texttt{sorry}."}, {})
        assert r.passed is True

    def test_an_fbox_placeholder_figure_fails(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch,
                      {"D1": r"\fbox{\parbox{3in}{figure goes here}}"}, {})
        assert r.passed is False
        assert any("fbox placeholder" in (d.message or "") for d in r.details)

    def test_a_missing_included_figure_fails(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch,
                      {"D1": r"\includegraphics[width=3in]{figures/absent}"}, {})
        assert r.passed is False
        assert any("Missing" in (d.message or "") for d in r.details)

    def test_a_figure_resolved_by_extension_passes(self, tmp_path, monkeypatch):
        """LaTeX auto-appends `.pdf`/`.png`, so a draft legitimately writes the stem.
        Requiring the literal path would flag every correct draft."""
        root = _papers(tmp_path, {"D1": r"\includegraphics{figures/fig1}"})
        (root / "D1" / "figures").mkdir(parents=True)
        (root / "D1" / "figures" / "fig1.png").write_bytes(b"\x89PNG")
        monkeypatch.setattr(_H, "PAPERS_DIR", root)
        monkeypatch.setattr(_H, "LEAN_DIR", _lean(tmp_path, {}))
        assert pp.check_paper_provenance().passed is True

    def test_a_placeholder_bibliography_entry_fails(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch,
                      {"D1": r"\bibitem{x} Nature \textbf{XXX}, arXiv:2604.XXXXX"}, {})
        assert r.passed is False
        assert any("placeholder bibliography" in (d.message or "") for d in r.details)

    def test_a_placeholder_inside_a_latex_comment_is_ignored(self, tmp_path, monkeypatch):
        """A historical cleanup note — `% [2026-05-04 cleanup: … arXiv:2604.XXXXX …]`
        — is a record, not a live placeholder. Flagging it would punish the very notes
        that document the cleanup."""
        r = self._run(tmp_path, monkeypatch,
                      {"D1": "Real prose.\n% [cleanup: was arXiv:2604.XXXXX]\n"}, {})
        assert r.passed is True, (
            "a placeholder inside a LaTeX COMMENT was flagged — comments are stripped "
            "precisely so cleanup records do not false-positive")


class TestAxiomCountProseConsistency:
    """Prose axiom claims vs `docs/counts.json`. ADR-009 §Deferred item 5 declines
    merging this with `count_literals` because THIS one compares against computed
    truth — merging would destroy the comparison."""

    def test_a_single_axiom_claim_against_zero_axioms_fails(self):
        """FIRES ON THE SEEDED DEFECT — the F-flagship failure class from the
        2026-06-05 external review verbatim: prose claiming 'one true axiom' while
        the live count is 0."""
        f = pp._axiom_prose_findings("The theory rests on one true axiom.", 0)
        assert any(x["kind"] == "singular" and x["fail"] for x in f), (
            "a present-tense single-axiom claim against a live count of 0 did not "
            "hard-fail — this is the external-review failure class")

    def test_the_same_claim_with_a_live_axiom_does_not_hard_fail(self):
        """SILENT ON CORRECT DATA — if there really is one axiom, saying so is right."""
        f = pp._axiom_prose_findings("The theory rests on one true axiom.", 1)
        assert not any(x["fail"] for x in f)
        assert not any(x["mismatch"] for x in f)

    def test_a_historical_attribution_never_flags(self):
        """The ±120-char window. 'formerly axiom gapped_interface_axiom' is the
        D2/F-style legitimate retrospective — the record of the retirement, which is
        exactly the prose a careless guard would punish."""
        text = ("The gapped interface was formerly an axiom; it is now the tracked "
                "Prop TPFConjecture, so there is one axiom in the historical account.")
        assert pp._axiom_prose_findings(text, 0) == [], (
            "a historical-attribution axiom claim was flagged — the retirement record "
            "is the opposite of a stale claim")

    def test_a_preceding_negation_never_flags(self):
        """'no single axiom …' asserts the opposite of what the pattern matches."""
        assert pp._axiom_prose_findings("There is no single axiom behind this.", 0) == []

    def test_a_per_wave_delta_claim_is_excluded(self):
        """'zero NEW axioms' is a delta, not a total. Comparing it to the total would
        flag every correct wave-close sentence."""
        assert pp._axiom_prose_findings("This wave introduces zero new axioms.", 3) == []

    def test_a_numeric_plural_mismatch_is_advisory_not_fatal(self):
        """Numeric plural drift is real signal but not a build break — it is often a
        legitimately different population (physics axioms vs project-local ones)."""
        f = pp._axiom_prose_findings("The construction uses 3 axioms.", 0)
        assert f and all(not x["fail"] for x in f)
        assert any(x["kind"] == "plural_mismatch" and x["mismatch"] for x in f)

    def test_a_matching_plural_claim_is_silent(self):
        assert pp._axiom_prose_findings("The construction uses 3 axioms.", 3) == []

    def test_a_word_numeral_plural_is_excluded_by_design(self):
        """'three axioms' is the Son-action physics-axioms idiom in D1/F — a different
        population from project-local axioms. Only digit and `zero` literals compare."""
        assert pp._axiom_prose_findings("The Son action rests on three axioms.", 0) == []

    def test_a_latex_comment_is_not_scanned(self):
        """Comments are blanked with offsets preserved, so a commented-out old claim
        neither flags nor shifts the reported line numbers."""
        assert pp._axiom_prose_findings("Real prose.\n% we had one axiom here\n", 0) == []

    def test_the_gapped_axiom_named_in_the_present_tense_fails(self):
        """A named retired axiom in the present tense is the specific regression the
        check was written against."""
        f = pp._axiom_prose_findings(r"We assume the axiom \texttt{gapped_interface}.", 0)
        assert any(x["kind"] == "gapped_present" and x["fail"] for x in f)

    def test_the_line_number_survives_comment_stripping(self):
        """Offsets are preserved on purpose — a finding that reports the wrong line
        sends the author to the wrong place, which is how a true finding gets
        dismissed as noise."""
        text = "line one\n% a comment\nthe sole axiom is here\n"
        f = pp._axiom_prose_findings(text, 0)
        assert f and f[0]["line"] == 3, f"expected line 3, got {f[0]['line'] if f else None}"


class TestAxiomCountProseConsistencyCheckBody:
    """The registered CHECK, not just its pure core.

    ⚠️ **Added after review, 2026-08-04.** The class above exercises
    `_axiom_prose_findings` thoroughly — but nothing invoked
    `check_axiom_count_prose_consistency` itself, so the check's own body was
    untested: the `counts.json` read, the draft iteration, the fail/warn split, and
    the verdict. `MUTATION_VERIFIED` nonetheless listed the check, and the seam guard
    accepted it because the name appeared in a module docstring.

    *Testing a pure core is not testing the check that calls it.* The core can be
    perfect while the caller reads the wrong key, iterates the wrong files, or
    discards the result — which is the exact defect class ADR-009 §Deferred item 3
    found in `paper_latex_compiles` (it computed `all_pass` and returned `True`).
    """

    def _run(self, tmp_path, monkeypatch, *, drafts, axioms=0, counts=None):
        docs = tmp_path / "docs"
        docs.mkdir(parents=True, exist_ok=True)
        (docs / "counts.json").write_text(
            counts if counts is not None else json.dumps({"lean": {"axioms": axioms}}))
        monkeypatch.setattr(_H, "COUNTS_JSON_PATH", docs / "counts.json")
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, drafts))
        return pp.check_axiom_count_prose_consistency()

    def test_a_clean_corpus_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch,
                      drafts={"D1": "The construction assumes nothing unusual."})
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]
        assert any(d.name == "all_consistent" for d in r.details)

    def test_a_stale_single_axiom_claim_fails_the_CHECK(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — through the check, not the core. This is the
        leg that proves the core's finding actually reaches the verdict."""
        r = self._run(tmp_path, monkeypatch,
                      drafts={"D1": "The theory rests on one true axiom."}, axioms=0)
        assert r.passed is False, (
            "the core reported a hard finding and the CHECK still passed — the "
            "verdict is being discarded (the paper_latex_compiles defect shape)")
        assert any(d.name.startswith("stale_axiom_claim:D1:") for d in r.details)

    def test_an_advisory_mismatch_does_not_fail_the_check(self, tmp_path, monkeypatch):
        """The fail/warn split lives in the CHECK, not the core — the core only
        labels findings. A numeric plural mismatch must warn, never block."""
        r = self._run(tmp_path, monkeypatch,
                      drafts={"D1": "The construction uses 3 axioms."}, axioms=0)
        assert r.passed is True
        assert any(d.name.startswith("axiom_count_mismatch:") and d.warning
                   for d in r.details)

    def test_the_axiom_count_is_read_from_counts_json(self, tmp_path, monkeypatch):
        """The same prose flips verdict with the COMPUTED count — which is what makes
        this a comparison against truth rather than a literal scan (ADR-009 item 5's
        reason for declining the merge with `count_literals`)."""
        prose = {"D1": "The theory rests on one true axiom."}
        assert self._run(tmp_path, monkeypatch, drafts=prose, axioms=0).passed is False
        assert self._run(tmp_path, monkeypatch, drafts=prose, axioms=1).passed is True

    def test_every_draft_is_scanned_not_just_the_first(self, tmp_path, monkeypatch):
        """Iteration is the check's job. A loop that broke early would leave later
        drafts unexamined while reporting a clean run."""
        r = self._run(tmp_path, monkeypatch, drafts={
            "D1": "Nothing to see.",
            "D2": "The theory rests on one true axiom."}, axioms=0)
        assert r.passed is False
        assert any(d.name.startswith("stale_axiom_claim:D2:") for d in r.details)
        assert "2 paper drafts" in next(d for d in r.details if d.name == "summary").message

    def test_a_missing_counts_json_fails_rather_than_passes(self, tmp_path, monkeypatch):
        """Cannot-measure is not success: with no computed count there is nothing to
        compare prose against."""
        monkeypatch.setattr(_H, "COUNTS_JSON_PATH", tmp_path / "absent.json")
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": "x"}))
        r = pp.check_axiom_count_prose_consistency()
        assert r.passed is False and "update_counts" in (r.error or "")

    def test_an_unreadable_counts_json_fails(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch, drafts={"D1": "x"}, counts="{not json")
        assert r.passed is False and "counts.json" in (r.error or "")
