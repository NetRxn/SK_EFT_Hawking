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
    """Figures referenced by a draft exist on disk; no placeholder figure box or
    bibliography entry ships.

    ⚠️ THE FOUR THEOREM-REFERENCE TESTS WERE DELETED 2026-08-05 with the leg they
    covered (audit finding QI-32), and the reason is worth more than the tests were.

    They passed. They were both-directions. They were mutation-verified on
    2026-08-04 — and the leg they certified had been incapable of matching a single
    reference in the production corpus since 2026-03-26.

    The regex was `\\\\texttt\\{([a-z_][a-zA-Z0-9_]*)\\}`, whose character class cannot
    cross a backslash. LaTeX escapes `_` as `\\_`, so every real reference is written
    `\\texttt{ghost\\_theorem}` and never matched. These fixtures wrote
    `\\texttt{ghost_theorem}` — a spelling that does not survive `pdflatex` and
    therefore does not occur in any draft. The fixture used the only spelling under
    which the leg worked.

    That is QI-30's criterion stated from the other side: *a mutation caught against
    a patched fixture does not establish that the check can fail in production.*
    Four green tests over a dead guard is the exact failure this audit exists to
    find, and it was found by measuring the corpus (480 raw matches, **0** with `_`,
    against 1,963 blocks containing `\\_`), not by running the tests again.

    Lean-name resolution now lives entirely in `prose_lean_refs`, which unescapes
    `\\_`; its legacy-draft leg and ratchet are covered in
    `test_d5_prose_lean_refs.py`.
    """

    def _run(self, tmp_path, monkeypatch, drafts, lean_files=None):
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, drafts))
        monkeypatch.setattr(_H, "LEAN_DIR", _lean(tmp_path, lean_files or {}))
        return pp.check_paper_provenance()

    def test_a_clean_draft_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch,
                      {"D1": r"See \texttt{real\_theorem} for the bound."}, {})
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_an_ESCAPED_underscore_reference_is_no_longer_this_check_s_business(
            self, tmp_path, monkeypatch):
        """The regression pin for QI-32. A draft citing a nonexistent theorem in the
        form LaTeX actually produces must NOT be silently reported here as verified —
        this check no longer claims to resolve theorem names at all, and a future
        re-introduction that once again cannot see `\\_` would fail this test."""
        r = self._run(tmp_path, monkeypatch,
                      {"D1": r"See \texttt{ghost\_theorem} for the bound."}, {})
        assert not any("theorem_refs" in d.name for d in r.details), (
            "paper_provenance is reporting on theorem references again — if that leg "
            "is revived it must handle the `\\_` escape, which is the whole of QI-32")

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


class TestBundleTablesUsePipeline:
    """⚠️ Operator ruling 2026-08-05: *"if a table is used in a bundle, it needs the
    table pipeline — otherwise the pipeline is worthless."*

    Git archaeology backs it. `68899aef` (2026-04-15), the pipeline's originating
    commit: *"After this lands, tabular numerical claims cannot drift from the
    canonical pipeline: every value comes from an autogenerated tex snippet produced
    by a declarative spec."* `BUNDLE_LIFT_PROCEDURE.md` §7 makes it procedure.

    MEASURED 2026-08-05: **zero of 21 bundles have a `tables.py`**, and 3 carry
    hand-written tabulars (D1 1, E1 1, L2 2). The pipeline existed, was tested, and
    protected only the legacy per-paper drafts it was retrofitted onto.
    """

    def _run(self, tmp_path, monkeypatch, drafts):
        papers = tmp_path / "papers"
        for code, body in drafts.items():
            d = papers / code
            d.mkdir(parents=True)
            (d / "paper_draft.tex").write_text(body)
        monkeypatch.setattr(pp._H, "PAPERS_DIR", papers)
        monkeypatch.setattr(pp, "BUNDLE_CODES", tuple(drafts))
        return pp.check_bundle_tables_use_pipeline()

    def test_a_piped_table_is_clean(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — the compliant shape must not be nagged."""
        r = self._run(tmp_path, monkeypatch,
                      {"D1": "text \\input{tables/t1.tex} more"})
        assert r.passed is True
        assert "0 hand-written" in r.details[0].message

    def test_a_hand_written_tabular_over_ceiling_FAILS(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        monkeypatch.setattr(pp, "BUNDLE_HANDWRITTEN_TABLE_CEILING", 0)
        r = self._run(tmp_path, monkeypatch,
                      {"D1": "\\begin{tabular}{cc}a&b\\\\\\end{tabular}"})
        assert r.passed is False, (
            "a hand-written tabular above the ceiling did not fail — the pipeline's "
            "no-drift guarantee is unenforced for bundles")
        assert any("D1" in d.name for d in r.details)

    def test_a_commented_out_tabular_does_not_count(self, tmp_path, monkeypatch):
        """The scan strips TeX comments; a discussion of tables in a comment is not
        a table."""
        monkeypatch.setattr(pp, "BUNDLE_HANDWRITTEN_TABLE_CEILING", 0)
        r = self._run(tmp_path, monkeypatch,
                      {"D1": "% \\begin{tabular}{cc} example in a comment\ntext"})
        assert r.passed is True

    def test_no_drafts_is_UNVERIFIED_not_passing(self, tmp_path, monkeypatch):
        """Absence of the population must not read as compliance."""
        monkeypatch.setattr(pp._H, "PAPERS_DIR", tmp_path / "empty")
        monkeypatch.setattr(pp, "BUNDLE_CODES", ("D1",))
        r = pp.check_bundle_tables_use_pipeline()
        assert r.passed is False and r.measured is False

    def test_the_ceiling_has_ZERO_HEADROOM_against_the_live_tree(self):
        """House ratchet idiom, measured against production."""
        r = pp.check_bundle_tables_use_pipeline()
        n = int(r.details[0].message.split()[0])
        assert n == pp.BUNDLE_HANDWRITTEN_TABLE_CEILING, (
            f"{n} hand-written tabular(s) live against a ceiling of "
            f"{pp.BUNDLE_HANDWRITTEN_TABLE_CEILING}. If it dropped, LOWER the ceiling "
            f"in the same commit; if it rose, add the tables.py spec.")


class TestBundleCrossReferencesResolve:
    """`bundle_cross_references_resolve` — a `\\ref` with no `\\label` renders `??`.

    Found in D3 (3 sites) on a tree where `paper_latex_compiles` reported 21/21 bundles
    clean, because that check hard-fails on fatal `!` breakage only.
    """

    def _bundle(self, tmp_path, monkeypatch, body: str, extra: dict | None = None):
        papers = tmp_path / "papers"
        (papers / "D1").mkdir(parents=True)
        (papers / "D1" / "paper_draft.tex").write_text(body)
        for name, content in (extra or {}).items():
            f = papers / "D1" / name
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(content)
        import bundle_registry as registry
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        monkeypatch.setattr(registry, "BUNDLE_CODES", ("D1",))
        import validation.checks.papers_prose as m
        monkeypatch.setattr(m, "BUNDLE_CODES", ("D1",), raising=False)

    def test_live_corpus_is_clean(self):
        r = pp.check_bundle_cross_references_resolve()
        assert r.passed, [d.message for d in r.details if not d.passed]

    def test_a_matching_label_passes(self, tmp_path, monkeypatch):
        self._bundle(tmp_path, monkeypatch,
                     "\\label{sec:a}\nSee \\ref{sec:a}.\n")
        assert pp.check_bundle_cross_references_resolve().passed

    def test_a_dangling_ref_fails_and_names_it(self, tmp_path, monkeypatch):
        self._bundle(tmp_path, monkeypatch,
                     "\\label{sec:a}\nSee \\ref{sec:ghost}.\n")
        r = pp.check_bundle_cross_references_resolve()
        assert not r.passed
        assert any("sec:ghost" in d.message for d in r.details if not d.passed)

    def test_eqref_and_cref_are_covered(self, tmp_path, monkeypatch):
        self._bundle(tmp_path, monkeypatch,
                     "\\label{eq:a}\nSee \\eqref{eq:ghost} and \\cref{eq:a}.\n")
        r = pp.check_bundle_cross_references_resolve()
        assert not r.passed and any("eq:ghost" in d.message for d in r.details if not d.passed)

    def test_a_label_in_an_INPUT_file_counts(self, tmp_path, monkeypatch):
        """PINS THE FALSE POSITIVE a draft-only scan would produce: generated tables
        define labels, and the closure helper is why they are seen."""
        self._bundle(tmp_path, monkeypatch,
                     "\\input{tables/t1}\nSee \\ref{tab:one}.\n",
                     extra={"tables/t1.tex": "\\label{tab:one}\n"})
        assert pp.check_bundle_cross_references_resolve().passed

    def test_an_empty_population_is_UNVERIFIED_not_clean(self, tmp_path, monkeypatch):
        self._bundle(tmp_path, monkeypatch, "prose with no references at all\n")
        r = pp.check_bundle_cross_references_resolve()
        assert not r.passed and not r.measured

    def test_the_ratchet_has_zero_headroom(self):
        """Target is 0 unresolved; any regression fails on the next run."""
        r = pp.check_bundle_cross_references_resolve()
        summary = next(d for d in r.details if d.name == "summary")
        assert "0 unresolved" in summary.message
