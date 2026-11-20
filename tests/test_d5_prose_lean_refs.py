"""D5 both-directions tests for `validation/checks/prose_lean_refs.py` — audit QI-27.

Two checks: `prose_theorem_reference_coverage`, `theorem_name_embedded_citations`.

WHAT THIS ADDS TO `tests/test_validate_prose_checks.py`
--------------------------------------------------------
That file is already good, and it is the D5 precedent working: `_extract_prose_lean_candidates`,
`_prose_occurrence_disclaimed` and `_embedded_citation_pairs` were extracted as pure cores
SPECIFICALLY to be testable, and it exercises all three thoroughly.

ADR-009 §Context nevertheless rates these checks "weakly" covered, and re-reading the file
shows exactly why: the CORES are well tested, but the CHECKS themselves appear only in
`TestLiveRepoSmoke`, which asserts `result.passed` on a compliant tree. So the step from
"the core found a problem" to "the check FAILS" — the verdict propagation — was untested,
and it is the step that decides whether anything blocks.

This file covers that step, and only that step. It does not restate the core tests.

MUTATION-VERIFIED 2026-08-04 — 7 mutations, all CAUGHT, clean negative control.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate_helpers as _H  # noqa: E402
from validation.checks import prose_lean_refs as plr  # noqa: E402


def _bundle(tmp_path: Path, monkeypatch, code: str, body: str) -> Path:
    root = tmp_path / "papers"
    (root / code).mkdir(parents=True, exist_ok=True)
    (root / code / "paper_draft.tex").write_text(body)
    monkeypatch.setattr(_H, "PAPERS_DIR", root)
    monkeypatch.setattr(plr, "BUNDLE_CODES", (code,))
    return root


def _index(monkeypatch, names=("real_theorem",)):
    """Stand in for the cached lean-name index. Patching the loader rather than the
    cache global keeps the module's own memoization out of the test."""
    p = SK_ROOT / "lean" / "lean_deps.json"
    monkeypatch.setattr(_H, "lean_deps_present", lambda: True)
    monkeypatch.setattr(plr, "_load_lean_name_index", lambda: {
        "full": {f"SKEFTHawking.M.{n}" for n in names},
        "short": {n: f"SKEFTHawking.M.{n}" for n in names},
        "modules": set(), "registry": set(),
    })
    return p


class TestProseTheoremReferenceCoverage:
    """The `wen_adw_factor_6000` failure class: bundle prose naming a Lean declaration
    that does not exist in the built library."""

    def test_a_resolving_reference_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        _index(monkeypatch)
        _bundle(tmp_path, monkeypatch, "D1", r"See \texttt{real_theorem}.")
        monkeypatch.setattr(plr, "_resolve_prose_ref", lambda t, i, deep=True: "OK")
        r = plr.check_prose_theorem_reference_coverage()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_an_absent_reference_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — and this is the leg the pre-existing file
        could not have: its check-level tests only ever run against a compliant tree."""
        _index(monkeypatch)
        _bundle(tmp_path, monkeypatch, "D1", r"See \texttt{ghost_theorem}.")
        monkeypatch.setattr(plr, "_resolve_prose_ref", lambda t, i, deep=True: "ABSENT")
        r = plr.check_prose_theorem_reference_coverage()
        assert r.passed is False, (
            "an unresolvable bundle-draft reference did not fail the check — the "
            "verdict does not propagate from the resolver")
        assert any(d.name.startswith("unresolved:D1:") for d in r.details)

    def test_a_disclaimed_absent_reference_does_not_fail(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA. Prose recording a RENAMED or RETIRED name is a
        record, not drift — flagging it would punish the documentation of the rename."""
        _index(monkeypatch)
        _bundle(tmp_path, monkeypatch, "D1",
                r"The theorem \texttt{ghost_theorem} was renamed in Phase 6.")
        monkeypatch.setattr(plr, "_resolve_prose_ref", lambda t, i, deep=True: "ABSENT")
        assert plr.check_prose_theorem_reference_coverage().passed is True

    def test_the_exemption_requires_EVERY_occurrence_to_be_disclaimed(
            self, tmp_path, monkeypatch):
        """The `all(...)` is load-bearing. One disclaimed mention must not license a
        bare one elsewhere in the same draft — that is how a real drift hides behind
        an unrelated historical note."""
        _index(monkeypatch)
        # MEASURED: the disclaimer window is +/-200 chars EACH SIDE, so the two
        # occurrences must be separated by more than 400 to isolate the bare one.
        # My first draft used 40 newlines and both sat inside the same window,
        # which tested nothing.
        filler = "\nfiller line.\n" * 60
        body = (r"The theorem \texttt{ghost_theorem} was renamed." + filler
                + r"We rely on \texttt{ghost_theorem} for the bound.")
        assert len(filler) > 2 * plr._PROSE_DISCLAIMER_WINDOW
        _bundle(tmp_path, monkeypatch, "D1", body)
        monkeypatch.setattr(plr, "_resolve_prose_ref", lambda t, i, deep=True: "ABSENT")
        assert plr.check_prose_theorem_reference_coverage().passed is False, (
            "a BARE occurrence was excused by a disclaimed one elsewhere in the same "
            "draft — the exemption must require every occurrence")

    def test_a_drifted_reference_is_advisory(self, tmp_path, monkeypatch):
        """The short name exists under a different namespace — a rename candidate, not
        a phantom. Hard-failing it would conflate the two."""
        _index(monkeypatch)
        _bundle(tmp_path, monkeypatch, "D1", r"See \texttt{Other.real_theorem}.")
        monkeypatch.setattr(plr, "_resolve_prose_ref", lambda t, i, deep=True: "DRIFTED")
        r = plr.check_prose_theorem_reference_coverage()
        assert r.passed is True
        assert any(d.name.startswith("drifted:") and d.warning for d in r.details)

    def test_a_waived_pair_passes_but_stays_visible(self, tmp_path, monkeypatch):
        """A waiver must never be silent — `_PROSE_REF_WAIVERS` is capped at 5 by its
        own comment, and an invisible waiver is how that cap gets exceeded."""
        _index(monkeypatch)
        _bundle(tmp_path, monkeypatch, "I1", r"See \texttt{gap_solution_bounded}.")
        monkeypatch.setattr(plr, "_resolve_prose_ref", lambda t, i, deep=True: "ABSENT")
        r = plr.check_prose_theorem_reference_coverage()
        assert r.passed is True
        assert any(d.name.startswith("waived:I1:") and d.warning for d in r.details), (
            "a documented waiver was applied SILENTLY — every use must surface")

    def test_a_LEGACY_draft_reference_is_measured_not_ignored(
            self, tmp_path, monkeypatch):
        """The QI-32 leg. 43 non-bundle drafts had NO Lean-name coverage: the leg that
        nominally covered them lived in `paper_provenance` and its regex could not
        cross the `\\_` LaTeX escape, so it matched zero references for five months.

        Note the fixture writes `\\texttt{ghost\\_theorem}` — the form `pdflatex`
        actually produces. The deleted leg's fixtures wrote the unescaped form, which
        is why they were green over a dead guard."""
        _index(monkeypatch)
        root = _bundle(tmp_path, monkeypatch, "D1", "no references here.")
        (root / "paper9_legacy").mkdir(parents=True)
        (root / "paper9_legacy" / "paper_draft.tex").write_text(
            r"We rely on \texttt{ghost\_theorem} for the bound.")
        monkeypatch.setattr(plr, "_resolve_prose_ref", lambda t, i, deep=True: "ABSENT")
        monkeypatch.setattr(plr, "_prose_occurrence_disclaimed", lambda s, o: False)
        r = plr.check_prose_theorem_reference_coverage()
        assert any(d.name == "legacy:paper9_legacy" for d in r.details), (
            "a legacy draft's unresolved reference was not measured at all — the "
            "`\\_`-escaped form is the only form the corpus contains (QI-32)")

    def test_the_legacy_ratchet_fails_above_the_ceiling(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. Inherited legacy debt is frozen, not tolerated:
        one NEW unresolved reference past the ceiling must turn the check red. Without
        this the leg is a report, and a report blocks nothing."""
        _index(monkeypatch)
        root = _bundle(tmp_path, monkeypatch, "D1", "no references here.")
        (root / "paper9_legacy").mkdir(parents=True)
        (root / "paper9_legacy" / "paper_draft.tex").write_text(
            r"We rely on \texttt{ghost\_theorem} for the bound.")
        monkeypatch.setattr(plr, "_resolve_prose_ref", lambda t, i, deep=True: "ABSENT")
        monkeypatch.setattr(plr, "_prose_occurrence_disclaimed", lambda s, o: False)
        from src.core import constants
        monkeypatch.setattr(constants, "LEGACY_DRAFT_UNRESOLVED_REF_CEILING", 0)
        r = plr.check_prose_theorem_reference_coverage()
        assert r.passed is False, (
            "1 unresolved legacy reference against a ceiling of 0 did not fail — "
            "the ratchet does not propagate to the verdict")
        assert any(d.name == "legacy_ratchet" and not d.passed for d in r.details)

    def test_the_legacy_ratchet_is_SILENT_at_the_ceiling(self, tmp_path, monkeypatch):
        """The other direction, and the one that keeps the gate switched on. Inherited
        debt sitting exactly AT the frozen ceiling must not fail — repairing the 81 is
        ADR-010 scope, and a gate that fires on work nobody has been asked to do gets
        turned off."""
        _index(monkeypatch)
        root = _bundle(tmp_path, monkeypatch, "D1", "no references here.")
        (root / "paper9_legacy").mkdir(parents=True)
        (root / "paper9_legacy" / "paper_draft.tex").write_text(
            r"We rely on \texttt{ghost\_theorem} for the bound.")
        monkeypatch.setattr(plr, "_resolve_prose_ref", lambda t, i, deep=True: "ABSENT")
        monkeypatch.setattr(plr, "_prose_occurrence_disclaimed", lambda s, o: False)
        from src.core import constants
        monkeypatch.setattr(constants, "LEGACY_DRAFT_UNRESOLVED_REF_CEILING", 1)
        r = plr.check_prose_theorem_reference_coverage()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_the_live_legacy_ceiling_has_ZERO_headroom(self, prose_ref_coverage_result):
        """The ratchet's whole value is that it is measured AT the corpus, not above
        it. A ceiling with slack admits new debt silently — the failure mode
        `recurrence_reopens_closures` demonstrated three times, where a constant was
        set beyond what the data could reach and the guard could never fire.

        Runs against the REAL corpus, not a fixture: this is the assertion that would
        catch the ceiling being raised to buy a green run."""
        from src.core.constants import LEGACY_DRAFT_UNRESOLVED_REF_CEILING as ceil
        r = prose_ref_coverage_result      # session-shared; this call is unpatched
        summary = next(d for d in r.details if d.name == "legacy_ratchet")
        import re as _re
        m = _re.search(r"(\d+) unresolved", summary.message or "")
        assert m, f"legacy_ratchet message shape changed: {summary.message!r}"
        assert int(m.group(1)) == ceil, (
            f"the live corpus carries {m.group(1)} unresolved legacy references but "
            f"the ceiling is {ceil}. If the corpus improved, LOWER the ceiling in the "
            f"same commit — headroom is how a ratchet stops ratcheting.")

    def test_a_missing_lean_deps_FAILS(self, tmp_path, monkeypatch):
        """⚠️ The H4 divergence, from the STRICT side: absence is FAIL here and PASS
        in the four substrate checks. ADR-009 §Deferred item 4 DECLINED unifying them;
        this is the arguably-correct policy and is pinned so a sweep is deliberate."""
        monkeypatch.setattr(_H, "lean_deps_present", lambda: False)
        assert plr.check_prose_theorem_reference_coverage().passed is False


class TestTexttExAliasesAreScanned:
    """The `\\texttt` ALIAS hole — found by the ADR-010 measurement pass, 2026-08-05.

    D8, D9 and paper14 route every Lean reference through a preamble alias
    (`\\newcommand{\\lean}[1]{\\texttt{#1}}`) instead of writing `\\texttt` at each
    site. The extractor matched the literal `\\texttt` only, so **288 references sat
    beyond the check while it reported PASS on "21 bundle drafts scanned"** — this
    branch's own defect class, absence of measurement rendered as success, and the
    reason `CHECK_AUTHORING_GUIDE.md` §2.5 says a scan needs a population guard.

    The check's own summary count is what made it look covered: 671 candidates read
    as thorough. It was 671 out of 889.
    """

    def test_alias_definitions_are_discovered(self):
        src = r"\newcommand{\lean}[1]{\texttt{#1}}" "\n" r"\newcommand{\thm}[1]{\mathtt{#1}}"
        assert plr._prose_verbatim_macros(src) == frozenset({"texttt", "lean", "thm"})

    def test_a_draft_with_no_alias_is_unchanged(self):
        assert plr._prose_verbatim_macros(r"\section{x} \texttt{a_b}") == frozenset({"texttt"})

    def test_alias_uses_become_candidates(self):
        src = (r"\newcommand{\lean}[1]{\texttt{#1}}"
               "\n" r"We prove \lean{avgGateFidelity\_eq} and \texttt{plain\_ref}.")
        toks = {t for t, _o in plr._extract_prose_lean_candidates(src)}
        assert "avgGateFidelity_eq" in toks, (
            "an aliased reference was not extracted — the alias hole is back")
        assert "plain_ref" in toks, "literal \\texttt extraction regressed"

    def test_verb_spans_become_candidates(self):
        r"""The third form. `\verb|x|` takes an arbitrary delimiter, so neither the
        `\texttt` regex nor the alias regex sees it."""
        toks = {t for t, _o in plr._extract_prose_lean_candidates(
            r"proves \verb|bbpsswRecurrence_gt| and \verb+endToEndFidelity.eq+ here")}
        assert "bbpsswRecurrence_gt" in toks
        assert "endToEndFidelity.eq" in toks, "a non-| \\verb delimiter was missed"

    def test_verb_does_not_swallow_across_two_spans(self):
        r"""A greedy `\verb` regex would match from the first delimiter to the LAST,
        merging two references into one unparseable token and silently dropping both."""
        toks = {t for t, _o in plr._extract_prose_lean_candidates(
            r"\verb|first_ref| and text and \verb|second_ref|")}
        assert toks == {"first_ref", "second_ref"}, toks

    def test_the_LIVE_corpus_exercises_the_verb_extraction_path(self):
        r"""PRODUCTION-SEEDED (QI-30). Asserts the DECIDER: that the `\verb` path
        extracts references the verb-blind scanner misses, measured on the live corpus.

        ⚠️ DO NOT key this on one named draft or a candidate-count threshold. A
        threshold answers "does this draft still have many refs", which drafting
        changes, not "does the `\verb` path work", which is the property. Two
        recalibrations were already spent chasing that difference, and the last one
        went stale the moment the named draft was redrafted — its `\verb` contribution
        is now 1, so it could no longer detect the hole reopening at all.

        The differential cannot go stale that way: strip every `\verb|…|` span from a
        draft, re-extract, and the tokens that disappear are exactly what the path
        contributes. If the extractor stops reading `\verb`, that difference goes to
        zero corpus-wide and this fails, whatever any individual draft looks like."""
        drafts = sorted((SK_ROOT / "papers").glob("*/paper_draft.tex"))
        if not drafts:                             # pragma: no cover - corpus in-repo
            import pytest
            pytest.skip("draft corpus absent")
        contributions: dict[str, int] = {}
        for tex in drafts:
            src = tex.read_text(errors="replace")
            aware = {t for t, _o in plr._extract_prose_lean_candidates(src)}
            blind = {t for t, _o in plr._extract_prose_lean_candidates(
                re.sub(r"\\verb\|[^|]*\|", " ", src))}
            if aware - blind:
                contributions[tex.parent.name] = len(aware - blind)
        assert contributions, (
            "no draft in the corpus yields a single reference that the verb-blind "
            "scanner misses — the \\verb extraction path is dead. Either the "
            "extractor stopped reading \\verb, or no draft uses it any more; the "
            "first is a regression and the second means this guard needs a live "
            "population to watch.")

    def test_the_LIVE_D9_draft_has_its_alias_refs_scanned(self):
        """PRODUCTION-SEEDED (QI-30). Asserted against the real `papers/D9/paper_draft.tex`,
        not a fixture — a fixture proves the regex works, not that the corpus is reached.
        Reverting the alias support drops this from ~170 to ~10 and fails here.
        """
        tex = (SK_ROOT / "papers" / "D9" / "paper_draft.tex")
        if not tex.is_file():                      # pragma: no cover - corpus present in-repo
            import pytest
            pytest.skip("D9 draft absent")
        src = tex.read_text(errors="replace")
        assert "lean" in plr._prose_verbatim_macros(src), (
            "D9 no longer defines a \\texttt alias — re-derive this test's premise "
            "rather than deleting it")
        toks = {t for t, _o in plr._extract_prose_lean_candidates(src)}
        assert len(toks) > 100, (
            f"only {len(toks)} candidate references extracted from D9, which carries "
            f"~192 \\lean{{}} sites — the alias hole has reopened")


class TestTheoremNameEmbeddedCitations:
    """A declaration name embedding an author+year asserts a citation; the
    bibliography must carry it."""

    def _run(self, tmp_path, monkeypatch, *, decls, bib, strict=False):
        from validation import _config as _cfg
        p = tmp_path / "lean_deps.json"
        p.write_text(json.dumps([{"name": n, "type": "P", "kind": "theorem"}
                                 for n in decls]))
        monkeypatch.setattr(_H, "LEAN_DEPS_PATH", p)
        monkeypatch.setattr(_cfg, "STRICT_MODE", strict)
        # The check is scoped to declarations the PROSE MENTIONS — a name nobody
        # cites embeds no claim in this paper. So the draft must name it.
        mentions = " ".join(rf"\texttt{{{n.rsplit('.', 1)[-1]}}}" for n in decls)
        body = (mentions + "\n" + r"\begin{thebibliography}{9}" + bib
                + r"\end{thebibliography}")
        _bundle(tmp_path, monkeypatch, "D1", body)
        return plr.check_theorem_name_embedded_citations()

    #: MEASURED, not guessed. `verlinde_no_go_2011` yields primary_author=None —
    #: the segment immediately before the year is `go`, which is under the 4-char
    #: floor — so it is SKIPPED as having no inferable author and tests nothing.
    #: The author must sit directly before the year. `zzarquon` is deliberately
    #: absent from CITATION_REGISTRY so `_registry_match` cannot rescue it and mask
    #: the bibliography leg.
    DECL = "SKEFTHawking.M.entropic_gravity_zzarquon_2011"
    CITED = r"\bibitem{z11} Zzarquon, A. (2011). On the origin of gravity."

    def test_a_cited_author_year_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch,
                      decls=[self.DECL], bib=self.CITED)
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_it_stays_advisory_when_the_citation_is_missing(self, tmp_path, monkeypatch):
        """ADVISORY in default mode — this is one of the six `--strict` consumers
        (ADR-009 §Deferred item 6), and `--strict` is the documented Paper Submission
        Gate rather than a build gate."""
        r = self._run(tmp_path, monkeypatch,
                      decls=[self.DECL],
                      bib=r"\bibitem{x} Someone Else (1999).")
        assert r.passed is True

    def test_a_missing_citation_fails_under_strict(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. A theorem NAME asserting `verlinde_2011` while
        the bibliography carries no such work is an uncheckable claim embedded in an
        identifier."""
        r = self._run(tmp_path, monkeypatch,
                      decls=[self.DECL],
                      bib=r"\bibitem{x} Someone Else (1999).", strict=True)
        assert r.passed is False, (
            "--strict did not fail on a theorem name embedding an uncited author+year "
            "— either the promotion is gone or STRICT_MODE is bound by value (H5)")
        # ...and the finding must RENDER as a failure, not as a warning glyph. The
        # verdict is set by a separate `if STRICT_MODE and n_warn` line at the end, so
        # asserting only `passed is False` leaves the detail-level branch untested —
        # measured: mutating it to `if False:` was MISSED until this assertion existed.
        # Same distinction `test_always_pass_dispositions` makes for paper_latex_compiles:
        # a failing item that reads as advisory is a defect one layer down from the verdict.
        d = next(x for x in r.details
                 if x.name.startswith("embedded_citation_missing:"))
        assert d.passed is False and not d.warning, (
            f"under --strict the mismatch rendered as {'warning' if d.warning else d.passed} "
            f"— a blocking finding must not be shown with an advisory glyph")

    def test_a_name_with_no_year_is_out_of_scope(self, tmp_path, monkeypatch):
        """No year token means no inferable citation; scanning it would manufacture
        findings from ordinary names."""
        r = self._run(tmp_path, monkeypatch,
                      decls=["SKEFTHawking.M.some_ordinary_theorem"],
                      bib=r"\bibitem{x} Nobody (1999).", strict=True)
        assert r.passed is True

    def test_a_naming_idiom_stopword_is_not_read_as_an_author(self, tmp_path, monkeypatch):
        """`d_n_bound_2020` is a numerical-bound naming idiom, not a citation of an
        author called 'bound'. Without the stopword list this check would fire on
        every dated bound in the library."""
        r = self._run(tmp_path, monkeypatch,
                      decls=["SKEFTHawking.M.d_n_bound_2020"],
                      bib=r"\bibitem{x} Nobody (1999).", strict=True)
        assert r.passed is True
        # The SKIP must be recorded, not silent. Measured: disabling the
        # no-inferable-author branch changes no verdict (an empty requirement list
        # produces no warnings either way), so the emitted detail is the ONLY
        # observable — and an unrecorded skip is indistinguishable from a check that
        # examined the declaration and found it clean.
        assert any(x.name.startswith("no_inferable_author:") for x in r.details), (
            "a declaration skipped for having no inferable author left no record — "
            "silence here reads as coverage")


def _generated_fixture(tmp_path, monkeypatch, spec, files, draft=""):
    _index(monkeypatch)
    paper = _bundle(tmp_path, monkeypatch, "D1", draft) / "D1"
    (paper / "tables.py").write_text(spec)
    tables = paper / "tables"
    tables.mkdir()
    for name, content in files.items():
        (tables / name).write_text(content)
    return paper


class TestRegisteredTableCoverage:
    def test_source_scope_uses_registered_outputs(self, tmp_path, monkeypatch):
        _generated_fixture(
            tmp_path, monkeypatch, "TABLES = {'witness': {}}",
            {"witness.tex": "\\lean{ghost_registered_theorem}\n",
             "orphan.tex": "\\lean{ghost_orphan_theorem}\n"},
            r"\newcommand{\lean}[1]{\texttt{#1}}",
        )
        monkeypatch.setattr(plr, "_resolve_prose_ref", lambda *args, **kwargs: "ABSENT")
        result = plr.check_prose_theorem_reference_coverage()
        detail = {d.name: d.message for d in result.details}
        assert not result.passed
        assert "papers/D1/tables/witness.tex:1" in detail[
            "unresolved:D1:ghost_registered_theorem"]
        assert "unresolved:D1:ghost_orphan_theorem" not in detail

    def test_bad_ownership_fails_the_checker(self, tmp_path, monkeypatch):
        import pytest
        from render_paper_tables import spec_output_paths

        paper = _generated_fixture(
            tmp_path, monkeypatch, "TABLES = {'witness': {}}", {},
        )
        spec = paper / "tables.py"
        for invalid in (
            "raise RuntimeError('broken spec')",
            "TABLES = ['bad shape']",
            "TABLES = {'witness': {}}; SCALARS = {'witness': {}}",
            "TABLES = {'../witness': {}}",
            "TABLES = {'witness': {}}",
        ):
            spec.write_text(invalid)
            # Prevent same-size same-tick spec edits from reusing a fixture .pyc.
            for cached in paper.glob("__pycache__/*"):
                cached.unlink()
            result = plr.check_prose_theorem_reference_coverage()
            assert not result.passed, invalid
            assert any(d.name.startswith("table_source:D1:") and not d.passed
                       for d in result.details), invalid
        path = tmp_path / "outside.tex"
        path.write_text("escaped")
        (paper / "tables/witness.tex").symlink_to(path)
        with pytest.raises(ValueError, match="symlink|escapes"):
            spec_output_paths(spec, strict=True)

    def test_spec_symlink_is_rejected_before_execution(self, tmp_path, monkeypatch):
        paper = _generated_fixture(tmp_path, monkeypatch, "", {})
        spec = paper / "tables.py"
        spec.unlink()
        target = tmp_path / "outside.py"
        marker = tmp_path / "executed"
        target.write_text(f"from pathlib import Path\nPath({str(marker)!r}).touch()\n")
        spec.symlink_to(target)
        result = plr.check_prose_theorem_reference_coverage()
        assert not result.passed
        assert not marker.exists()


def test_retained_recorder_distinguishes_active_orphan_and_path_escape(tmp_path):
    import pytest
    from compile_bundle_pdf import recorded_table_inputs

    paper = tmp_path / "papers" / "D9"
    tables = paper / "tables"
    tables.mkdir(parents=True)
    spec = paper / "tables.py"
    spec.write_text("TABLES = {'owned': {}}")
    for name in ("owned", "orphan"):
        (tables / f"{name}.tex").write_text("")
    draft = paper / "paper_draft.tex"
    draft.write_text("")
    recorder = tmp_path / "paper_draft.fls"
    header = f"PWD {paper}\nINPUT ./paper_draft.tex\nINPUT /usr/share/texmf/article.cls\n"
    recorder.write_text(header + "INPUT ./tables/owned.tex\nINPUT tables/owned.tex\n")
    assert recorded_table_inputs(paper, recorder) == ("tables/owned.tex",)
    recorder.write_text(header + "INPUT tables/orphan.tex\n")
    with pytest.raises(ValueError, match="unowned"):
        recorded_table_inputs(paper, recorder)

    outside = tmp_path / "outside.tex"
    outside.write_text("")
    (tables / "owned.tex").unlink()
    (tables / "owned.tex").symlink_to(outside)
    recorder.write_text(header + "INPUT ./tables/owned.tex\n")
    with pytest.raises(ValueError, match="escape"):
        recorded_table_inputs(paper, recorder)
    (tables / "owned.tex").unlink()
    (tables / "owned.tex").write_text("")

    other = paper.parent / "D8" / "tables"
    other.mkdir(parents=True)
    (other / "other.tex").write_text("")
    for raw in ("../D8/tables/other.tex", str(other / "other.tex")):
        recorder.write_text(header + f"INPUT {raw}\n")
        with pytest.raises(ValueError, match="escape"):
            recorded_table_inputs(paper, recorder)
    recorder.write_text(f"PWD {other}\nINPUT ./paper_draft.tex\n")
    with pytest.raises(ValueError, match="working directory"):
        recorded_table_inputs(paper, recorder)
    recorder.unlink()
    with pytest.raises(ValueError, match="recorder"):
        recorded_table_inputs(paper, recorder)


def test_live_d9_generated_reference_in_active_else_is_caught():
    """Seed the renderer-owned artifact with the original rendered R2 false pass."""
    import pytest
    from seed_journal import outstanding, seeded_mutation

    draft = _H.PAPERS_DIR / "D9" / "paper_draft.tex"
    table = draft.parent / "tables" / "exact.tex"
    if not table.exists():
        pytest.skip("D9 canonical generated table is absent")
    original_input = r"\input{tables/exact.tex}"
    original_ref = r"\lean{diamondDist\_dephasing\_eq}"
    assert draft.read_text().count(original_input) == table.read_text().count(original_ref) == 1
    old_journal = outstanding(include_live=True)
    original = {path: (path.read_bytes(), path.stat().st_mtime_ns)
                for path in (draft, table)}

    def adverse_draft(source):
        wrapped = r"\iffalse\ifthenelse{1=1}{True}{False}\else" + original_input + r"\fi"
        return source.replace(r"\usepackage{graphicx}", "\\usepackage{graphicx}\n\\usepackage{ifthen}").replace(
            original_input, wrapped)

    with seeded_mutation(draft, adverse_draft, reason="D9 active table in else branch"):
        with seeded_mutation(
            table, lambda source: source.replace(
                original_ref, r"\lean{d9\_registered\_table\_missing\_probe}"),
            reason="D9 generated theorem-reference diagnostic",
        ):
            result = plr.check_prose_theorem_reference_coverage()
            assert result.measured and not result.passed
            [detail] = [d for d in result.details
                        if d.name == "unresolved:D9:d9_registered_table_missing_probe"]
            assert not detail.passed
            assert "papers/D9/tables/exact.tex:9" in detail.message
    assert outstanding(include_live=True) == old_journal
    assert all((path.read_bytes(), path.stat().st_mtime_ns) == before
               for path, before in original.items())


def test_generated_reference_after_literal_percent(tmp_path, monkeypatch):
    _generated_fixture(
        tmp_path, monkeypatch, "TABLES = {'witness': {}}",
        {"witness.tex": (
            r"\verb|%| \lean{ghost_after_percent}" "\n"
            r"\verb*%payload% \lean{ghost_after_delimiter}" "\n"
            r"\% \lean{ghost_after_escaped_percent}" "\n"
            r"% \verb|%| \lean{ghost_in_real_comment}" "\n"
            r"\\verb|%| \lean{ghost_after_escaped_command}" "\n"
        )},
        r"\newcommand{\lean}[1]{\texttt{#1}}",
    )
    monkeypatch.setattr(plr, "_resolve_prose_ref", lambda *args, **kwargs: "ABSENT")
    result = plr.check_prose_theorem_reference_coverage()
    findings = {d.name: d.message for d in result.details}
    for line, name in enumerate((
        "ghost_after_percent", "ghost_after_delimiter", "ghost_after_escaped_percent",
    ), 1):
        assert f"papers/D1/tables/witness.tex:{line}" in findings[f"unresolved:D1:{name}"]
    assert "unresolved:D1:ghost_in_real_comment" not in findings
    assert "unresolved:D1:ghost_after_escaped_command" not in findings
