"""Tests for the three prose-consistency validate.py checks shipped from
the 2026-06-05 external-review remediation (Stage 14 process items a/b/c;
record: temporary/working-docs/reviews/papers/2026-06-05-Perplexity/
REMEDIATION_TRIAGE_2026-06-10.md):

    - CHECK 24 axiom_count_prose_consistency
    - CHECK 25 prose_theorem_reference_coverage  (closes qi-leantheoremdrift)
    - CHECK 26 theorem_name_embedded_citations   (advisory; kin to
      qi-citation_authoryear_metadata_match, which stays open)

Unit tests drive the pure extraction/regex cores with synthetic fixtures
(true positive, historical-context exemption, disclaimer exemption);
smoke tests run each check against the live repo (they must PASS — the
calibration sweep that shipped alongside these checks fixed every
genuine instance).
"""
from __future__ import annotations

import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

import validate as v
from validate import (
    _axiom_prose_findings,
    _embedded_citation_pairs,
    _extract_prose_lean_candidates,
    _paper_bibitems,
    _prose_occurrence_disclaimed,
    _resolve_prose_ref,
    _strip_tex_comments,
    check_axiom_count_prose_consistency,
    check_prose_theorem_reference_coverage,
    check_theorem_name_embedded_citations,
)


# ────────────────────────────────────────────────────────────────────────
# Registration
# ────────────────────────────────────────────────────────────────────────

class TestRegistration:
    def test_all_three_checks_registered(self):
        names = {spec.name for spec in v._CHECKS}
        for expected in ("axiom_count_prose_consistency",
                         "prose_theorem_reference_coverage",
                         "theorem_name_embedded_citations"):
            assert expected in names, f"{expected} not registered"

    def test_descriptions_nonempty(self):
        for spec in v._CHECKS:
            if spec.name in ("axiom_count_prose_consistency",
                             "prose_theorem_reference_coverage",
                             "theorem_name_embedded_citations"):
                assert spec.description.strip()


# ────────────────────────────────────────────────────────────────────────
# Shared helper: TeX comment stripping
# ────────────────────────────────────────────────────────────────────────

class TestStripTexComments:
    def test_strips_comment_preserving_offsets(self):
        text = "alpha % one axiom here\nbeta"
        out = _strip_tex_comments(text)
        assert len(out) == len(text)
        assert "one axiom" not in out
        assert out.split("\n")[1] == "beta"

    def test_escaped_percent_is_content(self):
        text = r"93\% reuse with one axiom"
        out = _strip_tex_comments(text)
        assert "one axiom" in out


# ────────────────────────────────────────────────────────────────────────
# CHECK 24 core: _axiom_prose_findings
# ────────────────────────────────────────────────────────────────────────

class TestAxiomProseFindings:
    def test_true_positive_single_axiom_at_zero(self):
        text = ("The project ships with zero sorry and a single axiom "
                r"(\texttt{gapped\_interface\_axiom} in "
                r"\texttt{SPTClassification.lean}).")
        findings = _axiom_prose_findings(text, axiom_count=0)
        assert len(findings) == 1
        assert findings[0]["kind"] == "singular"
        assert findings[0]["fail"] is True

    def test_historical_exemption_retired(self):
        text = ("one axiom (\\texttt{gapped\\_interface\\_axiom}; since "
                "retired into the tracked Prop \\texttt{TPFConjecture}).")
        assert _axiom_prose_findings(text, axiom_count=0) == []

    def test_historical_exemption_formerly(self):
        text = (r"the tracked Prop \texttt{TPFConjecture} (formerly "
                r"the axiom \texttt{gapped\_interface\_axiom}).")
        assert _axiom_prose_findings(text, axiom_count=0) == []

    def test_gapped_present_tense_flags(self):
        text = r"The proof relies on the axiom \texttt{gapped\_interface\_axiom} throughout."
        findings = _axiom_prose_findings(text, axiom_count=0)
        assert any(f["kind"] == "gapped_present" and f["fail"] for f in findings)

    def test_cross_line_and_tilde_forms(self):
        # "a single\naxiom" (newline separator) and "1~axiom" (LaTeX nbsp)
        text1 = "zero sorry and a single\naxiom\n(see registry)."
        assert any(f["kind"] == "singular"
                   for f in _axiom_prose_findings(text1, 0))
        text2 = "verified pipeline (4049+ theorems, 1~axiom, zero sorry)."
        assert any(f["kind"] == "singular"
                   for f in _axiom_prose_findings(text2, 0))

    def test_comment_lines_ignored(self):
        text = "% legacy: one axiom (gapped_interface_axiom)\nClean body."
        assert _axiom_prose_findings(text, axiom_count=0) == []

    def test_negation_guard(self):
        text = "There is no single axiom underlying the construction."
        assert _axiom_prose_findings(text, axiom_count=0) == []

    def test_axiomcount_macro_never_flags(self):
        text = r"ships $\axiomcount{}$~project-local axioms, zero sorry."
        assert _axiom_prose_findings(text, axiom_count=0) == []

    def test_plural_digit_mismatch_is_advisory(self):
        findings = _axiom_prose_findings("The library declares 3 axioms.",
                                         axiom_count=2)
        assert len(findings) == 1
        assert findings[0]["kind"] == "plural_mismatch"
        assert findings[0]["fail"] is False

    def test_plural_agreement_no_flag(self):
        assert _axiom_prose_findings("ships 0 axioms total.", 0) == []
        assert _axiom_prose_findings("ships zero axioms total.", 0) == []

    def test_new_axioms_delta_claims_skipped(self):
        # "zero NEW axioms" is a per-wave delta claim, not a total count
        assert _axiom_prose_findings(
            "Wave 3 adds 41 theorems with zero new axioms.", 2) == []

    def test_word_numeral_plurals_not_compared(self):
        # "three axioms" = the Son-action physics-axioms idiom (D1/F)
        assert _axiom_prose_findings(
            "constrained by three axioms encoded in our Lean library", 0) == []

    def test_singular_at_count_one_is_consistent(self):
        findings = _axiom_prose_findings("ships with one axiom total.", 1)
        assert all(not f["fail"] and not f["mismatch"] for f in findings)

    def test_kernel_axiom_closure_idiom_not_flagged(self):
        # "kernel-only axiom closure" (D4) must not match
        assert _axiom_prose_findings(
            "proved unconditionally with kernel-only axiom closure", 0) == []


# ────────────────────────────────────────────────────────────────────────
# CHECK 25 cores: extraction, resolution, disclaimer
# ────────────────────────────────────────────────────────────────────────

class TestProseLeanCandidateExtraction:
    def test_keeps_snake_case_theorem_name(self):
        toks = [t for t, _ in _extract_prose_lean_candidates(
            r"backed by \texttt{wen\_adw\_factor\_6000} in Lean.")]
        assert toks == ["wen_adw_factor_6000"]

    def test_keeps_module_qualified_name(self):
        toks = [t for t, _ in _extract_prose_lean_candidates(
            r"see \texttt{EmergentGravityBounds.wen\_adw\_lower}.")]
        assert toks == ["EmergentGravityBounds.wen_adw_lower"]

    def test_drops_all_caps_python_registries(self):
        assert _extract_prose_lean_candidates(
            r"registered in \texttt{CITATION\_REGISTRY} and "
            r"\texttt{PARAMETER\_PROVENANCE}.") == []

    def test_drops_mcp_tool_names_and_file_suffixes(self):
        src = (r"\texttt{lean\_multi\_attempt} on \texttt{formulas.py} "
               r"and \texttt{Basic.lean}")
        assert _extract_prose_lean_candidates(src) == []

    def test_drops_short_dated_and_underscore_edge_tokens(self):
        src = (r"\texttt{I\_X} \texttt{\_iff\_} "
               r"\texttt{project\_phase6q\_complete\_2026\_05\_23}")
        assert _extract_prose_lean_candidates(src) == []

    def test_drops_plain_words_and_paths(self):
        src = (r"\texttt{crossover} \texttt{src/core/formulas.py} "
               r"\texttt{uv run pytest}")
        assert _extract_prose_lean_candidates(src) == []


class TestProseRefResolution:
    INDEX = {
        "names": {"SKEFTHawking.Foo.bar_baz", "SKEFTHawking.top_level_thm"},
        "shorts": {"bar_baz", "top_level_thm", "in_file_thm"},
        "dotted_suffixes": {"Foo.bar_baz", "bar_baz", "top_level_thm"},
        "short_to_modules": {
            "bar_baz": {"SKEFTHawking.Foo"},
            "top_level_thm": {"SKEFTHawking.Widget"},
            "in_file_thm": {"SKEFTHawking.Widget"},
        },
        "modules": {"SKEFTHawking.Foo", "SKEFTHawking.Widget",
                    "SKEFTHawking.LDP.Cramer"},
        "registry_keys": {"c_minus_equals_8Nf"},
    }

    def test_exact_and_suffix_match(self):
        assert _resolve_prose_ref("SKEFTHawking.Foo.bar_baz", self.INDEX) == "OK"
        assert _resolve_prose_ref("Foo.bar_baz", self.INDEX) == "OK"

    def test_unqualified_short_name(self):
        assert _resolve_prose_ref("top_level_thm", self.INDEX) == "OK"

    def test_module_idiom_verified_by_module_field(self):
        # `Widget.in_file_thm`: theorem declared at top-level namespace
        # inside Widget.lean — the documentation idiom resolves because
        # the decl's module field matches the written prefix.
        assert _resolve_prose_ref("Widget.in_file_thm", self.INDEX) == "OK"

    def test_wrong_module_prefix_is_drifted(self):
        assert _resolve_prose_ref("Wrong.in_file_thm", self.INDEX) == "DRIFTED"

    def test_module_namespace_prefix(self):
        assert _resolve_prose_ref("SKEFTHawking.LDP", self.INDEX) == "OK"

    def test_python_registry_key(self):
        assert _resolve_prose_ref("c_minus_equals_8Nf", self.INDEX) == "OK"

    def test_mathlib_prefix_beats_short_name_fallback(self):
        # Even though `bar_baz` exists as a project short name, a
        # Mathlib-namespaced token is classified MATHLIB, not DRIFTED.
        assert _resolve_prose_ref("Nat.bar_baz", self.INDEX) == "MATHLIB"

    def test_absent(self):
        assert _resolve_prose_ref("totally_unknown_thm_xyz", self.INDEX) == "ABSENT"


class TestProseDisclaimerExemption:
    def test_planned_within_window(self):
        src = r"a planned \texttt{VerifiedJackknife.Helpers} sub-module is"
        off = src.index(r"\texttt")
        assert _prose_occurrence_disclaimed(src, off)

    def test_retired_within_window(self):
        src = (r"A prior redundant theorem \texttt{wave\_3b\_closure} "
               "restated the same conclusion and was retired in the "
               "Stage-13 fix-pass.")
        assert _prose_occurrence_disclaimed(src, src.index(r"\texttt"))

    def test_immediately_preceding_negation(self):
        src = (r"there are no \texttt{analog\_hawking\_simulable\_BEC} "
               "or analogous lemmas")
        assert _prose_occurrence_disclaimed(src, src.index(r"\texttt"))

    def test_bare_reference_not_disclaimed(self):
        src = (r"the headline \texttt{some\_great\_theorem} proves the "
               "main claim of this section directly.")
        assert not _prose_occurrence_disclaimed(src, src.index(r"\texttt"))


# ────────────────────────────────────────────────────────────────────────
# CHECK 26 cores: embedded-citation pair extraction + bibitem parsing
# ────────────────────────────────────────────────────────────────────────

class TestEmbeddedCitationPairs:
    LEXICON = {"halenka", "miller", "verlinde"}

    def test_verlinde_no_go_extraction(self):
        pairs = _embedded_citation_pairs(
            "verlinde_2017_no_go_via_cluster_mass_densities_halenka_miller",
            self.LEXICON)
        assert pairs["year"] == "2017"
        assert pairs["primary_author"] == "verlinde"
        assert pairs["trailing_authors"] == ["halenka", "miller"]

    def test_naming_idiom_stopword_yields_no_author(self):
        pairs = _embedded_citation_pairs("d_n_bound_2020", self.LEXICON)
        assert pairs["year"] == "2020"
        assert pairs["primary_author"] is None
        assert pairs["trailing_authors"] == []

    def test_english_segments_not_misread_as_authors(self):
        pairs = _embedded_citation_pairs(
            "smithson_2019_rate_bound_cluster_densities", self.LEXICON)
        # 'cluster'/'densities' are not in the registry surname lexicon
        assert pairs["trailing_authors"] == []
        assert pairs["primary_author"] == "smithson"

    def test_no_year_token(self):
        pairs = _embedded_citation_pairs("kzm_exponent_one_half", self.LEXICON)
        assert pairs["year"] is None

    def test_gw_event_numbers_not_years(self):
        # GW170817-style digit runs lack the _YYYY_ segment shape
        pairs = _embedded_citation_pairs("gw170817_bound_holds", self.LEXICON)
        assert pairs["year"] is None


class TestPaperBibitems:
    def test_inline_thebibliography_parse(self, tmp_path):
        tex = (
            "body text\n"
            "\\begin{thebibliography}{99}\n"
            "\\bibitem{Verlinde2017dSEmergent} E.~P.~Verlinde, SciPost "
            "Phys. 2, 016 (2017).\n"
            "\\bibitem{HalenkaMiller2020} V.~Halenka and C.~J.~Miller, "
            "Phys. Rev. D 102, 084007 (2020).\n"
            "\\end{thebibliography}\n"
        )
        items = _paper_bibitems(tex, tmp_path)
        assert [k for k, _ in items] == ["Verlinde2017dSEmergent",
                                         "HalenkaMiller2020"]
        assert "2017" in items[0][1]

    def test_no_bibliography_returns_empty(self, tmp_path):
        assert _paper_bibitems("no bibliography here", tmp_path) == []


# ────────────────────────────────────────────────────────────────────────
# Live-repo smoke tests (the calibration sweep fixed every genuine
# instance — each check must PASS against the current tree)
# ────────────────────────────────────────────────────────────────────────

class TestLiveRepoSmoke:
    def test_axiom_count_prose_consistency_passes(self):
        result = check_axiom_count_prose_consistency()
        assert result.error is None, result.error
        assert result.passed, [
            (d.name, d.message) for d in result.details if not d.passed]

    def test_prose_theorem_reference_coverage_passes(self):
        result = check_prose_theorem_reference_coverage()
        assert result.error is None, result.error
        assert result.passed, [
            (d.name, d.message) for d in result.details if not d.passed]

    def test_prose_coverage_waivers_surface_as_warnings(self):
        result = check_prose_theorem_reference_coverage()
        waived = [d for d in result.details if d.name.startswith("waived:")]
        # Exactly the documented waiver set — if this grows past 5 the
        # candidate filter is too loose (see _PROSE_REF_WAIVERS).
        assert len(waived) == len(v._PROSE_REF_WAIVERS)
        assert all(d.warning for d in waived)

    def test_theorem_name_embedded_citations_passes(self):
        result = check_theorem_name_embedded_citations()
        assert result.error is None, result.error
        assert result.passed, [
            (d.name, d.message) for d in result.details if not d.passed]

    def test_theorem_name_embedded_citations_passes_strict(self):
        # Mirrors provenance_doi_in_registry's strict-flag pattern: with
        # zero mismatches the check must also pass under --strict.
        old = v.STRICT_MODE
        try:
            v.STRICT_MODE = True
            result = check_theorem_name_embedded_citations()
            assert result.passed, [
                (d.name, d.message) for d in result.details if not d.passed]
        finally:
            v.STRICT_MODE = old

    def test_summary_details_present(self):
        for fn in (check_axiom_count_prose_consistency,
                   check_prose_theorem_reference_coverage,
                   check_theorem_name_embedded_citations):
            names = [d.name for d in fn().details]
            assert "summary" in names, f"{fn.__name__} missing summary detail"
