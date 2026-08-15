"""D5 both-directions tests for `validation/checks/citations.py` — audit QI-27.

Four checks: `parameter_provenance`, `citation_primary_sources_present`,
`provenance_doi_in_registry`, `bibitem_title_primary_source`.

THREE OF THE SIX `--strict` CONSUMERS LIVE HERE, which makes this module the centre
of ADR-009 §Deferred item 6. That item DECLINED the filed complaint (`--strict` is the
documented Paper Submission Gate, not dead code) but recorded a residue: five strict
legs enforce concerns no ReadinessGate covers, and nothing automated passes `--strict`.
So these legs are exercised only when a human runs the flag — which makes a test the
only thing standing between them and silent rot. Each strict promotion is a leg below.

MUTATION-VERIFIED 2026-08-04 — 10 mutations, all CAUGHT, clean negative control.
"""
from __future__ import annotations

import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate_helpers as _H  # noqa: E402
from src.core import citations as _cit  # noqa: E402
from src.core import constants as _c  # noqa: E402
from src.core import provenance as _prov  # noqa: E402
from src.core import workspace as _ws  # noqa: E402
from validation import _config as _cfg  # noqa: E402
from validation.checks import citations as ck  # noqa: E402


def _entry(**over):
    base = {"value": 1.0, "tier": "MEASURED", "source": "Smith 2020",
            "llm_verified_date": "2026-01-01", "human_verified_date": "2026-01-02"}
    base.update(over)
    return base


class TestParameterProvenance:
    """Invariant #8: every experimental parameter traces to a published source.
    LLM verification gates computation; human verification gates SUBMISSION."""

    def _run(self, monkeypatch, *, registry, experiments=None, strict=False):
        monkeypatch.setattr(_c, "EXPERIMENTS", experiments if experiments is not None
                            else {"Plat": {"omega": 1.0, "description": "d", "atom": "Rb"}})
        monkeypatch.setattr(_c, "ATOMS", {})
        monkeypatch.setattr(_c, "POLARITON_PLATFORMS", {})
        monkeypatch.setattr(_prov, "PARAMETER_PROVENANCE", registry)
        monkeypatch.setattr(_cfg, "STRICT_MODE", strict)
        return ck.check_parameter_provenance()

    #: `POLARITON_MASS` is resolved against the REAL constant by
    #: `_lookup_provenance_value`, so its registry value must be the real one or the
    #: consistency leg fires and every test in this class fails for the wrong reason.
    #: `Plat.omega` is fully synthetic (EXPERIMENTS is monkeypatched), so 1.0 is fine.
    @staticmethod
    def _pm(**over):
        from src.core.constants import POLARITON_MASS
        return _entry(value=POLARITON_MASS, **over)

    @property
    def FULL(self):
        return {"Plat.omega": _entry(), "POLARITON_MASS": self._pm()}

    def test_full_coverage_passes(self, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(monkeypatch, registry=self.FULL)
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_parameter_without_provenance_fails(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — Invariant #8's coverage leg."""
        r = self._run(monkeypatch, registry={"POLARITON_MASS": self._pm()})
        assert r.passed is False
        assert any(d.name == "coverage" and not d.passed for d in r.details)

    def test_an_unverified_parameter_fails(self, monkeypatch):
        """LLM verification gates STAGE 1 — computation must not proceed on an
        unverified parameter, so this is a hard fail in every mode."""
        reg = {"Plat.omega": _entry(llm_verified_date=None), "POLARITON_MASS": self._pm()}
        r = self._run(monkeypatch, registry=reg)
        assert r.passed is False
        assert any(d.name == "llm_verification" and not d.passed for d in r.details)

    def test_a_registry_value_disagreeing_with_the_code_fails(self, monkeypatch):
        """The consistency leg — the registry is a CLAIM about the constant, and a
        registry that has drifted from the code documents a value nobody computes."""
        reg = {"Plat.omega": _entry(value=2.0), "POLARITON_MASS": self._pm()}
        r = self._run(monkeypatch, registry=reg)
        assert r.passed is False
        assert any(d.name == "value_consistency" and not d.passed for d in r.details)

    def test_a_null_value_is_an_unresolved_conflict(self, monkeypatch):
        """`None` means two sources disagreed and nobody adjudicated. Treating it as
        'no value to check' would make the conflict permanent and invisible."""
        reg = {"Plat.omega": _entry(value=None), "POLARITON_MASS": self._pm()}
        r = self._run(monkeypatch, registry=reg)
        assert r.passed is False
        assert any(d.name == "unresolved_conflicts" and not d.passed for d in r.details)

    def test_human_verification_is_advisory_by_default(self, monkeypatch):
        """SILENT ON CORRECT DATA in a build context: human verification gates PAPER
        SUBMISSION, not computation, so a default run must not block on it."""
        reg = {"Plat.omega": _entry(human_verified_date=None), "POLARITON_MASS": self._pm()}
        r = self._run(monkeypatch, registry=reg)
        assert r.passed is True
        assert any(d.name == "human_verification" and d.warning for d in r.details)

    def test_human_verification_fails_under_strict(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. This is the ONE strict leg ADR-009 item 6
        measured as already covered by a ReadinessGate (`_eval_parameter_provenance`,
        P1) — but the gate is per-paper and this is registry-global, so the strict
        leg additionally covers entries no paper depends on yet."""
        reg = {"Plat.omega": _entry(human_verified_date=None), "POLARITON_MASS": self._pm()}
        r = self._run(monkeypatch, registry=reg, strict=True)
        assert r.passed is False, (
            "--strict did not block on an unverified parameter — the submission gate "
            "is off, or STRICT_MODE is bound by value (H5)")

    def test_the_projected_tier_is_exempt_from_human_verification(self, monkeypatch):
        """PROJECTED values are explicit estimates for experiments not yet performed.
        Demanding human verification of a projection would be asking someone to
        confirm a number that has no measurement behind it by construction."""
        reg = {"Plat.omega": _entry(human_verified_date=None, tier="PROJECTED"),
               "POLARITON_MASS": self._pm()}
        assert self._run(monkeypatch, registry=reg, strict=True).passed is True


class TestProvenanceDoiInRegistry:
    """Every provenance DOI resolves to a `CITATION_REGISTRY` entry, and every
    explicitly-cited bibkey exists."""

    def _run(self, monkeypatch, *, provenance, registry, strict=False):
        monkeypatch.setattr(_prov, "PARAMETER_PROVENANCE", provenance)
        monkeypatch.setattr(_cit, "CITATION_REGISTRY", registry)
        monkeypatch.setattr(_cfg, "STRICT_MODE", strict)
        return ck.check_provenance_doi_in_registry()

    REG = {"Smith2020": {"doi": "10.1000/abc", "authors": "Smith, J.", "year": "2020"}}

    def test_a_resolving_doi_passes(self, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(monkeypatch,
                      provenance={"p": _entry(doi="10.1000/abc")}, registry=self.REG)
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_an_unregistered_doi_is_advisory_by_default(self, monkeypatch):
        r = self._run(monkeypatch,
                      provenance={"p": _entry(doi="10.9999/zzz")}, registry=self.REG)
        assert r.passed is True
        assert any(d.name == "missing_dois" and d.warning for d in r.details)

    def test_an_unregistered_doi_fails_under_strict(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. ADR-009 item 6 measured this as a strict leg
        NO ReadinessGate covers — `CitationIntegrity` runs bibitem→registry, the
        OPPOSITE direction — so nothing automated will ever catch it."""
        r = self._run(monkeypatch, provenance={"p": _entry(doi="10.9999/zzz")},
                      registry=self.REG, strict=True)
        assert r.passed is False

    def test_an_unresolvable_cited_bibkey_fails_in_BOTH_modes(self, monkeypatch):
        """A `cited_bibkeys` entry is an EXPLICIT reference, so it must resolve
        regardless of mode — the asymmetry with DOIs above is deliberate."""
        prov = {"p": _entry(doi=None, cited_bibkeys=["GhostRef2099"])}
        assert self._run(monkeypatch, provenance=prov, registry=self.REG).passed is False
        assert self._run(monkeypatch, provenance=prov, registry=self.REG,
                         strict=True).passed is False

    def test_doi_matching_is_case_insensitive(self, monkeypatch):
        """DOIs are case-insensitive by specification; matching case-sensitively
        would produce false 'missing' reports on correct data."""
        r = self._run(monkeypatch, provenance={"p": _entry(doi="10.1000/ABC")},
                      registry=self.REG, strict=True)
        assert r.passed is True


class TestCitationPrimarySourcesPresent:
    """Every `\\cite{}`d bibkey has a cached primary source on disk."""

    def _run(self, tmp_path, monkeypatch, *, drafts, registry, cached=()):
        papers = tmp_path / "papers"
        for code, body in drafts.items():
            (papers / code).mkdir(parents=True, exist_ok=True)
            (papers / code / "paper_draft.tex").write_text(body)
        monkeypatch.setattr(_H, "PAPERS_DIR", papers)
        ws = tmp_path / "ws"
        for key in cached:
            d = ws / "Lit-Search" / "Phase-1-and-Background" / "primary-sources"
            d.mkdir(parents=True, exist_ok=True)
            (d / f"{key}.pdf").write_bytes(b"%PDF-1.4")
        monkeypatch.setattr(_ws, "find_workspace", lambda: ws)
        monkeypatch.setattr(_cit, "CITATION_REGISTRY", registry)
        monkeypatch.setattr(_cit, "bibkey_phase", lambda k: "Phase-1-and-Background")
        return ck.check_citation_primary_sources_present()

    def test_a_cached_source_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch, drafts={"D1": r"See \cite{Smith2020}."},
                      registry={"Smith2020": {"doi": "10.1/a"}}, cached=("Smith2020",))
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_missing_cache_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — a cited work with nothing cached cannot be
        checked against by any downstream title/DOI guard."""
        r = self._run(tmp_path, monkeypatch, drafts={"D1": r"See \cite{Smith2020}."},
                      registry={"Smith2020": {"doi": "10.1/a"}})
        assert r.passed is False

    def test_an_inprep_entry_is_exempt(self, tmp_path, monkeypatch):
        """There is no external primary source to cache for our own in-prep work."""
        r = self._run(tmp_path, monkeypatch, drafts={"D1": r"See \cite{OurWork}."},
                      registry={"OurWork": {"inprep": True}})
        assert r.passed is True

    def test_a_pre_doi_textbook_is_exempt(self, tmp_path, monkeypatch):
        """Gilkey 1995 / Trautman 1973: verified via secondary academic citations
        because no downloadable primary source exists. Requiring a cache would make
        the check unsatisfiable for a legitimate citation class."""
        r = self._run(tmp_path, monkeypatch, drafts={"D1": r"See \cite{Gilkey1995}."},
                      registry={"Gilkey1995": {"primary_source_path": None,
                                               "doi": None, "arxiv": None,
                                               "notes": "verified via secondary"}})
        assert r.passed is True

    def test_a_bibkey_absent_from_the_registry_fails(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch, drafts={"D1": r"See \cite{Unknown2020}."},
                      registry={})
        assert r.passed is False

    def test_citep_and_citet_variants_are_matched(self, tmp_path, monkeypatch):
        """The regex covers `\\citep`/`\\citet`/starred/optional-arg forms. Missing a
        variant would silently shrink the scanned population."""
        r = self._run(tmp_path, monkeypatch,
                      drafts={"D1": r"\citep[see][]{Smith2020} and \citet*{Smith2020}"},
                      registry={"Smith2020": {"doi": "10.1/a"}})
        assert r.passed is False, (
            "a \\citep/\\citet citation was not scanned — the cite regex has narrowed")

    def test_no_drafts_fails_rather_than_passes(self, tmp_path, monkeypatch):
        """Cannot-measure is not success."""
        monkeypatch.setattr(_H, "PAPERS_DIR", tmp_path / "absent")
        monkeypatch.setattr(_cit, "CITATION_REGISTRY", {})
        assert ck.check_citation_primary_sources_present().passed is False


class TestBibitemTitlePrimarySource:
    """Registry titles vs the cached PDF's page-1 text — the drift detector built
    after `BelenchiaLiberatiMohd2014` was registered as *"in a relativistic
    Bose-Einstein condensate"* while published as *"in relativistic Bose-Einstein
    condensate"*: a single dropped word."""

    TITLE = "Entanglement harvesting in relativistic Bose-Einstein condensate"

    def _run(self, tmp_path, monkeypatch, *, title, page1, strict=False, ceiling=0):
        """`ceiling` defaults to 0 — a fixture asserts the behaviour of a NEW drifted
        title, and the live `BIBITEM_TITLE_DRIFT_CEILING` freezes 7 inherited ones
        (audit QI-33). Leaving it at the live value would have made every case here
        pass on the slack rather than on the logic."""
        from src.core import constants as _const
        monkeypatch.setattr(_const, "BIBITEM_TITLE_DRIFT_CEILING", ceiling)
        ws = tmp_path / "ws"
        rel = "Lit-Search/Phase-1/primary-sources/Ref2014.pdf"
        p = ws / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(b"%PDF-1.4")
        monkeypatch.setattr(_ws, "find_workspace", lambda: ws)
        monkeypatch.setattr(_cit, "CITATION_REGISTRY", {
            "Ref2014": {"title": title, "primary_source_path": rel}})
        monkeypatch.setattr(_cfg, "STRICT_MODE", strict)
        import pdfminer.high_level as hl
        monkeypatch.setattr(hl, "extract_text", lambda *a, **k: page1)
        return ck.check_bibitem_title_primary_source()

    def test_a_matching_title_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch, title=self.TITLE,
                      page1=f"Some header\n{self.TITLE}\nAuthors, 2014")
        assert r.passed is True
        assert not any(d.warning and "drift" in (d.message or "").lower()
                       for d in r.details)

    def test_a_drifted_title_warns_by_default(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT (as a warning) — the exact BLOCKER pattern:
        the registry says 'in A relativistic', the paper says 'in relativistic'."""
        r = self._run(tmp_path, monkeypatch,
                      title="Entanglement harvesting in a relativistic BEC with extra words here",
                      page1="Some header\nCompletely different published title\nAuthors")
        assert r.passed is True
        assert any(d.warning for d in r.details)

    def test_a_NOT_FOUND_flag_stays_advisory_even_under_strict(self, tmp_path, monkeypatch):
        """⚠️ INVERTED 2026-08-05 (audit QI-33). This test asserted that `--strict`
        promotes a NOT-FOUND flag to a FAIL, and the code did — while the check's
        docstring and the comment beside the verdict line both call NOT-FOUND advisory
        *because it is false-positive-prone*: page 1 is often a journal cover, a chapter
        intro, or heavy metadata, and the title simply is not on it.

        That contradiction was harmless only for as long as nothing passed `--strict`.
        `gate_precheck.py submission` became that caller on 2026-08-04, and the live
        corpus carries **58 NOT-FOUND against 7 DROP-WORD** — so the submission gate
        would have gone red on 58 entries the check itself declines to call defects.
        A gate that fires on correct data is a gate that gets switched off."""
        r = self._run(tmp_path, monkeypatch,
                      title="Entanglement harvesting in a relativistic BEC with extra words here",
                      page1="Some header\nCompletely different published title\nAuthors",
                      strict=True)
        assert r.passed is True, (
            "--strict promoted a NOT-FOUND flag to a FAIL; NOT-FOUND is advisory in "
            "BOTH modes by design and the corpus carries 58 of them")
        assert any(d.name.startswith("not_found:") for d in r.details)

    def test_a_pdfminer_whitespace_artifact_is_not_a_drift_flag(self, tmp_path, monkeypatch):
        """`pdfminer` splits words across line breaks, so a verbatim-correct title can
        arrive as `quasi distillation` for `quasidistillation` — and that produced a
        DROP-WORD flag, the check's HIGH-CONFIDENCE class, for an entry with nothing
        wrong with it. Measured: 2 of 9 live flags were this artifact
        (`Horodecki1999`, `ElingGuedensJacobson2006fR`). A high-confidence class that
        is 22 % extraction noise is not high-confidence."""
        r = self._run(tmp_path, monkeypatch,
                      title="General teleportation channel and quasidistillation",
                      page1="Preprint\nGeneral teleportation channel and quasi distillation\nAuthors",
                      strict=True)
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]
        assert not any(d.name.startswith("drop_word:") for d in r.details), (
            "a whitespace artifact was reported as single-word title drift")

    def test_the_live_drift_ceiling_has_ZERO_headroom(self):
        """The ratchet's value is that it is measured AT the corpus. A ceiling with
        slack admits new drift silently — the failure this check's sibling
        `recurrence_reopens_closures` demonstrated three times. Runs against the REAL
        registry, so raising the ceiling to buy a green submission gate fails here."""
        from src.core.constants import BIBITEM_TITLE_DRIFT_CEILING as ceil
        r = ck.check_bibitem_title_primary_source()
        n = len([d for d in r.details if d.name.startswith("drop_word:")])
        assert n == ceil, (
            f"the live registry carries {n} DROP-WORD drift flag(s) but the ceiling is "
            f"{ceil}. If titles were corrected, LOWER the ceiling in the same commit.")

    def test_a_single_dropped_word_is_a_DROP_WORD_flag(self, tmp_path, monkeypatch):
        """The BLOCKER pattern verbatim, and a DIFFERENT code path from the test
        above. A wholly different page-1 title produces a NOT-FOUND flag; a title
        that MATCHES closely but drops one word produces a DROP-WORD flag, which is
        the high-confidence class the check was built for.

        ⚠️ Measured: without this leg the DROP-WORD detail's `passed` expression was
        untested — mutating it to a constant was MISSED, because my other fixtures
        only ever reached the NOT-FOUND branch.
        """
        published = "Entanglement harvesting in relativistic Bose-Einstein condensate"
        registered = "Entanglement harvesting in a relativistic Bose-Einstein condensate"
        r = self._run(tmp_path, monkeypatch, title=registered,
                      page1=f"Preprint\n{published}\nAuthors, 2014\nAbstract...")
        flags = [d for d in r.details if d.name.startswith("drop_word:")]
        assert flags, (
            "a single dropped word did not raise a DROP-WORD flag — this is the "
            "BelenchiaLiberatiMohd2014 BLOCKER this check exists for")
        assert r.passed is True and flags[0].warning, "advisory in default mode"

        strict = self._run(tmp_path, monkeypatch, title=registered,
                           page1=f"Preprint\n{published}\nAuthors, 2014\nAbstract...",
                           strict=True)
        assert strict.passed is False, (
            "a NEW DROP-WORD flag past the frozen ceiling did not fail under --strict; "
            "this is the one class the submission gate is supposed to block on")
        d = next(d for d in strict.details if d.name.startswith("drop_word:"))
        assert d.passed is False and not d.warning, (
            "under --strict a DROP-WORD finding must RENDER as a failure, not with an "
            "advisory glyph — the verdict and the rendering are separate expressions")

    def test_pdfminer_absent_skips_rather_than_fails(self, tmp_path, monkeypatch):
        """One of the five optional-toolchain PASS sites ADR-009 item 4 keeps
        deliberately: failing a build because an optional dependency is missing is
        its own defect."""
        import builtins
        real = builtins.__import__

        def _blocked(name, *a, **k):
            if name.startswith("pdfminer"):
                raise ImportError("not installed")
            return real(name, *a, **k)
        monkeypatch.setattr(builtins, "__import__", _blocked)
        r = ck.check_bibitem_title_primary_source()
        assert r.passed is True
        assert any(d.warning for d in r.details)


class TestCitationCacheVenueAgreementProduction:
    """PRODUCTION-SEEDED legs for `citation_primary_sources_present` (D11 Stage-13
    round-4 findings 1.1/1.2, round-8 finding 1.1).

    These run against the REAL `CITATION_REGISTRY` and the REAL
    `Lit-Search/*/primary-sources/*.abstract.txt` caches, not a fixture. A fixture can
    only show that the comparison logic works on data shaped the way the author
    imagined; three rounds of reviewers defeated exactly that. The mutation is applied
    to a deep copy of the production registry so the on-disk file is never touched.

    Manual file-write probe recorded 2026-08-14: `volume: 274 -> 275` and
    `journal -> 'Journal of Applied Physics'` written into the REAL
    `src/core/citations.py` each turned `validate.py --check
    citation_primary_sources_present` red naming `cache_venue_mismatch:Voigt1889`;
    restored and verified byte-identical by `cmp`.
    """

    #: A D11 bibkey whose cache header carries a full `Venue: <journal>, <vol>, p. <page>`
    #: line, so all three legs are exercisable. If this entry is ever retired, repoint at
    #: another entry with the same header shape rather than deleting the class.
    KEY = "Voigt1889"

    def _run_with(self, monkeypatch, mutate):
        import copy
        from src.core.citations import CITATION_REGISTRY as REAL
        reg = copy.deepcopy(dict(REAL))
        assert self.KEY in reg, f"{self.KEY} left CITATION_REGISTRY — repoint this test"
        mutate(reg[self.KEY])
        monkeypatch.setattr(_cit, "CITATION_REGISTRY", reg)
        return ck.check_citation_primary_sources_present()

    def _names(self, r, prefix):
        return [d.name for d in r.details
                if d.name.startswith(prefix) and not d.passed]

    def test_the_unmutated_production_corpus_has_no_venue_disagreement(self):
        """NEGATIVE CONTROL. Every leg below rides on this: a check that is red on
        clean data proves nothing when it goes red on a seed."""
        r = ck.check_citation_primary_sources_present()
        assert not self._names(r, "cache_venue_mismatch"), [
            d.message for d in r.details
            if d.name.startswith("cache_venue_mismatch")]

    def test_real_registry_volume_drift_is_caught(self, monkeypatch):
        """MUT — the leg `READINESS_GATES.md:36` requires and nothing checked until
        2026-08-14. A reviewer mutated journal + volume + page together and the check
        stayed green (round-8 MUT-7)."""
        def _m(e):
            e["volume"] = (int(e["volume"]) + 1) if e.get("volume") else 999
        r = self._run_with(monkeypatch, _m)
        assert f"cache_venue_mismatch:{self.KEY}" in self._names(
            r, "cache_venue_mismatch"), "a registry VOLUME drift was not caught"
        assert r.passed is False

    def test_real_registry_journal_drift_is_caught(self, monkeypatch):
        def _m(e):
            e["journal"] = "Journal of Applied Physics"
        r = self._run_with(monkeypatch, _m)
        assert f"cache_venue_mismatch:{self.KEY}" in self._names(
            r, "cache_venue_mismatch"), "a registry JOURNAL drift was not caught"

    def test_real_registry_page_drift_is_caught(self, monkeypatch):
        def _m(e):
            e["page"] = "9999"
        r = self._run_with(monkeypatch, _m)
        assert f"cache_venue_mismatch:{self.KEY}" in self._names(
            r, "cache_venue_mismatch"), "a registry PAGE drift was not caught"

    def test_abbreviated_and_first_page_forms_are_NOT_flagged(self, monkeypatch):
        """The tolerances, pinned. Without these the check ships false positives on
        `Phys. Rev. Lett.` vs `Physical Review Letters` and on a registry holding a
        page RANGE against a cache printing the first page — both measured in the
        corpus, neither a citation defect."""
        def _m(e):
            e["journal"] = "Ann. Phys."          # abbreviation of the cache's spelling
            e["page"] = "573-587"                # range vs the cache's first page
        r = self._run_with(monkeypatch, _m)
        assert not self._names(r, "cache_venue_mismatch"), (
            "an ABBREVIATED journal name or a first-page-vs-range difference was "
            "reported as a venue mismatch — the check now fires on formatting")

    def test_a_cited_entry_with_an_unresolvable_declared_path_fails(self, monkeypatch):
        """The silent `continue` that D11 round-4 finding 1.2 measured: a declared
        `primary_source_path` resolving to nothing skipped EVERY content comparison and
        the check reported `cache_content_agreement PASS` having read nothing."""
        def _m(e):
            e["primary_source_path"] = (
                "Lit-Search/Phase-6c/primary-sources/__no_such_bibkey__.abstract.txt")
        r = self._run_with(monkeypatch, _m)
        assert (f"cache_path_unresolvable:{self.KEY}" in
                self._names(r, "cache_path")
                or f"cache_path_wrong:{self.KEY}" in self._names(r, "cache_path")), (
            "a cited bibkey whose declared cache path resolves to nothing was skipped "
            "in silence")
        assert r.passed is False

    def test_declared_phase_tokens_match_on_disk_case_sensitively(self):
        """D11 round-4 finding 1.2's root cause, asserted directly rather than through
        the check: `PAPER_TO_PHASE['D11']` was `Phase-6C` while the directory is
        `Phase-6c`. Both spellings resolve on APFS, so nothing local could see it; on a
        case-sensitive filesystem all 11 D11 entries fell through a `continue` and the
        gate reported PASS having checked nothing. This leg is filesystem-independent."""
        import re as _re
        from src.core.citations import CITATION_REGISTRY, PAPER_TO_PHASE
        from src.core.workspace import find_workspace
        base = find_workspace() / "Lit-Search"
        real = {p.name for p in base.iterdir() if p.is_dir()}
        assert len(real) > 20, f"Lit-Search scan found only {len(real)} phase dirs"

        bad_map = sorted({v for v in PAPER_TO_PHASE.values() if v not in real})
        assert not bad_map, (
            f"PAPER_TO_PHASE names phase directories that do not exist under this "
            f"exact spelling: {bad_map}. On a case-sensitive filesystem every citation "
            f"routed through them is unverifiable.")

        bad_paths = sorted({
            (k, v["primary_source_path"]) for k, v in CITATION_REGISTRY.items()
            if v.get("primary_source_path")
            and (m := _re.match(r"Lit-Search/([^/]+)/", str(v["primary_source_path"])))
            and m.group(1) not in real})
        assert not bad_paths, (
            f"{len(bad_paths)} registry primary_source_path values name a phase "
            f"directory that does not exist under this exact spelling: "
            f"{bad_paths[:5]}")

    def test_the_PROMOTE_SIDECAR_carries_the_same_spellings(self):
        """`scripts/promote_primary_sources.py` writes `primary_source_path` into the
        registry FROM `docs/primary_sources_state.json`. Normalizing the registry alone
        would have left the next promote run free to write the wrong-case paths straight
        back in — the "fixed in one layer, re-found in a third" pattern these rounds keep
        catching. The sidecar is pinned to the same on-disk spellings."""
        import json as _json
        import re as _re
        from src.core.workspace import find_workspace
        ws = find_workspace()
        real = {p.name for p in (ws / "Lit-Search").iterdir() if p.is_dir()}
        sidecar = SK_ROOT / "docs" / "primary_sources_state.json"
        if not sidecar.is_file():
            import pytest as _pytest
            _pytest.skip("promote sidecar absent")
        bad, seen = [], 0

        def _walk(o):
            nonlocal seen
            if isinstance(o, dict):
                ps = o.get("primary_source_path")
                if isinstance(ps, str) and ps.startswith("Lit-Search/"):
                    seen += 1
                    m = _re.match(r"Lit-Search/([^/]+)/", ps)
                    if m and m.group(1) not in real:
                        bad.append(ps)
                ph = o.get("phase")
                if isinstance(ph, str) and ph.startswith("Phase-") and ph not in real:
                    bad.append(f"phase={ph}")
                for v in o.values():
                    _walk(v)
            elif isinstance(o, list):
                for v in o:
                    _walk(v)

        _walk(_json.loads(sidecar.read_text()))
        assert seen > 50, (
            f"only {seen} sidecar primary_source_path entries were read — the walk "
            f"matched almost nothing, which is unverified rather than clean")
        assert not bad, (
            f"{len(bad)} promote-sidecar entries name a phase directory that does not "
            f"exist under this exact spelling: {bad[:5]}. The next "
            f"`promote_primary_sources.py` run would write them into CITATION_REGISTRY.")


class TestAbstractIsNotFullText:
    """ADR-014 D1/D4 — `citation_primary_sources_present` reports FIDELITY, not presence.

    `abstract.txt` is an accepted cache extension, so before ADR-014 a source held only as a
    publisher abstract was indistinguishable from one held in full text: both reported
    "cached", and the check was green. Mather1982 is the measured cost — its cache file's own
    last line records that the body has never been read, and a convention ambiguity worth 21.5
    points at D12's worked point was written into PARAMETER_PROVENANCE as a property of the
    SOURCE rather than of our not having read it.

    The flag is ADVISORY by operator decision: acquisition is the only remedy and it costs
    money, so blocking would stall every downstream stage behind a purchase queue.
    """

    def _result(self):
        from validation.checks import citations as C
        return C.check_citation_primary_sources_present()

    def test_the_fidelity_flag_FIRES_on_the_production_corpus(self):
        """Non-vacuity against the real Lit-Search tree, not a fixture."""
        det = {d.name: d for d in self._result().details}
        assert "abstract_only_fidelity" in det, (
            "the fidelity leg did not report at all — either every cited source is now full "
            "text (verify before believing it) or the leg stopped running")
        msg = det["abstract_only_fidelity"].message
        n = int(msg.split("⚠️ ")[1].split(" ")[0])
        assert n > 0, "flag present but reporting zero — that is a leg that cannot fire"

    def test_the_flag_is_ADVISORY_and_does_not_block(self):
        """A blocking fidelity gate would stall the pipeline behind a purchase queue."""
        res = self._result()
        det = {d.name: d for d in res.details}
        assert det["abstract_only_fidelity"].warning is True
        assert det["abstract_only_fidelity"].passed is True, (
            "the fidelity leg must not fail the check — ADR-014 D4 makes it a flag")

    def test_the_DISCRIMINATOR_is_the_abstract_extension_not_mere_presence(self):
        """Guard the seam. A predicate that counted every cached key, or none, would satisfy
        a naive 'it reports a number' test. Pin it to the actual population: strictly fewer
        than all cached keys, and exactly the keys whose on-disk cache is an abstract."""
        from validation.checks import citations as C
        from src.core.citations import CITATION_REGISTRY
        from src.core.workspace import find_workspace

        res = self._result()
        det = {d.name: d for d in res.details}
        summary = det["summary"].message
        n_cached = int(summary.split(" cached (")[0].split("—")[1].strip())
        n_abstract = int(summary.split("full text, ")[1].split(" ABSTRACT")[0])
        assert 0 < n_abstract < n_cached, (
            f"{n_abstract} abstract of {n_cached} cached — a leg that flags all or none is "
            f"not discriminating on fidelity")

        ws = find_workspace()
        on_disk = sum(
            1 for e in CITATION_REGISTRY.values()
            if isinstance(e.get("primary_source_path"), str)
            and e["primary_source_path"].endswith(".abstract.txt")
            and (ws / e["primary_source_path"]).is_file())
        assert on_disk > 0, "no abstract-fidelity cache files on disk — the pin measures nothing"
