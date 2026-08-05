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

    def _run(self, tmp_path, monkeypatch, *, title, page1, strict=False):
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

    def test_a_drifted_title_fails_under_strict(self, tmp_path, monkeypatch):
        """ADR-009 item 6 measured this as a strict leg NO ReadinessGate covers —
        no gate compares titles to PDFs — so it runs only if a human passes the flag."""
        r = self._run(tmp_path, monkeypatch,
                      title="Entanglement harvesting in a relativistic BEC with extra words here",
                      page1="Some header\nCompletely different published title\nAuthors",
                      strict=True)
        assert r.passed is False, (
            "--strict did not promote a title-drift finding to a FAIL")

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
        assert strict.passed is False
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
