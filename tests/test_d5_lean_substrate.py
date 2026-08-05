"""D5 both-directions tests for `validation/checks/lean_substrate.py` — audit QI-27.

Six checks: `formulas`, `placeholder_not_cited`, `disclosure_consistency`,
`proxy_body_audit`, `tracked_hypothesis_ledger`, `tracked_hypotheses_fresh`.

These are the ADR-004 R1–R3 SUBSTANCE gates — the ones that ask whether a theorem
actually proves anything and whether every modelling assumption is disclosed. That
makes a green-only test especially cheap here: the live tree is compliant, so
`assert check_x().passed` passes for a check that has been deleted.

Every test below builds a synthetic Lean tree / paper corpus / registry in `tmp_path`
and drives the REAL check function over it, with `_H` paths monkeypatched by attribute
(ADR-009 H1/H5). The registries are monkeypatched on `src.core.constants` because each
check imports them INSIDE its body, at call time.

⚠️ `TestFormulasToTheorems` reads the check's own `mapping` literal out of the AST rather
than restating it. A hand-copied list goes stale the moment the mapping grows, and the
staleness would show up as an unrelated-looking failure in a test file nobody edits.

MUTATION-VERIFIED 2026-08-04 — 12 mutations, all CAUGHT, clean negative control.
Mutations AST-scoped, restored by writing back saved bytes (audit §4b):

  | mutation                                                        | caught by |
  |---|---|
  | `formulas`: `missing_from_lean` -> `[]`                          | `…absent_theorem…` |
  | `formulas`: `rglob` -> `glob`                                    | `…subdirectory…` (QI-01) |
  | `placeholder_not_cited`: drop the `_HEDGE_CLAIM_RE` conjunct     | `…hedged_claim…` |
  | `placeholder_not_cited`: `offenders.setdefault` -> `pass`        | `…cited_as_verified…` |
  | `disclosure_consistency`: drop the `_LEDGER_HEDGE_RE` conjunct   | `…ledger_hedge_beside…` |
  | `disclosure_consistency`: drop the `_OVERCLAIM_VERB_RE` conjunct | `…bookkeeping_framing…` |
  | `disclosure_consistency`: `offenders.add` -> `pass`              | `…establishing_language…` |
  | `proxy_body_audit`: `new_flagged.append` -> `pass`               | `…new_trivially_closed…` |
  | `proxy_body_audit`: `if v.get("reason") and v.get("discloses")`  | `…bare_whitelist…` |
  | `tracked_hypothesis_ledger`: `gap` -> `[]`                       | `…unregistered…` |
  | `tracked_hypotheses_fresh`: `if old == new` -> `if True`         | `…stale_doc…` |
Clean negative control: unmutated tree, all pass.

⚠️ **ONE MUTATION WAS MISSED ON THE FIRST PASS, AND IT FOUND A REAL DEFECT (QI-28).**
Dropping the `_LEDGER_HEDGE_RE` conjunct failed no test, because the hedge test used
*"records the closure"* — which carries no overclaim verb, so the FIRST conjunct
short-circuited and the hedge was never reached. Strengthening the test to put both in
one window then exposed that six of the nine hedge alternatives were stems closed with
`\\b` and could not match a single inflected form (`tabulated`, `aggregates`,
`bookkeeping`, `summarizes`, …). The hedge SUPPRESSES a flag, so those dead alternatives
meant correct bookkeeping prose would be flagged as an overclaim. Fixed in
`lean_substrate.py`; measured 0 verdict movement on the live corpus, so the hole was
latent. `test_every_hedge_alternative_can_match_an_inflected_form` is the structural
guard on the class.

This is the first defect the D5 discipline found rather than documented, and it argues
the case for the obligation better than the ADR does: the check was green, its test was
green, and a sixth of its logic could not execute.
"""
from __future__ import annotations

import ast
import json
import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate_helpers as _H  # noqa: E402
from src.core import constants as _c  # noqa: E402
from validation.checks import lean_substrate as ls  # noqa: E402


def _papers(tmp_path: Path, drafts: dict[str, str]) -> Path:
    root = tmp_path / "papers"
    for code, body in drafts.items():
        d = root / code
        d.mkdir(parents=True, exist_ok=True)
        (d / "paper_draft.tex").write_text(body)
    return root


def _lean_tree(tmp_path: Path, files: dict[str, str]) -> Path:
    """Synthetic `lean/SKEFTHawking/`. Keys may contain `/` to place a file in a
    SUBDIRECTORY — which is the whole point of several legs below (QI-01)."""
    root = tmp_path / "SKEFTHawking"
    for rel, body in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(body)
    root.mkdir(parents=True, exist_ok=True)
    return root


class TestFormulasToTheorems:
    """Every Python formula's docstring names its Lean theorem, and that theorem
    exists in the Lean source or in `ARISTOTLE_THEOREMS`."""

    @staticmethod
    def _mapping() -> list[tuple[str, list[str]]]:
        """The check's own `mapping` literal, read from the AST.

        Deliberately not restated: the mapping is function-local, and a copy here
        would silently describe a different set the moment a formula is added.
        `ast.literal_eval` also refuses anything that is not a plain literal, so
        this cannot start executing check code by accident.
        """
        src = Path(ls.__file__).read_text()
        fn = next(n for n in ast.walk(ast.parse(src))
                  if isinstance(n, ast.FunctionDef) and n.name == "check_formulas_to_theorems")
        for node in ast.walk(fn):
            if isinstance(node, ast.Assign) and \
                    any(getattr(t, "id", None) == "mapping" for t in node.targets):
                return ast.literal_eval(node.value)
        raise AssertionError(
            "check_formulas_to_theorems no longer assigns a literal `mapping` — this "
            "test read it from the AST precisely so it could not go stale; re-point it")

    def _all_theorem_names(self) -> list[str]:
        return [t for _f, thms in self._mapping() for t in thms]

    def test_a_theorem_absent_from_lean_and_the_registry_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — the docstrings still promise the theorems,
        but nothing on disk provides them."""
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(tmp_path, {}))
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS", {})
        r = ls.check_formulas_to_theorems()
        assert r.passed is False, (
            "every mapped Lean theorem was missing and the check passed — the "
            "formula↔theorem correspondence is unenforced")
        assert any("Not in Lean source" in (d.message or "") for d in r.details)

    def test_theorems_present_in_lean_source_pass(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — a synthetic Lean tree providing exactly the
        mapped names."""
        body = "\n".join(f"theorem {n} : True := trivial" for n in self._all_theorem_names())
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(tmp_path, {"All.lean": body}))
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS", {})
        r = ls.check_formulas_to_theorems()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_theorem_in_a_subdirectory_is_found(self, tmp_path, monkeypatch):
        """QI-01 REGRESSION GUARD, specific to this check. Under the pre-2026-08-04
        non-recursive `glob('*.lean')` this check read 1,373 of 2,039 files, so a
        mapped theorem living in a package read as absent while existing — a false
        FAILURE rather than a false pass, but the resolution set was two-thirds of
        the library.

        The sibling `tests/test_lean_scan_coverage.py` guards the class structurally;
        this leg proves the behaviour at this specific call site.
        """
        body = "\n".join(f"theorem {n} : True := trivial" for n in self._all_theorem_names())
        monkeypatch.setattr(_H, "LEAN_DIR",
                            _lean_tree(tmp_path, {"Nested/Deeper/All.lean": body}))
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS", {})
        assert ls.check_formulas_to_theorems().passed is True, (
            "a mapped theorem in a SUBDIRECTORY was not found — the Lean scan is "
            "non-recursive again (audit QI-01)")

    def test_the_aristotle_registry_also_satisfies_the_reference(self, tmp_path, monkeypatch):
        """Aristotle-proved theorems need not appear in local source."""
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(tmp_path, {}))
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS",
                            {n: {} for n in self._all_theorem_names()})
        monkeypatch.setattr(_H, "unresolved_aristotle_keys", list)
        assert ls.check_formulas_to_theorems().passed is True

    def test_a_STALE_registry_key_cannot_launder_a_nonexistent_theorem(
            self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — PR-review R4-I3, fixed 2026-08-05.

        This check unions `ARISTOTLE_THEOREMS`' KEYS into the set it resolves formula
        references against. The registry is hand-maintained, so a key naming no Lean
        declaration launders a nonexistent theorem into that set and a formula
        grounded on it reports as grounded.

        QI-30 ratcheted the COUNT of such keys, which closed the generator. It did not
        close the hole: the 14 already there kept laundering. Measured 2026-08-05, and
        stated honestly — **none of the 14 is currently a mapping target**, so the
        exposure was LATENT, not live. Same posture as QI-01, filed the same way.

        The fixture reproduces the live shape exactly: the Lean tree is EMPTY, and the
        registry's only key is a mapped theorem name that resolves to nothing. Before
        the fix the check passed; the theorem exists nowhere at all."""
        target = self._all_theorem_names()[0]
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(tmp_path, {}))
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS",
                            {n: {} for n in self._all_theorem_names()})
        # ...and `theorems`' ratchet has established this key names nothing.
        monkeypatch.setattr(_H, "unresolved_aristotle_keys", lambda: [target])
        r = ls.check_formulas_to_theorems()
        assert r.passed is False, (
            f"{target!r} resolves to NO Lean declaration — `theorems` says so — and "
            f"the formula citing it still reported as grounded. The registry key "
            f"laundered a nonexistent theorem into the valid-name set (R4-I3)")

    def test_an_ABSENT_substrate_does_not_suppress_the_subtraction_silently(
            self, tmp_path, monkeypatch):
        """Cannot-measure is not success, at the new seam too. If `lean_deps.json` is
        gone, `unresolved_aristotle_keys` raises and no key can be subtracted — the
        check must not therefore treat the whole registry as verified. It falls back
        to the full key set, which is the STRICTER direction (no suppression), and the
        `theorems` ratchet fails separately on the same absence."""
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(tmp_path, {}))
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS",
                            {n: {} for n in self._all_theorem_names()})

        def _boom():
            raise FileNotFoundError("lean_deps.json absent")
        monkeypatch.setattr(_H, "unresolved_aristotle_keys", _boom)
        r = ls.check_formulas_to_theorems()
        assert r.passed is True, (
            "a missing substrate turned this check red; the fallback must be the "
            "pre-fix behaviour, with `theorems` owning the absence verdict")

    def test_the_resolver_has_ONE_owner(self):
        """`check_theorem_count` ratchets the stale-key count and this check subtracts
        it — they must agree about WHICH keys are stale. A second resolver in either
        module could disagree with the ratchet about the very set the ratchet counts,
        which is the duplication shape this audit keeps finding (`_recurrence_norm`,
        `_SEVERITY_DECL_MAP`, `NUMERICAL_LITERAL_RE`)."""
        import re as _re
        for mod, fn in (("lean_toolchain", "check_theorem_count"),
                        ("lean_substrate", "check_formulas_to_theorems")):
            src = (Path(ls.__file__).parent / f"{mod}.py").read_text()
            body = src[src.index(f"def {fn}("):]
            assert "unresolved_aristotle_keys" in body[:6000], (
                f"{mod}.{fn} no longer routes through the shared resolver")
            assert not _re.search(r'\{d\.get\("name", ""\) for d in', body[:6000]), (
                f"{mod}.{fn} re-implements the lean_deps name index locally — it must "
                f"use `_H.unresolved_aristotle_keys()` so both sides agree")

    def test_a_docstring_that_drops_its_theorem_fails(self, tmp_path, monkeypatch):
        """The OTHER direction of the same invariant: the theorem exists, but the
        formula stops citing it. Provenance is the claim, so a silent drop is the
        defect — `formulas.py` is canonical precisely because of this coupling."""
        from src.core import formulas
        func_name, thms = self._mapping()[0]
        body = "\n".join(f"theorem {n} : True := trivial" for n in self._all_theorem_names())
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(tmp_path, {"All.lean": body}))
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS", {})
        monkeypatch.setattr(getattr(formulas, func_name), "__doc__",
                            "docstring with no theorem references")
        r = ls.check_formulas_to_theorems()
        assert r.passed is False
        assert any(d.name == func_name and "Missing from docstring" in (d.message or "")
                   for d in r.details)


class TestPlaceholderNotCited:
    """Pipeline Invariant #9 / R5: a `True := trivial` placeholder must not be
    presented as a formally-verified result."""

    KEY = "d5_synthetic_placeholder"
    LEAN = "synthetic_placeholder_thm"

    def _registry(self, monkeypatch, *, signature: str | None = None):
        entry = {"lean_name": self.LEAN}
        if signature:
            entry["tex_signature"] = signature
        monkeypatch.setattr(_c, "PLACEHOLDER_THEOREMS", {self.KEY: entry})

    def test_a_placeholder_cited_as_formally_verified_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        self._registry(monkeypatch)
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": (
            rf"The result \texttt{{{self.LEAN}}} is formally verified in Lean 4.")}))
        r = ls.check_placeholder_not_cited()
        assert r.passed is False, (
            "a registered placeholder was cited as formally verified and the check "
            "passed — Invariant #9's paper-claim clause is unenforced")

    def test_a_hedged_claim_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA. An honest disclosure — 'formalized at the
        statement level' — is the whole reason the hedge regex exists."""
        self._registry(monkeypatch)
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": (
            rf"\texttt{{{self.LEAN}}} is formally verified at the statement level; "
            rf"the general case is not yet proven.")}))
        r = ls.check_placeholder_not_cited()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_mention_without_a_verification_claim_passes(self, tmp_path, monkeypatch):
        """Naming a placeholder is not citing it as verified."""
        self._registry(monkeypatch)
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": (
            rf"See \texttt{{{self.LEAN}}} for the statement we intend to prove.")}))
        assert ls.check_placeholder_not_cited().passed is True

    def test_a_latex_escaped_underscore_is_still_matched(self, tmp_path, monkeypatch):
        """`_tex_name_pattern` exists because LaTeX writes `\\_`. Without it a paper
        could cite the placeholder in its normal typeset form and never be seen."""
        self._registry(monkeypatch)
        escaped = self.LEAN.replace("_", r"\_")
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": (
            rf"\texttt{{{escaped}}} is machine-checked end to end.")}))
        assert ls.check_placeholder_not_cited().passed is False, (
            "a placeholder cited with LaTeX-escaped underscores went unseen — "
            "`_tex_name_pattern` is the guard on exactly that")

    def test_the_tex_signature_is_matched_as_well_as_the_name(self, tmp_path, monkeypatch):
        """A paper cites a claim by its published NOTATION, not by the Lean decl
        name. Matching only the name leaves the normal citation form invisible."""
        # A `tex_signature` is a REGEX over the typeset form, not a literal — so it
        # has to span the markup between the operands. My first draft used `.` for
        # `\cong` and matched nothing, i.e. tested nothing.
        self._registry(monkeypatch, signature=r"Z\(Vec_G\)\s*\\cong\s*Rep")
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": (
            r"We show $Z(Vec_G) \cong Rep(D(G))$, kernel-verified in Lean.")}))
        assert ls.check_placeholder_not_cited().passed is False

    def test_a_far_away_verification_claim_does_not_flag(self, tmp_path, monkeypatch):
        """The window is bounded (320 chars each side) so an unrelated verification
        sentence elsewhere in the paper is not attributed to the placeholder."""
        self._registry(monkeypatch)
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D1": (
            rf"\texttt{{{self.LEAN}}} is a stub." + ("x " * 400) +
            r"Everything else here is formally verified in Lean.")}))
        assert ls.check_placeholder_not_cited().passed is True


class TestDisclosureConsistency:
    """A theorem disclosed as `definitional`/`vacuous_proxy` must not be presented as
    ESTABLISHING a scientific result. D5 prose-claimed a disclosed bookkeeping
    aggregator 'establishes the 8/8 closure', contradicting its own disclosure."""

    LEAN = "synthetic_ledger_count"

    def _registry(self, monkeypatch, category="definitional"):
        monkeypatch.setattr(_c, "MODELING_ASSUMPTION_THEOREMS",
                            {"k": {"lean_name": self.LEAN, "category": category,
                                   "reason": "bookkeeping", "discloses": "docs/x.md"}})

    def test_establishing_language_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        self._registry(monkeypatch)
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D5": (
            rf"\texttt{{{self.LEAN}}} establishes the 8/8 closure.")}))
        r = ls.check_disclosure_consistency()
        assert r.passed is False, (
            "a disclosed bookkeeping theorem was prose-claimed to 'establish' a "
            "result and the check passed — this is the D5 defect verbatim")

    def test_bookkeeping_framing_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — the honest framing the check exists to permit."""
        self._registry(monkeypatch)
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D5": (
            rf"\texttt{{{self.LEAN}}} records the 8/8 closure as a classification ledger.")}))
        r = ls.check_disclosure_consistency()
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_ledger_hedge_beside_an_overclaim_verb_suppresses(self, tmp_path, monkeypatch):
        """The hedge conjunct, exercised properly.

        ⚠️ The first draft of this class tested the hedge with *"records the closure"*,
        which carries NO overclaim verb — so the first conjunct short-circuited and the
        hedge was never reached. Dropping `_LEDGER_HEDGE_RE` from the check failed no
        test. This leg puts BOTH in the same 60-char window, which is the only shape
        where the hedge does any work.

        It is also the shape that found audit QI-28: six of the nine hedge alternatives
        were stems closed with `\\b` and could not match their own inflected forms.
        """
        self._registry(monkeypatch)
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D5": (
            rf"\texttt{{{self.LEAN}}} establishes the classification ledger for the closure.")}))
        assert ls.check_disclosure_consistency().passed is True, (
            "an overclaim verb whose object is explicitly a bookkeeping ledger was "
            "flagged — the hedge is inert, and a guard that flags correct prose is "
            "worse than no guard")

    def test_every_hedge_alternative_can_match_an_inflected_form(self, tmp_path, monkeypatch):
        """AUDIT QI-28 REGRESSION GUARD — the structural leg.

        A behavioural test only protects the phrasings it happens to use. This one
        asserts the property that was violated: every alternative in the hedge list
        must match at least one form a person would actually write. Six did not,
        because the pattern closed with `\\b` after a set of stems.

        Ships as a scan rather than a fixture list for the reason the QI-01 guard
        did: a fixture protects the words already there, while a scan protects the
        next word someone adds.
        """
        forms = {
            "record": ["records", "recorded", "recording"],
            "tabulat": ["tabulates", "tabulated", "tabulation"],
            "aggregat": ["aggregates", "aggregated", "aggregation"],
            "enumerat": ["enumerates", "enumerated", "enumeration"],
            "bookkeep": ["bookkeeping"],
            "tall": ["tallies", "tally"],
            "classification": ["classification ledger"],
            "summari": ["summarizes", "summarises"],
        }
        dead = [stem for stem, words in forms.items()
                if not any(ls._LEDGER_HEDGE_RE.search(w) for w in words)]
        assert not dead, (
            f"hedge alternative(s) {dead} match no inflected form — they can only "
            f"fire on a bare stem nobody writes. That is a guard that cannot fire, "
            f"and here it fires in the FALSE-POSITIVE direction: correct bookkeeping "
            f"prose gets flagged as an overclaim (audit QI-28).")

    def test_proven_is_deliberately_not_an_overclaim_verb(self, tmp_path, monkeypatch):
        """'the theorem is proven (zero sorry)' is a statement about the theorem
        EXISTING, not a claim that it establishes the physics. The verb list excludes
        `proven`/`proved` on purpose — pinned so it is not 'tightened' back in."""
        self._registry(monkeypatch)
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D5": (
            rf"\texttt{{{self.LEAN}}} is proven in Lean with zero sorry.")}))
        assert ls.check_disclosure_consistency().passed is True

    def test_an_undisclosed_theorem_is_out_of_scope(self, tmp_path, monkeypatch):
        """Only `definitional`/`vacuous_proxy` tiers are in scope — a substantive
        theorem is allowed to establish things."""
        self._registry(monkeypatch, category="substantive")
        monkeypatch.setattr(_H, "PAPERS_DIR", _papers(tmp_path, {"D5": (
            rf"\texttt{{{self.LEAN}}} establishes the 8/8 closure.")}))
        assert ls.check_disclosure_consistency().passed is True


class TestProxyBodyAudit:
    """A theorem whose NAME claims a structural result but whose PROOF is a trivial
    closer — the defining-the-conclusion anti-pattern (R2)."""

    def _run(self, tmp_path, monkeypatch, source, *, baseline=(), whitelist=None,
             placeholders=None):
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(tmp_path, {"M.lean": source}))
        monkeypatch.setattr(_c, "VACUOUS_STATEMENT_BASELINE", frozenset(baseline))
        monkeypatch.setattr(_c, "MODELING_ASSUMPTION_THEOREMS", whitelist or {})
        monkeypatch.setattr(_c, "PLACEHOLDER_LEAN_NAMES", placeholders or {})
        return ls.check_proxy_body_audit()

    TRIVIAL = "theorem sixteen_classification_holds : True := trivial\n"

    def test_a_new_trivially_closed_structural_theorem_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — a structural NAME closed by `trivial`,
        not in the baseline."""
        r = self._run(tmp_path, monkeypatch, self.TRIVIAL)
        assert r.passed is False, (
            "a new structurally-named theorem closed by `trivial` passed — the "
            "defining-the-conclusion generator is open again")

    def test_a_substantive_body_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch,
                      "theorem sixteen_classification_holds : 2 + 2 = 4 := by decide\n")
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_baselined_theorem_is_grandfathered_but_stays_visible(self, tmp_path, monkeypatch):
        """The ratchet shape: existing debt is tracked, not hidden. A grandfathered
        theorem must still be REPORTED — silently absorbing it is how a baseline
        becomes a place things go to disappear."""
        r = self._run(tmp_path, monkeypatch, self.TRIVIAL,
                      baseline={"sixteen_classification_holds"})
        assert r.passed is True
        assert any(d.name == "baseline" and d.warning for d in r.details)

    def test_a_bare_whitelist_entry_is_not_a_free_pass(self, tmp_path, monkeypatch):
        """A `MODELING_ASSUMPTION_THEOREMS` entry without `reason` AND `discloses`
        is not a disclosure — it is an unexplained exemption, and the check must
        fail on the ENTRY rather than quietly honouring it."""
        r = self._run(tmp_path, monkeypatch, self.TRIVIAL,
                      whitelist={"sixteen_classification_holds": {"category": "definitional"}})
        assert r.passed is False
        assert any(d.name == "sixteen_classification_holds" and
                   "not a valid disclosure" in (d.message or "") for d in r.details)

    def test_a_complete_whitelist_entry_exempts(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch, self.TRIVIAL, whitelist={
            "k": {"lean_name": "sixteen_classification_holds", "category": "definitional",
                  "reason": "ledger", "discloses": "docs/x.md"}})
        assert r.passed is True

    def test_a_non_structural_name_is_out_of_scope(self, tmp_path, monkeypatch):
        """The check is name-gated by design; `_thin_type_label` is the companion
        that catches statements proving nothing regardless of name."""
        r = self._run(tmp_path, monkeypatch, "theorem some_helper : True := trivial\n")
        assert r.passed is True

    def test_a_lemma_is_scanned_as_well_as_a_theorem(self, tmp_path, monkeypatch):
        """ADR-004 W7 finding C1: a defining-the-conclusion claim shipped as a
        `lemma` previously bypassed this check entirely."""
        r = self._run(tmp_path, monkeypatch,
                      "lemma sixteen_classification_holds : True := trivial\n")
        assert r.passed is False, (
            "a trivially-closed structural `lemma` passed — finding C1, reopened")

    def test_a_theorem_in_a_subdirectory_is_scanned(self, tmp_path, monkeypatch):
        """QI-01 at this call site."""
        monkeypatch.setattr(_H, "LEAN_DIR",
                            _lean_tree(tmp_path, {"Sub/Pkg/M.lean": self.TRIVIAL}))
        monkeypatch.setattr(_c, "VACUOUS_STATEMENT_BASELINE", frozenset())
        monkeypatch.setattr(_c, "MODELING_ASSUMPTION_THEOREMS", {})
        monkeypatch.setattr(_c, "PLACEHOLDER_LEAN_NAMES", {})
        assert ls.check_proxy_body_audit().passed is False


class TestTrackedHypothesisLedger:
    """Invariant #16 / R3: every CONSUMED tracked-hypothesis Prop is registered in
    `HYPOTHESIS_REGISTRY` or listed as non-load-bearing with a reason."""

    def _run(self, tmp_path, monkeypatch, *, deps, source, registry=None, non_lb=None):
        p = tmp_path / "lean_deps.json"
        p.write_text(json.dumps(deps))
        monkeypatch.setattr(_H, "LEAN_DEPS_PATH", p)
        monkeypatch.setattr(_H, "LEAN_DIR", _lean_tree(tmp_path, {"M.lean": source}))
        monkeypatch.setattr(_c, "HYPOTHESIS_REGISTRY", registry or {})
        monkeypatch.setattr(_c, "TRACKED_HYPOTHESIS_NON_LOAD_BEARING", non_lb or {})
        return ls.check_tracked_hypothesis_ledger()

    DEPS = [{"name": "SKEFTHawking.M.H_synthetic_gap", "type": "Prop", "module": "M"}]
    CONSUMER = "theorem uses_it (h : H_synthetic_gap) : True := trivial\n"

    def test_an_unregistered_consumed_hypothesis_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — a tracked Prop is load-bearing in a proof
        and appears in no ledger."""
        r = self._run(tmp_path, monkeypatch, deps=self.DEPS, source=self.CONSUMER)
        assert r.passed is False, (
            "a consumed tracked hypothesis was absent from both ledgers and the "
            "check passed — Invariant #16's single-source-of-truth is unenforced")
        assert any(d.name == "H_synthetic_gap" for d in r.details)

    def test_a_registered_hypothesis_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch, deps=self.DEPS, source=self.CONSUMER,
                      registry={"H_synthetic_gap": {"status": "open"}})
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_the_non_load_bearing_list_also_covers(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch, deps=self.DEPS, source=self.CONSUMER,
                      non_lb={"H_synthetic_gap": "not load-bearing"})
        assert r.passed is True

    def test_a_declared_but_unconsumed_hypothesis_is_out_of_scope(self, tmp_path, monkeypatch):
        """The gate is on CONSUMPTION. A Prop nobody binds carries no proof load,
        so requiring it in the registry would manufacture work."""
        r = self._run(tmp_path, monkeypatch, deps=self.DEPS,
                      source="theorem unrelated : True := trivial\n")
        assert r.passed is True

    def test_a_non_prop_definition_is_not_a_tracked_hypothesis(self, tmp_path, monkeypatch):
        """`_is_prop_codomain` exists to exclude `Subgroup`/type defs that happen to
        be `H_*`-named — flagging those would be a guard firing on correct data."""
        r = self._run(tmp_path, monkeypatch,
                      deps=[{"name": "SKEFTHawking.M.H_synthetic_gap",
                             "type": "Subgroup G", "module": "M"}],
                      source=self.CONSUMER)
        assert r.passed is True

    def test_a_missing_lean_deps_is_the_preserved_h4_divergence(self, tmp_path, monkeypatch):
        """⚠️ Asserts a KNOWN DIVERGENCE, not a desired property. Absence is PASS
        here and FAIL in `prose_theorem_reference_coverage` — ADR-009 H4, kept
        visible on purpose and DECLINED for wholesale unification in §Deferred
        item 4. Pinned so unifying it is a deliberate act that updates this test
        and `test_cannot_measure_baseline.py` together.
        """
        monkeypatch.setattr(_H, "LEAN_DEPS_PATH", tmp_path / "absent.json")
        assert ls.check_tracked_hypothesis_ledger().passed is True


class TestTrackedHypothesesFresh:
    """`docs/PERMANENT_TRACKED_HYPOTHESES.md` is an auto-generated VIEW of
    `HYPOTHESIS_REGISTRY`; drift is a HARD fail, never a silent rewrite."""

    def _run(self, tmp_path, monkeypatch, *, rendered, on_disk):
        import render_tracked_hypotheses as _r
        doc = tmp_path / "PERMANENT_TRACKED_HYPOTHESES.md"
        if on_disk is not None:
            doc.write_text(on_disk)
        monkeypatch.setattr(_r, "render", lambda: rendered)
        monkeypatch.setattr(_r, "DOC_PATH", doc)
        return ls.check_tracked_hypotheses_fresh()

    DOC = "### H_a\nbody\n"

    def test_a_stale_doc_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        r = self._run(tmp_path, monkeypatch, rendered=self.DOC, on_disk="### H_a\nOLD\n")
        assert r.passed is False, (
            "the generated doc drifted from HYPOTHESIS_REGISTRY and the check "
            "passed — this is the prior two-disjoint-ledgers failure")

    def test_a_current_doc_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch, rendered=self.DOC, on_disk=self.DOC)
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_missing_doc_fails_rather_than_being_written(self, tmp_path, monkeypatch):
        """ADR-004 W7 finding M1: do NOT silently rewrite a git-tracked file. The
        maintainer regenerates and commits it in the same wave — a check that
        repaired the tree would make the drift invisible in review."""
        doc = tmp_path / "PERMANENT_TRACKED_HYPOTHESES.md"
        r = self._run(tmp_path, monkeypatch, rendered=self.DOC, on_disk=None)
        assert r.passed is False
        assert not doc.exists(), (
            "the check WROTE the generated doc — it must hard-fail and leave the "
            "tree alone (ADR-004 W7 M1)")
