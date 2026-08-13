"""D5 both-directions tests for `validation/checks/lean_statements.py` — audit QI-27.

Three checks: `formula_grounding`, `vacuous_statement_audit`, `nogo_substrate_integrity`.
All three judge the ELABORATED TYPE from `lean_deps.json` — not a name, not a proof body,
not prose — so a synthetic `lean_deps.json` is the natural and complete seam. Every test
here writes one to `tmp_path` and repoints `_H.LEAN_DEPS_PATH`.

These are the checks that answer *"does this theorem's statement prove anything?"*. They
exist because `proxy_body_audit` is name-gated and excludes `norm_num`/`decide` bodies, so
a theorem whose statement is `∀ rank, rank = rank` slips past it entirely. A green-only
test on the live tree would be worth very little: the tree is compliant, and the classes
these catch are precisely the ones that arrive later.

MUTATION-VERIFIED 2026-08-04 — 9 mutations, all CAUGHT, clean negative control.
AST-scoped; restored with bytecode invalidation (§4b `.pyc` lesson).

  | mutation                                                       | caught by |
  |---|---|
  | `formula_grounding`: `dangling.append` -> `pass`                | `…dangling…` |
  | `formula_grounding`: drop the placeholder/`True` branch         | `…placeholder…` |
  | `formula_grounding`: `_THIN_HARD` membership -> `False`         | `…reflexive…` |
  | `formula_grounding`: leg-B kind violation -> `pass`             | `…undeclared_wrapper…` |
  | `vacuous_statement_audit`: `new_hard.append` -> `pass`          | `…new_reflexive…` |
  | `vacuous_statement_audit`: `short in BASELINE` -> `True`        | `…not_baselined…` |
  | `nogo_substrate_integrity`: `rec is None` -> `False`            | `…backing_absent…` |
  | `nogo_substrate_integrity`: `_kernel_pure` -> `True`            | `…tainted…` |
  | `nogo_substrate_integrity`: vacuity branch -> `pass`            | `…self_discharging…` |
"""
from __future__ import annotations

import json
import sys

import pytest
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import validate_helpers as _H  # noqa: E402
from src.core import constants as _c  # noqa: E402
from validation.checks import lean_statements as lst  # noqa: E402


def _deps(tmp_path: Path, monkeypatch, records: list[dict]) -> Path:
    p = tmp_path / "lean_deps.json"
    p.write_text(json.dumps(records))
    monkeypatch.setattr(_H, "LEAN_DEPS_PATH", p)
    return p


#: A kernel-pure, substantive declaration record — the shape everything else deviates from.
def _rec(name: str, *, type_: str = "0 < eps → cs > 0", kind: str = "theorem",
         core=("propext", "Classical.choice"), project=()) -> dict:
    return {"name": name, "type": type_, "kind": kind,
            "module": "SKEFTHawking.M",
            "axiom_deps_core": list(core), "axiom_deps_project": list(project)}


class TestFormulaGrounding:
    """Invariant #4 with teeth: every `Lean:` reference in `formulas.py` resolves to a
    real, non-placeholder, non-tautological theorem."""

    def _run(self, tmp_path, monkeypatch, *, doc: str, records: list[dict],
             placeholders=None, kinds=None):
        src = tmp_path / "src"
        (src / "core").mkdir(parents=True, exist_ok=True)
        (src / "core" / "formulas.py").write_text(
            f'def f():\n    """A formula.\n\n    {doc}\n    """\n    return 1\n')
        monkeypatch.setattr(_H, "SRC_DIR", src)
        _deps(tmp_path, monkeypatch, records)
        monkeypatch.setattr(_c, "PLACEHOLDER_LEAN_NAMES", placeholders or {})
        monkeypatch.setattr(_c, "FORMULA_GROUNDING_KIND", kinds or {})
        return lst.check_formula_grounding()

    def test_a_substantive_grounding_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch, doc="Lean: real_theorem",
                      records=[_rec("SKEFTHawking.M.real_theorem")])
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_dangling_reference_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — a renamed theorem leaves the formula citing
        a name that no longer exists. Hard-fail since the 2026-06-13 sweep drove the
        count to 0; it is a ratchet, not a backlog."""
        r = self._run(tmp_path, monkeypatch, doc="Lean: renamed_away",
                      records=[_rec("SKEFTHawking.M.real_theorem")])
        assert r.passed is False, (
            "a formula citing a nonexistent Lean theorem passed — Invariant #4 "
            "degenerates to 'a name was written down'")
        assert any(d.name == "renamed_away" and "does not resolve" in (d.message or "")
                   for d in r.details)

    def test_grounding_on_a_registered_placeholder_fails(self, tmp_path, monkeypatch):
        """The δ_diss-class hazard: a formula 'grounded' on a registered placeholder.

        ⚠️ The type here is deliberately SUBSTANTIVE. The first draft of this test used
        `type_="True"`, which the *thin-grounded* rule catches independently — so
        disabling the placeholder branch entirely was **MISSED**, and this test asserted
        nothing about the branch it is named for. Registering a substantive-typed
        declaration as a placeholder leaves the placeholder branch as the only rule that
        can fire.
        """
        r = self._run(tmp_path, monkeypatch, doc="Lean: stub_theorem",
                      records=[_rec("SKEFTHawking.M.stub_theorem")],
                      placeholders={"stub_theorem": {}})
        assert r.passed is False, (
            "a formula grounded on a REGISTERED placeholder passed — the registry leg "
            "of Invariant #4 is inert")
        assert any("placeholder" in (d.message or "") for d in r.details)

    def test_grounding_on_a_true_typed_stub_fails(self, tmp_path, monkeypatch):
        """The other half of the same branch, and the belt-and-braces case: a `True`
        type fails whether or not anyone remembered to register it as a placeholder.
        Two independent rules cover it, which is the correct redundancy — the registry
        is hand-maintained and the type is not."""
        r = self._run(tmp_path, monkeypatch, doc="Lean: stub_theorem",
                      records=[_rec("SKEFTHawking.M.stub_theorem", type_="True")])
        assert r.passed is False

    def test_grounding_on_a_reflexive_theorem_fails(self, tmp_path, monkeypatch):
        """ADR-004 reconcile #14. The 7–9-order δ_diss units bug hid precisely because
        grounding meant 'a named theorem exists', not 'the theorem's conclusion
        pertains to the formula'. A reflexive `X = X` proves nothing."""
        r = self._run(tmp_path, monkeypatch, doc="Lean: reflexive_thm",
                      records=[_rec("SKEFTHawking.M.reflexive_thm", type_="Eq n n")])
        assert r.passed is False, (
            "a formula grounded on a reflexive tautology passed — this is the exact "
            "shape ADR-004 reconcile #14 was written against")
        assert any("proves nothing" in (d.message or "") for d in r.details)

    #: A COMPOUND-argument identity wrapper. The distinction is load-bearing and
    #: subtle enough to be worth stating: a SIMPLE-arg wrapper (`Eq s s → Eq s s`)
    #: is ALSO caught by the thin-grounded rule, because `_thin_type_label` reads the
    #: conclusion `Eq s s` as reflexive — so it hard-fails before leg B is consulted,
    #: and the leg-B remedy ("declare grounding_kind='definitional-record'") cannot
    #: clear it. With a COMPOUND arg, `_SIMPLE_ARG_RE` correctly declines to call it
    #: reflexive (the pretty-print elision guard), so leg B is the only rule in play
    #: and its remedy works. Using the simple form here would have made these tests
    #: pass for the wrong reason and left leg B untested.
    WRAPPER = "Eq (f a) (f a) → Eq (f a) (f a)"

    def test_an_undeclared_identity_wrapper_fails(self, tmp_path, monkeypatch):
        """R-05 leg B: a `P → P` with reflexive body proves nothing, so it MUST be
        declared a definitional record. Grounding a formula on one as a derivation is
        the evidence-laundering shape."""
        r = self._run(tmp_path, monkeypatch, doc="Lean: wrapper_thm",
                      records=[_rec("SKEFTHawking.M.wrapper_thm", type_=self.WRAPPER)])
        assert r.passed is False
        assert any(d.name == "wrapper_thm" and "definitional-record" in (d.message or "")
                   for d in r.details)

    def test_declaring_it_a_definitional_record_satisfies_leg_b(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA — the honest declaration is accepted, so the rule
        is 'disclose it', not 'never use one'."""
        r = self._run(tmp_path, monkeypatch, doc="Lean: wrapper_thm",
                      records=[_rec("SKEFTHawking.M.wrapper_thm", type_=self.WRAPPER)],
                      kinds={"wrapper_thm": {"kind": "definitional-record"}})
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_definitional_record_cannot_be_relabelled_a_derivation(self, tmp_path, monkeypatch):
        """R-05 leg C — the relabel this project explicitly forbids."""
        r = self._run(tmp_path, monkeypatch, doc="Lean: wrapper_thm",
                      records=[_rec("SKEFTHawking.M.wrapper_thm", type_=self.WRAPPER)],
                      kinds={"wrapper_thm": {"kind": "derivation"}})
        assert r.passed is False
        assert any("evidence-laundering" in (d.message or "") for d in r.details)

    def test_a_grounding_kind_entry_naming_no_declaration_fails(self, tmp_path, monkeypatch):
        """Leg A's seam: the registry cannot describe theorems that do not exist."""
        r = self._run(tmp_path, monkeypatch, doc="Lean: real_theorem",
                      records=[_rec("SKEFTHawking.M.real_theorem")],
                      kinds={"ghost_thm": {"kind": "derivation"}})
        assert r.passed is False
        assert any(d.name == "ghost_thm" for d in r.details)


class TestVacuousStatementAudit:
    """The type-based companion to `proxy_body_audit`: name-agnostic and
    tactic-agnostic, so it catches `tetrad_components : 4*4=16` and
    `hom_tensor_adjunction_dim : ∀ rank, rank = rank`."""

    def _run(self, tmp_path, monkeypatch, records, *, baseline=(), placeholders=None,
             modeling=None):
        _deps(tmp_path, monkeypatch, records)
        monkeypatch.setattr(_c, "VACUOUS_STATEMENT_BASELINE", frozenset(baseline))
        monkeypatch.setattr(_c, "PLACEHOLDER_LEAN_NAMES", placeholders or {})
        monkeypatch.setattr(_c, "MODELING_ASSUMPTION_THEOREMS", modeling or {})
        return lst.check_vacuous_statement_audit()

    REFLEXIVE = [_rec("SKEFTHawking.M.dim_thm", type_="∀ rank, Eq rank rank")]

    def test_a_new_reflexive_statement_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT."""
        r = self._run(tmp_path, monkeypatch, self.REFLEXIVE)
        assert r.passed is False, (
            "a theorem whose statement is `∀ rank, rank = rank` passed — this is the "
            "class that slips `proxy_body_audit` by construction")
        assert any(d.name == "dim_thm" for d in r.details)

    def test_a_substantive_statement_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch, [_rec("SKEFTHawking.M.real_thm")])
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_a_baselined_statement_is_grandfathered_but_reported(self, tmp_path, monkeypatch):
        """Tracked debt stays VISIBLE. A baseline that silently absorbs entries is a
        place things go to disappear."""
        r = self._run(tmp_path, monkeypatch, self.REFLEXIVE, baseline={"dim_thm"})
        assert r.passed is True
        assert any(d.name == "baseline" and d.warning for d in r.details)

    def test_a_true_statement_fails(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch,
                      [_rec("SKEFTHawking.M.stub", type_="True")])
        assert r.passed is False

    def test_ground_arithmetic_is_advisory_not_a_failure(self, tmp_path, monkeypatch):
        """`4*5/2 = 10` is a closed numeric fact. The class legitimately mixes vacuous
        physics-dressing with real counting identities and has no syntactic separator,
        so hard-failing it would flag correct theorems."""
        r = self._run(tmp_path, monkeypatch,
                      [_rec("SKEFTHawking.M.count_thm", type_="Eq (4 * 4) 16")])
        assert r.passed is True
        assert any(d.name == "ground_arithmetic" and d.warning for d in r.details)

    def test_compiler_generated_declarations_are_excluded(self, tmp_path, monkeypatch):
        """`Foo.mk.congr_simp` and friends carry trivial types BY CONSTRUCTION and are
        not authored claims. Flagging them would bury the real signal."""
        r = self._run(tmp_path, monkeypatch,
                      [_rec("SKEFTHawking.M.Foo.congr_simp", type_="True"),
                       _rec("SKEFTHawking.M.Foo.mk.thing", type_="True")])
        assert r.passed is True

    def test_a_self_disclosed_definitional_suffix_is_exempt(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch,
                      [_rec("SKEFTHawking.M.shape_DEFINITIONAL", type_="True")])
        assert r.passed is True

    def test_a_compound_reflexive_is_not_flagged(self, tmp_path, monkeypatch):
        """The elision guard. `lean_deps` pretty-prints with implicit args ELIDED, so a
        genuine ℝ→ℚ transfer can print as `Eq (A.map Int.cast) (A.map Int.cast)`.
        Restricting reflexivity to SIMPLE arguments removes that whole false-positive
        class — asserting it here so the restriction is not 'tightened' away."""
        r = self._run(tmp_path, monkeypatch,
                      [_rec("SKEFTHawking.M.cast_pos",
                            type_="Eq (A.map Int.cast) (A.map Int.cast)")])
        assert r.passed is True, (
            "a compound `Eq (f a) (f a)` was flagged reflexive — that is the "
            "pretty-print elision false positive `_SIMPLE_ARG_RE` exists to prevent")


class TestNogoSubstrateIntegrity:
    """ADR-007 N-C / Invariant #17. A provably-false no-go must be backed by a live,
    kernel-pure, non-vacuous theorem — otherwise the blocker a fresh-context worker
    relies on is a prose hope."""

    def _run(self, tmp_path, monkeypatch, records, registry):
        _deps(tmp_path, monkeypatch, records)
        monkeypatch.setattr(_c, "KERNEL_NOGO_REGISTRY", registry)
        monkeypatch.setattr(_H, "PROJECT_ROOT", tmp_path / "root")
        return lst.check_nogo_substrate_integrity()

    REG = {"fork-x": {"fork_id": "fork-x", "nogo_kind": "kernel-no-go",
                      "backing_theorems": ["SKEFTHawking.M.refutation"]}}

    def test_a_live_kernel_pure_backing_passes(self, tmp_path, monkeypatch):
        """SILENT ON CORRECT DATA."""
        r = self._run(tmp_path, monkeypatch,
                      [_rec("SKEFTHawking.M.refutation")], self.REG)
        assert r.passed is True, [(d.name, d.message) for d in r.details if not d.passed]

    def test_an_absent_backing_theorem_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — Hole B: the theorem was renamed or deleted and
        the blocker rotted. This is the failure mode with no other detector: the
        registry still reads as authoritative."""
        r = self._run(tmp_path, monkeypatch, [_rec("SKEFTHawking.M.other")], self.REG)
        assert r.passed is False, (
            "a no-go whose backing theorem no longer exists passed — the registry is "
            "asserting a blocker that nothing proves")
        assert any("ABSENT" in (d.message or "") for d in r.details)

    def test_a_non_kernel_pure_backing_fails(self, tmp_path, monkeypatch):
        """A refutation resting on a project axiom or `sorryAx` is not self-enforcing."""
        r = self._run(tmp_path, monkeypatch,
                      [_rec("SKEFTHawking.M.refutation", project=("SKEFTHawking.my_axiom",))],
                      self.REG)
        assert r.passed is False
        assert any("NOT kernel-pure" in (d.message or "") for d in r.details)

    def test_a_sorry_backed_refutation_fails(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch,
                      [_rec("SKEFTHawking.M.refutation",
                            core=("propext", "sorryAx"))], self.REG)
        assert r.passed is False



    def test_a_self_discharging_backing_fails(self, tmp_path, monkeypatch):
        """Hole A: a no-go backed by `True` or a reflexive equality blocks nothing,
        while presenting as machine-enforced."""
        r = self._run(tmp_path, monkeypatch,
                      [_rec("SKEFTHawking.M.refutation", type_="True")], self.REG)
        assert r.passed is False
        assert any("VACUOUS" in (d.message or "") for d in r.details)

    # ⚠️ TWO TESTS WERE REVERSED HERE ON 2026-08-05 (PR-review R4-I5), and both were
    # mine, written 2026-08-04. Each asserted a deliberate design decision; the
    # reviewer disputed both and I judge the reviewer right. The originals read:
    #
    #   test_native_decide_is_not_counted_as_a_project_axiom
    #     "`native_decide` closure entries are filtered deliberately — they are
    #      ADR-002's concern, tracked by its own ratchet, not a taint here."
    #   test_an_entry_with_no_backing_theorem_is_advisory
    #     "A construction-level no-go may legitimately have no theorem. Hard-failing
    #      it would make the registry unusable for that class."
    #
    # Why they are wrong, in the project's own terms:
    #
    # * ADR-002's ratchet counts native_decide USES. It does not stop one from backing
    #   a no-go, and CLAUDE.md's bar is explicit — the target axiom set is
    #   `{propext, Classical.choice, Quot.sound}` — while `atlas_view._is_kernel_pure`
    #   states outright that "native_decide is policy-OK but not strictly kernel-pure".
    #   The check's own failure message says a tainted refutation "is not
    #   self-enforcing". A no-go is the one artifact whose whole purpose is to be
    #   handed to a fresh-context worker INSTEAD of re-deriving the obstacle, so it is
    #   the one place the strict reading has to hold. Aligning the check with the
    #   stated bar; not inventing a new one.
    #
    # * The "construction-level no-go" class the second test protects is hypothetical:
    #   0 of 45 live entries have empty backing. And CLAUDE.md already routes exactly
    #   that class elsewhere — "Policy / route / preference bans (not kernel-encodable)
    #   stay prose in docs/dev-loops/SETTLED_FORKS.md". An unbacked entry in the
    #   KERNEL registry is a prose ban filed in the machine-enforced store.
    #
    # Both changes were measured to be latent before landing (0 affected entries), so
    # neither turns a live population red.

    def test_a_native_decide_backing_is_NOT_kernel_pure(self, tmp_path, monkeypatch):
        """REVERSED — see the block above. Measured: 546 live declarations use
        `native_decide`; **0 of the registry's 126 backing theorems do**."""
        r = self._run(tmp_path, monkeypatch,
                      [_rec("SKEFTHawking.M.refutation",
                            project=("SKEFTHawking.M.refutation._native.native_decide",))],
                      self.REG)
        assert r.passed is False, (
            "a native_decide-backed no-go scored kernel-pure; `Lean.ofReduceBool` is "
            "in its trust surface and CLAUDE.md's bar excludes it")

    def test_an_entry_with_no_backing_theorem_FAILS(self, tmp_path, monkeypatch):
        """REVERSED — see the block above. This was the escape hatch on Invariant #17:
        an unbacked entry returned PASS, so adding one bought a pass in the registry
        that exists precisely to make a blocker machine-enforced."""
        r = self._run(tmp_path, monkeypatch, [],
                      {"fork-y": {"fork_id": "fork-y", "backing_theorems": []}})
        assert r.passed is False, (
            "a KERNEL_NOGO_REGISTRY entry with no backing theorem passed — Invariant "
            "#17's escape hatch is open again")
        assert any(d.name == "fork-y" and not d.passed for d in r.details)


class TestBinderBlindness:
    """Regression for the defect that made every other test in this file necessary.

    `_thin_type_label` tested `True` ONLY against the raw type string — before
    binder-stripping and before arrow-splitting — and never re-tested the conclusion
    it computed. And `_strip_leading_binders` matched the `∃ … ,` NOTATION, while
    lean_deps stores the ELABORATED type, where Lean has already rewritten
    `∃ x, P x` to `Exists fun x => P x`; the `∃` character never appears.

    Result: `∀ x, True`, `P → True` and `∃ x, True` all classified CLEAN — the purest
    vacuity there is, invisible to the check whose whole subject is vacuity. Measured
    2026-08-13: 897 authored theorems had an existential conclusion and the classifier
    had flagged 0 of them.
    """

    @pytest.mark.parametrize("type_str", [
        "True",
        "∀ (self : SMGPhaseData), True",
        "Exists fun x => True",
        "∀ (eos : E) (bg : B), Exists fun x => True",
        "P → True",
        "Exists fun x => Exists fun y => True",
    ])
    def test_True_is_reached_through_any_binder_or_arrow(self, type_str):
        assert lst._thin_type_label(type_str) == "True", (
            f"`{type_str}` did not classify as vacuous. A `True` conclusion is vacuous "
            f"however it is reached; anything implies True and `∃ x, True` asserts only "
            f"that some type is inhabited.")

    def test_the_elaborated_existential_form_is_what_gets_stripped(self):
        """The `∃` character never appears in an elaborated type — `Exists fun` does."""
        assert lst._strip_leading_binders("Exists fun x => Eq x x") == "Eq x x"
        assert lst._thin_type_label("Exists fun x => Eq x x") == "reflexive (X=X)"

    def test_a_substantive_conclusion_under_a_binder_is_untouched(self):
        """NEGATIVE CONTROL — the widening must not swallow real statements."""
        assert lst._thin_type_label("∀ (x : Real), 0 < x → Exists fun y => Eq (f y) x") is None
        assert lst._thin_type_label("∀ (eps : Real), 0 < eps → cs > 0") is None


class TestExistentialWitnessDisclosure:
    """`∃ x, P x` is vacuous exactly when a trivial witness satisfies `P`. That is a
    proof obligation, not a syntactic property, so the gate requires the witness be
    NAMED rather than trying to classify it.

    A syntactic discriminator WAS built and measured first — "is some bound variable
    equated to a project term" — and it was wrong in both directions on the live
    population. It was discarded, not shipped. These tests pin the disclosure contract
    that replaced it.
    """

    EXI = "∀ (mdr : M), Exists fun d => Exists fun C => And (0 < C) (LE.le (abs d) C)"

    def _run(self, tmp_path, monkeypatch, *, records, registry, aristotle=("thm_x",),
             doc="", placeholders=None, escape_ceiling=5, misnamed_ceiling=7):
        src = tmp_path / "src" / "core"
        src.mkdir(parents=True, exist_ok=True)
        (src / "formulas.py").write_text(doc)
        monkeypatch.setattr(_H, "SRC_DIR", tmp_path / "src")
        _deps(tmp_path, monkeypatch, records)
        monkeypatch.setattr(_c, "EXISTENTIAL_WITNESS_REGISTRY", registry)
        monkeypatch.setattr(_c, "ARISTOTLE_THEOREMS", {a: {} for a in aristotle})
        monkeypatch.setattr(_c, "PLACEHOLDER_LEAN_NAMES", placeholders or {})
        monkeypatch.setattr(_c, "MODELING_ASSUMPTION_THEOREMS", {})
        monkeypatch.setattr(_c, "EXISTENTIAL_ESCAPE_CEILING", escape_ceiling)
        monkeypatch.setattr(_c, "EXISTENTIAL_MISNAMED_CEILING", misnamed_ceiling)
        return lst.check_existential_witness_disclosure()

    def test_an_undisclosed_existential_result_fails(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — a result sold with no witness named."""
        r = self._run(tmp_path, monkeypatch,
                      records=[_rec("SKEFTHawking.M.thm_x", type_=self.EXI)],
                      registry={})
        assert r.passed is False
        assert any(d.name == "thm_x" for d in r.details)

    def test_a_disclosed_existential_passes(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch,
                      records=[_rec("SKEFTHawking.M.thm_x", type_=self.EXI)],
                      registry={"thm_x": {"status": "anchored", "witness": "the fixed point"}})
        assert r.passed is True

    def test_an_entry_with_no_witness_text_fails(self, tmp_path, monkeypatch):
        """A registry entry is not disclosure unless it actually names the witness."""
        r = self._run(tmp_path, monkeypatch,
                      records=[_rec("SKEFTHawking.M.thm_x", type_=self.EXI)],
                      registry={"thm_x": {"status": "anchored", "witness": ""}})
        assert r.passed is False

    def test_a_non_existential_result_is_out_of_scope(self, tmp_path, monkeypatch):
        """NEGATIVE CONTROL — the gate must not demand witnesses from every theorem.

        The population must be NON-EMPTY for this to test anything: with only the
        non-existential theorem in scope the seam guard fires UNVERIFIED, and a
        version of this test that passed on THAT would be asserting nothing.
        """
        r = self._run(tmp_path, monkeypatch,
                      records=[_rec("SKEFTHawking.M.plain", type_="0 < eps → cs > 0"),
                               _rec("SKEFTHawking.M.thm_x", type_=self.EXI)],
                      registry={"thm_x": {"status": "anchored", "witness": "w"}},
                      aristotle=("plain", "thm_x"))
        assert r.passed is True, "a non-existential theorem was asked to name a witness"
        assert not any(d.name == "plain" for d in r.details)

    def test_an_unsold_existential_is_out_of_scope(self, tmp_path, monkeypatch):
        """Scope is what the project SELLS as a result, not every existential."""
        r = self._run(tmp_path, monkeypatch,
                      records=[_rec("SKEFTHawking.M.internal", type_=self.EXI)],
                      registry={}, aristotle=())
        assert r.passed is False, (
            "population was empty — the seam guard must report UNVERIFIED, never PASS")
        assert any(d.name == "population" for d in r.details)

    def test_a_declared_placeholder_is_exempt(self, tmp_path, monkeypatch):
        """Disclosed elsewhere; two registrations would let them disagree."""
        r = self._run(tmp_path, monkeypatch,
                      records=[_rec("SKEFTHawking.M.thm_x", type_=self.EXI),
                               _rec("SKEFTHawking.M.thm_y", type_=self.EXI)],
                      registry={"thm_y": {"status": "anchored", "witness": "w"}},
                      aristotle=("thm_x", "thm_y"),
                      placeholders={"thm_x": "thm_x"})
        assert r.passed is True

    def test_a_new_escape_breaches_the_down_only_ceiling(self, tmp_path, monkeypatch):
        """The ratchet: disclosing an escape is not the same as being allowed one."""
        r = self._run(tmp_path, monkeypatch,
                      records=[_rec("SKEFTHawking.M.thm_x", type_=self.EXI)],
                      registry={"thm_x": {"status": "escape", "witness": "d=1, C=1"}},
                      escape_ceiling=0)
        assert r.passed is False
        assert any("never raise this ceiling" in (d.message or "") for d in r.details)

    def test_a_new_misnamed_breaches_its_ceiling(self, tmp_path, monkeypatch):
        r = self._run(tmp_path, monkeypatch,
                      records=[_rec("SKEFTHawking.M.thm_x", type_=self.EXI)],
                      registry={"thm_x": {"status": "misnamed", "witness": "w"}},
                      misnamed_ceiling=0)
        assert r.passed is False

    def test_an_escape_at_the_ceiling_is_advisory_not_red(self, tmp_path, monkeypatch):
        """Tracked debt stays visible without blocking — it leaves by remediation."""
        r = self._run(tmp_path, monkeypatch,
                      records=[_rec("SKEFTHawking.M.thm_x", type_=self.EXI)],
                      registry={"thm_x": {"status": "escape", "witness": "d=1, C=1"}},
                      escape_ceiling=1)
        assert r.passed is True
        assert any(d.warning for d in r.details)
