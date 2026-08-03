"""Unit tests for the Substrate Integrity Gates (ADR-004) detectors.

Covers the deterministic pattern logic of W1 (`placeholder_not_cited`) and W2
(`proxy_body_audit`) without running the full tree-scanning checks, plus the
registry invariants the gates rely on. Fast (no Lean, no I/O beyond imports).
"""
import re
import sys
from pathlib import Path

# `scripts/` on the path so this file imports `validate` under the SAME module
# name every other test uses. See the note below the imports.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from src.core.constants import (
    PLACEHOLDER_THEOREMS,
    PLACEHOLDER_LEAN_NAMES,
    PLACEHOLDER_TOTAL_COUNT,
    MODELING_ASSUMPTION_THEOREMS,
)
from validate import (
    _STRUCTURAL_NAME_RE,
    _TRIVIAL_BODY_RES,
    _NONTRIVIAL_MARKER_RE,
    _tex_name_pattern,
    _VERIFY_CLAIM_RE,
    _HEDGE_CLAIM_RE,
    _is_prop_codomain,
    _TRACKED_PROP_NAME_RE,
    _parse_formula_lean_refs,
)

# ⚠️ These nine import sites read `from scripts.validate import ...` until
# 2026-08-03. Because `pythonpath = ["."]` makes `scripts/validate.py` reachable
# as `scripts.validate`, while every other test reaches it as `validate`, that
# loaded the module TWICE — two distinct module objects, each executing the
# `@register_check` decorators, each with its own caches and its own copies of
# what used to be module-global flags.
#
# It was invisible for as long as every piece of that state was per-module: two
# registries of 59 each looked exactly like one registry of 59 from either side.
# It stopped being invisible when `_CHECKS` moved to the shared
# `validation._registry` singleton (ADR-009 Phase 2) — both loads then appended to
# the SAME list and the registry contract failed at 118 checks with duplicate
# names. The extraction did not create the defect; it made an existing one
# observable, which is the argument for the package boundary in miniature.
#
# It was never harmless. Two module identities also meant `validate.CheckResult`
# and `scripts.validate.CheckResult` were different classes, so `isinstance`
# across the boundary silently returned False, and before `validation._config`
# existed a `--strict` set on one had no effect on the other.
#
# `tests/test_validate_public_surface.py::test_validate_is_loaded_exactly_once`
# now guards this. Import `validate`, never `scripts.validate`.


# ── Registry invariants (W1 / W2) ──────────────────────────────────────

def test_placeholder_registry_total_matches_constant():
    assert PLACEHOLDER_TOTAL_COUNT == len(PLACEHOLDER_THEOREMS) == 26


def test_every_placeholder_has_lean_name_and_category():
    for key, meta in PLACEHOLDER_THEOREMS.items():
        assert meta.get("lean_name"), f"{key} missing lean_name"
        assert meta.get("category") in ("content", "docs_marker"), key


def test_placeholder_lean_names_are_unique_and_indexed():
    assert len(PLACEHOLDER_LEAN_NAMES) == len(PLACEHOLDER_THEOREMS)


def test_modeling_assumption_entries_disclose():
    """A whitelist entry is only a valid disclosure if it carries reason+discloses."""
    for key, meta in MODELING_ASSUMPTION_THEOREMS.items():
        assert meta.get("lean_name"), f"{key} missing lean_name"
        assert meta.get("category") in ("definitional", "vacuous_proxy"), key
        assert meta.get("reason"), f"{key} missing reason"
        assert meta.get("discloses"), f"{key} missing discloses"
        if meta["category"] == "vacuous_proxy":
            assert meta.get("discharge"), f"vacuous_proxy {key} needs a discharge pointer"


# ── W2 proxy-body detector logic ───────────────────────────────────────

def _is_trivial(body: str):
    norm = " ".join(body.split())
    if _NONTRIVIAL_MARKER_RE.search(norm):
        return None
    return next((lbl for rx, lbl in _TRIVIAL_BODY_RES if rx.match(norm)), None)


def test_structural_name_matches_quantity_claims():
    for name in ["ext_dim_3", "ising_wrt_rank", "dg_generator_count",
                 "rank2_classification_count", "sixteen_convergence_full",
                 "gauge_emergence_equivalence", "free_energy_well_defined"]:
        assert _STRUCTURAL_NAME_RE.search(name), name


def test_structural_name_ignores_ordinary_theorems():
    for name in ["bogoliubov_superluminal", "damping_rate_pos", "sm_z4_all_odd"]:
        assert not _STRUCTURAL_NAME_RE.search(name), name


def test_trivial_body_detection():
    assert _is_trivial("rfl") == "rfl"
    assert _is_trivial("by rfl") == "rfl"
    assert _is_trivial("by exact rfl") == "rfl"
    assert _is_trivial("trivial") == "trivial"
    assert _is_trivial("by cases c <;> rfl") == "cases <;> rfl"
    assert _is_trivial("h_dd") == "identity-return (hypothesis)"
    assert _is_trivial("by exact h_step") == "identity-return (hypothesis)"


def test_decide_and_real_proofs_are_not_trivial():
    # ADR-002 owns decide/native_decide; real tactics are not trivial closers.
    assert _is_trivial("by decide") is None
    assert _is_trivial("by native_decide") is None
    assert _is_trivial("by norm_num") is None
    assert _is_trivial("sixteen_dvd_latticeSig M.form M.even_unimod M.topo") is None
    assert _is_trivial("by simp [foo]; ring") is None


def test_known_flagged_decls_are_all_whitelisted():
    """Every decl the 2026-06-13 calibration flagged is disclosed in the whitelist."""
    flagged = {
        "change_of_rings_ext_dim", "g2k1_dims_eq_fib", "rank2_classification_count",
        "emanant_su2_dim", "hw_matches_sm_count", "sl2_dim_eq", "dg_generator_count",
        "dg_relation_count", "free_energy_well_defined", "ising_wrt_rank",
        "fib_wrt_rank", "sVec_fermion_dim_DEFINITIONAL",
    }
    wl = {m.get("lean_name", k) for k, m in MODELING_ASSUMPTION_THEOREMS.items()}
    assert flagged <= wl, f"un-disclosed flagged decls: {flagged - wl}"


# ── W1 placeholder-citation detector logic ─────────────────────────────

def test_tex_name_pattern_matches_escaped_underscores():
    pat = _tex_name_pattern("gauge_emergence_statement")
    assert pat.search(r"\texttt{gauge\_emergence\_statement}")
    assert pat.search("gauge_emergence_statement")


def test_gauge_signature_present_for_paper7_case():
    sig = PLACEHOLDER_THEOREMS["gauge_emergence_equivalence"].get("tex_signature")
    assert sig
    assert re.compile(sig).search(r"$Z(\mathrm{Vec}_G) \cong \mathrm{Rep}(D(G))$")


def test_verify_vs_hedge_windows():
    overclaim = r"these 4049 theorems provide end-to-end formal verification"
    assert _VERIFY_CLAIM_RE.search(overclaim)
    assert not _HEDGE_CLAIM_RE.search(overclaim)
    fixed = (r"verified concretely for $G = \mathbb{Z}/2$ ... the general-$G$ "
             r"statement is formalized at the statement level")
    assert _HEDGE_CLAIM_RE.search(fixed)


# ── W3 tracked-hypothesis single source of truth ───────────────────────

from src.core.constants import HYPOTHESIS_REGISTRY  # noqa: E402


def test_prop_codomain_filter_excludes_subgroup_defs():
    assert _is_prop_codomain("Prop")
    assert _is_prop_codomain("SKEFTHawking.NeutrinoMixing.PMNSMatrix → Prop")
    # the H_Fib / H_of_G false positives are Subgroup-valued, not Prop
    assert not _is_prop_codomain(
        "Subgroup (Subtype fun x => SetLike.instMembership.mem (Matrix.specialUnitaryGroup (Fin 2) Complex) x)")


def test_tracked_prop_name_filter():
    for n in ["H_RegimePartition", "TPFConjecture", "Phase6hHyperchargeSplittingHypothesis"]:
        assert _TRACKED_PROP_NAME_RE.match(n), n
    for n in ["wrtS2xS1", "sm_fermion_count"]:
        assert not _TRACKED_PROP_NAME_RE.match(n), n


def test_every_registry_entry_is_tiered():
    valid = {"headline", "external_boundary", "discharge_future", "local"}
    for k, v in HYPOTHESIS_REGISTRY.items():
        assert v.get("tier") in valid, f"{k} tier={v.get('tier')!r}"
        assert v.get("statement") or v.get("status"), k


def test_doc_props_merged_into_registry():
    """The cosmology Props formerly only in the markdown doc now live in the registry."""
    for k in ["H_VestigialModeIsGraviton", "H_DESICompatibility",
              "H_RT_Formula_Valid", "TPFConjecture"]:
        assert k in HYPOTHESIS_REGISTRY, k
        assert HYPOTHESIS_REGISTRY[k].get("prose"), f"{k} needs publication prose"


def test_topo_covered_by_rokhlin_not_double_registered():
    """topo (2|sigma/8) is covered via rokhlin_sigma_mod_16's dependent_theorems, not its own entry."""
    assert "topo" not in HYPOTHESIS_REGISTRY
    dts = HYPOTHESIS_REGISTRY["rokhlin_sigma_mod_16"].get("dependent_theorems", [])
    assert any("SmoothSpinManifold4.rokhlin" in d for d in dts)


def test_render_is_deterministic_and_matches_disk():
    from scripts import render_tracked_hypotheses as r
    out = r.render()
    assert out == r.render()  # deterministic
    assert out.count("### ") == len(HYPOTHESIS_REGISTRY)
    assert r.DOC_PATH.read_text() == out, "doc out of sync — run render_tracked_hypotheses.py"


# ── W4 formula content-grounding ───────────────────────────────────────

def test_formula_ref_parser_drops_artifacts():
    src = (
        '    """\n    Lean: real_theorem_name, AnotherModule.also_real (Foo.lean)\n'
        '    Lean: WRTComputation.lean\n'           # filename — drop
        '    Lean: pending\n'                        # aristotle convention — drop
        '    Lean: K0E0\n'                           # matrix label — drop
        '    Lean: firstOrder_correction_zero_iff — proves stuff\n    """\n'
    )
    refs = _parse_formula_lean_refs(src)
    assert "real_theorem_name" in refs
    assert "AnotherModule.also_real" in refs
    assert "firstOrder_correction_zero_iff" in refs
    for artifact in ("WRTComputation.lean", "pending", "K0E0"):
        assert artifact not in refs


def test_no_formula_grounded_on_placeholder():
    """Invariant #4 content-grounding: no formula cites a True/placeholder stub.
    Invokes the real check (which resolution-gates before classifying)."""
    from validate import check_formula_grounding
    res = check_formula_grounding()
    assert res.passed, "a formula is grounded on a placeholder/True stub"
    # the hard-fail dimension is placeholder-grounding; dangling refs are advisory
    fails = [d for d in res.details if not d.passed]
    assert not fails, f"placeholder-grounded formula refs: {[d.name for d in fails]}"


# ── W5 native_decide accounting ────────────────────────────────────────

def test_native_decide_metric_in_counts_and_under_ceiling():
    import json
    from src.core.constants import NATIVE_DECIDE_DECL_CLOSURE_CEILING as CEIL
    root = Path(__file__).resolve().parent.parent
    lean = json.loads((root / "docs" / "counts.json").read_text())["lean"]
    cur = lean.get("native_decide_decl_closure")
    assert isinstance(cur, int), "counts.json must carry native_decide_decl_closure (R4)"
    assert cur <= CEIL, f"native_decide decl-closure {cur} exceeds ceiling {CEIL}"
    # the audit's key finding: FKLW/RossSelinger + QuantumNetwork carry ZERO real nd
    clusters = lean.get("native_decide_clusters", {})
    assert "fklw_rossselinger" not in clusters
    assert "quantum_network" not in clusters


# ── W7 adversarial-review hardening (C1/C2/H2/L1) ───────────────────────

def test_scanner_yields_lemmas_not_just_theorems():  # C1
    from scripts.build_graph import _scan_lean_theorem_bodies
    names = [n for n, _, _ in _scan_lean_theorem_bodies(
        "lemma foo_rank_iso : a = a := rfl\ntheorem bar : b := rfl\ndef baz : Nat := 3\n")]
    assert "foo_rank_iso" in names and "bar" in names
    assert "baz" not in names  # defs are NOT claims — not scanned


def test_new_trivial_body_patterns_fire_but_spare_genuine_bundles():  # C2
    from validate import _TRIVIAL_BODY_RES, _NONTRIVIAL_MARKER_RE

    def istriv(b):
        n = " ".join(b.split())
        if _NONTRIVIAL_MARKER_RE.search(n):
            return None
        return next((l for rx, l in _TRIVIAL_BODY_RES if rx.match(n)), None)
    assert istriv("Iff.rfl")
    assert istriv("⟨rfl, rfl⟩")
    assert istriv("by exact ⟨rfl, rfl⟩")
    assert istriv("And.intro rfl rfl")
    assert istriv("fun M => M.topo")
    # a genuine bundle of REAL proven lemmas must NOT be flagged
    assert istriv("⟨left_inverse, right_inverse, grading_preserved⟩") is None
    assert istriv("⟨h1, by ring⟩") is None


def test_hedge_is_claim_specific_not_stray_word():  # H2
    from validate import _VERIFY_CLAIM_RE, _HEDGE_CLAIM_RE
    attack = ("We formally verify Z(Vec_G)=Rep(D(G)) for all G in Lean. "
              "The CLI stub script is separate; arithmetic modulo p.")
    assert _VERIFY_CLAIM_RE.search(attack)
    assert not _HEDGE_CLAIM_RE.search(attack), "a stray 'stub'/'modulo' must NOT suppress"
    legit = ("verified concretely for G=Z/2; the general-G statement is "
             "formalized at the statement level, deferred to future work")
    assert _HEDGE_CLAIM_RE.search(legit)


def test_non_load_bearing_registry_exists():  # L1
    from src.core.constants import TRACKED_HYPOTHESIS_NON_LOAD_BEARING
    assert isinstance(TRACKED_HYPOTHESIS_NON_LOAD_BEARING, dict)


# ── SIG gate hardening: blind-spot reconciliation (2026-06-13) ──────────

from validate import (  # noqa: E402
    _thin_type_label, _THIN_HARD, _is_autogen_decl,
    _OVERCLAIM_VERB_RE, _LEDGER_HEDGE_RE,
    check_vacuous_statement_audit, check_proxy_body_audit,
    check_formula_grounding, check_disclosure_consistency,
)
from src.core.constants import VACUOUS_STATEMENT_BASELINE  # noqa: E402


def test_thin_type_reflexive_simple_args():
    assert _thin_type_label("∀ (rank : Nat), Eq rank rank") == "reflexive (X=X)"
    assert _thin_type_label("Eq 2 2") == "reflexive (X=X)"
    assert _thin_type_label("∀ (N_f : Nat), Eq 10 10") == "reflexive (X=X)"


def test_thin_type_compound_eq_is_elision_safe():  # sigPos_cast_pos class
    # lean_deps elides implicit args, so a genuine transfer P_ℝ→P_ℚ prints with
    # identical sides; restricting reflexive to SIMPLE args avoids the FP, and
    # type-based hyp-return is omitted entirely.
    assert _thin_type_label(
        "∀ A, instLTNat.lt 0 (sigPos (A.map Int.cast)) "
        "→ instLTNat.lt 0 (sigPos (A.map Int.cast))") is None
    assert _thin_type_label("Eq (sigPos (A.map Int.cast)) (sigPos (A.map Int.cast))") is None


def test_thin_type_ground_arith_is_advisory_not_hard():
    assert _thin_type_label("Eq (instHMul.hMul 4 4) 16") == "ground-arith"
    assert _thin_type_label("GT.gt 6 1") == "ground-arith"
    assert "ground-arith" not in _THIN_HARD


def test_thin_type_true_and_genuine_nonthin():
    assert _thin_type_label("True") == "True"
    assert _thin_type_label("Eq (wrtS2xS1 D) D.n") is None  # relates distinct named things


def test_is_autogen_decl():
    assert _is_autogen_decl("Padic.congr_simp")
    assert _is_autogen_decl("SKEFTHawking.Foo.mk.congr_simp")
    assert _is_autogen_decl("Bar.injEq")
    assert not _is_autogen_decl("even_odd_force_equivalence")
    assert not _is_autogen_decl("SKEFTHawking.RokhlinHMDischarge.sigPos_cast_pos")


def test_scanner_captures_body_on_continuation_line():  # #25 (the empty-body bug)
    from scripts.build_graph import _scan_lean_theorem_bodies
    src = "theorem foo (x : Nat) :\n    x = x := rfl\n"
    bodies = {n: b for n, _, b in _scan_lean_theorem_bodies(src)}
    assert bodies.get("foo") == "rfl", bodies  # was '' before the fix


def test_anon_ctor_equiv_refl_pattern_fires():  # #23
    def label(b):
        return next((lbl for rx, lbl in _TRIVIAL_BODY_RES if rx.match(b)), None)
    assert "Equiv.refl" in (label("⟨Equiv.refl _, (Equiv.refl _).bijective⟩") or "")
    assert label("⟨left_inverse, right_inverse⟩") is None  # real constructor spared


def test_overclaim_and_ledger_regexes():  # #9
    assert _OVERCLAIM_VERB_RE.search("establishes the 8/8 closure")
    assert _OVERCLAIM_VERB_RE.search("demonstrates that")
    assert not _OVERCLAIM_VERB_RE.search("is proven (zero sorry)")  # 'proven' excluded
    assert _LEDGER_HEDGE_RE.search("records the 8/8 tally")
    assert _LEDGER_HEDGE_RE.search("a verified-consistent classification ledger")


def test_vacuous_baseline_nonempty_and_all_gates_green():
    assert len(VACUOUS_STATEMENT_BASELINE) >= 40
    assert check_vacuous_statement_audit().passed
    assert check_proxy_body_audit().passed
    assert check_formula_grounding().passed
    assert check_disclosure_consistency().passed


# ── R-07: apex discharge + dependent-theorem resolution (live smoke) ─────

def test_r07_fib_apexes_discharged_in_registry():
    """The three Fibonacci headline apexes are marked discharged with a
    producer pointer, and the phantom central_charge dep target is gone."""
    from src.core.constants import HYPOTHESIS_REGISTRY
    for key, producer_suffix in (
        ("H_Fib_v4_witness", "H_Fib_v4_witness_unconditional"),
        ("H_Fib_TwoLITangents", "H_Fib_TwoLITangents_unconditional"),
        ("H_Fib_NonCentralConjugateWitness", "H_Fib_NonCentralConjugateWitness_discharged"),
    ):
        h = HYPOTHESIS_REGISTRY[key]
        assert h["status"] == "discharged", key
        assert h.get("discharged_by", "").endswith(producer_suffix), key
    # the phantom target is replaced by the real WangBridge derivation theorem
    cc = HYPOTHESIS_REGISTRY["c_minus_equals_8Nf"]["dependent_theorems"]
    assert "SKEFTHawking.central_charge_from_sm" not in cc
    assert "SKEFTHawking.fermion_count_gives_central_charge" in cc


def test_r07_atlas_integrity_apex_and_dep_legs():
    """The strengthened atlas_integrity check passes and reflects R-07:
    3 apexes explicitly discharged (producer-verified), all dependent_theorems
    FQNs resolve (no phantom)."""
    from validate import check_atlas_integrity
    result = check_atlas_integrity()
    assert result.passed, [(d.name, d.message) for d in result.details if not d.passed]
    by_name = {d.name: d for d in result.details}
    assert "discharged" in by_name["apex_not_closed"].message
    assert by_name["dependent_theorems_resolve"].passed


# ── R-05: formula-grounding kind (definitional-record vs derivation) ─────

def test_r05_grounding_kind_registry_and_helpers():
    from src.core.constants import FORMULA_GROUNDING_KIND
    from validate import _is_vacuous_identity_wrapper
    for k in ("wrt_S2xS1_eq_rank", "dd_simples_count"):
        assert FORMULA_GROUNDING_KIND[k]["kind"] == "definitional-record"
    # dd_simples_count-shape: `P → P` with a reflexive body -> vacuous idwrap.
    dd_ty = ("∀ (n : Nat) (f : Fin n → Nat), Eq (Finset.univ.sum f) (Finset.univ.sum f) "
             "→ Eq (Finset.univ.sum f) (Finset.univ.sum f)")
    assert _is_vacuous_identity_wrapper(dd_ty)
    # a genuine transfer P_ℝ → P_ℚ (elision) is NOT flagged (body not reflexive).
    assert not _is_vacuous_identity_wrapper("∀ (x : R), P x → Q x")
    # a plain equality is not an identity wrapper.
    assert not _is_vacuous_identity_wrapper("∀ (D : T), Eq (wrtS2xS1 D) D.n")


def test_r05_formula_grounding_passes_live():
    from validate import check_formula_grounding
    r = check_formula_grounding()
    assert r.passed, [(d.name, d.message) for d in r.details if not d.passed]


def test_r05_gate_fails_if_definitional_record_relabeled_derivation(monkeypatch):
    """The gate must FAIL if someone re-labels a definitional record as a
    derivation, for BOTH shapes: the identity wrapper (auto-detected) and the
    rfl-definitional equality (source-proof-confirmed)."""
    from validate import check_formula_grounding
    from src.core import constants as C
    base = dict(C.FORMULA_GROUNDING_KIND)

    # (1) drop dd_simples_count entirely -> its vacuous identity wrapper is now
    #     an undeclared derivation-grounding -> FAIL flagging dd_simples_count.
    monkeypatch.setattr(
        C, "FORMULA_GROUNDING_KIND",
        {k: v for k, v in base.items() if k != "dd_simples_count"})
    r = check_formula_grounding()
    assert not r.passed
    assert any("dd_simples_count" in d.name for d in r.details if not d.passed)

    # (2) relabel wrt_S2xS1_eq_rank to 'derivation' -> its rfl-definitional
    #     equality contradicts the label -> FAIL flagging wrt_S2xS1_eq_rank.
    relabel = dict(base)
    relabel["wrt_S2xS1_eq_rank"] = {"kind": "derivation", "note": "x"}
    monkeypatch.setattr(C, "FORMULA_GROUNDING_KIND", relabel)
    r = check_formula_grounding()
    assert not r.passed
    assert any("wrt_S2xS1_eq_rank" in d.name for d in r.details if not d.passed)
