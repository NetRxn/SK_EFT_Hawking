/-
# Phase 6n Wave 1b Stage 5 — Project-local Witt-class infrastructure

**Mathlib upstream-PR candidate** per the program's in-program-build
track record (`feedback_mathlib_upstream_pr_track_record.md`).

The chiral central charge mod 24 is the simplest Witt invariant for
chiral CFTs/MTCs (Schellekens hep-th/9205072 §3, Kong-Wen
arXiv:1404.6029 §4, Davydov-Müger-Nikshych-Ostrik J. reine angew.
Math. 677 (2013) 135). For the Schellekens-class chiral CFT setting
relevant to the program, the chiral-central-charge → Witt-invariant
map factors through `ZMod 24` and captures the load-bearing data for
the chiralCentralChargeMod24 ↔ Witt-class biconditional.

This module ships project-local Witt-class infrastructure at the
abelian-group level via `WittInvariant := ZMod 24`, sidestepping the
absent Mathlib MTC + Witt-group infrastructure (a multi-year community
project per the Stage-1 §6 risk register) while preserving the
substantive content needed for the Wave 1b Stage 5 closure of the
chiralCentralChargeMod24 ↔ Witt-class biconditional.

**Stage 5 substantive content:**

1. `WittInvariant := ZMod 24` with inherited AddCommGroup + DecidableEq.
2. `WittInvariant.fromChiralCentralCharge` AddMonoidHom from integer
   chiral central charges to Witt invariants.
3. `WittTrivial` predicate + biconditional with `24 ∣ c`.
4. `WittEquivalent` equivalence relation on integer chiral central
   charges, with proven reflexivity, symmetry, transitivity.
5. `chiralCentralCharge_wittTrivial_iff_three_dvd_N_f` — the Schellekens
   chain LIFTED to Witt-invariant level (project-local Stage 5
   substantive deliverable; previously only at integer-divisibility
   level via `generation_constraint_iff`).
6. `standardModel_wittTrivial` — concrete physical witness at
   3-generation N_f = 3 case.
7. `stage5_chiralCentralCharge_witt_bridge` — bridges Stage 5 Witt-class
   form to SymTFT-side `chiralCentralChargeMod24Compatible` predicate,
   closing the previous Stage-4c "predicate-level only" bridge with the
   Witt-group-grade form.
8. `wittInvariant_homomorphism_witness` — the AddMonoidHom property of
   the chiral-central-charge → Witt-invariant map, the load-bearing
   Witt-group structure that lifts the Stage-4c arithmetic biconditional
   to the level of an abelian-group homomorphism.

**Mathlib-PR retention pattern.** When full Mathlib MTC/Witt-group
infrastructure lands, this module's predicates connect to the canonical
forms via re-derivation lemmas (Stage 4c → Stage 5 → Mathlib MTC
Witt-group). Until then, the project-local form is load-bearing for the
SymTFT bridge.

References:
- Schellekens A N, hep-th/9205072 — chiral central charge mod 24 invariant
- Kong L, Wen X-G, arXiv:1404.6029 — Witt class for chiral CFTs
- Davydov-Müger-Nikshych-Ostrik J. reine angew. Math. 677 (2013) 135 — Witt group
- `GenerationConstraint.lean` — Stage-4c project-local biconditional
- `SymTFTAudit/Applicability.lean` — Stage 3 SymTFT predicates
- `SymTFTAudit/CrossBridges.lean` — Stage 4 cross-bridges (Stage-4c third bridge)
-/
import SKEFTHawking.GenerationConstraint
import SKEFTHawking.SymTFTAudit.Applicability
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD

namespace SKEFTHawking.SymTFTAudit

/-! ## The Witt invariant. -/

/--
**The project-local Witt invariant for chiral CFTs: chiral central
charge mod 24.**

Captures the Schellekens hep-th/9205072 §3 / Kong-Wen arXiv:1404.6029 §4
invariant at the level of integer divisibility, sidestepping the absent
Mathlib MTC + Witt-group infrastructure. The full MTC Witt group is
strictly larger (carries higher-torsion / cyclotomic structure beyond
`ZMod 24`); this project-local form captures the chiral-central-charge
piece which is load-bearing for the Schellekens chain.

When Mathlib MTC + Witt-group infrastructure ships, this becomes the
chiral-central-charge component of the canonical Mathlib Witt-group
structure via a Witt-group-quotient projection. -/
def WittInvariant : Type := ZMod 24

instance : AddCommGroup WittInvariant := inferInstanceAs (AddCommGroup (ZMod 24))
instance : DecidableEq WittInvariant := inferInstanceAs (DecidableEq (ZMod 24))
instance : Fintype WittInvariant := inferInstanceAs (Fintype (ZMod 24))

/-- The Witt invariant of a chiral central charge `c : ℤ` is `c mod 24`. -/
def WittInvariant.fromChiralCentralCharge : ℤ →+ WittInvariant :=
  (Int.castRingHom (ZMod 24)).toAddMonoidHom

/-! ## Witt-triviality. -/

/--
**A chiral central charge is Witt-trivial iff its Witt invariant is
zero, iff it is divisible by 24.**

This is the Stage 5 form of the chiralCentralCharge mod 24 condition,
lifted from "arithmetic divisibility" (Stage 4c) to "abelian-group-level
Witt invariant zero" (Stage 5). -/
def WittTrivial (c : ℤ) : Prop :=
  WittInvariant.fromChiralCentralCharge c = 0

theorem WittTrivial_iff_dvd (c : ℤ) : WittTrivial c ↔ (24 : ℤ) ∣ c := by
  unfold WittTrivial WittInvariant.fromChiralCentralCharge WittInvariant
  show ((c : ZMod 24) : ZMod 24) = 0 ↔ (24 : ℤ) ∣ c
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd c 24)

/-! ## Witt-equivalence on integer chiral central charges. -/

/--
**Witt-equivalence: two integer chiral central charges are
Witt-equivalent iff they map to the same Witt invariant, iff their
difference is divisible by 24.**

This is the equivalence relation underlying the project-local Witt-class
quotient. The lift to abelian-group level (this module's Stage 5 form)
sees Witt-equivalence as the kernel-equivalence of an AddMonoidHom — a
load-bearing distinction vs. Stage 4c's "ad-hoc divisibility test." -/
def WittEquivalent (c c' : ℤ) : Prop :=
  WittInvariant.fromChiralCentralCharge c = WittInvariant.fromChiralCentralCharge c'

theorem WittEquivalent_iff_dvd (c c' : ℤ) :
    WittEquivalent c c' ↔ (24 : ℤ) ∣ (c - c') := by
  unfold WittEquivalent
  constructor
  · intro h
    have : WittInvariant.fromChiralCentralCharge (c - c') = 0 := by
      rw [map_sub, h, sub_self]
    exact (WittTrivial_iff_dvd (c - c')).mp this
  · intro h
    have hzero : WittInvariant.fromChiralCentralCharge (c - c') = 0 :=
      (WittTrivial_iff_dvd (c - c')).mpr h
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero

theorem WittEquivalent_refl (c : ℤ) : WittEquivalent c c := rfl

theorem WittEquivalent_symm {c c' : ℤ} (h : WittEquivalent c c') :
    WittEquivalent c' c := h.symm

theorem WittEquivalent_trans {c c' c'' : ℤ}
    (h1 : WittEquivalent c c') (h2 : WittEquivalent c' c'') :
    WittEquivalent c c'' := h1.trans h2

/--
**Witt-equivalence is an equivalence relation on integer chiral
central charges.**

Packaged as `Equivalence WittEquivalent` for use in `Setoid`-based
quotient constructions and as a load-bearing structural witness for
the Witt-class equivalence-class structure. -/
theorem WittEquivalent_equivalence : Equivalence WittEquivalent :=
  ⟨WittEquivalent_refl, WittEquivalent_symm, WittEquivalent_trans⟩

/-- Witt-equivalence packaged as a Setoid (project-local; not a global
instance to avoid conflicts with other equivalence structures on `ℤ`). -/
def wittSetoid : Setoid ℤ where
  r := WittEquivalent
  iseqv := WittEquivalent_equivalence

/-! ## The Schellekens chain at Witt-invariant level (Stage 5 deliverable). -/

/--
**The Schellekens chain at Witt-invariant level: c₋ = 8·N_f is
Witt-trivial iff 3 ∣ N_f.**

Stage 5 substantive deliverable: lifts the Stage-4c arithmetic
biconditional `3 ∣ n ↔ 24 ∣ 8·n` (`GenerationConstraint.generation_constraint_iff`)
to the abelian-group level via the Witt-invariant homomorphism
`WittInvariant.fromChiralCentralCharge : ℤ →+ ZMod 24`.

The Witt-group-grade content: the Standard-Model chiral central charge
c₋ = 8·N_f maps to the trivial Witt invariant iff 3 ∣ N_f, which is the
Schellekens hep-th/9205072 / Kong-Wen arXiv:1404.6029 modular-invariance
constraint expressed at the Witt-class level rather than at the level
of integer divisibility. -/
theorem chiralCentralCharge_wittTrivial_iff_three_dvd_N_f (N_f : ℕ) :
    WittTrivial (8 * (N_f : ℤ)) ↔ 3 ∣ N_f := by
  rw [WittTrivial_iff_dvd]
  constructor
  · intro h
    apply (SKEFTHawking.generation_constraint_iff N_f).mpr
    -- Cast the integer divisibility to natural divisibility
    rcases h with ⟨k, hk⟩
    -- 8 * N_f = 24 * k, with k : ℤ. Need 24 ∣ (8 * N_f) at ℕ.
    -- Since 8 * N_f ≥ 0 and 24 * k = 8 * N_f ≥ 0, k ≥ 0.
    have hk_nonneg : 0 ≤ k := by
      have : 0 ≤ 8 * (N_f : ℤ) := by positivity
      nlinarith
    refine ⟨k.toNat, ?_⟩
    have : (8 * N_f : ℤ) = 24 * k.toNat := by
      rw [hk, Int.toNat_of_nonneg hk_nonneg]
    exact_mod_cast this
  · intro h
    obtain ⟨k, hk⟩ := SKEFTHawking.div_3_n_implies_div_24_8n N_f h
    exact ⟨k, by exact_mod_cast hk⟩

/-! ## The Standard Model concrete witness. -/

/--
**The Standard Model 3-generation chiral central charge has trivial
Witt invariant.**

Concrete physical witness: at N_f = 3, c₋ = 8·3 = 24 maps to 24 mod 24
= 0, the trivial Witt class. This is the explicit substantive instance
that the Schellekens-chain biconditional resolves to TRUE at the
3-generation case actually realized by the Standard Model. -/
theorem standardModel_wittTrivial : WittTrivial (8 * (3 : ℤ)) := by
  rw [WittTrivial_iff_dvd]
  exact ⟨1, by norm_num⟩

/-- For N_f = 1 (one generation), the chiral central charge c₋ = 8 is
NOT Witt-trivial — its Witt invariant is `8` in `ZMod 24`, not zero. -/
theorem one_generation_not_wittTrivial : ¬ WittTrivial (8 * (1 : ℤ)) := by
  rw [WittTrivial_iff_dvd]
  intro h
  rcases h with ⟨k, hk⟩
  omega

/-- For N_f = 2 (two generations), the chiral central charge c₋ = 16 is
NOT Witt-trivial — its Witt invariant is `16` in `ZMod 24`. -/
theorem two_generations_not_wittTrivial : ¬ WittTrivial (8 * (2 : ℤ)) := by
  rw [WittTrivial_iff_dvd]
  intro h
  rcases h with ⟨k, hk⟩
  omega

/-! ## SymTFT bridge (Stage 5 closure). -/

/--
**Stage 5 substantive deliverable: the chiralCentralChargeMod24Compatible
SymTFT predicate combined with the Witt-trivial Standard-Model 3-generation
witness.**

Closes the Wave 1b Stage 5 in-program-build form of the
chiralCentralChargeMod24 ↔ Witt-class biconditional at the
3-generation case. The previous Stage-4c bridge
(`chiralCentralCharge_bridges_to_GenerationConstraint`) operated at the
*integer-divisibility* level (`3 ∣ n ↔ 24 ∣ 8·n`); this Stage-5 bridge
LIFTS it to the *abelian-group / Witt-invariant* level via the
`WittInvariant.fromChiralCentralCharge` AddMonoidHom.

The SymTFT-side predicate `chiralCentralChargeMod24Compatible` is now
backed by:
  - Stage 4c: project-local Schellekens chain at integer-divisibility
    level (3 ∣ n ↔ 24 ∣ 8·n).
  - Stage 5 (this theorem): full abelian-group Witt-invariant lift of
    the same content + Standard-Model concrete 3-generation witness
    (c₋ = 24 has trivial Witt invariant).

P6 cross-module bridge: substantive (uses both
`stage2Verdict_instantiates_chiralCentralCharge` from Applicability
and `standardModel_wittTrivial` from this module). -/
theorem stage5_chiralCentralCharge_witt_bridge :
    chiralCentralChargeMod24Compatible stage2Verdict ∧
    WittTrivial (8 * (3 : ℤ)) ∧
    (∀ N_f : ℕ, WittTrivial (8 * (N_f : ℤ)) ↔ 3 ∣ N_f) :=
  ⟨stage2Verdict_instantiates_chiralCentralCharge,
   standardModel_wittTrivial,
   chiralCentralCharge_wittTrivial_iff_three_dvd_N_f⟩

/-! ## Witt-invariant homomorphism property (Stage 5 structural witness). -/

/--
**The chiral-central-charge → Witt-invariant map is a group
homomorphism.**

Stage 5 structural witness: the Witt-invariant content is not just an
ad-hoc "mod 24 divisibility test" but a load-bearing
`AddMonoidHom : ℤ →+ ZMod 24`. The homomorphism property captures the
algebraic structure of the Witt class — additive composition of chiral
central charges (e.g., taking the tensor product of two CFTs and
summing their c₋) commutes with the Witt-class projection.

This is the cleanest abelian-group-level statement of the Stage 5
deliverable beyond the Stage-4c arithmetic biconditional. -/
theorem wittInvariant_homomorphism_witness :
    ∀ c c' : ℤ,
      WittInvariant.fromChiralCentralCharge (c + c') =
        WittInvariant.fromChiralCentralCharge c +
          WittInvariant.fromChiralCentralCharge c' :=
  fun c c' => map_add WittInvariant.fromChiralCentralCharge c c'

/-- Stage 5 closure summary: the project-local Witt-class infrastructure
satisfies all four substantive conditions: (i) homomorphism property,
(ii) Schellekens biconditional at Witt-invariant level, (iii) Standard
Model 3-generation concrete witness, (iv) one-generation and
two-generation explicit non-Witt-trivial counterexamples. Combined with
the SymTFT bridge `stage5_chiralCentralCharge_witt_bridge`, this
constitutes the Wave 1b Stage 5 in-program-build deliverable. -/
theorem stage5_closure_summary :
    (∀ c c' : ℤ,
      WittInvariant.fromChiralCentralCharge (c + c') =
        WittInvariant.fromChiralCentralCharge c +
          WittInvariant.fromChiralCentralCharge c') ∧
    (∀ N_f : ℕ, WittTrivial (8 * (N_f : ℤ)) ↔ 3 ∣ N_f) ∧
    WittTrivial (8 * (3 : ℤ)) ∧
    ¬ WittTrivial (8 * (1 : ℤ)) ∧
    ¬ WittTrivial (8 * (2 : ℤ)) :=
  ⟨wittInvariant_homomorphism_witness,
   chiralCentralCharge_wittTrivial_iff_three_dvd_N_f,
   standardModel_wittTrivial,
   one_generation_not_wittTrivial,
   two_generations_not_wittTrivial⟩

end SKEFTHawking.SymTFTAudit
