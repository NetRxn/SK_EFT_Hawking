/-
# Phase 5q.H (W-A addClosure, layer 4 core) — the disjoint-union Wu-class naturality

The conceptual heart of the `⊔`-closure `addClosure`: given a Lefschetz–Wu datum `Pu` on the union
pair `(A ⊔ B, S₁ ⊔ S₂)` and data `P₁`, `P₂` on the summand pairs, all **block-compatible** across the
two inclusions (the union's cup/`Sq`/`μ` restrict componentwise — `WuBlockHyp`), the union's Wu class
restricts to the summands' Wu classes: `inl*(v_k(Pu)) = v_k(P₁)`, `inr*(v_k(Pu)) = v_k(P₂)`.

The block hypotheses `cup_inl`/`cup_inr`/`sq_inl`/`sq_inr` are exactly the layer-2 naturality of the
substrate `relCupH14`/`relCupH23`/`relSq1`/`relSq2` (discharged by `SingularRelativeCupSqNaturality`
once `Pu`/`Pᵢ` are `ofRelFund`-assembled), and `mu` is the μ-block-sum of the disjoint-union relative
fundamental class (the one deep residual). From these, the Wu naturality follows purely from the
perfect-pairing characterisation of the Wu class (`pairing_bijective`) and the block sections of the
relative splitting (`relSectionInl`/`relSectionInr`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomologyDisjointSum
import SKEFTHawking.PoincareLefschetzWu5

namespace SKEFTHawking.PoincareLefschetzWuBlock

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.SingularRelativeCohomologyDisjointSum
open SKEFTHawking.PoincareLefschetzWu5

variable {A B : TopCat} {S₁ : Set ↑A} {S₂ : Set ↑B} {k nk : ℕ}

/-! ## §1. `pairing`/`wuFunctional` evaluation rules -/

theorem pairing_apply {X : TopCat} {S : Set ↑X} {k' nk' n' : ℕ} (P : LefschetzWuDatum X S k' nk' n')
    (v : Cohomology X k') (y : RelativeCohomology S nk') :
    pairing P v y = P.mu (P.cup v y) := rfl

theorem wuFunctional_apply {X : TopCat} {S : Set ↑X} {k' nk' n' : ℕ}
    (P : LefschetzWuDatum X S k' nk' n') (y : RelativeCohomology S nk') :
    wuFunctional P y = P.mu (P.sqOp y) := rfl

/-! ## §2. The block-compatibility hypotheses -/

/-- **Block compatibility** of a union Lefschetz–Wu datum `Pu` with the summands' data `P₁`, `P₂`
across the two inclusions: the union's cup/`Sq`/`μ` all restrict componentwise. -/
structure WuBlockHyp
    (Pu : LefschetzWuDatum (sumSpace A B) (sumSet A B S₁ S₂) k nk 5)
    (P₁ : LefschetzWuDatum A S₁ k nk 5) (P₂ : LefschetzWuDatum B S₂ k nk 5) : Prop where
  cup_inl : ∀ (v : Cohomology (sumSpace A B) k) (y : RelativeCohomology (sumSet A B S₁ S₂) nk),
    relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) 5 (Pu.cup v y)
      = P₁.cup (cohomologyPullback (inlMap A B) k v)
          (relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) nk y)
  cup_inr : ∀ (v : Cohomology (sumSpace A B) k) (y : RelativeCohomology (sumSet A B S₁ S₂) nk),
    relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) 5 (Pu.cup v y)
      = P₂.cup (cohomologyPullback (inrMap A B) k v)
          (relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) nk y)
  mu : ∀ (z : RelativeCohomology (sumSet A B S₁ S₂) 5),
    Pu.mu z = P₁.mu (relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) 5 z)
            + P₂.mu (relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) 5 z)
  sq_inl : ∀ (y : RelativeCohomology (sumSet A B S₁ S₂) nk),
    relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) 5 (Pu.sqOp y)
      = P₁.sqOp (relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) nk y)
  sq_inr : ∀ (y : RelativeCohomology (sumSet A B S₁ S₂) nk),
    relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) 5 (Pu.sqOp y)
      = P₂.sqOp (relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) nk y)

variable {Pu : LefschetzWuDatum (sumSpace A B) (sumSet A B S₁ S₂) k nk 5}
  {P₁ : LefschetzWuDatum A S₁ k nk 5} {P₂ : LefschetzWuDatum B S₂ k nk 5}

/-! ## §3. The block identities for `pairing` and `wuFunctional` -/

/-- **The block pairing identity** (★): the union Lefschetz pairing decomposes as the sum of the
summand pairings on the restricted arguments. -/
theorem pairing_block (H : WuBlockHyp Pu P₁ P₂)
    (v : Cohomology (sumSpace A B) k) (y : RelativeCohomology (sumSet A B S₁ S₂) nk) :
    pairing Pu v y
      = pairing P₁ (cohomologyPullback (inlMap A B) k v)
          (relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) nk y)
        + pairing P₂ (cohomologyPullback (inrMap A B) k v)
          (relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) nk y) := by
  rw [pairing_apply, H.mu (Pu.cup v y), H.cup_inl v y, H.cup_inr v y, pairing_apply, pairing_apply]

/-- **The block Wu-functional identity** (★★): the union Wu functional decomposes as the sum of the
summand Wu functionals on the restricted argument. -/
theorem wuFunctional_block (H : WuBlockHyp Pu P₁ P₂)
    (y : RelativeCohomology (sumSet A B S₁ S₂) nk) :
    wuFunctional Pu y
      = wuFunctional P₁ (relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) nk y)
        + wuFunctional P₂ (relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) nk y) := by
  rw [wuFunctional_apply, H.mu (Pu.sqOp y), H.sq_inl y, H.sq_inr y, wuFunctional_apply,
    wuFunctional_apply]

/-! ## §3b. Block non-degeneracy -/

/-- **Block non-degeneracy**: the union Lefschetz pairing is injective, from the summands' Lefschetz
non-degeneracy and the absolute disjoint-union splitting injectivity. This is the `nondeg` field of the
`ofRelFund`-assembled union datum (block-diagonal perfect pairing). -/
theorem pairing_injective_block (H : WuBlockHyp Pu P₁ P₂)
    (h₁ : Function.Injective ⇑(pairing P₁)) (h₂ : Function.Injective ⇑(pairing P₂)) :
    Function.Injective ⇑(pairing Pu) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  rw [Submodule.mem_bot]
  have hzero : ∀ w, pairing Pu v w = 0 := fun w => by
    rw [show pairing Pu v = 0 from hv]; rfl
  have hl : cohomologyPullback (inlMap A B) k v = 0 := by
    apply h₁
    rw [map_zero]
    apply LinearMap.ext
    intro y₁
    have hb := pairing_block H v (relSectionInl A B S₁ S₂ nk y₁)
    rw [relCohomPullback_inl_relSectionInl, relCohomPullback_inr_relSectionInl,
      map_zero, add_zero] at hb
    rw [LinearMap.zero_apply, ← hb, hzero]
  have hr : cohomologyPullback (inrMap A B) k v = 0 := by
    apply h₂
    rw [map_zero]
    apply LinearMap.ext
    intro y₂
    have hb := pairing_block H v (relSectionInr A B S₁ S₂ nk y₂)
    rw [relCohomPullback_inl_relSectionInr, relCohomPullback_inr_relSectionInr,
      map_zero, zero_add] at hb
    rw [LinearMap.zero_apply, ← hb, hzero]
  apply restrictPairCohomology_injective A B k
  rw [restrictPairCohomology_apply, map_zero]
  exact Prod.ext hl hr

/-! ## §4. Wu-class naturality -/

/-- **Wu-class naturality, left**: `inl*(v_k(Pu)) = v_k(P₁)`. The union Wu class restricts to the
left summand's Wu class. Uses the perfect-pairing characterisation and the left block section. -/
theorem wuClass_pullback_inl (H : WuBlockHyp Pu P₁ P₂) :
    cohomologyPullback (inlMap A B) k (wuClass Pu) = wuClass P₁ := by
  have key : pairing P₁ (cohomologyPullback (inlMap A B) k (wuClass Pu)) = wuFunctional P₁ := by
    apply LinearMap.ext
    intro y₁
    have hsec_l : relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) nk
        (relSectionInl A B S₁ S₂ nk y₁) = y₁ :=
      relCohomPullback_inl_relSectionInl A B S₁ S₂ nk y₁
    have hsec_r : relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) nk
        (relSectionInl A B S₁ S₂ nk y₁) = 0 :=
      relCohomPullback_inr_relSectionInl A B S₁ S₂ nk y₁
    have hpair := pairing_block H (wuClass Pu) (relSectionInl A B S₁ S₂ nk y₁)
    rw [hsec_l, hsec_r, map_zero, add_zero] at hpair
    have hwuf := wuFunctional_block H (relSectionInl A B S₁ S₂ nk y₁)
    rw [hsec_l, hsec_r, map_zero, add_zero] at hwuf
    have hrel : pairing Pu (wuClass Pu) (relSectionInl A B S₁ S₂ nk y₁)
        = wuFunctional Pu (relSectionInl A B S₁ S₂ nk y₁) := by
      have h := wu_relation Pu (relSectionInl A B S₁ S₂ nk y₁)
      rw [pairing_apply, wuFunctional_apply]; exact h
    rw [hpair] at hrel
    rw [hrel, hwuf]
  calc cohomologyPullback (inlMap A B) k (wuClass Pu)
      = (Equiv.ofBijective _ (pairing_bijective P₁)).symm
          ((Equiv.ofBijective _ (pairing_bijective P₁))
            (cohomologyPullback (inlMap A B) k (wuClass Pu))) :=
        ((Equiv.ofBijective _ (pairing_bijective P₁)).symm_apply_apply _).symm
    _ = (Equiv.ofBijective _ (pairing_bijective P₁)).symm (wuFunctional P₁) := congrArg _ key
    _ = wuClass P₁ := rfl

/-- **Wu-class naturality, right**: `inr*(v_k(Pu)) = v_k(P₂)`. -/
theorem wuClass_pullback_inr (H : WuBlockHyp Pu P₁ P₂) :
    cohomologyPullback (inrMap A B) k (wuClass Pu) = wuClass P₂ := by
  have key : pairing P₂ (cohomologyPullback (inrMap A B) k (wuClass Pu)) = wuFunctional P₂ := by
    apply LinearMap.ext
    intro y₂
    have hsec_l : relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) nk
        (relSectionInr A B S₁ S₂ nk y₂) = 0 :=
      relCohomPullback_inl_relSectionInr A B S₁ S₂ nk y₂
    have hsec_r : relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) nk
        (relSectionInr A B S₁ S₂ nk y₂) = y₂ :=
      relCohomPullback_inr_relSectionInr A B S₁ S₂ nk y₂
    have hpair := pairing_block H (wuClass Pu) (relSectionInr A B S₁ S₂ nk y₂)
    rw [hsec_l, hsec_r, map_zero, zero_add] at hpair
    have hwuf := wuFunctional_block H (relSectionInr A B S₁ S₂ nk y₂)
    rw [hsec_l, hsec_r, map_zero, zero_add] at hwuf
    have hrel : pairing Pu (wuClass Pu) (relSectionInr A B S₁ S₂ nk y₂)
        = wuFunctional Pu (relSectionInr A B S₁ S₂ nk y₂) := by
      have h := wu_relation Pu (relSectionInr A B S₁ S₂ nk y₂)
      rw [pairing_apply, wuFunctional_apply]; exact h
    rw [hpair] at hrel
    rw [hrel, hwuf]
  calc cohomologyPullback (inrMap A B) k (wuClass Pu)
      = (Equiv.ofBijective _ (pairing_bijective P₂)).symm
          ((Equiv.ofBijective _ (pairing_bijective P₂))
            (cohomologyPullback (inrMap A B) k (wuClass Pu))) :=
        ((Equiv.ofBijective _ (pairing_bijective P₂)).symm_apply_apply _).symm
    _ = (Equiv.ofBijective _ (pairing_bijective P₂)).symm (wuFunctional P₂) := congrArg _ key
    _ = wuClass P₂ := rfl

/-! ## §5. The union W-admissibility `w₂(Wu) = 0` from the summands' -/

/-- **Disjoint-union W-admissibility**: if the union's `(1,4)` and `(2,3)` Lefschetz–Wu data are
block-compatible with the summands' and each summand is W-admissible (`w₂ = 0`), the union is too.
Proven by the absolute disjoint-union splitting injectivity (`restrictPairCohomology_injective`):
`w₂(Wu) = 0 ⟺ v₂(Wu) = v₁(Wu)²` in `H²(Wu)`, and both restrict componentwise to the summands'
`v₂ = v₁²` (Wu-class naturality + `cohomologyPullback_cupH`), each of which is the summand's `w₂ = 0`. -/
theorem wuW2_block_eq_zero
    {Pu14 : LefschetzWuDatum (sumSpace A B) (sumSet A B S₁ S₂) 1 4 5}
    {Pu23 : LefschetzWuDatum (sumSpace A B) (sumSet A B S₁ S₂) 2 3 5}
    {P14₁ : LefschetzWuDatum A S₁ 1 4 5} {P23₁ : LefschetzWuDatum A S₁ 2 3 5}
    {P14₂ : LefschetzWuDatum B S₂ 1 4 5} {P23₂ : LefschetzWuDatum B S₂ 2 3 5}
    (H14 : WuBlockHyp Pu14 P14₁ P14₂) (H23 : WuBlockHyp Pu23 P23₁ P23₂)
    (hwu₁ : wuW2 P14₁ P23₁ = 0) (hwu₂ : wuW2 P14₂ P23₂ = 0) :
    wuW2 Pu14 Pu23 = 0 := by
  rw [wuW2_eq_zero_iff]
  apply restrictPairCohomology_injective A B 2
  rw [restrictPairCohomology_apply, restrictPairCohomology_apply]
  refine Prod.ext ?_ ?_
  · show cohomologyPullback (inlMap A B) 2 (wuClassW2 Pu23)
      = cohomologyPullback (inlMap A B) 2 (cupH (wuClassW1 Pu14) (wuClassW1 Pu14))
    rw [wuClassW2, wuClass_pullback_inl H23, cohomologyPullback_cupH, wuClassW1,
      wuClass_pullback_inl H14]
    exact (wuW2_eq_zero_iff P14₁ P23₁).mp hwu₁
  · show cohomologyPullback (inrMap A B) 2 (wuClassW2 Pu23)
      = cohomologyPullback (inrMap A B) 2 (cupH (wuClassW1 Pu14) (wuClassW1 Pu14))
    rw [wuClassW2, wuClass_pullback_inr H23, cohomologyPullback_cupH, wuClassW1,
      wuClass_pullback_inr H14]
    exact (wuW2_eq_zero_iff P14₂ P23₂).mp hwu₂

end SKEFTHawking.PoincareLefschetzWuBlock
