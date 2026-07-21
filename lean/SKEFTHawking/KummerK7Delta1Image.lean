/-
# Phase 5q.H — K7 residual (b): the δ₁-image parity cut — `im δ₁ ⊆ {Σ = 0}` in `(ℤ/2)¹⁶`

The first exact row of the δ₁-image computation, assembled from the deck functional
(`KummerQuotientDeckFunctional`), the seam single-copy evaluation
(`SingularFiniteProdSingleInt`), and the unconditional window (`KummerK7Delta1Window`):

* **The 16 seam generators identified** (`interEquiv_symm_single`, `qThickEquiv_incl_single`):
  under `H₁(collar;ℤ) ≅ (ℤ/2)¹⁶` the `c`-th basis class is the `c`-th seam `ℝP³` generator, and
  its image in `H₁(qThick) ≅ H₁(Q;ℤ)` is `(qBdryMap c)_*[gen]` — the weld glue
  (`weldMk_seam`) turns the collar retraction into the Q-side seam boundary map.
* **The deck row** (`deck_row`): for EVERY `w ∈ H₁(collar;ℤ)`, the coordinate sum of
  `interH1EquivInt w` equals the deck value of its `qThick`-image — because each of the 16 seam
  loops is deck-odd (`qDeck_qBdryMap`).
* **THE PARITY CUT** (`delta1_image_parity`): `im δ₁ ⊆ {v ∈ (ℤ/2)¹⁶ : ∑ v_c = 0}` — a class in
  the δ₁-image dies in `H₁(qThick)`, so its deck value — its coordinate sum — vanishes. Hence
  (`cokerSigma2Embed_parity`, `torsionEmbed_parity`, `card_cokerSigma2_le`,
  `card_torsion_le`): `coker Σ₂` and `Torsion H₂(K3;ℤ)` embed in the parity-zero hyperplane —
  order ≤ `2¹⁵`.

The remaining rows of the δ₁-image matrix (the four ℤ/2-translation functionals of
`H₁(Q) ≅ (ℤ/2)⁵`, cutting `2¹⁵ → 2¹¹`, and the SUFFICIENCY bound `2¹¹ ≤ |im δ₁|` via explicit
bounding 2-chains) are the sharp residual toward the exact `H₂(K3;ℤ)` computation.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerK7Delta1Window
import SKEFTHawking.KummerQuotientDeckFunctional
import SKEFTHawking.SingularFiniteProdSingleInt

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt Homology.mapInt_comp)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (subIncl ambIncl)
open SKEFTHawking.KummerK7Opener (KummerK3top seamHomologyEquivInt seamHomeoCM seamHomeo
  seamParam continuous_seamParam)
open SKEFTHawking.KummerWeld (EIndex eImage qImage seam weldMk weldMk_seam qBdryMap)
open SKEFTHawking.KummerResolutionPiece (RP3)
open SKEFTHawking.KummerRP3Covering (RP3top)
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerK7MVAssembly
open SKEFTHawking.SingularFiniteProdSingleInt (eInclC eIndexProdHnEquivInt_mapInt_single
  homologyCongrInt_apply)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (eIndexProdHnEquivInt homologyCongrInt)
open SKEFTHawking.KummerQuotientDeckFunctional (qDeck qDeck_qBdryMap qBdryMapC genRP3Class)
open SKEFTHawking.KummerRP3HomologySolve (rp3H1EquivZMod2)
open SKEFTHawking.KummerRP3H1Pin (rp3H1_generator_pin)
open SKEFTHawking.KummerK7Delta1Window

namespace SKEFTHawking.KummerK7Delta1Image

/-- Classical decidable equality on the exceptional index (the fixed points live on the real
torus, so equality is classical); scoped to the δ₁-image analysis. -/
noncomputable scoped instance : DecidableEq EIndex := Classical.decEq EIndex

noncomputable section

/-! ## §1. The seam generators of `H₁(collar;ℤ)`, identified -/

/-- The pinned `ℝP³` generator hits `1` under the banked `H₁(ℝP³;ℤ) ≅ ℤ/2`. -/
theorem rp3H1Equiv_genRP3Class : rp3H1EquivZMod2 genRP3Class = 1 := rp3H1_generator_pin

/-- **The collar equivalence at a single seam**: the inverse of
`H₁(collar) ≅ ⊕₁₆ H₁(ℝP³)` carries `Pi.single c y` to the `c`-th seam pushforward. -/
theorem interEquiv_symm_single (c : EIndex) (y : Homology (TopCat.of RP3) 1) :
    (interHnEquivInt 0).symm (Pi.single c y)
      = Homology.mapInt seamInclC 1 (Homology.mapInt seamHomeoCM 1
          (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
            (eInclC c) 1 y)) := by
  rw [LinearEquiv.symm_apply_eq, interHnEquivInt, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply]
  have e1 : (LinearEquiv.ofBijective (Homology.mapInt seamInclC 1)
      (seamIncl_mapInt_bijective 0)).symm
        (Homology.mapInt seamInclC 1 (Homology.mapInt seamHomeoCM 1
          (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
            (eInclC c) 1 y)))
      = Homology.mapInt seamHomeoCM 1
          (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
            (eInclC c) 1 y) := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  rw [e1]
  have e2 : (seamHomologyEquivInt 1).symm
      (Homology.mapInt seamHomeoCM 1
        (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
          (eInclC c) 1 y))
      = Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
          (eInclC c) 1 y := by
    rw [LinearEquiv.symm_apply_eq, seamHomologyEquivInt, LinearEquiv.ofBijective_apply]
  rw [e2]
  exact (eIndexProdHnEquivInt_mapInt_single (0 + 1) c y).symm

/-! ## §2. The weld square: collar seam ↦ Q-side seam boundary -/

/-- The `c`-th seam parametrised into the `Q`-piece of the weld. -/
def seamToQImageC (c : EIndex) : C(RP3top, ↑(sub (X := KummerK3top) qImage)) :=
  ⟨fun r => ⟨seamParam (c, r), seam_subset_qImage
      (by rw [← SKEFTHawking.KummerK7Opener.range_seamParam]; exact Set.mem_range_self (c, r))⟩,
    Continuous.subtype_mk
      (continuous_seamParam.comp (continuous_const.prodMk continuous_id)) _⟩

/-- **The collar composite lands as `qInclC ∘ seamToQImageC`** — the seam sits inside the
`Q`-piece. -/
theorem incl_comp_seam_eq (c : EIndex) :
    (((subIncl (X := KummerK3top)
        (Set.inter_subset_left (s := qThick) (t := eImage))).comp
      seamInclC).comp seamHomeoCM).comp (eInclC c)
      = qInclC.comp (seamToQImageC c) :=
  ContinuousMap.ext fun _ => Subtype.ext rfl

/-- **The weld glue square**: undoing the `Q`-piece identification carries the parametrised seam
to the Q-side seam boundary map `qBdryMap c` (the `weldMk_seam` relation). -/
theorem qImageHomeo_symm_comp_seam (c : EIndex) :
    (⟨qImageHomeo.symm, qImageHomeo.symm.continuous⟩ :
        C(↑(sub (X := KummerK3top) qImage), FreeQuotient)).comp (seamToQImageC c)
      = qBdryMapC c := by
  refine ContinuousMap.ext fun r => ?_
  show qImageHomeo.symm ((seamToQImageC c) r) = qBdryMap c r
  rw [Homeomorph.symm_apply_eq]
  show (seamToQImageC c) r = qImageHomeo (qBdryMap c r)
  exact Subtype.ext (weldMk_seam c r).symm

/-- **The `qThick`-image of the `c`-th seam generator is `(qBdryMap c)_*[gen]`** — the collar
class transported through the thickening retraction and the `Q`-piece identification. -/
theorem qThickEquiv_incl_single (c : EIndex) :
    (qThickHnEquivInt 0) (Homology.mapInt (subIncl (X := KummerK3top)
        (Set.inter_subset_left (s := qThick) (t := eImage))) 1
        ((interHnEquivInt 0).symm (Pi.single c genRP3Class)))
      = Homology.mapInt (X := RP3top) (Y := TopCat.of FreeQuotient)
          (qBdryMapC c) 1 genRP3Class := by
  rw [interEquiv_symm_single]
  have h1 : Homology.mapInt (subIncl (X := KummerK3top)
      (Set.inter_subset_left (s := qThick) (t := eImage))) 1
        (Homology.mapInt seamInclC 1 (Homology.mapInt seamHomeoCM 1
          (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
            (eInclC c) 1 genRP3Class)))
      = Homology.mapInt qInclC 1
          (Homology.mapInt (seamToQImageC c) 1 genRP3Class) := by
    rw [← LinearMap.comp_apply, ← Homology.mapInt_comp, ← LinearMap.comp_apply,
      ← Homology.mapInt_comp, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
      incl_comp_seam_eq]
    exact LinearMap.congr_fun (Homology.mapInt_comp qInclC (seamToQImageC c) 1) genRP3Class
  rw [h1, qThickHnEquivInt, LinearEquiv.trans_apply]
  have h2 : (LinearEquiv.ofBijective (Homology.mapInt qInclC 1)
      (qIncl_mapInt_bijective 0)).symm
        (Homology.mapInt qInclC 1 (Homology.mapInt (seamToQImageC c) 1 genRP3Class))
      = Homology.mapInt (seamToQImageC c) 1 genRP3Class := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  rw [h2, homologyCongrInt_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
    qImageHomeo_symm_comp_seam]

/-! ## §3. The deck row -/

/-- **The deck functional transported to `H₁(qThick;ℤ)`.** -/
def qThickDeck : Homology (sub (X := KummerK3top) qThick) 1 →ₗ[ℤ] ZMod 2 :=
  qDeck.comp (qThickHnEquivInt 0).toLinearMap

/-- The `c`-th seam generator has deck value `1` in the thickened `Q`-piece. -/
theorem qThickDeck_incl_single (c : EIndex) :
    qThickDeck (Homology.mapInt (subIncl (X := KummerK3top)
        (Set.inter_subset_left (s := qThick) (t := eImage))) 1
        ((interHnEquivInt 0).symm (Pi.single c genRP3Class))) = 1 := by
  show qDeck ((qThickHnEquivInt 0) (Homology.mapInt (subIncl (X := KummerK3top)
      (Set.inter_subset_left (s := qThick) (t := eImage))) 1
      ((interHnEquivInt 0).symm (Pi.single c genRP3Class)))) = 1
  rw [qThickEquiv_incl_single]
  exact qDeck_qBdryMap c

/-- ZMod-2 dichotomy. -/
theorem zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

/-- **THE DECK ROW of the δ₁-image matrix**: for every collar class, the coordinate sum under
`H₁(collar;ℤ) ≅ (ℤ/2)¹⁶` is the deck value of its `qThick`-image. All 16 seam loops are
deck-odd, so the total parity is exactly what survives into `H₁(Q;ℤ)`'s deck quotient. -/
theorem deck_row (w : Homology (sub (X := KummerK3top) (qThick ∩ eImage)) 1) :
    (∑ c, interH1EquivInt w c)
      = qThickDeck (Homology.mapInt (subIncl (X := KummerK3top)
          (Set.inter_subset_left (s := qThick) (t := eImage))) 1 w) := by
  set u : EIndex → Homology (TopCat.of RP3) 1 := interHnEquivInt 0 w with hu
  have hw : w = (interHnEquivInt 0).symm (∑ c, Pi.single c (u c)) := by
    rw [Finset.univ_sum_single u, hu, LinearEquiv.symm_apply_apply]
  have hL : ∀ c, interH1EquivInt w c = rp3H1EquivZMod2 (u c) := by
    intro c
    rw [interH1EquivInt, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
  calc (∑ c, interH1EquivInt w c)
      = ∑ c, rp3H1EquivZMod2 (u c) := Finset.sum_congr rfl (fun c _ => hL c)
    _ = ∑ c, qThickDeck (Homology.mapInt (subIncl (X := KummerK3top)
          (Set.inter_subset_left (s := qThick) (t := eImage))) 1
          ((interHnEquivInt 0).symm (Pi.single c (u c)))) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rcases zmod2_cases (rp3H1EquivZMod2 (u c)) with h | h
        · have hu0 : u c = 0 := by
            rwa [LinearEquiv.map_eq_zero_iff] at h
          rw [h, hu0, Pi.single_zero, map_zero, map_zero, map_zero]
        · have hgen : u c = genRP3Class := by
            apply rp3H1EquivZMod2.injective
            rw [h, rp3H1Equiv_genRP3Class]
          rw [h, hgen, qThickDeck_incl_single]
    _ = qThickDeck (Homology.mapInt (subIncl (X := KummerK3top)
          (Set.inter_subset_left (s := qThick) (t := eImage))) 1 w) := by
        rw [hw, map_sum, map_sum, map_sum]

/-! ## §4. THE PARITY CUT: `im δ₁ ⊆ {Σ = 0}` -/

/-- **The δ₁-image parity theorem**: every class in the image of the MV connecting map
`δ₁ : H₂(K3;ℤ) → H₁(collar;ℤ) ≅ (ℤ/2)¹⁶` has coordinate sum zero — the first exact cut of
the δ₁-image below the full `(ℤ/2)¹⁶`. -/
theorem delta1_image_parity {w : Homology (sub (X := KummerK3top) (qThick ∩ eImage)) 1}
    (hw : w ∈ LinearMap.range (k7Delta 1)) :
    (∑ c, interH1EquivInt w c) = 0 := by
  rw [deck_row w, (mem_range_k7Delta_one_iff w).mp hw, map_zero]

/-- **coker Σ₂ lands in the parity-zero hyperplane** of `(ℤ/2)¹⁶`. -/
theorem cokerSigma2Embed_parity (x : Homology KummerK3top 2 ⧸ pieceBlock) :
    (∑ c, cokerSigma2Embed x c) = 0 :=
  delta1_image_parity (cokerSigma2Equiv x).2

/-- **The torsion of `H₂(K3;ℤ)` lands in the parity-zero hyperplane** of `(ℤ/2)¹⁶`. -/
theorem torsionEmbed_parity (t : ↥(Submodule.torsion ℤ (Homology KummerK3top 2))) :
    (∑ c, torsionEmbed t c) = 0 :=
  cokerSigma2Embed_parity _

/-! ## §5. The quantitative cut: `|coker Σ₂| ≤ 2¹⁵`, `|Torsion H₂| ≤ 2¹⁵` -/

/-- The coordinate-sum functional on `(ℤ/2)¹⁶`, as an additive monoid hom. -/
def sumF : (EIndex → ZMod 2) →+ ZMod 2 :=
  { toFun := fun v => ∑ c, v c
    map_zero' := by simp
    map_add' := fun v w => by
      simp [Finset.sum_add_distrib] }

theorem sumF_single_one (c : EIndex) : sumF (Pi.single c 1) = 1 := by
  show (∑ d, Pi.single c (1 : ZMod 2) d) = 1
  rw [Finset.sum_eq_single c (fun d _ hd => Pi.single_eq_of_ne hd 1) (by simp),
    Pi.single_eq_same]

theorem sumF_surjective : Function.Surjective sumF := by
  haveI : Nonempty EIndex :=
    Fintype.card_pos_iff.mp (by rw [SKEFTHawking.KummerWeld.eIndex_card]; omega)
  intro t
  rcases zmod2_cases t with rfl | rfl
  · exact ⟨0, map_zero sumF⟩
  · exact ⟨Pi.single (Classical.arbitrary EIndex) 1, sumF_single_one _⟩

/-- `|ker Σ| = 2¹⁵` — the parity-zero hyperplane has index 2 in `(ℤ/2)¹⁶`. -/
theorem card_ker_sumF : Nat.card ↥sumF.ker = 2 ^ 15 := by
  have h1 : Nat.card (EIndex → ZMod 2) = 2 ^ 16 := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card,
      Nat.card_eq_fintype_card (α := EIndex), SKEFTHawking.KummerWeld.eIndex_card]
  have h2 := Nat.card_congr
    (QuotientAddGroup.quotientKerEquivOfSurjective sumF sumF_surjective).toEquiv
  have h3 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (sumF.ker)
  rw [h1, h2] at h3
  have h4 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [h4] at h3
  omega

/-- **`|coker Σ₂| ≤ 2¹⁵`** — the parity cut, quantitatively: the MV cokernel of the rank-22
piece block has order at most `2¹⁵` (down from the a-priori `2¹⁶` window). -/
theorem card_cokerSigma2_le :
    Nat.card (Homology KummerK3top 2 ⧸ pieceBlock) ≤ 2 ^ 15 := by
  have hmap : Function.Injective (fun x : Homology KummerK3top 2 ⧸ pieceBlock =>
      (⟨cokerSigma2Embed x, cokerSigma2Embed_parity x⟩ : ↥sumF.ker)) := by
    intro a b hab
    exact cokerSigma2Embed_injective (congrArg Subtype.val hab)
  have := Nat.card_le_card_of_injective _ hmap
  rwa [card_ker_sumF] at this

/-- **`|Torsion H₂(K3;ℤ)| ≤ 2¹⁵`** — the torsion subgroup obeys the same parity cut. -/
theorem card_torsion_le :
    Nat.card ↥(Submodule.torsion ℤ (Homology KummerK3top 2)) ≤ 2 ^ 15 := by
  have hmap : Function.Injective (fun t : ↥(Submodule.torsion ℤ (Homology KummerK3top 2)) =>
      (⟨torsionEmbed t, torsionEmbed_parity t⟩ : ↥sumF.ker)) := by
    intro a b hab
    exact torsionEmbed_injective (congrArg Subtype.val hab)
  have := Nat.card_le_card_of_injective _ hmap
  rwa [card_ker_sumF] at this

end

end SKEFTHawking.KummerK7Delta1Image
