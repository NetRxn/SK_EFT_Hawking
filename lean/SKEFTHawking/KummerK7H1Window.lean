/-
# Phase 5q.H — K7 residual (b): the `H₁(K3;ℤ)` window — `Σ₁` surjective, `H₁(K3)` a quotient of `H₁(Q)`

The degree-1 Mayer–Vietoris window of the collar-thickened Kummer weld — the "path-connectedness
bookkeeping" leg of the δ₁/extension analysis:

* **The outer collar is path-connected** (`instPathConnectedOuterE`): every outer point flows to
  the boundary `∂E ≅ ℝP³` (`resFlow`), and the boundary is path-connected.
* **`H₀(collar;ℤ) ≅ ℤ¹⁶`, with the `E`-side `H₀`-leg injective** (`diag0_eImage_injective`): the
  16 collar components inject into the 16 `E`-copy components — per component both sides are
  path-connected and the augmentation is natural.
* **`δ₀ = 0`** (`k7Delta_zero_eq_zero`) hence **`Σ₁` is surjective** (`k7Sum1_surjective`):
  `H₁(qThick) ⊕ H₁(eImage) ↠ H₁(K3;ℤ)`.
* **HEADLINE** (`k7H1_surjective_from_qThick`, `h1K3_surjective_from_Q`): `H₁(eImage) = 0`, so
  every class of `H₁(K3;ℤ)` comes from the thickened `Q`-piece — `H₁(K3;ℤ)` is a quotient of
  `H₁(Q;ℤ)`. This is the degree-1 input of the torsion-freeness residual (`H₁(K3;ℤ) = 0` would
  follow from `H₁(Q)`-kill data; with UCT/PD-style input it kills `Torsion H₂(K3;ℤ)`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerK7Delta1Window
import SKEFTHawking.SingularFiniteProdSingleInt

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt Homology.mapInt_comp
  Homology.mapInt_id)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (subIncl ambIncl)
open SKEFTHawking.SingularMayerVietorisLESInt (mvHomSumInt mvHomDiagInt mvHomDiagInt_apply
  mvHomSumInt_apply)
open SKEFTHawking.SingularLineMinusPointInt (augHInt augHInt_naturality)
open SKEFTHawking.SingularH0PathConnectedInt (augHInt_injective_pathConnected)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerWeld (EIndex eImage qImage seam weldMk weldMk_inr_injective
  KummerK3 continuous_weldMk)
open SKEFTHawking.KummerResolutionPiece (RP3 ResE bdryMapRP3 continuous_bdryMapRP3
  boundaryE range_bdryMapRP3_eq_boundaryE)
open SKEFTHawking.KummerWeldFiberFlow (fiberNorm fiberNorm_nonneg continuous_fiberNorm
  fiberNorm_eq_one_iff fiberNorm_bdryMapRP3 resFlow resFlow_one continuous_resFlow
  fiberNorm_resFlow)
open SKEFTHawking.KummerK7MVAssembly
open SKEFTHawking.SingularFiniteProdSingleInt (homologyCongrInt_apply)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (homologyCongrInt eIndexEquivFin
  finProdHnEquivInt)
open SKEFTHawking.SingularFiniteProdSingleInt (finInclC finProdHnEquivInt_mapInt_single)

namespace SKEFTHawking.KummerK7H1Window

/-- Classical decidable equality on the exceptional index; scoped to the `H₁` window analysis. -/
noncomputable scoped instance : DecidableEq EIndex := Classical.decEq EIndex

noncomputable section

/-! ## §1. The outer collar carrier of a single `E`-copy -/

/-- The outer half-collar of the resolution piece: fiber radius `≥ 1/2`. -/
def outerE : Set ResE := {e | 1 / 2 ≤ fiberNorm e}

theorem isClosed_outerE : IsClosed outerE :=
  isClosed_le continuous_const continuous_fiberNorm

instance : CompactSpace ↥outerE :=
  isCompact_iff_compactSpace.mp isClosed_outerE.isCompact

theorem bdry_mem_outerE (r : RP3) : bdryMapRP3 r ∈ outerE := by
  show 1 / 2 ≤ fiberNorm (bdryMapRP3 r)
  rw [fiberNorm_bdryMapRP3]
  norm_num

theorem resFlow_mem_outerE {e : ResE} (he : e ∈ outerE) (t : unitInterval) :
    resFlow (e, t) ∈ outerE := by
  show 1 / 2 ≤ fiberNorm (resFlow (e, t))
  rw [fiberNorm_resFlow]
  refine le_min (by norm_num) ?_
  calc (1 : ℝ) / 2 ≤ fiberNorm e := he
    _ = 1 * fiberNorm e := (one_mul _).symm
    _ ≤ (2 - (t : ℝ)) * fiberNorm e :=
        mul_le_mul_of_nonneg_right (by have := t.2.2; linarith) (fiberNorm_nonneg _)

theorem resFlow_zero_mem_boundary {e : ResE} (he : e ∈ outerE) :
    resFlow (e, 0) ∈ boundaryE := by
  rw [← fiberNorm_eq_one_iff, fiberNorm_resFlow]
  have h1 : (1 : ℝ) ≤ (2 - ((0 : unitInterval) : ℝ)) * fiberNorm e := by
    have h2 : ((0 : unitInterval) : ℝ) = 0 := rfl
    rw [h2, sub_zero]
    have : (1 : ℝ) / 2 ≤ fiberNorm e := he
    linarith
  exact min_eq_left h1

/-! ## §2. The outer collar is path-connected -/

/-- The boundary `ℝP³` into the outer collar. -/
def bdryIntoOuterC : C(RP3, ↥outerE) :=
  ⟨fun r => ⟨bdryMapRP3 r, bdry_mem_outerE r⟩, continuous_bdryMapRP3.subtype_mk _⟩

/-- Every outer point is joined (inside the collar) to a boundary point. -/
theorem joined_to_boundary {e : ResE} (he : e ∈ outerE) :
    ∃ r : RP3, Joined (⟨e, he⟩ : ↥outerE) ⟨bdryMapRP3 r, bdry_mem_outerE r⟩ := by
  obtain ⟨r, hr⟩ : resFlow (e, 0) ∈ Set.range bdryMapRP3 := by
    rw [range_bdryMapRP3_eq_boundaryE]
    exact resFlow_zero_mem_boundary he
  refine ⟨r, ⟨⟨⟨fun s => ⟨resFlow (e, unitInterval.symm s), resFlow_mem_outerE he _⟩, ?_⟩,
    ?_, ?_⟩⟩⟩
  · exact Continuous.subtype_mk
      (continuous_resFlow.comp (continuous_const.prodMk unitInterval.continuous_symm)) _
  · exact Subtype.ext (show resFlow (e, unitInterval.symm 0) = e by
      rw [unitInterval.symm_zero]; exact resFlow_one e)
  · exact Subtype.ext (show resFlow (e, unitInterval.symm 1) = bdryMapRP3 r by
      rw [unitInterval.symm_one]; exact hr.symm)

/-- **The outer collar is path-connected**: flow to the boundary, then move along `ℝP³`. -/
instance instPathConnectedOuterE : PathConnectedSpace ↥outerE := by
  refine ⟨⟨⟨bdryMapRP3 (Classical.arbitrary RP3), bdry_mem_outerE _⟩⟩, ?_⟩
  rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
  obtain ⟨r₁, h₁⟩ := joined_to_boundary he₁
  obtain ⟨r₂, h₂⟩ := joined_to_boundary he₂
  have hmid : Joined (⟨bdryMapRP3 r₁, bdry_mem_outerE r₁⟩ : ↥outerE)
      ⟨bdryMapRP3 r₂, bdry_mem_outerE r₂⟩ :=
    ⟨(PathConnectedSpace.somePath r₁ r₂).map bdryIntoOuterC.continuous⟩
  exact (h₁.trans hmid).trans h₂.symm

/-! ## §3. The collar as 16 outer half-collars -/

/-- The 16-fold outer-collar parametrisation of `eOuter ⊆ K3`. -/
def eOuterParamEquiv : (EIndex × ↥outerE) ≃ ↥eOuter :=
  Equiv.ofBijective
    (fun p => ⟨weldMk (Sum.inr (p.1, p.2.1)), ⟨(p.1, p.2.1), by exact p.2.2, rfl⟩⟩)
    ⟨by
      rintro ⟨c₁, e₁, he₁⟩ ⟨c₂, e₂, he₂⟩ h
      have h1 : ((c₁, e₁) : EIndex × ResE) = (c₂, e₂) :=
        weldMk_inr_injective (congrArg Subtype.val h)
      have hc : c₁ = c₂ := congrArg Prod.fst h1
      have he : e₁ = e₂ := congrArg Prod.snd h1
      subst hc
      exact Prod.ext rfl (Subtype.ext he),
     by
      rintro ⟨x, ⟨c, e⟩, hp, rfl⟩
      exact ⟨(c, ⟨e, by exact hp⟩), rfl⟩⟩

/-- **The 16-fold outer-collar homeomorphism** (continuous bijection, compact to `T2`). -/
def eOuterParamHomeo : (EIndex × ↥outerE) ≃ₜ ↥eOuter :=
  Continuous.homeoOfEquivCompactToT2 (f := eOuterParamEquiv)
    (Continuous.subtype_mk
      (continuous_weldMk.comp (continuous_inr.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))) _)

/-- The collar `qThick ∩ eImage` as the 16 outer half-collars. -/
def interParamHomeo : (EIndex × ↥outerE) ≃ₜ ↥(qThick ∩ eImage : Set KummerK3) :=
  eOuterParamHomeo.trans (Homeomorph.setCongr qThick_inter_eImage.symm)

/-- **`H₀(collar;ℤ) ≅ ℤ¹⁶`-shape**: the 16-fold `H₀` splitting of the collar. -/
def interH0EquivInt :
    Homology (sub (X := KummerK3top) (qThick ∩ eImage)) 0
      ≃ₗ[ℤ] (EIndex → Homology (TopCat.of ↥outerE) 0) :=
  (homologyCongrInt (X := sub (X := KummerK3top) (qThick ∩ eImage))
      (Y := TopCat.of (EIndex × ↥outerE)) interParamHomeo.symm 0).trans
    (eIndexProdHnEquivIntGen (TopCat.of ↥outerE) 0)

/-! ## §4. The generic single-copy evaluation for `eIndexProdHnEquivIntGen` -/

/-- The `c`-th copy inclusion `Y → EIndex × Y`. -/
def genInclC (Y : TopCat) (c : EIndex) : C(↑Y, EIndex × ↑Y) :=
  ⟨fun y => (c, y), continuous_const.prodMk continuous_id⟩

theorem eIndexProdHomeoGen_comp_genInclC (Y : TopCat) (c : EIndex) :
    (⟨eIndexProdHomeoGen Y, (eIndexProdHomeoGen Y).continuous⟩ :
        C(EIndex × ↑Y, Fin 16 × ↑Y)).comp (genInclC Y c)
      = finInclC Y 15 (eIndexEquivFin c) :=
  ContinuousMap.ext fun _ => rfl

/-- **The generic seam single-copy evaluation**: pushing `y ∈ Hₙ(Y;ℤ)` into the `c`-th copy of
`EIndex × Y` and splitting gives `Pi.single c y`. -/
theorem eIndexProdHnEquivIntGen_mapInt_single (Y : TopCat) (n : ℕ) (c : EIndex)
    (y : Homology Y n) :
    eIndexProdHnEquivIntGen Y n
        (Homology.mapInt (X := Y) (Y := TopCat.of (EIndex × ↑Y)) (genInclC Y c) n y)
      = Pi.single c y := by
  rw [eIndexProdHnEquivIntGen, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  have h1 : (homologyCongrInt (X := TopCat.of (EIndex × ↑Y)) (Y := TopCat.of (Fin 16 × ↑Y))
      (eIndexProdHomeoGen Y) n)
        (Homology.mapInt (X := Y) (Y := TopCat.of (EIndex × ↑Y)) (genInclC Y c) n y)
      = Homology.mapInt (finInclC Y 15 (eIndexEquivFin c)) n y := by
    rw [homologyCongrInt_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
      eIndexProdHomeoGen_comp_genInclC]
  rw [h1, finProdHnEquivInt_mapInt_single]
  funext d
  show (Pi.single (eIndexEquivFin c) y : Fin 16 → Homology Y n) (eIndexEquivFin d)
    = (Pi.single c y : EIndex → Homology Y n) d
  rcases eq_or_ne d c with rfl | hne
  · rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (fun h => hne (eIndexEquivFin.injective h)),
      Pi.single_eq_of_ne hne]

/-! ## §5. The `H₀`-leg injectivity: collar components inject into the `E`-copy components -/

/-- The `c`-th outer half-collar inside the collar. -/
def interCopyC (c : EIndex) : C(↥outerE, ↑(sub (X := KummerK3top) (qThick ∩ eImage))) :=
  (⟨interParamHomeo, interParamHomeo.continuous⟩ :
    C(EIndex × ↥outerE, ↑(sub (X := KummerK3top) (qThick ∩ eImage)))).comp
    (genInclC (TopCat.of ↥outerE) c)

/-- The collar-splitting inverse at a single copy. -/
theorem interH0Equiv_symm_single (c : EIndex) (y : Homology (TopCat.of ↥outerE) 0) :
    interH0EquivInt.symm (Pi.single c y) = Homology.mapInt (interCopyC c) 0 y := by
  rw [LinearEquiv.symm_apply_eq, interH0EquivInt, LinearEquiv.trans_apply]
  have h1 : (homologyCongrInt (X := sub (X := KummerK3top) (qThick ∩ eImage))
      (Y := TopCat.of (EIndex × ↥outerE)) interParamHomeo.symm 0)
        (Homology.mapInt (interCopyC c) 0 y)
      = Homology.mapInt (X := TopCat.of ↥outerE) (Y := TopCat.of (EIndex × ↥outerE))
          (genInclC (TopCat.of ↥outerE) c) 0 y := by
    rw [homologyCongrInt_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
    have h2 : (⟨interParamHomeo.symm, interParamHomeo.symm.continuous⟩ :
        C(↑(sub (X := KummerK3top) (qThick ∩ eImage)), EIndex × ↥outerE)).comp (interCopyC c)
        = genInclC (TopCat.of ↥outerE) c :=
      ContinuousMap.ext fun u => interParamHomeo.symm_apply_apply _
    rw [h2]
  rw [h1]
  exact (eIndexProdHnEquivIntGen_mapInt_single (TopCat.of ↥outerE) 0 c y).symm

/-- The outer half-collar into its full `E`-copy fiber. -/
def outerInclResC : C(↥outerE, ResE) := ⟨Subtype.val, continuous_subtype_val⟩

/-- **The `E`-side square**: including the `c`-th half-collar into `eImage` and splitting is the
`c`-th copy of the half-collar inclusion. -/
theorem eImage_incl_copy_square (c : EIndex) :
    ((⟨eImageHomeo.symm, eImageHomeo.symm.continuous⟩ :
        C(↑(sub (X := KummerK3top) eImage), EIndex × ResE)).comp
      (subIncl (X := KummerK3top)
          (Set.inter_subset_right (s := qThick) (t := eImage)))).comp (interCopyC c)
      = (genInclC (TopCat.of ResE) c).comp outerInclResC := by
  refine ContinuousMap.ext fun u => ?_
  show eImageHomeo.symm ((subIncl (X := KummerK3top)
      (Set.inter_subset_right (s := qThick) (t := eImage))) ((interCopyC c) u))
    = (c, (u : ResE))
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext rfl

/-- Per-copy `H₀`-injectivity: the half-collar and the `E`-copy are both path-connected, and the
augmentation is natural. -/
theorem outerIncl_H0_injective : Function.Injective (Homology.mapInt
    (X := TopCat.of ↥outerE) (Y := TopCat.of ResE) outerInclResC 0) := by
  intro a b hab
  apply augHInt_injective_pathConnected (X := TopCat.of ↥outerE)
  rw [← augHInt_naturality (X := TopCat.of ↥outerE) (Y := TopCat.of ResE) outerInclResC a,
    ← augHInt_naturality (X := TopCat.of ↥outerE) (Y := TopCat.of ResE) outerInclResC b, hab]

/-- **The `E`-side `H₀`-leg of the MV diagonal is injective**: the 16 collar components remain
independent in `H₀(eImage;ℤ)`. -/
theorem diag0_eImage_injective :
    Function.Injective (Homology.mapInt (subIncl (X := KummerK3top)
      (Set.inter_subset_right (s := qThick) (t := eImage))) 0) := by
  have hker : ∀ w, Homology.mapInt (subIncl (X := KummerK3top)
      (Set.inter_subset_right (s := qThick) (t := eImage))) 0 w = 0 → w = 0 := by
    intro w hw
    set v : EIndex → Homology (TopCat.of ↥outerE) 0 := interH0EquivInt w with hv
    have hdec : w = ∑ c, Homology.mapInt (interCopyC c) 0 (v c) := by
      have h1 : w = interH0EquivInt.symm (∑ c, Pi.single c (v c)) := by
        rw [Finset.univ_sum_single v, hv, LinearEquiv.symm_apply_apply]
      rw [h1, map_sum]
      exact Finset.sum_congr rfl (fun c _ => interH0Equiv_symm_single c (v c))
    have himg : ∀ c, Homology.mapInt (X := TopCat.of ↥outerE) (Y := TopCat.of ResE)
        outerInclResC 0 (v c) = 0 := by
      have h2 : eImageHnEquivInt 0 (Homology.mapInt (subIncl (X := KummerK3top)
          (Set.inter_subset_right (s := qThick) (t := eImage))) 0 w) = 0 := by
        rw [hw, map_zero]
      have h3 : eImageHnEquivInt 0 (Homology.mapInt (subIncl (X := KummerK3top)
          (Set.inter_subset_right (s := qThick) (t := eImage))) 0 w)
          = fun c => Homology.mapInt (X := TopCat.of ↥outerE) (Y := TopCat.of ResE)
              outerInclResC 0 (v c) := by
        rw [hdec, map_sum, map_sum]
        have h4 : ∀ c, eImageHnEquivInt 0 (Homology.mapInt (subIncl (X := KummerK3top)
            (Set.inter_subset_right (s := qThick) (t := eImage))) 0
              (Homology.mapInt (interCopyC c) 0 (v c)))
            = Pi.single c (Homology.mapInt (X := TopCat.of ↥outerE) (Y := TopCat.of ResE)
                outerInclResC 0 (v c)) := by
          intro c
          rw [eImageHnEquivInt, LinearEquiv.trans_apply]
          have h5 : (homologyCongrInt (X := sub (X := KummerK3top) eImage)
              (Y := TopCat.of (EIndex × ResE)) eImageHomeo.symm 0)
                (Homology.mapInt (subIncl (X := KummerK3top)
                  (Set.inter_subset_right (s := qThick) (t := eImage))) 0
                  (Homology.mapInt (interCopyC c) 0 (v c)))
              = Homology.mapInt (X := TopCat.of ResE) (Y := TopCat.of (EIndex × ResE))
                  (genInclC (TopCat.of ResE) c) 0
                  (Homology.mapInt (X := TopCat.of ↥outerE) (Y := TopCat.of ResE)
                    outerInclResC 0 (v c)) := by
            rw [homologyCongrInt_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
              ← LinearMap.comp_apply, ← Homology.mapInt_comp, eImage_incl_copy_square c,
              Homology.mapInt_comp, LinearMap.comp_apply]
          rw [h5]
          exact eIndexProdHnEquivIntGen_mapInt_single (TopCat.of ResE) 0 c _
        calc (∑ c, eImageHnEquivInt 0 (Homology.mapInt (subIncl (X := KummerK3top)
              (Set.inter_subset_right (s := qThick) (t := eImage))) 0
                (Homology.mapInt (interCopyC c) 0 (v c))))
            = ∑ c, Pi.single c (Homology.mapInt (X := TopCat.of ↥outerE)
                (Y := TopCat.of ResE) outerInclResC 0 (v c)) :=
              Finset.sum_congr rfl (fun c _ => h4 c)
          _ = fun c => Homology.mapInt (X := TopCat.of ↥outerE) (Y := TopCat.of ResE)
                outerInclResC 0 (v c) :=
              Finset.univ_sum_single _
      intro c
      have h6 := congrFun (h3.symm.trans h2) c
      exact h6
    have hv0 : ∀ c, v c = 0 := fun c => outerIncl_H0_injective (by rw [himg c, map_zero])
    rw [hdec]
    simp [hv0]
  intro a b hab
  have h := hker (a - b) (by rw [map_sub, hab, sub_self])
  exact sub_eq_zero.mp h

/-! ## §6. `δ₀ = 0`, `Σ₁` surjective — `H₁(K3;ℤ)` is a quotient of `H₁(Q;ℤ)` -/

/-- **The degree-0 connecting map vanishes** — the collar components stay independent in the
`E`-side, so nothing connects. -/
theorem k7Delta_zero_eq_zero (x : Homology KummerK3top 1) : k7Delta 0 x = 0 := by
  have hdiag : mvHomDiagInt (X := KummerK3top) qThick eImage 0 (k7Delta 0 x) = 0 :=
    (k7_exact_inter 0).apply_apply_eq_zero x
  have h2 : Homology.mapInt (subIncl (X := KummerK3top)
      (Set.inter_subset_right (s := qThick) (t := eImage))) 0 (k7Delta 0 x) = 0 := by
    have h1 := congrArg Prod.snd hdiag
    rwa [mvHomDiagInt_apply] at h1
  exact diag0_eImage_injective (by rw [h2, map_zero])

/-- **`Σ₁` is surjective**: `H₁(qThick;ℤ) ⊕ H₁(eImage;ℤ) ↠ H₁(K3;ℤ)`. -/
theorem k7Sum1_surjective :
    Function.Surjective (mvHomSumInt (X := KummerK3top) qThick eImage 1) := fun x =>
  (k7_exact_ambient 0 x).mp (k7Delta_zero_eq_zero x)

/-- **Every `H₁(K3;ℤ)` class comes from the thickened `Q`-piece alone** (`H₁(eImage;ℤ) = 0`). -/
theorem k7H1_surjective_from_qThick :
    Function.Surjective (Homology.mapInt (ambIncl (X := KummerK3top) qThick) 1) := by
  intro x
  obtain ⟨⟨u, v⟩, h⟩ := k7Sum1_surjective x
  rw [mvHomSumInt_apply, eImageH1_eq_zero v, map_zero, sub_zero] at h
  exact ⟨u, h⟩

/-- **HEADLINE: `H₁(K3;ℤ)` is a quotient of `H₁(Q;ℤ)`** — the free-quotient first homology
surjects onto the K3 first homology through the weld. The degree-1 window: combined with an
`H₁(Q;ℤ)`-computation this pins `H₁(K3;ℤ)` (and `H₁(K3) = 0` is the classical torsion-freeness
input for `H₂`). -/
theorem h1K3_surjective_from_Q :
    Function.Surjective ((Homology.mapInt (ambIncl (X := KummerK3top) qThick) 1).comp
      (qThickHnEquivInt 0).symm.toLinearMap) := by
  intro x
  obtain ⟨u, hu⟩ := k7H1_surjective_from_qThick x
  refine ⟨qThickHnEquivInt 0 u, ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  exact hu

end

end SKEFTHawking.KummerK7H1Window
