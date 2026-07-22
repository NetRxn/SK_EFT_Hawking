/-
# The degree-3 puncture-MV ingredient: `H₃(Ann⁴;ℤ) ≅ ℤ`

The `H₂(Q;ℤ) ≅ ℤ⁶` computation (`KummerPuncturedMV`) is degree-2-specialised: it uses the annulus
table `H_j(Ann⁴) = 0` for `0 < j < 3` (`ann4_homology_vanish`). At **degree 3** that vanishing does
NOT hold — the closed chart annulus `Ann⁴` is a spherical shell, homotopy-equivalent to `S³`, so its
top homology `H₃(Ann⁴;ℤ) ≅ ℤ` is nonzero. This is the new ingredient the degree-3 puncture-MV needs
(feeding, ultimately, `H₃(T⁴°)` and then `H₃(Q)` — the Q-side degree-3 homology that the
`KummerK3H3Reduction` residual bottoms out in).

Same retraction chain as `ann4_homology_vanish`, but at the top degree with the banked top-sphere
value instead of the middle-vanishing:

    Ann⁴ ≃ₜ annE  (`ann4HomeoE`)
    annE ↩ {‖w‖ = 1/2}  homology-iso via the radial retraction (`sphIncl_mapInt_bijective`, all degrees)
    {‖w‖ = 1/2} ≃ₜ S³ = `Sph 3`  (`sphHalfHomeoSph3`)
    H₃(Sph 3) ≅ ℤ  (`SingularLineMinusPointInt.H3S3IsoInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerPunctureAnnulus
import SKEFTHawking.SingularLineMinusPointInt
import SKEFTHawking.KummerPuncturedMV

namespace SKEFTHawking.KummerPunctureH3

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (homologyCongrInt)
open SKEFTHawking.KummerPunctureBalls (ann4)
open SKEFTHawking.KummerPunctureAnnulus
open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.KummerPunctureBalls (ballsV thickA punc_hcov)
open SKEFTHawking.KummerPuncturedMV (interH2_eq_zero ballsV_homology_eq_zero)
open SKEFTHawking.SingularMayerVietorisLESInt (mvHomSumInt mv_exact_ambientInt mvHomSumInt_apply
  mvHomDiagInt mvDeltaInt mv_exact_interInt mv_exact_middleInt)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl)

noncomputable section

/-- **`H₃(Ann⁴;ℤ) ≅ ℤ`** — the closed chart annulus is a spherical shell (`≃ S³`), so its top
homology is `ℤ`, unlike the middle degrees `1, 2` which vanish (`ann4_homology_vanish`). This is the
degree-3 ingredient of the puncture Mayer–Vietoris that the `H₂` computation did not need. -/
def ann4H3Equiv : Homology (TopCat.of ↥ann4) 3 ≃ₗ[ℤ] ℤ :=
  ((homologyCongrInt (X := TopCat.of ↥ann4) (Y := sub (X := Eucl 4) annE) ann4HomeoE 3).trans
    (LinearEquiv.ofBijective (Homology.mapInt sphInclC (2 + 1))
      (sphIncl_mapInt_bijective 2)).symm).trans
    ((homologyCongrInt (X := sub (X := Eucl 4) sphHalf) (Y := Sph 3) sphHalfHomeoSph3 (2 + 1)).trans
      SKEFTHawking.SingularLineMinusPointInt.H3S3IsoInt)

/-- **`H₃(thickA ∩ ballsV;ℤ) ≅ (EIndex → ℤ)`** — the sixteen degree-3 annulus classes. Composes the
degree-generic 16-fold splitter (`interHnEquiv 3`) with the per-annulus `ann4H3Equiv`. This is the
`ℤ¹⁶` diagonal term of the degree-3 puncture-MV (nonzero, unlike degree 2 where the annuli vanished
and `Σ₂` was bijective). -/
def interH3EquivEIndex :
    Homology (sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)) 3 ≃ₗ[ℤ] (EIndex → ℤ) :=
  (SKEFTHawking.KummerPuncturedMV.interHnEquiv 3).trans
    (LinearEquiv.piCongrRight fun _ : EIndex => ann4H3Equiv)

/-- **`H₃(ballsV;ℤ) = 0`** — the sixteen closed balls are contractible, so `H₃(D⁴) = 0` on each
(`d4_homology_vanish`). The `E`-side vanishes in degree 3, exactly as at degree 2. -/
theorem ballsVH3_eq_zero (x : Homology (sub (X := TopCat.of TorusFour) ballsV) 3) : x = 0 := by
  refine (LinearEquiv.map_eq_zero_iff (SKEFTHawking.KummerPuncturedMV.ballsVHnEquiv 3)).mp ?_
  funext _
  exact d4_homology_vanish 2 _

/-- **`Σ₃` is surjective** — `H₂(collar) = 0` kills the outgoing connecting map, so
`H₃(thickA) ⊕ H₃(ballsV) → H₃(T⁴)` is onto. Degree-3 mirror of `puncSum2_surjective`. -/
theorem puncSum3_surjective :
    Function.Surjective (mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV 3) := fun x =>
  (mv_exact_ambientInt (X := TopCat.of TorusFour) thickA ballsV 2 punc_hcov x).mp
    (interH2_eq_zero _)

/-- **Every `H₃(T⁴;ℤ)` class comes from `thickA` alone** — the ball side is dead in degree 3
(`H₃(ballsV) = 0`). So `H₃(thickA) = H₃(T⁴°) ↠ H₃(T⁴) = ℤ⁴`. Degree-3 mirror of `thickIncl2_surjective`;
the `ℤ⁴` free-quotient half of `H₃(T⁴°) ≅ ℤ¹⁹` (the `ℤ¹⁵` kernel half is `im Δ₃`, still open). -/
theorem thickIncl3_surjective :
    Function.Surjective (Homology.mapInt (ambIncl (X := TopCat.of TorusFour) thickA) 3) := by
  intro x
  obtain ⟨⟨u, v⟩, h⟩ := puncSum3_surjective x
  rw [mvHomSumInt_apply, ballsV_homology_eq_zero 2 v, map_zero, sub_zero] at h
  exact ⟨u, h⟩

/-! ## The degree-3 exact sequence, named — the scaffolding the `H₃(T⁴°) ≅ ℤ¹⁹` solve consumes.

`H₄(T⁴)=ℤ --∂₃--> H₃(collar)=ℤ¹⁶ --Δ₃--> H₃(thickA)⊕H₃(ballsV) --Σ₃--> H₃(T⁴)=ℤ⁴ --> 0`.
`Σ₃` surjective (`puncSum3_surjective`) + `ker Σ₃ = im Δ₃` (`puncMiddle3_exact`) give the SES
`0 → im Δ₃ → H₃(T⁴°) → ℤ⁴ → 0` (splits, ℤ⁴ free); `ker Δ₃ = im ∂₃` (`puncInter3_exact`) reduces
`im Δ₃ = ℤ¹⁶/ker Δ₃ = ℤ¹⁶/im ∂₃`. The single remaining GEOMETRIC input is `im ∂₃ =` the diagonal
`ℤ ⊆ ℤ¹⁶` — the MV connecting map on `[T⁴]` (the fundamental class bounds the 16-annulus complement).
That is a bespoke connecting-map computation (cf. the K7 `delta1_image_parity` arc), NOT a compose. -/

/-- **`ker Σ₃ = im Δ₃`** at the middle — the SES-defining exactness. -/
theorem puncMiddle3_exact :
    Function.Exact (mvHomDiagInt (X := TopCat.of TorusFour) thickA ballsV 3)
      (mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV 3) :=
  mv_exact_middleInt (X := TopCat.of TorusFour) thickA ballsV 2 punc_hcov

/-- **`ker Δ₃ = im ∂₃`** at the collar — reduces `im Δ₃` to `ℤ¹⁶ / im ∂₃`, isolating the connecting
map `∂₃ : H₄(T⁴) → H₃(collar)` as the single remaining geometric input. -/
theorem puncInter3_exact :
    Function.Exact (mvDeltaInt (X := TopCat.of TorusFour) thickA ballsV 3 punc_hcov)
      (mvHomDiagInt (X := TopCat.of TorusFour) thickA ballsV 3) :=
  mv_exact_interInt (X := TopCat.of TorusFour) thickA ballsV 3 punc_hcov

/-! ## The H₃(T⁴°) 2-saturation reduction — isolating the connecting-map crux.

Mirroring `KummerK3H3Reduction` one level down (`T⁴°` in place of `K3`): `H₃(T⁴°) = H₃(thickA)` is
2-torsion-free **as soon as** the puncture connecting map `∂₃ = mvDeltaInt thickA ballsV 3` has
2-saturated image in `H₃(collar) ≅ ℤ¹⁶`. This reduces the still-open `H₃(T⁴°) ≅ ℤ¹⁹` torsion-freeness
to the single geometric fact that `∂₃[T⁴]` is a *primitive* vector — the fundamental class's local
degree `±1` at each of the 16 punctures — removing all the LES bookkeeping from the residual. -/

/-- **`H₃(T⁴)` is 2-torsion-free** — it is `≅ ℤ⁴` (`torusFourH3EquivFin4`), a free module. -/
theorem torusFourH3_twoTorsionFree
    (a : Homology (TopCat.of TorusFour) 3) (ha : (2 : ℤ) • a = 0) : a = 0 := by
  refine (SKEFTHawking.KummerHomologyT4Full.torusFourH3EquivFin4).injective ?_
  rw [map_zero]
  have h : (2 : ℤ) • SKEFTHawking.KummerHomologyT4Full.torusFourH3EquivFin4 a = 0 := by
    rw [← map_smul, ha, map_zero]
  funext i
  have hi := congrFun h i
  simpa using hi

/-- **THE H₃(T⁴°) 2-SATURATION REDUCTION (sufficiency).** `H₃(T⁴°) = H₃(thickA)` is 2-torsion-free
whenever `∂₃ = mvDeltaInt thickA ballsV 3` has 2-saturated image in `H₃(collar)`. Pure diagram chase
over the two banked exactness rows (`puncMiddle3_exact`, `puncInter3_exact`) + `H₃(T⁴)` free: a
2-torsion class `x ∈ H₃(thickA)` dies in `H₃(T⁴)` (ℤ⁴ free) ⟹ `(x,0) ∈ ker Σ₃ = im Δ₃`, say
`Δ₃ w = (x,0)` ⟹ `2•w ∈ ker Δ₃ = im ∂₃` ⟹ (saturation) `w ∈ im ∂₃` ⟹ `Δ₃ w = 0` ⟹ `x = 0`.
Isolates the connecting-map crux (`∂₃[T⁴]` primitive) as the single remaining input to `ℤ¹⁹`. -/
theorem thickA_H3_twoTorsionFree_of_delta3_saturated
    (hsat : ∀ w, (2 : ℤ) • w ∈
          Set.range (mvDeltaInt (X := TopCat.of TorusFour) thickA ballsV 3 punc_hcov) →
        w ∈ Set.range (mvDeltaInt (X := TopCat.of TorusFour) thickA ballsV 3 punc_hcov))
    (x : Homology (sub (X := TopCat.of TorusFour) thickA) 3) (hx : (2 : ℤ) • x = 0) : x = 0 := by
  -- (1) `x` dies in `H₃(T⁴)` (ℤ⁴ free): `thickIncl₃ x = 0`.
  have hincl0 : Homology.mapInt (ambIncl (X := TopCat.of TorusFour) thickA) 3 x = 0 :=
    torusFourH3_twoTorsionFree _ (by rw [← map_smul, hx, map_zero])
  -- (2) `(x,0) ∈ ker Σ₃ = im Δ₃`.
  have hsum0 : mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV 3 (x, 0) = 0 := by
    rw [mvHomSumInt_apply]; simp [hincl0]
  obtain ⟨w, hw⟩ := (puncMiddle3_exact (x, 0)).mp hsum0
  -- (3) `2•w ∈ ker Δ₃ = im ∂₃`, so by saturation `w ∈ im ∂₃`, hence `Δ₃ w = 0`.
  have hdiag2 : mvHomDiagInt (X := TopCat.of TorusFour) thickA ballsV 3 ((2 : ℤ) • w) = 0 := by
    rw [map_smul, hw, Prod.smul_mk, hx, smul_zero]; rfl
  have hwmem := hsat w ((puncInter3_exact ((2 : ℤ) • w)).mp hdiag2)
  have hzero : mvHomDiagInt (X := TopCat.of TorusFour) thickA ballsV 3 w = 0 :=
    (puncInter3_exact w).mpr hwmem
  -- (4) `(x,0) = Δ₃ w = 0`, so `x = 0`.
  have : ((x, 0) : Homology (sub (X := TopCat.of TorusFour) thickA) 3 ×
      Homology (sub (X := TopCat.of TorusFour) ballsV) 3) = 0 := hw ▸ hzero
  simpa using congrArg Prod.fst this

end

end SKEFTHawking.KummerPunctureH3
