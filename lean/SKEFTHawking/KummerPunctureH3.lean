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
open SKEFTHawking.SingularMayerVietorisLESInt (mvHomSumInt mv_exact_ambientInt mvHomSumInt_apply)
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

end

end SKEFTHawking.KummerPunctureH3
