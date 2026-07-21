import Mathlib
import SKEFTHawking.KummerRP3Covering
import SKEFTHawking.KummerK7Opener
import SKEFTHawking.SingularSphereMiddleInt
import SKEFTHawking.SingularSphereHighDegreeInt
import SKEFTHawking.SingularFiniteProdDiscreteHnInt

/-!
# `S³ ⊂ ℂ²  ≃ₜ  S³ ⊂ ℝ⁴` and the integral homology package of the covering sphere

The pinned `ℂ²`-carrier `KummerResolutionPiece.S3` is homeomorphic to the banked metric sphere
`SingularSphereAcyclic.Sph 3` (unit `S³ ⊂ 𝔼⁴`) via the coordinate map `eucToC2` of
`KummerK7Opener` (`(v₀+v₁i, v₂+v₃i)`), upgraded compact-to-`T2`. Transport along
`homologyCongrInt` then delivers the **full integral homology of the covering sphere** on the
`S3top` carrier the `ℝP³` transfer engine (`KummerRP3Covering`) computes with:

* `s3H3EquivInt : H₃(S³;ℤ) ≅ ℤ` (top class — the double cover's fundamental class),
* `s3_homology_one_eq_zero`, `s3_homology_two_eq_zero` (middle vanishing),
* `s3_homology_high : Hₚ(S³;ℤ) = 0` for `p > 3`.

These are the `H_*(S³)` inputs of the interlocking Smith sequences that compute `H_*(ℝP³;ℤ)`
(the K7 seam carrier; `H₂(seam) = 0` is the b₂-accounting priority target).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerRP3Covering (S3top)
open SKEFTHawking.KummerK7Opener
  (eucToC2 continuous_eucToC2 eucToC2_image_sphere euc4_norm_sq norm_sq_symm complex_norm_sq)
open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (homologyCongrInt)

namespace SKEFTHawking.KummerRP3SphereHomeo

noncomputable section

/-- The coordinate map `𝔼⁴ ⊃ S³ → S³ ⊂ ℂ²`, `v ↦ (v₀+v₁i, v₂+v₃i)`, on the spheres. -/
def sphToS3 (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) : S3 :=
  ⟨eucToC2 v.1, by
    have hv : ‖(v : EuclideanSpace ℝ (Fin 4))‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
    have hv2 : ‖(v : EuclideanSpace ℝ (Fin 4))‖ ^ 2 = 1 := by rw [hv]; norm_num
    rw [euc4_norm_sq] at hv2
    show ‖(eucToC2 v.1).1‖ ^ 2 + ‖(eucToC2 v.1).2‖ ^ 2 = 1
    unfold eucToC2
    rw [norm_sq_symm, norm_sq_symm]
    linarith⟩

theorem continuous_sphToS3 : Continuous sphToS3 :=
  Continuous.subtype_mk (continuous_eucToC2.comp continuous_subtype_val) _

theorem sphToS3_injective : Function.Injective sphToS3 := by
  intro v w h
  have h1 : eucToC2 v.1 = eucToC2 w.1 := congrArg Subtype.val h
  unfold eucToC2 at h1
  have hfst := congrArg Prod.fst h1
  have hsnd := congrArg Prod.snd h1
  simp only at hfst hsnd
  have h01 : ((v : EuclideanSpace ℝ (Fin 4)) 0, (v : EuclideanSpace ℝ (Fin 4)) 1)
      = ((w : EuclideanSpace ℝ (Fin 4)) 0, (w : EuclideanSpace ℝ (Fin 4)) 1) :=
    Complex.equivRealProdCLM.symm.toEquiv.injective hfst
  have h23 : ((v : EuclideanSpace ℝ (Fin 4)) 2, (v : EuclideanSpace ℝ (Fin 4)) 3)
      = ((w : EuclideanSpace ℝ (Fin 4)) 2, (w : EuclideanSpace ℝ (Fin 4)) 3) :=
    Complex.equivRealProdCLM.symm.toEquiv.injective hsnd
  apply Subtype.ext
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · exact congrArg Prod.fst h01
  · exact congrArg Prod.snd h01
  · exact congrArg Prod.fst h23
  · exact congrArg Prod.snd h23

theorem sphToS3_surjective : Function.Surjective sphToS3 := by
  intro x
  have hx : (x : ℂ × ℂ) ∈ SKEFTHawking.KummerK7Opener.S3set := x.2
  rw [← eucToC2_image_sphere] at hx
  obtain ⟨v, hv, hvx⟩ := hx
  exact ⟨⟨v, hv⟩, Subtype.ext hvx⟩

/-- **The homeomorphism `S³ ⊂ 𝔼⁴ ≃ₜ S³ ⊂ ℂ²`** — the continuous coordinate bijection upgraded
compact-to-`T2`. -/
def sphHomeoS3 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₜ S3 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective sphToS3 ⟨sphToS3_injective, sphToS3_surjective⟩)
    continuous_sphToS3

/-! ### The integral homology package of the covering sphere, on the `S3top` carrier -/

/-- **`H₃(S³; ℤ) ≅ ℤ`** on the pinned `ℂ²`-carrier — the covering sphere's top class. -/
def s3H3EquivInt : Homology S3top 3 ≃ₗ[ℤ] ℤ :=
  (homologyCongrInt (X := S3top) (Y := Sph 3) sphHomeoS3.symm 3).trans
    SKEFTHawking.SingularLineMinusPointInt.H3S3IsoInt

/-- **`H₁(S³; ℤ) = 0`** on the pinned `ℂ²`-carrier. -/
theorem s3_homology_one_eq_zero (x : Homology S3top 1) : x = 0 := by
  set e := homologyCongrInt (X := S3top) (Y := Sph 3) sphHomeoS3.symm 1 with he
  have hx0 : e x = 0 := SKEFTHawking.SingularSphereMiddleInt.sphere_homology_oneInt
    (by norm_num) _
  have h := e.symm_apply_apply x
  rw [hx0, map_zero] at h
  exact h.symm

/-- **`H₂(S³; ℤ) = 0`** on the pinned `ℂ²`-carrier — the middle-degree vanishing that makes the
seam contribute nothing to `b₂` upstairs. -/
theorem s3_homology_two_eq_zero (x : Homology S3top 2) : x = 0 := by
  set e := homologyCongrInt (X := S3top) (Y := Sph 3) sphHomeoS3.symm 2 with he
  have hx0 : e x = 0 := SKEFTHawking.SingularSphereMiddleInt.sphere_homology_middleInt
    2 3 (by norm_num) (by norm_num) _
  have h := e.symm_apply_apply x
  rw [hx0, map_zero] at h
  exact h.symm

/-- **`Hₚ(S³; ℤ) = 0` for `p > 3`** on the pinned `ℂ²`-carrier. -/
theorem s3_homology_high (p : ℕ) (hp : 3 < p) (x : Homology S3top p) : x = 0 := by
  set e := homologyCongrInt (X := S3top) (Y := Sph 3) sphHomeoS3.symm p with he
  have hx0 : e x = 0 := SKEFTHawking.SingularSphereHighDegreeInt.sphere_homology_high
    3 p hp _
  have h := e.symm_apply_apply x
  rw [hx0, map_zero] at h
  exact h.symm

end

end SKEFTHawking.KummerRP3SphereHomeo
