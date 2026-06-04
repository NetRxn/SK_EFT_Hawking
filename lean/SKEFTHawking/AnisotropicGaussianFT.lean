/-
Phase 5q.B, [Θ2]: the anisotropic multivariate Gaussian Fourier transform.

The theta S-transformation (the hard half of the definite-case input [Θ]) needs the Fourier transform of
the anisotropic Gaussian `x ↦ cexp(-b · xᵀGx)` for a positive-definite `G`. The plan (see `ThetaModularity`):
reduce to Mathlib's *isotropic* inner-product-space Gaussian integral `integral_cexp_neg_mul_sq_norm_add`
(`Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform`) by the linear change of variables
`x ↦ (√G)⁻¹ u` (so `xᵀGx = ‖u‖²`), the Jacobian being `|det (√G)⁻¹| = (det G)^{-1/2}`.

This module builds that route brick by brick. The foundational brick — landed here — is the **linear
change-of-variables formula for the Lebesgue (additive Haar) integral**: for an invertible linear
`f : ℝᵈ → ℝᵈ`, `∫ g(f x) dx = |det f|⁻¹ • ∫ g`. It is derived from Mathlib's measure-pushforward identity
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` (`map f μ = ofReal|（det f)⁻¹| • μ`) plus
`integral_map` and `integral_smul_measure`.

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib

namespace SKEFTHawking

open MeasureTheory Matrix
open scoped MatrixOrder

/-- **Linear change of variables for the Lebesgue integral on `ℝᵈ`.** For an invertible linear map
`f : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)` (`det f ≠ 0`) and a measurable `ℂ`-valued `g`,
`∫ x, g (f x) = |（det f)⁻¹| • ∫ y, g y`. This is the Jacobian brick of the anisotropic Gaussian Fourier
transform [Θ2]: composing the Gaussian with `(√G)⁻¹` contributes the factor `(det G)^{-1/2}`. Derived from
`Measure.map_linearMap_addHaar_eq_smul_addHaar` + `integral_map` + `integral_smul_measure`. -/
theorem integral_comp_linearMap_volume {d : ℕ} {f : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)}
    (hf : LinearMap.det f ≠ 0) {g : (Fin d → ℝ) → ℂ} (hg : Measurable g) :
    ∫ x, g (f x) = |(LinearMap.det f)⁻¹| • ∫ y, g y := by
  have hmeas : Measurable f := f.continuous_of_finiteDimensional.measurable
  rw [← integral_map hmeas.aemeasurable hg.aestronglyMeasurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hf, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

/-- **Anisotropic → isotropic reduction (algebraic).** For a positive-semidefinite real matrix `G`, the
quadratic form `xᵀGx` equals `‖(√G) x‖²` (here written `(√G *ᵥ x) ⬝ᵥ (√G *ᵥ x)`), using `√G · √G = G`
(`PosSemidef.sqrt_mul_self`) and symmetry of `√G` (`posSemidef_sqrt`). This is what lets the change of
variables `x ↦ (√G)⁻¹ u` turn the anisotropic Gaussian `exp(-b·xᵀGx)` into the isotropic
`exp(-b·‖u‖²)` that Mathlib's `integral_cexp_neg_mul_sq_norm_add` evaluates. -/
theorem dotProduct_mulVec_eq_sqrt {d : ℕ} {G : Matrix (Fin d) (Fin d) ℝ} (hG : G.PosSemidef)
    (x : Fin d → ℝ) :
    x ⬝ᵥ G *ᵥ x = (CFC.sqrt G *ᵥ x) ⬝ᵥ (CFC.sqrt G *ᵥ x) := by
  have hsym : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have hH : (CFC.sqrt G).IsHermitian := (CFC.sqrt_nonneg G).isSelfAdjoint
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at hH
  conv_lhs => rw [← CFC.sqrt_mul_sqrt_self G hG.nonneg]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym]

end SKEFTHawking
