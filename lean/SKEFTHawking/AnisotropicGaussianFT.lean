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

/-- **Change of variables `x ↦ (√G)⁻¹ u` with the Gaussian Jacobian** (positive-definite `G`). For measurable
`g`, `∫ u, g ((√G)⁻¹ *ᵥ u) = √(det G) • ∫ y, g y`. The Jacobian `√(det G)` is `|det (√G)⁻¹|⁻¹ = (det √G) =
√(det G)` via `Matrix.PosSemidef.det_sqrt`. Applied to `g(x) = exp(-b·xᵀGx + linear)`, the substitution turns
`xᵀGx` into `‖u‖²` (brick `dotProduct_mulVec_eq_sqrt` with `√G·(√G)⁻¹ = 1`), reducing the anisotropic
Gaussian to the separable isotropic one `integral_cexp_neg_mul_sum_add`. -/
theorem integral_comp_sqrtInv {d : ℕ} {G : Matrix (Fin d) (Fin d) ℝ} (hG : G.PosDef)
    {g : (Fin d → ℝ) → ℂ} (hg : Measurable g) :
    ∫ u, g ((CFC.sqrt G)⁻¹ *ᵥ u) = Real.sqrt G.det • ∫ y, g y := by
  have hdetpos : 0 < G.det := hG.det_pos
  have hsqrtdet : (CFC.sqrt G).det = Real.sqrt G.det := by
    rw [Matrix.PosSemidef.det_sqrt hG.posSemidef, RCLike.sqrt_of_nonneg hdetpos.le]
    simp
  have hMdet : ((CFC.sqrt G)⁻¹).det = (Real.sqrt G.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, hsqrtdet, Ring.inverse_eq_inv']
  have hf : LinearMap.det (Matrix.toLin' ((CFC.sqrt G)⁻¹)) ≠ 0 := by
    rw [LinearMap.det_toLin', hMdet]
    exact inv_ne_zero (Real.sqrt_pos.mpr hdetpos).ne'
  have hcv := integral_comp_linearMap_volume hf hg
  simp only [Matrix.toLin'_apply, LinearMap.det_toLin', hMdet, inv_inv,
    abs_of_nonneg (Real.sqrt_nonneg G.det)] at hcv
  exact hcv

/-- `IsUnit (√G).det` for positive-definite `G` (det `√G = √(det G) > 0`). -/
theorem isUnit_det_sqrt {d : ℕ} {G : Matrix (Fin d) (Fin d) ℝ} (hG : G.PosDef) :
    IsUnit (CFC.sqrt G).det := by
  have h : (CFC.sqrt G).det = Real.sqrt G.det := by
    rw [Matrix.PosSemidef.det_sqrt hG.posSemidef, RCLike.sqrt_of_nonneg hG.det_pos.le]; simp
  rw [h]; exact (Real.sqrt_pos.mpr hG.det_pos).ne'.isUnit

/-- The change of variables `u ↦ (√G)⁻¹ u` sends the quadratic form `G` to the standard one:
`((√G)⁻¹ u)ᵀ G ((√G)⁻¹ u) = ∑ᵢ uᵢ²` (using `dotProduct_mulVec_eq_sqrt` and `√G·(√G)⁻¹ = 1`). -/
theorem sqrtInv_quadratic {d : ℕ} {G : Matrix (Fin d) (Fin d) ℝ} (hG : G.PosDef) (u : Fin d → ℝ) :
    ((CFC.sqrt G)⁻¹ *ᵥ u) ⬝ᵥ G *ᵥ ((CFC.sqrt G)⁻¹ *ᵥ u) = ∑ i, (u i) ^ 2 := by
  rw [dotProduct_mulVec_eq_sqrt hG.posSemidef, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_det_sqrt hG), Matrix.one_mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => (sq (u i)).symm

/-- The linear term transforms under `u ↦ (√G)⁻¹ u` as a `vecMul` (over the ℝ→ℂ cast):
`∑ᵢ cᵢ ((√G)⁻¹ u)ᵢ = ∑ⱼ (c ᵥ* (√G)⁻¹_ℂ)ⱼ uⱼ` where `(√G)⁻¹_ℂ = ((√G)⁻¹).map (↑)`. Via the
`dotProduct`/`vecMul` adjunction `(c ᵥ* M) ⬝ᵥ u = c ⬝ᵥ (M *ᵥ u)` and commutation of the cast with `mulVec`. -/
theorem sqrtInv_linear {d : ℕ} {G : Matrix (Fin d) (Fin d) ℝ} (c : Fin d → ℂ) (u : Fin d → ℝ) :
    ∑ i, c i * (((CFC.sqrt G)⁻¹ *ᵥ u) i : ℂ)
      = ∑ j, (c ᵥ* ((CFC.sqrt G)⁻¹.map (Complex.ofReal))) j * (u j : ℂ) := by
  have hcast : ∀ i, (((CFC.sqrt G)⁻¹ *ᵥ u) i : ℂ)
      = (((CFC.sqrt G)⁻¹.map (Complex.ofReal)) *ᵥ (fun k => (u k : ℂ))) i := by
    intro i
    simp [Matrix.mulVec, dotProduct]
  simp only [hcast]
  exact Matrix.dotProduct_mulVec c ((CFC.sqrt G)⁻¹.map (Complex.ofReal)) (fun k => (u k : ℂ))

/-- **The anisotropic multivariate Gaussian integral with a linear character** ([Θ2]). For positive-definite
real `G`, `b : ℂ` with `0 < b.re`, and any complex coefficient vector `c`:

> `∫_{ℝᵈ} exp(-b·xᵀGx + ∑ᵢ cᵢ xᵢ) dx = (det G)^{-1/2} · (π/b)^{d/2} · exp((∑ᵢ (c ᵥ* (√G)⁻¹_ℂ)ᵢ²)/(4b))`

where `(√G)⁻¹_ℂ = ((√G)⁻¹).map ofReal`. (For the theta route the linear coefficient is the character
`cᵢ = -2πI·nᵢ`, `b = -iπτ` with `b.re = π·Im τ > 0`, and `∑(c ᵥ* (√G)⁻¹_ℂ)ᵢ² = cᵀG⁻¹c`.) Assembled from the
change of variables `x ↦ (√G)⁻¹ u` (`integral_comp_sqrtInv`, Jacobian `√(det G)`), the substitution lemmas
`sqrtInv_quadratic`/`sqrtInv_linear`, and Mathlib's separable isotropic Gaussian `integral_cexp_neg_mul_sum_add`. -/
theorem integral_cexp_neg_quadratic_form {d : ℕ} {G : Matrix (Fin d) (Fin d) ℝ} (hG : G.PosDef)
    {b : ℂ} (hb : 0 < b.re) (c : Fin d → ℂ) :
    ∫ x : Fin d → ℝ, Complex.exp (-b * ((x ⬝ᵥ G *ᵥ x : ℝ) : ℂ) + ∑ i, c i * (x i : ℂ))
      = ((Real.sqrt G.det : ℂ))⁻¹ * (((Real.pi : ℂ) / b) ^ ((d : ℂ) / 2)
        * Complex.exp ((∑ i, (c ᵥ* ((CFC.sqrt G)⁻¹.map (Complex.ofReal))) i ^ 2) / (4 * b))) := by
  have hmeas : Measurable (fun x : Fin d → ℝ =>
      Complex.exp (-b * ((x ⬝ᵥ G *ᵥ x : ℝ) : ℂ) + ∑ i, c i * (x i : ℂ))) := by fun_prop
  have hdne : Real.sqrt G.det ≠ 0 := (Real.sqrt_pos.mpr hG.det_pos).ne'
  have hpt : ∀ u : Fin d → ℝ,
      Complex.exp (-b * ((((CFC.sqrt G)⁻¹ *ᵥ u) ⬝ᵥ G *ᵥ ((CFC.sqrt G)⁻¹ *ᵥ u) : ℝ) : ℂ)
          + ∑ i, c i * (((CFC.sqrt G)⁻¹ *ᵥ u) i : ℂ))
        = Complex.exp (-b * ∑ i, ((u i : ℂ)) ^ 2
          + ∑ i, (c ᵥ* ((CFC.sqrt G)⁻¹.map (Complex.ofReal))) i * (u i : ℂ)) := by
    intro u
    rw [sqrtInv_quadratic hG u, sqrtInv_linear c u]
    push_cast
    ring_nf
  have key : Real.sqrt G.det • (∫ x : Fin d → ℝ,
        Complex.exp (-b * ((x ⬝ᵥ G *ᵥ x : ℝ) : ℂ) + ∑ i, c i * (x i : ℂ)))
      = ((Real.pi : ℂ) / b) ^ ((d : ℂ) / 2)
        * Complex.exp ((∑ i, (c ᵥ* ((CFC.sqrt G)⁻¹.map (Complex.ofReal))) i ^ 2) / (4 * b)) := by
    rw [← integral_comp_sqrtInv hG hmeas]
    simp only [hpt]
    rw [GaussianFourier.integral_cexp_neg_mul_sum_add hb (c ᵥ* ((CFC.sqrt G)⁻¹.map (Complex.ofReal))),
      Fintype.card_fin]
  rw [← key, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hdne), one_mul]

/-- The exponent quadratic form of `integral_cexp_neg_quadratic_form` is the inverse form `cᵀ G⁻¹ c`:
`∑ᵢ (c ᵥ* (√G)⁻¹_ℂ)ᵢ² = c ⬝ᵥ (G⁻¹_ℂ) *ᵥ c`, using `(√G)⁻¹` symmetric and `(√G)⁻¹(√G)⁻¹ = G⁻¹`
(`mul_inv_rev` + `CFC.sqrt_mul_sqrt_self`). Recognises the [Θ2] Gaussian integral's exponent in the form the
theta S-transformation `Θ_G(-1/τ) ∝ Θ_{G⁻¹}(τ)` consumes. -/
theorem sum_sq_vecMul_sqrtInv_eq {d : ℕ} {G : Matrix (Fin d) (Fin d) ℝ} (hG : G.PosDef) (c : Fin d → ℂ) :
    ∑ i, (c ᵥ* ((CFC.sqrt G)⁻¹.map (Complex.ofReal))) i ^ 2
      = c ⬝ᵥ (G⁻¹.map (Complex.ofReal)) *ᵥ c := by
  have hsqrtsym : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have hH : (CFC.sqrt G).IsHermitian := (CFC.sqrt_nonneg G).isSelfAdjoint
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at hH
  have hreal : (CFC.sqrt G)⁻¹ * (CFC.sqrt G)⁻¹ = G⁻¹ := by
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]
  set M := (CFC.sqrt G)⁻¹.map (Complex.ofReal) with hM
  have hMsym : Mᵀ = M := by
    rw [hM, ← Matrix.transpose_map, Matrix.transpose_nonsing_inv, hsqrtsym]
  have hMM : M * M = G⁻¹.map (Complex.ofReal) := by
    rw [hM, ← hreal]
    ext i j
    simp [Matrix.mul_apply, Matrix.map_apply, Complex.ofReal_sum, Complex.ofReal_mul]
  have hsum : ∑ i, (c ᵥ* M) i ^ 2 = (c ᵥ* M) ⬝ᵥ (c ᵥ* M) := by
    simp only [dotProduct, pow_two]
  rw [hsum, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hMsym, Matrix.mulVec_mulVec, hMM]

end SKEFTHawking
