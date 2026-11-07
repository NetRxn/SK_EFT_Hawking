import SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
import SKEFTHawking.ADW.GaussianPolynomialStein

/-!
# Weighted Gaussian transfer on the original Haar polynomial carrier

The Gaussian derivative transfers to the adjoint acting on the weight.
Both integrations use the original normalized link Haar measure.
-/

open MeasureTheory
open scoped NNReal

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

open FiniteGrassmannCoframe GaussianGrassmannAuxiliary MvPolynomial
noncomputable section

/-- The centered Gaussian adjoint of a coordinate derivative on the weight. -/
def haarGaussianWeightAdjoint (L : Torus) (σ : ℝ) (a : Auxiliary L)
    (W : HaarPolynomial L) : HaarPolynomial L :=
  constantHaarPolynomial L (((σ : ℂ) ^ 2)⁻¹) * X a * W - pderiv a W

private theorem integral_haarPolynomial_pderiv (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (a : Auxiliary L) (P : HaarPolynomial L) :
    (∫ z : Links L × (Auxiliary L → ℝ), haarPolynomialEvaluation L z.1 z.2 (pderiv a P)
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) =
    ∫ z : Links L × (Auxiliary L → ℝ),
      haarPolynomialEvaluation L z.1 z.2
        (constantHaarPolynomial L (((σ : ℂ) ^ 2)⁻¹) * X a * P)
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v) := by
  rw [integral_prod _ (haarPolynomial_integrable L σ hσ v hv _),
    integral_prod _ (haarPolynomial_integrable L σ hσ v hv _)]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun U ↦ ?_
  simp only [map_mul, haarPolynomialEvaluation_constant, haarPolynomialEvaluation_X]
  simp only [haarPolynomialEvaluation, MvPolynomial.coe_eval₂Hom,
    eval₂_eq_eval_map, ← pderiv_map]
  exact integral_gaussianPolynomial_pderiv σ hσ v hv a (map (coefficientEvaluation L U) P)

private theorem integral_haarPolynomial_sub (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P Q : HaarPolynomial L) :
    (∫ z : Links L × (Auxiliary L → ℝ), haarPolynomialEvaluation L z.1 z.2 (P - Q)
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) =
    (∫ z : Links L × (Auxiliary L → ℝ), haarPolynomialEvaluation L z.1 z.2 P
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) -
    (∫ z : Links L × (Auxiliary L → ℝ), haarPolynomialEvaluation L z.1 z.2 Q
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) := by
  simp only [map_sub]
  exact integral_sub (haarPolynomial_integrable L σ hσ v hv P)
    (haarPolynomial_integrable L σ hσ v hv Q)

/-- Transfer one partial derivative from a Haar polynomial to its Gaussian weight. -/
theorem integral_haar_eval_weight_pderiv (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (a : Auxiliary L) (W P : HaarPolynomial L) :
    (∫ z : Links L × (Auxiliary L → ℝ), haarPolynomialEvaluation L z.1 z.2 (W * pderiv a P)
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) =
    ∫ z : Links L × (Auxiliary L → ℝ),
      haarPolynomialEvaluation L z.1 z.2 (haarGaussianWeightAdjoint L σ a W * P)
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v) := by
  have h : W * pderiv a P = pderiv a (W * P) - pderiv a W * P := by
    rw [pderiv_mul, add_sub_cancel_left]
  rw [h, integral_haarPolynomial_sub L σ hσ v hv,
    integral_haarPolynomial_pderiv L σ hσ v hv]
  simp only [haarGaussianWeightAdjoint, sub_mul, mul_assoc]
  rw [integral_haarPolynomial_sub L σ hσ v hv]

/-- Both integrands of the first weighted transfer are jointly integrable. -/
theorem haar_eval_weight_pderiv_integrable (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (a : Auxiliary L) (W P : HaarPolynomial L) :
    let μ := (linkHaar L).prod (gaussianMeasure (Auxiliary L) v)
    Integrable (fun z ↦ haarPolynomialEvaluation L z.1 z.2 (W * pderiv a P)) μ ∧
      Integrable (fun z ↦ haarPolynomialEvaluation L z.1 z.2
        (haarGaussianWeightAdjoint L σ a W * P)) μ :=
  ⟨haarPolynomial_integrable L σ hσ v hv _, haarPolynomial_integrable L σ hσ v hv _⟩

/-- Transfer the outer derivative at a first, then transfer the inner derivative at b. -/
theorem integral_haar_eval_weight_pderiv_pderiv (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (a b : Auxiliary L) (W P : HaarPolynomial L) :
    (∫ z : Links L × (Auxiliary L → ℝ),
      haarPolynomialEvaluation L z.1 z.2 (W * pderiv a (pderiv b P))
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) =
    ∫ z : Links L × (Auxiliary L → ℝ), haarPolynomialEvaluation L z.1 z.2
      (haarGaussianWeightAdjoint L σ b (haarGaussianWeightAdjoint L σ a W) * P)
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v) :=
  (integral_haar_eval_weight_pderiv L σ hσ v hv a W (pderiv b P)).trans
    (integral_haar_eval_weight_pderiv L σ hσ v hv b (haarGaussianWeightAdjoint L σ a W) P)

/-- Both integrands of the second weighted transfer are jointly integrable. -/
theorem haar_eval_weight_pderiv_pderiv_integrable (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (a b : Auxiliary L) (W P : HaarPolynomial L) :
    let μ := (linkHaar L).prod (gaussianMeasure (Auxiliary L) v)
    Integrable (fun z ↦ haarPolynomialEvaluation L z.1 z.2 (W * pderiv a (pderiv b P))) μ ∧
      Integrable (fun z ↦ haarPolynomialEvaluation L z.1 z.2
        (haarGaussianWeightAdjoint L σ b (haarGaussianWeightAdjoint L σ a W) * P)) μ :=
  ⟨haarPolynomial_integrable L σ hσ v hv _, haarPolynomial_integrable L σ hσ v hv _⟩

/-- The repeated-coordinate contact is the derivative of the first coordinate factor. -/
theorem haarGaussianWeightAdjoint_comp (L : Torus) (σ : ℝ) (a b : Auxiliary L)
    (W : HaarPolynomial L) :
    let q := constantHaarPolynomial L (((σ : ℂ) ^ 2)⁻¹)
    haarGaussianWeightAdjoint L σ b (haarGaussianWeightAdjoint L σ a W) =
      (q ^ 2 * X a * X b - if a = b then q else 0) * W -
        q * X a * pderiv b W - q * X b * pderiv a W + pderiv b (pderiv a W) := by
  dsimp only
  by_cases h : a = b
  · subst b
    simp only [haarGaussianWeightAdjoint, if_true, map_sub, pderiv_mul,
      constantHaarPolynomial, pderiv_C, pderiv_X_self, zero_mul, zero_add, mul_one]
    ring
  · simp only [haarGaussianWeightAdjoint, if_neg h, map_sub, pderiv_mul,
      constantHaarPolynomial, pderiv_C, pderiv_X_of_ne h, zero_mul, mul_zero, zero_add]
    ring

end
end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
