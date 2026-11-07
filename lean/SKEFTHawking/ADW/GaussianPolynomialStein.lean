import SKEFTHawking.ADW.GaussianAuxiliaryComplex
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Centered Gaussian Stein identity for complex polynomials

Absolute integrability and coordinatewise integration by parts follow from the
finite product Hermite moments. The polynomial coefficients are complex, and the
coordinates and Gaussian variance are real.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SKEFTHawking.ADW
noncomputable section
variable {ι : Type*} [Fintype ι]

private theorem eval_monomial_auxiliary (d : ι →₀ ℕ) (c : ℂ) (h : ι → ℝ) :
    MvPolynomial.eval (fun i ↦ (h i : ℂ)) (MvPolynomial.monomial d c) =
      c * (auxiliaryMonomial d h : ℂ) := by
  rw [MvPolynomial.eval_monomial, auxiliaryMonomial, Complex.ofReal_prod]
  simp only [Complex.ofReal_pow]
  rw [Finsupp.prod_fintype d (fun i n ↦ (h i : ℂ) ^ n) (by simp)]

/-- Finite complex polynomials in real coordinates have absolute centered Gaussian moments. -/
theorem integrable_gaussianPolynomialEval (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0)
    (hv : (v : ℝ) = σ ^ 2) (P : MvPolynomial ι ℂ) :
    Integrable (fun h : ι → ℝ ↦ MvPolynomial.eval (fun i ↦ (h i : ℂ)) P)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 v) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    simp only [eval_monomial_auxiliary]
    have hi := (integrable_auxiliaryHermite_mul_monomial σ hσ v hv
      (0 : ι →₀ ℕ) d).ofReal (𝕜 := ℂ)
    simpa [auxiliaryHermite] using hi.const_mul c
  | add P Q hP hQ =>
    refine (hP.add hQ).congr (Filter.Eventually.of_forall ?_)
    intro h
    exact MvPolynomial.eval_add.symm

private theorem integral_auxiliaryMonomial_complex (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0)
    (hv : (v : ℝ) = σ ^ 2) (d : ι →₀ ℕ) :
    (∫ h : ι → ℝ, (auxiliaryMonomial d h : ℂ) ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v)) =
      ((∏ i, ∫ y : ℝ, y ^ d i ∂gaussianReal 0 v : ℝ) : ℂ) := by
  simpa [auxiliaryHermite] using
    integral_auxiliaryHermite_mul_monomial σ hσ v hv (0 : ι →₀ ℕ) d

private theorem auxiliaryHermite_single_one (σ : ℝ) (a : ι) (h : ι → ℝ) :
    auxiliaryHermite σ (Finsupp.single a 1) h = h a / σ := by
  classical
  rw [auxiliaryHermite, Fintype.prod_eq_single a]
  · simp
  · intro i hi
    simp [Finsupp.single_eq_of_ne hi, Polynomial.hermite_zero]

private theorem integral_coordinate_mul_auxiliaryMonomial (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (a : ι) (d : ι →₀ ℕ) :
    (∫ h : ι → ℝ, (h a : ℂ) * (auxiliaryMonomial d h : ℂ)
      ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v)) =
      (σ : ℂ) ^ 2 * (d a : ℂ) *
        ∫ h : ι → ℝ, (auxiliaryMonomial (d - Finsupp.single a 1) h : ℂ)
          ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v) := by
  classical
  let e : ι →₀ ℕ := Finsupp.single a 1
  have hs := integral_auxiliaryHermite_mul_monomial σ hσ v hv e d
  have hfactor :
      (∏ i, σ ^ e i * ((d i).descFactorial (e i) : ℝ) *
        ∫ y : ℝ, y ^ (d i - e i) ∂gaussianReal 0 v) =
      σ * (d a : ℝ) * (∏ i, ∫ y : ℝ, y ^ (d i - e i) ∂gaussianReal 0 v) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_eq_single a]
    · simp [e]
    · intro i hi
      simp [e, Finsupp.single_eq_of_ne hi]
  rw [hfactor] at hs
  have he :
      (fun h : ι → ℝ ↦ ((auxiliaryHermite σ e h * auxiliaryMonomial d h : ℝ) : ℂ)) =
      (fun h : ι → ℝ ↦ ((h a : ℂ) * (auxiliaryMonomial d h : ℂ)) / (σ : ℂ)) := by
    funext h
    rw [show auxiliaryHermite σ e h = h a / σ from auxiliaryHermite_single_one σ a h]
    push_cast
    ring
  rw [he, integral_div, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_natCast] at hs
  have hn : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  rw [integral_auxiliaryMonomial_complex σ hσ v hv]
  simp only [e, Finsupp.tsub_apply] at hs ⊢
  linear_combination (div_eq_iff hn).mp hs

/-- Under the centered product Gaussian, a polynomial partial derivative transfers to
multiplication by the corresponding coordinate divided by the variance. -/
theorem integral_gaussianPolynomial_pderiv (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0)
    (hv : (v : ℝ) = σ ^ 2) (a : ι) (P : MvPolynomial ι ℂ) :
    (∫ h : ι → ℝ, MvPolynomial.eval (fun i ↦ (h i : ℂ)) (MvPolynomial.pderiv a P)
      ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v)) =
    ∫ h : ι → ℝ, ((σ : ℂ) ^ 2)⁻¹ * (h a : ℂ) *
      MvPolynomial.eval (fun i ↦ (h i : ℂ)) P ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v) := by
  have hi (Q : MvPolynomial ι ℂ) :
      Integrable (fun h : ι → ℝ ↦ ((σ : ℂ) ^ 2)⁻¹ * (h a : ℂ) *
        MvPolynomial.eval (fun i ↦ (h i : ℂ)) Q)
        (Measure.pi fun _ : ι ↦ gaussianReal 0 v) := by
    refine ((integrable_gaussianPolynomialEval σ hσ v hv (MvPolynomial.X a * Q)).const_mul
      (((σ : ℂ) ^ 2)⁻¹)).congr (Filter.Eventually.of_forall ?_)
    intro h
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, mul_assoc]
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    simp only [MvPolynomial.pderiv_monomial, eval_monomial_auxiliary]
    have he :
        (fun h : ι → ℝ ↦ ((σ : ℂ) ^ 2)⁻¹ * (h a : ℂ) * (c * (auxiliaryMonomial d h : ℂ))) =
        (fun h : ι → ℝ ↦ (((σ : ℂ) ^ 2)⁻¹ * c) * ((h a : ℂ) * (auxiliaryMonomial d h : ℂ))) := by
      funext h
      ring
    rw [he]
    simp only [integral_const_mul, integral_coordinate_mul_auxiliaryMonomial σ hσ v hv]
    have hn : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    field_simp
  | add P Q hP hQ =>
    simp only [map_add, mul_add]
    rw [integral_add (integrable_gaussianPolynomialEval σ hσ v hv _)
      (integrable_gaussianPolynomialEval σ hσ v hv _), integral_add (hi P) (hi Q), hP, hQ]

end
end SKEFTHawking.ADW
