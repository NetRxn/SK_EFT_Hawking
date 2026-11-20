import SKEFTHawking.ADW.GaussianPolynomialHermite
import SKEFTHawking.Detection.GaussianThreshold
import Mathlib.MeasureTheory.Integral.Pi
/-!
# Affine Gaussian polynomial Hermite identities

The scale σ is positive and the Gaussian variance is σ². The identities hold for every
polynomial degree and every finite coordinate type, including an empty type. Absolute
integrability is proved separately from the integral equalities.

These coefficient identities do not construct the complex auxiliary weight, its Grassmann
evaluation, Berezin orientation, link integration, or the physical source/response bridge.
-/

open Polynomial MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SKEFTHawking.ADW
/-- The formal affine chain rule at every derivative order, for arbitrary real scale. -/
theorem iterate_derivative_comp_affine (n : ℕ) (p : ℝ[X]) (σ μ : ℝ) :
    (derivative^[n]) (p.comp (C σ * X + C μ)) =
      C (σ ^ n) * ((derivative^[n] p).comp (C σ * X + C μ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp]
    rw [Function.iterate_succ_apply']
    simp only [derivative_add, derivative_C_mul_X, derivative_C, add_zero,
      pow_succ, C_mul, mul_assoc]

/-- Every polynomial is integrable under the actual affine Gaussian law. -/
theorem integrable_polynomial_gaussianReal_affine (p : ℝ[X]) (σ μ : ℝ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    Integrable (fun x : ℝ ↦ p.eval x) (gaussianReal μ v) := by
  rw [← Detection.gaussianReal_map_affine hv μ]
  apply (integrable_map_measure p.continuous.aestronglyMeasurable
    (by fun_prop : Measurable (fun z : ℝ ↦ σ*z+μ)).aemeasurable).2
  convert integrable_polynomial_gaussianReal (p.comp (C σ * X + C μ)) using 1
  funext z
  simp [eval_comp]

/-- The entire standardized Hermite insertion is absolutely integrable. -/
theorem integrable_hermite_mul_affine (n : ℕ) (p : ℝ[X]) (σ μ : ℝ)
    (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    Integrable (fun x : ℝ ↦
      aeval ((x-μ)/σ) (hermite n) * p.eval x) (gaussianReal μ v) := by
  rw [← Detection.gaussianReal_map_affine hv μ]
  have hc : Continuous (fun x : ℝ ↦ aeval ((x-μ)/σ) (hermite n) * p.eval x) := by
    fun_prop
  apply (integrable_map_measure hc.aestronglyMeasurable
    (by fun_prop : Measurable (fun z : ℝ ↦ σ*z+μ)).aemeasurable).2
  convert integrable_hermite_mul n (p.comp (C σ * X + C μ)) using 1
  funext z
  simp [eval_comp, ne_of_gt hσ]

private theorem integral_affine_map (f : ℝ → ℝ) (hf : Continuous f)
    (σ μ : ℝ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ x : ℝ, f x ∂gaussianReal μ v) =
      ∫ z : ℝ, f (σ*z+μ) ∂gaussianReal 0 1 := by
  rw [← Detection.gaussianReal_map_affine hv μ]
  exact integral_map (by fun_prop : Measurable (fun z : ℝ ↦ σ*z+μ)).aemeasurable
    hf.aestronglyMeasurable

/-- All-order Hermite integration by parts for mean μ and positive scale σ. -/
theorem integral_hermite_mul_affine (n : ℕ) (p : ℝ[X]) (σ μ : ℝ)
    (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ x : ℝ, aeval ((x-μ)/σ) (hermite n) * p.eval x ∂gaussianReal μ v) =
      σ ^ n * ∫ x : ℝ, ((derivative^[n]) p).eval x ∂gaussianReal μ v := by
  rw [integral_affine_map _ (by fun_prop) σ μ v hv,
    integral_affine_map _ ((derivative^[n]) p).continuous σ μ v hv]
  calc
    (∫ z : ℝ, aeval ((σ*z+μ-μ)/σ) (hermite n) * p.eval (σ*z+μ)
      ∂gaussianReal 0 1) =
        ∫ z : ℝ, aeval z (hermite n) * (p.comp (C σ * X + C μ)).eval z
          ∂gaussianReal 0 1 := by
            apply integral_congr_ae
            filter_upwards [] with z
            simp [eval_comp, ne_of_gt hσ]
    _ = ∫ z : ℝ, ((derivative^[n]) (p.comp (C σ * X + C μ))).eval z
        ∂gaussianReal 0 1 := integral_hermite_mul n _
    _ = σ ^ n * ∫ z : ℝ, ((derivative^[n]) p).eval (σ*z+μ)
        ∂gaussianReal 0 1 := by
      rw [iterate_derivative_comp_affine]
      simp only [eval_mul, eval_C, eval_comp]
      convert integral_const_mul (σ ^ n)
        (fun z : ℝ ↦ ((derivative^[n]) p).eval (σ*z+μ)) using 1
      apply integral_congr_ae
      filter_upwards [] with z
      simp

/-- Genuine absolute integrability of independent polynomial Hermite insertions. -/
theorem integrable_prod_hermite_mul_affine {ι : Type*} [Fintype ι]
    (α : ι → ℕ) (p : ι → ℝ[X]) (σ μ : ι → ℝ) (hσ : ∀ i, 0 < σ i)
    (v : ι → ℝ≥0) (hv : ∀ i, (v i : ℝ) = σ i ^ 2) :
    Integrable (fun x : ι → ℝ ↦
      ∏ i, aeval ((x i-μ i)/σ i) (hermite (α i)) * (p i).eval (x i))
      (Measure.pi (fun i ↦ gaussianReal (μ i) (v i))) :=
  Integrable.fintype_prod (fun i ↦
    integrable_hermite_mul_affine (α i) (p i) (σ i) (μ i) (hσ i) (v i) (hv i))

/-- Every finite coordinate family, with no nonempty-dimension requirement. -/
theorem integral_prod_hermite_mul_affine {ι : Type*} [Fintype ι]
    (α : ι → ℕ) (p : ι → ℝ[X]) (σ μ : ι → ℝ) (hσ : ∀ i, 0 < σ i)
    (v : ι → ℝ≥0) (hv : ∀ i, (v i : ℝ) = σ i ^ 2) :
    (∫ x : ι → ℝ,
      ∏ i, aeval ((x i-μ i)/σ i) (hermite (α i)) * (p i).eval (x i)
        ∂Measure.pi (fun i ↦ gaussianReal (μ i) (v i))) =
      ∏ i, σ i ^ α i *
        ∫ y : ℝ, ((derivative^[α i]) (p i)).eval y ∂gaussianReal (μ i) (v i) := by
  rw [integral_fintype_prod_eq_prod (fun i y ↦
    aeval ((y-μ i)/σ i) (hermite (α i)) * (p i).eval y)]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_hermite_mul_affine (α i) (p i) (σ i) (μ i) (hσ i) (v i) (hv i)

/-- All mixed centered-monomial coefficients, including orders above degree. -/
theorem integral_prod_hermite_mul_pow_affine {ι : Type*} [Fintype ι]
    (α β : ι → ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ x : ι → ℝ, ∏ i, aeval (x i/σ) (hermite (α i)) * x i ^ β i
      ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 v)) =
      ∏ i, σ ^ α i * ((β i).descFactorial (α i) : ℝ) *
        ∫ y : ℝ, y ^ (β i - α i) ∂gaussianReal 0 v := by
  have h := integral_prod_hermite_mul_affine α (fun i ↦ X ^ β i)
    (fun _ ↦ σ) (fun _ ↦ 0) (fun _ ↦ hσ) (fun _ ↦ v) (fun _ ↦ hv)
  simpa [Polynomial.iterate_derivative_X_pow_eq_C_mul, integral_const_mul, mul_assoc]
    using h

/-- Monomial coefficient insertions have genuine product integrability. -/
theorem integrable_prod_hermite_mul_pow_affine {ι : Type*} [Fintype ι]
    (α β : ι → ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    Integrable (fun x : ι → ℝ ↦
      ∏ i, aeval (x i/σ) (hermite (α i)) * x i ^ β i)
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 v)) := by
  simpa using integrable_prod_hermite_mul_affine α (fun i ↦ X ^ β i)
    (fun _ ↦ σ) (fun _ ↦ 0) (fun _ ↦ hσ) (fun _ ↦ v) (fun _ ↦ hv)

/-- Finite coefficient sums inherit absolute integrability, without sign restrictions. -/
theorem integrable_sum_prod_hermite_mul_pow_affine
    {ι κ : Type*} [Fintype ι] (s : Finset κ) (c : κ → ℝ)
    (α : ι → ℕ) (β : κ → ι → ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    Integrable (fun x : ι → ℝ ↦
      ∑ k ∈ s, c k * ∏ i, aeval (x i/σ) (hermite (α i)) * x i ^ β k i)
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 v)) := by
  apply integrable_finsetSum
  intro k _
  exact (integrable_prod_hermite_mul_pow_affine α (β k) σ hσ v hv).const_mul (c k)

/-- Actual finite linearity lifts the all-index coefficient identity to finite polynomials. -/
theorem integral_sum_prod_hermite_mul_pow_affine
    {ι κ : Type*} [Fintype ι] (s : Finset κ) (c : κ → ℝ)
    (α : ι → ℕ) (β : κ → ι → ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ x : ι → ℝ,
      ∑ k ∈ s, c k * ∏ i, aeval (x i/σ) (hermite (α i)) * x i ^ β k i
      ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 v)) =
      ∑ k ∈ s, c k * ∏ i, σ ^ α i * ((β k i).descFactorial (α i) : ℝ) *
        ∫ y : ℝ, y ^ (β k i - α i) ∂gaussianReal 0 v := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, integral_prod_hermite_mul_pow_affine α (β k) σ hσ v hv]
  · intro k _
    exact (integrable_prod_hermite_mul_pow_affine α (β k) σ hσ v hv).const_mul (c k)

-- Normalization checks are consequences of the unrestricted carrying theorem.
example (p : ℝ[X]) (σ μ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ x : ℝ, aeval ((x-μ)/σ) (hermite 0) * p.eval x ∂gaussianReal μ v) =
      ∫ x : ℝ, p.eval x ∂gaussianReal μ v := by
  simpa only [pow_zero, one_mul, Function.iterate_zero, id_eq] using
    integral_hermite_mul_affine 0 p σ μ hσ v hv

example (σ μ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ x : ℝ, aeval ((x-μ)/σ) (hermite 1) * (x-μ) ∂gaussianReal μ v) = σ := by
  have h := integral_hermite_mul_affine 1 (X-C μ) σ μ hσ v hv
  simp_rw [eval_sub, eval_X, eval_C] at h
  simpa using h

example (σ μ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ x : ℝ, aeval ((x-μ)/σ) (hermite 2) * (x-μ)^2 ∂gaussianReal μ v) =
      2*σ^2 := by
  have h := integral_hermite_mul_affine 2 ((X-C μ)^2) σ μ hσ v hv
  norm_num [Function.iterate_succ_apply', derivative_pow, derivative_mul] at h
  simpa [mul_comm] using h

example (n : ℕ) (p : ℝ[X]) :
    (∫ x : ℝ, aeval x (hermite n) * p.eval x ∂gaussianReal 0 1) =
      ∫ x : ℝ, ((derivative^[n]) p).eval x ∂gaussianReal 0 1 := by
  simpa using integral_hermite_mul_affine n p 1 0 (by norm_num) 1 (by norm_num)

example (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ x : Fin 2 → ℝ, ∏ i, aeval (x i/σ) (hermite 1) * x i
      ∂Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 v)) = σ^2 := by
  simpa [Fin.prod_univ_two, pow_two] using
    integral_prod_hermite_mul_pow_affine (fun _ : Fin 2 ↦ 1) (fun _ ↦ 1) σ hσ v hv

example (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    σ^(-2 : ℤ) * (∫ x : Fin 2 → ℝ, ∏ i, aeval (x i/σ) (hermite 1) * x i
      ∂Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 v)) = 1 := by
  have h := integral_prod_hermite_mul_pow_affine
    (fun _ : Fin 2 ↦ 1) (fun _ ↦ 1) σ hσ v hv
  simp only [Fin.prod_univ_two] at h
  have hi : (∫ x : Fin 2 → ℝ, ∏ i, aeval (x i/σ) (hermite 1) * x i
      ∂Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 v)) = σ^2 := by
    simpa [Fin.prod_univ_two, pow_two] using h
  rw [hi]
  simp only [zpow_neg, zpow_ofNat]
  exact inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hσ))

example {ι : Type*} [Fintype ι] [IsEmpty ι]
    (α β : ι → ℕ) (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ^2) :
    (∫ x : ι → ℝ, ∏ i, aeval (x i/σ) (hermite (α i)) * x i ^ β i
      ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 v)) = 1 := by
  rw [integral_prod_hermite_mul_pow_affine α β σ hσ v hv]
  simp
end SKEFTHawking.ADW
