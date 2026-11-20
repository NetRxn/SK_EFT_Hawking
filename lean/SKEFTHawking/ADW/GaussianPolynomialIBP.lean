import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Polynomial integration by parts for the standard Gaussian

The Gaussian probability measure here has mean zero and variance one. The
identity retains the derivative of the entire polynomial insertion, as required
coefficientwise by the signed auxiliary observable identity.
-/

namespace SKEFTHawking.ADW

open MeasureTheory ProbabilityTheory

/-- Every real polynomial times the standard unnormalized Gaussian is integrable. -/
theorem integrable_polynomial_mul_gaussian (p : Polynomial ℝ) :
    Integrable (fun z : ℝ ↦ p.eval z * Real.exp (-(z ^ 2 / 2))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, add_mul]
    exact hp.add hq
  | monomial n a =>
    have hn : (-1 : ℝ) < (n : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) hn
    simp only [Polynomial.eval_monomial, mul_assoc]
    simp_rw [show ∀ z : ℝ, -(z ^ 2 / 2) = -(1 / 2 : ℝ) * z ^ 2 by intro z; ring]
    exact (by simpa only [Real.rpow_natCast] using h.const_mul a)

/-- The unnormalized polynomial identity follows from whole-line integration by parts. -/
theorem integral_mul_polynomial_gaussian_weight (p : Polynomial ℝ) :
    (∫ z : ℝ, z * p.eval z * Real.exp (-(z ^ 2 / 2))) =
      ∫ z : ℝ, p.derivative.eval z * Real.exp (-(z ^ 2 / 2)) := by
  have hd (z : ℝ) : HasDerivAt (fun z : ℝ ↦ Real.exp (-(z ^ 2 / 2)))
      (-z * Real.exp (-(z ^ 2 / 2))) z := by
    have h : HasDerivAt (fun z : ℝ ↦ -(z ^ 2 / 2)) (-z) z :=
      (((hasDerivAt_pow 2 z).div_const 2).neg).congr_deriv (by ring)
    exact h.exp.congr_deriv (by ring)
  have hint : Integrable (fun z : ℝ ↦ p.eval z * (-z * Real.exp (-(z ^ 2 / 2)))) := by
    apply (integrable_polynomial_mul_gaussian (Polynomial.X * p)).neg.congr
    filter_upwards [] with z
    simp only [Pi.neg_apply, Polynomial.eval_mul, Polynomial.eval_X]
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun z : ℝ ↦ p.eval z) (v := fun z : ℝ ↦ Real.exp (-(z ^ 2 / 2)))
    (u' := fun z : ℝ ↦ p.derivative.eval z)
    (v' := fun z : ℝ ↦ -z * Real.exp (-(z ^ 2 / 2)))
    (fun z _ ↦ p.hasDerivAt z) (fun z _ ↦ hd z) hint
    (integrable_polynomial_mul_gaussian p.derivative) (integrable_polynomial_mul_gaussian p)
  simp only [mul_neg, neg_mul, integral_neg] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using neg_injective h

/-- Integration by parts for every polynomial under the actual standard Gaussian probability. -/
theorem integral_mul_polynomial_gaussianReal (p : Polynomial ℝ) :
    (∫ z : ℝ, z * p.eval z ∂gaussianReal 0 1) =
      ∫ z : ℝ, p.derivative.eval z ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul, neg_div]
  simp_rw [mul_assoc, mul_left_comm (Real.exp _)]
  rw [integral_const_mul, integral_const_mul]
  congr 1
  convert integral_mul_polynomial_gaussian_weight p using 1 <;>
    congr 1 <;> funext z <;> ring

end SKEFTHawking.ADW
