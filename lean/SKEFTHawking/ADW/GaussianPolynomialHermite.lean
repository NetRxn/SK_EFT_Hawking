import SKEFTHawking.ADW.GaussianPolynomialIBP
import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Polynomial Hermite insertions under the standard Gaussian

These are coefficient-level identities for actual probability integrals.
They do not assert the multivariate auxiliary transform or physical closure.
-/

namespace SKEFTHawking.ADW
open MeasureTheory ProbabilityTheory Polynomial

/-- Every real polynomial is integrable under the standard Gaussian probability. -/
theorem integrable_polynomial_gaussianReal (p : Polynomial ℝ) :
    Integrable (fun z : ℝ ↦ p.eval z) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : NNReal) ≠ 0)]
  rw [integrable_withDensity_iff (measurable_gaussianPDF 0 1)
    (Filter.Eventually.of_forall (fun z ↦ gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  convert (integrable_polynomial_mul_gaussian p).const_mul
    (1 / Real.sqrt (2 * Real.pi)) using 1
  all_goals first | rfl | (funext z; rw [neg_div]; ring)

/-- Mathlib's integer Hermite polynomial, evaluated as a real polynomial. -/
noncomputable abbrev realHermite (n : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)

@[simp] theorem eval_realHermite (n : ℕ) (z : ℝ) :
    (realHermite n).eval z = aeval z (Polynomial.hermite n) := by
  simp [realHermite, Polynomial.eval_map, Polynomial.aeval_def]

/-- The true probabilists' recurrence after scalar extension. -/
theorem realHermite_succ (n : ℕ) :
    realHermite (n + 1) = X * realHermite n - (realHermite n).derivative := by
  simp [realHermite, Polynomial.derivative_map]

/-- One Hermite insertion transfers one derivative to the full polynomial. -/
theorem integral_realHermite_succ_mul (n : ℕ) (p : Polynomial ℝ) :
    (∫ z : ℝ, (realHermite (n + 1)).eval z * p.eval z ∂gaussianReal 0 1) =
      ∫ z : ℝ, (realHermite n).eval z * p.derivative.eval z ∂gaussianReal 0 1 := by
  have h := integral_mul_polynomial_gaussianReal (realHermite n * p)
  have ha := integrable_polynomial_gaussianReal ((realHermite n).derivative * p)
  have hb := integrable_polynomial_gaussianReal (realHermite n * p.derivative)
  simp only [eval_mul, derivative_mul, eval_add] at h ha hb
  simp only [← mul_assoc] at h
  have hc := integral_add ha hb
  simp only [realHermite_succ, eval_sub, eval_mul, eval_X, sub_mul]
  rw [integral_sub]
  · linarith
  · have hh := integrable_polynomial_gaussianReal (X * realHermite n * p)
    simp only [Polynomial.eval_mul, Polynomial.eval_X] at hh
    exact hh
  · exact ha

/-- All-order polynomial Hermite integration by parts under actual Gaussian probability. -/
theorem integral_realHermite_mul (n : ℕ) (p : Polynomial ℝ) :
    (∫ z : ℝ, (realHermite n).eval z * p.eval z ∂gaussianReal 0 1) =
      ∫ z : ℝ, ((Polynomial.derivative)^[n] p).eval z ∂gaussianReal 0 1 := by
  induction n generalizing p with
  | zero => simp [realHermite]
  | succ n ih =>
    rw [integral_realHermite_succ_mul, ih, Function.iterate_succ_apply]

/-- The insertion identity stated directly with Mathlib's Hermite evaluation. -/
theorem integral_hermite_mul (n : ℕ) (p : Polynomial ℝ) :
    (∫ z : ℝ, aeval z (Polynomial.hermite n) * p.eval z ∂gaussianReal 0 1) =
      ∫ z : ℝ, ((Polynomial.derivative)^[n] p).eval z ∂gaussianReal 0 1 := by
  simpa only [eval_realHermite] using integral_realHermite_mul n p

/-- Hermite-polynomial products are genuinely integrable, before taking their integrals. -/
theorem integrable_hermite_mul (n : ℕ) (p : Polynomial ℝ) :
    Integrable (fun z : ℝ ↦ aeval z (Polynomial.hermite n) * p.eval z)
      (gaussianReal 0 1) := by
  have h := integrable_polynomial_gaussianReal (realHermite n * p)
  simpa only [Polynomial.eval_mul, eval_realHermite] using h

/-- Every mixed monomial coefficient reduces to an actual Gaussian moment. -/
theorem integral_hermite_mul_pow (n k : ℕ) :
    (∫ z : ℝ, aeval z (Polynomial.hermite n) * z ^ k ∂gaussianReal 0 1) =
      (k.descFactorial n : ℝ) * ∫ z : ℝ, z ^ (k - n) ∂gaussianReal 0 1 := by
  have h := integral_hermite_mul n (X ^ k)
  simpa [Polynomial.iterate_derivative_X_pow_eq_C_mul, integral_const_mul] using h

/-- Insertions against lower-degree polynomials vanish. -/
theorem integral_hermite_mul_eq_zero (n : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree < n) :
    (∫ z : ℝ, aeval z (Polynomial.hermite n) * p.eval z ∂gaussianReal 0 1) = 0 := by
  rw [integral_hermite_mul, Polynomial.iterate_derivative_eq_zero hp]
  simp

/-- At the degree bound, integration extracts the top coefficient with factorial normalization. -/
theorem integral_hermite_mul_eq_factorial_coeff (n : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ n) :
    (∫ z : ℝ, aeval z (Polynomial.hermite n) * p.eval z ∂gaussianReal 0 1) =
      (n.factorial : ℝ) * p.coeff n := by
  have hd : ((Polynomial.derivative)^[n] p).natDegree ≤ 0 :=
    (Polynomial.natDegree_iterate_derivative p n).trans (by omega)
  rw [integral_hermite_mul, Polynomial.eq_C_of_natDegree_le_zero hd]
  simp [Polynomial.coeff_iterate_derivative, Nat.descFactorial_self]

/-- Mixed Hermite-monomial integrals vanish below the Hermite degree. -/
theorem integral_hermite_mul_pow_eq_zero (n k : ℕ) (hk : k < n) :
    (∫ z : ℝ, aeval z (Polynomial.hermite n) * z ^ k ∂gaussianReal 0 1) = 0 := by
  simpa using integral_hermite_mul_eq_zero n (X ^ k) (by simpa using hk)

/-- The diagonal mixed monomial integral has normalization n!. -/
theorem integral_hermite_mul_pow_self (n : ℕ) :
    (∫ z : ℝ, aeval z (Polynomial.hermite n) * z ^ n ∂gaussianReal 0 1) =
      (n.factorial : ℝ) := by
  simpa using integral_hermite_mul_eq_factorial_coeff n (X ^ n) (by simp)

/-- Scalar extension preserves the Hermite degree. -/
@[simp] theorem natDegree_realHermite (n : ℕ) : (realHermite n).natDegree = n := by
  rw [realHermite, (Polynomial.hermite_monic n).natDegree_map]
  exact Polynomial.natDegree_hermite

/-- Distinct Hermite degrees are orthogonal under actual Gaussian probability. -/
theorem integral_hermite_mul_hermite_of_ne (n m : ℕ) (hnm : n ≠ m) :
    (∫ z : ℝ, aeval z (Polynomial.hermite n) *
      aeval z (Polynomial.hermite m) ∂gaussianReal 0 1) = 0 := by
  rcases lt_or_gt_of_ne hnm with h | h
  · have hh := integral_hermite_mul_eq_zero m (realHermite n) (by simpa using h)
    simpa only [eval_realHermite, mul_comm] using hh
  · simpa only [eval_realHermite] using
      integral_hermite_mul_eq_zero n (realHermite m) (by simpa using h)

/-- The squared Hermite norm is n!, with no degree restriction. -/
theorem integral_hermite_mul_hermite_self (n : ℕ) :
    (∫ z : ℝ, aeval z (Polynomial.hermite n) *
      aeval z (Polynomial.hermite n) ∂gaussianReal 0 1) = (n.factorial : ℝ) := by
  have h := integral_hermite_mul_eq_factorial_coeff n (realHermite n) (by simp)
  simpa [realHermite, Polynomial.coeff_map] using h

end SKEFTHawking.ADW
