import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Standard Gaussian moments (Phase 6AG, Ask 4 — foundation for the Haar twirl)

Foundational moment lemmas for the standard 1-D Gaussian, the seed of the degree-4
sphere-moment / unitary-2-design identity behind the average-gate-fidelity formula
`F_avg = (d·F_e + 1)/(d+1)`. These are the building blocks the Gaussian→sphere polar route consumes;
the Weingarten/2-design machinery is absent from Mathlib at this pin, so it is built from the
moment level up.

## Architecture note (route selection)

Mathlib's polar-coordinate decomposition `measurePreserving_homeomorphUnitSphereProd` and the
unit-sphere surface measure `Measure.toSphere` are defined for an **additive Haar measure**
(`volume`), *not* for the Gaussian probability measure (`stdGaussian` is a pushforward of a product
of `gaussianReal` and carries no density-w.r.t.-`volume` lemma at this pin). Consequently the
Gaussian→sphere bridge (downstream bricks) routes through the **Lebesgue (`volume`) polar
decomposition with the Gaussian weight `exp(-‖x‖²/2)` folded into the integrand**, and the radial
normalisation factors cancel. The 1-D building blocks therefore live as **unnormalised
Lebesgue-weighted moments** `∫ x^n · exp(-x²/2)` (this file), feeding the multivariate Wick tensor
and the radial/sphere split. The probability-measure forms `∫ x^n ∂N(0,1)` are recorded as
corollaries via `integral_gaussianReal_eq_integral_smul`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open MeasureTheory ProbabilityTheory Real Set

/-- **Second moment of the standard 1-D Gaussian:** `∫ x² ∂N(0,1) = 1`. Since `N(0,1)` has mean `0`,
the second moment equals the variance, which is `1` (`variance_id_gaussianReal`). -/
theorem integral_sq_gaussianReal : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hv := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [ProbabilityTheory.variance_eq_integral aemeasurable_id] at hv
  simp only [id_eq] at hv
  rw [integral_id_gaussianReal] at hv
  simpa using hv

/-! ### Unnormalised Lebesgue-weighted 1-D Gaussian moments

`J_n := ∫_ℝ x^n · exp(-x²/2) dx`. The even moments are evaluated through the half-line
Gamma integral `integral_rpow_mul_exp_neg_mul_rpow` (doubled across `ℝ` via `integral_comp_abs`),
and the odd moments vanish by the odd-function symmetry of the integrand. -/

/-- `J₀ = ∫_ℝ exp(-x²/2) dx = √(2π)` (the Gaussian normalising integral). -/
theorem integral_gaussian_weight : ∫ x : ℝ, Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * π) := by
  have h := integral_gaussian (1 / 2)
  rw [show √(π / (1 / 2)) = √(2 * π) by rw [show π / (1 / 2) = 2 * π by ring]] at h
  rw [← h]; congr 1; funext x; congr 1; ring

/-- `J₂ = ∫_ℝ x²·exp(-x²/2) dx = √(2π)`. -/
theorem integral_pow_two_mul_gaussian :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * π) := by
  have hg : ∀ x : ℝ, x ^ 2 * Real.exp (-x ^ 2 / 2)
      = (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 2)) |x| := by
    intro x; simp only [sq_abs]
  calc ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2 / 2)
      = ∫ x : ℝ, (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 2)) |x| :=
        integral_congr_ae (Filter.Eventually.of_forall hg)
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-x ^ 2 / 2) :=
        integral_comp_abs (f := fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 2))
    _ = Real.sqrt (2 * π) := by
        have hconv : (∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-x ^ 2 / 2))
            = ∫ x in Set.Ioi (0 : ℝ), x ^ (2 : ℝ) * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
          simp only []
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          push_cast
          rw [show (-(1 / 2 : ℝ) * x ^ 2) = -x ^ 2 / 2 by ring]
        rw [hconv, integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num),
            show ((2 : ℝ) + 1) / 2 = 3 / 2 by norm_num,
            show (-((2 : ℝ) + 1) / 2) = (-(3 : ℝ) / 2) by norm_num]
        have hΓ : Real.Gamma (3 / 2) = Real.sqrt π / 2 := by
          have h := Real.Gamma_nat_add_one_add_half 0
          norm_num [Nat.doubleFactorial] at h
          linarith [h]
        have hb : (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2) = 2 * Real.sqrt 2 := by
          rw [show (-(3 : ℝ) / 2) = -(3 / 2) by ring, Real.rpow_neg (by norm_num),
              show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num), inv_inv,
              show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add (by norm_num), Real.rpow_one,
              ← Real.sqrt_eq_rpow]
        rw [hb, hΓ, Real.sqrt_mul (by norm_num) π]; ring

/-- `J₄ = ∫_ℝ x⁴·exp(-x²/2) dx = 3·√(2π)`. The seed of the `E[x⁴] = 3` Wick contraction. -/
theorem integral_pow_four_mul_gaussian :
    ∫ x : ℝ, x ^ 4 * Real.exp (-x ^ 2 / 2) = 3 * Real.sqrt (2 * π) := by
  have hg : ∀ x : ℝ, x ^ 4 * Real.exp (-x ^ 2 / 2)
      = (fun t : ℝ => t ^ 4 * Real.exp (-t ^ 2 / 2)) |x| := by
    intro x
    have h4 : |x| ^ 4 = x ^ 4 := by
      calc |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
        _ = (x ^ 2) ^ 2 := by rw [sq_abs]
        _ = x ^ 4 := by ring
    simp only [sq_abs, h4]
  calc ∫ x : ℝ, x ^ 4 * Real.exp (-x ^ 2 / 2)
      = ∫ x : ℝ, (fun t : ℝ => t ^ 4 * Real.exp (-t ^ 2 / 2)) |x| :=
        integral_congr_ae (Filter.Eventually.of_forall hg)
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), x ^ 4 * Real.exp (-x ^ 2 / 2) :=
        integral_comp_abs (f := fun t : ℝ => t ^ 4 * Real.exp (-t ^ 2 / 2))
    _ = 3 * Real.sqrt (2 * π) := by
        have hconv : (∫ x in Set.Ioi (0 : ℝ), x ^ 4 * Real.exp (-x ^ 2 / 2))
            = ∫ x in Set.Ioi (0 : ℝ), x ^ (4 : ℝ) * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
          simp only []
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
              Real.rpow_natCast, Real.rpow_natCast]
          push_cast
          rw [show (-(1 / 2 : ℝ) * x ^ 2) = -x ^ 2 / 2 by ring]
        rw [hconv, integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num),
            show ((4 : ℝ) + 1) / 2 = 5 / 2 by norm_num,
            show (-((4 : ℝ) + 1) / 2) = (-(5 : ℝ) / 2) by norm_num]
        have hΓ : Real.Gamma (5 / 2) = 3 * Real.sqrt π / 4 := by
          have h := Real.Gamma_nat_add_one_add_half 1
          norm_num [Nat.doubleFactorial] at h
          linarith [h]
        have hb : (1 / 2 : ℝ) ^ (-(5 : ℝ) / 2) = 4 * Real.sqrt 2 := by
          rw [show (-(5 : ℝ) / 2) = -(5 / 2) by ring, Real.rpow_neg (by norm_num),
              show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num), inv_inv,
              show (5 / 2 : ℝ) = 2 + 1 / 2 by ring, Real.rpow_add (by norm_num), Real.rpow_two,
              ← Real.sqrt_eq_rpow]
          norm_num
        rw [hb, hΓ, Real.sqrt_mul (by norm_num) π]; ring

/-- The odd unnormalised moments vanish: `∫_ℝ x^(2k+1)·exp(-x²/2) dx = 0`, by odd symmetry of the
integrand (covers `J₁` at `k = 0` and `J₃` at `k = 1`). -/
theorem integral_odd_mul_gaussian (k : ℕ) :
    ∫ x : ℝ, x ^ (2 * k + 1) * Real.exp (-x ^ 2 / 2) = 0 := by
  set f : ℝ → ℝ := fun x => x ^ (2 * k + 1) * Real.exp (-x ^ 2 / 2) with hf
  have hodd : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    simp only [hf]
    rw [Odd.neg_pow ⟨k, by ring⟩, show ((-x) ^ 2) = x ^ 2 by ring]
    ring
  have key : ∫ x, f x = -∫ x, f x := by
    calc ∫ x, f x = ∫ x, f (-x) := (integral_neg_eq_self f volume).symm
      _ = ∫ x, -f x := by congr 1; funext x; exact hodd x
      _ = -∫ x, f x := integral_neg _
  linarith [key]

/-- **Fourth moment of the standard 1-D Gaussian:** `∫ x⁴ ∂N(0,1) = 3` (the kurtosis-3 identity),
derived from the unnormalised Lebesgue moment `J₄` via the Gaussian density. Pairs with
`integral_sq_gaussianReal` (`∫ x² ∂N(0,1) = 1`); together these are the per-coordinate inputs to
the multivariate Wick contraction. -/
theorem integral_pow_four_gaussianReal : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have hpdf : ∀ x : ℝ, gaussianPDFReal 0 1 x • (x ^ 4)
      = (Real.sqrt (2 * π))⁻¹ * (x ^ 4 * Real.exp (-x ^ 2 / 2)) := by
    intro x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    ring
  simp_rw [hpdf]
  rw [integral_const_mul, integral_pow_four_mul_gaussian]
  have h2pi : Real.sqrt (2 * π) ≠ 0 := by positivity
  field_simp

end SKEFTHawking.QuantumNetwork
