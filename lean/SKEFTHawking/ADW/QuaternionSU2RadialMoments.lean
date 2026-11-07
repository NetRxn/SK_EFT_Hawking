import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Four-dimensional radial Gaussian moments

The radial density in four Euclidean dimensions contributes the power three.
These identities evaluate the radial factor used in the polar comparison for
quaternion sphere moments.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace SKEFTHawking.ADW.QuaternionSU2Sphere

/-- The Gaussian radial factor for a homogeneous polynomial of degree `n` in dimension four. -/
noncomputable def radialGaussianMoment (n : ℕ) : ℝ :=
  ∫ r : ℝ in Ioi 0, r ^ (n + 3) * Real.exp (-(r ^ 2 / 2))

/-- Every polynomial radial factor is absolutely integrable on the positive half-line. -/
theorem radialGaussianIntegrable (n : ℕ) :
    IntegrableOn (fun r : ℝ ↦ r ^ (n + 3) * Real.exp (-(r ^ 2 / 2))) (Ioi 0) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (s := ((n + 3 : ℕ) : ℝ))
    (by norm_num) (by linarith [show 0 ≤ ((n + 3 : ℕ) : ℝ) by positivity])
  have heq (r : ℝ) : -(1 / 2 : ℝ) * r ^ 2 = -(r ^ 2 / 2) := by ring
  simpa only [Real.rpow_natCast, heq] using h.integrableOn (s := Ioi (0 : ℝ))

/-- Substitute the squared radius and evaluate the resulting Gamma integral. -/
theorem radialGaussianMoment_eq_gamma (n : ℕ) :
    radialGaussianMoment n =
      (2 : ℝ) ^ (((n : ℝ) + 2) / 2) * Real.Gamma (((n : ℝ) + 4) / 2) := by
  let a : ℝ := ((n : ℝ) + 4) / 2
  let g : ℝ → ℝ := fun t ↦ t ^ (a - 1) * Real.exp (-((1 / 2 : ℝ) * t))
  have ha : 0 < a := by dsimp [a]; positivity
  have hchange := integral_comp_rpow_Ioi_of_pos (g := g) (p := (2 : ℝ)) (by norm_num)
  have hpow (r : ℝ) (hr : 0 < r) : (r ^ (2 : ℝ)) ^ (a - 1) = r ^ (n + 2) := by
    have he : (2 : ℝ) * (a - 1) = ((n + 2 : ℕ) : ℝ) := by
      simp only [a, Nat.cast_add, Nat.cast_ofNat]
      ring
    rw [← Real.rpow_mul hr.le, he, Real.rpow_natCast]
  have hpoint (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) :
      ((2 : ℝ) * r ^ ((2 : ℝ) - 1)) • g (r ^ (2 : ℝ)) =
        2 * (r ^ (n + 3) * Real.exp (-(r ^ 2 / 2))) := by
    have he : -((1 / 2 : ℝ) * r ^ 2) = -(r ^ 2 / 2) := by ring
    simp only [smul_eq_mul, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, g]
    rw [hpow r hr, show r ^ (2 : ℝ) = r ^ (2 : ℕ) by exact_mod_cast Real.rpow_natCast r 2,
      he, show n + 3 = (n + 2) + 1 by rfl, pow_succ']
    ring
  have hscaled : 2 * radialGaussianMoment n = (2 : ℝ) ^ a * Real.Gamma a := by
    calc
      2 * radialGaussianMoment n =
          ∫ r : ℝ in Ioi 0, 2 * (r ^ (n + 3) * Real.exp (-(r ^ 2 / 2))) := by
        rw [radialGaussianMoment, integral_const_mul]
      _ = ∫ r : ℝ in Ioi 0, ((2 : ℝ) * r ^ ((2 : ℝ) - 1)) • g (r ^ (2 : ℝ)) :=
        setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ (hpoint r hr).symm
      _ = ∫ t : ℝ in Ioi 0, g t := hchange
      _ = (2 : ℝ) ^ a * Real.Gamma a := by
        simpa only [g, show (1 : ℝ) / (1 / 2) = 2 by norm_num] using
          Real.integral_rpow_mul_exp_neg_mul_Ioi (a := a) (r := 1 / 2) ha (by norm_num)
  have hexp : ((n : ℝ) + 2) / 2 = a - 1 := by dsimp [a]; ring
  rw [hexp, Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  linarith only [hscaled]

/-- The radial factor is strictly positive in every degree. -/
theorem radialGaussianMoment_pos (n : ℕ) : 0 < radialGaussianMoment n := by
  rw [radialGaussianMoment_eq_gamma]
  exact mul_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity))

/-- The radial factor for the constant polynomial is two. -/
theorem radialGaussianMoment_zero : radialGaussianMoment 0 = 2 := by
  rw [radialGaussianMoment_eq_gamma]
  have h := Real.Gamma_nat_eq_factorial 1
  norm_num at h
  norm_num [h]

/-- The normalized radial factor in even degree is the denominator of the sphere moment. -/
theorem radialGaussianMoment_even_ratio (k : ℕ) :
    radialGaussianMoment (2 * k) / radialGaussianMoment 0 = (2 : ℝ) ^ k * (k + 1).factorial := by
  rw [radialGaussianMoment_zero, radialGaussianMoment_eq_gamma]
  have he : (((2 * k : ℕ) : ℝ) + 2) / 2 = ((k + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  have hg : (((2 * k : ℕ) : ℝ) + 4) / 2 = ((k + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [he, hg, Real.rpow_natCast, Real.Gamma_nat_eq_factorial, pow_succ]
  ring

end SKEFTHawking.ADW.QuaternionSU2Sphere
