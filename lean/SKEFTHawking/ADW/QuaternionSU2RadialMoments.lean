import SKEFTHawking.QuantumNetwork.GaussianSphere

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
  have hg := SKEFTHawking.QuantumNetwork.halfline_moment (n + 3)
  simp_rw [neg_div] at hg
  rw [radialGaussianMoment, hg, Nat.cast_add,
    Nat.cast_ofNat, show (n : ℝ) + 3 + 1 = (n : ℝ) + 4 by ring,
    Real.rpow_neg_eq_inv_rpow, show (1 / 2 : ℝ)⁻¹ = 2 by norm_num,
    show ((n : ℝ) + 2) / 2 = ((n : ℝ) + 4) / 2 - 1 by ring,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  ring

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
