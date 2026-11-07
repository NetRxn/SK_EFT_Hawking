import SKEFTHawking.ADW.GaussianAuxiliaryComplex
import SKEFTHawking.ADW.QuaternionSU2Haar
import SKEFTHawking.ADW.QuaternionSU2RadialMoments
import SKEFTHawking.QuantumNetwork.GaussianSphere

/-!
# Quaternion monomial moments on SU(2)

The Cartesian Gaussian integral factors over the four coordinates. Its polar
form splits into a surface integral and a radial moment. Comparing the two
forms and using the normalized sphere pushforward gives exact Haar moments
at every degree.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace SKEFTHawking.ADW.QuaternionSU2Sphere

open FiniteGrassmannCoframe FiniteGrassmannDiracBerezin
open SKEFTHawking.QuantumNetwork

private theorem gaussianWeightedPower (n : ℕ) :
    (∫ x : ℝ, x ^ n * Real.exp (-(x ^ 2 / 2))) =
      Real.sqrt (2 * Real.pi) * ∫ x : ℝ, x ^ n ∂gaussianReal 0 1 := by
  have hd := integral_gaussianReal_eq_integral_smul
    (μ := 0) (v := 1) (f := fun x : ℝ ↦ x ^ n) one_ne_zero
  have hp (x : ℝ) :
      gaussianPDFReal 0 1 x • x ^ n =
        (Real.sqrt (2 * Real.pi))⁻¹ * (x ^ n * Real.exp (-(x ^ 2) / 2)) := by
    simp [gaussianPDFReal, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  simp_rw [hp, integral_const_mul, neg_div] at hd
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  rw [hd, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- Comparison of the Cartesian Gaussian and polar integrals for every coordinate monomial. -/
theorem normalizedSphere_monomial (powers : Fin 4 → ℕ) :
    (∫ q : UnitSphere, ∏ i, q.val i ^ powers i ∂normalizedSphere) =
      ((∏ i, ∫ x : ℝ, x ^ powers i ∂gaussianReal 0 1) * radialGaussianMoment 0) /
        radialGaussianMoment (∑ i, powers i) := by
  let P : Coordinates → ℝ := fun x ↦ ∏ i, x i ^ powers i
  let μ := (volume : Measure Coordinates).toSphere
  have hP (r : ℝ) (q : Coordinates) (_ : 0 < r) (_ : ‖q‖ = 1) :
      P (r • q) = r ^ (∑ i, powers i) * P q := by
    simp only [P, PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  have hdim : Module.finrank ℝ Coordinates - 1 = 3 := by simp
  have hpolar := polar_split P (∑ i, powers i) hP
  rw [hdim, radial_volumeIoiPow, Nat.add_comm 3] at hpolar
  simp_rw [neg_div] at hpolar
  change _ = (∫ q : UnitSphere, P q.val ∂μ) * radialGaussianMoment (∑ i, powers i) at hpolar
  have hcart := gaussInt_monomial powers
  simp_rw [neg_div] at hcart
  change (∫ x : Coordinates, P x * Real.exp (-(‖x‖ ^ 2 / 2))) = _ at hcart
  rw [hpolar] at hcart
  simp_rw [gaussianWeightedPower, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hcart
  have hmass := sphere_polar_one (ι := Fin 4)
  simp_rw [Fintype.card_fin, neg_div] at hmass
  change Real.sqrt (2 * Real.pi) ^ 4 = μ.real univ * radialGaussianMoment 0 at hmass
  rw [hmass] at hcart
  have hμ : μ.real univ ≠ 0 := by
    unfold Measure.real
    exact (ENNReal.toReal_pos
      (fun h ↦ (Measure.toSphere_ne_zero volume)
        (Measure.measure_univ_eq_zero.mp h))
      (IsFiniteMeasure.measure_univ_lt_top (μ := μ)).ne).ne'
  have hn := (radialGaussianMoment_pos (∑ i, powers i)).ne'
  change (∫ q : UnitSphere, P q.val ∂normalizedSphere) = _
  rw [normalizedSphere, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  change (μ.real univ)⁻¹ * (∫ q : UnitSphere, P q.val ∂μ) = _
  field_simp [hμ, hn]
  linear_combination hcart

/-- The same Cartesian-to-polar comparison for quaternion coordinates on actual SU(2). -/
theorem su2Haar_monomial (powers : Fin 4 → ℕ) :
    (∫ A : SU2, ∏ i, coordinates A.val i ^ powers i ∂su2Haar) =
      ((∏ i, ∫ x : ℝ, x ^ powers i ∂gaussianReal 0 1) * radialGaussianMoment 0) /
        radialGaussianMoment (∑ i, powers i) := by
  change (∫ A : SU2, ∏ i, (sphereHomeomorphSU2.symm A).val i ^ powers i ∂su2Haar) = _
  rw [← measurePreserving_sphereHomeomorphSU2.integral_comp
    sphereHomeomorphSU2.measurableEmbedding]
  simpa only [Homeomorph.symm_apply_apply] using normalizedSphere_monomial powers

/-- A monomial with an odd coordinate exponent integrates to zero on SU(2). -/
theorem su2Haar_monomial_of_odd (powers : Fin 4 → ℕ) (i : Fin 4) (hi : Odd (powers i)) :
    (∫ A : SU2, ∏ j, coordinates A.val j ^ powers j ∂su2Haar) = 0 := by
  obtain ⟨k, hk⟩ := hi
  have hz : (∫ x : ℝ, x ^ powers i ∂gaussianReal 0 1) = 0 := by
    rw [hk]
    exact auxiliaryMoment_odd 1 (by norm_num) 1 (by norm_num) k
  rw [su2Haar_monomial, Finset.prod_eq_zero (Finset.mem_univ i) hz, zero_mul, zero_div]

/-- Even powers have the exact factorial moment on SU(2), including degree zero. -/
theorem su2Haar_monomial_even (k : Fin 4 → ℕ) :
    (∫ A : SU2, ∏ i, coordinates A.val i ^ (2 * k i) ∂su2Haar) =
      (∏ i, (((2 * k i).factorial : ℝ) / ((2 : ℝ) ^ k i * (k i).factorial))) /
        ((2 : ℝ) ^ (∑ i, k i) * ((∑ i, k i) + 1).factorial) := by
  rw [su2Haar_monomial, ← Finset.mul_sum, ← div_div_eq_mul_div, radialGaussianMoment_even_ratio]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hm := auxiliaryMoment_even 1 (by norm_num) 1 (by norm_num) (k i)
  norm_num only [one_pow, one_div, inv_pow] at hm
  apply (eq_div_iff (by positivity)).2
  calc
    _ = ((∫ x : ℝ, x ^ (2 * k i) ∂gaussianReal 0 1) * (k i).factorial) *
        (2 : ℝ) ^ k i := by ring
    _ = _ := by rw [hm, mul_assoc, ← mul_pow, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_pow, mul_one]

private theorem oddFactors (k : ℕ) :
    ((2 * k).factorial : ℝ) / ((2 : ℝ) ^ k * k.factorial) =
      ∏ j ∈ Finset.range k, (2 * (j : ℝ) + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ← ih, show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
    field_simp
    ring

private theorem radialFactors (k : ℕ) :
    (2 : ℝ) ^ k * (k + 1).factorial = ∏ j ∈ Finset.range k, (4 + 2 * (j : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ← ih, pow_succ, show k.succ + 1 = (k + 1).succ by omega,
      Nat.factorial_succ]
    push_cast
    ring

/-- The even SU(2) moments written as the two finite products of the quaternion evaluator. -/
theorem su2Haar_monomial_even_products (k : Fin 4 → ℕ) :
    (∫ A : SU2, ∏ i, coordinates A.val i ^ (2 * k i) ∂su2Haar) =
      (∏ i, ∏ j ∈ Finset.range (k i), (2 * (j : ℝ) + 1)) /
        (∏ j ∈ Finset.range (∑ i, k i), (4 + 2 * (j : ℝ))) := by
  rw [su2Haar_monomial_even, radialFactors]
  simp_rw [oddFactors]

end SKEFTHawking.ADW.QuaternionSU2Sphere
