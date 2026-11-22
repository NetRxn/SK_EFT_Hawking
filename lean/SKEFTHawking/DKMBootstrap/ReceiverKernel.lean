import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! Scalar Cauchy receiver analysis for Wave 6v.10, equation (29).
This module makes no claim about transfer to a physical correlator. -/

noncomputable section

open MeasureTheory Complex
open scoped NNReal

namespace SKEFTHawking.DKMBootstrap

/-- The normalized scalar receiver uses Mathlib's Cauchy density. -/
abbrev receiverKernel (τ : ℝ≥0) : ℝ → ℝ := ProbabilityTheory.cauchyPDFReal 0 τ

theorem receiverKernel_integrable (τ : ℝ≥0) : Integrable (receiverKernel τ) :=
  ProbabilityTheory.integrable_cauchyPDFReal 0

theorem receiverKernel_integral (τ : ℝ≥0) (hτ : 0 < τ) :
    ∫ x, receiverKernel τ x = 1 :=
  ProbabilityTheory.integral_cauchyPDFReal_eq_one 0 (ne_of_gt hτ)

/-- Complex differentiation at a point away from the pole. -/
theorem receiverPole_complex_hasDerivAt (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun z : ℂ => (z + τ * I)⁻¹ ^ n)
      (-(n : ℂ) * (((x : ℂ) + τ * I)⁻¹ ^ (n + 1))) (x : ℂ) := by
  have hz : (x : ℂ) + τ * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hd := (((hasDerivAt_id ((x : ℂ))).add_const ((τ : ℂ) * I)).inv hz).pow n
  convert hd using 1 <;> try rfl
  change -(n : ℂ) * ((↑x + ↑τ * I)⁻¹ ^ (n + 1)) =
    (n : ℂ) * ((↑x + ↑τ * I)⁻¹ ^ (n - 1)) * (-1 / (↑x + ↑τ * I) ^ 2)
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one, neg_div, one_div, ← inv_pow]
    simp only [pow_succ]
    ring

/-- Restrict the complex derivative to the real axis. -/
theorem receiverPole_hasDerivAt (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y : ℂ) + τ * I)⁻¹ ^ n)
      (-(n : ℂ) * (((x : ℂ) + τ * I)⁻¹ ^ (n + 1))) x :=
  (receiverPole_complex_hasDerivAt τ hτ n x).comp_ofReal

/-- Real projection of the reciprocal powers, with its actual derivative. -/
theorem receiverPole_real_hasDerivAt (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (I * (((y : ℂ) + τ * I)⁻¹ ^ n)).re)
      (-(n : ℝ) * (I * (((x : ℂ) + τ * I)⁻¹ ^ (n + 1))).re) x := by
  have hp := ((receiverPole_complex_hasDerivAt τ hτ n x).const_mul I).real_of_complex
  convert hp using 1
  change -(n : ℝ) * (I * ((↑x + ↑τ * I)⁻¹ ^ (n + 1))).re =
    (I * (-(n : ℂ) * ((↑x + ↑τ * I)⁻¹ ^ (n + 1)))).re
  rw [mul_left_comm I, Complex.mul_re]
  simp

/-- The Cauchy density is the real projection of a single off-axis pole. -/
theorem receiverKernel_eq_pole (τ : ℝ≥0) (x : ℝ) :
    receiverKernel τ x = Real.pi⁻¹ * (I * ((x : ℂ) + (τ : ℝ) * I)⁻¹).re := by
  simp only [receiverKernel, ProbabilityTheory.cauchyPDFReal, sub_zero,
    Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, Complex.inv_im, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add,
    neg_div, neg_neg]
  simp [Complex.normSq, pow_two, div_eq_mul_inv, mul_assoc]

/-- Actual iterated real derivatives of the normalized Cauchy receiver. -/
theorem receiverKernel_iteratedDeriv (τ : ℝ≥0) (hτ : 0 < τ) (k : ℕ) :
    iteratedDeriv k (receiverKernel τ) = fun x : ℝ =>
      ((-1 : ℝ) ^ k * (k.factorial : ℝ) * Real.pi⁻¹) *
        (I * (((x : ℂ) + (τ : ℝ) * I)⁻¹ ^ (k + 1))).re := by
  have ht : 0 < (τ : ℝ) := hτ
  induction k with
  | zero =>
    funext x
    simpa using receiverKernel_eq_pole τ x
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [((receiverPole_real_hasDerivAt (τ : ℝ) ht (k + 1) x).const_mul
      ((-1 : ℝ) ^ k * (k.factorial : ℝ) * Real.pi⁻¹)).deriv]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

/-- Absolute integrability and the order-zero endpoint of equation (29). -/
theorem receiverKernel_order_zero (τ : ℝ≥0) (hτ : 0 < τ) :
    Integrable (fun x => |iteratedDeriv 0 (receiverKernel τ) x|) ∧
      (∫ x, |iteratedDeriv 0 (receiverKernel τ) x|) = 1 := by
  have he : (fun x => |iteratedDeriv 0 (receiverKernel τ) x|) = receiverKernel τ := by
    funext x
    simp only [iteratedDeriv_zero]
    exact abs_of_pos (ProbabilityTheory.cauchyPDF_pos 0 (ne_of_gt hτ) x)
  rw [he]
  exact ⟨receiverKernel_integrable τ, receiverKernel_integral τ hτ⟩

/-- The pole radius retains two reciprocal factors for the Cauchy tail. -/
theorem receiverKernel_deriv_domination (τ : ℝ≥0) (hτ : 0 < τ) (k : ℕ)
    (hk : 1 ≤ k) (x : ℝ) :
    |iteratedDeriv k (receiverKernel τ) x| ≤
      ((k.factorial : ℝ) / (τ : ℝ) ^ k) * receiverKernel τ x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  let z : ℂ := (x : ℂ) + (τ : ℝ) * I
  have ht : 0 < (τ : ℝ) := hτ
  have hr : (τ : ℝ) ≤ ‖z‖ := by
    simpa [z, abs_of_pos ht] using Complex.abs_im_le_norm z
  have hrp : 0 < ‖z‖ := lt_of_lt_of_le ht hr
  have hrs : ‖z‖ ^ 2 = x ^ 2 + (τ : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [z, Complex.normSq, pow_two]
  have hi : ‖z‖⁻¹ ≤ (τ : ℝ)⁻¹ := inv_anti₀ ht hr
  have hp : (‖z‖⁻¹) ^ n ≤ ((τ : ℝ)⁻¹) ^ n :=
    pow_le_pow_left₀ (by positivity) hi n
  have hn : ‖z⁻¹ ^ (1 + n + 1)‖ ≤
      ((τ : ℝ)⁻¹) ^ n * (x ^ 2 + (τ : ℝ) ^ 2)⁻¹ := by
    rw [norm_pow, norm_inv]
    have he : 1 + n + 1 = n + 2 := by omega
    rw [he, pow_add, inv_pow ‖z‖ 2, hrs]
    exact mul_le_mul_of_nonneg_right hp (by positivity)
  rw [receiverKernel_iteratedDeriv τ hτ]
  change |((-1 : ℝ) ^ (1 + n) * ((1 + n).factorial : ℝ) * Real.pi⁻¹) *
    (I * z⁻¹ ^ (1 + n + 1)).re| ≤ _
  rw [abs_mul]
  have hc : |(-1 : ℝ) ^ (1 + n) * ((1 + n).factorial : ℝ) * Real.pi⁻¹| =
      ((1 + n).factorial : ℝ) * Real.pi⁻¹ := by
    simp [abs_mul, abs_pow, abs_of_nonneg (show (0 : ℝ) ≤ ((1 + n).factorial : ℝ) by positivity),
      abs_of_pos (inv_pos.mpr Real.pi_pos)]
  rw [hc]
  calc
    _ ≤ (((1 + n).factorial : ℝ) * Real.pi⁻¹) * ‖I * z⁻¹ ^ (1 + n + 1)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ = (((1 + n).factorial : ℝ) * Real.pi⁻¹) * ‖z⁻¹ ^ (1 + n + 1)‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ (((1 + n).factorial : ℝ) * Real.pi⁻¹) *
        (((τ : ℝ)⁻¹) ^ n * (x ^ 2 + (τ : ℝ) ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by
      simp only [receiverKernel, ProbabilityTheory.cauchyPDFReal, sub_zero]
      rw [pow_add, pow_one, inv_pow]
      field_simp

/-- Every actual scalar receiver derivative is absolutely integrable. -/
theorem receiverKernel_iteratedDeriv_integrable (τ : ℝ≥0) (hτ : 0 < τ) (k : ℕ) :
    Integrable (iteratedDeriv k (receiverKernel τ)) := by
  cases k with
  | zero => simpa using receiverKernel_integrable τ
  | succ n =>
    have hm : AEStronglyMeasurable (iteratedDeriv (n + 1) (receiverKernel τ)) := by
      rw [receiverKernel_iteratedDeriv τ hτ]
      fun_prop
    apply ((receiverKernel_integrable τ).const_mul
      (((n + 1).factorial : ℝ) / (τ : ℝ) ^ (n + 1))).mono' hm
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using
      receiverKernel_deriv_domination τ hτ (n + 1) (by omega) x

/-- Equation (29): the absolute integral of the actual kth real derivative. -/
theorem receiverKernel_iteratedDeriv_integral_abs_le (τ : ℝ≥0) (hτ : 0 < τ) (k : ℕ) :
    (∫ x, |iteratedDeriv k (receiverKernel τ) x|) ≤
      (k.factorial : ℝ) / (τ : ℝ) ^ k := by
  cases k with
  | zero => simpa using le_of_eq (receiverKernel_order_zero τ hτ).2
  | succ n =>
    have hi := (receiverKernel_iteratedDeriv_integrable τ hτ (n + 1)).abs
    calc
      _ ≤ ∫ x, (((n + 1).factorial : ℝ) / (τ : ℝ) ^ (n + 1)) *
          receiverKernel τ x := integral_mono hi
        ((receiverKernel_integrable τ).const_mul _) (fun x =>
          receiverKernel_deriv_domination τ hτ (n + 1) (by omega) x)
      _ = _ := by rw [integral_const_mul, receiverKernel_integral τ hτ, mul_one]

/-- The pole formula supplies differentiability of every actual receiver derivative. -/
theorem receiverKernel_iteratedDeriv_hasDerivAt (τ : ℝ≥0) (hτ : 0 < τ)
    (j : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv j (receiverKernel τ))
      (iteratedDeriv (j + 1) (receiverKernel τ) t) t := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j (receiverKernel τ)) t := by
    rw [receiverKernel_iteratedDeriv τ hτ]
    exact ((receiverPole_real_hasDerivAt (τ : ℝ) hτ (j + 1) t).const_mul
      ((-1 : ℝ) ^ j * (j.factorial : ℝ) * Real.pi⁻¹)).differentiableAt
  simpa only [iteratedDeriv_succ] using hd.hasDerivAt

/-- A translation by at most the scale preserves a common integrable Cauchy tail. -/
theorem receiverKernel_sub_le (τ : ℝ≥0) (hτ : 0 < τ) (t u : ℝ)
    (hu : |u| ≤ (τ : ℝ)) :
    receiverKernel τ (t - u) ≤ 3 * receiverKernel τ t := by
  have ht : 0 < (τ : ℝ) := hτ
  have hu2 : u ^ 2 ≤ (τ : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg u) hu 2
  have hden : t ^ 2 + (τ : ℝ) ^ 2 ≤ 3 * ((t - u) ^ 2 + (τ : ℝ) ^ 2) := by
    nlinarith [sq_nonneg (t - 2 * u), sq_nonneg (t - u)]
  simp only [receiverKernel, ProbabilityTheory.cauchyPDFReal, sub_zero]
  have hd0 : 0 < (t - u) ^ 2 + (τ : ℝ) ^ 2 := by positivity
  have hd1 : 0 < t ^ 2 + (τ : ℝ) ^ 2 := by positivity
  field_simp
  nlinarith [Real.pi_pos]

/-- A first translation estimate obtained on the fixed unit interval. -/
theorem receiverKernel_iteratedDeriv_sub_le (τ : ℝ≥0) (hτ : 0 < τ)
    (j : ℕ) (t s : ℝ) (hs : |s| ≤ (τ : ℝ)) :
    |iteratedDeriv j (receiverKernel τ) (t - s) -
      iteratedDeriv j (receiverKernel τ) t| ≤
      |s| * (3 * (((j + 1).factorial : ℝ) / (τ : ℝ) ^ (j + 1)) *
        receiverKernel τ t) := by
  have hd (a : ℝ) : HasDerivAt
      (fun a : ℝ ↦ iteratedDeriv j (receiverKernel τ) (t - a * s))
      (iteratedDeriv (j + 1) (receiverKernel τ) (t - a * s) * (-s)) a := by
    simpa only [one_mul, Function.comp_def, id_eq] using
      (receiverKernel_iteratedDeriv_hasDerivAt τ hτ j (t - a * s)).comp a
        (((hasDerivAt_id a).mul_const s).const_sub t)
  have hb (a : ℝ) (ha : a ∈ Set.Ico (0 : ℝ) 1) :
      ‖iteratedDeriv (j + 1) (receiverKernel τ) (t - a * s) * (-s)‖ ≤
        |s| * (3 * (((j + 1).factorial : ℝ) / (τ : ℝ) ^ (j + 1)) *
          receiverKernel τ t) := by
    have has : |a * s| ≤ |s| := by
      rw [abs_mul, abs_of_nonneg ha.1]
      exact mul_le_of_le_one_left (abs_nonneg s) ha.2.le
    have hm := (receiverKernel_deriv_domination τ hτ (j + 1) (by omega)
      (t - a * s)).trans (mul_le_mul_of_nonneg_left
        (receiverKernel_sub_le τ hτ t (a * s) (has.trans hs)) (by positivity))
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    nlinarith [mul_le_mul_of_nonneg_right hm (abs_nonneg s)]
  simpa only [one_mul, zero_mul, sub_zero, Real.norm_eq_abs] using
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun a _ ↦ (hd a).hasDerivWithinAt) hb

/-- A quadratic pointwise remainder for either sign of the translation, including zero. -/
theorem receiverKernel_taylor_remainder_abs_le (τ : ℝ≥0) (hτ : 0 < τ)
    (j : ℕ) (t s : ℝ) (hs : |s| ≤ (τ : ℝ)) :
    |iteratedDeriv j (receiverKernel τ) (t - s) -
      iteratedDeriv j (receiverKernel τ) t +
      s * iteratedDeriv (j + 1) (receiverKernel τ) t| ≤
      |s| ^ 2 * (3 * (((j + 2).factorial : ℝ) / (τ : ℝ) ^ (j + 2)) *
        receiverKernel τ t) := by
  let M := 3 * (((j + 2).factorial : ℝ) / (τ : ℝ) ^ (j + 2)) * receiverKernel τ t
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (by positivity)
      (le_of_lt (ProbabilityTheory.cauchyPDF_pos 0 (ne_of_gt hτ) t))
  have hfirst (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
      |iteratedDeriv (j + 1) (receiverKernel τ) (t - a * s) -
        iteratedDeriv (j + 1) (receiverKernel τ) t| ≤ |s| * M := by
    have has : |a * s| ≤ |s| := by
      rw [abs_mul, abs_of_nonneg ha.1]
      exact mul_le_of_le_one_left (abs_nonneg s) ha.2
    have he := receiverKernel_iteratedDeriv_sub_le τ hτ (j + 1) t (a * s)
      (has.trans hs)
    exact he.trans (mul_le_mul_of_nonneg_right has hM)
  have hd (a : ℝ) : HasDerivAt
      (fun a : ℝ ↦ iteratedDeriv j (receiverKernel τ) (t - a * s) -
        iteratedDeriv j (receiverKernel τ) t +
        a * s * iteratedDeriv (j + 1) (receiverKernel τ) t)
      (s * (iteratedDeriv (j + 1) (receiverKernel τ) t -
        iteratedDeriv (j + 1) (receiverKernel τ) (t - a * s))) a := by
    have hc := (receiverKernel_iteratedDeriv_hasDerivAt τ hτ j (t - a * s)).comp a
      (((hasDerivAt_id a).mul_const s).const_sub t)
    convert (hc.sub_const (iteratedDeriv j (receiverKernel τ) t)).add
      (((hasDerivAt_id a).mul_const s).mul_const
        (iteratedDeriv (j + 1) (receiverKernel τ) t)) using 1 <;>
      first | rfl | ring
  have hb (a : ℝ) (ha : a ∈ Set.Ico (0 : ℝ) 1) :
      ‖s * (iteratedDeriv (j + 1) (receiverKernel τ) t -
        iteratedDeriv (j + 1) (receiverKernel τ) (t - a * s))‖ ≤ |s| ^ 2 * M := by
    rw [Real.norm_eq_abs, abs_mul, abs_sub_comm]
    calc
      _ ≤ |s| * (|s| * M) :=
        mul_le_mul_of_nonneg_left (hfirst a ⟨ha.1, ha.2.le⟩) (abs_nonneg s)
      _ = _ := by ring
  simpa only [one_mul, zero_mul, sub_zero, sub_self, zero_add, Real.norm_eq_abs] using
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun a _ ↦ (hd a).hasDerivWithinAt) hb

/-- The actual Taylor remainder is integrable, for every real shift. -/
theorem receiverKernel_taylor_remainder_integrable (τ : ℝ≥0) (hτ : 0 < τ)
    (j : ℕ) (s : ℝ) :
    Integrable (fun t ↦ iteratedDeriv j (receiverKernel τ) (t - s) -
      iteratedDeriv j (receiverKernel τ) t +
      s * iteratedDeriv (j + 1) (receiverKernel τ) t) := by
  exact (((receiverKernel_iteratedDeriv_integrable τ hτ j).comp_sub_right s).sub
    (receiverKernel_iteratedDeriv_integrable τ hτ j)).add
      ((receiverKernel_iteratedDeriv_integrable τ hτ (j + 1)).const_mul s)

/-- Local quantitative L¹ Taylor control of the actual Cauchy derivatives.
The two unit-interval estimates apply to all real shifts with `|s| ≤ τ`. -/
theorem receiverKernel_taylor_remainder_integral_abs_le (τ : ℝ≥0) (hτ : 0 < τ)
    (j : ℕ) (s : ℝ) (hs : |s| ≤ (τ : ℝ)) :
    (∫ t, |iteratedDeriv j (receiverKernel τ) (t - s) -
      iteratedDeriv j (receiverKernel τ) t +
      s * iteratedDeriv (j + 1) (receiverKernel τ) t|) ≤
      3 * |s| ^ 2 * (((j + 2).factorial : ℝ) / (τ : ℝ) ^ (j + 2)) := by
  have hi := (receiverKernel_taylor_remainder_integrable τ hτ j s).abs
  calc
    _ ≤ ∫ t, (|s| ^ 2 * (3 * (((j + 2).factorial : ℝ) /
        (τ : ℝ) ^ (j + 2)))) * receiverKernel τ t :=
      integral_mono hi ((receiverKernel_integrable τ).const_mul _) (fun t ↦ by
        simpa only [mul_assoc] using receiverKernel_taylor_remainder_abs_le τ hτ j t s hs)
    _ = _ := by
      rw [integral_const_mul, receiverKernel_integral τ hτ, mul_one]
      ring

end SKEFTHawking.DKMBootstrap
