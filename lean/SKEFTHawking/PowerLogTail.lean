import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact logarithm-weighted power tails above positive unit radius. -/
namespace SKEFTHawking.PowerLogTail
open MeasureTheory Filter Set
open scoped Topology

noncomputable def primitive (d x : ℝ) : ℝ := x ^ (-d) * (Real.log x / d + 1 / d^2)

/-- A decreasing antiderivative of the logarithm-weighted power. -/
theorem primitive_hasDerivAt {d x : ℝ} (hd : 0 < d) (hx : 0 < x) :
    HasDerivAt (primitive d) (-Real.log x * x ^ (-d-1)) x := by
  have h := (Real.hasDerivAt_rpow_const (p := -d) (Or.inl hx.ne')).mul
    (((Real.hasDerivAt_log hx.ne').div_const d).add_const (1/d^2))
  convert h using 1 <;> first | rfl | (rw [Real.rpow_sub hx, Real.rpow_one]; field_simp; ring)

/-- The explicit primitive vanishes at infinity for every strictly positive decay exponent. -/
theorem primitive_tendsto {d : ℝ} (hd : 0 < d) : Tendsto (primitive d) atTop (𝓝 0) := by
  have hl := (isLittleO_log_rpow_atTop hd).tendsto_div_nhds_zero
  have hp := tendsto_rpow_neg_atTop hd
  have h := (hl.div_const d).add (hp.div_const (d^2))
  simp only [zero_div,zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold primitive
  rw [Real.rpow_neg hx.le]
  ring

/-- Integrability is established before using the improper integral identity. -/
theorem log_power_integrable {d R : ℝ} (hd : 0 < d) (hR : 1 ≤ R) :
    IntegrableOn (fun x : ℝ => Real.log x * x ^ (-d-1)) (Ioi R) := by
  have hi := integrableOn_Ioi_deriv_of_nonpos'
    (fun x (hx : x ∈ Ici R) => primitive_hasDerivAt hd (lt_of_lt_of_le zero_lt_one (hR.trans hx)))
    (fun x (hx : x ∈ Ioi R) => by
      have hlog : 0 ≤ Real.log x := Real.log_nonneg (hR.trans (le_of_lt hx))
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) (Real.rpow_nonneg ((zero_le_one.trans hR).trans (le_of_lt hx)) _))
    (primitive_tendsto hd)
  have hn := hi.neg
  change IntegrableOn (fun x : ℝ => -(-Real.log x * x ^ (-d-1))) (Ioi R) at hn
  simpa only [neg_mul,neg_neg] using hn

/-- Exact tail integral with the logarithmic and inverse-square gap terms retained. -/
theorem integral_log_power {d R : ℝ} (hd : 0 < d) (hR : 1 ≤ R) :
    (∫ x : ℝ in Ioi R, Real.log x * x ^ (-d-1)) =
      R ^ (-d) * (Real.log R / d + 1 / d^2) := by
  have hi := integral_Ioi_of_hasDerivAt_of_nonpos'
    (fun x (hx : x ∈ Ici R) => primitive_hasDerivAt hd (lt_of_lt_of_le zero_lt_one (hR.trans hx)))
    (fun x (hx : x ∈ Ioi R) => by
      have hlog : 0 ≤ Real.log x := Real.log_nonneg (hR.trans (le_of_lt hx))
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) (Real.rpow_nonneg ((zero_le_one.trans hR).trans (le_of_lt hx)) _))
    (primitive_tendsto hd)
  simp only [neg_mul,integral_neg,zero_sub] at hi
  exact neg_injective hi

theorem integral_log_power_one {d : ℝ} (hd : 0 < d) :
    (∫ x : ℝ in Ioi 1, Real.log x * x ^ (-d-1)) = 1 / d^2 := by
  simpa using integral_log_power hd (le_refl (1 : ℝ))

end SKEFTHawking.PowerLogTail
