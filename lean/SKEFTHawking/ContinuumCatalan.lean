import Mathlib
import SKEFTHawking.GammaStirling

/-!
# Continuum (Γ-interpolated) Catalan asymptotic — Phase 6a Wave 7C (deliverable 3)

The faithful real-`A` Verlinde dimension is the analytic continuation of the Catalan/singlet
count via `Real.Gamma`:
`continuumLogCatalan x = log Γ(2x+1) − log Γ(x+1) − log Γ(x+2)`  (= log of `Γ(2x+1)/(Γ(x+1)Γ(x+2))`).

This module proves its `O(1/x)` asymptotic
`continuumLogCatalan x = 2x·log 2 − (3/2)·log x − ½·log π + O(1/x)`
**given** the `Real.Gamma` Stirling-with-remainder (built kernel-pure in `GammaStirling.lean`,
passed here as a hypothesis `hΓ` to keep this module independent of that build):
- `continuumLogCatalan_isBigO_of hΓ` — the headline, parameterized by the Gamma asymptotic.
- `sPart_combo_isBigO` — the GammaStirling-INDEPENDENT analytic core: the Stirling principal parts
  combine to the Catalan principal part up to `O(1/x)` (pure `log(1+t) = t + O(t²)` expansions).

`sPart` here is definitionally `GammaStirling.stirlingPart`; the two are bridged at integration.
Kernel-pure; Mathlib-only (no project imports) so it builds without the in-flight GammaStirling.
-/

namespace SKEFTHawking
namespace ContinuumCatalan

open Real Filter Asymptotics Topology

/-- The Stirling principal part `(y − ½)·log y − y + ½·log(2π)` (= `GammaStirling.stirlingPart`). -/
noncomputable def sPart (y : ℝ) : ℝ :=
  (y - 1 / 2) * Real.log y - y + (1 / 2) * Real.log (2 * Real.pi)

/-- Continuum (Γ-interpolated) log-Catalan: `log Γ(2x+1) − log Γ(x+1) − log Γ(x+2)`. -/
noncomputable def continuumLogCatalan (x : ℝ) : ℝ :=
  Real.log (Real.Gamma (2 * x + 1)) - Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma (x + 2))

/-- Per-term `O(1/x)` estimate for a Stirling cross-term: `(α x + β)·log(1+γ/x) − α γ = O(1/x)`.
Two-sided `γ/(x+γ) ≤ log(1+γ/x) ≤ γ/x` (from `Real.log_le_sub_one_of_pos`). -/
private lemma hterm (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) :
    (fun x : ℝ => (α * x + β) * Real.log (1 + γ / x) - α * γ) =O[atTop] (fun x : ℝ => 1 / x) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨β * γ + |γ * (β - α * γ)|, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop (max 1 γ)] with x hx
  have hx1 : 1 < x := lt_of_le_of_lt (le_max_left 1 γ) hx
  have hxγ : γ < x := lt_of_le_of_lt (le_max_right 1 γ) hx
  have hx0 : 0 < x := lt_trans one_pos hx1
  have hxγ0 : 0 < x + γ := by linarith
  have h1gx : 0 < 1 + γ / x := by positivity
  have hcoef : 0 < α * x + β := by positivity
  -- upper log bound
  have hupper : Real.log (1 + γ / x) ≤ γ / x := by
    have := Real.log_le_sub_one_of_pos h1gx
    linarith
  -- lower log bound
  have hlower : γ / (x + γ) ≤ Real.log (1 + γ / x) := by
    have hpos : (0 : ℝ) < 1 / (1 + γ / x) := by positivity
    have hl := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div one_ne_zero (ne_of_gt h1gx), Real.log_one] at hl
    have hval : (1 : ℝ) / (1 + γ / x) - 1 = -(γ / (x + γ)) := by
      field_simp
      ring
    rw [hval] at hl
    linarith
  -- upper assembly
  have hub : (α * x + β) * Real.log (1 + γ / x) - α * γ ≤ β * γ / x := by
    have hm := mul_le_mul_of_nonneg_left hupper hcoef.le
    have he : (α * x + β) * (γ / x) = α * γ + β * γ / x := by
      field_simp
    nlinarith [hm, he]
  -- lower assembly
  have hlb : γ * (β - α * γ) / (x + γ) ≤ (α * x + β) * Real.log (1 + γ / x) - α * γ := by
    have hm := mul_le_mul_of_nonneg_left hlower hcoef.le
    have he : (α * x + β) * (γ / (x + γ)) - α * γ = γ * (β - α * γ) / (x + γ) := by
      field_simp
      ring
    nlinarith [hm, he]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 1 / x by positivity),
    abs_le]
  constructor
  · -- lower side: -((βγ+|A|)*(1/x)) ≤ term - αγ
    have hAle : -(|γ * (β - α * γ)|) / x ≤ γ * (β - α * γ) / (x + γ) := by
      rw [le_div_iff₀ hxγ0, div_mul_eq_mul_div, div_le_iff₀ hx0]
      nlinarith [le_abs_self (γ * (β - α * γ)), neg_abs_le (γ * (β - α * γ)),
        abs_nonneg (γ * (β - α * γ)), hx0, hγ]
    have hbridge : -((β * γ + |γ * (β - α * γ)|) * (1 / x)) ≤ -(|γ * (β - α * γ)|) / x := by
      rw [neg_div, mul_one_div, neg_le_neg_iff]
      gcongr
      linarith [mul_pos hβ hγ]
    calc -((β * γ + |γ * (β - α * γ)|) * (1 / x))
        ≤ -(|γ * (β - α * γ)|) / x := hbridge
      _ ≤ γ * (β - α * γ) / (x + γ) := hAle
      _ ≤ (α * x + β) * Real.log (1 + γ / x) - α * γ := hlb
  · -- upper side: term - αγ ≤ (βγ+|A|)*(1/x)
    have hbridge : β * γ / x ≤ (β * γ + |γ * (β - α * γ)|) * (1 / x) := by
      rw [mul_one_div]
      gcongr
      linarith [abs_nonneg (γ * (β - α * γ))]
    linarith [hub, hbridge]

/-- **Analytic core (GammaStirling-independent).** The Stirling principal parts of the three Γ
factors combine to the Catalan principal part `2x·log2 − (3/2)·log x − ½·log π` up to `O(1/x)`.
Pure real-analysis: `log(2x+1) = log2 + log x + log(1+1/(2x))` etc. with `log(1+t) = t + O(t²)`;
the `log 2` and `log x` coefficients give `2x·log2` and `−3/2·log x` exactly, and the constant
`+2 − ½log(2π)` plus the first-order cross terms collapse to `−½log π + O(1/x)`. -/
theorem sPart_combo_isBigO :
    (fun x : ℝ => (sPart (2 * x + 1) - sPart (x + 1) - sPart (x + 2))
        - (2 * x * Real.log 2 - (3 / 2) * Real.log x - (1 / 2) * Real.log Real.pi))
      =O[atTop] (fun x : ℝ => 1 / x) := by
  have h1 := hterm 2 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 := hterm 1 (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
  have h3 := hterm 1 (3 / 2) 2 (by norm_num) (by norm_num) (by norm_num)
  have hsum := (h1.sub h2).sub h3
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [Filter.eventually_gt_atTop 0] with x hx
  have hx2 : 0 < 2 * x := by linarith
  have hxne : x ≠ 0 := hx.ne'
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have hp1 : (0 : ℝ) < 1 + 1 / 2 / x := by positivity
  have hp2 : (0 : ℝ) < 1 + 1 / x := by positivity
  have hp3 : (0 : ℝ) < 1 + 2 / x := by positivity
  -- log splits (valid for x > 0)
  have hl1 : Real.log (2 * x + 1) = Real.log 2 + Real.log x + Real.log (1 + 1 / 2 / x) := by
    have hfac : 2 * x + 1 = 2 * x * (1 + 1 / 2 / x) := by
      field_simp
    rw [hfac, Real.log_mul hx2.ne' hp1.ne', Real.log_mul h2ne hxne]
  have hl2 : Real.log (x + 1) = Real.log x + Real.log (1 + 1 / x) := by
    have hfac : x + 1 = x * (1 + 1 / x) := by
      field_simp
    rw [hfac, Real.log_mul hxne hp2.ne']
  have hl3 : Real.log (x + 2) = Real.log x + Real.log (1 + 2 / x) := by
    have hfac : x + 2 = x * (1 + 2 / x) := by
      field_simp
    rw [hfac, Real.log_mul hxne hp3.ne']
  have hl2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul h2ne Real.pi_ne_zero
  unfold sPart
  rw [hl1, hl2, hl3, hl2pi]
  ring

/-- **Continuum log-Catalan asymptotic (deliverable 3), parameterized by the Γ Stirling rate.**
Given `hΓ : log Γ(y) − sPart y = O(1/y)`, the continuum log-Catalan matches the Catalan principal
part to `O(1/x)`. Decomposes as `[continuumLogCatalan − sPart-combo] + [sPart-combo − target]`:
the first is three copies of `hΓ` (at `2x+1, x+1, x+2`), the second is `sPart_combo_isBigO`. -/
theorem continuumLogCatalan_isBigO_of
    (hΓ : (fun y : ℝ => Real.log (Real.Gamma y) - sPart y) =O[atTop] (fun y : ℝ => 1 / y)) :
    (fun x : ℝ => continuumLogCatalan x
        - (2 * x * Real.log 2 - (3 / 2) * Real.log x - (1 / 2) * Real.log Real.pi))
      =O[atTop] (fun x : ℝ => 1 / x) := by
  -- `1/(x+c) = O(1/x)` and `1/(2x+1) = O(1/x)`
  have hbigO : ∀ c : ℝ, 0 ≤ c → (fun x : ℝ => 1 / (x + c)) =O[atTop] (fun x : ℝ => 1 / x) := by
    intro c hc
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (x + c)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / x), one_mul]
    exact one_div_le_one_div_of_le hx (by linarith)
  have hbigO2 : (fun x : ℝ => 1 / (2 * x + 1)) =O[atTop] (fun x : ℝ => 1 / x) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * x + 1)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / x), one_mul]
    exact one_div_le_one_div_of_le hx (by linarith)
  -- the three arguments tend to atTop
  have ht2 : Tendsto (fun x : ℝ => 2 * x + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 (Filter.tendsto_id.const_mul_atTop (by norm_num))
  have ht1 : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 Filter.tendsto_id
  have ht1' : Tendsto (fun x : ℝ => x + 2) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 2 Filter.tendsto_id
  -- three copies of hΓ
  have hP1 : (fun x : ℝ => Real.log (Real.Gamma (2 * x + 1)) - sPart (2 * x + 1))
      =O[atTop] (fun x : ℝ => 1 / x) := (hΓ.comp_tendsto ht2).trans hbigO2
  have hP2 : (fun x : ℝ => Real.log (Real.Gamma (x + 1)) - sPart (x + 1))
      =O[atTop] (fun x : ℝ => 1 / x) := (hΓ.comp_tendsto ht1).trans (hbigO 1 (by norm_num))
  have hP3 : (fun x : ℝ => Real.log (Real.Gamma (x + 2)) - sPart (x + 2))
      =O[atTop] (fun x : ℝ => 1 / x) := (hΓ.comp_tendsto ht1').trans (hbigO 2 (by norm_num))
  have hcombo := sPart_combo_isBigO
  have heq : (fun x : ℝ => continuumLogCatalan x
        - (2 * x * Real.log 2 - (3 / 2) * Real.log x - (1 / 2) * Real.log Real.pi))
      = (fun x : ℝ =>
          (Real.log (Real.Gamma (2 * x + 1)) - sPart (2 * x + 1))
            - (Real.log (Real.Gamma (x + 1)) - sPart (x + 1))
            - (Real.log (Real.Gamma (x + 2)) - sPart (x + 2))
          + ((sPart (2 * x + 1) - sPart (x + 1) - sPart (x + 2))
              - (2 * x * Real.log 2 - (3 / 2) * Real.log x - (1 / 2) * Real.log Real.pi))) := by
    funext x
    unfold continuumLogCatalan
    ring
  rw [heq]
  exact ((hP1.sub hP2).sub hP3).add hcombo

/-- **Continuum log-Catalan asymptotic (deliverable 3), unconditional.** The committed `Real.Gamma`
Stirling rate `GammaStirling.logGamma_sub_stirlingPart_isBigO` discharges the `hΓ` hypothesis of
`continuumLogCatalan_isBigO_of` (note `sPart` is definitionally `GammaStirling.stirlingPart`). -/
theorem continuumLogCatalan_isBigO :
    (fun x : ℝ => continuumLogCatalan x
        - (2 * x * Real.log 2 - (3 / 2) * Real.log x - (1 / 2) * Real.log Real.pi))
      =O[atTop] (fun x : ℝ => 1 / x) := by
  apply continuumLogCatalan_isBigO_of
  have hbridge : sPart = GammaStirling.stirlingPart := by
    funext y
    unfold sPart GammaStirling.stirlingPart
    rfl
  rw [hbridge]
  exact GammaStirling.logGamma_sub_stirlingPart_isBigO

end ContinuumCatalan
end SKEFTHawking
