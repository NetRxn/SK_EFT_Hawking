/-
# Phase 5q.H — K7 residual (a): the outward chart flow on the punctured-torus collar

The deformation device of the puncture Mayer–Vietoris: a per-ball outward radial flow in the
`τ`-centered charts of `KummerPuncturedTorus`, glued over the 16 disjoint excised balls into a
global homotopy `F : ℝ × T⁴ → T⁴` with

* `F 1 = id`, `F` fixes every point outside the open chart balls (in particular all of `T⁴°`),
* `F` preserves each closed chart ball, moves chart radii monotonically outward
  (`r ↦ max(r, min(ρ, (2−s)·r))`, `ρ = 1/2`), and at `s = 0` pushes the collar
  `r ∈ [ρ/2, ρ]` onto the boundary sphere `r = ρ`.

Mirrors the K7 `weldFlow` (`KummerWeldFiberFlow`) one level down: the same
`min(·, 2−s)`-profile, with the junk-value-total formula and a squeeze for continuity at the
center. Consumed by `KummerPuncturedMV` to deformation-retract the thickened complement onto
`T⁴°` and the collar annuli onto the chart spheres.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerPuncturedTorus

namespace SKEFTHawking.KummerPunctureFlow

open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerPuncturedTorus

noncomputable section

/-! ## §1. The radial profile -/

/-- The chart norm. -/
def nrm (t : ℝ × ℝ × ℝ × ℝ) : ℝ := Real.sqrt (sqNorm t)

theorem nrm_nonneg (t : ℝ × ℝ × ℝ × ℝ) : 0 ≤ nrm t := Real.sqrt_nonneg _

theorem nrm_sq (t : ℝ × ℝ × ℝ × ℝ) : nrm t ^ 2 = sqNorm t :=
  Real.sq_sqrt (sqNorm_nonneg t)

theorem nrm_continuous : Continuous nrm :=
  Real.continuous_sqrt.comp sqNorm_continuous

/-- The outward radial factor `λ(s, r) = max(1, min(ρ/r, 2−s))` (junk-total at `r = 0`). -/
def lam (s r : ℝ) : ℝ := max 1 (min ((1 / 2) / r) (2 - s))

theorem lam_one_le (s r : ℝ) : 1 ≤ lam s r := le_max_left _ _

theorem lam_le_two {s r : ℝ} (hs : 0 ≤ s) : lam s r ≤ 2 := by
  rw [lam]
  refine max_le (by norm_num) (le_trans (min_le_right _ _) (by linarith))

/-- At `s = 1` the factor is `1` (the identity time). -/
theorem lam_at_one (r : ℝ) (hr : 0 ≤ r) : lam 1 r = 1 := by
  rw [lam]
  rcases eq_or_lt_of_le hr with h0 | h0
  · rw [← h0]
    norm_num
  · rcases le_total r (1 / 2) with hle | hle
    · have h1 : (1 : ℝ) ≤ (1 / 2) / r := (le_div_iff₀ h0).mpr (by linarith)
      rw [show (2 : ℝ) - 1 = 1 by norm_num, min_eq_right (by linarith), max_eq_left le_rfl]
    · have h1 : (1 / 2 : ℝ) / r ≤ 1 := (div_le_one h0).mpr (by linarith)
      rw [min_eq_left (by linarith), max_eq_left h1]

/-- Outside the ball (`r ≥ ρ`) the factor is `1` at every time. -/
theorem lam_of_ge {s r : ℝ} (hs : s ≤ 1) (hr : 1 / 2 ≤ r) : lam s r = 1 := by
  have h0 : (0 : ℝ) < r := by linarith
  have h1 : (1 / 2 : ℝ) / r ≤ 1 := (div_le_one h0).mpr hr
  rw [lam, min_eq_left (by linarith), max_eq_left h1]

/-- At `s = 0` the collar radii `r ∈ [ρ/2, ρ]` land exactly on the sphere: `λ(0,r)·r = ρ`. -/
theorem lam_at_zero_mul {r : ℝ} (hlo : 1 / 4 ≤ r) (hhi : r ≤ 1 / 2) :
    lam 0 r * r = 1 / 2 := by
  have h0 : (0 : ℝ) < r := by linarith
  have h1 : (1 / 2 : ℝ) / r ≤ 2 := by
    rw [div_le_iff₀ h0]
    linarith
  have h2 : (1 : ℝ) ≤ (1 / 2) / r := (le_div_iff₀ h0).mpr (by linarith)
  rw [lam, sub_zero, min_eq_left h1, max_eq_right h2, div_mul_cancel₀]
  linarith

/-- The flowed radius never shrinks. -/
theorem le_lam_mul {s r : ℝ} (hr : 0 ≤ r) : r ≤ lam s r * r := by
  nlinarith [lam_one_le s r, hr]

/-- The flowed radius stays `≤ max(r, ρ)`. -/
theorem lam_mul_le {s r : ℝ} (_hs : 0 ≤ s) (hr : 0 ≤ r) : lam s r * r ≤ max r (1 / 2) := by
  rcases eq_or_lt_of_le hr with h0 | h0
  · rw [← h0, mul_zero]
    exact le_max_of_le_right (by norm_num)
  · rw [lam]
    rcases le_total ((1 / 2 : ℝ) / r) (2 - s) with hm | hm
    · rw [min_eq_left hm]
      rcases le_total ((1 / 2 : ℝ) / r) 1 with h1 | h1
      · rw [max_eq_left h1, one_mul]
        exact le_max_left _ _
      · rw [max_eq_right h1, div_mul_cancel₀ _ (ne_of_gt h0)]
        exact le_max_right _ _
    · rw [min_eq_right hm]
      rcases le_total ((2 : ℝ) - s) 1 with h1 | h1
      · rw [max_eq_left h1, one_mul]
        exact le_max_left _ _
      · rw [max_eq_right h1]
        refine le_max_of_le_right ?_
        calc (2 - s) * r ≤ ((1 / 2) / r) * r := by nlinarith
          _ = 1 / 2 := div_mul_cancel₀ _ (ne_of_gt h0)

/-! ## §2. The chart-domain scale map and its continuity -/

/-- The scaled chart point. -/
def scaleMap (s : ℝ) (t : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ := lam s (nrm t) • t

theorem scaleMap_apply (s : ℝ) (t : ℝ × ℝ × ℝ × ℝ) :
    scaleMap s t = (lam s (nrm t) * t.1, lam s (nrm t) * t.2.1,
      lam s (nrm t) * t.2.2.1, lam s (nrm t) * t.2.2.2) := rfl

/-- The scaled chart point's squared norm: `sqNorm (scale) = λ² · sqNorm`. -/
theorem sqNorm_scaleMap (s : ℝ) (t : ℝ × ℝ × ℝ × ℝ) :
    sqNorm (scaleMap s t) = lam s (nrm t) ^ 2 * sqNorm t := by
  rw [scaleMap_apply]
  simp only [sqNorm]
  ring

/-- The scaled norm is `λ · nrm`. -/
theorem nrm_scaleMap (s : ℝ) (t : ℝ × ℝ × ℝ × ℝ) :
    nrm (scaleMap s t) = lam s (nrm t) * nrm t := by
  rw [nrm, sqNorm_scaleMap, show lam s (nrm t) ^ 2 * sqNorm t
      = (lam s (nrm t) * nrm t) ^ 2 by rw [mul_pow, nrm_sq],
    Real.sqrt_sq (mul_nonneg (by linarith [lam_one_le s (nrm t)]) (nrm_nonneg t))]

/-- `scaleMap 1 = id` on the closed chart domain. -/
theorem scaleMap_at_one {t : ℝ × ℝ × ℝ × ℝ} : scaleMap 1 t = t := by
  rw [scaleMap, lam_at_one _ (nrm_nonneg t), one_smul]

/-- `scaleMap` fixes the sphere and beyond. -/
theorem scaleMap_of_ge {s : ℝ} (hs : s ≤ 1) {t : ℝ × ℝ × ℝ × ℝ} (ht : 1 / 2 ≤ nrm t) :
    scaleMap s t = t := by
  rw [scaleMap, lam_of_ge hs ht, one_smul]

/-- **Continuity of the scale map** (jointly; squeeze at the center). -/
theorem scaleMap_continuousOn :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ × ℝ × ℝ) => scaleMap p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  rw [Metric.continuousOn_iff]
  intro p hp ε hε
  by_cases hp0 : p.2 = 0
  · -- squeeze: `‖scale q‖ ≤ 2‖q.2‖`, and the value at `p` is `0`
    refine ⟨ε / 4, by positivity, fun q hq hdist => ?_⟩
    have hq0 : dist q.2 p.2 < ε / 4 := lt_of_le_of_lt (le_trans (le_max_right _ _)
      (le_of_eq (Prod.dist_eq (x := q) (y := p)).symm)) hdist
    rw [hp0, dist_eq_norm, sub_zero] at hq0
    have hval : scaleMap p.1 p.2 = 0 := by
      rw [hp0, scaleMap, smul_zero]
    rw [hval, dist_eq_norm, sub_zero]
    have hbound : ‖scaleMap q.1 q.2‖ ≤ 2 * ‖q.2‖ := by
      have hl1 : 1 ≤ lam q.1 (nrm q.2) := lam_one_le _ _
      have hl2 : lam q.1 (nrm q.2) ≤ 2 := lam_le_two hq.1.1
      calc ‖scaleMap q.1 q.2‖ = ‖lam q.1 (nrm q.2) • q.2‖ := rfl
        _ = |lam q.1 (nrm q.2)| * ‖q.2‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 2 * ‖q.2‖ := by
            have : |lam q.1 (nrm q.2)| = lam q.1 (nrm q.2) := abs_of_pos (by linarith)
            rw [this]
            exact mul_le_mul_of_nonneg_right hl2 (norm_nonneg _)
    calc ‖scaleMap q.1 q.2‖ ≤ 2 * ‖q.2‖ := hbound
      _ < 2 * (ε / 4) := by linarith
      _ < ε := by linarith
  · -- ordinary continuity away from the center
    have hnrm0 : nrm p.2 ≠ 0 := by
      refine ne_of_gt (Real.sqrt_pos.mpr ?_)
      rcases lt_or_eq_of_le (sqNorm_nonneg p.2) with h | h
      · exact h
      · exfalso
        apply hp0
        have h1 := h.symm
        simp only [sqNorm] at h1
        have hs1 := sq_nonneg p.2.1
        have hs2 := sq_nonneg p.2.2.1
        have hs3 := sq_nonneg p.2.2.2.1
        have hs4 := sq_nonneg p.2.2.2.2
        have e1 : p.2.1 = 0 := by nlinarith
        have e2 : p.2.2.1 = 0 := by nlinarith
        have e3 : p.2.2.2.1 = 0 := by nlinarith
        have e4 : p.2.2.2.2 = 0 := by nlinarith
        exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))
    have hdiv : ContinuousAt (fun q : ℝ × (ℝ × ℝ × ℝ × ℝ) => (1 / 2 : ℝ) / nrm q.2) p :=
      ContinuousAt.div continuousAt_const
        ((nrm_continuous.comp continuous_snd).continuousAt) hnrm0
    have hsub : ContinuousAt (fun q : ℝ × (ℝ × ℝ × ℝ × ℝ) => (2 : ℝ) - q.1) p :=
      (continuous_const.sub continuous_fst).continuousAt
    have h1 : ContinuousAt (fun q : ℝ × (ℝ × ℝ × ℝ × ℝ) => lam q.1 (nrm q.2)) p :=
      Filter.Tendsto.max tendsto_const_nhds (Filter.Tendsto.min hdiv hsub)
    have hCA : ContinuousAt (fun q : ℝ × (ℝ × ℝ × ℝ × ℝ) => scaleMap q.1 q.2) p :=
      (h1.smul continuous_snd.continuousAt : _)
    have hcont := hCA.continuousWithinAt
      (s := Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (ℝ × ℝ × ℝ × ℝ)))
    rw [Metric.continuousWithinAt_iff] at hcont
    exact hcont ε hε

end

end SKEFTHawking.KummerPunctureFlow
