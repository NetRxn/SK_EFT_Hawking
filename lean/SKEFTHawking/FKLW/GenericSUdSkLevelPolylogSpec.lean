/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) polylog level spec SUBSTANTIVE discharge

The **SU(d) generic substantive discharge of `SkLevelPolylog_sud_spec`**
(analog of SU(2) Phase 6u `skLevel_polylog_spec` ~110-LoC proof).

For any K > 0 and ε₀_sud > 0 satisfying the **calibration condition**
`K² · 2·ε₀_sud ≤ 1/4` (cf SU(2) `K_compose² · 2·ε₀ = 1/4`), the polylog
level chooser `skLevel_polylog_sud K ε` achieves `ε_seq K (2·ε₀_sud)
(skLevel_polylog_sud K ε) ≤ ε` for all ε ∈ (0, ε₀_sud].

## Proof outline (same as SU(2), parametric in K)

  - Step 1: ε ≤ ε₀_sud + K²·2·ε₀_sud ≤ 1/4 ⟹ K²·ε ≤ 1/8.
  - Step 2: log(1/(K²·ε)) ≥ log 8 > 0.
  - Step 3: M := log(1/(K²·ε)) / log 4 ≥ 3/2 > 1.
  - Step 4: skLevel_polylog_sud K ε ≥ log M / log(3/2).
  - Step 5: (3/2)^skLevel_polylog ≥ M.
  - Step 6: ε_seq closed form + (1/4)^((3/2)^n) ≤ K²·ε.
  - Step 7: linarith closes.

## Substantive content shipped

  * `skLevel_polylog_sud_spec_holds` — the substantive discharge given
    K > 0 + calibration condition.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — SU(d) polylog level
spec substantive discharge (3rd of 4 substantive ingredients).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkLevelPolylog
import SKEFTHawking.FKLW.EpsilonSeq

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

private lemma log_three_halves_pos : 0 < Real.log (3/2) :=
  Real.log_pos (by norm_num)

private lemma log_four_pos : 0 < Real.log 4 :=
  Real.log_pos (by norm_num)

/-- **SUBSTANTIVE DISCHARGE of `SkLevelPolylog_sud_spec`** given the
calibration condition `K² · 2·ε₀_sud ≤ 1/4`.

For any K > 0 and ε₀_sud > 0 with `K² · 2·ε₀_sud ≤ 1/4`, the polylog
level chooser `skLevel_polylog_sud K ε` achieves
`ε_seq K (2·ε₀_sud) (skLevel_polylog_sud K ε) ≤ ε` for ε ∈ (0, ε₀_sud].

Proof: lifts SU(2) `skLevel_polylog_spec` (Phase 6u SolovayKitaevRecursion)
to generic K via parametric substitution. -/
theorem skLevel_polylog_sud_spec_holds (K ε₀_sud : ℝ)
    (hK_pos : 0 < K) (hε₀_pos : 0 < ε₀_sud)
    (h_cal : K^2 * (2 * ε₀_sud) ≤ 1 / 4) :
    SkLevelPolylog_sud_spec K ε₀_sud := by
  intro ε hε_pos hε_le
  -- Step 1: ε ≤ ε₀_sud ⟹ K²·ε ≤ K²·ε₀_sud ≤ 1/8.
  have h_K_sq_pos : 0 < K^2 := pow_pos hK_pos 2
  have h_K_sq_eps_pos : 0 < K^2 * ε := mul_pos h_K_sq_pos hε_pos
  have h_eps_le_eps₀ : K^2 * ε ≤ K^2 * ε₀_sud :=
    mul_le_mul_of_nonneg_left hε_le h_K_sq_pos.le
  have h_eps₀_le_1_8 : K^2 * ε₀_sud ≤ 1 / 8 := by linarith
  have h_K_eps_le : K^2 * ε ≤ 1 / 8 := le_trans h_eps_le_eps₀ h_eps₀_le_1_8
  have h_inv_K_eps_pos : 0 < 1 / (K^2 * ε) := by positivity
  have h_inv_K_eps_gt_8 : (8 : ℝ) ≤ 1 / (K^2 * ε) := by
    rw [le_div_iff₀ h_K_sq_eps_pos]; linarith
  -- Step 2: log(1/(K²·ε)) ≥ log 8 > 0.
  have h_log_inv : Real.log 8 ≤ Real.log (1 / (K^2 * ε)) :=
    Real.log_le_log (by norm_num) h_inv_K_eps_gt_8
  have h_log_8_pos : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have h_log_inv_pos : 0 < Real.log (1 / (K^2 * ε)) :=
    lt_of_lt_of_le h_log_8_pos h_log_inv
  -- Step 3: M := log(1/(K²·ε)) / log 4 ≥ 3/2 > 1.
  set M : ℝ := Real.log (1 / (K^2 * ε)) / Real.log 4 with hM_def
  have h_M_pos : 0 < M := div_pos h_log_inv_pos log_four_pos
  have h_M_ge : M ≥ 3 / 2 := by
    rw [hM_def, ge_iff_le, le_div_iff₀ log_four_pos]
    have h_log_4_eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 from by norm_num, Real.log_pow]; ring
    have h_log_8_eq : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2^3 from by norm_num, Real.log_pow]; ring
    calc 3 / 2 * Real.log 4
        = 3 / 2 * (2 * Real.log 2) := by rw [h_log_4_eq]
      _ = 3 * Real.log 2 := by ring
      _ = Real.log 8 := h_log_8_eq.symm
      _ ≤ Real.log (1 / (K^2 * ε)) := h_log_inv
  have h_M_gt_one : 1 < M := by linarith
  have h_log_M_pos : 0 < Real.log M := Real.log_pos h_M_gt_one
  -- Step 4: skLevel_polylog_sud K ε ≥ log M / log(3/2).
  set n := skLevel_polylog_sud K ε with hn_def
  have h_n_ge : (n : ℝ) ≥ Real.log M / Real.log (3 / 2) := by
    rw [hn_def]; unfold skLevel_polylog_sud
    exact_mod_cast Nat.le_ceil _
  -- Step 5: (3/2)^n ≥ M.
  have h_rpow_le_pow : (3 / 2 : ℝ) ^ (n : ℝ) = (3 / 2 : ℝ) ^ n :=
    Real.rpow_natCast (3/2) n
  have h_3_2_pow_n_ge : ((3 / 2 : ℝ)) ^ n ≥ M := by
    have h_rpow_mono : (3 / 2 : ℝ) ^ (Real.log M / Real.log (3 / 2)) ≤
        (3 / 2 : ℝ) ^ (n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3 / 2) h_n_ge
    have h_3_2_pow_log_M : (3 / 2 : ℝ) ^ (Real.log M / Real.log (3 / 2)) = M := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3/2)]
      rw [show Real.log (3 / 2) * (Real.log M / Real.log (3 / 2)) = Real.log M from by
        field_simp]
      exact Real.exp_log h_M_pos
    rw [h_3_2_pow_log_M] at h_rpow_mono
    rw [← h_rpow_le_pow]; exact h_rpow_mono
  -- Step 6: ε_seq closed form + (1/4)^((3/2)^n) ≤ K²·ε.
  have h_two_ε₀_pos : 0 < 2 * ε₀_sud := by linarith
  have h_K_sq_two_ε₀ : K^2 * (2 * ε₀_sud) ≤ 1 / 4 := h_cal
  have h_closed := SKEFTHawking.FKLW.EpsilonSeq.ε_seq_closed_form
    K (2 * ε₀_sud) hK_pos h_two_ε₀_pos n
  -- Need ε_seq K (2·ε₀_sud) n ≤ ε, using h_closed:
  -- ε_seq K (2·ε₀_sud) n = (K² · 2·ε₀_sud)^((3/2)^n) / K²
  rw [h_closed]
  rw [div_le_iff₀ h_K_sq_pos]
  -- Goal: (K² · 2·ε₀_sud)^((3/2)^n) ≤ ε · K²
  -- Use: a := K² · 2·ε₀_sud ≤ 1/4 < 1 ⟹ a^x ≤ (1/4)^x for x ≥ 0
  set a := K^2 * (2 * ε₀_sud) with ha_def
  have h_a_pos : 0 < a := by positivity
  have h_a_le_quarter : a ≤ 1 / 4 := h_cal
  have h_quarter_pos : (0 : ℝ) < 1 / 4 := by norm_num
  have h_quarter_lt_one : (1 / 4 : ℝ) < 1 := by norm_num
  have h_quarter_le_one : (1 / 4 : ℝ) ≤ 1 := h_quarter_lt_one.le
  have h_3_2_n_nn : 0 ≤ ((3 / 2 : ℝ)) ^ n := pow_nonneg (by norm_num) n
  -- a^((3/2)^n) ≤ (1/4)^((3/2)^n) since a ≤ 1/4 and (3/2)^n ≥ 0.
  have h_a_pow_le_quarter_pow : a ^ ((3 / 2 : ℝ) ^ n) ≤
      (1 / 4 : ℝ) ^ ((3 / 2 : ℝ) ^ n) :=
    Real.rpow_le_rpow h_a_pos.le h_a_le_quarter h_3_2_n_nn
  -- (1/4)^((3/2)^n) ≤ (1/4)^M (antitone since 1/4 < 1 and (3/2)^n ≥ M)
  have h_rpow_antitone :
      (1 / 4 : ℝ) ^ ((3 / 2 : ℝ) ^ n) ≤ (1 / 4 : ℝ) ^ M :=
    Real.rpow_le_rpow_of_exponent_ge h_quarter_pos h_quarter_le_one h_3_2_pow_n_ge
  -- (1/4)^M ≤ K²·ε (key inequality).
  have h_quarter_M_le : (1 / 4 : ℝ) ^ M ≤ K^2 * ε := by
    rw [Real.rpow_def_of_pos h_quarter_pos]
    have h_log_quarter : Real.log (1 / 4) = -Real.log 4 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
    rw [h_log_quarter]
    rw [show -Real.log 4 * M = -(Real.log 4 * M) by ring]
    have h_M_unfold : Real.log 4 * M = Real.log (1 / (K^2 * ε)) := by
      rw [hM_def]; field_simp
    rw [h_M_unfold]
    rw [show -Real.log (1 / (K^2 * ε)) = Real.log (K^2 * ε) by
      rw [Real.log_div (by norm_num) (ne_of_gt h_K_sq_eps_pos), Real.log_one]
      ring]
    exact (Real.exp_log h_K_sq_eps_pos).le
  -- Chain: a^((3/2)^n) ≤ (1/4)^((3/2)^n) ≤ (1/4)^M ≤ K²·ε.
  have h_chain : a ^ ((3 / 2 : ℝ) ^ n) ≤ K^2 * ε :=
    le_trans (le_trans h_a_pow_le_quarter_pow h_rpow_antitone) h_quarter_M_le
  linarith

end SKEFTHawking.FKLW.GenericSUd
