/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) polylog word-length asymptotic discharge

UNCONDITIONAL discharge of `SkLengthPolylogBound_sud` at the canonical
Dawson-Nielsen exponent `skLengthExponent_sud = log 5 / log (3/2) ≈ 3.97`.

This is the SU(d) generalization of the SU(2) `skLength_at_skLevel_polylog_le`
(`SolovayKitaevLengthBound.lean`), lifted parametrically in the per-alphabet
constants `(baseCase, decompCost)`, the composition constant `K`, the regime
bound `ε₀_sud`, and the headline constant `c`.

## Proof structure (mirrors SU(2))

  * `skLength_sud_le_const_pow_5` : `skLength_sud b d n ≤ (b + d/4) · 5^n`.
  * `M_le_log_inv_ε_sud` : `M ≤ log(1/ε)` where `M := log(1/(K²·ε))/log 4`.
  * `pow_5_skLevel_polylog_le_sud` : `5^(skLevel_polylog_sud K ε) ≤ 5 · M^c`,
    `c = skLengthExponent_sud`, via the change-of-base
    `5^(log M/log(3/2)) = M^(log 5/log(3/2))`.
  * Compose: `skLength_sud(level) ≤ (b+d/4)·5·M^c ≤ 5·(b+d/4)·(log(1/ε))^c ≤
    c_headline · (log(1/ε))^c`.

The regime hypothesis `hcal : K² · (2·ε₀_sud) ≤ 1/4` is exactly the calibration
condition the SU(d) cascade already carries (cf SU(2) `K_compose²·2·ε₀ = 1/4`);
it gives `K²·ε ≤ 1/8` for `ε ≤ ε₀_sud`, hence `log(1/(K²·ε)) ≥ log 8 = 3 log 2`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected (decomposed into private helpers).
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Wave 1" remaining item (a): discharge the polylog asymptotic
`SkLengthPolylogBound_sud` at the corrected exponent. 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkLength
import SKEFTHawking.FKLW.GenericSUdSkLengthExponent
import SKEFTHawking.FKLW.GenericSUdSkLevelPolylog

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

/-! ## 1. Algebraic bound on `skLength_sud` -/

/-- `skLength_sud b d n ≤ (b + d/4) · 5^n` (from the closed form
`b·5^n + d·(5^n - 1)/4`). -/
private lemma skLength_sud_le_const_pow_5
    (baseCase decompCost : ℝ) (hd : 0 ≤ decompCost) (n : ℕ) :
    skLength_sud baseCase decompCost n ≤ (baseCase + decompCost / 4) * (5 : ℝ) ^ n := by
  unfold skLength_sud
  have h5 : (0 : ℝ) ≤ (5 : ℝ) ^ n := by positivity
  nlinarith [h5, hd]

/-! ## 2. `log 4 ≥ 1` helper -/

private lemma one_le_log_four_sud : (1 : ℝ) ≤ Real.log 4 := by
  have h_log_4_eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; ring
  rw [h_log_4_eq]
  have h := Real.log_two_gt_d9
  linarith

/-! ## 3. `K²·ε ≤ 1/8` from the calibration -/

private lemma K_sq_eps_le_eighth
    (K ε ε₀_sud : ℝ) (hε_pos : 0 < ε) (hK_sq : 1 ≤ K ^ 2)
    (hcal : K ^ 2 * (2 * ε₀_sud) ≤ 1 / 4) (hε_le : ε ≤ ε₀_sud) :
    K ^ 2 * ε ≤ 1 / 8 := by
  have hK_sq_pos : 0 < K ^ 2 := by linarith
  have h1 : K ^ 2 * ε ≤ K ^ 2 * ε₀_sud :=
    mul_le_mul_of_nonneg_left hε_le hK_sq_pos.le
  nlinarith [h1, hcal]

/-! ## 4. `M ≤ log(1/ε)` -/

/-- `M := log(1/(K²·ε)) / log 4 ≤ log(1/ε)`, using `log 4 ≥ 1` and `K² ≥ 1`. -/
private lemma M_le_log_inv_ε_sud
    (K ε ε₀_sud : ℝ) (hε_pos : 0 < ε) (hK_sq : 1 ≤ K ^ 2)
    (hcal : K ^ 2 * (2 * ε₀_sud) ≤ 1 / 4) (hε_le : ε ≤ ε₀_sud) :
    Real.log (1 / (K ^ 2 * ε)) / Real.log 4 ≤ Real.log (1 / ε) := by
  have hK_sq_pos : 0 < K ^ 2 := by linarith
  have h_K_sq_eps_pos : 0 < K ^ 2 * ε := mul_pos hK_sq_pos hε_pos
  have h_inv_K_eps_pos : 0 < 1 / (K ^ 2 * ε) := by positivity
  -- 1/(K²·ε) ≤ 1/ε
  have h_inv_le : 1 / (K ^ 2 * ε) ≤ 1 / ε := by
    apply one_div_le_one_div_of_le hε_pos
    calc ε = 1 * ε := (one_mul ε).symm
      _ ≤ K ^ 2 * ε := mul_le_mul_of_nonneg_right hK_sq hε_pos.le
  have h_log_le : Real.log (1 / (K ^ 2 * ε)) ≤ Real.log (1 / ε) :=
    Real.log_le_log h_inv_K_eps_pos h_inv_le
  -- log(1/(K²·ε)) ≥ 0 (since 1/(K²·ε) ≥ 8 ≥ 1)
  have h_K_eps_le : K ^ 2 * ε ≤ 1 / 8 :=
    K_sq_eps_le_eighth K ε ε₀_sud hε_pos hK_sq hcal hε_le
  have h_inv_ge_8 : (8 : ℝ) ≤ 1 / (K ^ 2 * ε) := by
    rw [le_div_iff₀ h_K_sq_eps_pos]; linarith
  have h_log_K_inv_nn : 0 ≤ Real.log (1 / (K ^ 2 * ε)) :=
    Real.log_nonneg (by linarith)
  calc Real.log (1 / (K ^ 2 * ε)) / Real.log 4
      ≤ Real.log (1 / (K ^ 2 * ε)) / 1 := by
          apply div_le_div_of_nonneg_left h_log_K_inv_nn (by norm_num)
          exact one_le_log_four_sud
    _ = Real.log (1 / (K ^ 2 * ε)) := div_one _
    _ ≤ Real.log (1 / ε) := h_log_le

/-! ## 5. `5^(skLevel_polylog_sud K ε) ≤ 5 · M^c` -/

/-- `5^(skLevel_polylog_sud K ε) ≤ 5 · M^skLengthExponent_sud` where
`M := log(1/(K²·ε))/log 4`. Change-of-base `5^(log M/log(3/2)) = M^(log 5/log(3/2))`. -/
private lemma pow_5_skLevel_polylog_le_sud
    (K ε ε₀_sud : ℝ) (hε_pos : 0 < ε) (hK_sq : 1 ≤ K ^ 2)
    (hcal : K ^ 2 * (2 * ε₀_sud) ≤ 1 / 4) (hε_le : ε ≤ ε₀_sud) :
    (5 : ℝ) ^ (skLevel_polylog_sud K ε) ≤
      5 * (Real.log (1 / (K ^ 2 * ε)) / Real.log 4) ^ skLengthExponent_sud := by
  have hK_sq_pos : 0 < K ^ 2 := by linarith
  have h_K_sq_eps_pos : 0 < K ^ 2 * ε := mul_pos hK_sq_pos hε_pos
  have h_K_eps_le : K ^ 2 * ε ≤ 1 / 8 :=
    K_sq_eps_le_eighth K ε ε₀_sud hε_pos hK_sq hcal hε_le
  have h_inv_ge_8 : (8 : ℝ) ≤ 1 / (K ^ 2 * ε) := by
    rw [le_div_iff₀ h_K_sq_eps_pos]; linarith
  have h_log_8_pos : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have h_log_inv_pos : 0 < Real.log (1 / (K ^ 2 * ε)) :=
    lt_of_lt_of_le h_log_8_pos (Real.log_le_log (by norm_num) h_inv_ge_8)
  have h_log_4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set M : ℝ := Real.log (1 / (K ^ 2 * ε)) / Real.log 4 with hM_def
  have h_M_pos : 0 < M := div_pos h_log_inv_pos h_log_4_pos
  -- M ≥ 3/2
  have h_M_ge : (3 : ℝ) / 2 ≤ M := by
    rw [hM_def, le_div_iff₀ h_log_4_pos]
    have h_log_4_eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; ring
    have h_log_8_eq : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow]; ring
    calc 3 / 2 * Real.log 4
        = 3 / 2 * (2 * Real.log 2) := by rw [h_log_4_eq]
      _ = 3 * Real.log 2 := by ring
      _ = Real.log 8 := h_log_8_eq.symm
      _ ≤ Real.log (1 / (K ^ 2 * ε)) :=
          Real.log_le_log (by norm_num) h_inv_ge_8
  have h_M_gt_one : 1 < M := by linarith
  have h_log_M_pos : 0 < Real.log M := Real.log_pos h_M_gt_one
  have h_log_3_2_pos : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  -- level = ⌈log M / log(3/2)⌉₊
  have hlevel_eq : skLevel_polylog_sud K ε = ⌈Real.log M / Real.log (3 / 2)⌉₊ := by
    unfold skLevel_polylog_sud; rw [← hM_def]
  have h_n_le_real :
      ((skLevel_polylog_sud K ε : ℕ) : ℝ) ≤ Real.log M / Real.log (3 / 2) + 1 := by
    rw [hlevel_eq]
    have h_ratio_nn : 0 ≤ Real.log M / Real.log (3 / 2) :=
      div_nonneg h_log_M_pos.le h_log_3_2_pos.le
    exact le_of_lt (Nat.ceil_lt_add_one h_ratio_nn)
  -- 5^(n : ℕ) = (5:ℝ)^((n : ℕ) : ℝ)
  have h_pow_eq : (5 : ℝ) ^ (skLevel_polylog_sud K ε) =
      (5 : ℝ) ^ ((skLevel_polylog_sud K ε : ℕ) : ℝ) :=
    (Real.rpow_natCast 5 (skLevel_polylog_sud K ε)).symm
  have h_rpow_le : (5 : ℝ) ^ ((skLevel_polylog_sud K ε : ℕ) : ℝ) ≤
      (5 : ℝ) ^ (Real.log M / Real.log (3 / 2) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5) h_n_le_real
  have h_split : (5 : ℝ) ^ (Real.log M / Real.log (3 / 2) + 1) =
      5 * (5 : ℝ) ^ (Real.log M / Real.log (3 / 2)) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 5), Real.rpow_one]; ring
  have h_change_base :
      (5 : ℝ) ^ (Real.log M / Real.log (3 / 2)) = M ^ skLengthExponent_sud := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5),
        Real.rpow_def_of_pos h_M_pos]
    congr 1
    unfold skLengthExponent_sud
    field_simp
  rw [h_pow_eq]
  calc (5 : ℝ) ^ ((skLevel_polylog_sud K ε : ℕ) : ℝ)
      ≤ (5 : ℝ) ^ (Real.log M / Real.log (3 / 2) + 1) := h_rpow_le
    _ = 5 * (5 : ℝ) ^ (Real.log M / Real.log (3 / 2)) := h_split
    _ = 5 * M ^ skLengthExponent_sud := by rw [h_change_base]

/-! ## 6. The headline discharge -/

/-- **UNCONDITIONAL discharge of `SkLengthPolylogBound_sud`** at the canonical
Dawson-Nielsen exponent `skLengthExponent_sud = log 5 / log (3/2)`.

Hypotheses: nonneg per-alphabet constants `baseCase, decompCost`; `K² ≥ 1`;
the calibration `K²·(2·ε₀_sud) ≤ 1/4` (the cascade's own condition); and the
headline constant dominates `5·(baseCase + decompCost/4) ≤ c`. -/
theorem skLengthPolylogBound_sud_holds
    (baseCase decompCost ε₀_sud K c : ℝ)
    (hb : 0 ≤ baseCase) (hd : 0 ≤ decompCost)
    (hK_sq : 1 ≤ K ^ 2)
    (hcal : K ^ 2 * (2 * ε₀_sud) ≤ 1 / 4)
    (hc : 5 * (baseCase + decompCost / 4) ≤ c) :
    SkLengthPolylogBound_sud baseCase decompCost ε₀_sud c (skLevel_polylog_sud K) := by
  intro ε hε_pos hε_le
  -- abbreviations
  set C₁ : ℝ := baseCase + decompCost / 4 with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := by rw [hC₁_def]; positivity
  have hK_sq_pos : 0 < K ^ 2 := by linarith
  have h_K_sq_eps_pos : 0 < K ^ 2 * ε := mul_pos hK_sq_pos hε_pos
  -- log(1/ε) > 0 : ε ≤ ε₀_sud and K²·ε ≤ 1/8 with K² ≥ 1 ⟹ ε ≤ 1/8 < 1
  have h_K_eps_le : K ^ 2 * ε ≤ 1 / 8 :=
    K_sq_eps_le_eighth K ε ε₀_sud hε_pos hK_sq hcal hε_le
  have h_ε_lt_one : ε < 1 := by nlinarith [hK_sq, hε_pos, h_K_eps_le]
  have h_inv_ε_gt_one : (1 : ℝ) < 1 / ε := by
    rw [lt_div_iff₀ hε_pos, one_mul]; exact h_ε_lt_one
  have h_log_inv_ε_pos : 0 < Real.log (1 / ε) := Real.log_pos h_inv_ε_gt_one
  have h_log_inv_ε_nn : 0 ≤ Real.log (1 / ε) := h_log_inv_ε_pos.le
  have h_c_pos : 0 < skLengthExponent_sud := skLengthExponent_sud_pos
  -- M and its nonnegativity
  set M : ℝ := Real.log (1 / (K ^ 2 * ε)) / Real.log 4 with hM_def
  have h_log_4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h_inv_ge_8 : (8 : ℝ) ≤ 1 / (K ^ 2 * ε) := by
    rw [le_div_iff₀ h_K_sq_eps_pos]; linarith
  have h_log_inv_pos : 0 < Real.log (1 / (K ^ 2 * ε)) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 8))
      (Real.log_le_log (by norm_num) h_inv_ge_8)
  have h_M_nn : 0 ≤ M := by rw [hM_def]; exact (div_pos h_log_inv_pos h_log_4_pos).le
  -- the three composed pieces
  have h_skLen_le := skLength_sud_le_const_pow_5 baseCase decompCost hd (skLevel_polylog_sud K ε)
  have h_pow_5_le := pow_5_skLevel_polylog_le_sud K ε ε₀_sud hε_pos hK_sq hcal hε_le
  have h_M_le := M_le_log_inv_ε_sud K ε ε₀_sud hε_pos hK_sq hcal hε_le
  have h_M_rpow_le : M ^ skLengthExponent_sud ≤ (Real.log (1 / ε)) ^ skLengthExponent_sud :=
    Real.rpow_le_rpow h_M_nn h_M_le h_c_pos.le
  have h_log_rpow_nn : 0 ≤ (Real.log (1 / ε)) ^ skLengthExponent_sud :=
    Real.rpow_nonneg h_log_inv_ε_nn _
  -- compose
  calc skLength_sud baseCase decompCost (skLevel_polylog_sud K ε)
      ≤ C₁ * (5 : ℝ) ^ (skLevel_polylog_sud K ε) := h_skLen_le
    _ ≤ C₁ * (5 * M ^ skLengthExponent_sud) :=
          mul_le_mul_of_nonneg_left h_pow_5_le hC₁_nn
    _ = (5 * C₁) * M ^ skLengthExponent_sud := by ring
    _ ≤ (5 * C₁) * (Real.log (1 / ε)) ^ skLengthExponent_sud :=
          mul_le_mul_of_nonneg_left h_M_rpow_le (by positivity)
    _ ≤ c * (Real.log (1 / ε)) ^ skLengthExponent_sud :=
          mul_le_mul_of_nonneg_right hc h_log_rpow_nn

end SKEFTHawking.FKLW.GenericSUd
