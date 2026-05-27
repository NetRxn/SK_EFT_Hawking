/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2e — Matrix log of SU(d) element is traceless (local)

For `h ∈ SU(d)` sufficiently close to `1`, the matrix logarithm
`matrixLog d h` is **traceless** (`trace = 0`). Combined with S.2c
(skew-Hermitian preservation), this proves `matrixLog d h ∈ 𝔰𝔲(d)` on
a nbhd of `1` — the substrate Phase 6y's S.2g discharge needs.

## Mathematical content

For `h ∈ SU(d)` near `1`:

  1. Let `Y := matrixLog d h`, with `exp Y = h` and `Y ∈ source`.
  2. By S.2c (`matrixLog_isSkewHermitian_on_nhd_one`): `Y` is skew-Hermitian.
  3. By S.2d Jacobi (`det_exp_skewHermitian`): `det(exp Y) = exp(tr Y)`.
  4. `det h = 1` (since `h ∈ SU(d)`), so `exp(tr Y) = 1`.
  5. For `Y` near 0, `tr Y` is also near 0. Combined with
     `exp(tr Y) = 1 ⟹ tr Y ∈ 2πi · ℤ`, we conclude `tr Y = 0`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2e (traceless preservation).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixLogSkewHerm
import SKEFTHawking.FKLW.GenericSUdDetExpSkewHerm
import SKEFTHawking.FKLW.GenericSUdTraceNorm
import SKEFTHawking.FKLW.GenericSUdMatrixLogLipschitz

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. exp(tr Y) = 1 when Y = matrixLog of SU(d) element

For h ∈ SU(d) ∩ target, det(h) = 1, so by Jacobi for skew-Hermitian Y =
matrixLog d h (with Y skew-Hermitian by S.2c), exp(tr Y) = 1. -/

/-- **`exp(tr Y) = 1` when `Y = matrixLog d h` for `h ∈ SU(d)` near 1**.

Combines `Matrix.det_of_mem_unitary` + Jacobi formula
`det_exp_skewHermitian` + S.2c skew-Hermitian preservation. -/
theorem exp_trace_matrixLog_eq_one_on_nhd_one (d : ℕ) :
    ∃ V ∈ nhds (1 : Matrix (Fin d) (Fin d) ℂ),
      ∀ h ∈ V, h ∈ Matrix.specialUnitaryGroup (Fin d) ℂ →
        h ∈ (expAmbientPartialHomeo d).target →
        Complex.exp (matrixLog d h).trace = 1 := by
  -- Use the S.2c nbhd
  obtain ⟨V, hV_nhd, hV_skewHerm⟩ := matrixLog_isSkewHermitian_on_nhd_one d
  refine ⟨V, hV_nhd, ?_⟩
  intro h hh_V hh_su hh_target
  set Y := matrixLog d h with hY_def
  have hY_skewHerm : Y.IsSkewHermitian := hV_skewHerm h hh_V hh_su hh_target
  -- exp Y = h.
  have hexp_Y : NormedSpace.exp Y = h := expAmbient_matrixLog d hh_target
  -- det(exp Y) = exp(tr Y) by Jacobi.
  have h_jacobi : (NormedSpace.exp Y).det = Complex.exp Y.trace :=
    det_exp_skewHermitian Y hY_skewHerm
  -- det h = 1 since h ∈ SU(d).
  have h_det_one : h.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hh_su).2
  -- exp(tr Y) = det(exp Y) = det h = 1.
  rw [hexp_Y, h_det_one] at h_jacobi
  exact h_jacobi.symm

/-! ## 2. Helper: norm of integer multiple of 2π·I in ℂ -/

/-- For `n : ℤ`, `‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |n| * (2 * Real.pi)`. -/
theorem norm_int_mul_two_pi_I (n : ℤ) :
    ‖((n : ℂ) * (2 * Real.pi * Complex.I))‖ = (|n| : ℝ) * (2 * Real.pi) := by
  rw [norm_mul]
  rw [Complex.norm_intCast]
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  -- ‖2 * π * I‖ = ‖(2 * π : ℂ)‖ * ‖I‖ = 2π * 1 = 2π
  have h_norm_2piI : ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one]
    rw [show ((2 : ℂ) * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real]
    exact abs_of_pos h2pi_pos
  rw [h_norm_2piI]

/-! ## 3. Full traceless conclusion (substantive) -/

/-- **Matrix log of unitary near 1 is traceless** (substantive headline).

For `h ∈ SU(d)` in a sufficiently small neighborhood of `1`,
`(matrixLog d h).trace = 0`. -/
theorem matrixLog_trace_eq_zero_on_nhd_one (d : ℕ) [Nonempty (Fin d)]
    (hd_pos : 0 < d) :
    ∃ V ∈ nhds (1 : Matrix (Fin d) (Fin d) ℂ),
      ∀ h ∈ V, h ∈ Matrix.specialUnitaryGroup (Fin d) ℂ →
        h ∈ (expAmbientPartialHomeo d).target →
        (matrixLog d h).trace = 0 := by
  obtain ⟨V₁, hV₁_nhd, hV₁_exp_one⟩ := exp_trace_matrixLog_eq_one_on_nhd_one d
  set r : ℝ := 2 * Real.pi / d with hr_def
  have hd_pos_real : (0 : ℝ) < d := by exact_mod_cast hd_pos
  have hr_pos : 0 < r := div_pos (by positivity) hd_pos_real
  -- {h | ‖matrixLog d h‖ < r} is a nbhd of 1 by continuity.
  obtain ⟨δ, hδ_pos, hδ_subset⟩ :=
    matrixLog_smallness_on_nhd_one d hr_pos
  -- Convert h ∈ Metric.ball 1 δ to a nbhd predicate.
  have h_ball_nhd : Metric.ball (1 : Matrix (Fin d) (Fin d) ℂ) δ ∈
      nhds (1 : Matrix (Fin d) (Fin d) ℂ) := Metric.ball_mem_nhds 1 hδ_pos
  have h_target_nhd := expAmbientPartialHomeo_target_mem_nhds_one d
  have h_smallNorm_nhd :
      {h : Matrix (Fin d) (Fin d) ℂ |
        ‖h - 1‖ < δ ∧ h ∈ (expAmbientPartialHomeo d).target} ∈
        nhds (1 : Matrix (Fin d) (Fin d) ℂ) := by
    filter_upwards [h_ball_nhd, h_target_nhd] with h h_in_ball h_in_target
    refine ⟨?_, h_in_target⟩
    rwa [Metric.mem_ball, dist_eq_norm] at h_in_ball
  refine ⟨V₁ ∩ _, Filter.inter_mem hV₁_nhd h_smallNorm_nhd, ?_⟩
  intro h hh_V hh_su hh_target
  obtain ⟨hh_V₁, hh_dist, _⟩ := hh_V
  have hh_norm : ‖matrixLog d h‖ < r := hδ_subset h hh_dist hh_target
  have h_exp_one : Complex.exp (matrixLog d h).trace = 1 :=
    hV₁_exp_one h hh_V₁ hh_su hh_target
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h_exp_one
  -- ‖tr Y‖ ≤ d · ‖Y‖ < d · r = 2π.
  have h_trace_bound : ‖(matrixLog d h).trace‖ < 2 * Real.pi := by
    calc ‖(matrixLog d h).trace‖
        ≤ (d : ℝ) * ‖matrixLog d h‖ := norm_trace_le_dim_mul_norm _
      _ < (d : ℝ) * r := mul_lt_mul_of_pos_left hh_norm hd_pos_real
      _ = 2 * Real.pi := by rw [hr_def]; field_simp
  -- ‖n · 2π·I‖ = |n| · 2π via helper.
  rw [hn] at h_trace_bound
  rw [norm_int_mul_two_pi_I] at h_trace_bound
  -- |n| · 2π < 2π ⟹ |n| < 1.
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_abs_n_lt : (|n| : ℝ) < 1 := by
    by_contra h_neg
    push_neg at h_neg
    -- h_neg : 1 ≤ (|n| : ℝ)
    have h_ge : (1 : ℝ) * (2 * Real.pi) ≤ (|n| : ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right h_neg (le_of_lt h2pi_pos)
    linarith
  -- |n| : ℝ < 1 implies |n| : ℤ < 1, which gives n = 0.
  have h_abs_int_lt : (|n| : ℤ) < 1 := by exact_mod_cast h_abs_n_lt
  have h_n_zero : n = 0 := Int.abs_lt_one_iff.mp h_abs_int_lt
  rw [hn, h_n_zero]; push_cast; ring

/-! ## 4. Combined: matrixLog ∈ 𝔰𝔲(d) on nbhd of 1

Composes S.2c (skew-Hermitian preservation) + S.2e PROPER (traceless
preservation) to give: for h ∈ SU(d) sufficiently close to 1, the
local matrix log `matrixLog d h` is both skew-Hermitian AND traceless,
i.e., it lies in the traceless skew-Hermitian Lie algebra `𝔰𝔲(d)`. -/

/-- **Matrix log of unitary near 1 is in `𝔰𝔲(d)`** (combined headline).

For `h ∈ SU(d)` in a sufficiently small neighborhood of `1`, the local
matrix log `Y := matrixLog d h` satisfies BOTH `Y.IsSkewHermitian` AND
`Y.trace = 0` — i.e., `Y ∈ 𝔰𝔲(d)`. This is the **substrate Phase 6y
S.2g final discharge needs**: matrixLog of SU(d) elements gives back
the Lie algebra. -/
theorem matrixLog_in_su_d_on_nhd_one (d : ℕ) [Nonempty (Fin d)]
    (hd_pos : 0 < d) :
    ∃ V ∈ nhds (1 : Matrix (Fin d) (Fin d) ℂ),
      ∀ h ∈ V, h ∈ Matrix.specialUnitaryGroup (Fin d) ℂ →
        h ∈ (expAmbientPartialHomeo d).target →
        (matrixLog d h).IsSkewHermitian ∧ (matrixLog d h).trace = 0 := by
  obtain ⟨V_sh, hV_sh_nhd, hV_sh⟩ := matrixLog_isSkewHermitian_on_nhd_one d
  obtain ⟨V_tr, hV_tr_nhd, hV_tr⟩ := matrixLog_trace_eq_zero_on_nhd_one d hd_pos
  refine ⟨V_sh ∩ V_tr, Filter.inter_mem hV_sh_nhd hV_tr_nhd, ?_⟩
  intro h hh_V hh_su hh_target
  exact ⟨hV_sh h hh_V.1 hh_su hh_target, hV_tr h hh_V.2 hh_su hh_target⟩

end SKEFTHawking.FKLW.GenericSUd
