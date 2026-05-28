/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — concrete-radius (B) super-quad bound, UNCONDITIONAL (re-point R4 FINAL)

The culmination of the R4 re-point: the super-quad bound for the **concrete** SK recursion
`skApproxC_generic_sud_concrete` (S133), discharged by `Nat.rec` over recursion depth applying
the concrete single-step bound `skApproxC_sud_succ_super_quad_valid_concrete` (S138) at each
level. **The payoff vs. the IFT (B) bound (S102): this version takes NO `h_regime` hypothesis.**

The IFT (B) bound threads `h_regime` (the existential IFT-log Hermitian/traceless/θ-bound on a
neighborhood of `1`) as an undischargeable hypothesis. Here every per-level regime obligation is
discharged **internally** on the named calibration ball:

  * the θ-bound from `regime_thetabound_concrete` (S120) — `‖(-i)·mLog(Δ−1)‖ ≤ 2(m+2)·‖V_n−U‖`,
    valid once `(m+2)·‖V_n−U‖ ≤ 1/2`;
  * the calibration `(m+2)²·‖V_n−U‖ ≤ 1/8` (for the concrete cubic term);

both supplied from the IH `‖V_n−U‖ ≤ ε_k ≤ 2·ε₀_sud` together with the calibration inequalities
`(m+2)·2·ε₀_sud ≤ 1/2` and `(m+2)²·2·ε₀_sud ≤ 1/8` (proved here from
`K_compose_sud_sq_times_two_ε₀_sud` + `K_compose_sud ≥ 1024`). The Hermitian/traceless conjuncts
the keystone needs are already baked into `dnStepFG_sud_concrete` via S122/S127/S128.

## Substantive content shipped

  * `SkApproxCSuperQuadraticBound_generic_sud_concrete` — the predicate (concrete recursion).
  * `two_ε₀_sud_mul_le_half` / `sq_two_ε₀_sud_mul_le_eighth` — the calibration inequalities.
  * `SkApproxCSuperQuadraticBound_generic_sud_concrete_holds` — the **UNCONDITIONAL** (B) bound
    discharge (no `h_regime`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R4 FINAL: the UNCONDITIONAL concrete
(B) bound (eliminates the threaded existential `h_regime`).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSuperQuadInductionConcrete

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Concrete super-quad bound predicate**: the concrete recursion's level-`n` error is bounded
by the super-quadratic sequence `ε_seq K (2·ε₀_sud) n`. Concrete counterpart of
`SkApproxCSuperQuadraticBound_generic_sud` (S44). -/
def SkApproxCSuperQuadraticBound_generic_sud_concrete {m : ℕ}
    (K ε₀_sud : ℝ)
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2)) : Prop :=
  ∀ (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)),
    ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n U) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K (2 * ε₀_sud) n

/-- **Calibration `(m+2)·2·ε₀_sud(m+2) ≤ 1/2`**: needed to discharge the concrete θ-bound's
`(m+2)·‖V_n−U‖ ≤ 1/2` hypothesis (S120) from the IH `‖V_n−U‖ ≤ 2·ε₀_sud`. Since `(m+2) ≤ K` and
`K·2·ε₀_sud = (K²·2·ε₀_sud)/K = (1/4)/K ≤ 1/4096`. -/
lemma two_ε₀_sud_mul_le_half {m : ℕ} :
    ((m : ℝ) + 2) * (2 * ε₀_sud (m + 2)) ≤ 1 / 2 := by
  have hd : 1 ≤ m + 2 := by omega
  have hKpos := K_compose_sud_pos (d := m + 2) hd
  have hKge := K_compose_sud_ge_1024 (d := m + 2) hd
  have h2ε₀_nn : 0 ≤ 2 * ε₀_sud (m + 2) := by have := ε₀_sud_pos (d := m + 2) hd; linarith
  have hsq := K_compose_sud_sq_times_two_ε₀_sud (d := m + 2) hd
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hd_le_K : ((m : ℝ) + 2) ≤ K_compose_sud (m + 2) := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith
    have h16 : ((m : ℝ) + 2) ≤ ((m : ℝ) + 2) ^ 16 := by
      calc ((m : ℝ) + 2) = ((m : ℝ) + 2) ^ 1 := (pow_one _).symm
        _ ≤ ((m : ℝ) + 2) ^ 16 := pow_le_pow_right₀ h1 (by norm_num)
    unfold K_compose_sud; rw [hcast]; nlinarith [h16]
  have hstep1 : ((m : ℝ) + 2) * (2 * ε₀_sud (m + 2)) ≤
      K_compose_sud (m + 2) * (2 * ε₀_sud (m + 2)) :=
    mul_le_mul_of_nonneg_right hd_le_K h2ε₀_nn
  have hKt_le : K_compose_sud (m + 2) * (2 * ε₀_sud (m + 2)) ≤ 1 / 4096 := by
    nlinarith [hsq, hKge, h2ε₀_nn, mul_nonneg (mul_nonneg hKpos.le h2ε₀_nn) (sub_nonneg.mpr hKge)]
  calc ((m : ℝ) + 2) * (2 * ε₀_sud (m + 2))
      ≤ K_compose_sud (m + 2) * (2 * ε₀_sud (m + 2)) := hstep1
    _ ≤ 1 / 4096 := hKt_le
    _ ≤ 1 / 2 := by norm_num

/-- **Calibration `(m+2)²·2·ε₀_sud(m+2) ≤ 1/8`**: needed to discharge the concrete cubic term's
`(m+2)²·‖V_n−U‖ ≤ 1/8` hypothesis (S136/S138) from the IH `‖V_n−U‖ ≤ 2·ε₀_sud`. Since `(m+2)² ≤ K`
and `K·2·ε₀_sud ≤ 1/4096 ≤ 1/8`. -/
lemma sq_two_ε₀_sud_mul_le_eighth {m : ℕ} :
    ((m : ℝ) + 2) ^ 2 * (2 * ε₀_sud (m + 2)) ≤ 1 / 8 := by
  have hd : 1 ≤ m + 2 := by omega
  have hKpos := K_compose_sud_pos (d := m + 2) hd
  have hKge := K_compose_sud_ge_1024 (d := m + 2) hd
  have h2ε₀_nn : 0 ≤ 2 * ε₀_sud (m + 2) := by have := ε₀_sud_pos (d := m + 2) hd; linarith
  have hsq := K_compose_sud_sq_times_two_ε₀_sud (d := m + 2) hd
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hsq_le_K : ((m : ℝ) + 2) ^ 2 ≤ K_compose_sud (m + 2) := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith
    have h16 : ((m : ℝ) + 2) ^ 2 ≤ ((m : ℝ) + 2) ^ 16 :=
      pow_le_pow_right₀ h1 (by norm_num)
    unfold K_compose_sud; rw [hcast]; nlinarith [h16]
  have hstep1 : ((m : ℝ) + 2) ^ 2 * (2 * ε₀_sud (m + 2)) ≤
      K_compose_sud (m + 2) * (2 * ε₀_sud (m + 2)) :=
    mul_le_mul_of_nonneg_right hsq_le_K h2ε₀_nn
  have hKt_le : K_compose_sud (m + 2) * (2 * ε₀_sud (m + 2)) ≤ 1 / 4096 := by
    nlinarith [hsq, hKge, h2ε₀_nn, mul_nonneg (mul_nonneg hKpos.le h2ε₀_nn) (sub_nonneg.mpr hKge)]
  calc ((m : ℝ) + 2) ^ 2 * (2 * ε₀_sud (m + 2))
      ≤ K_compose_sud (m + 2) * (2 * ε₀_sud (m + 2)) := hstep1
    _ ≤ 1 / 4096 := hKt_le
    _ ≤ 1 / 8 := by norm_num

/-- **(B) SUPER-QUAD BOUND DISCHARGE for the concrete recursion — UNCONDITIONAL** (re-point R4
FINAL). The `SkApproxCSuperQuadraticBound_generic_sud_concrete` predicate holds at the
calibration `(K_compose_sud(m+2), ε₀_sud(m+2))`, given **only** the base-finder ε₀-net property —
**no `h_regime` hypothesis**. By induction on recursion depth: base case S134; the inductive step
applies the concrete single-step valid-branch bound `skApproxC_sud_succ_super_quad_valid_concrete`
(S138), with the regime obligations discharged internally — the θ-bound from
`regime_thetabound_concrete` (S120) and the cubic calibration from the IH
(`‖V_n−U‖ ≤ ε_k ≤ 2·ε₀_sud`) + the calibration inequalities `two_ε₀_sud_mul_le_half`,
`sq_two_ε₀_sud_mul_le_eighth`. This eliminates the threaded existential `h_regime` that the IFT
`SkApproxCSuperQuadraticBound_generic_sud_holds` (S102) carries — the payoff of the entire
concrete-radius re-point (S109–S138). -/
theorem SkApproxCSuperQuadraticBound_generic_sud_concrete_holds {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (h_baseFinder : BaseFinder_approximates_within_sud gs baseFinder (2 * ε₀_sud (m + 2))) :
    SkApproxCSuperQuadraticBound_generic_sud_concrete (K_compose_sud (m + 2)) (ε₀_sud (m + 2))
      gs baseFinder h_det_pred := by
  have hK_pos := K_compose_sud_pos (d := m + 2) (by omega)
  have hε₀_pos := ε₀_sud_pos (d := m + 2) (by omega)
  have h2ε₀_pos : 0 < 2 * ε₀_sud (m + 2) := by linarith
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  intro n
  induction n with
  | zero =>
    intro U
    exact skApproxC_generic_sud_concrete_zero_error_bound gs baseFinder h_det_pred
      (K_compose_sud (m + 2)) (ε₀_sud (m + 2)) h_baseFinder U
  | succ k ih =>
    intro U
    rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_succ]
    set ε_k := SKEFTHawking.FKLW.EpsilonSeq.ε_seq (K_compose_sud (m + 2))
      (2 * ε₀_sud (m + 2)) k with hε_k_def
    have hε_k_nn : 0 ≤ ε_k :=
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq_nonneg _ _ hK_pos h2ε₀_pos k
    have hε_k_le : ε_k ≤ 2 * ε₀_sud (m + 2) :=
      ε_seq_K_compose_sud_two_ε₀_sud_le_two_ε₀_sud (d := m + 2) (by omega) k
    have h_V_n_bound : ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred k U) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
          (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ ε_k := ih U
    -- Concrete θ-bound, discharged internally from S120 + the IH (no existential h_regime).
    have h_theta_calib : ((m + 2 : ℕ) : ℝ) *
        ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred k U) :
            ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
            Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
          (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ 1 / 2 := by
      rw [hcast]
      calc ((m : ℝ) + 2) *
            ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred k U) :
                ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
                Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
              (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖
          ≤ ((m : ℝ) + 2) * (2 * ε₀_sud (m + 2)) :=
            mul_le_mul_of_nonneg_left (le_trans h_V_n_bound hε_k_le) (by positivity)
        _ ≤ 1 / 2 := two_ε₀_sud_mul_le_half
    have h_theta_le : ‖((-Complex.I) • matrixMercatorLog
        (((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred k U))⁻¹ * U :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)).val - 1) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ 2 * ((m : ℝ) + 2) * ε_k := by
      have hreg := regime_thetabound_concrete (d := m + 2)
        (gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred k U)) U h_theta_calib
      rw [hcast] at hreg
      exact le_trans hreg (mul_le_mul_of_nonneg_left h_V_n_bound (by positivity))
    have hVU : ((m : ℝ) + 2) ^ 2 *
        ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred k U) :
            ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
            Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
          (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ 1 / 8 := by
      calc ((m : ℝ) + 2) ^ 2 *
            ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred k U) :
                ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
                Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
              (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖
          ≤ ((m : ℝ) + 2) ^ 2 * (2 * ε₀_sud (m + 2)) :=
            mul_le_mul_of_nonneg_left (le_trans h_V_n_bound hε_k_le) (by positivity)
        _ ≤ 1 / 8 := sq_two_ε₀_sud_mul_le_eighth
    exact skApproxC_sud_succ_super_quad_valid_concrete gs baseFinder h_det_pred k U ε_k
      hε_k_nn hε_k_le (delta_le_one_of_eps_le ε_k hε_k_nn hε_k_le) h_theta_le hVU ih

end SKEFTHawking.FKLW.GenericSUd
