/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — concrete-radius super-quad induction substrate (re-point R4)

The first bricks of the super-quad induction re-pointed onto the concrete-radius SK
recursion `skApproxC_generic_sud_concrete` (S133). These mirror the IFT-log induction
substrate (`GenericSUdSuperQuadInduction.lean`, S89–S102) with `skApproxC_generic_sud` →
`skApproxC_generic_sud_concrete` and `dnStepFG_sud` → `dnStepFG_sud_concrete`:

  * the **base case** (level-0 error ≤ `ε_seq … 0 = 2·ε₀`) is log-agnostic — depends only on
    the base finder — so it is a verbatim copy;
  * the **polynomial F/G-norm bounds** (`‖F‖, ‖G‖ ≤ (n+2)⁴·√(θ/2)`) compose the concrete
    F/G-norm bound (S131, `≤ K_F·√(θ/2)`) with `K_F ≤ (n+2)⁴` (S90) — `θ = ‖(-i)·mLog(Δ−1)‖`.

These feed the concrete single-step super-quad bound (the remaining inductive-step brick),
whose regime ingredients (θ-bound S120, exp-delta S130, cubic S132) are all available on the
named calibration ball with no `Δ ∈ target` hypothesis.

## Substantive content shipped

  * `skApproxC_generic_sud_concrete_zero_error_bound` — base-case error bound.
  * `dnStepFG_sud_concrete_F_norm_le_poly` / `_G_norm_le_poly` — `(n+2)⁴·√(θ/2)` form.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R4: concrete super-quad
induction substrate (base case + polynomial norm bounds).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkApproxCConcrete
import SKEFTHawking.FKLW.GenericSUdDnStepFGFromLogNormBound
import SKEFTHawking.FKLW.GenericSUdSuperQuadInduction

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Concrete recursion base-case error bound**: the level-0 concrete approximation is within
`ε_seq K (2·ε₀) 0 = 2·ε₀` of the target. Log-agnostic (depends only on the base finder);
verbatim concrete counterpart of `skApproxC_generic_sud_zero_error_bound` (S89). -/
lemma skApproxC_generic_sud_concrete_zero_error_bound {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (K ε₀ : ℝ)
    (h_baseFinder : BaseFinder_approximates_within_sud gs baseFinder (2 * ε₀))
    (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
    ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred 0 U) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K (2 * ε₀) 0 := by
  rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_zero, skApproxC_generic_sud_concrete_zero]
  exact (h_baseFinder U).le

/-- **Concrete polynomial F-norm bound**: `‖(dnStepFG_sud_concrete V_n U).F‖ ≤ (n+2)⁴·√(θ/2)`
with `θ = ‖(-i)·matrixMercatorLog ((V_n⁻¹U).val − 1)‖`. Composes the concrete F-norm bound
(S131, `≤ K_F·√(θ/2)`) with `K_F ≤ (n+2)⁴` (S90). Concrete counterpart of
`dnStepFG_sud_F_norm_le_poly`. -/
lemma dnStepFG_sud_concrete_F_norm_le_poly {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    ‖(dnStepFG_sud_concrete V_n U).F‖ ≤ ((n : ℝ) + 2) ^ 4 *
      Real.sqrt (‖((-Complex.I) • matrixMercatorLog
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ / 2) := by
  refine le_trans (dnStepFG_sud_concrete_F_norm_le V_n U) ?_
  exact mul_le_mul_of_nonneg_right (dnStepFG_sud_K_F_le n) (Real.sqrt_nonneg _)

/-- **Concrete polynomial G-norm bound** (mirror of F). -/
lemma dnStepFG_sud_concrete_G_norm_le_poly {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    ‖(dnStepFG_sud_concrete V_n U).G‖ ≤ ((n : ℝ) + 2) ^ 4 *
      Real.sqrt (‖((-Complex.I) • matrixMercatorLog
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ / 2) := by
  refine le_trans (dnStepFG_sud_concrete_G_norm_le V_n U) ?_
  exact mul_le_mul_of_nonneg_right (dnStepFG_sud_K_F_le n) (Real.sqrt_nonneg _)

/-- **Concrete F-norm in √ε form**: given the concrete θ-bound
`‖(-i)·matrixMercatorLog(Δ−1)‖ ≤ 2(n+2)·ε`, `‖(dnStepFG_sud_concrete V_n U).F‖ ≤ (n+2)^5·√ε`.
Concrete counterpart of `dnStepFG_sud_F_norm_le_sqrt_eps` (S100): composes the concrete poly
norm `(n+2)^4·√(θ/2)` with `√(θ/2) ≤ (n+2)·√ε` (the `√(n+2) ≤ n+2` step). The `hδ_le` input
shape required by the (concrete) super-quad numeric chain. The θ-bound hypothesis is itself
dischargeable on the calibration ball from `regime_thetabound_concrete` (S120) + the IH. -/
lemma dnStepFG_sud_concrete_F_norm_le_sqrt_eps {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) (ε : ℝ)
    (h_theta_le : ‖((-Complex.I) • matrixMercatorLog
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 2 * ((n : ℝ) + 2) * ε) :
    ‖(dnStepFG_sud_concrete V_n U).F‖ ≤ ((n : ℝ) + 2) ^ 5 * Real.sqrt ε := by
  have hd_ge_one : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  refine le_trans (dnStepFG_sud_concrete_F_norm_le_poly V_n U) ?_
  set θ := ‖((-Complex.I) • matrixMercatorLog
    ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ with hθ_def
  have h_sqrt_d_le : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 2 by linarith),
      Real.sqrt_nonneg ((n : ℝ) + 2), sq_nonneg (Real.sqrt ((n : ℝ) + 2) - 1)]
  have h_sqrt_half : Real.sqrt (θ / 2) ≤ ((n : ℝ) + 2) * Real.sqrt ε := by
    calc Real.sqrt (θ / 2)
        ≤ Real.sqrt (((n : ℝ) + 2) * ε) := Real.sqrt_le_sqrt (by linarith [h_theta_le])
      _ = Real.sqrt ((n : ℝ) + 2) * Real.sqrt ε := Real.sqrt_mul (by linarith) ε
      _ ≤ ((n : ℝ) + 2) * Real.sqrt ε :=
          mul_le_mul_of_nonneg_right h_sqrt_d_le (Real.sqrt_nonneg ε)
  calc ((n : ℝ) + 2) ^ 4 * Real.sqrt (θ / 2)
      ≤ ((n : ℝ) + 2) ^ 4 * (((n : ℝ) + 2) * Real.sqrt ε) :=
        mul_le_mul_of_nonneg_left h_sqrt_half (by positivity)
    _ = ((n : ℝ) + 2) ^ 5 * Real.sqrt ε := by ring

/-- **Concrete G-norm in √ε form** (mirror of F). -/
lemma dnStepFG_sud_concrete_G_norm_le_sqrt_eps {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) (ε : ℝ)
    (h_theta_le : ‖((-Complex.I) • matrixMercatorLog
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 2 * ((n : ℝ) + 2) * ε) :
    ‖(dnStepFG_sud_concrete V_n U).G‖ ≤ ((n : ℝ) + 2) ^ 5 * Real.sqrt ε := by
  have hd_ge_one : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  refine le_trans (dnStepFG_sud_concrete_G_norm_le_poly V_n U) ?_
  set θ := ‖((-Complex.I) • matrixMercatorLog
    ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ with hθ_def
  have h_sqrt_d_le : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 2 by linarith),
      Real.sqrt_nonneg ((n : ℝ) + 2), sq_nonneg (Real.sqrt ((n : ℝ) + 2) - 1)]
  have h_sqrt_half : Real.sqrt (θ / 2) ≤ ((n : ℝ) + 2) * Real.sqrt ε := by
    calc Real.sqrt (θ / 2)
        ≤ Real.sqrt (((n : ℝ) + 2) * ε) := Real.sqrt_le_sqrt (by linarith [h_theta_le])
      _ = Real.sqrt ((n : ℝ) + 2) * Real.sqrt ε := Real.sqrt_mul (by linarith) ε
      _ ≤ ((n : ℝ) + 2) * Real.sqrt ε :=
          mul_le_mul_of_nonneg_right h_sqrt_d_le (Real.sqrt_nonneg ε)
  calc ((n : ℝ) + 2) ^ 4 * Real.sqrt (θ / 2)
      ≤ ((n : ℝ) + 2) ^ 4 * (((n : ℝ) + 2) * Real.sqrt ε) :=
        mul_le_mul_of_nonneg_left h_sqrt_half (by positivity)
    _ = ((n : ℝ) + 2) ^ 5 * Real.sqrt ε := by ring

end SKEFTHawking.FKLW.GenericSUd
