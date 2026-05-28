/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — concrete-radius Dawson-Nielsen step `dnStepFG_sud_concrete` (re-point R4)

Instantiates the log-agnostic `dnStepFG_fromLog` (S129) at the **concrete-radius** Mercator
logarithm `matrixMercatorLog (Δ.val − 1)` (S109/S118), giving the re-pointed DN step

  `dnStepFG_sud_concrete V_n U := dnStepFG_fromLog (matrixMercatorLog ((V_n⁻¹ U).val − 1))`,

and discharges its `exp(-[F,G]) = Δ` identity **UNCONDITIONALLY on the named calibration
ball** `(n+2)²·‖V_n − U‖ ≤ 1/8`. Whereas the IFT step's exp-delta (`dnStepFG_sud_exp_neg_comm_eq_Delta`,
S84) requires the *existential* hypotheses `Δ ∈ target` + the IFT-log regime conjuncts (the
last blocker to an UNCONDITIONAL `h_regime`), the concrete step needs only the named-ball
bound, because:

  * the round-trip `exp (matrixMercatorLog (Δ−1)) = Δ` holds on `‖Δ−1‖ < 1`
    (`exp_matrixMercatorLog`, S118);
  * the regime conjuncts `‖(-i)·log‖ ≤ 1`, Hermitian, traceless are CONCRETE-RADIUS
    UNCONDITIONAL (`regime_normH_le_one_concrete` S122, `regime_herm_traceless_concrete_sud`
    S127+S128).

This is the **payoff of the R4 factoring**: the concrete DN step's central error-analysis
identity is now hypothesis-free beyond the calibration ball, with no super-quad-chain
duplication (it reuses the generic `dnStepFG_fromLog_exp_neg_comm_eq_Delta`).

## Substantive content shipped

  * `dnStepFG_sud_concrete` — the re-pointed (concrete-log) DN step.
  * `dnStepFG_sud_concrete_exp_neg_comm_eq_Delta` — `exp(-[F,G]) = Δ` UNCONDITIONALLY for
    `(n+2)²·‖V_n − U‖ ≤ 1/8` (named calibration ball).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R4: concrete DN step + its
unconditional exp-delta on the calibration ball.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDnStepFGFromLog
import SKEFTHawking.FKLW.GenericSUdRegimeConcrete

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Concrete-radius SU(d) Dawson-Nielsen step**: the re-pointed DN step using the
concrete Mercator logarithm `matrixMercatorLog (Δ.val − 1)` in place of the existential IFT
`matrixLog (n+2) Δ.val`. Definitionally `dnStepFG_fromLog (matrixMercatorLog ((V_n⁻¹U).val − 1))`.
Its regime conjuncts hold on a *named* ball (S120–S128), so the error analysis is
dischargeable without the existential IFT `target`. -/
noncomputable def dnStepFG_sud_concrete {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    DNStepData_SUd (n + 2) :=
  dnStepFG_fromLog (matrixMercatorLog
    ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1))

/-- **Concrete DN step exp(-[F,G]) = Δ, UNCONDITIONAL on the calibration ball**: for
`V_n, U ∈ SU(n+2)` with `(n+2)²·‖V_n − U‖ ≤ 1/8`,

  `NormedSpace.exp (-([F, G])) = (V_n⁻¹ U).val`

for the concrete DN step `dnStepFG_sud_concrete`. The re-pointed counterpart of S84's
`dnStepFG_sud_exp_neg_comm_eq_Delta`, but **with the existential `Δ ∈ target` hypothesis
eliminated** — replaced by the named-ball bound. Composes the generic
`dnStepFG_fromLog_exp_neg_comm_eq_Delta` with: the concrete round-trip `exp_matrixMercatorLog`
(`exp (mLog (Δ−1)) = 1 + (Δ−1) = Δ`, `‖Δ−1‖ < 1`); `regime_normH_le_one_concrete` (`‖H‖ ≤ 1`);
and `regime_herm_traceless_concrete_sud` (Hermitian ∧ traceless). All smallness bounds follow
from `(n+2)²·‖V_n − U‖ ≤ 1/8` via the residual bound `residual_norm_le_d_mul`. -/
theorem dnStepFG_sud_concrete_exp_neg_comm_eq_Delta {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    (hVU : ((n : ℝ) + 2) ^ 2 *
        ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
          (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 / 8) :
    NormedSpace.exp (-((dnStepFG_sud_concrete V_n U).F * (dnStepFG_sud_concrete V_n U).G -
        (dnStepFG_sud_concrete V_n U).G * (dnStepFG_sud_concrete V_n U).F)) =
      (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val := by
  set Δ : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
    (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val with hΔ
  -- Rewrite the `(d : ℝ)`-form of the regime lemmas as `((n : ℝ) + 2)`.
  have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  have hnn : (0 : ℝ) ≤ ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
      (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ := norm_nonneg _
  have hd1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hdd : (n : ℝ) + 2 ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith [hd1]
  -- d·‖V−U‖ ≤ d²·‖V−U‖ ≤ 1/8.
  have hd_le : ((n : ℝ) + 2) *
      ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
        (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 / 8 :=
    le_trans (mul_le_mul_of_nonneg_right hdd hnn) hVU
  -- ‖Δ − 1‖ ≤ d·‖V−U‖ ≤ 1/8 < 1.
  have hres : ‖Δ - 1‖ ≤ ((n : ℝ) + 2) *
      ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
        (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ := by
    have := residual_norm_le_d_mul V_n U
    rwa [hcast] at this
  have hΔ1 : ‖Δ - 1‖ < 1 := by linarith
  -- d·‖V−U‖ ≤ 1/2 (for the regime θ-bound / ‖H‖≤1 conjunct).
  have hhalf : ((n + 2 : ℕ) : ℝ) *
      ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
        (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 / 2 := by
    rw [hcast]; linarith
  -- (n+2)²·‖V−U‖ ≤ 1/8 in `((n+2 : ℕ) : ℝ)` form (for regime_herm_traceless_concrete_sud).
  have hVU' : ((n + 2 : ℕ) : ℝ) ^ 2 *
      ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
        (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 / 8 := by
    rw [hcast]; exact hVU
  -- Round-trip: exp (matrixMercatorLog (Δ − 1)) = Δ.
  have h_roundtrip : NormedSpace.exp (matrixMercatorLog (Δ - 1)) = Δ := by
    rw [exp_matrixMercatorLog (Δ - 1) hΔ1]; abel
  -- Regime conjuncts at the concrete log.
  have h_herm_tr := regime_herm_traceless_concrete_sud (d := n + 2) V_n U hVU'
  have h_normH := regime_normH_le_one_concrete (d := n + 2) V_n U hhalf
  -- Assemble and apply the generic exp-delta.
  exact dnStepFG_fromLog_exp_neg_comm_eq_Delta (matrixMercatorLog (Δ - 1)) Δ
    ⟨h_normH, h_herm_tr.1, h_herm_tr.2⟩ h_roundtrip

end SKEFTHawking.FKLW.GenericSUd
