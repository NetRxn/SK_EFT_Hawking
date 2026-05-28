/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Concrete-radius regime substrate (re-point R0/R1, θ-bound)

The super-quad regime hypothesis `h_regime` (carried by S102's (B) discharge + the
cascade) is stated with the **IFT** `matrixLog d` and the IFT `target` — both
irreducibly existential (`HasStrictFDerivAt.toOpenPartialHomeomorph`, no quantitative
IFT in Mathlib). The concrete-radius Mercator logarithm
(`GenericSUdMatrixMercatorLog.lean`, with the round-trip `exp_matrixMercatorLog` on
the named ball `‖X‖<1`) cannot bridge to the IFT log on a *concrete* ball (the
agreement requires `matrixMercatorLog(Δ−1) ∈ source`, existential — see the Phase 6y
roadmap §"BRICK-3 ARCHITECTURAL FINDING"). The route to an UNCONDITIONAL regime is to
**re-point** `dnStepFG_sud` + the (B) discharge + `h_regime` to
`matrixLogConcrete d Δ := matrixMercatorLog (Δ − 1)`, whose regime conjuncts hold on a
*named* ball. This file ships the concrete regime substrate brick by brick (R0–R4).

## Substantive content shipped (this wave)

  * `regime_thetabound_concrete` — the **θ-bound conjunct, concrete-radius**:
    `‖(-i)·matrixMercatorLog((V⁻¹U).val − 1)‖ ≤ 2·d·‖V − U‖` whenever
    `d·‖V − U‖ ≤ 1/2`. Composes the K=2 Mercator bound
    (`norm_matrixMercatorLog_le_two_mul`, S109) with the SU(d) residual bound
    (`residual_norm_le_d_mul`, S60). This is the concrete-radius analog of the
    existential `regime_thetabound_herm_traceless_on_residual_nhd` (S106).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R0/R1 θ-bound for the
concrete-radius regime.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixMercatorLog
import SKEFTHawking.FKLW.GenericSUdSuperQuadSubstrate

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Concrete-radius regime θ-bound**: for `V, U ∈ SU(d)` with
`d·‖V − U‖ ≤ 1/2`, the concrete Mercator log of the residual satisfies the regime's
θ-bound

  `‖(-i)·matrixMercatorLog((V⁻¹U).val − 1)‖ ≤ 2·d·‖V − U‖`.

Composes the concrete-radius K=2 Lipschitz bound `norm_matrixMercatorLog_le_two_mul`
(S109; the `(-i)` scalar has norm 1) with the SU(d) residual bound
`residual_norm_le_d_mul` (S60; `‖(V⁻¹U).val − 1‖ ≤ d·‖V − U‖`). The hypothesis
`d·‖V − U‖ ≤ 1/2` keeps the residual inside the named ball `‖·‖ ≤ 1/2` where the K=2
bound holds; on the calibration ball `‖V − U‖ ≤ 2·ε₀_sud` (with `ε₀_sud` tiny) this is
automatic. This is the concrete-radius analog of the existential S106 θ-bound — the
first conjunct of the re-pointed (concrete) regime. -/
theorem regime_thetabound_concrete {d : ℕ} [Nonempty (Fin d)]
    (V U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (hVU : (d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 / 2) :
    ‖((-Complex.I) • matrixMercatorLog
        ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1) :
        Matrix (Fin d) (Fin d) ℂ)‖
      ≤ 2 * (d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := by
  have hres := residual_norm_le_d_mul V U
  have hΔm_half : ‖((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1)‖ ≤ 1 / 2 :=
    le_trans hres hVU
  have hmlog := norm_matrixMercatorLog_le_two_mul
    ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1) hΔm_half
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  calc ‖matrixMercatorLog ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1)‖
      ≤ 2 * ‖((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val - 1)‖ := hmlog
    _ ≤ 2 * ((d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖) := by
        linarith [hres]
    _ = 2 * (d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := by ring

end SKEFTHawking.FKLW.GenericSUd
