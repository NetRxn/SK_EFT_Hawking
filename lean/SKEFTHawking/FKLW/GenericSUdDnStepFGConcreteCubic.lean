/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — concrete-radius dnStep group-commutator cubic remainder (re-point R4)

Re-pointed counterpart of `dnStepFG_sud_gC_minus_Delta_norm_le_cubic` (S86): for the
**concrete** DN step `dnStepFG_sud_concrete` (S130) with `‖F‖, ‖G‖ ≤ δ ≤ 1`, the group
commutator of `exp(iF), exp(iG)` approximates the residual Δ to cubic order:

  `‖groupCommutator(expIsud F, expIsud G) − Δ.val‖ ≤ 320·δ³`.

The crucial improvement over S86 is the hypotheses: S86 requires the existential-radius
`h_regime3` (IFT-log Hermitian/traceless/`‖H‖≤1`) **and** `Δ.val ∈ target`; this concrete
version needs **only the named calibration bound** `(n+2)²·‖V_n − U‖ ≤ 1/8`, because it
composes the dimension-generic BCH cubic remainder with the UNCONDITIONAL concrete
exp-delta `dnStepFG_sud_concrete_exp_neg_comm_eq_Delta` (S130) — the existential `target`
wall is gone. This is the re-pointed recursion's error-contraction step.

## Substantive content shipped

  * `dnStepFG_sud_concrete_gC_minus_Delta_norm_le_cubic` — `‖gC(expIsud F, expIsud G) − Δ‖
    ≤ 320·δ³` on the named calibration ball (no `h_regime3`, no `target`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R4: concrete dnStep cubic
remainder (re-pointed super-quad error-contraction step).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDnStepFGConcrete
import SKEFTHawking.FKLW.GenericSUdDnStepFGCubic

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix
open SKEFTHawking.FKLW.GroupCommutator

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Concrete dnStep group-commutator cubic remainder, on the named calibration ball**:
for `V_n, U ∈ SU(n+2)` with `(n+2)²·‖V_n − U‖ ≤ 1/8` and the concrete-step witnesses with
`‖F‖, ‖G‖ ≤ δ ≤ 1`,

  `‖groupCommutator(expIsud F, expIsud G) − Δ.val‖ ≤ 320·δ³`.

Re-pointed counterpart of S86, with the existential `h_regime3` + `Δ ∈ target` hypotheses
ELIMINATED — composes the dimension-generic BCH cubic remainder
`groupCommutator_lie_bracket_cubic_remainder` with the UNCONDITIONAL concrete exp-delta
`dnStepFG_sud_concrete_exp_neg_comm_eq_Delta` (S130). -/
lemma dnStepFG_sud_concrete_gC_minus_Delta_norm_le_cubic {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    (hVU : ((n : ℝ) + 2) ^ 2 *
        ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
          (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 / 8)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (hF_norm : ‖(dnStepFG_sud_concrete V_n U).F‖ ≤ δ)
    (hG_norm : ‖(dnStepFG_sud_concrete V_n U).G‖ ≤ δ) :
    ‖(groupCommutator
        ((expIsud n (dnStepFG_sud_concrete V_n U).F (dnStepFG_sud_concrete V_n U).hF_herm
            (dnStepFG_sud_concrete V_n U).hF_tr :
            ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
        ((expIsud n (dnStepFG_sud_concrete V_n U).G (dnStepFG_sud_concrete V_n U).hG_herm
            (dnStepFG_sud_concrete V_n U).hG_tr :
            ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)) -
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val‖ ≤ 320 * δ ^ 3 := by
  rw [expIsud_val, expIsud_val]
  have h_bch := groupCommutator_lie_bracket_cubic_remainder δ hδ_nn hδ_le_one
    (dnStepFG_sud_concrete V_n U).F (dnStepFG_sud_concrete V_n U).G hF_norm hG_norm
  have h_exp_eq_Δ := dnStepFG_sud_concrete_exp_neg_comm_eq_Delta V_n U hVU
  rw [← h_exp_eq_Δ]
  exact h_bch

end SKEFTHawking.FKLW.GenericSUd
