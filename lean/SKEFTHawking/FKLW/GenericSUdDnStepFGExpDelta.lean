/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — dnStepFG_sud exp(-[F,G]) = Δ identity

The SU(d) analog of SU(2)'s `dnStepFG_su2_exp_neg_comm_eq_Delta`: in the valid
recursion regime, the matrix exponential of the negated balanced commutator
recovers the residual Δ:

  `NormedSpace.exp (-([F, G])) = Δ.val`

Composes Session 83's commutator identity `[F, G] = -matrixLog (n+2) Δ.val`
(so `-[F, G] = matrixLog (n+2) Δ.val`) with the matrix exp/log right-inverse
`expAmbient_matrixLog` (valid on the `target` neighborhood of `1`, i.e. when
`Δ.val ∈ (expAmbientPartialHomeo (n+2)).target`). Since `expAmbient (n+2)` is
definitionally `NormedSpace.exp`, the round-trip closes directly.

This is the next super-quad main-induction substrate brick: it underwrites the
`gC(exp(iF), exp(iG)) ≈ Δ` cubic composition bound (the recursion's
error-contraction step).

## Substantive content shipped

  * `dnStepFG_sud_exp_neg_comm_eq_Delta` — `exp(-[F,G]) = Δ.val` in the valid
    regime (carrying `Δ.val ∈ target`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — dnStep exp/log round-trip
(super-quad main induction substrate).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDnStepFGCommutator
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **dnStepFG_sud exp(-[F,G]) = Δ identity (valid branch)**: in the valid
recursion regime, with `Δ.val` in the exp/log `target` neighborhood of `1`,

  `NormedSpace.exp (-([F, G])) = Δ.val`.

Mirrors SU(2)'s `dnStepFG_su2_exp_neg_comm_eq_Delta`. Composes Session 83's
commutator identity with the matrix exp/log right-inverse `expAmbient_matrixLog`. -/
lemma dnStepFG_sud_exp_neg_comm_eq_Delta {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    (h_valid : 0 < ‖((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ∧
        ‖((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 ∧
        (((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)).IsHermitian ∧
        (((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)).trace = 0)
    (h_target : (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val ∈
        (expAmbientPartialHomeo (n + 2)).target) :
    NormedSpace.exp (-((dnStepFG_sud V_n U).F * (dnStepFG_sud V_n U).G -
        (dnStepFG_sud V_n U).G * (dnStepFG_sud V_n U).F)) =
      (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val := by
  have h_comm := dnStepFG_sud_commutator_identity_valid V_n U h_valid
  have h_neg_comm : -((dnStepFG_sud V_n U).F * (dnStepFG_sud V_n U).G -
      (dnStepFG_sud V_n U).G * (dnStepFG_sud V_n U).F) =
      matrixLog (n + 2) (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val := by
    rw [h_comm]
    exact neg_neg _
  rw [h_neg_comm]
  show expAmbient (n + 2) (matrixLog (n + 2)
    (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val) = _
  exact expAmbient_matrixLog (n + 2) h_target

end SKEFTHawking.FKLW.GenericSUd
