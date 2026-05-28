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

/-- **dnStepFG_sud exp(-[F,G]) = Δ identity (regime-unconditional in `0 < ‖H‖`)**:
with `Δ.val` in the exp/log `target` neighborhood of `1`, and `H = (-i)·log Δ`
bounded (`‖H‖ ≤ 1`), Hermitian, and traceless,

  `NormedSpace.exp (-([F, G])) = Δ.val`.

Mirrors SU(2)'s `dnStepFG_su2_exp_neg_comm_eq_Delta`, but **drops the `0 < ‖H‖`
hypothesis** by case-splitting internally:

  * **`0 < ‖H‖` (valid branch)**: reconstruct the 4-conjunct keystone predicate
    and compose Session 83's commutator identity with the exp/log right-inverse
    `expAmbient_matrixLog`.
  * **`‖H‖ = 0` (degenerate branch, `V_n = U`)**: `H = 0 ⟹ log Δ = 0`, so the
    `target` round-trip gives `Δ = expAmbient 0 = 1`; the DN step falls back to
    `F = G = 0`, whence `exp(-[0,0]) = exp 0 = 1 = Δ`.

This makes the identity hold for **every** `V_n, U` in the regime — including the
`V_n = U` edge case where the bundled `0 < ‖H‖` conjunct is false — so the
super-quad `h_regime` hypothesis no longer needs the (universally false at
`V = U`) positivity conjunct. -/
lemma dnStepFG_sud_exp_neg_comm_eq_Delta {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    (h_regime3 :
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
  by_cases h_pos : 0 < ‖((-Complex.I) • matrixLog (n + 2)
      (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
      Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖
  · -- Valid branch: reconstruct the 4-conjunct predicate from `h_pos` + `h_regime3`.
    have h_comm := dnStepFG_sud_commutator_identity_valid V_n U
      ⟨h_pos, h_regime3.1, h_regime3.2.1, h_regime3.2.2⟩
    have h_neg_comm : -((dnStepFG_sud V_n U).F * (dnStepFG_sud V_n U).G -
        (dnStepFG_sud V_n U).G * (dnStepFG_sud V_n U).F) =
        matrixLog (n + 2) (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val := by
      rw [h_comm]
      exact neg_neg _
    rw [h_neg_comm]
    show expAmbient (n + 2) (matrixLog (n + 2)
      (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val) = _
    exact expAmbient_matrixLog (n + 2) h_target
  · -- Degenerate branch: ‖H‖ = 0 ⟹ log Δ = 0 ⟹ Δ = 1; DN step gives F = G = 0.
    have hFG := dnStepFG_sud_invalid_F_G_zero V_n U (fun h => h_pos h.1)
    have hH0 : ((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) = 0 := by
      rw [← norm_le_zero_iff]; exact not_lt.mp h_pos
    have hlog0 : matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val = 0 := by
      have h2 : (-Complex.I)⁻¹ • ((-Complex.I) • matrixLog (n + 2)
          (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val) = 0 := by
        rw [hH0, smul_zero]
      rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero), one_smul] at h2
    have hΔ1 : (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val = 1 := by
      have hrt := expAmbient_matrixLog (n + 2) h_target
      rw [hlog0, expAmbient_zero] at hrt
      exact hrt.symm
    rw [hFG.1, hFG.2, hΔ1]
    simp

end SKEFTHawking.FKLW.GenericSUd
