/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — dnStepFG_sud group-commutator cubic remainder

The SU(d) analog of SU(2)'s `dnStepFG_su2_gC_minus_Delta_norm_le_cubic`: for
the dnStep witnesses `F, G` with `‖F‖, ‖G‖ ≤ δ ≤ 1` (valid regime), the group
commutator of `exp(iF), exp(iG)` approximates the residual Δ to cubic order:

  `‖groupCommutator(expIsud F, expIsud G) − Δ.val‖ ≤ 320·δ³`.

Composes the **dimension-generic** BCH cubic remainder
`GroupCommutator.groupCommutator_lie_bracket_cubic_remainder`
(`‖gC(exp iF, exp iG) − exp(−⁅F,G⁆)‖ ≤ 320·δ³`) with Session 84's
`dnStepFG_sud_exp_neg_comm_eq_Delta` (`exp(−[F,G]) = Δ.val`), since the ring
Lie bracket `⁅F,G⁆` is `F·G − G·F` definitionally.

This is the recursion's error-contraction step: one Dawson-Nielsen level turns
an ε-approximation into a `320·δ³`-with-`δ = O(√ε)` approximation, i.e. the
super-quadratic `ε ↦ O(ε^{3/2})` contraction.

## Substantive content shipped

  * `dnStepFG_sud_gC_minus_Delta_norm_le_cubic` — `‖gC(expIsud F, expIsud G) − Δ‖ ≤ 320·δ³`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — dnStep cubic remainder
(super-quad main induction error-contraction step).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDnStepFGExpDelta
import SKEFTHawking.FKLW.GenericSUdExpIsuDNormBound
import SKEFTHawking.FKLW.GroupCommutator

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix
open SKEFTHawking.FKLW.GroupCommutator

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **dnStepFG_sud group-commutator cubic remainder (valid branch)**: for the
dnStep witnesses with `‖F‖, ‖G‖ ≤ δ ≤ 1` and `Δ.val` in the exp/log target,

  `‖groupCommutator(expIsud F, expIsud G) − Δ.val‖ ≤ 320·δ³`.

Mirrors SU(2)'s `dnStepFG_su2_gC_minus_Delta_norm_le_cubic`. Composes the
dimension-generic BCH cubic remainder with Session 84's `exp(−[F,G]) = Δ`. -/
lemma dnStepFG_sud_gC_minus_Delta_norm_le_cubic {n : ℕ}
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
        (expAmbientPartialHomeo (n + 2)).target)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (hF_norm : ‖(dnStepFG_sud V_n U).F‖ ≤ δ)
    (hG_norm : ‖(dnStepFG_sud V_n U).G‖ ≤ δ) :
    ‖(groupCommutator
        ((expIsud n (dnStepFG_sud V_n U).F (dnStepFG_sud V_n U).hF_herm
            (dnStepFG_sud V_n U).hF_tr : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
        ((expIsud n (dnStepFG_sud V_n U).G (dnStepFG_sud V_n U).hG_herm
            (dnStepFG_sud V_n U).hG_tr : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)) -
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val‖ ≤ 320 * δ ^ 3 := by
  rw [expIsud_val, expIsud_val]
  have h_bch := groupCommutator_lie_bracket_cubic_remainder δ hδ_nn hδ_le_one
    (dnStepFG_sud V_n U).F (dnStepFG_sud V_n U).G hF_norm hG_norm
  have h_exp_eq_Δ := dnStepFG_sud_exp_neg_comm_eq_Delta V_n U h_valid h_target
  rw [← h_exp_eq_Δ]
  exact h_bch

end SKEFTHawking.FKLW.GenericSUd
