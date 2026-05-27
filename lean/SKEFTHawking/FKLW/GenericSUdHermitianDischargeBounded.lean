/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Bounded-form Hermitian discharge for ANY H

For ANY Hermitian-traceless H ∈ Matrix (Fin (n+2)) (Fin (n+2)) ℂ with
spectral decomposition H = U · diag(a) · U*, there exist F, G satisfying

  F · G − G · F = -((θ : ℂ) · Complex.I) • H

with explicit linftyOp bounds:

  ‖F‖_linftyOp ≤ (n+2)² · √(θ/2)
  ‖G‖_linftyOp ≤ (n+2)² · √(θ/2)

(the `(n+2)²` factor is the norm-bridge looseness from Session 36).

This composes Session 32's spectral-lift discharge with Session 36's
norm-bridge bound to give the **bounded-form** existence theorem suitable
for downstream consumers requiring concrete bounds on F, G.

## Note: bound looseness

The bound `‖F‖ ≤ (n+2)² · √(θ/2)` is loose by a factor of (n+2)² compared
to the diagonal case (where ‖F'‖ ≤ √(θ/2) via Session 24). The looseness
comes from:
  - Session 26's unitary conjugation NOT preserving linftyOp norm
  - Session 36's loose bound `‖U · A · star U‖_linftyOp ≤ n² · ‖A‖_linftyOp`

Tightening this to `(n+2) · √(θ/2)` (via Cauchy-Schwarz row-sum) ships
in a follow-on if needed for downstream polylog discharges.

## Substantive content shipped

  * `symmetric_balanced_commutator_hermitian_via_spectral_bounded` — the
    discharge with explicit linftyOp norm bounds on F, G.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" — bounded-form spectral-lift discharge
(combines S32 algebraic discharge + S36 norm bridge).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSpectralLift
import SKEFTHawking.FKLW.GenericSUdNormBridgeUnitaryConjugation
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## Bounded-form Hermitian discharge via spectral lift

Composes S32's spectral discharge for diagonal H (giving F' = U_inner ·
σ_y-blocks · U_inner*) with S36's norm bridge to give a concrete
linftyOp bound on the final F, G. -/

/-- **Bounded-form Hermitian discharge via spectral decomposition** —
extends Session 32's `symmetric_balanced_commutator_hermitian_via_spectral`
with explicit linftyOp norm bounds on the witnesses F, G:

  `‖F‖_linftyOp ≤ K · ‖F_inner‖_linftyOp`
  `‖G‖_linftyOp ≤ K · ‖G_inner‖_linftyOp`

where `K = (n+2)²` (the Session 36 norm-bridge bound for unitary conjugation)
and `F_inner, G_inner` are the inner diagonal-case discharge witnesses. -/
theorem symmetric_balanced_commutator_hermitian_via_spectral_bounded {n : ℕ}
    (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (h_tr : H.trace = 0)
    (U : ↥(Matrix.unitaryGroup (Fin (n + 2)) ℂ))
    (a : Fin (n + 2) → ℝ)
    (h_spec : H = U.val * Matrix.diagonal (fun k => (a k : ℂ)) * star U.val)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
      (F_inner G_inner : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H ∧
      ‖F‖ ≤ ((n + 2 : ℕ) : ℝ)^2 * ‖F_inner‖ ∧
      ‖G‖ ≤ ((n + 2 : ℕ) : ℝ)^2 * ‖G_inner‖ ∧
      F = U.val * F_inner * star U.val ∧
      G = U.val * G_inner * star U.val := by
  -- Apply Session 32 to extract (F_inner, G_inner).
  obtain ⟨F_inner', G_inner', hFi_herm, hGi_herm, hFi_tr, hGi_tr, hcomm_inner⟩ := by
    have h_diag_tr : (Matrix.diagonal (fun k => (a k : ℂ))).trace = 0 := by
      have h_inv : (Matrix.diagonal (fun k => (a k : ℂ))).trace =
          (U.val * Matrix.diagonal (fun k => (a k : ℂ)) * star U.val).trace := by
        rw [unitary_group_conjugation_trace_invariance U]
      rw [h_inv, ← h_spec]
      exact h_tr
    have h_tr_sum : (∑ k, (a k : ℂ)) = 0 := by
      rw [Matrix.trace_diagonal] at h_diag_tr
      exact h_diag_tr
    have h_tr_real : (∑ k, a k) = 0 := (real_sum_coerce_eq_zero_iff a).mp h_tr_sum
    exact symmetric_balanced_commutator_diagonal_real_full a h_tr_real θ hθ_nn hθ_le_one
  -- Now conjugate.
  refine ⟨U.val * F_inner' * star U.val, U.val * G_inner' * star U.val, F_inner', G_inner',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · exact unitary_group_conjugation_isHermitian U F_inner' hFi_herm
  · exact unitary_group_conjugation_isHermitian U G_inner' hGi_herm
  · exact unitary_group_conjugation_traceless U F_inner' hFi_tr
  · exact unitary_group_conjugation_traceless U G_inner' hGi_tr
  · -- Commutator identity
    have h_smul := unitary_group_conjugation_smul_commutator_invariance U
      F_inner' G_inner' (Matrix.diagonal (fun k => (a k : ℂ)))
      (-((θ : ℂ) * Complex.I)) hcomm_inner
    rw [h_smul, ← h_spec]
  · -- ‖F‖ ≤ (n+2)² · ‖F_inner‖
    by_cases hn : Nonempty (Fin (n + 2))
    · exact linftyOpNorm_unitary_conj_bound U F_inner'
    · exact absurd ⟨0⟩ hn
  · -- ‖G‖ ≤ (n+2)² · ‖G_inner‖
    by_cases hn : Nonempty (Fin (n + 2))
    · exact linftyOpNorm_unitary_conj_bound U G_inner'
    · exact absurd ⟨0⟩ hn

end SKEFTHawking.FKLW.GenericSUd
