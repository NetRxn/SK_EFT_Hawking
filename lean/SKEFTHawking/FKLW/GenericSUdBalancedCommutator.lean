/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 — `dnStepFG_sud` substrate: d-generic balanced commutator

The d-generic Aharonov-Arad balanced commutator theorem: for any traceless
Hermitian H ∈ 𝔰𝔲(d) with ‖H‖ ≤ 1 (operator norm), and any θ ∈ [0, 1],
construct traceless Hermitian F, G ∈ 𝔰𝔲(d) with `‖F‖, ‖G‖ ≤ √(θ/2)` and
`F·G − G·F = −iθ·H`.

This is the **load-bearing substrate** for `dnStepFG_sud`, the d-generic
Dawson-Nielsen recursion step (Phase 6y S.3). The SU(2) discharge ships
via existing `balanced_commutator_general_axis_lie_traceless` (Pauli
decomposition). The d ≥ 3 substantive discharge composes spectral
decomposition + per-2-block SU(2) lift + block-orthogonality argument.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3.

-/

import Mathlib
import SKEFTHawking.FKLW.SU2BalancedCommutator
import SKEFTHawking.FKLW.GenericSUdGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The d-generic balanced commutator predicate -/

/-- **The d-generic balanced commutator predicate** for SU(d). For any
traceless Hermitian H with `‖H‖ = 1` (operator norm) and `θ ∈ [0, 1]`,
there exist traceless Hermitian F, G ∈ Matrix (Fin d) (Fin d) ℂ with
`‖F‖, ‖G‖ ≤ √(θ/2)` and `F · G − G · F = −iθ · H`.

This is the **d-generic Aharonov-Arad balanced commutator** statement
(Phase 6y S.3). The d = 2 case is discharged in `BalancedCommutator_SUd_two`
below via direct mechanical lift of the SU(2) Pauli-decomposition substrate
(`balanced_commutator_general_axis_lie_traceless`). The d ≥ 3 case is
the substantive S.3 PROPER ship (spectral decomposition + per-2-block SU(2)
lift + block-orthogonal sum). -/
def BalancedCommutator_SUd (d : ℕ) : Prop :=
  ∀ (H : Matrix (Fin d) (Fin d) ℂ)
    (_hH : H.IsHermitian) (_htr : H.trace = 0)
    (_hH_norm : ‖H‖ = 1)
    (θ : ℝ) (_hθ_nn : 0 ≤ θ) (_hθ_le_one : θ ≤ 1),
    ∃ (F G : Matrix (Fin d) (Fin d) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧
      F.trace = 0 ∧ G.trace = 0 ∧
      ‖F‖ ≤ Real.sqrt (θ / 2) ∧ ‖G‖ ≤ Real.sqrt (θ / 2) ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H

/-! ## 2. d = 0 discharge (vacuous) -/

/-- **`BalancedCommutator_SUd 0`** is vacuous: no Hermitian matrix in
`Matrix (Fin 0) (Fin 0) ℂ` has `‖H‖ = 1` (since the only matrix is 0). -/
theorem BalancedCommutator_SUd_zero : BalancedCommutator_SUd 0 := by
  intro H _hH _htr hH_norm θ _hθ_nn _hθ_le_one
  -- In Fin 0, the only matrix is the zero matrix.
  have h_zero : H = 0 := by
    ext i; exact i.elim0
  rw [h_zero, norm_zero] at hH_norm
  exact absurd hH_norm (by norm_num)

/-! ## 3. d = 1 discharge (vacuous) -/

/-- **`BalancedCommutator_SUd 1`** is vacuous: the only traceless Hermitian
matrix in `Matrix (Fin 1) (Fin 1) ℂ` is 0 (since trace = H 0 0 = 0 forces
H 0 0 = 0, and 1×1 Hermitian H is determined by H 0 0). So `‖H‖ = 0 ≠ 1`. -/
theorem BalancedCommutator_SUd_one : BalancedCommutator_SUd 1 := by
  intro H _hH htr hH_norm θ _hθ_nn _hθ_le_one
  -- trace H = H 0 0 = 0 ⟹ H is the zero matrix (1×1).
  have h_zero : H = 0 := by
    ext i j
    fin_cases i; fin_cases j
    simp only [Matrix.zero_apply]
    have h_tr : H.trace = 0 := htr
    rw [Matrix.trace, Fin.sum_univ_one, Matrix.diag_apply] at h_tr
    exact h_tr
  rw [h_zero, norm_zero] at hH_norm
  exact absurd hH_norm (by norm_num)

/-! ## 4. d = 2 discharge (mechanical lift from SU(2) substrate) -/

/-- **`BalancedCommutator_SUd 2`** discharges via direct mechanical lift
of `balanced_commutator_general_axis_lie_traceless` (Phase 6t SU(2) substrate
via Pauli decomposition with Bloch-sphere coefficient bound K = √(1/2)). -/
theorem BalancedCommutator_SUd_two : BalancedCommutator_SUd 2 := by
  intro H hH htr hH_norm θ hθ_nn hθ_le_one
  exact SKEFTHawking.FKLW.SU2BalancedCommutator.balanced_commutator_general_axis_lie_traceless
    H hH htr hH_norm θ hθ_nn hθ_le_one

/-! ## 5. Aggregated dispatcher for d ∈ {0, 1, 2}

The d ≤ 2 cases are discharged via the explicit case-analysis above.
Downstream consumers can use this aggregated form when working with a
specific d ∈ {0, 1, 2}. The d ≥ 3 substantive discharge is the S.3
PROPER ship (multi-session, Aharonov-Arad spectral block argument). -/

/-- **`BalancedCommutator_SUd d` holds for any `d ≤ 2`**. -/
theorem BalancedCommutator_SUd_of_le_two (d : ℕ) (hd : d ≤ 2) :
    BalancedCommutator_SUd d := by
  interval_cases d
  · exact BalancedCommutator_SUd_zero
  · exact BalancedCommutator_SUd_one
  · exact BalancedCommutator_SUd_two

end SKEFTHawking.FKLW.GenericSUd
