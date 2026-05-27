/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Spectral lift of diagonal discharge to arbitrary Hermitian H

For ANY Hermitian-traceless H ∈ Matrix (Fin (n+2)) (Fin (n+2)) ℂ that admits
a spectral decomposition H = U · diag(a) · U* with U ∈ U(d) and a : Fin (n+2) → ℝ:

  `∃ F G, F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
     F * G - G * F = -((θ : ℂ) * Complex.I) • H`

This is the **FULL S.3 d≥3 PROPER discharge** (modulo invoking Mathlib's
`Matrix.IsHermitian.spectralTheorem` to extract the (U, a) data, which the
user of this theorem can do).

## Composition chain

Given H Hermitian + traceless + spectral decomposition H = U · diag(a) · U*:
  1. Trace invariance (S26): trace H = trace (U · D · U*) = trace D = ∑ a
  2. Hence H traceless ⟹ ∑ a = 0
  3. Apply S31's diagonal discharge to a: ∃ F_D, G_D for diag(a) Hermitian-traceless
  4. Conjugate by U: F := U · F_D · U*, G := U · G_D · U*
  5. By S26: F, G Hermitian + traceless + F·G - G·F = U · (-iθ · diag(a)) · U*
  6. Substitute h_spec backwards: U · diag(a) · U* = H, so the result is -iθ · H

## Substantive content shipped

  * `symmetric_balanced_commutator_hermitian_via_spectral` — the full S.3 d≥3
    PROPER discharge (parameterized on spectral decomposition).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 d≥3 PROPER (spectral lift
from diagonal case to arbitrary Hermitian via U(d) conjugation).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSymmetricDiagonalDischargeFull
import SKEFTHawking.FKLW.GenericSUdUnitaryConjugationInvariance

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Helper: sum of real coerces equals zero ⟺ real sum equals zero -/

/-- **Real-coerced sum = 0 iff real sum = 0**. -/
theorem real_sum_coerce_eq_zero_iff {n : ℕ} (a : Fin n → ℝ) :
    (∑ k, (a k : ℂ)) = 0 ↔ (∑ k, a k) = 0 := by
  rw [show (∑ k, (a k : ℂ)) = ((∑ k, a k : ℝ) : ℂ) from by push_cast; rfl]
  exact Complex.ofReal_eq_zero

/-! ## 2. MAIN THEOREM: Spectral lift discharge for any Hermitian H -/

/-- **FULL S.3 d≥3 PROPER discharge** (spectral lift form): for ANY
Hermitian-traceless `H` that admits a spectral decomposition
`H = U · diag(a) · U*` with `U ∈ unitaryGroup` and `a : Fin (n+2) → ℝ`,
there exist Hermitian-traceless F, G such that

  `F · G - G · F = -((θ : ℂ) * Complex.I) • H`

for any θ ∈ [0, 1].

The spectral decomposition (U, a) is the input; Mathlib's
`Matrix.IsHermitian.spectralTheorem` provides such (U, a) for any Hermitian H. -/
theorem symmetric_balanced_commutator_hermitian_via_spectral {n : ℕ}
    (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (h_tr : H.trace = 0)
    (U : ↥(Matrix.unitaryGroup (Fin (n + 2)) ℂ))
    (a : Fin (n + 2) → ℝ)
    (h_spec : H = U.val * Matrix.diagonal (fun k => (a k : ℂ)) * star U.val)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H := by
  -- Step 1: Extract real traceless from H.trace = 0 via spectral.
  -- trace H = trace (U · D · U*) = trace D = ∑ a (using trace_mul_cycle).
  have h_tr_D : (Matrix.diagonal (fun k => (a k : ℂ))).trace = 0 := by
    have h_inv : (Matrix.diagonal (fun k => (a k : ℂ))).trace =
        (U.val * Matrix.diagonal (fun k => (a k : ℂ)) * star U.val).trace := by
      rw [unitary_group_conjugation_trace_invariance U]
    rw [h_inv, ← h_spec]
    exact h_tr
  have h_tr_sum : (∑ k, (a k : ℂ)) = 0 := by
    rw [Matrix.trace_diagonal] at h_tr_D
    exact h_tr_D
  have h_tr_real : (∑ k, a k) = 0 := (real_sum_coerce_eq_zero_iff a).mp h_tr_sum
  -- Step 2: Apply S31 to a (the eigenvalue sequence).
  obtain ⟨F_D, G_D, hF_D_herm, hG_D_herm, hF_D_tr, hG_D_tr, hcomm_D⟩ :=
    symmetric_balanced_commutator_diagonal_real_full a h_tr_real θ hθ_nn hθ_le_one
  -- Step 3: Lift via U-conjugation (S26).
  refine ⟨U.val * F_D * star U.val, U.val * G_D * star U.val, ?_, ?_, ?_, ?_, ?_⟩
  -- F Hermitian
  · exact unitary_group_conjugation_isHermitian U F_D hF_D_herm
  -- G Hermitian
  · exact unitary_group_conjugation_isHermitian U G_D hG_D_herm
  -- F traceless
  · exact unitary_group_conjugation_traceless U F_D hF_D_tr
  -- G traceless
  · exact unitary_group_conjugation_traceless U G_D hG_D_tr
  -- Commutator identity
  · -- Apply S26 scaled commutator
    have h_smul := unitary_group_conjugation_smul_commutator_invariance U
      F_D G_D (Matrix.diagonal (fun k => (a k : ℂ)))
      (-((θ : ℂ) * Complex.I)) hcomm_D
    rw [h_smul]
    -- Goal: -(θ · i) • (U · diag(a) · U*) = -(θ · i) • H
    rw [← h_spec]

end SKEFTHawking.FKLW.GenericSUd
