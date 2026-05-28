/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Bounded Hermitian discharge with EXPLICIT ∑√ inner bound

Re-threads Session 37's `symmetric_balanced_commutator_hermitian_via_spectral_bounded`
(which bounds `‖F‖ ≤ (n+2)²·‖F_inner‖` with an abstract inner norm) using
Session 79's BOUNDED full diagonal discharge
`symmetric_balanced_commutator_diagonal_real_full_bounded`, so the inner
witness norm is replaced by the EXPLICIT spectral partial-sum bound:

  `‖F‖ ≤ (n+2)² · ∑_p √(θ·(b'_p).re/2)`

where `b'_p = partialSumCoeff (a_sorted coerced) p` and `a_sorted = a ∘ Tuple.sort (-a)`
is the eigenvalue-sorted version of the spectral eigenvalues `a`.

This is the bridge that exposes the inner-witness norm in concrete spectral
terms — the missing link between Session 37's abstract `(n+2)²·‖F_inner‖` and
the concrete `K_F·√(θ/2)` form needed by `DnStepFG_sud_F_norm_bound_predicate`.

## Substantive content shipped

  * `symmetric_balanced_commutator_hermitian_via_spectral_bounded_explicit` —
    Session 37's spectral-lift discharge with the inner norm replaced by the
    explicit ∑√ spectral partial-sum bound (via Session 79 + Session 36).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — explicit-∑√ bounded
Hermitian discharge (F-norm bound bridge to concrete K_F·√(θ/2)).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeBounded
import SKEFTHawking.FKLW.GenericSUdSymmetricDiagonalDischargeFullBounded

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Bounded Hermitian discharge with EXPLICIT ∑√ inner bound** — for any
Hermitian `H = U · diag(a) · U*` (spectral form) and `θ ∈ [0, 1]`, there exist
Hermitian-traceless F, G with the balanced commutator identity AND

  `‖F‖ ≤ (n+2)² · ∑_p √(θ·(b'_p).re/2)`  (and mirror for G)

where `b'_p = partialSumCoeff (a_sorted coerced) p` for the eigenvalue-sorted
`a_sorted = a ∘ Tuple.sort (-a)`.

Re-threads Session 37 using Session 79's bounded diagonal discharge: the inner
witnesses F', G' (from Session 79 applied to the eigenvalues `a`) carry the
explicit ∑√ norm bound, which the Session 36 norm bridge propagates through the
spectral conjugation `F = U · F' · U*`. -/
theorem symmetric_balanced_commutator_hermitian_via_spectral_bounded_explicit {n : ℕ}
    (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (h_tr : H.trace = 0)
    (U : ↥(Matrix.unitaryGroup (Fin (n + 2)) ℂ))
    (a : Fin (n + 2) → ℝ)
    (h_spec : H = U.val * Matrix.diagonal (fun k => (a k : ℂ)) * star U.val)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H ∧
      ‖F‖ ≤ ((n + 2 : ℕ) : ℝ)^2 * ∑ p : Fin (n + 1),
        Real.sqrt (θ * (partialSumCoeff
          (fun k => (a ((Tuple.sort (fun i => -(a i))) k) : ℂ)) p).re / 2) ∧
      ‖G‖ ≤ ((n + 2 : ℕ) : ℝ)^2 * ∑ p : Fin (n + 1),
        Real.sqrt (θ * (partialSumCoeff
          (fun k => (a ((Tuple.sort (fun i => -(a i))) k) : ℂ)) p).re / 2) := by
  -- Eigenvalues sum to zero (from H traceless + spectral form).
  have h_tr_real : (∑ k, a k) = 0 := by
    have h_diag_tr : (Matrix.diagonal (fun k => (a k : ℂ))).trace = 0 := by
      have h_inv : (Matrix.diagonal (fun k => (a k : ℂ))).trace =
          (U.val * Matrix.diagonal (fun k => (a k : ℂ)) * star U.val).trace := by
        rw [unitary_group_conjugation_trace_invariance U]
      rw [h_inv, ← h_spec]
      exact h_tr
    have h_tr_sum : (∑ k, (a k : ℂ)) = 0 := by
      rw [Matrix.trace_diagonal] at h_diag_tr
      exact h_diag_tr
    exact (real_sum_coerce_eq_zero_iff a).mp h_tr_sum
  -- Apply Session 79 (BOUNDED full diagonal discharge) to the eigenvalues.
  obtain ⟨F', G', hF'_herm, hG'_herm, hF'_tr, hG'_tr, hcomm', hF'_bound, hG'_bound⟩ :=
    symmetric_balanced_commutator_diagonal_real_full_bounded a h_tr_real θ hθ_nn hθ_le_one
  -- Conjugate by the eigenvector unitary U.
  refine ⟨U.val * F' * star U.val, U.val * G' * star U.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact unitary_group_conjugation_isHermitian U F' hF'_herm
  · exact unitary_group_conjugation_isHermitian U G' hG'_herm
  · exact unitary_group_conjugation_traceless U F' hF'_tr
  · exact unitary_group_conjugation_traceless U G' hG'_tr
  · -- Commutator identity: F · G − G · F = -iθ · H
    have h_smul := unitary_group_conjugation_smul_commutator_invariance U
      F' G' (Matrix.diagonal (fun k => (a k : ℂ)))
      (-((θ : ℂ) * Complex.I)) hcomm'
    rw [h_smul, ← h_spec]
  · -- ‖F‖ ≤ (n+2)² · ∑√ : norm bridge (S36) then S79 inner bound
    have hn : Nonempty (Fin (n + 2)) := ⟨0⟩
    calc ‖U.val * F' * star U.val‖
        ≤ ((n + 2 : ℕ) : ℝ)^2 * ‖F'‖ := linftyOpNorm_unitary_conj_bound U F'
      _ ≤ ((n + 2 : ℕ) : ℝ)^2 * ∑ p : Fin (n + 1),
            Real.sqrt (θ * (partialSumCoeff
              (fun k => (a ((Tuple.sort (fun i => -(a i))) k) : ℂ)) p).re / 2) := by
          apply mul_le_mul_of_nonneg_left hF'_bound
          positivity
  · -- ‖G‖ ≤ (n+2)² · ∑√ : same via S36 + S79
    have hn : Nonempty (Fin (n + 2)) := ⟨0⟩
    calc ‖U.val * G' * star U.val‖
        ≤ ((n + 2 : ℕ) : ℝ)^2 * ‖G'‖ := linftyOpNorm_unitary_conj_bound U G'
      _ ≤ ((n + 2 : ℕ) : ℝ)^2 * ∑ p : Fin (n + 1),
            Real.sqrt (θ * (partialSumCoeff
              (fun k => (a ((Tuple.sort (fun i => -(a i))) k) : ℂ)) p).re / 2) := by
          apply mul_le_mul_of_nonneg_left hG'_bound
          positivity

end SKEFTHawking.FKLW.GenericSUd
