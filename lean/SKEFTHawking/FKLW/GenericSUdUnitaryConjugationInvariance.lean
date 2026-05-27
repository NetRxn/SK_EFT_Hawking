/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — U(d) (unitary-group) conjugation invariance

Generalizes Session 13's `specialUnitaryGroup`-stated conjugation invariance
lemmas to the broader `unitaryGroup` setting. This enables permutation-matrix
conjugation downstream (permutation matrices have determinant ±1, so generally
lie in `U(d) ∖ SU(d)`).

The proofs are IDENTICAL to Session 13's — the conjugation invariance properties
only use `star U · U = 1`, not the determinant constraint of SU(d).

## Substantive content shipped

  * `unitary_group_conjugation_commutator_invariance` — `[F, G]` equivariant
    under U(d) conjugation.
  * `unitary_group_conjugation_smul_commutator_invariance` — scaled version.
  * `unitary_group_conjugation_isHermitian` — Hermitian preservation.
  * `unitary_group_conjugation_trace_invariance` — trace preservation.
  * `unitary_group_conjugation_traceless` — trace-zero preservation.
  * `unitary_group_conjugation_balanced_commutator_structure` — composite.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (U(d) generalization
of conjugation invariance for permutation-matrix discharge).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Commutator equivariance under U(d) conjugation -/

/-- **Commutator equivariance under U(d) conjugation**. -/
theorem unitary_group_conjugation_commutator_invariance {d : ℕ}
    (U : ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (F G H : Matrix (Fin d) (Fin d) ℂ) (hFG : F * G - G * F = H) :
    (U.val * F * star U.val) * (U.val * G * star U.val) -
      (U.val * G * star U.val) * (U.val * F * star U.val) =
        U.val * H * star U.val := by
  have hUU' : star U.val * U.val = 1 := U.2.1
  have hkey : ∀ (M N : Matrix (Fin d) (Fin d) ℂ),
      (U.val * M * star U.val) * (U.val * N * star U.val) = U.val * (M * N) * star U.val := by
    intros M N
    calc (U.val * M * star U.val) * (U.val * N * star U.val)
        = U.val * M * (star U.val * U.val) * N * star U.val := by noncomm_ring
      _ = U.val * M * 1 * N * star U.val := by rw [hUU']
      _ = U.val * (M * N) * star U.val := by noncomm_ring
  rw [hkey, hkey]
  rw [show U.val * (F * G) * star U.val - U.val * (G * F) * star U.val =
        U.val * (F * G - G * F) * star U.val from by noncomm_ring]
  rw [hFG]

/-- **Scaled commutator equivariance under U(d)**. -/
theorem unitary_group_conjugation_smul_commutator_invariance {d : ℕ}
    (U : ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (F G H : Matrix (Fin d) (Fin d) ℂ) (c : ℂ)
    (hFG : F * G - G * F = c • H) :
    (U.val * F * star U.val) * (U.val * G * star U.val) -
      (U.val * G * star U.val) * (U.val * F * star U.val) =
        c • (U.val * H * star U.val) := by
  have h := unitary_group_conjugation_commutator_invariance U F G (c • H) hFG
  rw [h]
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-! ## 2. Hermiticity preservation under U(d) conjugation -/

/-- **Hermiticity is preserved under U(d) conjugation**. -/
theorem unitary_group_conjugation_isHermitian {d : ℕ}
    (U : ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : F.IsHermitian) :
    (U.val * F * star U.val).IsHermitian := by
  show (U.val * F * star U.val).conjTranspose = U.val * F * star U.val
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp [star_eq_conjTranspose]
  rw [mul_assoc, hF]

/-! ## 3. Trace preservation under U(d) conjugation -/

/-- **Trace is U(d)-conjugation-invariant**. -/
theorem unitary_group_conjugation_trace_invariance {d : ℕ}
    (U : ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (F : Matrix (Fin d) (Fin d) ℂ) :
    (U.val * F * star U.val).trace = F.trace := by
  rw [Matrix.trace_mul_cycle, show star U.val * U.val = 1 from U.2.1, Matrix.one_mul]

/-- **Trace zero is preserved under U(d) conjugation**. -/
theorem unitary_group_conjugation_traceless {d : ℕ}
    (U : ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : F.trace = 0) :
    (U.val * F * star U.val).trace = 0 := by
  rw [unitary_group_conjugation_trace_invariance, hF]

/-! ## 4. Composite: balanced commutator structure preserved under U(d) -/

/-- **Composite U(d)-conjugation invariance**: a balanced commutator structure
(Hermitian + traceless + commutator identity) is preserved under U(d) conjugation. -/
theorem unitary_group_conjugation_balanced_commutator_structure {d : ℕ}
    (U : ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (F G H : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hF_herm : F.IsHermitian) (hG_herm : G.IsHermitian)
    (hF_tr : F.trace = 0) (hG_tr : G.trace = 0)
    (hcomm : F * G - G * F = -((θ : ℂ) * Complex.I) • H) :
    let F' := U.val * F * star U.val
    let G' := U.val * G * star U.val
    let H' := U.val * H * star U.val
    F'.IsHermitian ∧ G'.IsHermitian ∧ F'.trace = 0 ∧ G'.trace = 0 ∧
    F' * G' - G' * F' = -((θ : ℂ) * Complex.I) • H' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact unitary_group_conjugation_isHermitian U F hF_herm
  · exact unitary_group_conjugation_isHermitian U G hG_herm
  · exact unitary_group_conjugation_traceless U F hF_tr
  · exact unitary_group_conjugation_traceless U G hG_tr
  · exact unitary_group_conjugation_smul_commutator_invariance U F G H _ hcomm

end SKEFTHawking.FKLW.GenericSUd
