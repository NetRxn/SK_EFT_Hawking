/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Permutation matrices are unitary

For any `σ : Equiv.Perm (Fin n)`, the permutation matrix `Equiv.Perm.permMatrix ℂ σ`
lies in `Matrix.unitaryGroup (Fin n) ℂ`.

This module ships the unitary-group membership for permutation matrices,
enabling permutation-based conjugation via Session 26's U(d) conjugation
invariance lemmas. The eigenvalue-sort lift (Session 28+) uses this:
discharge for diag(a ∘ σ) is lifted to discharge for diag(a) by conjugating
with `permMatrix σ` (which is unitary).

## Substantive content shipped

  * `permMatrix_mem_unitaryGroup` — permutation matrices are unitary.
  * `permMatrixAsUnitary` — convenient `↥(unitaryGroup _ _)` bundling.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (permutation
matrix unitary membership for eigenvalue-sort lift).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdUnitaryConjugationInvariance

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

/-! ## 1. Permutation matrices are unitary -/

/-- **Permutation matrix is unitary**: `permMatrix ℂ σ ∈ Matrix.unitaryGroup`
for any `σ : Equiv.Perm (Fin n)`.

Proof: both `star (permMatrix σ) * permMatrix σ = 1` and the mirror identity
follow from `Matrix.conjTranspose_permMatrix` + `Matrix.permMatrix_mul` +
inverse cancellation. -/
theorem permMatrix_mem_unitaryGroup {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.permMatrix ℂ σ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  refine ⟨?_, ?_⟩
  · -- star (permMatrix σ) * permMatrix σ = 1
    rw [star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    rw [show Equiv.Perm.permMatrix ℂ σ⁻¹ * Equiv.Perm.permMatrix ℂ σ =
            Equiv.Perm.permMatrix ℂ (σ * σ⁻¹) from by
      rw [Matrix.permMatrix_mul]]
    rw [mul_inv_cancel σ, Matrix.permMatrix_one]
  · -- permMatrix σ * star (permMatrix σ) = 1
    rw [star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    rw [show Equiv.Perm.permMatrix ℂ σ * Equiv.Perm.permMatrix ℂ σ⁻¹ =
            Equiv.Perm.permMatrix ℂ (σ⁻¹ * σ) from by
      rw [Matrix.permMatrix_mul]]
    rw [inv_mul_cancel σ, Matrix.permMatrix_one]

/-- **`permMatrix σ` as element of `unitaryGroup`** — convenient bundling. -/
noncomputable def permMatrixAsUnitary {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ↥(Matrix.unitaryGroup (Fin n) ℂ) :=
  ⟨Equiv.Perm.permMatrix ℂ σ, permMatrix_mem_unitaryGroup σ⟩

/-- The underlying matrix of `permMatrixAsUnitary σ` is `permMatrix ℂ σ`. -/
@[simp]
theorem permMatrixAsUnitary_val {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permMatrixAsUnitary σ).val = Equiv.Perm.permMatrix ℂ σ :=
  rfl

/-- **`star (permMatrixAsUnitary σ).val = permMatrix ℂ σ⁻¹`** —
explicit star-form for use with S26 conjugation lemmas. -/
theorem permMatrixAsUnitary_star {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    star (permMatrixAsUnitary σ).val = Equiv.Perm.permMatrix ℂ σ⁻¹ := by
  rw [permMatrixAsUnitary_val, star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]

end SKEFTHawking.FKLW.GenericSUd
