/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Permutation-conjugation preserves linftyOp norm

For `σ : Equiv.Perm (Fin n)` and any `A : Matrix (Fin n) (Fin n) ℂ`:

  `‖permMatrix σ · A · permMatrix σ⁻¹‖_linftyOp = ‖A‖_linftyOp`

Permutation conjugation relabels rows/columns, preserving the max-row-sum
linftyOp norm. Proven via the entry-wise identity
`permMatrix σ · A · permMatrix σ⁻¹ = Matrix.reindex σ⁻¹ σ⁻¹ A` + the
Phase 6x M.1 lemma `Matrix.linftyOpNorm_reindex`.

This is the bridge connecting the eigenvalue-sort permutation conjugation
(Session 28/31) to the σ_y-sum norm bound (Session 70): the inner witness
`F_inner = permMatrix σ · (∑_p γ_p σ_y(p)) · permMatrix σ⁻¹` has the same
linftyOp norm as `∑_p γ_p σ_y(p)`, hence `≤ ∑_p |γ_p|`.

## Substantive content shipped

  * `permMatrix_conj_eq_reindex` — entry-wise identity
    `permMatrix σ · A · permMatrix σ⁻¹ = Matrix.reindex σ⁻¹ σ⁻¹ A`
  * `permMatrix_conj_linftyOpNorm_eq` — norm preservation

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — permutation-conjugation
norm preservation (F_inner norm bound bridge).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdPermutationConjugation
import SKEFTHawking.FKLW.GenericSUdSigmaYSumNormBound
import SKEFTHawking.MatrixBCHCubicMathlibPR

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Entry-wise identity**: `permMatrix σ · A · permMatrix σ⁻¹ = reindex σ⁻¹ σ⁻¹ A`.

In Mathlib's convention `(permMatrix σ)_{ik} = if σ i = k then 1 else 0`,
so `(permMatrix σ · A · permMatrix σ⁻¹)_{ij} = A_{σ i, σ j}`, which equals
`(reindex σ⁻¹ σ⁻¹ A)_{ij} = A ((σ⁻¹).symm i) ((σ⁻¹).symm j) = A (σ i) (σ j)`. -/
theorem permMatrix_conj_eq_reindex {n : ℕ} (σ : Equiv.Perm (Fin n))
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (Equiv.Perm.permMatrix ℂ σ) * A * (Equiv.Perm.permMatrix ℂ σ⁻¹) =
      Matrix.reindex σ⁻¹ σ⁻¹ A := by
  rw [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
      Matrix.submatrix_submatrix]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.Perm.inv_def,
    Equiv.symm_symm, Function.comp_apply, id_eq]

/-- **Permutation-conjugation preserves linftyOp norm**:
`‖permMatrix σ · A · permMatrix σ⁻¹‖ = ‖A‖`. -/
theorem permMatrix_conj_linftyOpNorm_eq {n : ℕ} (σ : Equiv.Perm (Fin n))
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖(Equiv.Perm.permMatrix ℂ σ) * A * (Equiv.Perm.permMatrix ℂ σ⁻¹)‖ = ‖A‖ := by
  rw [permMatrix_conj_eq_reindex]
  exact Matrix.linftyOpNorm_reindex σ⁻¹ A

/-- **F_inner-form norm bound**: a permMatrix-conjugated σ_y-block sum has
linftyOp norm `≤ ∑ |γ_p|`.

This is the composition of `permMatrix_conj_linftyOpNorm_eq` (Session 71)
with `sigmaYBlock_sum_linftyOpNorm_le` (Session 70): for the inner
diagonal-case witness `F_inner = permMatrix σ · (∑ γ_p σ_y) · permMatrix σ⁻¹`
(eigenvalue-sort conjugation, Session 31), this directly gives
`‖F_inner‖ ≤ ∑ |γ_p|`. -/
theorem permMatrix_conj_sigmaYBlock_sum_norm_le {n : ℕ} {ι : Type*}
    (σ : Equiv.Perm (Fin n)) (s : Finset ι) (γ : ι → ℝ) (a b : ι → Fin n)
    (h_ne : ∀ p ∈ s, a p ≠ b p) :
    ‖(Equiv.Perm.permMatrix ℂ σ) *
        (∑ p ∈ s, ((γ p : ℂ)) • sigmaYBlock (a p) (b p)) *
        (Equiv.Perm.permMatrix ℂ σ⁻¹)‖ ≤ ∑ p ∈ s, |γ p| := by
  rw [permMatrix_conj_linftyOpNorm_eq]
  exact sigmaYBlock_sum_linftyOpNorm_le s γ a b h_ne

/-- **`permMatrixAsUnitary` conjugation preserves linftyOp norm** — the exact
form used by Session 31's `symmetric_balanced_commutator_diagonal_real_full`
(`F = P.val · F' · star P.val` with `P = permMatrixAsUnitary σ`).

`‖(permMatrixAsUnitary σ).val · A · star (permMatrixAsUnitary σ).val‖ = ‖A‖`.

Composes `permMatrixAsUnitary_val` + `permMatrixAsUnitary_star` (Session 27)
with `permMatrix_conj_linftyOpNorm_eq` (Session 71). -/
theorem permMatrixAsUnitary_conj_linftyOpNorm_eq {n : ℕ} (σ : Equiv.Perm (Fin n))
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖(permMatrixAsUnitary σ).val * A * star (permMatrixAsUnitary σ).val‖ = ‖A‖ := by
  rw [permMatrixAsUnitary_val, star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
  exact permMatrix_conj_linftyOpNorm_eq σ A

end SKEFTHawking.FKLW.GenericSUd
