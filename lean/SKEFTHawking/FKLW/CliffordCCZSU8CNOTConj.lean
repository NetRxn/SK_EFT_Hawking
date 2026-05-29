/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4f.2b (part 1) — permutation-matrix conjugation as a submatrix reindex

The CNOT generators are permutation matrices (`CNOT_{ct}_mat = Equiv.Perm.permMatrix ℂ σ_cnot`), so their
conjugation action on the tensor-Paulis is a **reindexing**. This module ships the general fact

  `permMatrix σ · M · permMatrix σ⁻¹ = M.submatrix σ σ`  (i.e. `(…) i j = M (σ i) (σ j)`),

the reusable first step of the CNOT tableau lift `CNOT · kronK8 v · CNOT⁻¹ = ± kronK8 (cnotLabel v)`.
(The remaining step — identifying the reindexed `kronK8 v` with the CNOT-transformed tensor-Pauli via the
3-bit index decomposition — is the companion increment.) Clean general lemma, Mathlib-PR-quality.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4f.2b part 1 (permMatrix conjugation reindex). 2026-05-29.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

/-- **Conjugation by a permutation matrix is a submatrix reindex**: for any permutation `σ` of a finite
type and any square matrix `M`, `permMatrix σ · M · permMatrix σ⁻¹ = M.submatrix σ σ`, i.e. entrywise
`(permMatrix σ · M · permMatrix σ⁻¹) i j = M (σ i) (σ j)`.

This is the structural form of the CNOT (and any permutation-gate) conjugation action: conjugating a
matrix by a permutation matrix permutes its rows and columns by `σ`. -/
theorem permMatrix_conj_eq_submatrix {n : Type*} [Fintype n] [DecidableEq n]
    (σ : Equiv.Perm n) (M : Matrix n n ℂ) :
    Equiv.Perm.permMatrix ℂ σ * M * Equiv.Perm.permMatrix ℂ σ⁻¹ = M.submatrix σ σ := by
  ext i j
  simp only [Matrix.mul_apply, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply,
    Matrix.submatrix_apply, Option.mem_some_iff, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Equiv.Perm.inv_def, Equiv.symm_apply_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end SKEFTHawking.FKLW.CliffordCCZSU8
