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
import SKEFTHawking.FKLW.CliffordCCZSU8TangentSpan
import SKEFTHawking.FKLW.CliffordCCZSU8CNOT

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4

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

/-! ## 2. The 3-qubit bit-iso and `kronK8` bit-entry / CNOT bit-actions

The CNOT conjugation reindexes `kronK8 v` by `σ_cnot`, which acts on `Fin 8` by permuting the 3-qubit
bit decomposition. This section sets up the bit-iso `Fin 2 × Fin 2 × Fin 2 ≃ Fin 8` (matching the
`kronSU8 = kronSU2SU4 ∘ kronSU4` Kronecker structure), the entrywise formula for `kronK8` in those bits,
and the per-CNOT bit-action (each flips the target bit iff the control bit is set). -/

/-- The 3-qubit bit isomorphism `Fin 2 × Fin 2 × Fin 2 ≃ Fin 8` matching `kronSU8`'s nested-Kronecker
index structure: `(q₁, q₂, q₃) ↦ finProdFinEquiv (q₁, finProdFinEquiv (q₂, q₃))`. -/
def bitIso8 : Fin 2 × Fin 2 × Fin 2 ≃ Fin 8 :=
  ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- **`kronK8` bit-entry formula**: at bit-decomposed indices, the tensor-Pauli matrix factors as the
product of the three single-qubit Pauli entries. -/
theorem kronK8_bitIso8_apply (v : Fin 4 × Fin 4 × Fin 4) (i j : Fin 2 × Fin 2 × Fin 2) :
    kronK8 v (bitIso8 i) (bitIso8 j)
      = pauli4 v.1 i.1 j.1 * pauli4 v.2.1 i.2.1 j.2.1 * pauli4 v.2.2 i.2.2 j.2.2 := by
  unfold kronK8 kronSU8 kronSU2SU4 kronSU4 bitIso8
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id_eq,
    Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

/-- **CNOT₁₂ bit-action**: flips bit 2 iff bit 1 is set. -/
theorem cnot12_bitIso8 (b : Fin 2 × Fin 2 × Fin 2) :
    σ_cnot_12 (bitIso8 b) = bitIso8 (b.1, b.1 + b.2.1, b.2.2) := by
  obtain ⟨b1, b2, b3⟩ := b; fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> decide

/-- **CNOT₁₃ bit-action**: flips bit 3 iff bit 1 is set. -/
theorem cnot13_bitIso8 (b : Fin 2 × Fin 2 × Fin 2) :
    σ_cnot_13 (bitIso8 b) = bitIso8 (b.1, b.2.1, b.1 + b.2.2) := by
  obtain ⟨b1, b2, b3⟩ := b; fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> decide

/-- **CNOT₂₃ bit-action**: flips bit 3 iff bit 2 is set. -/
theorem cnot23_bitIso8 (b : Fin 2 × Fin 2 × Fin 2) :
    σ_cnot_23 (bitIso8 b) = bitIso8 (b.1, b.2.1, b.2.1 + b.2.2) := by
  obtain ⟨b1, b2, b3⟩ := b; fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> decide

end SKEFTHawking.FKLW.CliffordCCZSU8
