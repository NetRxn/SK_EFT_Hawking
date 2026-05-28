/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2 (D) witness — entangling-tangent flow spread (foundation)

The `hX_flow` field of the SU(8) `ClosureDenseWitness` requires flow lines for the 54 entangling
tangents (weight ≥ 2). Per the DR blueprint §5.3, these are reached from the 9 per-qubit flows
(`CliffordCCZSU8PerQubitFlow`) by **conjugation** (`GenericSUd.flow_conj_mem`: a flow for `X` plus
`R ∈ H_of_G` gives a flow for `R·X·R⁻¹`), with `R` ranging over the CNOT entanglers and per-qubit
Cliffords (all in `H_of_G`, being alphabet generators / products thereof). The base entanglers come
from the CNOT Pauli-conjugation table (`CNOT₁₂·(σ_a⊗I⊗I)·CNOT₁₂ = σ_a⊗σ_a⊗I` etc.), and per-qubit
Cliffords rotate each factor — exactly the SU(4) `TrappedIonSU4EntanglerSpread` methodology scaled
to 63 = 27 two-qubit + 27 three-qubit. (Trotter is NOT used; this is the conjugation route.)

This module ships the **CNOT involution foundation**: each `CNOT_{ij}` is an involution
(`CNOT² = 1`), hence its matrix inverse is itself, so conjugation by `CNOT_{ij}` is `CNOT·M·CNOT`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 PROPER — (D) witness entangling spread
(CNOT involution foundation). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8CNOT
import SKEFTHawking.FKLW.CliffordCCZSU8Tangents

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4

/-! ## 1. The CNOT permutations are involutions -/

theorem σ_cnot_12_mul_self : σ_cnot_12 * σ_cnot_12 = 1 := by decide
theorem σ_cnot_13_mul_self : σ_cnot_13 * σ_cnot_13 = 1 := by decide
theorem σ_cnot_23_mul_self : σ_cnot_23 * σ_cnot_23 = 1 := by decide

/-! ## 2. `CNOT_{ij}_mat` is an involution; its matrix inverse is itself -/

theorem CNOT_12_mat_mul_self : CNOT_12_mat * CNOT_12_mat = 1 := by
  rw [CNOT_12_mat, ← permMatrix_mul, σ_cnot_12_mul_self, permMatrix_one]
theorem CNOT_13_mat_mul_self : CNOT_13_mat * CNOT_13_mat = 1 := by
  rw [CNOT_13_mat, ← permMatrix_mul, σ_cnot_13_mul_self, permMatrix_one]
theorem CNOT_23_mat_mul_self : CNOT_23_mat * CNOT_23_mat = 1 := by
  rw [CNOT_23_mat, ← permMatrix_mul, σ_cnot_23_mul_self, permMatrix_one]

theorem CNOT_12_mat_inv : (CNOT_12_mat)⁻¹ = CNOT_12_mat := Matrix.inv_eq_left_inv CNOT_12_mat_mul_self
theorem CNOT_13_mat_inv : (CNOT_13_mat)⁻¹ = CNOT_13_mat := Matrix.inv_eq_left_inv CNOT_13_mat_mul_self
theorem CNOT_23_mat_inv : (CNOT_23_mat)⁻¹ = CNOT_23_mat := Matrix.inv_eq_left_inv CNOT_23_mat_mul_self

/-! ## 3. Generic permutation-matrix conjugation = index relabel -/

theorem permMatrix_fin8_inv (σ : Equiv.Perm (Fin 8)) :
    (Equiv.Perm.permMatrix ℂ σ)⁻¹ = Equiv.Perm.permMatrix ℂ σ⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [← permMatrix_mul, mul_inv_cancel, permMatrix_one]

/-- **Conjugation by a permutation matrix is an index relabel**:
`permMatrix σ · M · (permMatrix σ)⁻¹ = M.submatrix σ σ` (entry `(i,j) ↦ M (σ i) (σ j)`). This
collapses the permutation sum via the `PEquiv` row/column-relabel lemmas — no 8-term expansion. -/
theorem permMatrix_fin8_conj (σ : Equiv.Perm (Fin 8)) (M : Matrix (Fin 8) (Fin 8) ℂ) :
    Equiv.Perm.permMatrix ℂ σ * M * (Equiv.Perm.permMatrix ℂ σ)⁻¹ = M.submatrix ⇑σ ⇑σ := by
  rw [permMatrix_fin8_inv]
  show σ.toPEquiv.toMatrix * M * (σ⁻¹).toPEquiv.toMatrix = M.submatrix ⇑σ ⇑σ
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  simp only [Function.comp_id, Function.id_comp, Equiv.Perm.inv_def, Equiv.symm_symm]

/-! ## 4. Base CNOT Pauli-conjugation identity (validation: submatrix relabel of a tensor-Pauli) -/

/-- **Base entangler on pair (1,2)**: `CNOT₁₂·(σ_x⊗I⊗I)·CNOT₁₂⁻¹ = σ_x⊗σ_x⊗I`. -/
theorem cnot12_conj_X1 :
    CNOT_12_mat * kronSU8 SKEFTHawking.σ_x 1 1 * (CNOT_12_mat)⁻¹
      = kronSU8 SKEFTHawking.σ_x SKEFTHawking.σ_x 1 := by
  rw [CNOT_12_mat, permMatrix_fin8_conj]
  unfold kronSU8 kronSU2SU4 kronSU4 σ_cnot_12
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix_apply, Matrix.reindex_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, SKEFTHawking.σ_x, finProdFinEquiv, Equiv.swap_apply_def,
      Fin.divNat, Fin.modNat, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff]

/-- **Base entangler on pair (1,3)**: `CNOT₁₃·(σ_x⊗I⊗I)·CNOT₁₃⁻¹ = σ_x⊗I⊗σ_x`. -/
theorem cnot13_conj_X1 :
    CNOT_13_mat * kronSU8 SKEFTHawking.σ_x 1 1 * (CNOT_13_mat)⁻¹
      = kronSU8 SKEFTHawking.σ_x 1 SKEFTHawking.σ_x := by
  rw [CNOT_13_mat, permMatrix_fin8_conj]
  unfold kronSU8 kronSU2SU4 kronSU4 σ_cnot_13
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix_apply, Matrix.reindex_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, SKEFTHawking.σ_x, finProdFinEquiv, Equiv.swap_apply_def,
      Fin.divNat, Fin.modNat, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff]

/-- **Base entangler on pair (2,3)**: `CNOT₂₃·(I⊗σ_x⊗I)·CNOT₂₃⁻¹ = I⊗σ_x⊗σ_x`. -/
theorem cnot23_conj_X2 :
    CNOT_23_mat * kronSU8 1 SKEFTHawking.σ_x 1 * (CNOT_23_mat)⁻¹
      = kronSU8 1 SKEFTHawking.σ_x SKEFTHawking.σ_x := by
  rw [CNOT_23_mat, permMatrix_fin8_conj]
  unfold kronSU8 kronSU2SU4 kronSU4 σ_cnot_23
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix_apply, Matrix.reindex_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, SKEFTHawking.σ_x, finProdFinEquiv, Equiv.swap_apply_def,
      Fin.divNat, Fin.modNat, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff]

/-- **Base 3-qubit entangler**: `CNOT₂₃·(σ_x⊗σ_x⊗I)·CNOT₂₃⁻¹ = σ_x⊗σ_x⊗σ_x`. -/
theorem cnot23_conj_X1X2 :
    CNOT_23_mat * kronSU8 SKEFTHawking.σ_x SKEFTHawking.σ_x 1 * (CNOT_23_mat)⁻¹
      = kronSU8 SKEFTHawking.σ_x SKEFTHawking.σ_x SKEFTHawking.σ_x := by
  rw [CNOT_23_mat, permMatrix_fin8_conj]
  unfold kronSU8 kronSU2SU4 kronSU4 σ_cnot_23
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix_apply, Matrix.reindex_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, SKEFTHawking.σ_x, finProdFinEquiv, Equiv.swap_apply_def,
      Fin.divNat, Fin.modNat, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff]

end SKEFTHawking.FKLW.CliffordCCZSU8
