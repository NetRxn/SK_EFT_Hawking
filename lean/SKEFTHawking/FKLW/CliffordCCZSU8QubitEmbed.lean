/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2 (D) witness substrate — per-qubit SU(2) → SU(8) embeddings

The 3-qubit analog of the SU(4) `ion{1,2}Embed`: continuous monoid homomorphisms
`SU(2) → SU(8)` that act on one qubit and the identity on the other two.

  * qubit 1: `A ↦ A ⊗ I₄`        (`kronSU2SU4 A 1`)
  * qubit 2: `B ↦ I ⊗ B ⊗ I`     (`kronSU2SU4 1 (kronSU4 B 1)`)
  * qubit 3: `C ↦ I₄ ⊗ C`        (`kronSU4SU2 1 C`)

These are the maps through which per-qubit single-qubit gate density lifts to per-qubit 𝔰𝔲(2)
flow-line containment in `H_of_G`, the per-qubit half of the SU(8) `ClosureDenseWitness`.

This module is **alphabet-agnostic substrate**: the embedding homomorphisms are needed by any
SU(8) gate set that acts qubit-wise (Clifford+CCZ, Clifford+T+CCZ, Clifford+T). Supporting
Kronecker monoid-hom lemmas (`kronSU2SU4_one`/`kronSU4SU2_one`/`kronSU4SU2_mul` + per-qubit
multiplicativity) mirror the SU(4) `kronSU4` monoid-hom substrate.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 PROPER — (D) witness substrate
(per-qubit embedding monoid homs). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8TangentSpan
import SKEFTHawking.FKLW.TrappedIonSU4KronHom

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4

/-! ## 1. Kronecker identity + multiplicativity for the SU(8) reindexers -/

/-- `kronSU2SU4 1 1 = 1`. -/
theorem kronSU2SU4_one :
    kronSU2SU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
  have h1 : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 :=
    Matrix.one_kronecker_one
  unfold kronSU2SU4
  rw [h1]
  exact Matrix.submatrix_one_equiv finProdFinEquiv.symm

/-- `kronSU4SU2 1 1 = 1`. -/
theorem kronSU4SU2_one :
    kronSU4SU2 (1 : Matrix (Fin 4) (Fin 4) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have h1 : Matrix.kronecker (1 : Matrix (Fin 4) (Fin 4) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.one_kronecker_one
  unfold kronSU4SU2
  rw [h1]
  exact Matrix.submatrix_one_equiv finProdFinEquiv.symm

/-- **`kronSU4SU2` mixed-product**: `kronSU4SU2 (A*C) (B*D) = kronSU4SU2 A B * kronSU4SU2 C D`. -/
theorem kronSU4SU2_mul (A C : Matrix (Fin 4) (Fin 4) ℂ) (B D : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4SU2 (A * C) (B * D) = kronSU4SU2 A B * kronSU4SU2 C D := by
  have hmix : Matrix.kronecker (A * C) (B * D) =
      Matrix.kronecker A B * Matrix.kronecker C D :=
    Matrix.mul_kronecker_mul A C B D
  unfold kronSU4SU2
  rw [hmix, reindex_self_mul finProdFinEquiv (Matrix.kronecker A B) (Matrix.kronecker C D)]

/-- Per-qubit-1 multiplicativity: `kronSU2SU4 (A*C) 1 = kronSU2SU4 A 1 * kronSU2SU4 C 1`. -/
theorem kronSU2SU4_q1_mul (A C : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU2SU4 (A * C) 1 = kronSU2SU4 A 1 * kronSU2SU4 C 1 := by
  conv_lhs => rw [show (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 * 1 from (one_mul _).symm]
  rw [kronSU2SU4_mul]

/-- Per-qubit-2 multiplicativity (inner `kronSU4 · 1`). -/
theorem kronSU2SU4_q2_mul (B D : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU2SU4 1 (kronSU4 (B * D) 1)
      = kronSU2SU4 1 (kronSU4 B 1) * kronSU2SU4 1 (kronSU4 D 1) := by
  rw [← kronSU2SU4_mul, ← kronSU4_ion1_mul, one_mul]

/-- Per-qubit-3 multiplicativity: `kronSU4SU2 1 (C*E) = kronSU4SU2 1 C * kronSU4SU2 1 E`. -/
theorem kronSU4SU2_q3_mul (C E : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4SU2 1 (C * E) = kronSU4SU2 1 C * kronSU4SU2 1 E := by
  conv_lhs => rw [show (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 * 1 from (one_mul _).symm]
  rw [kronSU4SU2_mul]

/-! ## 2. SU(4) identity membership -/

theorem one_mem_su4' : (1 : Matrix (Fin 4) (Fin 4) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ :=
  one_mem _

theorem one_mem_su2' : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  one_mem _

/-- The inner `kronSU4 B 1 ∈ SU(4)` for `B ∈ SU(2)`. -/
theorem kronSU4_q2_mem (B : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    kronSU4 (B : Matrix (Fin 2) (Fin 2) ℂ) 1 ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ :=
  kronSU4_mem_specialUnitaryGroup B.2 one_mem_su2'

/-! ## 3. The three per-qubit embeddings as monoid homomorphisms -/

/-- **Per-qubit-1 embedding `SU(2) →* SU(8)`**: `A ↦ A ⊗ I₄`. -/
noncomputable def qubit1Embed :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) →* ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) where
  toFun A := ⟨kronSU2SU4 (A : Matrix (Fin 2) (Fin 2) ℂ) 1,
    kronSU2SU4_mem_specialUnitaryGroup A.2 one_mem_su4'⟩
  map_one' := by
    apply Subtype.ext
    show kronSU2SU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 = 1
    exact kronSU2SU4_one
  map_mul' A C := by
    apply Subtype.ext
    show kronSU2SU4 ((A : Matrix (Fin 2) (Fin 2) ℂ) * C) 1 =
      kronSU2SU4 (A : Matrix (Fin 2) (Fin 2) ℂ) 1 * kronSU2SU4 (C : Matrix (Fin 2) (Fin 2) ℂ) 1
    exact kronSU2SU4_q1_mul _ _

/-- **Per-qubit-2 embedding `SU(2) →* SU(8)`**: `B ↦ I ⊗ B ⊗ I`. -/
noncomputable def qubit2Embed :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) →* ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) where
  toFun B := ⟨kronSU2SU4 1 (kronSU4 (B : Matrix (Fin 2) (Fin 2) ℂ) 1),
    kronSU2SU4_mem_specialUnitaryGroup one_mem_su2' (kronSU4_q2_mem B)⟩
  map_one' := by
    apply Subtype.ext
    show kronSU2SU4 1 (kronSU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) 1) = 1
    rw [kronSU4_one]; exact kronSU2SU4_one
  map_mul' B D := by
    apply Subtype.ext
    show kronSU2SU4 1 (kronSU4 ((B : Matrix (Fin 2) (Fin 2) ℂ) * D) 1) =
      kronSU2SU4 1 (kronSU4 (B : Matrix (Fin 2) (Fin 2) ℂ) 1) *
        kronSU2SU4 1 (kronSU4 (D : Matrix (Fin 2) (Fin 2) ℂ) 1)
    exact kronSU2SU4_q2_mul _ _

/-- **Per-qubit-3 embedding `SU(2) →* SU(8)`**: `C ↦ I₄ ⊗ C`. -/
noncomputable def qubit3Embed :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) →* ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) where
  toFun C := ⟨kronSU4SU2 1 (C : Matrix (Fin 2) (Fin 2) ℂ),
    kronSU4SU2_mem_specialUnitaryGroup one_mem_su4' C.2⟩
  map_one' := by
    apply Subtype.ext
    show kronSU4SU2 1 (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
    exact kronSU4SU2_one
  map_mul' C E := by
    apply Subtype.ext
    show kronSU4SU2 1 ((C : Matrix (Fin 2) (Fin 2) ℂ) * E) =
      kronSU4SU2 1 (C : Matrix (Fin 2) (Fin 2) ℂ) * kronSU4SU2 1 (E : Matrix (Fin 2) (Fin 2) ℂ)
    exact kronSU4SU2_q3_mul _ _

/-! ## 4. Continuity of the underlying matrix maps -/

theorem continuous_kronSU2SU4_right_one :
    Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ => kronSU2SU4 A (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  unfold kronSU2SU4
  apply Continuous.matrix_submatrix
  apply continuous_matrix
  intro i j
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.of_apply]
  exact (continuous_apply_apply _ _).mul continuous_const

theorem continuous_kronSU4SU2_left_one :
    Continuous fun C : Matrix (Fin 2) (Fin 2) ℂ => kronSU4SU2 (1 : Matrix (Fin 4) (Fin 4) ℂ) C := by
  unfold kronSU4SU2
  apply Continuous.matrix_submatrix
  apply continuous_matrix
  intro i j
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.of_apply]
  exact continuous_const.mul (continuous_apply_apply _ _)

theorem continuous_kronSU2SU4_left_one :
    Continuous fun C : Matrix (Fin 4) (Fin 4) ℂ => kronSU2SU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) C := by
  unfold kronSU2SU4
  apply Continuous.matrix_submatrix
  apply continuous_matrix
  intro i j
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.of_apply]
  exact continuous_const.mul (continuous_apply_apply _ _)

theorem continuous_kronSU4_right_one :
    Continuous fun B : Matrix (Fin 2) (Fin 2) ℂ => kronSU4 B (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold kronSU4
  apply Continuous.matrix_submatrix
  apply continuous_matrix
  intro i j
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.of_apply]
  exact (continuous_apply_apply _ _).mul continuous_const

/-- **`qubit1Embed` is continuous**. -/
theorem qubit1Embed_continuous : Continuous qubit1Embed := by
  apply Continuous.subtype_mk
  exact continuous_kronSU2SU4_right_one.comp continuous_subtype_val

/-- **`qubit2Embed` is continuous**. -/
theorem qubit2Embed_continuous : Continuous qubit2Embed := by
  apply Continuous.subtype_mk
  exact (continuous_kronSU2SU4_left_one.comp continuous_kronSU4_right_one).comp
    continuous_subtype_val

/-- **`qubit3Embed` is continuous**. -/
theorem qubit3Embed_continuous : Continuous qubit3Embed := by
  apply Continuous.subtype_mk
  exact continuous_kronSU4SU2_left_one.comp continuous_subtype_val

end SKEFTHawking.FKLW.CliffordCCZSU8
