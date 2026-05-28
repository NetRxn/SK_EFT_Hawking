/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness substrate — per-ion SU(2) → SU(4) embeddings

Packages the per-ion Kronecker embeddings as **continuous monoid homomorphisms**
`SU(2) → SU(4)`:
  * ion 1: `A ↦ kronSU4 A 1`  (acts on the first qubit, identity on the second)
  * ion 2: `B ↦ kronSU4 1 B`  (identity on the first qubit, acts on the second)

These are the maps through which the already-shipped SU(2) Clifford+T density
(`cliffordT_density_unconditional`) lifts to per-ion 𝔰𝔲(2) flow-line containment in
`H_of_G (trappedIonGeneratingSetSU4 N hN)`, the per-ion half of the
Brylinski-Brylinski `ClosureDenseWitness`.

Multiplicativity is `kronSU4_ion{1,2}_mul`; identity is `kronSU4_one`; membership is
`kronSU4_mem_specialUnitaryGroup`; continuity is entrywise (`continuous_matrix`) through the
reindex (`Continuous.matrix_submatrix`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness substrate
(per-ion embedding monoid homs). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4KronHom

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

/-- `1 ∈ specialUnitaryGroup (Fin 2) ℂ` (re-derived; the substrate's version is `private`). -/
theorem one_mem_su2' : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈
    Matrix.specialUnitaryGroup (Fin 2) ℂ := one_mem _

/-! ## 1. Ion-1 embedding `A ↦ kronSU4 A 1` -/

/-- **Per-ion-1 embedding as a monoid homomorphism `SU(2) →* SU(4)`**:
`A ↦ ⟨kronSU4 A 1, _⟩`, acting on the first qubit and the identity on the second. -/
noncomputable def ion1Embed :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) →*
      ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ) where
  toFun A := ⟨kronSU4 (A : Matrix (Fin 2) (Fin 2) ℂ) 1,
    kronSU4_mem_specialUnitaryGroup A.2 one_mem_su2'⟩
  map_one' := by
    apply Subtype.ext
    show kronSU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 = 1
    exact kronSU4_one
  map_mul' A C := by
    apply Subtype.ext
    show kronSU4 ((A : Matrix (Fin 2) (Fin 2) ℂ) * C) 1 =
      kronSU4 (A : Matrix (Fin 2) (Fin 2) ℂ) 1 * kronSU4 (C : Matrix (Fin 2) (Fin 2) ℂ) 1
    exact kronSU4_ion1_mul _ _

/-- **Ion-2 embedding as a monoid homomorphism `SU(2) →* SU(4)`**:
`B ↦ ⟨kronSU4 1 B, _⟩`, the identity on the first qubit and acting on the second. -/
noncomputable def ion2Embed :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) →*
      ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ) where
  toFun B := ⟨kronSU4 1 (B : Matrix (Fin 2) (Fin 2) ℂ),
    kronSU4_mem_specialUnitaryGroup one_mem_su2' B.2⟩
  map_one' := by
    apply Subtype.ext
    show kronSU4 1 (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
    exact kronSU4_one
  map_mul' B D := by
    apply Subtype.ext
    show kronSU4 1 ((B : Matrix (Fin 2) (Fin 2) ℂ) * D) =
      kronSU4 1 (B : Matrix (Fin 2) (Fin 2) ℂ) * kronSU4 1 (D : Matrix (Fin 2) (Fin 2) ℂ)
    exact kronSU4_ion2_mul _ _

/-! ## 2. Continuity of the underlying matrix maps -/

/-- The matrix map `A ↦ kronSU4 A 1` is continuous (entrywise through the reindex). -/
theorem continuous_kronSU4_right_one :
    Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      kronSU4 A (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold kronSU4
  apply Continuous.matrix_submatrix
  apply continuous_matrix
  intro i j
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.of_apply]
  exact (continuous_apply_apply _ _).mul continuous_const

/-- The matrix map `B ↦ kronSU4 1 B` is continuous. -/
theorem continuous_kronSU4_left_one :
    Continuous fun B : Matrix (Fin 2) (Fin 2) ℂ =>
      kronSU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) B := by
  unfold kronSU4
  apply Continuous.matrix_submatrix
  apply continuous_matrix
  intro i j
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.of_apply]
  exact continuous_const.mul (continuous_apply_apply _ _)

/-- **`ion1Embed` is continuous**. -/
theorem ion1Embed_continuous : Continuous ion1Embed := by
  apply Continuous.subtype_mk
  exact continuous_kronSU4_right_one.comp continuous_subtype_val

/-- **`ion2Embed` is continuous**. -/
theorem ion2Embed_continuous : Continuous ion2Embed := by
  apply Continuous.subtype_mk
  exact continuous_kronSU4_left_one.comp continuous_subtype_val

end SKEFTHawking.FKLW.TrappedIonSU4
