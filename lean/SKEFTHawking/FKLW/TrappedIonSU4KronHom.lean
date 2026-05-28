/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness substrate — `kronSU4` is a homomorphism

Foundational substrate for the SU(4) trapped-ion `ClosureDenseWitness` (the
Brylinski-Brylinski universality discharge). The per-ion embeddings
`A ↦ kronSU4 A 1` (ion 1) and `B ↦ kronSU4 1 B` (ion 2) are continuous group
homomorphisms `SU(2) → SU(4)`; their multiplicativity rests on the Kronecker
mixed-product property `(A⊗B)(C⊗D) = (AC)⊗(BD)` together with the fact that the
shared row/col reindex `finProdFinEquiv` respects matrix multiplication.

This module ships the two load-bearing facts:
  * `kronSU4_one` — `kronSU4 1 1 = 1`.
  * `kronSU4_mul` — `kronSU4 (A*C) (B*D) = kronSU4 A B * kronSU4 C D`.

plus the per-ion specializations used to build the embedding monoid homs.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness
substrate (per-ion embedding homomorphism foundation). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4Substrate

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

/-! ## 1. `reindex` (shared equiv) respects matrix multiplication -/

/-- For a single equiv `e` used on both rows and columns, `reindex e e`
distributes over matrix multiplication. (Special case of
`Matrix.submatrix_mul_equiv`, since `reindex e e M = submatrix M e.symm e.symm`.) -/
theorem reindex_self_mul {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) (M N : Matrix m m ℂ) :
    Matrix.reindex e e (M * N) =
      Matrix.reindex e e M * Matrix.reindex e e N := by
  show Matrix.submatrix (M * N) e.symm e.symm =
    Matrix.submatrix M e.symm e.symm * Matrix.submatrix N e.symm e.symm
  exact (Matrix.submatrix_mul_equiv M N e.symm e.symm e.symm).symm

/-! ## 2. `kronSU4` identity and multiplicativity -/

/-- **`kronSU4 1 1 = 1`**: Kronecker of identities, reindexed, is the identity. -/
theorem kronSU4_one : kronSU4 (1 : Matrix (Fin 2) (Fin 2) ℂ)
    (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have h1 : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ)
      (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := Matrix.one_kronecker_one
  unfold kronSU4
  rw [h1]
  exact Matrix.submatrix_one_equiv finProdFinEquiv.symm

/-- **`kronSU4` mixed-product (homomorphism) property**:
`kronSU4 (A*C) (B*D) = kronSU4 A B * kronSU4 C D`. -/
theorem kronSU4_mul (A B C D : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4 (A * C) (B * D) = kronSU4 A B * kronSU4 C D := by
  have hmix : Matrix.kronecker (A * C) (B * D) =
      Matrix.kronecker A B * Matrix.kronecker C D :=
    Matrix.mul_kronecker_mul A C B D
  unfold kronSU4
  rw [hmix, reindex_self_mul finProdFinEquiv (Matrix.kronecker A B) (Matrix.kronecker C D)]

/-! ## 3. Per-ion specializations (ion 1: `· ⊗ 1`; ion 2: `1 ⊗ ·`) -/

/-- **Ion-1 embedding is multiplicative**: `kronSU4 (A*C) 1 = kronSU4 A 1 * kronSU4 C 1`. -/
theorem kronSU4_ion1_mul (A C : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4 (A * C) (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      kronSU4 A 1 * kronSU4 C 1 := by
  have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) * 1 :=
    (one_mul _).symm
  rw [h, kronSU4_mul, mul_one]

/-- **Ion-2 embedding is multiplicative**: `kronSU4 1 (B*D) = kronSU4 1 B * kronSU4 1 D`. -/
theorem kronSU4_ion2_mul (B D : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) (B * D) =
      kronSU4 1 B * kronSU4 1 D := by
  have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) * 1 :=
    (one_mul _).symm
  rw [h, kronSU4_mul, mul_one]

end SKEFTHawking.FKLW.TrappedIonSU4
