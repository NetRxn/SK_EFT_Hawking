/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2 (D) witness substrate — exp commutes with the per-qubit embedding

The 3-qubit analog of `TrappedIonSU4ExpCommute`: packages each per-qubit Kronecker embedding
`SU(2) → SU(8)` (qubit 1: `A ↦ A ⊗ I₄`; qubit 2: `B ↦ I₂ ⊗ B ⊗ I₂`; qubit 3: `C ↦ I₄ ⊗ C`)
as a **continuous `RingHom`** on the matrix algebras, and applies Mathlib's `NormedSpace.map_exp`
(continuous ring homs commute with `NormedSpace.exp`) to obtain

  `kronSU2SU4 (exp X) 1 = exp (kronSU2SU4 X 1)`            (qubit 1)
  `kronSU2SU4 1 (kronSU4 (exp X) 1) = exp (kronSU2SU4 1 (kronSU4 X 1))`  (qubit 2)
  `kronSU4SU2 1 (exp X) = exp (kronSU4SU2 1 X)`            (qubit 3)

Consequence (used by the witness `hX_flow`): for a per-qubit 𝔰𝔲(2) tangent `x`, the SU(8)
one-parameter subgroup `exp(t • (x embedded)) = (exp(t•x) embedded)` is the embedded image of the
SU(2) one-parameter subgroup — which lands in `H_of_G` by per-qubit containment (next module),
using that `H_of_G cliffordTGeneratingSet = ⊤` (Phase 6u, `cliffordT_H_of_G_eq_top_unconditional`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 PROPER — (D) witness substrate
(exp/embedding commute → per-qubit tangent flow lines). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8QubitEmbed
import SKEFTHawking.FKLW.TrappedIonSU4ExpCommute

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. zero / add structure of the SU(8) Kronecker embeddings -/

theorem kronSU2SU4_zero_right_one :
    kronSU2SU4 (0 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 4) (Fin 4) ℂ) = 0 := by
  have h : Matrix.kronecker (0 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 4) (Fin 4) ℂ) = 0 :=
    Matrix.zero_kronecker 1
  unfold kronSU2SU4; rw [h]; simp

theorem kronSU2SU4_add_right_one (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU2SU4 (A + B) 1 = kronSU2SU4 A 1 + kronSU2SU4 B 1 := by
  have h : Matrix.kronecker (A + B) (1 : Matrix (Fin 4) (Fin 4) ℂ) =
      Matrix.kronecker A 1 + Matrix.kronecker B 1 := Matrix.add_kronecker A B 1
  unfold kronSU2SU4; rw [h]; ext i j; simp [Matrix.submatrix_apply]

theorem kronSU2SU4_zero_left_one :
    kronSU2SU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) (0 : Matrix (Fin 4) (Fin 4) ℂ) = 0 := by
  have h : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (0 : Matrix (Fin 4) (Fin 4) ℂ) = 0 :=
    Matrix.kronecker_zero 1
  unfold kronSU2SU4; rw [h]; simp

theorem kronSU2SU4_add_left_one (C D : Matrix (Fin 4) (Fin 4) ℂ) :
    kronSU2SU4 1 (C + D) = kronSU2SU4 1 C + kronSU2SU4 1 D := by
  have h : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (C + D) =
      Matrix.kronecker 1 C + Matrix.kronecker 1 D := Matrix.kronecker_add 1 C D
  unfold kronSU2SU4; rw [h]; ext i j; simp [Matrix.submatrix_apply]

theorem kronSU4SU2_zero_left_one :
    kronSU4SU2 (1 : Matrix (Fin 4) (Fin 4) ℂ) (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  have h : Matrix.kronecker (1 : Matrix (Fin 4) (Fin 4) ℂ) (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 :=
    Matrix.kronecker_zero 1
  unfold kronSU4SU2; rw [h]; simp

theorem kronSU4SU2_add_left_one (C D : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4SU2 1 (C + D) = kronSU4SU2 1 C + kronSU4SU2 1 D := by
  have h : Matrix.kronecker (1 : Matrix (Fin 4) (Fin 4) ℂ) (C + D) =
      Matrix.kronecker 1 C + Matrix.kronecker 1 D := Matrix.kronecker_add 1 C D
  unfold kronSU4SU2; rw [h]; ext i j; simp [Matrix.submatrix_apply]

/-! ## 2. The three per-qubit matrix embeddings as `RingHom`s -/

/-- **Per-qubit-1 matrix embedding `A ↦ A ⊗ I₄`** as a `RingHom`. -/
noncomputable def qubit1MatRingHom :
    Matrix (Fin 2) (Fin 2) ℂ →+* Matrix (Fin 8) (Fin 8) ℂ where
  toFun A := kronSU2SU4 A 1
  map_one' := kronSU2SU4_one
  map_mul' := kronSU2SU4_q1_mul
  map_zero' := kronSU2SU4_zero_right_one
  map_add' := kronSU2SU4_add_right_one

/-- **Per-qubit-2 matrix embedding `B ↦ I₂ ⊗ B ⊗ I₂`** as a `RingHom`. -/
noncomputable def qubit2MatRingHom :
    Matrix (Fin 2) (Fin 2) ℂ →+* Matrix (Fin 8) (Fin 8) ℂ where
  toFun B := kronSU2SU4 1 (kronSU4 B 1)
  map_one' := by
    show kronSU2SU4 1 (kronSU4 1 1) = 1
    rw [kronSU4_one]; exact kronSU2SU4_one
  map_mul' := kronSU2SU4_q2_mul
  map_zero' := by
    show kronSU2SU4 1 (kronSU4 0 1) = 0
    rw [kronSU4_zero_right_one]; exact kronSU2SU4_zero_left_one
  map_add' := by
    intro A B
    show kronSU2SU4 1 (kronSU4 (A + B) 1) =
      kronSU2SU4 1 (kronSU4 A 1) + kronSU2SU4 1 (kronSU4 B 1)
    rw [kronSU4_add_right_one, kronSU2SU4_add_left_one]

/-- **Per-qubit-3 matrix embedding `C ↦ I₄ ⊗ C`** as a `RingHom`. -/
noncomputable def qubit3MatRingHom :
    Matrix (Fin 2) (Fin 2) ℂ →+* Matrix (Fin 8) (Fin 8) ℂ where
  toFun C := kronSU4SU2 1 C
  map_one' := kronSU4SU2_one
  map_mul' := kronSU4SU2_q3_mul
  map_zero' := kronSU4SU2_zero_left_one
  map_add' := kronSU4SU2_add_left_one

/-! ## 3. exp commutes with the per-qubit embeddings -/

/-- **exp commutes with the qubit-1 embedding**. -/
theorem kronSU2SU4_exp_q1 (X : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU2SU4 (NormedSpace.exp X) 1 = NormedSpace.exp (kronSU2SU4 X 1) :=
  NormedSpace.map_exp qubit1MatRingHom continuous_kronSU2SU4_right_one X

/-- **exp commutes with the qubit-2 embedding**. -/
theorem kronSU2SU4_kronSU4_exp_q2 (X : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU2SU4 1 (kronSU4 (NormedSpace.exp X) 1) =
      NormedSpace.exp (kronSU2SU4 1 (kronSU4 X 1)) :=
  NormedSpace.map_exp qubit2MatRingHom
    (continuous_kronSU2SU4_left_one.comp continuous_kronSU4_right_one) X

/-- **exp commutes with the qubit-3 embedding**. -/
theorem kronSU4SU2_exp_q3 (X : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4SU2 1 (NormedSpace.exp X) = NormedSpace.exp (kronSU4SU2 1 X) :=
  NormedSpace.map_exp qubit3MatRingHom continuous_kronSU4SU2_left_one X

end SKEFTHawking.FKLW.CliffordCCZSU8
