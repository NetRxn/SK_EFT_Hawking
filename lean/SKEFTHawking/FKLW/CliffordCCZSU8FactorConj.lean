/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2 (D) witness — factor-wise conjugation by per-qubit embeddings

Conjugating a 3-qubit tensor `kronSU8 A B D` by a per-qubit embedding `qubit_iEmbed C` rotates
**only the qubit-i factor**: `qubit1Embed C` rotates `A`, `qubit2Embed C` rotates `B`,
`qubit3Embed C` rotates `D`. This is pure Kronecker mixed-product algebra
(`kronSU2SU4_mul` / `kronSU4_mul`), plus the inverse bridge `(kronSU2SU4 C 1)⁻¹ = kronSU2SU4 C⁻¹ 1`
for `C ∈ SU(2)` (via `Matrix.inv_eq_right_inv`, using `det C = 1 ⟹ C·C⁻¹ = 1`). It is the SU(8)
analog of the per-ion Clifford-conjugation step in `TrappedIonSU4EntanglerSpread`, and (composed with
the shipped single-qubit `cliffordSU2_conj`) spreads the base CNOT entanglers to all 54 entangling
tangents via `GenericSUd.flow_conj_mem`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 PROPER — (D) witness factor-wise
conjugation (per-qubit Clifford rotation lift). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8PerQubitFlow

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4

/-! ## 1. Inverse bridge: the per-qubit embeddings invert factor-wise -/

private theorem su2_val_mul_inv (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (C : Matrix (Fin 2) (Fin 2) ℂ) * (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = 1 := by
  have hdet : (C : Matrix (Fin 2) (Fin 2) ℂ).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp C.2).2
  exact Matrix.mul_nonsing_inv _ (hdet ▸ isUnit_one)

theorem qubit1Embed_val_inv (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ((qubit1Embed C : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
        Matrix (Fin 8) (Fin 8) ℂ)⁻¹ = kronSU2SU4 (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ 1 := by
  apply Matrix.inv_eq_right_inv
  show kronSU2SU4 (C : Matrix (Fin 2) (Fin 2) ℂ) 1 * kronSU2SU4 (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ 1 = 1
  rw [← kronSU2SU4_mul, su2_val_mul_inv, one_mul, kronSU2SU4_one]

theorem qubit2Embed_val_inv (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ((qubit2Embed C : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
        Matrix (Fin 8) (Fin 8) ℂ)⁻¹
      = kronSU2SU4 1 (kronSU4 (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ 1) := by
  apply Matrix.inv_eq_right_inv
  show kronSU2SU4 1 (kronSU4 (C : Matrix (Fin 2) (Fin 2) ℂ) 1) *
      kronSU2SU4 1 (kronSU4 (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ 1) = 1
  rw [← kronSU2SU4_mul, ← kronSU4_mul, su2_val_mul_inv, one_mul, kronSU4_one, kronSU2SU4_one]

theorem qubit3Embed_val_inv (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ((qubit3Embed C : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
        Matrix (Fin 8) (Fin 8) ℂ)⁻¹ = kronSU4SU2 1 (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  show kronSU4SU2 1 (C : Matrix (Fin 2) (Fin 2) ℂ) * kronSU4SU2 1 (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = 1
  rw [← kronSU4SU2_mul, su2_val_mul_inv, one_mul, kronSU4SU2_one]

/-! ## 2. Factor-wise conjugation: `qubit_iEmbed C` rotates only the qubit-i factor -/

/-- **Qubit-1 conjugation** rotates the first tensor factor. -/
theorem qubit1Embed_conj (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (A B D : Matrix (Fin 2) (Fin 2) ℂ) :
    (qubit1Embed C : Matrix (Fin 8) (Fin 8) ℂ) * kronSU8 A B D *
        ((qubit1Embed C : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ)⁻¹
      = kronSU8 ((C : Matrix (Fin 2) (Fin 2) ℂ) * A * (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹) B D := by
  rw [qubit1Embed_val_inv]
  show kronSU2SU4 (C : Matrix (Fin 2) (Fin 2) ℂ) 1 * kronSU2SU4 A (kronSU4 B D) *
      kronSU2SU4 (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ 1 = kronSU8 _ B D
  rw [← kronSU2SU4_mul, one_mul, ← kronSU2SU4_mul, mul_one]; rfl

/-- **Qubit-2 conjugation** rotates the second tensor factor. -/
theorem qubit2Embed_conj (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (A B D : Matrix (Fin 2) (Fin 2) ℂ) :
    (qubit2Embed C : Matrix (Fin 8) (Fin 8) ℂ) * kronSU8 A B D *
        ((qubit2Embed C : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ)⁻¹
      = kronSU8 A ((C : Matrix (Fin 2) (Fin 2) ℂ) * B * (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹) D := by
  rw [qubit2Embed_val_inv]
  show kronSU2SU4 1 (kronSU4 (C : Matrix (Fin 2) (Fin 2) ℂ) 1) * kronSU2SU4 A (kronSU4 B D) *
      kronSU2SU4 1 (kronSU4 (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ 1) = kronSU8 A _ D
  unfold kronSU8
  rw [← kronSU2SU4_mul, ← kronSU4_mul, one_mul, one_mul, ← kronSU2SU4_mul, ← kronSU4_mul,
    mul_one, mul_one]

/-- **Qubit-3 conjugation** rotates the third tensor factor. -/
theorem qubit3Embed_conj (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (A B D : Matrix (Fin 2) (Fin 2) ℂ) :
    (qubit3Embed C : Matrix (Fin 8) (Fin 8) ℂ) * kronSU8 A B D *
        ((qubit3Embed C : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ)⁻¹
      = kronSU8 A B ((C : Matrix (Fin 2) (Fin 2) ℂ) * D * (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹) := by
  rw [qubit3Embed_val_inv]
  show kronSU4SU2 1 (C : Matrix (Fin 2) (Fin 2) ℂ) * kronSU8 A B D *
      kronSU4SU2 1 (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = kronSU8 A B _
  rw [← kronSU2SU4_one_kronSU4_one, ← kronSU2SU4_one_kronSU4_one]
  unfold kronSU8
  rw [← kronSU2SU4_mul, ← kronSU4_mul, one_mul, one_mul, ← kronSU2SU4_mul, ← kronSU4_mul,
    mul_one, mul_one]

end SKEFTHawking.FKLW.CliffordCCZSU8
