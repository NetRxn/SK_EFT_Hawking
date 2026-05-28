/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness — per-ion conjugation spreads `X₂₁` to all entangling tangents

The first entangling flow `exp(t·X₂₁) ∈ H_of_G` (`X₂₁ = (i/2)(σ_y ⊗ σ_x)`) is spread to every
entangling direction by conjugating with a per-ion `SU(2)×SU(2)` element `ion1Embed A · ion2Embed B`
(which lies in `H_of_G` by the per-ion containment): for all `A, B ∈ SU(2)`,

  `exp(t · (i/2)·(A σ_y A⁻¹) ⊗ (B σ_x B⁻¹)) ∈ H_of_G`.

Choosing single-qubit Cliffords `A, B` rotating `σ_y, σ_x` to `±σ_a, ±σ_b` yields each entangling
tensor-Pauli tangent `X_{ab} = (i/2)(σ_a ⊗ σ_b)`, `(a,b) ∈ {1,2,3}²`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness per-ion conjugation
spread of the entangling flow. 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4EntanglerFlow
import SKEFTHawking.FKLW.TrappedIonSU4PerIonContainment
import SKEFTHawking.FKLW.GenericSUdFlowConj

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix Complex SKEFTHawking.FKLW.GenericSUd

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- `A · A⁻¹ = 1` for `A ∈ SU(2)`. -/
theorem su2_mul_inv (A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) * (A : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = 1 := by
  have hdet : IsUnit ((A : Matrix (Fin 2) (Fin 2) ℂ)).det := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp A.property).2]; exact isUnit_one
  exact Matrix.mul_nonsing_inv _ hdet

/-- `(kronSU4 A B)⁻¹ = kronSU4 A⁻¹ B⁻¹` for `A, B ∈ SU(2)`. -/
theorem kronSU4_inv_su2 (A B : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (kronSU4 (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ))⁻¹
      = kronSU4 (A : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ (B : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← kronSU4_mul, su2_mul_inv, su2_mul_inv, kronSU4_one]

/-- The conjugate of `X₂₁` by `ion1Embed A · ion2Embed B` is `(i/2)·(A σ_y A⁻¹) ⊗ (B σ_x B⁻¹)`. -/
theorem entangler_conj_eq (A B : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (ion1Embed A * ion2Embed B : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)).val *
        suFourTangentAux 2 1 *
        ((ion1Embed A * ion2Embed B : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)).val)⁻¹
      = (Complex.I / 2) • kronSU4 ((A : Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_y *
          (A : Matrix (Fin 2) (Fin 2) ℂ)⁻¹)
          ((B : Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_x * (B : Matrix (Fin 2) (Fin 2) ℂ)⁻¹) := by
  have hval : (ion1Embed A * ion2Embed B : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)).val
      = kronSU4 (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) := by
    show kronSU4 (A : Matrix (Fin 2) (Fin 2) ℂ) 1 * kronSU4 1 (B : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [← kronSU4_mul, mul_one, one_mul]
  rw [hval, kronSU4_inv_su2]
  show kronSU4 (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) *
      ((Complex.I / 2) • kronSU4 (pauli4 2) (pauli4 1)) *
      kronSU4 (A : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ (B : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = _
  rw [show pauli4 2 = SKEFTHawking.σ_y from rfl, show pauli4 1 = SKEFTHawking.σ_x from rfl,
    mul_smul_comm, smul_mul_assoc, ← kronSU4_mul, ← kronSU4_mul]

/-- **Per-ion conjugation spreads the entangling flow**: for `A, B ∈ SU(2)` and even `N`,
`exp(t · (i/2)·(A σ_y A⁻¹) ⊗ (B σ_x B⁻¹)) ∈ H_of_G`. -/
theorem entangler_conj_flow (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N)
    (A B : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • ((Complex.I / 2) • kronSU4
          ((A : Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_y * (A : Matrix (Fin 2) (Fin 2) ℂ)⁻¹)
          ((B : Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_x *
            (B : Matrix (Fin 2) (Fin 2) ℂ)⁻¹))) := by
  obtain ⟨M, hM_mem, hM_val⟩ :=
    flow_conj_mem (H_of_G (trappedIonGeneratingSetSU4 N hN)) (ion1Embed A * ion2Embed B)
      ((H_of_G (trappedIonGeneratingSetSU4 N hN)).mul_mem
        (ion1Embed_mem_H_of_G N hN A) (ion2Embed_mem_H_of_G N hN B))
      (suFourTangentAux_X21_flow N hN hN2) t
  refine ⟨M, hM_mem, ?_⟩
  rw [hM_val, entangler_conj_eq]

end SKEFTHawking.FKLW.TrappedIonSU4
