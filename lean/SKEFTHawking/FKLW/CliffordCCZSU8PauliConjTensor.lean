/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4c — 3-qubit Pauli conjugation eigenvector law

Tensors the single-qubit Pauli conjugation eigenvector law (`pauli4_conj`,
`σ_w σ_v σ_w = (−1)^⟨w,v⟩ σ_v`) up to the 3-qubit tensor-Paulis:

  `kronK8 w · kronK8 v · kronK8 w = (−1)^⟨w,v⟩ · kronK8 v`,

where the total symplectic sign `sigmaSign8 w v` is the product of the three single-qubit signs. This is
the eigenvector structure of the Pauli-group adjoint action on `𝔰𝔲(8)`: each tensor-Pauli `kronK8 v` is a
common eigenvector of every `Ad_{kronK8 w}` with eigenvalue `±1`. It drives the partial-Pauli-twirl
projection onto a single Pauli line (companion module), hence the irreducibility of the Clifford adjoint
representation.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6z provenance

Phase 6z Wave 4 increment 4c (3-qubit Pauli conjugation). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8TangentSpan
import SKEFTHawking.FKLW.CliffordCCZSU8PauliConj
import SKEFTHawking.FKLW.CliffordCCZSU8PerQubitFlow
import SKEFTHawking.FKLW.TrappedIonSU4PerIonFlow

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4

/-! ## 1. Heterogeneous triple `kronSU8` scalar law -/

/-- **Heterogeneous `kronSU8` scalar law**: `kronSU8 (s₁•A) (s₂•B) (s₃•C) = (s₁ s₂ s₃) • kronSU8 A B C`.
The hetero-scalar generalization of `kronSU8_smul_cube`. -/
theorem kronSU8_smul3 (s1 s2 s3 : ℂ) (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU8 (s1 • A) (s2 • B) (s3 • C) = (s1 * s2 * s3) • kronSU8 A B C := by
  unfold kronSU8
  simp only [kronSU4_smul_left, kronSU4_smul_right, kronSU2SU4_smul_left, kronSU2SU4_smul_right,
    smul_smul]
  congr 1
  ring

/-! ## 2. The 3-qubit total symplectic sign and the conjugation eigenvector law -/

/-- The 3-qubit total symplectic sign `(−1)^⟨w,v⟩ = ∏ᵢ (−1)^⟨wᵢ,vᵢ⟩ ∈ {±1}`. -/
noncomputable def sigmaSign8 (w v : Fin 4 × Fin 4 × Fin 4) : ℂ :=
  sigmaSign w.1 v.1 * sigmaSign w.2.1 v.2.1 * sigmaSign w.2.2 v.2.2

/-- **3-qubit Pauli conjugation eigenvector law**: `kronK8 w · kronK8 v · kronK8 w = (−1)^⟨w,v⟩ kronK8 v`.
Each tensor-Pauli `kronK8 v` is a common eigenvector of every Pauli conjugation `Ad_{kronK8 w}` with
eigenvalue `sigmaSign8 w v ∈ {±1}`. -/
theorem kronK8_conj (w v : Fin 4 × Fin 4 × Fin 4) :
    kronK8 w * kronK8 v * kronK8 w = sigmaSign8 w v • kronK8 v := by
  unfold kronK8
  rw [← kronSU8_mul, ← kronSU8_mul, pauli4_conj, pauli4_conj, pauli4_conj, kronSU8_smul3]
  rfl

end SKEFTHawking.FKLW.CliffordCCZSU8
