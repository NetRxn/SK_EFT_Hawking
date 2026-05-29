/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4f.2b — the six H/S three-qubit generator conjugation lifts

The single-qubit Clifford conjugation values `H_SU.val · σ_a · (H_SU.val)⁻¹ = hSign a · σ_{hLabel a}` and
`S_SU.val · σ_a · (S_SU.val)⁻¹ = sSign a · σ_{sLabel a}` (`CliffordCCZSU8GenConjValues`) tensor up to the
three-qubit `SU(8)` generators via the factor-conjugation lemmas `qubit{1,2,3}Embed_conj`
(`CliffordCCZSU8FactorConj`). This module ships the six resulting **generator tableau lifts**

  `(qubit_qEmbed C).val · kronK8 v · (qubit_qEmbed C).val⁻¹ = sign(v_q) · kronK8 (onQubit φ_C (q-1) v)`

for `C ∈ {H_SU, S_SU}` and qubit `q ∈ {1,2,3}`, where `φ_H = hLabel`, `φ_S = sLabel`, and `onQubit`,
`hLabel`, `sLabel`, `hSign`, `sSign` match the label-transitivity combinatorics (`CliffordCCZSU8LabelTransitivity`).

These six lifts plus the three CNOT lifts (`CliffordCCZSU8CNOTConj`) are exactly the matrix realizations of
the nine label generators `cliffordLabelGens`; together with `clifford_label_transitive` they drive the
W-membership transport (every tensor-Pauli line `ℝ·kronK8 v` reachable from a single one under Clifford
conjugation), which feeds the Clifford-adjoint irreducibility on `𝔰𝔲(8)`.

The single-factor scalar pull-outs `kronSU8_smul_{left,mid,right}` (`kronSU8 (c•A) B D = c • kronSU8 A B D`,
etc.) are the small algebraic substrate; each lift is then `qubit_qEmbed_conj` + the single-qubit value +
the matching scalar pull-out, definitionally aligned with `onQubit φ (q-1) v`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4f.2b (H/S three-qubit generator lifts). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8GenConjValues
import SKEFTHawking.FKLW.CliffordCCZSU8FactorConj
import SKEFTHawking.FKLW.CliffordCCZSU8TangentSpan

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4 SKEFTHawking.FKLW.GenericSU2

/-! ## 1. Single-factor scalar pull-outs from the `SU(8)` Kronecker product

`kronSU8 A B D = (A ⊗ B) ⊗ D` is `ℂ`-bilinear in each factor; pulling a scalar out of any one factor
yields the global scalar. These are the algebraic substrate of the generator lifts (the single-qubit
conjugation value carries a `±1` scalar on the rotated factor, which must surface as a global `±1`). -/

/-- Pull a scalar out of the **first** Kronecker factor: `kronSU8 (c•A) B D = c • kronSU8 A B D`. -/
theorem kronSU8_smul_left (c : ℂ) (A B D : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU8 (c • A) B D = c • kronSU8 A B D := by
  unfold kronSU8; rw [kronSU2SU4_smul_left]

/-- Pull a scalar out of the **middle** Kronecker factor: `kronSU8 A (c•B) D = c • kronSU8 A B D`. -/
theorem kronSU8_smul_mid (c : ℂ) (A B D : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU8 A (c • B) D = c • kronSU8 A B D := by
  unfold kronSU8; rw [kronSU4_smul_left, kronSU2SU4_smul_right]

/-- Pull a scalar out of the **last** Kronecker factor: `kronSU8 A B (c•D) = c • kronSU8 A B D`. -/
theorem kronSU8_smul_right (c : ℂ) (A B D : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU8 A B (c • D) = c • kronSU8 A B D := by
  unfold kronSU8; rw [kronSU4_smul_right, kronSU2SU4_smul_right]

/-! ## 2. The three Hadamard generator lifts -/

/-- **Hadamard on qubit 1** (tableau lift): `H₁ · kronK8 v · H₁⁻¹ = hSign v.1 · kronK8 (onQubit hLabel 0 v)`. -/
theorem hsu_q1_kronK8_conj (v : PauliLabel) :
    (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronK8 v *
      ((qubit1Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹
      = hSign v.1 • kronK8 (onQubit hLabel 0 v) := by
  obtain ⟨v1, v2, v3⟩ := v
  show (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronSU8 (pauli4 v1) (pauli4 v2) (pauli4 v3) * _
      = hSign v1 • kronSU8 (pauli4 (hLabel v1)) (pauli4 v2) (pauli4 v3)
  rw [qubit1Embed_conj, H_SU_conj_pauli4, kronSU8_smul_left]

/-- **Hadamard on qubit 2** (tableau lift): `H₂ · kronK8 v · H₂⁻¹ = hSign v.2.1 · kronK8 (onQubit hLabel 1 v)`. -/
theorem hsu_q2_kronK8_conj (v : PauliLabel) :
    (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronK8 v *
      ((qubit2Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹
      = hSign v.2.1 • kronK8 (onQubit hLabel 1 v) := by
  obtain ⟨v1, v2, v3⟩ := v
  show (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronSU8 (pauli4 v1) (pauli4 v2) (pauli4 v3) * _
      = hSign v2 • kronSU8 (pauli4 v1) (pauli4 (hLabel v2)) (pauli4 v3)
  rw [qubit2Embed_conj, H_SU_conj_pauli4, kronSU8_smul_mid]

/-- **Hadamard on qubit 3** (tableau lift): `H₃ · kronK8 v · H₃⁻¹ = hSign v.2.2 · kronK8 (onQubit hLabel 2 v)`. -/
theorem hsu_q3_kronK8_conj (v : PauliLabel) :
    (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronK8 v *
      ((qubit3Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹
      = hSign v.2.2 • kronK8 (onQubit hLabel 2 v) := by
  obtain ⟨v1, v2, v3⟩ := v
  show (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronSU8 (pauli4 v1) (pauli4 v2) (pauli4 v3) * _
      = hSign v3 • kronSU8 (pauli4 v1) (pauli4 v2) (pauli4 (hLabel v3))
  rw [qubit3Embed_conj, H_SU_conj_pauli4, kronSU8_smul_right]

/-! ## 3. The three S-gate generator lifts -/

/-- **S-gate on qubit 1** (tableau lift): `S₁ · kronK8 v · S₁⁻¹ = sSign v.1 · kronK8 (onQubit sLabel 0 v)`. -/
theorem ssu_q1_kronK8_conj (v : PauliLabel) :
    (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronK8 v *
      ((qubit1Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹
      = sSign v.1 • kronK8 (onQubit sLabel 0 v) := by
  obtain ⟨v1, v2, v3⟩ := v
  show (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronSU8 (pauli4 v1) (pauli4 v2) (pauli4 v3) * _
      = sSign v1 • kronSU8 (pauli4 (sLabel v1)) (pauli4 v2) (pauli4 v3)
  rw [qubit1Embed_conj, S_SU_conj_pauli4, kronSU8_smul_left]

/-- **S-gate on qubit 2** (tableau lift): `S₂ · kronK8 v · S₂⁻¹ = sSign v.2.1 · kronK8 (onQubit sLabel 1 v)`. -/
theorem ssu_q2_kronK8_conj (v : PauliLabel) :
    (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronK8 v *
      ((qubit2Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹
      = sSign v.2.1 • kronK8 (onQubit sLabel 1 v) := by
  obtain ⟨v1, v2, v3⟩ := v
  show (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronSU8 (pauli4 v1) (pauli4 v2) (pauli4 v3) * _
      = sSign v2 • kronSU8 (pauli4 v1) (pauli4 (sLabel v2)) (pauli4 v3)
  rw [qubit2Embed_conj, S_SU_conj_pauli4, kronSU8_smul_mid]

/-- **S-gate on qubit 3** (tableau lift): `S₃ · kronK8 v · S₃⁻¹ = sSign v.2.2 · kronK8 (onQubit sLabel 2 v)`. -/
theorem ssu_q3_kronK8_conj (v : PauliLabel) :
    (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronK8 v *
      ((qubit3Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹
      = sSign v.2.2 • kronK8 (onQubit sLabel 2 v) := by
  obtain ⟨v1, v2, v3⟩ := v
  show (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * kronSU8 (pauli4 v1) (pauli4 v2) (pauli4 v3) * _
      = sSign v3 • kronSU8 (pauli4 v1) (pauli4 v2) (pauli4 (sLabel v3))
  rw [qubit3Embed_conj, S_SU_conj_pauli4, kronSU8_smul_right]

end SKEFTHawking.FKLW.CliffordCCZSU8
