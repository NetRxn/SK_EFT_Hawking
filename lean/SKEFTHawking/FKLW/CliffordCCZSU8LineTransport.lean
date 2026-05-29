/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4f.3a — tensor-Pauli line transport under the Clifford generators

The Clifford-adjoint irreducibility on `𝔰𝔲(8)` runs through a **transport** step: a Clifford-conjugation-
invariant ℝ-submodule `W` that contains *one* tensor-Pauli line `ℝ·(i·kronK8 v)` must contain *all* of
them (then `W = ⊤` by `suEightTangent_spans`). This module ships the atomic transport substrate.

The nine generator tableau lifts (`hsu_q{1,2,3}_kronK8_conj`, `ssu_q{1,2,3}_kronK8_conj` in
`CliffordCCZSU8GenLift`; `cnot{12,13,23}_kronK8_conj` in `CliffordCCZSU8CNOTConj`) each say
`g · kronK8 v · g⁻¹ = sign(v) • kronK8 (φ_g v)` with `sign(v) ∈ {±1}`. The generic helper

  `line_transport`: `W` conjugation-closed under `g` + `g·kronK8 v·g⁻¹ = sign•kronK8 w` (`sign = ±1`)
    ⟹ `i·kronK8 v ∈ W → i·kronK8 w ∈ W`,

pushes a line through one generator (the `±1` sign is absorbed by the ℝ-submodule's negation closure).
The nine corollaries instantiate it at the nine generators, giving: the set `{v | i·kronK8 v ∈ W}` is
closed under each of the nine Clifford label maps `cliffordLabelGens` (`onQubit hLabel/sLabel q`,
`cnotLabel`). Combined with the Clifford label transitivity (`clifford_label_transitive`,
`CliffordCCZSU8LabelTransitivity`) this yields the full "one line ⟹ all lines" transport (companion
increment).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4f.3a (tensor-Pauli line transport substrate). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8GenLift
import SKEFTHawking.FKLW.CliffordCCZSU8CNOTConj
import SKEFTHawking.FKLW.CliffordCCZSU8EntanglerSpread

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4 SKEFTHawking.FKLW.GenericSU2

/-! ## 1. The conjugation signs are `±1` -/

/-- The Hadamard-conjugation sign is `±1`. -/
theorem hSign_pm (a : Fin 4) : hSign a = 1 ∨ hSign a = -1 := by
  fin_cases a <;> simp [hSign]

/-- The S-gate-conjugation sign is `±1`. -/
theorem sSign_pm (a : Fin 4) : sSign a = 1 ∨ sSign a = -1 := by
  fin_cases a <;> simp [sSign]

/-- The CNOT-conjugation sign is `±1`. -/
theorem cnotSign_pm (v1 v2 : Fin 4) : cnotSign v1 v2 = 1 ∨ cnotSign v1 v2 = -1 := by
  unfold cnotSign; split_ifs <;> simp

/-! ## 2. The generic single-generator line transport -/

/-- **Generic single-generator line transport**. If an ℝ-submodule `W` of complex `8×8` matrices is
closed under conjugation by `g`, and `g · kronK8 v · g⁻¹ = sign • kronK8 w` with `sign = ±1`, then
`i·kronK8 v ∈ W` implies `i·kronK8 w ∈ W`.

Proof: conjugate `i·kronK8 v ∈ W`; pull `i` through (`mul_smul`/`smul_mul`) and rewrite the conjugation
to `(i·sign)•kronK8 w`. For `sign = 1` this is `i·kronK8 w`; for `sign = -1` it is `-(i·kronK8 w)`, and
`W`'s negation closure recovers `i·kronK8 w`. -/
theorem line_transport
    (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (g : Matrix (Fin 8) (Fin 8) ℂ)
    (hclosed : ∀ Y ∈ W, g * Y * g⁻¹ ∈ W)
    (sign : ℂ) (hsign : sign = 1 ∨ sign = -1)
    (v w : PauliLabel)
    (hconj : g * kronK8 v * g⁻¹ = sign • kronK8 w)
    (hv : Complex.I • kronK8 v ∈ W) :
    Complex.I • kronK8 w ∈ W := by
  have hZ : g * (Complex.I • kronK8 v) * g⁻¹ ∈ W := hclosed _ hv
  rw [Matrix.mul_smul, Matrix.smul_mul, hconj, smul_smul] at hZ
  rcases hsign with h1 | hm1
  · rwa [h1, mul_one] at hZ
  · rw [hm1, mul_neg_one, neg_smul] at hZ
    rw [← neg_neg (Complex.I • kronK8 w)]; exact W.neg_mem hZ

/-! ## 3. The nine generator corollaries

Each instantiates `line_transport` at one Clifford label generator, with `hclosed` the conjugation
closure under that generator's `SU(8)` matrix and the conclusion the line moved by the matching label
map. Together they certify that `{v | i·kronK8 v ∈ W}` is closed under `cliffordLabelGens`. -/

section Corollaries

variable (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ)) (v : PauliLabel)
  (hv : Complex.I • kronK8 v ∈ W)

include hv

/-- Line transport under `H` on qubit 1. -/
theorem line_transport_H_q1
    (hclosed : ∀ Y ∈ W, (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
        ((qubit1Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W) :
    Complex.I • kronK8 (onQubit hLabel 0 v) ∈ W :=
  line_transport W _ hclosed (hSign v.1) (hSign_pm v.1) v _ (hsu_q1_kronK8_conj v) hv

/-- Line transport under `H` on qubit 2. -/
theorem line_transport_H_q2
    (hclosed : ∀ Y ∈ W, (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
        ((qubit2Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W) :
    Complex.I • kronK8 (onQubit hLabel 1 v) ∈ W :=
  line_transport W _ hclosed (hSign v.2.1) (hSign_pm v.2.1) v _ (hsu_q2_kronK8_conj v) hv

/-- Line transport under `H` on qubit 3. -/
theorem line_transport_H_q3
    (hclosed : ∀ Y ∈ W, (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
        ((qubit3Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W) :
    Complex.I • kronK8 (onQubit hLabel 2 v) ∈ W :=
  line_transport W _ hclosed (hSign v.2.2) (hSign_pm v.2.2) v _ (hsu_q3_kronK8_conj v) hv

/-- Line transport under `S` on qubit 1. -/
theorem line_transport_S_q1
    (hclosed : ∀ Y ∈ W, (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
        ((qubit1Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W) :
    Complex.I • kronK8 (onQubit sLabel 0 v) ∈ W :=
  line_transport W _ hclosed (sSign v.1) (sSign_pm v.1) v _ (ssu_q1_kronK8_conj v) hv

/-- Line transport under `S` on qubit 2. -/
theorem line_transport_S_q2
    (hclosed : ∀ Y ∈ W, (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
        ((qubit2Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W) :
    Complex.I • kronK8 (onQubit sLabel 1 v) ∈ W :=
  line_transport W _ hclosed (sSign v.2.1) (sSign_pm v.2.1) v _ (ssu_q2_kronK8_conj v) hv

/-- Line transport under `S` on qubit 3. -/
theorem line_transport_S_q3
    (hclosed : ∀ Y ∈ W, (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
        ((qubit3Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W) :
    Complex.I • kronK8 (onQubit sLabel 2 v) ∈ W :=
  line_transport W _ hclosed (sSign v.2.2) (sSign_pm v.2.2) v _ (ssu_q3_kronK8_conj v) hv

/-- Line transport under `CNOT` on pair `(1,2)`. -/
theorem line_transport_cnot_12
    (hclosed : ∀ Y ∈ W, CNOT_12_mat * Y * CNOT_12_mat⁻¹ ∈ W) :
    Complex.I • kronK8 (cnotLabel 0 1 v) ∈ W := by
  refine line_transport W CNOT_12_mat hclosed (cnotSign v.1 v.2.1) (cnotSign_pm _ _) v _ ?_ hv
  rw [show CNOT_12_mat = Equiv.Perm.permMatrix ℂ σ_cnot_12 from rfl, permMatrix_fin8_inv,
    cnot12_kronK8_conj]

/-- Line transport under `CNOT` on pair `(1,3)`. -/
theorem line_transport_cnot_13
    (hclosed : ∀ Y ∈ W, CNOT_13_mat * Y * CNOT_13_mat⁻¹ ∈ W) :
    Complex.I • kronK8 (cnotLabel 0 2 v) ∈ W := by
  refine line_transport W CNOT_13_mat hclosed (cnotSign v.1 v.2.2) (cnotSign_pm _ _) v _ ?_ hv
  rw [show CNOT_13_mat = Equiv.Perm.permMatrix ℂ σ_cnot_13 from rfl, permMatrix_fin8_inv,
    cnot13_kronK8_conj]

/-- Line transport under `CNOT` on pair `(2,3)`. -/
theorem line_transport_cnot_23
    (hclosed : ∀ Y ∈ W, CNOT_23_mat * Y * CNOT_23_mat⁻¹ ∈ W) :
    Complex.I • kronK8 (cnotLabel 1 2 v) ∈ W := by
  refine line_transport W CNOT_23_mat hclosed (cnotSign v.2.1 v.2.2) (cnotSign_pm _ _) v _ ?_ hv
  rw [show CNOT_23_mat = Equiv.Perm.permMatrix ℂ σ_cnot_23 from rfl, permMatrix_fin8_inv,
    cnot23_kronK8_conj]

end Corollaries

end SKEFTHawking.FKLW.CliffordCCZSU8
