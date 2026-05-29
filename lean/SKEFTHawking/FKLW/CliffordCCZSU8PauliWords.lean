/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4g.2 — single-qubit Paulis as Clifford words ⟹ per-qubit conjugation closure

The Pauli twirl in the irreducibility step (4g) needs the invariant submodule `W` closed under conjugation
by each tensor-Pauli `kronK8 w`. Tensor-Paulis factor over the three qubits, so it suffices to close `W`
under conjugation by each single-qubit Pauli on each qubit. Each single-qubit Pauli is a **forward word**
in the literal Clifford generators `H_SU, S_SU` (no inverses), up to a unit phase:

  `S² = -i·σ_z`,  `H·S²·H = i·σ_x`,  `H·S²·H·S² = -i·σ_y`,  `I = σ_I`,

so by the conjugation-closure homomorphism (`conj_closed_mul`) plus phase-blindness for involutions
(`conj_involution_smul`, `kronK8_sq`), conjugation closure under `H_SU, S_SU` on a qubit transfers to
conjugation closure under every single-qubit Pauli on that qubit. This module ships:

  * the three 2×2 word values (`S_val_sq`, `H_S2_H`, `H_S2_H_S2`) and `px_pz` (`σ_x·σ_z = -i·σ_y`);
  * the three qubit-embedding value normal forms (`qubit{1,2,3}Embed_val`, lifting the embeds to `kronSU8`);
  * the three **per-qubit Pauli conjugation closures** `conjP{1,2,3}`: for every Pauli index `a`,
    `W` closed under conj by `H`/`S` on qubit `q` ⟹ `W` closed under conj by `σ_a` on qubit `q`
    (`kronK8 (a,0,0)` / `(0,a,0)` / `(0,0,a)`).

The full `kronK8 w` closure (compose the three per-qubit closures) is the companion increment.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4g.2 (Paulis as Clifford words; per-qubit conj closure). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8ConjClosure
import SKEFTHawking.FKLW.CliffordCCZSU8GenLift
import SKEFTHawking.FKLW.CliffordCCZSU8GenConjValues
import SKEFTHawking.FKLW.CliffordCCZSU8QubitEmbed

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4 SKEFTHawking.FKLW.GenericSU2

/-! ## 1. The 2×2 single-qubit Pauli word values -/

/-- `σ_x · σ_z = -i·σ_y` (`Y = i·X·Z`). -/
theorem px_pz : pauli4 1 * pauli4 3 = (-Complex.I) • pauli4 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply]

/-- `S² = -i·σ_z`. -/
theorem S_val_sq : S_SU.val * S_SU.val = (-Complex.I) • pauli4 3 := by
  show S_SU_mat * S_SU_mat = _
  rw [show S_SU_mat = !![Complex.exp (-(Complex.I * (Real.pi : ℂ) / 4)), 0;
        0, Complex.exp (Complex.I * (Real.pi : ℂ) / 4)] from rfl]
  set α := Complex.exp (-(Complex.I * (Real.pi : ℂ) / 4)) with hα
  set β := Complex.exp (Complex.I * (Real.pi : ℂ) / 4) with hβ
  have hαα : α ^ 2 = -Complex.I := by
    rw [sq, hα, ← Complex.exp_add, show -(Complex.I * (Real.pi : ℂ) / 4) + -(Complex.I * (Real.pi : ℂ) / 4)
      = -(Complex.I * (Real.pi : ℂ) / 2) by ring, expNIpiHalf]
  have hββ : β ^ 2 = Complex.I := by
    rw [sq, hβ, ← Complex.exp_add, show Complex.I * (Real.pi : ℂ) / 4 + Complex.I * (Real.pi : ℂ) / 4
      = Complex.I * (Real.pi : ℂ) / 2 by ring, expIpiHalf]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli4, SKEFTHawking.σ_z, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    (try rw [← sq]) <;> first | rw [hαα] | rw [hββ]

/-- `H·S²·H = i·σ_x` (Hadamard maps `σ_z ↦ σ_x`). -/
theorem H_S2_H : H_SU.val * (S_SU.val * S_SU.val) * H_SU.val = Complex.I • pauli4 1 := by
  rw [S_val_sq, H_SU_val_eq_smul_litHadamard]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [litHadamard_conj_pauli4, show hSign 3 = 1 from rfl, show hLabel 3 = 1 from rfl, smul_smul]
  congr 1
  simp [Complex.I_mul_I]

/-- `H·S²·H·S² = -i·σ_y`. -/
theorem H_S2_H_S2 :
    H_SU.val * (S_SU.val * S_SU.val) * H_SU.val * (S_SU.val * S_SU.val) = (-Complex.I) • pauli4 2 := by
  rw [H_S2_H, S_val_sq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, px_pz, smul_smul]
  congr 1
  simp [Complex.I_mul_I]

/-! ## 2. The three per-qubit Pauli conjugation closures

(The qubit-embedding value normal forms `qubit{1,2,3}Embed_val` are reused from
`CliffordCCZSU8SeedNotFiniteOrder`.) -/

/-- **Per-qubit-1 Pauli conjugation closure**: `W` closed under conj by `H`/`S` on qubit 1 ⟹ `W` closed
under conj by `σ_a` on qubit 1 (`kronK8 (a,0,0)`), for every Pauli index `a`. -/
theorem conjP1 (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (hH1 : ∀ Y ∈ W, (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS1 : ∀ Y ∈ W, (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (a : Fin 4) :
    ∀ Y ∈ W, kronK8 (a, 0, 0) * Y * kronK8 (a, 0, 0) ∈ W := by
  have hSS : ∀ Y ∈ W, (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) *
      (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) *
       (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ))⁻¹ ∈ W := conj_closed_mul W _ _ hS1 hS1
  fin_cases a
  · intro Y hY
    show kronSU8 (pauli4 0) (pauli4 0) (pauli4 0) * Y * kronSU8 (pauli4 0) (pauli4 0) (pauli4 0) ∈ W
    rw [show (pauli4 0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 from rfl, kronSU8_one_one_one, one_mul, mul_one]
    exact hY
  · intro Y hY
    have hval : ((qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) *
        ((qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ)))
        * (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) = Complex.I • kronK8 (1, 0, 0) := by
      simp only [qubit1Embed_val, ← kronSU8_mul, one_mul]; rw [H_S2_H, kronSU8_smul_left]; rfl
    have cHSS := conj_closed_mul W _ _ hH1 hSS
    have cHSSH := conj_closed_mul W _ _ cHSS hH1
    have h := cHSSH Y hY
    rw [hval, conj_involution_smul Complex.I (by simp) (kronK8 (1, 0, 0)) Y (kronK8_sq _)] at h
    exact h
  · intro Y hY
    have hval : (((qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) *
        ((qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ)))
        * (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ)) *
        ((qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ))
        = (-Complex.I) • kronK8 (2, 0, 0) := by
      simp only [qubit1Embed_val, ← kronSU8_mul, one_mul]; rw [H_S2_H_S2, kronSU8_smul_left]; rfl
    have cHSS := conj_closed_mul W _ _ hH1 hSS
    have cHSSH := conj_closed_mul W _ _ cHSS hH1
    have cY := conj_closed_mul W _ _ cHSSH hSS
    have h := cY Y hY
    rw [hval, conj_involution_smul (-Complex.I) (by simp) (kronK8 (2, 0, 0)) Y (kronK8_sq _)] at h
    exact h
  · intro Y hY
    have hval : (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) *
        (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) = (-Complex.I) • kronK8 (3, 0, 0) := by
      simp only [qubit1Embed_val, ← kronSU8_mul, one_mul]; rw [S_val_sq, kronSU8_smul_left]; rfl
    have h := hSS Y hY
    rw [hval, conj_involution_smul (-Complex.I) (by simp) (kronK8 (3, 0, 0)) Y (kronK8_sq _)] at h
    exact h

/-- **Per-qubit-2 Pauli conjugation closure**: `W` closed under conj by `H`/`S` on qubit 2 ⟹ `W` closed
under conj by `σ_a` on qubit 2 (`kronK8 (0,a,0)`), for every Pauli index `a`. -/
theorem conjP2 (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (hH2 : ∀ Y ∈ W, (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS2 : ∀ Y ∈ W, (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (a : Fin 4) :
    ∀ Y ∈ W, kronK8 (0, a, 0) * Y * kronK8 (0, a, 0) ∈ W := by
  have hSS : ∀ Y ∈ W, (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) *
      (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) *
       (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ))⁻¹ ∈ W := conj_closed_mul W _ _ hS2 hS2
  fin_cases a
  · intro Y hY
    show kronSU8 (pauli4 0) (pauli4 0) (pauli4 0) * Y * kronSU8 (pauli4 0) (pauli4 0) (pauli4 0) ∈ W
    rw [show (pauli4 0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 from rfl, kronSU8_one_one_one, one_mul, mul_one]
    exact hY
  · intro Y hY
    have hval : ((qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) *
        ((qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ)))
        * (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) = Complex.I • kronK8 (0, 1, 0) := by
      simp only [qubit2Embed_val, ← kronSU8_mul, one_mul]; rw [H_S2_H, kronSU8_smul_mid]; rfl
    have cHSS := conj_closed_mul W _ _ hH2 hSS
    have cHSSH := conj_closed_mul W _ _ cHSS hH2
    have h := cHSSH Y hY
    rw [hval, conj_involution_smul Complex.I (by simp) (kronK8 (0, 1, 0)) Y (kronK8_sq _)] at h
    exact h
  · intro Y hY
    have hval : (((qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) *
        ((qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ)))
        * (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ)) *
        ((qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ))
        = (-Complex.I) • kronK8 (0, 2, 0) := by
      simp only [qubit2Embed_val, ← kronSU8_mul, one_mul]; rw [H_S2_H_S2, kronSU8_smul_mid]; rfl
    have cHSS := conj_closed_mul W _ _ hH2 hSS
    have cHSSH := conj_closed_mul W _ _ cHSS hH2
    have cY := conj_closed_mul W _ _ cHSSH hSS
    have h := cY Y hY
    rw [hval, conj_involution_smul (-Complex.I) (by simp) (kronK8 (0, 2, 0)) Y (kronK8_sq _)] at h
    exact h
  · intro Y hY
    have hval : (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) *
        (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) = (-Complex.I) • kronK8 (0, 3, 0) := by
      simp only [qubit2Embed_val, ← kronSU8_mul, one_mul]; rw [S_val_sq, kronSU8_smul_mid]; rfl
    have h := hSS Y hY
    rw [hval, conj_involution_smul (-Complex.I) (by simp) (kronK8 (0, 3, 0)) Y (kronK8_sq _)] at h
    exact h

/-- **Per-qubit-3 Pauli conjugation closure**: `W` closed under conj by `H`/`S` on qubit 3 ⟹ `W` closed
under conj by `σ_a` on qubit 3 (`kronK8 (0,0,a)`), for every Pauli index `a`. -/
theorem conjP3 (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (hH3 : ∀ Y ∈ W, (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS3 : ∀ Y ∈ W, (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (a : Fin 4) :
    ∀ Y ∈ W, kronK8 (0, 0, a) * Y * kronK8 (0, 0, a) ∈ W := by
  have hSS : ∀ Y ∈ W, (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) *
      (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) *
       (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ))⁻¹ ∈ W := conj_closed_mul W _ _ hS3 hS3
  fin_cases a
  · intro Y hY
    show kronSU8 (pauli4 0) (pauli4 0) (pauli4 0) * Y * kronSU8 (pauli4 0) (pauli4 0) (pauli4 0) ∈ W
    rw [show (pauli4 0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 from rfl, kronSU8_one_one_one, one_mul, mul_one]
    exact hY
  · intro Y hY
    have hval : ((qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) *
        ((qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ)))
        * (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) = Complex.I • kronK8 (0, 0, 1) := by
      simp only [qubit3Embed_val, ← kronSU8_mul, one_mul]; rw [H_S2_H, kronSU8_smul_right]; rfl
    have cHSS := conj_closed_mul W _ _ hH3 hSS
    have cHSSH := conj_closed_mul W _ _ cHSS hH3
    have h := cHSSH Y hY
    rw [hval, conj_involution_smul Complex.I (by simp) (kronK8 (0, 0, 1)) Y (kronK8_sq _)] at h
    exact h
  · intro Y hY
    have hval : (((qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) *
        ((qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ)))
        * (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ)) *
        ((qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ))
        = (-Complex.I) • kronK8 (0, 0, 2) := by
      simp only [qubit3Embed_val, ← kronSU8_mul, one_mul]; rw [H_S2_H_S2, kronSU8_smul_right]; rfl
    have cHSS := conj_closed_mul W _ _ hH3 hSS
    have cHSSH := conj_closed_mul W _ _ cHSS hH3
    have cY := conj_closed_mul W _ _ cHSSH hSS
    have h := cY Y hY
    rw [hval, conj_involution_smul (-Complex.I) (by simp) (kronK8 (0, 0, 2)) Y (kronK8_sq _)] at h
    exact h
  · intro Y hY
    have hval : (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) *
        (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) = (-Complex.I) • kronK8 (0, 0, 3) := by
      simp only [qubit3Embed_val, ← kronSU8_mul, one_mul]; rw [S_val_sq, kronSU8_smul_right]; rfl
    have h := hSS Y hY
    rw [hval, conj_involution_smul (-Complex.I) (by simp) (kronK8 (0, 0, 3)) Y (kronK8_sq _)] at h
    exact h

end SKEFTHawking.FKLW.CliffordCCZSU8
