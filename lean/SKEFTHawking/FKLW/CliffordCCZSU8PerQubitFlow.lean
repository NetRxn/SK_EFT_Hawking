/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2 (D) witness — the 9 per-qubit tangent flow lines

The `hX_flow` field of the SU(8) `ClosureDenseWitness` needs, for each tangent `X i` and each
`t : ℝ`, an element of `H_of_G cliffordCCZGeneratingSetSU8` whose underlying matrix is `exp(t • X i)`.
This module discharges the **9 single-qubit tangents** `X_{a00}, X_{0b0}, X_{00c}` (`a,b,c ∈ {1,2,3}`),
mirroring the SU(4) `TrappedIonSU4PerIonFlow`:

  * `exp(t • X_{a00}) = (qubit1Embed A).val`, `A = exp(t·(i/2)σ_a) ∈ SU(2)`, via `kronSU2SU4_exp_q1`;
  * `exp(t • X_{0b0}) = (qubit2Embed A).val` via `kronSU2SU4_kronSU4_exp_q2`;
  * `exp(t • X_{00c}) = (qubit3Embed A).val` via `kronSU4SU2_exp_q3` + the reindex-associativity
    `kronSU2SU4 1 (kronSU4 1 C) = kronSU4SU2 1 C` (the kronSU8 nesting puts qubit 3 in the inner-right
    slot; the alphabet's qubit-3 gate uses `kronSU4SU2` — they are the same `I⊗I⊗C` matrix).

Each `qubit_iEmbed A ∈ H_of_G` by the per-qubit containment (Clifford+T density transfer). The SU(2)
element `A` is `expIsud 0 ((t/2)·σ_a)` (exp of `I·F` for Hermitian-traceless `F`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 PROPER — (D) witness per-qubit flow lines.
DR blueprint §3.1 L_flow_a-1 (alphabet flows in closure). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8Tangents
import SKEFTHawking.FKLW.CliffordCCZSU8ExpCommute
import SKEFTHawking.FKLW.CliffordCCZSU8PerQubitContainment
import SKEFTHawking.FKLW.TrappedIonSU4PerIonFlow
import SKEFTHawking.FKLW.GenericSUdExpIsuDUnconditional

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix Complex SKEFTHawking.FKLW.GenericSUd SKEFTHawking.FKLW.TrappedIonSU4

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. ℂ-linearity of the SU(8) Kronecker embeddings -/

theorem kronSU2SU4_smul_left (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 4) (Fin 4) ℂ) :
    kronSU2SU4 (c • A) B = c • kronSU2SU4 A B := by
  unfold kronSU2SU4
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, mul_assoc]

theorem kronSU2SU4_smul_right (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 4) (Fin 4) ℂ) :
    kronSU2SU4 A (c • B) = c • kronSU2SU4 A B := by
  unfold kronSU2SU4
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, mul_left_comm]

theorem kronSU4SU2_smul_right (c : ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4SU2 A (c • B) = c • kronSU4SU2 A B := by
  unfold kronSU4SU2
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, mul_left_comm]

/-! ## 2. Reindex-associativity `I₂ ⊗ (I₂ ⊗ C) = I₄ ⊗ C` (qubit-3 nesting bridge) -/

/-- **`kronSU2SU4 1 (kronSU4 1 C) = kronSU4SU2 1 C`**: the two `I⊗I⊗C` reindexings agree.
The kronSU8 tangent nesting puts qubit 3 as `kronSU2SU4 1 (kronSU4 1 ·)`; the alphabet's qubit-3
gate uses `kronSU4SU2 1 ·`. They are the same 8×8 matrix. -/
theorem kronSU2SU4_one_kronSU4_one (C : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU2SU4 (1 : Matrix (Fin 2) (Fin 2) ℂ)
        (kronSU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) C) = kronSU4SU2 1 C := by
  unfold kronSU2SU4 kronSU4SU2 kronSU4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, finProdFinEquiv, Equiv.coe_fn_symm_mk,
      mul_ite, mul_zero, ite_mul, zero_mul, one_mul] <;> rfl

/-! ## 3. `(t/2)·σ_a` is Hermitian-traceless (the SU(2) exponent) -/

private theorem half_smul_pauli4_isHermitian' (a : Fin 4) (t : ℝ) :
    (((t / 2 : ℝ) : ℂ) • pauli4 a).IsHermitian := by
  show (((t / 2 : ℝ) : ℂ) • pauli4 a)ᴴ = ((t / 2 : ℝ) : ℂ) • pauli4 a
  rw [Matrix.conjTranspose_smul, pauli4_hermitian,
    show star ((t / 2 : ℝ) : ℂ) = ((t / 2 : ℝ) : ℂ) by
      rw [Complex.star_def, Complex.conj_ofReal]]

private theorem half_smul_pauli4_trace_zero' (a : Fin 4) (ha : a ≠ 0) (t : ℝ) :
    (((t / 2 : ℝ) : ℂ) • pauli4 a).trace = 0 := by
  rw [Matrix.trace_smul, pauli4_trace]; simp [ha]

/-! ## 4. The 9 per-qubit tangent flow lines -/

/-- **Qubit-1 flow**: `exp(t • X_{a00}) ∈ H_of_G` for `a ≠ 0`. -/
theorem suEightTangentAux_qubit1_flow (a : Fin 4) (ha : a ≠ 0) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux a 0 0) := by
  set F : Matrix (Fin 2) (Fin 2) ℂ := ((t / 2 : ℝ) : ℂ) • pauli4 a with hF_def
  set A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    expIsud 0 F (half_smul_pauli4_isHermitian' a t) (half_smul_pauli4_trace_zero' a ha t) with hA_def
  refine ⟨qubit1Embed A, qubit1Embed_mem_H_of_G A, ?_⟩
  show kronSU2SU4 (A : Matrix (Fin 2) (Fin 2) ℂ) 1 =
    NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux a 0 0)
  rw [hA_def, expIsud_val, kronSU2SU4_exp_q1]
  congr 1
  rw [hF_def, smul_smul, kronSU2SU4_smul_left]
  unfold suEightTangentAux kronSU8
  rw [show pauli4 0 = 1 from rfl, kronSU4_one, smul_smul]
  congr 1
  push_cast; ring

/-- **Qubit-2 flow**: `exp(t • X_{0b0}) ∈ H_of_G` for `b ≠ 0`. -/
theorem suEightTangentAux_qubit2_flow (b : Fin 4) (hb : b ≠ 0) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux 0 b 0) := by
  set F : Matrix (Fin 2) (Fin 2) ℂ := ((t / 2 : ℝ) : ℂ) • pauli4 b with hF_def
  set A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    expIsud 0 F (half_smul_pauli4_isHermitian' b t) (half_smul_pauli4_trace_zero' b hb t) with hA_def
  refine ⟨qubit2Embed A, qubit2Embed_mem_H_of_G A, ?_⟩
  show kronSU2SU4 1 (kronSU4 (A : Matrix (Fin 2) (Fin 2) ℂ) 1) =
    NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux 0 b 0)
  rw [hA_def, expIsud_val, kronSU2SU4_kronSU4_exp_q2]
  congr 1
  rw [hF_def, smul_smul, kronSU4_smul_left, kronSU2SU4_smul_right]
  unfold suEightTangentAux kronSU8
  rw [show pauli4 0 = 1 from rfl, smul_smul]
  congr 1
  push_cast; ring

/-- **Qubit-3 flow**: `exp(t • X_{00c}) ∈ H_of_G` for `c ≠ 0`. -/
theorem suEightTangentAux_qubit3_flow (c : Fin 4) (hc : c ≠ 0) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux 0 0 c) := by
  set F : Matrix (Fin 2) (Fin 2) ℂ := ((t / 2 : ℝ) : ℂ) • pauli4 c with hF_def
  set A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    expIsud 0 F (half_smul_pauli4_isHermitian' c t) (half_smul_pauli4_trace_zero' c hc t) with hA_def
  refine ⟨qubit3Embed A, qubit3Embed_mem_H_of_G A, ?_⟩
  show kronSU4SU2 1 (A : Matrix (Fin 2) (Fin 2) ℂ) =
    NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux 0 0 c)
  rw [hA_def, expIsud_val, kronSU4SU2_exp_q3]
  congr 1
  rw [hF_def, smul_smul, kronSU4SU2_smul_right]
  unfold suEightTangentAux kronSU8
  rw [show pauli4 0 = 1 from rfl, ← kronSU2SU4_one_kronSU4_one, smul_smul]
  congr 1
  push_cast; ring

end SKEFTHawking.FKLW.CliffordCCZSU8
