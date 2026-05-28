/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness — the 6 per-ion tangent flow lines

The `hX_flow` field of the trapped-ion SU(4) `ClosureDenseWitness` requires, for each tangent
`X i` and each `t : ℝ`, an element of `H_of_G (trappedIonGeneratingSetSU4 N hN)` whose underlying
matrix is `exp(t • X i)`. This module discharges the **6 per-ion tangents**
`X_{a0} = (i/2)·(σ_a ⊗ I)` (ion 1) and `X_{0b} = (i/2)·(I ⊗ σ_b)` (ion 2), `a, b ∈ {1,2,3}`.

The proof composes already-shipped substrate, with no new analytic content:

  * `exp(t • X_{a0}) = kronSU4 (exp(t·(i/2)σ_a)) 1 = (ion1Embed A).val` where
    `A = exp(t·(i/2)σ_a) ∈ SU(2)`, via `kronSU4_exp_right_one` + `kronSU4_smul_left`;
  * `ion1Embed A ∈ H_of_G` by the per-ion containment `ion1Embed_mem_H_of_G`
    (Clifford+T density transfer);

and symmetrically for ion 2 via `kronSU4_exp_left_one` + `ion2Embed_mem_H_of_G`. The SU(2)
element `A` is produced by the unconditional `expIsud 0` (exp of `I·F` for Hermitian-traceless
`F = (t/2)·σ_a`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness per-ion flow lines
(D1). DR blueprint §3.1 L_flow_a-1 (alphabet flows in closure). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4Tangents
import SKEFTHawking.FKLW.TrappedIonSU4PerIonContainment
import SKEFTHawking.FKLW.TrappedIonSU4ExpCommute
import SKEFTHawking.FKLW.GenericSUdExpIsuDUnconditional

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix Complex SKEFTHawking.FKLW.GenericSUd

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. `kronSU4` is ℂ-linear in each argument -/

/-- **`kronSU4 (c • A) B = c • kronSU4 A B`**. -/
theorem kronSU4_smul_left (c : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4 (c • A) B = c • kronSU4 A B := by
  unfold kronSU4
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, mul_assoc]

/-- **`kronSU4 A (c • B) = c • kronSU4 A B`**. -/
theorem kronSU4_smul_right (c : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4 A (c • B) = c • kronSU4 A B := by
  unfold kronSU4
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, mul_left_comm]

/-! ## 2. `(t/2)·σ_a` is Hermitian-traceless (the SU(2) exponent) -/

private theorem half_smul_pauli4_isHermitian (a : Fin 4) (t : ℝ) :
    (((t / 2 : ℝ) : ℂ) • pauli4 a).IsHermitian := by
  show (((t / 2 : ℝ) : ℂ) • pauli4 a)ᴴ = ((t / 2 : ℝ) : ℂ) • pauli4 a
  rw [Matrix.conjTranspose_smul, pauli4_hermitian,
    show star ((t / 2 : ℝ) : ℂ) = ((t / 2 : ℝ) : ℂ) by
      rw [Complex.star_def, Complex.conj_ofReal]]

private theorem half_smul_pauli4_trace_zero (a : Fin 4) (ha : a ≠ 0) (t : ℝ) :
    (((t / 2 : ℝ) : ℂ) • pauli4 a).trace = 0 := by
  rw [Matrix.trace_smul, pauli4_trace]
  simp [ha]

/-! ## 3. The 6 per-ion tangent flow lines -/

/-- **Ion-1 per-ion flow**: for `a ≠ 0`, the 1-parameter subgroup `exp(t • X_{a0})` lies in
`H_of_G (trappedIonGeneratingSetSU4 N hN)`. -/
theorem suFourTangentAux_ion1_flow (N : ℕ) (hN : 0 < N) (a : Fin 4) (ha : a ≠ 0) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux a 0) := by
  set F : Matrix (Fin 2) (Fin 2) ℂ := ((t / 2 : ℝ) : ℂ) • pauli4 a with hF_def
  set A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    expIsud 0 F (half_smul_pauli4_isHermitian a t) (half_smul_pauli4_trace_zero a ha t) with hA_def
  refine ⟨ion1Embed A, ion1Embed_mem_H_of_G N hN A, ?_⟩
  show kronSU4 (A : Matrix (Fin 2) (Fin 2) ℂ) 1 =
    NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux a 0)
  rw [hA_def, expIsud_val, kronSU4_exp_right_one]
  congr 1
  rw [hF_def, smul_smul, kronSU4_smul_left]
  unfold suFourTangentAux
  rw [smul_smul]
  congr 1
  push_cast; ring

/-- **Ion-2 per-ion flow**: for `b ≠ 0`, the 1-parameter subgroup `exp(t • X_{0b})` lies in
`H_of_G (trappedIonGeneratingSetSU4 N hN)`. -/
theorem suFourTangentAux_ion2_flow (N : ℕ) (hN : 0 < N) (b : Fin 4) (hb : b ≠ 0) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 0 b) := by
  set F : Matrix (Fin 2) (Fin 2) ℂ := ((t / 2 : ℝ) : ℂ) • pauli4 b with hF_def
  set A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    expIsud 0 F (half_smul_pauli4_isHermitian b t) (half_smul_pauli4_trace_zero b hb t) with hA_def
  refine ⟨ion2Embed A, ion2Embed_mem_H_of_G N hN A, ?_⟩
  show kronSU4 1 (A : Matrix (Fin 2) (Fin 2) ℂ) =
    NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 0 b)
  rw [hA_def, expIsud_val, kronSU4_exp_left_one]
  congr 1
  rw [hF_def, smul_smul, kronSU4_smul_right]
  unfold suFourTangentAux
  rw [smul_smul]
  congr 1
  push_cast; ring

end SKEFTHawking.FKLW.TrappedIonSU4
