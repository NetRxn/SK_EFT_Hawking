/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness — single-qubit Cliffords spread `X₂₁` to all 9 entanglers

`entangler_conj_flow A B` gives `exp(t·(i/2)·(A σ_y A⁻¹)⊗(B σ_x B⁻¹)) ∈ H_of_G` for any
`A, B ∈ SU(2)`. Choosing single-qubit Cliffords `C_c = exp(−iπ/4·σ_c)` that rotate
`σ_y ↦ ±σ_a` (first ion) and `σ_x ↦ ±σ_b` (second ion) yields the flow of each entangling
tensor-Pauli tangent `X_{ab} = (i/2)(σ_a ⊗ σ_b)`, `(a,b) ∈ {1,2,3}²` (the 9 entangling
directions), up to a sign absorbed by reparametrising `t ↦ ±t`.

The conjugation action of `C_c` is uniform: for an involution `J` (`J²=1`, Hermitian, traceless)
and a Pauli `M` anticommuting with `J`, `C_J·M·C_J⁻¹ = i·(M·J)` (`cliffordSU2_conj`), via
`exp_mul_of_anticommute` + `exp_iHalfPi_involution`. The four needed instances:

  * `C_{σz}·σ_y·C_{σz}⁻¹ = −σ_x`,  `C_{σx}·σ_y·C_{σx}⁻¹ = σ_z`  (first ion: σ_y ↦ σ_x, σ_z);
  * `C_{σz}·σ_x·C_{σz}⁻¹ = σ_y`,   `C_{σy}·σ_x·C_{σy}⁻¹ = −σ_z` (second ion: σ_x ↦ σ_y, σ_z).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness Clifford spread of
the entangling flow to all 9 directions. 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4PerIonConjFlow
import SKEFTHawking.FKLW.GenericExpInvolution
import SKEFTHawking.FKLW.GenericSUdExpIsuDNormBound

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix Complex SKEFTHawking.FKLW SKEFTHawking.FKLW.GenericSUd

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Pauli products (the conjugation outputs) -/

theorem sigmaY_mul_sigmaZ : SKEFTHawking.σ_y * SKEFTHawking.σ_z = Complex.I • SKEFTHawking.σ_x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem sigmaY_mul_sigmaX :
    SKEFTHawking.σ_y * SKEFTHawking.σ_x = (-Complex.I) • SKEFTHawking.σ_z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem sigmaX_mul_sigmaZ :
    SKEFTHawking.σ_x * SKEFTHawking.σ_z = (-Complex.I) • SKEFTHawking.σ_y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem sigmaX_mul_sigmaY : SKEFTHawking.σ_x * SKEFTHawking.σ_y = Complex.I • SKEFTHawking.σ_z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.mul_apply,
      Fin.sum_univ_two]

/-! ## 2. Anticommutators (the `cliffordSU2_conj` hypotheses) -/

theorem sigmaZ_anticomm_sigmaY :
    SKEFTHawking.σ_z * SKEFTHawking.σ_y = -(SKEFTHawking.σ_y * SKEFTHawking.σ_z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaX_anticomm_sigmaY :
    SKEFTHawking.σ_x * SKEFTHawking.σ_y = -(SKEFTHawking.σ_y * SKEFTHawking.σ_x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SKEFTHawking.σ_x, SKEFTHawking.σ_y, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaZ_anticomm_sigmaX :
    SKEFTHawking.σ_z * SKEFTHawking.σ_x = -(SKEFTHawking.σ_x * SKEFTHawking.σ_z) :=
  eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact SKEFTHawking.anticomm_σ_x_σ_z)

theorem sigmaY_anticomm_sigmaX :
    SKEFTHawking.σ_y * SKEFTHawking.σ_x = -(SKEFTHawking.σ_x * SKEFTHawking.σ_y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SKEFTHawking.σ_x, SKEFTHawking.σ_y, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ_y` is Hermitian. -/
theorem σ_y_isHermitian : SKEFTHawking.σ_y.IsHermitian := by
  show SKEFTHawking.σ_y.conjTranspose = SKEFTHawking.σ_y
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SKEFTHawking.σ_y, Matrix.conjTranspose]

/-! ## 3. The generic single-qubit Clifford `exp(−iπ/4·J)` and its conjugation action -/

/-- The single-qubit Clifford `exp(−iπ/4·J)` for a Hermitian-traceless involution `J`,
as an element of `SU(2)`. -/
noncomputable def cliffordSU2 (J : Matrix (Fin 2) (Fin 2) ℂ)
    (hJherm : J.IsHermitian) (hJtr : J.trace = 0) :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  expIsud 0 (((-(Real.pi / 4) : ℝ) : ℂ) • J)
    (by
      show ((((-(Real.pi / 4) : ℝ) : ℂ) • J)).conjTranspose = ((-(Real.pi / 4) : ℝ) : ℂ) • J
      rw [Matrix.conjTranspose_smul, hJherm,
        show star ((-(Real.pi / 4) : ℝ) : ℂ) = ((-(Real.pi / 4) : ℝ) : ℂ) by
          rw [Complex.star_def, Complex.conj_ofReal]])
    (by rw [Matrix.trace_smul, hJtr, smul_zero])

/-- **Generic Clifford conjugation**: `C_J · M · C_J⁻¹ = i·(M·J)` for an involution `J`
(`J²=1`) anticommuting with `M`. -/
theorem cliffordSU2_conj (J M : Matrix (Fin 2) (Fin 2) ℂ)
    (hJherm : J.IsHermitian) (hJtr : J.trace = 0)
    (hJ2 : J * J = 1) (hanti : J * M = -(M * J)) :
    (cliffordSU2 J hJherm hJtr : Matrix (Fin 2) (Fin 2) ℂ) * M *
        ((cliffordSU2 J hJherm hJtr : Matrix (Fin 2) (Fin 2) ℂ))⁻¹
      = Complex.I • (M * J) := by
  unfold cliffordSU2
  rw [expIsud_inv_val_eq_exp_neg, expIsud_val]
  simp only [smul_smul]
  set z : ℂ := Complex.I * ((-(Real.pi / 4) : ℝ) : ℂ) with hz_def
  have hz_anti : (z • J) * M = -(M * (z • J)) := by
    rw [smul_mul_assoc, hanti, smul_neg, mul_smul_comm]
  rw [exp_mul_of_anticommute _ _ hz_anti, mul_assoc,
    ← NormedSpace.exp_add_of_commute (Commute.refl (-(z • J)))]
  rw [show -(z • J) + -(z • J) = (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • J by
    rw [← neg_smul, ← add_smul]; congr 1; rw [hz_def]; push_cast; ring]
  rw [exp_iHalfPi_involution J hJ2, mul_smul_comm]

/-! ## 4. The four concrete Clifford conjugations -/

/-- First ion, `σ_y ↦ −σ_x`: `C_{σz} · σ_y · C_{σz}⁻¹ = −σ_x`. -/
theorem clifford_σz_conj_σy :
    (cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace :
        Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_y *
        ((cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace :
          Matrix (Fin 2) (Fin 2) ℂ))⁻¹
      = -SKEFTHawking.σ_x := by
  rw [cliffordSU2_conj _ _ _ _ SKEFTHawking.σ_z_sq sigmaZ_anticomm_sigmaY, sigmaY_mul_sigmaZ,
    smul_smul, Complex.I_mul_I, neg_one_smul]

/-- First ion, `σ_y ↦ σ_z`: `C_{σx} · σ_y · C_{σx}⁻¹ = σ_z`. -/
theorem clifford_σx_conj_σy :
    (cliffordSU2 SKEFTHawking.σ_x SKEFTHawking.σ_x_hermitian SKEFTHawking.σ_x_trace :
        Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_y *
        ((cliffordSU2 SKEFTHawking.σ_x SKEFTHawking.σ_x_hermitian SKEFTHawking.σ_x_trace :
          Matrix (Fin 2) (Fin 2) ℂ))⁻¹
      = SKEFTHawking.σ_z := by
  rw [cliffordSU2_conj _ _ _ _ SKEFTHawking.σ_x_sq sigmaX_anticomm_sigmaY, sigmaY_mul_sigmaX,
    smul_smul]
  rw [show Complex.I * (-Complex.I) = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_smul]

/-- Second ion, `σ_x ↦ σ_y`: `C_{σz} · σ_x · C_{σz}⁻¹ = σ_y`. -/
theorem clifford_σz_conj_σx :
    (cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace :
        Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_x *
        ((cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace :
          Matrix (Fin 2) (Fin 2) ℂ))⁻¹
      = SKEFTHawking.σ_y := by
  rw [cliffordSU2_conj _ _ _ _ SKEFTHawking.σ_z_sq sigmaZ_anticomm_sigmaX, sigmaX_mul_sigmaZ,
    smul_smul]
  rw [show Complex.I * (-Complex.I) = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_smul]

/-- Second ion, `σ_x ↦ −σ_z`: `C_{σy} · σ_x · C_{σy}⁻¹ = −σ_z`. -/
theorem clifford_σy_conj_σx :
    (cliffordSU2 SKEFTHawking.σ_y σ_y_isHermitian SKEFTHawking.σ_y_trace :
        Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_x *
        ((cliffordSU2 SKEFTHawking.σ_y σ_y_isHermitian SKEFTHawking.σ_y_trace :
          Matrix (Fin 2) (Fin 2) ℂ))⁻¹
      = -SKEFTHawking.σ_z := by
  rw [cliffordSU2_conj _ _ _ _ SKEFTHawking.σ_y_sq sigmaY_anticomm_sigmaX, sigmaX_mul_sigmaY,
    smul_smul, Complex.I_mul_I, neg_one_smul]

/-! ## 5. Conjugations in `s • pauli4 idx` form (incl. the trivial identity element) -/

/-- `1 · M · 1⁻¹ = M` for the `SU(2)` identity. -/
theorem su2_one_conj (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ((1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) * M *
        ((1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = M := by
  simp

theorem clifford_σz_conj_σy_p :
    (cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace :
        Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_y *
        ((cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace :
          Matrix (Fin 2) (Fin 2) ℂ))⁻¹
      = (-1 : ℂ) • pauli4 1 := by
  rw [clifford_σz_conj_σy, show (pauli4 1 : Matrix (Fin 2) (Fin 2) ℂ) = SKEFTHawking.σ_x from rfl,
    neg_one_smul]

theorem clifford_σx_conj_σy_p :
    (cliffordSU2 SKEFTHawking.σ_x SKEFTHawking.σ_x_hermitian SKEFTHawking.σ_x_trace :
        Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_y *
        ((cliffordSU2 SKEFTHawking.σ_x SKEFTHawking.σ_x_hermitian SKEFTHawking.σ_x_trace :
          Matrix (Fin 2) (Fin 2) ℂ))⁻¹
      = (1 : ℂ) • pauli4 3 := by
  rw [clifford_σx_conj_σy, show (pauli4 3 : Matrix (Fin 2) (Fin 2) ℂ) = SKEFTHawking.σ_z from rfl,
    one_smul]

theorem clifford_σz_conj_σx_p :
    (cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace :
        Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_x *
        ((cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace :
          Matrix (Fin 2) (Fin 2) ℂ))⁻¹
      = (1 : ℂ) • pauli4 2 := by
  rw [clifford_σz_conj_σx, show (pauli4 2 : Matrix (Fin 2) (Fin 2) ℂ) = SKEFTHawking.σ_y from rfl,
    one_smul]

theorem clifford_σy_conj_σx_p :
    (cliffordSU2 SKEFTHawking.σ_y σ_y_isHermitian SKEFTHawking.σ_y_trace :
        Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_x *
        ((cliffordSU2 SKEFTHawking.σ_y σ_y_isHermitian SKEFTHawking.σ_y_trace :
          Matrix (Fin 2) (Fin 2) ℂ))⁻¹
      = (-1 : ℂ) • pauli4 3 := by
  rw [clifford_σy_conj_σx, show (pauli4 3 : Matrix (Fin 2) (Fin 2) ℂ) = SKEFTHawking.σ_z from rfl,
    neg_one_smul]

theorem one_conj_σy_p :
    ((1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_y *
        ((1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)⁻¹
      = (1 : ℂ) • pauli4 2 := by
  rw [su2_one_conj, show (pauli4 2 : Matrix (Fin 2) (Fin 2) ℂ) = SKEFTHawking.σ_y from rfl, one_smul]

theorem one_conj_σx_p :
    ((1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_x *
        ((1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)⁻¹
      = (1 : ℂ) • pauli4 1 := by
  rw [su2_one_conj, show (pauli4 1 : Matrix (Fin 2) (Fin 2) ℂ) = SKEFTHawking.σ_x from rfl, one_smul]

/-! ## 6. Entangling-flow helper: conjugate the `X₂₁` flow to `± X_{ab}` -/

/-- **Entangling-flow helper**: per-ion conjugation of the entangling flow by single-qubit
Cliffords whose action is `A σ_y A⁻¹ = sA·σ_a`, `B σ_x B⁻¹ = sB·σ_b` produces the flow of
`(sA·sB)·X_{ab}`. -/
theorem entangling_flow_of_conj (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N)
    (A B : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (a b : Fin 4) (sA sB : ℂ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_y *
        (A : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = sA • pauli4 a)
    (hB : (B : Matrix (Fin 2) (Fin 2) ℂ) * SKEFTHawking.σ_x *
        (B : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = sB • pauli4 b)
    (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • ((sA * sB) • suFourTangentAux a b)) := by
  obtain ⟨M, hM, hMval⟩ := entangler_conj_flow N hN hN2 A B t
  refine ⟨M, hM, ?_⟩
  have hinner : (Complex.I / 2) • kronSU4 (sA • pauli4 a) (sB • pauli4 b)
      = (sA * sB) • suFourTangentAux a b := by
    unfold suFourTangentAux
    rw [kronSU4_smul_left, kronSU4_smul_right]
    simp only [smul_smul]
    congr 1
    ring
  rw [hMval, hA, hB, hinner]

/-! ## 7. The 9 entangling tangent flows `exp(t • X_{ab}) ∈ H_of_G`, `(a,b) ∈ {1,2,3}²` -/

theorem suFourTangentAux_X11_flow (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 1 1) := by
  obtain ⟨M, hM, hval⟩ := entangling_flow_of_conj N hN hN2
    (cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace) 1 1 1 (-1) 1
    clifford_σz_conj_σy_p one_conj_σx_p (-t)
  exact ⟨M, hM, by rw [hval]; congr 1; rw [smul_smul]; congr 1; push_cast; ring⟩

theorem suFourTangentAux_X12_flow (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 1 2) := by
  obtain ⟨M, hM, hval⟩ := entangling_flow_of_conj N hN hN2
    (cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace)
    (cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace) 1 2 (-1) 1
    clifford_σz_conj_σy_p clifford_σz_conj_σx_p (-t)
  exact ⟨M, hM, by rw [hval]; congr 1; rw [smul_smul]; congr 1; push_cast; ring⟩

theorem suFourTangentAux_X13_flow (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 1 3) := by
  obtain ⟨M, hM, hval⟩ := entangling_flow_of_conj N hN hN2
    (cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace)
    (cliffordSU2 SKEFTHawking.σ_y σ_y_isHermitian SKEFTHawking.σ_y_trace) 1 3 (-1) (-1)
    clifford_σz_conj_σy_p clifford_σy_conj_σx_p t
  exact ⟨M, hM, by rw [hval]; congr 1; rw [smul_smul]; congr 1; ring⟩

theorem suFourTangentAux_X21_flow_entangling (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 2 1) := by
  obtain ⟨M, hM, hval⟩ := entangling_flow_of_conj N hN hN2 1 1 2 1 1 1
    one_conj_σy_p one_conj_σx_p t
  exact ⟨M, hM, by rw [hval]; congr 1; rw [smul_smul]; congr 1; ring⟩

theorem suFourTangentAux_X22_flow (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 2 2) := by
  obtain ⟨M, hM, hval⟩ := entangling_flow_of_conj N hN hN2 1
    (cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace) 2 2 1 1
    one_conj_σy_p clifford_σz_conj_σx_p t
  exact ⟨M, hM, by rw [hval]; congr 1; rw [smul_smul]; congr 1; ring⟩

theorem suFourTangentAux_X23_flow (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 2 3) := by
  obtain ⟨M, hM, hval⟩ := entangling_flow_of_conj N hN hN2 1
    (cliffordSU2 SKEFTHawking.σ_y σ_y_isHermitian SKEFTHawking.σ_y_trace) 2 3 1 (-1)
    one_conj_σy_p clifford_σy_conj_σx_p (-t)
  exact ⟨M, hM, by rw [hval]; congr 1; rw [smul_smul]; congr 1; push_cast; ring⟩

theorem suFourTangentAux_X31_flow (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 3 1) := by
  obtain ⟨M, hM, hval⟩ := entangling_flow_of_conj N hN hN2
    (cliffordSU2 SKEFTHawking.σ_x SKEFTHawking.σ_x_hermitian SKEFTHawking.σ_x_trace) 1 3 1 1 1
    clifford_σx_conj_σy_p one_conj_σx_p t
  exact ⟨M, hM, by rw [hval]; congr 1; rw [smul_smul]; congr 1; ring⟩

theorem suFourTangentAux_X32_flow (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 3 2) := by
  obtain ⟨M, hM, hval⟩ := entangling_flow_of_conj N hN hN2
    (cliffordSU2 SKEFTHawking.σ_x SKEFTHawking.σ_x_hermitian SKEFTHawking.σ_x_trace)
    (cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace) 3 2 1 1
    clifford_σx_conj_σy_p clifford_σz_conj_σx_p t
  exact ⟨M, hM, by rw [hval]; congr 1; rw [smul_smul]; congr 1; ring⟩

theorem suFourTangentAux_X33_flow (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 3 3) := by
  obtain ⟨M, hM, hval⟩ := entangling_flow_of_conj N hN hN2
    (cliffordSU2 SKEFTHawking.σ_x SKEFTHawking.σ_x_hermitian SKEFTHawking.σ_x_trace)
    (cliffordSU2 SKEFTHawking.σ_y σ_y_isHermitian SKEFTHawking.σ_y_trace) 3 3 1 (-1)
    clifford_σx_conj_σy_p clifford_σy_conj_σx_p (-t)
  exact ⟨M, hM, by rw [hval]; congr 1; rw [smul_smul]; congr 1; push_cast; ring⟩

/-! ## 8. `hX_flow` for all 15 tensor-Pauli tangents -/

/-- **`hX_flow` for the SU(4) witness**: every tensor-Pauli tangent's 1-parameter flow line lies
in `H_of_G (trappedIonGeneratingSetSU4 N hN)` (for even `N`). The 6 per-ion tangents use the
per-ion flows (D1); the 9 entangling tangents use the Clifford-spread flows (§7). -/
theorem suFourTangent_flow (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) (j : Fin 15) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangent j) := by
  fin_cases j
  · exact suFourTangentAux_ion2_flow N hN 1 (by decide) t
  · exact suFourTangentAux_ion2_flow N hN 2 (by decide) t
  · exact suFourTangentAux_ion2_flow N hN 3 (by decide) t
  · exact suFourTangentAux_ion1_flow N hN 1 (by decide) t
  · exact suFourTangentAux_X11_flow N hN hN2 t
  · exact suFourTangentAux_X12_flow N hN hN2 t
  · exact suFourTangentAux_X13_flow N hN hN2 t
  · exact suFourTangentAux_ion1_flow N hN 2 (by decide) t
  · exact suFourTangentAux_X21_flow_entangling N hN hN2 t
  · exact suFourTangentAux_X22_flow N hN hN2 t
  · exact suFourTangentAux_X23_flow N hN hN2 t
  · exact suFourTangentAux_ion1_flow N hN 3 (by decide) t
  · exact suFourTangentAux_X31_flow N hN hN2 t
  · exact suFourTangentAux_X32_flow N hN hN2 t
  · exact suFourTangentAux_X33_flow N hN hN2 t

end SKEFTHawking.FKLW.TrappedIonSU4
