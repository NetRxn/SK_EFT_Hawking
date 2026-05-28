/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness — the first entangling tangent flow `X₂₁`

The Mølmer-Sørensen gate at the maximally-entangling angle conjugates a per-ion tangent to a pure
entangling tangent: `Ad_{MS(π/2)}(X₃₀) = −X₂₁`. Combined with the per-ion flow of `X₃₀` (D1) and
the generic `flow_conj_mem`, this yields the continuous flow `exp(t • X₂₁) ∈ H_of_G` — the first of
the 9 entangling directions (the rest follow by per-ion Clifford conjugation).

Proof of the conjugation identity (no √2; via the anticommutation route):
`MS(π/2).val = exp(A)`, `A = msGenerator(π/2) = (−iπ/4)·(σ_x⊗σ_x)`; since `A` anticommutes with
`X₃₀`, `exp(A)·X₃₀·exp(−A) = X₃₀·exp(−2A)` (`exp_mul_of_anticommute`), `exp(−2A) =
exp(iπ/2·(σ_x⊗σ_x)) = i·(σ_x⊗σ_x)` (`exp_smul_involution`), and `X₃₀·(i·σ_x⊗σ_x) = −X₂₁`
(Pauli algebra `σ_z σ_x = i σ_y`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness entangler conjugation
(first entangling flow). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.MSGateExpForm
import SKEFTHawking.FKLW.TrappedIonSU4Tangents
import SKEFTHawking.FKLW.TrappedIonSU4PerIonFlow
import SKEFTHawking.FKLW.TrappedIonSU4MSFlowGrid
import SKEFTHawking.FKLW.GenericExpInvolution
import SKEFTHawking.FKLW.GenericSUdFlowConj

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix Complex SKEFTHawking.FKLW SKEFTHawking.FKLW.GenericSUd

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Pauli / xKronX algebra -/

/-- `σ_z · σ_x = i · σ_y`. -/
theorem sigmaZ_mul_sigmaX : SKEFTHawking.σ_z * SKEFTHawking.σ_x = Complex.I • SKEFTHawking.σ_y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- `σ_x · σ_z = −(σ_z · σ_x)` (distinct Paulis anticommute). -/
theorem sigmaX_mul_sigmaZ_anti :
    SKEFTHawking.σ_x * SKEFTHawking.σ_z = -(SKEFTHawking.σ_z * SKEFTHawking.σ_x) :=
  eq_neg_of_add_eq_zero_left SKEFTHawking.anticomm_σ_x_σ_z

/-- `xKronX` is an involution: `(σ_x ⊗ σ_x)² = 1`. -/
theorem xKronX_sq : xKronX * xKronX = 1 := by
  unfold xKronX
  rw [← kronSU4_mul, SKEFTHawking.σ_x_sq, kronSU4_one]

/-! ## 2. `exp(iπ/2 · xKronX) = i · xKronX` -/

theorem exp_iHalfPi_xKronX :
    NormedSpace.exp ((Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • xKronX) = Complex.I • xKronX := by
  rw [exp_smul_involution xKronX xKronX_sq]
  rw [show Complex.cosh (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = 0 by
        rw [mul_comm, Complex.cosh_mul_I]; simp [Complex.cos_pi_div_two]]
  rw [show Complex.sinh (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I by
        rw [mul_comm, Complex.sinh_mul_I]; simp [Complex.sin_pi_div_two]]
  rw [zero_smul, zero_add]

/-! ## 3. The key product identity `X₃₀ · (i · xKronX) = −X₂₁` -/

theorem X30_mul_I_xKronX :
    suFourTangentAux 3 0 * (Complex.I • xKronX) = -suFourTangentAux 2 1 := by
  unfold suFourTangentAux xKronX
  rw [show pauli4 3 = SKEFTHawking.σ_z from rfl, show pauli4 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    show pauli4 2 = SKEFTHawking.σ_y from rfl, show pauli4 1 = SKEFTHawking.σ_x from rfl,
    smul_mul_smul_comm, ← kronSU4_mul, one_mul, sigmaZ_mul_sigmaX, kronSU4_smul_left, smul_smul,
    ← neg_smul]
  congr 1
  rw [mul_assoc, Complex.I_mul_I]; ring

/-! ## 4. The conjugation identity `MS(π/2) · X₃₀ · MS(π/2)⁻¹ = −X₂₁` -/

/-- `kronSU4 (−A) B = −(kronSU4 A B)`. -/
theorem kronSU4_neg_left (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4 (-A) B = -(kronSU4 A B) := by
  rw [← neg_one_smul ℂ A, kronSU4_smul_left, neg_one_smul]

/-- `xKronX` anticommutes with `X₃₀`. -/
theorem xKronX_anticomm_X30 :
    xKronX * suFourTangentAux 3 0 = -(suFourTangentAux 3 0 * xKronX) := by
  unfold suFourTangentAux xKronX
  rw [show pauli4 3 = SKEFTHawking.σ_z from rfl,
    show pauli4 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    mul_smul_comm, smul_mul_assoc, ← kronSU4_mul, ← kronSU4_mul, mul_one, one_mul,
    sigmaX_mul_sigmaZ_anti, kronSU4_neg_left, smul_neg]

/-- `msGenerator(π/2)` anticommutes with `X₃₀`. -/
theorem msGen_anticomm_X30 :
    msGenerator (Real.pi / 2) * suFourTangentAux 3 0
      = -(suFourTangentAux 3 0 * msGenerator (Real.pi / 2)) := by
  unfold msGenerator
  rw [smul_mul_assoc, xKronX_anticomm_X30, mul_smul_comm, smul_neg]

/-- `(MSGate_SU4 (π/2)).val⁻¹ = exp(−msGenerator(π/2))`. -/
theorem MS_halfPi_inv :
    ((MSGate_SU4 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℂ))⁻¹
      = NormedSpace.exp (-msGenerator (Real.pi / 2)) := by
  have hmul : (MSGate_SU4 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℂ) *
      NormedSpace.exp (-msGenerator (Real.pi / 2)) = 1 := by
    show NormedSpace.exp (msGenerator (Real.pi / 2)) *
      NormedSpace.exp (-msGenerator (Real.pi / 2)) = 1
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl _)),
      add_neg_cancel, NormedSpace.exp_zero]
  exact Matrix.inv_eq_right_inv hmul

/-- **The entangler conjugation identity**: `MS(π/2) · X₃₀ · MS(π/2)⁻¹ = −X₂₁`. -/
theorem MS_conj_X30 :
    (MSGate_SU4 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℂ) * suFourTangentAux 3 0 *
        ((MSGate_SU4 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℂ))⁻¹
      = -suFourTangentAux 2 1 := by
  rw [MS_halfPi_inv]
  show NormedSpace.exp (msGenerator (Real.pi / 2)) * suFourTangentAux 3 0 *
      NormedSpace.exp (-msGenerator (Real.pi / 2)) = _
  rw [SKEFTHawking.FKLW.exp_mul_of_anticommute _ _ msGen_anticomm_X30, mul_assoc,
    ← NormedSpace.exp_add_of_commute (Commute.refl (-msGenerator (Real.pi / 2)))]
  rw [show -msGenerator (Real.pi / 2) + -msGenerator (Real.pi / 2)
        = (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • xKronX by
      unfold msGenerator; rw [← neg_add, ← add_smul, ← neg_smul]; congr 1; push_cast; ring]
  rw [exp_iHalfPi_xKronX, X30_mul_I_xKronX]

end SKEFTHawking.FKLW.TrappedIonSU4
