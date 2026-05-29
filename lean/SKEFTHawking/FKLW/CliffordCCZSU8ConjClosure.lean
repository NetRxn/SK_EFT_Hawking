/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4g.1 — conjugation-closure infrastructure (Ad is a homomorphism)

The Clifford-adjoint irreducibility (4g) extracts a tensor-Pauli line from a nonzero invariant `Y` via the
Pauli twirl (`pauli_twirl`), which needs the invariant submodule `W` to be closed under conjugation by
each tensor-Pauli `kronK8 w`. Tensor-Paulis are *forward words* in the Clifford generators (`σ_z = i·S²`,
`σ_x = -i·H·S²·H`, `σ_y = i·H·S²·H·S²`, up to a unit phase), so the conjugation closure transfers from
the generators because **`Ad` is a homomorphism** and conjugation is **phase-blind**. This module ships
that infrastructure:

  * `conj_closed_mul` — closure under `Ad_{g₁}` and `Ad_{g₂}` gives closure under `Ad_{g₁·g₂}`
    (`(g₁g₂)·Y·(g₁g₂)⁻¹ = g₁·(g₂·Y·g₂⁻¹)·g₁⁻¹` via `Matrix.mul_inv_rev`). Generic in the index type.
  * `conj_involution_smul` — for an involution `K` (`K·K = 1`) and a unit phase `c ≠ 0`,
    `(c•K)·Y·(c•K)⁻¹ = K·Y·K` (the phase cancels; `(c•K)⁻¹ = c⁻¹•K` by `inv_eq_right_inv`). Generic.
  * `pauli4_mul_self` / `kronK8_sq` — every single-qubit Pauli and every tensor-Pauli `kronK8 w` is an
    involution, so `conj_involution_smul` applies with `K = kronK8 w`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4g.1 (conjugation-closure infrastructure). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8TangentSpan

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4

/-! ## 1. Generic conjugation-closure composition and phase-invariance -/

/-- **`Ad` is a homomorphism (closure form).** If an ℝ-submodule `W` of matrices is closed under
conjugation by `g₁` and by `g₂`, it is closed under conjugation by `g₁·g₂`. -/
theorem conj_closed_mul {n : Type*} [Fintype n] [DecidableEq n]
    (W : Submodule ℝ (Matrix n n ℂ)) (g1 g2 : Matrix n n ℂ)
    (h1 : ∀ Y ∈ W, g1 * Y * g1⁻¹ ∈ W) (h2 : ∀ Y ∈ W, g2 * Y * g2⁻¹ ∈ W) :
    ∀ Y ∈ W, (g1 * g2) * Y * (g1 * g2)⁻¹ ∈ W := by
  intro Y hY
  have : (g1 * g2) * Y * (g1 * g2)⁻¹ = g1 * (g2 * Y * g2⁻¹) * g1⁻¹ := by
    rw [Matrix.mul_inv_rev]; noncomm_ring
  rw [this]; exact h1 _ (h2 _ hY)

/-- **Conjugation is phase-blind for involutions.** For an involution `K` (`K·K = 1`) and a unit
phase `c ≠ 0`, conjugation by `c•K` equals conjugation by `K`: `(c•K)·Y·(c•K)⁻¹ = K·Y·K`. -/
theorem conj_involution_smul {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℂ) (hc : c ≠ 0) (K Y : Matrix n n ℂ) (hK : K * K = 1) :
    (c • K) * Y * (c • K)⁻¹ = K * Y * K := by
  have hinv : (c • K)⁻¹ = c⁻¹ • K := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, hK]
  rw [hinv, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc,
    one_smul, mul_assoc]

/-! ## 2. Single-qubit Paulis and tensor-Paulis are involutions -/

/-- Every single-qubit Pauli is an involution: `σ_a · σ_a = 1`. -/
theorem pauli4_mul_self (a : Fin 4) : pauli4 a * pauli4 a = 1 := by
  fin_cases a <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply])

/-- The 3-fold identity Kronecker is the identity: `kronSU8 1 1 1 = 1`. -/
theorem kronSU8_one_one_one : kronSU8 (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := by
  show kronSU2SU4 1 (kronSU4 1 1) = 1
  rw [kronSU4_one]
  have h1 : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 :=
    Matrix.one_kronecker_one
  unfold kronSU2SU4
  rw [h1]
  exact Matrix.submatrix_one_equiv finProdFinEquiv.symm

/-- **Every tensor-Pauli `kronK8 w` is an involution**: `kronK8 w · kronK8 w = 1`
(tensor of single-qubit-Pauli involutions). -/
theorem kronK8_sq (w : Fin 4 × Fin 4 × Fin 4) : kronK8 w * kronK8 w = 1 := by
  obtain ⟨a, b, c⟩ := w
  show kronSU8 (pauli4 a) (pauli4 b) (pauli4 c) * kronSU8 (pauli4 a) (pauli4 b) (pauli4 c) = 1
  rw [← kronSU8_mul, pauli4_mul_self, pauli4_mul_self, pauli4_mul_self, kronSU8_one_one_one]

end SKEFTHawking.FKLW.CliffordCCZSU8
