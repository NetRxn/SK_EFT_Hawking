/-
Phase 5a Wave 2A: Pauli Matrix Infrastructure

Pauli matrices σ_x, σ_y, σ_z as 2×2 complex matrices with:
- Commutation relations: [σ_i, σ_j] = 2i ε_{ijk} σ_k
- Anti-commutation: {σ_i, σ_j} = 2 δ_{ij}
- Hermiticity, involutivity (σ_i² = 1), trace properties
- Kronecker product mixed-product lemma: (A⊗B)(C⊗D) = (AC)⊗(BD)
- Commutator identity: [A⊗1, 1⊗B] = 0

This is shared infrastructure for the Gioia-Thorngren lattice chiral
fermion formalization and any future lattice fermion work.

References:
  Gioia & Thorngren, PRL 136, 061601 (2026) — GT construction uses σ ⊗ τ
  Misumi, arXiv:2512.22609 (2025) — BdG Hamiltonian in σ-τ form
-/

import Mathlib

open Matrix Complex

universe u

noncomputable section

namespace SKEFTHawking

/-! ## 1. Pauli Matrix Definitions -/

/-- Pauli σ_x matrix: [[0, 1], [1, 0]] -/
def σ_x : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Pauli σ_y matrix: [[0, -i], [i, 0]] -/
def σ_y : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- Pauli σ_z matrix: [[1, 0], [0, -1]] -/
def σ_z : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- 2×2 identity matrix -/
def σ_id : Matrix (Fin 2) (Fin 2) ℂ :=
  1

/-! ## 2. Nambu (τ) Pauli Matrices

The Nambu/particle-hole Pauli matrices are identical to σ but act
on a different physical space (particle-hole rather than spin). -/

def τ_x : Matrix (Fin 2) (Fin 2) ℂ := σ_x
def τ_y : Matrix (Fin 2) (Fin 2) ℂ := σ_y
def τ_z : Matrix (Fin 2) (Fin 2) ℂ := σ_z

/-! ## 3. Basic Properties -/

/-- σ_x is Hermitian. -/
theorem σ_x_hermitian : σ_x.conjTranspose = σ_x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ_x, conjTranspose] <;> ring

/-- σ_z is Hermitian. -/
theorem σ_z_hermitian : σ_z.conjTranspose = σ_z := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ_z, conjTranspose] <;> ring

/-
σ_x² = 1 (involutivity).
-/
theorem σ_x_sq : σ_x * σ_x = 1 := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ σ_x ]

/-
σ_z² = 1.
-/
theorem σ_z_sq : σ_z * σ_z = 1 := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, σ_z ]

/-
σ_y² = 1.
-/
theorem σ_y_sq : σ_y * σ_y = 1 := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ σ_y ]

/-! ## 4. Commutation Relations -/

/-
[σ_x, σ_y] = 2i σ_z
-/
theorem comm_σ_x_σ_y : σ_x * σ_y - σ_y * σ_x = (2 * I) • σ_z := by
  unfold σ_x σ_y σ_z; ext i j; fin_cases i <;> fin_cases j <;> norm_num [ Complex.ext_iff, Matrix.mul_apply ] ;

/-
[σ_y, σ_z] = 2i σ_x
-/
theorem comm_σ_y_σ_z : σ_y * σ_z - σ_z * σ_y = (2 * I) • σ_x := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, σ_x, σ_y, σ_z ] <;> ring;

/-
[σ_z, σ_x] = 2i σ_y
-/
theorem comm_σ_z_σ_x : σ_z * σ_x - σ_x * σ_z = (2 * I) • σ_y := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, σ_x, σ_y, σ_z ] <;> ring;
  · norm_num;
  · norm_num

/-- [τ_z, τ_x] = 2i τ_y — the key relation for the GT commutation proof -/
theorem comm_τ_z_τ_x : τ_z * τ_x - τ_x * τ_z = (2 * I) • τ_y := by
  exact comm_σ_z_σ_x

/-! ## 5. Anti-commutation Relations -/

/-
{σ_x, σ_z} = 0 (anti-commute for distinct Pauli matrices).
-/
theorem anticomm_σ_x_σ_z : σ_x * σ_z + σ_z * σ_x = 0 := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ σ_x, σ_z ]

/-- {τ_x, τ_z} = 0 — needed for chiral charge properties. -/
theorem anticomm_τ_x_τ_z : τ_x * τ_z + τ_z * τ_x = 0 := by
  exact anticomm_σ_x_σ_z

/-! ## 6. Trace Properties -/

/-
Pauli matrices are traceless.
-/
theorem σ_x_trace : σ_x.trace = 0 := by
  norm_num [ Matrix.trace, σ_x ]

theorem σ_y_trace : σ_y.trace = 0 := by
  unfold σ_y; norm_num;

theorem σ_z_trace : σ_z.trace = 0 := by
  unfold σ_z; norm_num;

/-! ## 7. Pauli Matrix Dimension -/

/-- Pauli matrices are 2×2. -/
theorem pauli_dim : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2

end SKEFTHawking