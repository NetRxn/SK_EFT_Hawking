/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′ — CNOT gates on 3 qubits as SU(8) permutation matrices

The cross-qubit Clifford generators for the universal Clifford+CCZ+T SU(8) alphabet. In the
computational basis index `4·q1 + 2·q2 + q3`, `CNOT_{ij}` (control qubit i, target qubit j) is a
permutation matrix of an **even** permutation (two disjoint transpositions), hence its determinant
is `+1` — it sits in `SU(8)` with **no global-phase correction needed**:

  * `CNOT₁₂` swaps basis states 4↔6, 5↔7  (flip q2 when q1 = 1)
  * `CNOT₁₃` swaps 4↔5, 6↔7              (flip q3 when q1 = 1)
  * `CNOT₂₃` swaps 2↔3, 6↔7              (flip q3 when q2 = 1)

Together with the per-qubit Hadamards/phase gates, `{CNOT₁₂, CNOT₁₃, CNOT₂₃}` generate the full
3-qubit Clifford group, whose conjugation action factors through `Sp(6, 𝔽₂)` acting transitively on
the 63 non-identity tripartite Paulis (Aaronson-Gottesman 2004 group structure; universality via
Boykin-Mor-Pulver-Roychowdhury-Vatan 1999 + Brylinski-Brylinski 2001) — the mechanism that spreads
the per-qubit `𝔰𝔲(2)` flow lines to all 63 entangling tangents of the `ClosureDenseWitness`.

Membership uses the Mathlib permutation-matrix API: `Equiv.Perm.permMatrix`,
`Matrix.det_permutation` (det = sign), `Matrix.conjTranspose_permMatrix`, `Matrix.permMatrix_mul`,
`Matrix.permMatrix_one`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.1 PROPER — universal-alphabet CNOT
substrate. 2026-05-28.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

/-! ## 1. Generic helper: an even permutation matrix is in `SU(8)` -/

/-- **An even-permutation matrix over `ℂ` lies in `specialUnitaryGroup (Fin 8) ℂ`.**
Unitary via `conjTranspose_permMatrix` + `permMatrix_mul` + `permMatrix_one`; det = sign = 1. -/
theorem permMatrix_fin8_mem_specialUnitaryGroup (σ : Equiv.Perm (Fin 8))
    (hσ : Equiv.Perm.sign σ = 1) :
    Equiv.Perm.permMatrix ℂ σ ∈ Matrix.specialUnitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
      Matrix.permMatrix_one]
  · rw [Matrix.det_permutation, hσ]; simp

/-! ## 2. The three CNOT permutations + sign computations -/

/-- `CNOT₁₂` permutation: swaps 4↔6 and 5↔7. -/
def σ_cnot_12 : Equiv.Perm (Fin 8) := Equiv.swap 4 6 * Equiv.swap 5 7

/-- `CNOT₁₃` permutation: swaps 4↔5 and 6↔7. -/
def σ_cnot_13 : Equiv.Perm (Fin 8) := Equiv.swap 4 5 * Equiv.swap 6 7

/-- `CNOT₂₃` permutation: swaps 2↔3 and 6↔7. -/
def σ_cnot_23 : Equiv.Perm (Fin 8) := Equiv.swap 2 3 * Equiv.swap 6 7

theorem sign_σ_cnot_12 : Equiv.Perm.sign σ_cnot_12 = 1 := by
  unfold σ_cnot_12
  rw [map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]; decide

theorem sign_σ_cnot_13 : Equiv.Perm.sign σ_cnot_13 = 1 := by
  unfold σ_cnot_13
  rw [map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]; decide

theorem sign_σ_cnot_23 : Equiv.Perm.sign σ_cnot_23 = 1 := by
  unfold σ_cnot_23
  rw [map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]; decide

/-! ## 3. CNOT matrices + SU(8) membership + bundled subtype elements -/

/-- `CNOT₁₂` as an 8×8 matrix. -/
noncomputable def CNOT_12_mat : Matrix (Fin 8) (Fin 8) ℂ := Equiv.Perm.permMatrix ℂ σ_cnot_12
/-- `CNOT₁₃` as an 8×8 matrix. -/
noncomputable def CNOT_13_mat : Matrix (Fin 8) (Fin 8) ℂ := Equiv.Perm.permMatrix ℂ σ_cnot_13
/-- `CNOT₂₃` as an 8×8 matrix. -/
noncomputable def CNOT_23_mat : Matrix (Fin 8) (Fin 8) ℂ := Equiv.Perm.permMatrix ℂ σ_cnot_23

theorem CNOT_12_mem : CNOT_12_mat ∈ Matrix.specialUnitaryGroup (Fin 8) ℂ :=
  permMatrix_fin8_mem_specialUnitaryGroup σ_cnot_12 sign_σ_cnot_12
theorem CNOT_13_mem : CNOT_13_mat ∈ Matrix.specialUnitaryGroup (Fin 8) ℂ :=
  permMatrix_fin8_mem_specialUnitaryGroup σ_cnot_13 sign_σ_cnot_13
theorem CNOT_23_mem : CNOT_23_mat ∈ Matrix.specialUnitaryGroup (Fin 8) ℂ :=
  permMatrix_fin8_mem_specialUnitaryGroup σ_cnot_23 sign_σ_cnot_23

/-- `CNOT₁₂` as an `SU(8)` subtype element. -/
noncomputable def CNOT_12_SU8 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) := ⟨CNOT_12_mat, CNOT_12_mem⟩
/-- `CNOT₁₃` as an `SU(8)` subtype element. -/
noncomputable def CNOT_13_SU8 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) := ⟨CNOT_13_mat, CNOT_13_mem⟩
/-- `CNOT₂₃` as an `SU(8)` subtype element. -/
noncomputable def CNOT_23_SU8 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) := ⟨CNOT_23_mat, CNOT_23_mem⟩

end SKEFTHawking.FKLW.CliffordCCZSU8
