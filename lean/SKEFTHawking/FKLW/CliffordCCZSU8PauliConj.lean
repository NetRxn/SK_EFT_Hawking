/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4b — single-qubit Pauli conjugation eigenvector relation

The first concrete brick of the Clifford-adjoint irreducibility (Wave 4): the single-qubit Pauli
conjugation eigenvector law

  `σ_w · σ_v · σ_w = (−1)^⟨w,v⟩ · σ_v`

where `⟨·,·⟩` is the symplectic form on `F₂²` (the `(x,z)` symplectic encoding of the four Paulis:
`I=(0,0)`, `X=(1,0)`, `Y=(1,1)`, `Z=(0,1)`). Concretely `σ_w σ_v σ_w = ±σ_v`: `+` when `σ_w, σ_v`
commute (symplectic form `0`), `−` when they anticommute (symplectic form `1`).

This single-qubit law tensors up (companion module) to `kronK8 w · kronK8 v · kronK8 w =
(−1)^⟨w,v⟩ · kronK8 v` — the eigenvector structure that drives the partial-Pauli-twirl projection onto a
single Pauli line, hence the irreducibility of the Clifford adjoint representation on `𝔰𝔲(8)`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6z provenance

Phase 6z Wave 4 increment 4b (single-qubit Pauli conjugation). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4Tangents

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4

/-! ## 1. The symplectic `(x, z)` encoding of the four Paulis -/

/-- The `x`-bit of each Pauli in the `F₂²` symplectic encoding: `I↦0, X↦1, Y↦1, Z↦0`. -/
def pauliX4 : Fin 4 → ZMod 2 := ![0, 1, 1, 0]

/-- The `z`-bit of each Pauli in the `F₂²` symplectic encoding: `I↦0, X↦0, Y↦1, Z↦1`. -/
def pauliZ4 : Fin 4 → ZMod 2 := ![0, 0, 1, 1]

/-- The symplectic form `⟨a, b⟩ = x_a z_b + z_a x_b ∈ ZMod 2`; `0` iff `σ_a, σ_b` commute. -/
def symForm4 (a b : Fin 4) : ZMod 2 := pauliX4 a * pauliZ4 b + pauliZ4 a * pauliX4 b

/-- The commutation sign `(−1)^⟨a,b⟩ ∈ {±1} ⊆ ℂ`: `+1` when `σ_a, σ_b` commute, `−1` when they
anticommute. -/
noncomputable def sigmaSign (a b : Fin 4) : ℂ := if symForm4 a b = 0 then 1 else -1

/-- `sigmaSign` is symmetric. -/
theorem sigmaSign_symm (a b : Fin 4) : sigmaSign a b = sigmaSign b a := by
  unfold sigmaSign symForm4
  fin_cases a <;> fin_cases b <;> simp [pauliX4, pauliZ4]

/-! ## 2. The single-qubit conjugation eigenvector law -/

/-- **Single-qubit Pauli conjugation eigenvector law**: `σ_w · σ_v · σ_w = (−1)^⟨w,v⟩ · σ_v`. Proved by
the 16-case table (`fin_cases` on `w, v`), reducing the symplectic sign via `(1+1 : ZMod 2) = 0` and
computing the 2×2 matrix product entrywise. -/
theorem pauli4_conj (w v : Fin 4) :
    pauli4 w * pauli4 v * pauli4 w = sigmaSign w v • pauli4 v := by
  fin_cases w <;> fin_cases v <;>
    · simp only [sigmaSign, symForm4, pauliX4, pauliZ4]
      norm_num [show ((1 : ZMod 2) + 1) = 0 from rfl]
      all_goals
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.mul_apply,
            Fin.sum_univ_two]

end SKEFTHawking.FKLW.CliffordCCZSU8
