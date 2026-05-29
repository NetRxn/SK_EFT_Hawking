/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4d — Pauli character orthogonality

The orthogonality of the symplectic characters `χ_v(w) = (−1)^⟨w,v⟩` driving the partial Pauli twirl:

  per qubit: `∑_{w : Fin 4} (−1)^⟨w,a⟩ (−1)^⟨w,b⟩ = 4 · δ_{a,b}`
  3 qubits:  `∑_{w : (Fin 4)³} (−1)^⟨w,a⟩ (−1)^⟨w,b⟩ = 64 · δ_{a,b}`

(`64 = 4³` = the size of the single-qubit and 3-qubit Pauli label sets). This is the discrete Fourier /
character-orthogonality fact: the 64 sign-characters `χ_v` are orthogonal, so summing `χ_{v₀}(w)` against
the conjugation action `Ad_{P_w}` projects onto the single Pauli line `ℝ·P_{v₀}` (the partial Pauli twirl,
companion module).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6z provenance

Phase 6z Wave 4 increment 4d (Pauli character orthogonality). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8PauliConjTensor

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

/-- Factorization of a sum over `(Fin 4)³` of a coordinatewise product into a product of three sums. -/
private theorem sum_prod4_cube (F G H : Fin 4 → ℂ) :
    (∑ w : Fin 4 × Fin 4 × Fin 4, F w.1 * G w.2.1 * H w.2.2)
      = (∑ x, F x) * (∑ y, G y) * (∑ z, H z) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Finset.sum_mul_sum]

/-- **Single-qubit character orthogonality**: `∑_w (−1)^⟨w,a⟩ (−1)^⟨w,b⟩ = 4 · δ_{a,b}`. -/
theorem sigmaSign_orth (a b : Fin 4) :
    ∑ w : Fin 4, sigmaSign w a * sigmaSign w b = if a = b then 4 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [sigmaSign, symForm4, pauliX4, pauliZ4, Fin.sum_univ_four,
      show ((1 : ZMod 2) + 1) = 0 from rfl] <;> norm_num

/-- **3-qubit character orthogonality**: `∑_w (−1)^⟨w,a⟩ (−1)^⟨w,b⟩ = 64 · δ_{a,b}`. The orthogonality
of the 64 sign-characters of the Pauli conjugation action — the discrete-Fourier identity behind the
partial Pauli twirl. -/
theorem sigmaSign8_orth (a b : Fin 4 × Fin 4 × Fin 4) :
    ∑ w : Fin 4 × Fin 4 × Fin 4, sigmaSign8 w a * sigmaSign8 w b = if a = b then 64 else 0 := by
  have hreshape : ∀ w : Fin 4 × Fin 4 × Fin 4, sigmaSign8 w a * sigmaSign8 w b
      = sigmaSign w.1 a.1 * sigmaSign w.1 b.1 * (sigmaSign w.2.1 a.2.1 * sigmaSign w.2.1 b.2.1)
        * (sigmaSign w.2.2 a.2.2 * sigmaSign w.2.2 b.2.2) := fun w => by
    simp only [sigmaSign8]; ring
  rw [Finset.sum_congr rfl (fun w _ => hreshape w),
      sum_prod4_cube (fun x => sigmaSign x a.1 * sigmaSign x b.1)
        (fun y => sigmaSign y a.2.1 * sigmaSign y b.2.1)
        (fun z => sigmaSign z a.2.2 * sigmaSign z b.2.2),
      sigmaSign_orth, sigmaSign_orth, sigmaSign_orth]
  rcases a with ⟨a1, a2, a3⟩; rcases b with ⟨b1, b2, b3⟩
  by_cases h1 : a1 = b1 <;> by_cases h2 : a2 = b2 <;> by_cases h3 : a3 = b3 <;>
    simp_all [Prod.ext_iff]
  all_goals norm_num

end SKEFTHawking.FKLW.CliffordCCZSU8
