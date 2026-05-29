/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4g.3 — full tensor-Pauli conjugation closure

Composes the three per-qubit Pauli conjugation closures (`conjP1`/`conjP2`/`conjP3`,
`CliffordCCZSU8PauliWords`) into the **full tensor-Pauli closure**: a submodule `W` closed under
conjugation by the six per-qubit `H`/`S` generator matrices is closed under conjugation by *every*
tensor-Pauli `kronK8 w`.

A tensor-Pauli factors over the three qubits, `kronK8 (a,b,c) = K_a · K_b · K_c` (forward,
`kronK8_fwd`) `= K_c · K_b · K_a` (backward, `kronK8_bwd`), with `K_a = kronK8 (a,0,0)` etc. — the
single-qubit Paulis on disjoint qubits commute. Hence the iterated single-qubit conjugation
`K_a·(K_b·(K_c·Y·K_c)·K_b)·K_a` equals the tensor-Pauli conjugation `kronK8 w · Y · kronK8 w` by pure
reassociation, and the closure follows by applying `conjP3`, then `conjP2`, then `conjP1`.

This is exactly the "`W` closed under conj by `kronK8 w`" hypothesis the Pauli twirl (`pauli_twirl`)
consumes in the irreducibility step (4g).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4g.3 (full tensor-Pauli conjugation closure). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8PauliWords

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4 SKEFTHawking.FKLW.GenericSU2

/-! ## 1. The single-qubit-Pauli factorization of a tensor-Pauli -/

/-- **Forward factorization**: `kronK8 (a,b,c) = K_a · K_b · K_c` (per-qubit Paulis, qubit-1 first). -/
theorem kronK8_fwd (a b c : Fin 4) :
    kronK8 (a, b, c) = kronK8 (a, 0, 0) * kronK8 (0, b, 0) * kronK8 (0, 0, c) := by
  show kronSU8 (pauli4 a) (pauli4 b) (pauli4 c)
    = kronSU8 (pauli4 a) (pauli4 0) (pauli4 0) * kronSU8 (pauli4 0) (pauli4 b) (pauli4 0)
      * kronSU8 (pauli4 0) (pauli4 0) (pauli4 c)
  rw [← kronSU8_mul, ← kronSU8_mul]
  simp [show (pauli4 0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 from rfl]

/-- **Backward factorization**: `kronK8 (a,b,c) = K_c · K_b · K_a` (per-qubit Paulis, qubit-3 first).
The disjoint-qubit Paulis commute, so this equals the forward factorization. -/
theorem kronK8_bwd (a b c : Fin 4) :
    kronK8 (a, b, c) = kronK8 (0, 0, c) * kronK8 (0, b, 0) * kronK8 (a, 0, 0) := by
  show kronSU8 (pauli4 a) (pauli4 b) (pauli4 c)
    = kronSU8 (pauli4 0) (pauli4 0) (pauli4 c) * kronSU8 (pauli4 0) (pauli4 b) (pauli4 0)
      * kronSU8 (pauli4 a) (pauli4 0) (pauli4 0)
  rw [← kronSU8_mul, ← kronSU8_mul]
  simp [show (pauli4 0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 from rfl]

/-! ## 2. The full tensor-Pauli conjugation closure -/

/-- **Full tensor-Pauli conjugation closure.** If an ℝ-submodule `W` of `8×8` matrices is closed under
conjugation by each of the six per-qubit `H`/`S` generator matrices, then it is closed under conjugation
by every tensor-Pauli `kronK8 w`. (The conjugation by `kronK8 w` factors as the iterated single-qubit
conjugation `conjP1 ∘ conjP2 ∘ conjP3`, matched up by the forward/backward factorizations.) -/
theorem conj_kronK8_closed (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (hH1 : ∀ Y ∈ W, (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH2 : ∀ Y ∈ W, (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH3 : ∀ Y ∈ W, (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS1 : ∀ Y ∈ W, (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS2 : ∀ Y ∈ W, (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS3 : ∀ Y ∈ W, (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (w : PauliLabel) :
    ∀ Y ∈ W, kronK8 w * Y * kronK8 w ∈ W := by
  obtain ⟨a, b, c⟩ := w
  intro Y hY
  have h3 := conjP3 W hH3 hS3 c Y hY
  have h2 := conjP2 W hH2 hS2 b _ h3
  have h1 := conjP1 W hH1 hS1 a _ h2
  have key : kronK8 (a, b, c) * Y * kronK8 (a, b, c)
      = kronK8 (a, 0, 0) * (kronK8 (0, b, 0) * (kronK8 (0, 0, c) * Y * kronK8 (0, 0, c)) *
          kronK8 (0, b, 0)) * kronK8 (a, 0, 0) := by
    nth_rewrite 1 [kronK8_fwd a b c]
    rw [kronK8_bwd a b c]
    simp only [mul_assoc]
  rw [key]; exact h1

end SKEFTHawking.FKLW.CliffordCCZSU8
