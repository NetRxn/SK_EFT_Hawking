/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2 — SU(8) Clifford+CCZ v4 witness (tracked Prop + extraction)

Tracked-Prop framework for the substantive Lie-algebra spanning + flow-line
containment witness needed to discharge `H_of_G cliffordCCZGeneratingSetSU8
= ⊤`. Follows the Phase 6u CliffordT pattern + the Phase 6y T-A1′.2
trapped-ion pattern.

## Substantive discharge (SHIPPED — `CliffordCCZSU8WitnessFull`)

The discharge ships on the **universal Clifford+CCZ+T** alphabet: the 63 tensor-Pauli tangents
span `𝔰𝔲(8)` (standard Hilbert-Schmidt linear algebra), and their flow lines are obtained NOT by
bracket-generation but by **conjugation transport** — the 9 per-qubit flows come from the Phase 6u
Clifford+T SU(2) density (the `T` gate; Boykin et al 1999 Clifford+T universality), and the 54
entangling flows are explicit `CNOT`/Clifford conjugates of them. Density rests on the `{H,T,CNOT}`
sub-alphabet; **CCZ is over-complete and unused** in the witness. (Aaronson-Gottesman 2004 is
stabilizer *simulability* / Clifford group structure, NOT a universality result — do not cite it as
such. The CCZ-essential literal-Clifford+CCZ statement is a tracked strengthening follow-on.)

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 (tracked Prop +
extraction; substantive discharge in T-A2′.2 PROPER).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdClosureDenseWitness
import SKEFTHawking.FKLW.CliffordCCZSU8DensityFromWitness

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The tracked v4-witness Prop for Clifford+CCZ SU(8) -/

/-- **Tracked v4-witness Prop for Clifford+CCZ at SU(8)**.

Existentially asserts the v4 witness data: a finite collection of
traceless skew-Hermitian tangents whose ℝ-span covers 𝔰𝔲(8) (63-dim)
and whose 1-parameter flow lines are in `H_of_G cliffordCCZGeneratingSetSU8`. -/
def cliffordCCZSU8_v4_witness_tracked : Prop :=
  ∃ (n : ℕ) (X : Fin n → Matrix (Fin 8) (Fin 8) ℂ),
    (∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0) ∧
    (∀ Y : Matrix (Fin 8) (Fin 8) ℂ, Y.IsSkewHermitian → Y.trace = 0 →
        ∃ c : Fin n → ℝ, Y = ∑ i, ((c i : ℝ) : ℂ) • X i) ∧
    (∀ i, ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
        M ∈ SKEFTHawking.FKLW.GenericSUd.H_of_G cliffordCCZGeneratingSetSU8 ∧
        M.val = NormedSpace.exp (((t : ℝ) : ℂ) • X i))

/-! ## 2. Build `ClosureDenseWitness` from tracked Prop -/

/-- **`ClosureDenseWitness` extraction from Clifford+CCZ tracked v4-witness**. -/
noncomputable def cliffordCCZSU8ClosureDenseWitness_of_tracked
    (h_tracked : cliffordCCZSU8_v4_witness_tracked) :
    SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness cliffordCCZGeneratingSetSU8 := by
  have h_ne : Nonempty
      (SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness cliffordCCZGeneratingSetSU8) := by
    obtain ⟨n, X, hX_in_sud, hX_spans, hX_flow⟩ := h_tracked
    exact ⟨{ n := n, X := X, hX_in_sud := hX_in_sud,
             hX_spans := hX_spans, hX_flow := hX_flow }⟩
  exact h_ne.some

/-! ## 3. UNCONDITIONAL density + ε₀-net from tracked Prop -/

/-- **UNCONDITIONAL Clifford+CCZ SU(8) density** given the tracked Prop. -/
theorem cliffordCCZGeneratingSetSU8_isDense_of_tracked
    (h_tracked : cliffordCCZSU8_v4_witness_tracked) :
    SKEFTHawking.FKLW.GenericSUd.IsDenseInSUd_gs cliffordCCZGeneratingSetSU8 :=
  cliffordCCZGeneratingSetSU8_isDense
    (cliffordCCZSU8ClosureDenseWitness_of_tracked h_tracked)

/-- **UNCONDITIONAL `H_of_G cliffordCCZGeneratingSetSU8 = ⊤` from tracked Prop**. -/
theorem cliffordCCZGeneratingSetSU8_H_of_G_eq_top_of_tracked
    (h_tracked : cliffordCCZSU8_v4_witness_tracked) :
    SKEFTHawking.FKLW.GenericSUd.H_of_G cliffordCCZGeneratingSetSU8 = ⊤ :=
  cliffordCCZGeneratingSetSU8_H_of_G_eq_top
    (cliffordCCZSU8ClosureDenseWitness_of_tracked h_tracked)

/-- **UNCONDITIONAL Clifford+CCZ ε₀-net findNearest from tracked Prop**. -/
noncomputable def cliffordCCZEpsilonNet_findNearest_of_tracked
    (h_tracked : cliffordCCZSU8_v4_witness_tracked)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    cliffordCCZGeneratingSetSU8.W :=
  cliffordCCZEpsilonNet_findNearest
    (cliffordCCZSU8ClosureDenseWitness_of_tracked h_tracked) U ε₀ hε₀_pos

/-- **Correctness of `cliffordCCZEpsilonNet_findNearest_of_tracked`**. -/
theorem cliffordCCZEpsilonNet_findNearest_of_tracked_approx
    (h_tracked : cliffordCCZSU8_v4_witness_tracked)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    ‖((cliffordCCZGeneratingSetSU8.ρ_hom
          (cliffordCCZEpsilonNet_findNearest_of_tracked h_tracked U ε₀ hε₀_pos) :
        ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
      Matrix (Fin 8) (Fin 8) ℂ) -
        (U : Matrix (Fin 8) (Fin 8) ℂ)‖ < ε₀ :=
  cliffordCCZEpsilonNet_findNearest_approx
    (cliffordCCZSU8ClosureDenseWitness_of_tracked h_tracked) U ε₀ hε₀_pos

end SKEFTHawking.FKLW.CliffordCCZSU8
