/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 — SU(4) trapped-ion v4 witness (tracked Prop + extraction)

Tracked-Prop framework for the substantive Lie-algebra spanning + flow-line
containment witness needed to discharge `H_of_G (trappedIonGeneratingSetSU4
N hN) = ⊤`. Follows the Phase 6u CliffordT pattern
(`cliffordT_v4_witness_tracked`).

The tracked Prop captures the existential v4-witness shape directly matching
`ClosureDenseWitness (trappedIonGeneratingSetSU4 N hN)`:
  * `n` tangents `X : Fin n → Matrix (Fin 4) (Fin 4) ℂ` in 𝔰𝔲(4)
  * Spanning: every Y ∈ 𝔰𝔲(4) is an ℝ-linear combination of the X i
  * Flow-line containment: `exp(ℝ • X i) ⊆ H_of_G trappedIonGeneratingSetSU4`

## Substantive discharge plan (multi-session work)

The substantive discharge requires the Brylinski-Brylinski 2002 entangler
theorem applied to the trapped-ion alphabet:
  1. Per-ion 1Q closure: `{H_SU, T_SU}` on each ion generates a dense
     subgroup of SU(2) per ion (via BMPRV 1999 Niven argument, Phase 6u
     CliffordT lineage).
  2. MS(θ) as 2-qubit entangler: MS(π/N) for N ≥ 1 is a non-trivial
     entangling 2-qubit gate (not equivalent to product of 1Q gates).
  3. Brylinski-Brylinski 2002: per-ion universal 1Q + entangling 2Q ⟹
     universal compilation for SU(4) = 15-dimensional.
  4. Extract tangents from the 15 Lie algebra generators of 𝔰𝔲(4) via
     1Q derivatives (4 single-qubit Pauli rotations per ion = 6 tangents)
     and MS-conjugated 1Q derivatives (9 additional tangents via the
     entangler-conjugation construction).

This is honest multi-session formalization work (~300-500 LoC per the
Phase 6y roadmap line 139). The current commit ships the tracked-Prop
interface + extraction to `ClosureDenseWitness`; the substantive discharge
ships in T-A1′.2 PROPER follow-on.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected — the tracked Prop is
    a regular `def` (no `axiom`); substantive discharge is shipped via
    conventional Lean proof.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 (tracked Prop +
extraction; substantive discharge in T-A1′.2 PROPER).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdClosureDenseWitness
import SKEFTHawking.FKLW.TrappedIonSU4DensityFromWitness

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The tracked v4-witness Prop for trapped-ion SU(4) -/

/-- **Tracked v4-witness Prop for trapped-ion at SU(4)** at grid resolution `N`.

Existentially asserts the v4 witness data: a finite collection of
traceless skew-Hermitian tangents whose ℝ-span covers 𝔰𝔲(4) (15-dim) and
whose 1-parameter flow lines are in
`H_of_G (trappedIonGeneratingSetSU4 N hN)`.

Substantive discharge requires the Brylinski-Brylinski entangler theorem +
per-ion 1Q Niven density; this Prop is the tracked-Prop interface
consumers depend on, decoupling the cascade architecture from the
substantive Lie-theoretic work. -/
def trappedIonSU4_v4_witness_tracked (N : ℕ) (hN : 0 < N) : Prop :=
  ∃ (n : ℕ) (X : Fin n → Matrix (Fin 4) (Fin 4) ℂ),
    (∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0) ∧
    (∀ Y : Matrix (Fin 4) (Fin 4) ℂ, Y.IsSkewHermitian → Y.trace = 0 →
        ∃ c : Fin n → ℝ, Y = ∑ i, ((c i : ℝ) : ℂ) • X i) ∧
    (∀ i, ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
        M ∈ SKEFTHawking.FKLW.GenericSUd.H_of_G
          (trappedIonGeneratingSetSU4 N hN) ∧
        M.val = NormedSpace.exp (((t : ℝ) : ℂ) • X i))

/-! ## 2. Build `ClosureDenseWitness` from tracked Prop -/

/-- **`ClosureDenseWitness` extraction from tracked v4-witness Prop**
(Type-level extraction via `Nonempty.some + Classical.choice`).

Mirrors `cliffordTClosureDenseWitness_of_tracked` from Phase 6u Wave 2. -/
noncomputable def trappedIonSU4ClosureDenseWitness_of_tracked
    (N : ℕ) (hN : 0 < N)
    (h_tracked : trappedIonSU4_v4_witness_tracked N hN) :
    SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
      (trappedIonGeneratingSetSU4 N hN) := by
  have h_ne : Nonempty
      (SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
        (trappedIonGeneratingSetSU4 N hN)) := by
    obtain ⟨n, X, hX_in_sud, hX_spans, hX_flow⟩ := h_tracked
    exact ⟨{ n := n, X := X, hX_in_sud := hX_in_sud,
             hX_spans := hX_spans, hX_flow := hX_flow }⟩
  exact h_ne.some

/-! ## 3. UNCONDITIONAL density + ε₀-net from tracked Prop -/

/-- **UNCONDITIONAL trapped-ion SU(4) density** given the tracked v4-witness
Prop. -/
theorem trappedIonGeneratingSetSU4_isDense_of_tracked
    (N : ℕ) (hN : 0 < N)
    (h_tracked : trappedIonSU4_v4_witness_tracked N hN) :
    SKEFTHawking.FKLW.GenericSUd.IsDenseInSUd_gs
      (trappedIonGeneratingSetSU4 N hN) :=
  trappedIonGeneratingSetSU4_isDense N hN
    (trappedIonSU4ClosureDenseWitness_of_tracked N hN h_tracked)

/-- **UNCONDITIONAL `H_of_G trappedIonGeneratingSetSU4 = ⊤` from tracked Prop**. -/
theorem trappedIonGeneratingSetSU4_H_of_G_eq_top_of_tracked
    (N : ℕ) (hN : 0 < N)
    (h_tracked : trappedIonSU4_v4_witness_tracked N hN) :
    SKEFTHawking.FKLW.GenericSUd.H_of_G
      (trappedIonGeneratingSetSU4 N hN) = ⊤ :=
  trappedIonGeneratingSetSU4_H_of_G_eq_top N hN
    (trappedIonSU4ClosureDenseWitness_of_tracked N hN h_tracked)

/-- **UNCONDITIONAL trapped-ion ε₀-net findNearest from tracked Prop**. -/
noncomputable def trappedIonEpsilonNet_findNearest_of_tracked
    (N : ℕ) (hN : 0 < N)
    (h_tracked : trappedIonSU4_v4_witness_tracked N hN)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    FreeGroup (Fin (4 + 2 * N)) :=
  trappedIonEpsilonNet_findNearest N hN
    (trappedIonSU4ClosureDenseWitness_of_tracked N hN h_tracked) U ε₀ hε₀_pos

/-- **Correctness of `trappedIonEpsilonNet_findNearest_of_tracked`**. -/
theorem trappedIonEpsilonNet_findNearest_of_tracked_approx
    (N : ℕ) (hN : 0 < N)
    (h_tracked : trappedIonSU4_v4_witness_tracked N hN)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    ‖(((trappedIonGeneratingSetSU4 N hN).ρ_hom
          (trappedIonEpsilonNet_findNearest_of_tracked N hN h_tracked
            U ε₀ hε₀_pos) :
        ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
      Matrix (Fin 4) (Fin 4) ℂ) -
        (U : Matrix (Fin 4) (Fin 4) ℂ)‖ < ε₀ :=
  trappedIonEpsilonNet_findNearest_approx N hN
    (trappedIonSU4ClosureDenseWitness_of_tracked N hN h_tracked) U ε₀ hε₀_pos

end SKEFTHawking.FKLW.TrappedIonSU4
