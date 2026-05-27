/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 — SU(4) trapped-ion density (UNCONDITIONAL from witness)

The cascade-closing module that takes a `ClosureDenseWitness` for the full
trapped-ion `trappedIonGeneratingSetSU4 N hN` and produces the UNCONDITIONAL
SU(4) closure-density predicate, using:

  * Phase 6y **S.2g** UNCONDITIONAL Cartan v4 (`CartanFinalStep_SUd_v4_holds`,
    shipped in `GenericSUdCartanUnconditional`).
  * Phase 6y **S.5** UNCONDITIONAL discharge (`densityFromWitness`, composes
    S.2g with the conditional density).

This module ships the **structural bridge** — the substantive `ClosureDenseWitness`
itself is a separate ship (`TrappedIonSU4WitnessTracked` for the tracked-Prop
discharge form; substantive Brylinski-Brylinski 2002 entangler argument for the
fully unconditional witness ships in a follow-on).

For trapped-ion at SU(4) the standard Brylinski-Brylinski universality theorem
(2002) shows that ANY entangling 2-qubit gate + universal 1Q gates gives
universal compilation; the MS(θ) family at θ = π/(2N) (or similar) provides
an entangler, the H_SU+T_SU per-ion gates provide universal 1Q closure (via
the BMPRV 1999 Niven argument, instantiated per ion).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 cascade-closing
bridge (UNCONDITIONAL from witness; substantive witness construction in
T-A1′.2 PROPER).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDischargeUnconditional
import SKEFTHawking.FKLW.GenericSUdEpsilonNet
import SKEFTHawking.FKLW.TrappedIonGeneratingSetSU4Full

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. UNCONDITIONAL T-A1′.2 density from witness

Given a `ClosureDenseWitness` for the full trapped-ion alphabet, density
follows UNCONDITIONALLY (the prior `h_cartan` hypothesis is now auto-
discharged via Phase 6y S.2g UNCONDITIONAL). -/

/-- **UNCONDITIONAL T-A1′.2 density**: the full trapped-ion alphabet at
grid resolution `N` is dense in SU(4), given a `ClosureDenseWitness`.

The hypothesis on the substantive Lie-algebra-spanning witness is now
the ONLY input — the previous `(h_cartan : CartanFinalStep_SUd_v4 4)`
hypothesis is auto-discharged via Phase 6y S.2g UNCONDITIONAL. -/
theorem trappedIonGeneratingSetSU4_isDense (N : ℕ) (hN : 0 < N)
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            (trappedIonGeneratingSetSU4 N hN)) :
    SKEFTHawking.FKLW.GenericSUd.IsDenseInSUd_gs
      (trappedIonGeneratingSetSU4 N hN) :=
  SKEFTHawking.FKLW.GenericSUd.densityFromWitness (d := 4) (by decide) w

/-! ## 2. UNCONDITIONAL `H_of_G = ⊤` for trapped-ion -/

/-- **UNCONDITIONAL `H_of_G (trappedIonGeneratingSetSU4 N hN) = ⊤`**. -/
theorem trappedIonGeneratingSetSU4_H_of_G_eq_top (N : ℕ) (hN : 0 < N)
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            (trappedIonGeneratingSetSU4 N hN)) :
    SKEFTHawking.FKLW.GenericSUd.H_of_G (trappedIonGeneratingSetSU4 N hN) = ⊤ :=
  SKEFTHawking.FKLW.GenericSUd.H_of_G_eq_top_of_witness (d := 4) (by decide) w

/-! ## 3. UNCONDITIONAL ε₀-net findNearest for trapped-ion at SU(4)

Consumer-facing: given a witness, return a word approximating any U to
within ε₀. -/

/-- **UNCONDITIONAL ε₀-net findNearest for trapped-ion at SU(4)**.

For any U ∈ SU(4) and ε₀ > 0, returns a word in `FreeGroup (Fin (4 + 2*N))`
whose ρ_hom image is within ε₀ of U (operator norm). UNCONDITIONAL given a
closure-density witness. -/
noncomputable def trappedIonEpsilonNet_findNearest
    (N : ℕ) (hN : 0 < N)
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            (trappedIonGeneratingSetSU4 N hN))
    (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    FreeGroup (Fin (4 + 2 * N)) :=
  SKEFTHawking.FKLW.GenericSUd.epsilonNet_findNearest_SUd
    (trappedIonGeneratingSetSU4 N hN)
    (trappedIonGeneratingSetSU4_isDense N hN w)
    U ε₀ hε₀_pos

/-- **Correctness of `trappedIonEpsilonNet_findNearest`** (UNCONDITIONAL). -/
theorem trappedIonEpsilonNet_findNearest_approx
    (N : ℕ) (hN : 0 < N)
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            (trappedIonGeneratingSetSU4 N hN))
    (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    ‖(((trappedIonGeneratingSetSU4 N hN).ρ_hom
          (trappedIonEpsilonNet_findNearest N hN w U ε₀ hε₀_pos) :
        ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
      Matrix (Fin 4) (Fin 4) ℂ) -
        (U : Matrix (Fin 4) (Fin 4) ℂ)‖ < ε₀ :=
  SKEFTHawking.FKLW.GenericSUd.epsilonNet_findNearest_SUd_approx_opNorm
    (trappedIonGeneratingSetSU4 N hN)
    (trappedIonGeneratingSetSU4_isDense N hN w)
    U ε₀ hε₀_pos

end SKEFTHawking.FKLW.TrappedIonSU4
