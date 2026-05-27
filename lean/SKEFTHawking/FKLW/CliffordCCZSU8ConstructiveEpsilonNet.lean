/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.3 — Clifford+CCZ SU(8) constructive (algorithmic) ε₀-net

F#5-compliant ALGORITHMIC ε₀-net for the Clifford+CCZ SU(8) alphabet
`cliffordCCZGeneratingSetSU8`. Mirrors `TrappedIonSU4ConstructiveEpsilonNet`
at d=8.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.3 (F#5-compliant
algorithmic ε₀-net).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdConstructiveEpsilonNet
import SKEFTHawking.FKLW.CliffordCCZSU8WitnessTracked

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Constructive ε-cover for Clifford+CCZ SU(8) -/

/-- **Constructive ε-cover Finset for Clifford+CCZ SU(8)**
(F#5 algorithmic, conditional on tracked-Prop witness). -/
noncomputable def cliffordCCZSU8ConstructiveEpsilonCover
    (h_tracked : cliffordCCZSU8_v4_witness_tracked)
    (ε : ℝ) (hε_pos : 0 < ε) :
    Finset cliffordCCZGeneratingSetSU8.W :=
  SKEFTHawking.FKLW.GenericSUd.constructiveEpsilonCover_SUd
    cliffordCCZGeneratingSetSU8
    (cliffordCCZGeneratingSetSU8_isDense_of_tracked h_tracked) ε hε_pos

/-- **Cover correctness**. -/
theorem cliffordCCZSU8ConstructiveEpsilonCover_covers
    (h_tracked : cliffordCCZSU8_v4_witness_tracked)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
    ∃ w ∈ cliffordCCZSU8ConstructiveEpsilonCover h_tracked ε hε_pos,
      ‖((cliffordCCZGeneratingSetSU8.ρ_hom w :
          ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ) -
        (U : Matrix (Fin 8) (Fin 8) ℂ)‖ < ε :=
  SKEFTHawking.FKLW.GenericSUd.constructiveEpsilonCover_SUd_covers
    cliffordCCZGeneratingSetSU8
    (cliffordCCZGeneratingSetSU8_isDense_of_tracked h_tracked) ε hε_pos U

/-! ## 2. Algorithmic find-nearest -/

/-- **F#5-compliant ALGORITHMIC find-nearest for Clifford+CCZ SU(8)**. -/
noncomputable def cliffordCCZSU8FindNearestInCover
    (h_tracked : cliffordCCZSU8_v4_witness_tracked)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
    cliffordCCZGeneratingSetSU8.W :=
  SKEFTHawking.FKLW.GenericSUd.findNearestInCover_SUd
    cliffordCCZGeneratingSetSU8
    (cliffordCCZGeneratingSetSU8_isDense_of_tracked h_tracked) ε hε_pos U

/-- **`cliffordCCZSU8FindNearestInCover` is in the cover**. -/
theorem cliffordCCZSU8FindNearestInCover_mem_cover
    (h_tracked : cliffordCCZSU8_v4_witness_tracked)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
    cliffordCCZSU8FindNearestInCover h_tracked ε hε_pos U ∈
      cliffordCCZSU8ConstructiveEpsilonCover h_tracked ε hε_pos :=
  SKEFTHawking.FKLW.GenericSUd.findNearestInCover_SUd_mem_cover
    cliffordCCZGeneratingSetSU8
    (cliffordCCZGeneratingSetSU8_isDense_of_tracked h_tracked) ε hε_pos U

/-- **`cliffordCCZSU8FindNearestInCover` approximates U to within ε**. -/
theorem cliffordCCZSU8FindNearestInCover_approx
    (h_tracked : cliffordCCZSU8_v4_witness_tracked)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
    ‖((cliffordCCZGeneratingSetSU8.ρ_hom
          (cliffordCCZSU8FindNearestInCover h_tracked ε hε_pos U) :
        ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
      Matrix (Fin 8) (Fin 8) ℂ) -
        (U : Matrix (Fin 8) (Fin 8) ℂ)‖ < ε :=
  SKEFTHawking.FKLW.GenericSUd.findNearestInCover_SUd_approx_opNorm
    cliffordCCZGeneratingSetSU8
    (cliffordCCZGeneratingSetSU8_isDense_of_tracked h_tracked) ε hε_pos U

end SKEFTHawking.FKLW.CliffordCCZSU8
