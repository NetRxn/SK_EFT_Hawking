/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.3 — Trapped-ion SU(4) constructive (algorithmic) ε₀-net

F#5-compliant ALGORITHMIC ε₀-net for the trapped-ion SU(4) alphabet
`trappedIonGeneratingSetSU4 N hN`. Composes:

  * `findNearestInCover_SUd` (Phase 6y T-X′.3 algorithmic ε-net substrate,
    GenericSUdConstructiveEpsilonNet)
  * `trappedIonSU4_v4_witness_tracked → IsDenseInSUd_gs` (Phase 6y
    T-A1′.2 tracked-Prop framework, TrappedIonSU4WitnessTracked)

The result: per-`U` algorithmic word extraction via finite-Finset
minimization (NOT existential `Classical.choose` per query), satisfying
the F#5 ALGORITHMIC ε₀-net requirement.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.3 (F#5-compliant
algorithmic ε₀-net).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdConstructiveEpsilonNet
import SKEFTHawking.FKLW.TrappedIonSU4WitnessTracked

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Constructive ε-cover for trapped-ion SU(4) alphabet -/

/-- **Constructive ε-cover Finset for trapped-ion SU(4) alphabet**
(F#5 algorithmic, conditional on tracked-Prop witness).

Given the tracked v4-witness Prop (T-A1′.2), produces the finite Finset
of words ε-covering SU(4). The Finset itself comes from the unconditional
`Matrix.specialUnitaryGroup_isCompact` + density witness via
`GenericSUdConstructiveEpsilonNet`. -/
noncomputable def trappedIonSU4ConstructiveEpsilonCover
    (N : ℕ) (hN : 0 < N)
    (h_tracked : trappedIonSU4_v4_witness_tracked N hN)
    (ε : ℝ) (hε_pos : 0 < ε) :
    Finset (FreeGroup (Fin (4 + 2 * N))) :=
  SKEFTHawking.FKLW.GenericSUd.constructiveEpsilonCover_SUd
    (trappedIonGeneratingSetSU4 N hN)
    (trappedIonGeneratingSetSU4_isDense_of_tracked N hN h_tracked)
    ε hε_pos

/-- **Constructive ε-cover correctness** (every U ∈ SU(4) is ε-close to
some word in the cover). -/
theorem trappedIonSU4ConstructiveEpsilonCover_covers
    (N : ℕ) (hN : 0 < N)
    (h_tracked : trappedIonSU4_v4_witness_tracked N hN)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
    ∃ w ∈ trappedIonSU4ConstructiveEpsilonCover N hN h_tracked ε hε_pos,
      ‖(((trappedIonGeneratingSetSU4 N hN).ρ_hom w :
          ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
          Matrix (Fin 4) (Fin 4) ℂ) -
        (U : Matrix (Fin 4) (Fin 4) ℂ)‖ < ε :=
  SKEFTHawking.FKLW.GenericSUd.constructiveEpsilonCover_SUd_covers
    (trappedIonGeneratingSetSU4 N hN)
    (trappedIonGeneratingSetSU4_isDense_of_tracked N hN h_tracked)
    ε hε_pos U

/-! ## 2. Algorithmic find-nearest -/

/-- **F#5-compliant ALGORITHMIC find-nearest for trapped-ion SU(4)**
(conditional on tracked-Prop witness). -/
noncomputable def trappedIonSU4FindNearestInCover
    (N : ℕ) (hN : 0 < N)
    (h_tracked : trappedIonSU4_v4_witness_tracked N hN)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
    FreeGroup (Fin (4 + 2 * N)) :=
  SKEFTHawking.FKLW.GenericSUd.findNearestInCover_SUd
    (trappedIonGeneratingSetSU4 N hN)
    (trappedIonGeneratingSetSU4_isDense_of_tracked N hN h_tracked)
    ε hε_pos U

/-- **`trappedIonSU4FindNearestInCover` is in the cover**. -/
theorem trappedIonSU4FindNearestInCover_mem_cover
    (N : ℕ) (hN : 0 < N)
    (h_tracked : trappedIonSU4_v4_witness_tracked N hN)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
    trappedIonSU4FindNearestInCover N hN h_tracked ε hε_pos U ∈
      trappedIonSU4ConstructiveEpsilonCover N hN h_tracked ε hε_pos :=
  SKEFTHawking.FKLW.GenericSUd.findNearestInCover_SUd_mem_cover
    (trappedIonGeneratingSetSU4 N hN)
    (trappedIonGeneratingSetSU4_isDense_of_tracked N hN h_tracked)
    ε hε_pos U

/-- **`trappedIonSU4FindNearestInCover` approximates U to within ε**
(operator norm). -/
theorem trappedIonSU4FindNearestInCover_approx
    (N : ℕ) (hN : 0 < N)
    (h_tracked : trappedIonSU4_v4_witness_tracked N hN)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
    ‖(((trappedIonGeneratingSetSU4 N hN).ρ_hom
          (trappedIonSU4FindNearestInCover N hN h_tracked ε hε_pos U) :
        ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
      Matrix (Fin 4) (Fin 4) ℂ) -
        (U : Matrix (Fin 4) (Fin 4) ℂ)‖ < ε :=
  SKEFTHawking.FKLW.GenericSUd.findNearestInCover_SUd_approx_opNorm
    (trappedIonGeneratingSetSU4 N hN)
    (trappedIonGeneratingSetSU4_isDense_of_tracked N hN h_tracked)
    ε hε_pos U

end SKEFTHawking.FKLW.TrappedIonSU4
