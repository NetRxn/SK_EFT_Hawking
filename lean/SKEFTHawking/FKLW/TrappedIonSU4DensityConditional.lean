/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2-substrate — SU(4) trapped-ion density (CONDITIONAL on Cartan v4)

The structural connection: assuming a `ClosureDenseWitness` is constructed
for the full trapped-ion `trappedIonGeneratingSetSU4 N hN`, the conditional
density follows from Phase 6y S.2g (`CartanFinalStep_SUd_v4 4` discharge).

This module ships the **conditional bridge**: given a hypothetical
witness (4 generators + MS-grid generate dense subgroup of SU(4)) AND
the Cartan v4 discharge at d=4, then `trappedIonGeneratingSetSU4 N hN`
is dense in SU(4).

The unconditional discharge composes:
  * The substantive witness construction (Aharonov-Arad lineage for
    trapped-ion alphabet; ships in T-A1′.2 PROPER).
  * Phase 6y S.2g unconditional (`CartanFinalStep_SUd_v4_holds`; ships
    in S.2g PROPER via the multi-parameter IFT route).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 substrate
(conditional structural bridge; PROPER discharge in T-A1′.2 PROPER).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdClosureDenseWitness
import SKEFTHawking.FKLW.GenericSUdEpsilonNet
import SKEFTHawking.FKLW.TrappedIonGeneratingSetSU4Full

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Conditional density of the full trapped-ion GeneratingSet

Given (a) a `ClosureDenseWitness` for `trappedIonGeneratingSetSU4 N hN`
and (b) the Phase 6y S.2g `CartanFinalStep_SUd_v4 4` discharge, the
full trapped-ion image is dense in SU(4). -/

/-- **Conditional T-A1′.2 density**: the full trapped-ion alphabet at
grid resolution `N` is dense in SU(4), conditional on a closure-density
witness AND Phase 6y S.2g (Cartan v4 at d = 4).

For the unconditional version, both prerequisites need to ship:
  * **Witness**: explicit Aharonov-Arad-style tangents from the alphabet
    (4 single-qubit generators + 2N MS gates) spanning 𝔰𝔲(4) (15-dim).
  * **Cartan v4**: Phase 6y S.2g full discharge via the multi-parameter
    IFT route. -/
theorem trappedIonGeneratingSetSU4_isDense_conditional (N : ℕ) (hN : 0 < N)
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            (trappedIonGeneratingSetSU4 N hN))
    (h_cartan : SKEFTHawking.FKLW.GenericSUd.CartanFinalStep_SUd_v4 4) :
    SKEFTHawking.FKLW.GenericSUd.IsDenseInSUd_gs
      (trappedIonGeneratingSetSU4 N hN) :=
  SKEFTHawking.FKLW.GenericSUd.densityFromWitness_conditional w h_cartan

/-! ## 2. Consumer: ε₀-net findNearest at full trapped-ion alphabet

Direct consumer of `epsilonNet_findNearest_SUd` instantiated at the full
trapped-ion GeneratingSet. Returns a word in
`FreeGroup (Fin (4 + 2*N))` approximating any U ∈ SU(4) to within ε₀,
conditional on the same prerequisites. -/

/-- **Consumer ε₀-net for full trapped-ion SU(4) compilation**
(conditional version).

For any target `U ∈ SU(4)` and `ε₀ > 0`, returns a word in
`FreeGroup (Fin (4 + 2*N))` whose ρ_hom image is within ε₀ of U,
conditional on the witness + Cartan v4. -/
noncomputable def trappedIonEpsilonNet_findNearest_conditional
    (N : ℕ) (hN : 0 < N)
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            (trappedIonGeneratingSetSU4 N hN))
    (h_cartan : SKEFTHawking.FKLW.GenericSUd.CartanFinalStep_SUd_v4 4)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    FreeGroup (Fin (4 + 2 * N)) :=
  SKEFTHawking.FKLW.GenericSUd.epsilonNet_findNearest_SUd
    (trappedIonGeneratingSetSU4 N hN)
    (trappedIonGeneratingSetSU4_isDense_conditional N hN w h_cartan)
    U ε₀ hε₀_pos

/-- **Correctness of `trappedIonEpsilonNet_findNearest_conditional`**:
the returned word approximates U to within ε₀ (operator norm). -/
theorem trappedIonEpsilonNet_findNearest_conditional_approx
    (N : ℕ) (hN : 0 < N)
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            (trappedIonGeneratingSetSU4 N hN))
    (h_cartan : SKEFTHawking.FKLW.GenericSUd.CartanFinalStep_SUd_v4 4)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    ‖(((trappedIonGeneratingSetSU4 N hN).ρ_hom
          (trappedIonEpsilonNet_findNearest_conditional N hN w h_cartan
            U ε₀ hε₀_pos) :
        ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
      Matrix (Fin 4) (Fin 4) ℂ) -
        (U : Matrix (Fin 4) (Fin 4) ℂ)‖ < ε₀ :=
  SKEFTHawking.FKLW.GenericSUd.epsilonNet_findNearest_SUd_approx_opNorm
    (trappedIonGeneratingSetSU4 N hN)
    (trappedIonGeneratingSetSU4_isDense_conditional N hN w h_cartan)
    U ε₀ hε₀_pos

end SKEFTHawking.FKLW.TrappedIonSU4
