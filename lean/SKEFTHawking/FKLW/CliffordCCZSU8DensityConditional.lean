/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2-substrate — SU(8) Clifford+CCZ density (CONDITIONAL on Cartan v4)

The structural connection: assuming a `ClosureDenseWitness` is constructed
for the full Clifford+CCZ `cliffordCCZGeneratingSetSU8`, the conditional
density follows from Phase 6y S.2g (`CartanFinalStep_SUd_v4 8` discharge).

Parallel to `TrappedIonSU4DensityConditional` but at d = 8 for the
Clifford+CCZ alphabet.

The unconditional discharge composes:
  * The substantive witness construction (Aaronson-Gottesman 2004
    lineage for Clifford+CCZ universality at SU(2^n); ships in T-A2′.2
    PROPER).
  * Phase 6y S.2g unconditional (`CartanFinalStep_SUd_v4_holds` at
    d = 8; ships in S.2g PROPER via the multi-parameter IFT route).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 substrate
(conditional structural bridge; PROPER discharge in T-A2′.2 PROPER).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdClosureDenseWitness
import SKEFTHawking.FKLW.GenericSUdEpsilonNet
import SKEFTHawking.FKLW.CliffordCCZGeneratingSetSU8Full

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Conditional density of the full Clifford+CCZ GeneratingSet -/

/-- **Conditional T-A2′.2 density**: the full Clifford+CCZ alphabet
`{H_q1, H_q2, H_q3, CCZ_SU}` is dense in SU(8), conditional on a
closure-density witness AND Phase 6y S.2g (Cartan v4 at d = 8).

For the unconditional version, both prerequisites need to ship:
  * **Witness**: explicit Aaronson-Gottesman 2004 lineage tangents from
    the alphabet (3 single-qubit Hadamards + CCZ) spanning 𝔰𝔲(8)
    (63-dim).
  * **Cartan v4**: Phase 6y S.2g full discharge at d = 8. -/
theorem cliffordCCZGeneratingSetSU8_isDense_conditional
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            cliffordCCZGeneratingSetSU8)
    (h_cartan : SKEFTHawking.FKLW.GenericSUd.CartanFinalStep_SUd_v4 8) :
    SKEFTHawking.FKLW.GenericSUd.IsDenseInSUd_gs
      cliffordCCZGeneratingSetSU8 :=
  SKEFTHawking.FKLW.GenericSUd.densityFromWitness_conditional w h_cartan

/-! ## 2. Consumer: ε₀-net findNearest at full Clifford+CCZ alphabet -/

/-- **Consumer ε₀-net for full Clifford+CCZ SU(8) compilation**
(conditional version). -/
noncomputable def cliffordCCZEpsilonNet_findNearest_conditional
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            cliffordCCZGeneratingSetSU8)
    (h_cartan : SKEFTHawking.FKLW.GenericSUd.CartanFinalStep_SUd_v4 8)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    FreeGroup (Fin 10) :=
  SKEFTHawking.FKLW.GenericSUd.epsilonNet_findNearest_SUd
    cliffordCCZGeneratingSetSU8
    (cliffordCCZGeneratingSetSU8_isDense_conditional w h_cartan)
    U ε₀ hε₀_pos

/-- **Correctness of `cliffordCCZEpsilonNet_findNearest_conditional`**. -/
theorem cliffordCCZEpsilonNet_findNearest_conditional_approx
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            cliffordCCZGeneratingSetSU8)
    (h_cartan : SKEFTHawking.FKLW.GenericSUd.CartanFinalStep_SUd_v4 8)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    ‖((cliffordCCZGeneratingSetSU8.ρ_hom
          (cliffordCCZEpsilonNet_findNearest_conditional w h_cartan
            U ε₀ hε₀_pos) :
        ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
      Matrix (Fin 8) (Fin 8) ℂ) -
        (U : Matrix (Fin 8) (Fin 8) ℂ)‖ < ε₀ :=
  SKEFTHawking.FKLW.GenericSUd.epsilonNet_findNearest_SUd_approx_opNorm
    cliffordCCZGeneratingSetSU8
    (cliffordCCZGeneratingSetSU8_isDense_conditional w h_cartan)
    U ε₀ hε₀_pos

end SKEFTHawking.FKLW.CliffordCCZSU8
