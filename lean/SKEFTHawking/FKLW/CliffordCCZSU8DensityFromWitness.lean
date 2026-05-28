/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2 — SU(8) Clifford+CCZ density (UNCONDITIONAL from witness)

The cascade-closing module for Clifford+CCZ at SU(8): given a closure-density
witness for `cliffordCCZGeneratingSetSU8`, produces UNCONDITIONAL SU(8)
density + ε₀-net via the Phase 6y S.5 unconditional discharge chain.

Clifford+CCZ is universal for SU(2^n) (Shi 2002 / Aharonov 2003; Brylinski-Brylinski 2001 give the
entangling-gate criterion — CCZ is non-primitive). NB: Boykin-Mor-Pulver-Roychowdhury-Vatan 1999 is
the Clifford+**T** basis ({H, σ_z^{1/4}, CNOT}) — i.e. exactly the sub-alphabet the shipped witness
actually uses: its density rests on `{H,T,CNOT}` (Clifford+T, BMPRV 1999), CCZ is over-complete and
unused. (Aaronson-Gottesman 2004 is stabilizer *simulability*, NOT universality — do not cite it as
such.)

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 cascade-closing
bridge (UNCONDITIONAL from witness).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDischargeUnconditional
import SKEFTHawking.FKLW.GenericSUdEpsilonNet
import SKEFTHawking.FKLW.CliffordCCZGeneratingSetSU8Full

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. UNCONDITIONAL T-A2′.2 density from witness -/

/-- **UNCONDITIONAL T-A2′.2 density**: the full Clifford+CCZ alphabet
on 3 qubits is dense in SU(8), given a `ClosureDenseWitness`. -/
theorem cliffordCCZGeneratingSetSU8_isDense
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            cliffordCCZGeneratingSetSU8) :
    SKEFTHawking.FKLW.GenericSUd.IsDenseInSUd_gs cliffordCCZGeneratingSetSU8 :=
  SKEFTHawking.FKLW.GenericSUd.densityFromWitness (d := 8) (by decide) w

/-! ## 2. UNCONDITIONAL `H_of_G = ⊤` for Clifford+CCZ -/

/-- **UNCONDITIONAL `H_of_G cliffordCCZGeneratingSetSU8 = ⊤`**. -/
theorem cliffordCCZGeneratingSetSU8_H_of_G_eq_top
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            cliffordCCZGeneratingSetSU8) :
    SKEFTHawking.FKLW.GenericSUd.H_of_G cliffordCCZGeneratingSetSU8 = ⊤ :=
  SKEFTHawking.FKLW.GenericSUd.H_of_G_eq_top_of_witness (d := 8) (by decide) w

/-! ## 3. UNCONDITIONAL ε₀-net findNearest for Clifford+CCZ at SU(8) -/

/-- **UNCONDITIONAL ε₀-net findNearest for Clifford+CCZ at SU(8)**. -/
noncomputable def cliffordCCZEpsilonNet_findNearest
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            cliffordCCZGeneratingSetSU8)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    cliffordCCZGeneratingSetSU8.W :=
  SKEFTHawking.FKLW.GenericSUd.epsilonNet_findNearest_SUd
    cliffordCCZGeneratingSetSU8
    (cliffordCCZGeneratingSetSU8_isDense w)
    U ε₀ hε₀_pos

/-- **Correctness of `cliffordCCZEpsilonNet_findNearest`** (UNCONDITIONAL). -/
theorem cliffordCCZEpsilonNet_findNearest_approx
    (w : SKEFTHawking.FKLW.GenericSUd.ClosureDenseWitness
            cliffordCCZGeneratingSetSU8)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    ‖((cliffordCCZGeneratingSetSU8.ρ_hom
          (cliffordCCZEpsilonNet_findNearest w U ε₀ hε₀_pos) :
        ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
      Matrix (Fin 8) (Fin 8) ℂ) -
        (U : Matrix (Fin 8) (Fin 8) ℂ)‖ < ε₀ :=
  SKEFTHawking.FKLW.GenericSUd.epsilonNet_findNearest_SUd_approx_opNorm
    cliffordCCZGeneratingSetSU8
    (cliffordCCZGeneratingSetSU8_isDense w)
    U ε₀ hε₀_pos

end SKEFTHawking.FKLW.CliffordCCZSU8
