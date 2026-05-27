/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-X′.3-substrate — Generic SU(d) ε₀-net infrastructure

d-parametric lift of Phase 6u's `GenericSU2.epsilonNet_findNearest`
to the SU(d) substrate. Takes an `IsDenseInSUd_gs gs` density witness
(from a Cartan-discharged `ClosureDenseWitness`) and returns a word in
`gs.W` approximating any target `U ∈ SU(d)` to within `ε₀`.

## Headline definitions

  * `epsilonNet_findNearest_SUd gs h_dense U ε₀ hε₀_pos : gs.W` — for any
    target `U ∈ SU(d)` and threshold `ε₀ > 0`, returns a word in `gs.W`
    whose ρ_hom image is within `ε₀` of `U` in the operator (l∞) norm.

  * `epsilonNet_findNearest_SUd_approx_opNorm` — correctness lemma: the
    returned word satisfies `‖(gs.ρ_hom w).val - U.val‖ < ε₀`.

## Status posture

This module ships the **existential ε₀-net** (`Classical.choose` extraction
of the density theorem). The **finite-Finset ALGORITHMIC** form (per F#5)
is per-alphabet:

  - Phase 6y T-A1′.3 (SU(4) trapped-ion): ships in a follow-on with
    MS-grid + 1Q-rotation-grid enumeration.
  - Phase 6y T-A2′.3 (SU(8) Clifford+CCZ): ships in a follow-on with
    Clifford+CCZ enumeration (Aaronson-Gottesman lineage).

The existential substrate here is the consumer-friendly building block
for the per-alphabet algorithmic ships.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected — proofs are direct
    `Classical.choose_spec` extractions.
  * **#15** (no new project-local axioms): respected — `Classical.choose`
    is in the standard kernel closure.

## Phase 6y Track T-X′ provenance

Phase 6y Roadmap §"Track T-A1′/T-A2′ detail" sub-wave T-X′.3 substrate
(consumer-facing existential ε-net).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdClosureDenseWitness

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Generic SU(d) ε₀-net findNearest

The fundamental abstraction: a noncomputable function that picks a word
in `gs.W` whose `ρ_hom`-image is within `ε₀` of any target `U ∈ SU(d)`. -/

/-- **Generic SU(d) ε₀-net `findNearest`**: pick a word `w : gs.W` whose
representation under `gs.ρ_hom` approximates `U` to within `ε₀` in the
operator norm.

Built via `Classical.choose` on the density predicate (`h_dense`).
Noncomputable for general `gs`; per-alphabet constructive versions ship
in track instantiations (T-A1′.3 for SU(4) trapped-ion, T-A2′.3 for
SU(8) Clifford+CCZ). -/
noncomputable def epsilonNet_findNearest_SUd {d : ℕ}
    (gs : GeneratingSet d) (h_dense : IsDenseInSUd_gs gs)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) : gs.W :=
  Classical.choose (h_dense U ε₀ hε₀_pos)

/-- **`epsilonNet_findNearest_SUd` correctness**: the returned word
approximates `U` to within `ε₀` in operator norm. -/
theorem epsilonNet_findNearest_SUd_approx_opNorm {d : ℕ}
    (gs : GeneratingSet d) (h_dense : IsDenseInSUd_gs gs)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    ‖((gs.ρ_hom (epsilonNet_findNearest_SUd gs h_dense U ε₀ hε₀_pos) :
        ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
      Matrix (Fin d) (Fin d) ℂ) -
        (U : Matrix (Fin d) (Fin d) ℂ)‖ < ε₀ :=
  Classical.choose_spec (h_dense U ε₀ hε₀_pos)

/-! ## 2. Closeness as `≤` form (consumer-friendly) -/

/-- **`epsilonNet_findNearest_SUd` correctness, `≤` form**: same as
`epsilonNet_findNearest_SUd_approx_opNorm` but with `≤ ε₀` (sometimes
required by downstream consumers expecting non-strict inequality). -/
theorem epsilonNet_findNearest_SUd_approx_opNorm_le {d : ℕ}
    (gs : GeneratingSet d) (h_dense : IsDenseInSUd_gs gs)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    ‖((gs.ρ_hom (epsilonNet_findNearest_SUd gs h_dense U ε₀ hε₀_pos) :
        ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
      Matrix (Fin d) (Fin d) ℂ) -
        (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ε₀ :=
  le_of_lt (epsilonNet_findNearest_SUd_approx_opNorm gs h_dense U ε₀ hε₀_pos)

end SKEFTHawking.FKLW.GenericSUd
