/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.5 — Generic SU(d) UNCONDITIONAL discharge

Composes S.2g (`CartanFinalStep_SUd_v4_holds`, the UNCONDITIONAL Cartan
v4 discharge) with the S.1+S.2-conditional `densityFromWitness_conditional`
+ `H_of_G_eq_top_of_witness_conditional` to ship the UNCONDITIONAL forms.

The signature now requires ONLY a `ClosureDenseWitness gs` (the per-alphabet
substantive witness), with NO `h_cartan : CartanFinalStep_SUd_v4 d`
hypothesis (auto-discharged via Phase 6y S.2g UNCONDITIONAL).

## Headlines (UNCONDITIONAL, kernel-only modulo per-alphabet witness)

  * `H_of_G_eq_top_of_witness` — `H_of_G gs = ⊤` given a witness.
  * `densityFromWitness` — `IsDenseInSUd_gs gs` given a witness.

These are the d-generic counterparts of Phase 6u's
`H_of_G_eq_top_of_witness` and `densityFromWitness` (SU(2)-specific).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.5 (UNCONDITIONAL discharge —
composes S.2g with S.1+S.2 conditional density).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdClosureDenseWitness
import SKEFTHawking.FKLW.GenericSUdCartanUnconditional

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. UNCONDITIONAL `H_of_G gs = ⊤` from witness alone -/

/-- **UNCONDITIONAL `H_of_G gs = ⊤`** given a `ClosureDenseWitness gs`.

Composes `H_of_G_eq_top_of_witness_conditional` (S.2 conditional) with
`CartanFinalStep_SUd_v4_holds` (S.2g UNCONDITIONAL).

Requires `[Nonempty (Fin d)]` and `0 < d` (i.e., d ≥ 1); the d = 0 case
is trivial (SU(0) is the singleton group). -/
theorem H_of_G_eq_top_of_witness {d : ℕ} [Nonempty (Fin d)] (hd_pos : 0 < d)
    {gs : GeneratingSet d} (w : ClosureDenseWitness gs) :
    H_of_G gs = ⊤ :=
  H_of_G_eq_top_of_witness_conditional w (CartanFinalStep_SUd_v4_holds d hd_pos)

/-- **UNCONDITIONAL density `IsDenseInSUd_gs gs`** given a witness. -/
theorem densityFromWitness {d : ℕ} [Nonempty (Fin d)] (hd_pos : 0 < d)
    {gs : GeneratingSet d} (w : ClosureDenseWitness gs) :
    IsDenseInSUd_gs gs :=
  densityFromWitness_conditional w (CartanFinalStep_SUd_v4_holds d hd_pos)

end SKEFTHawking.FKLW.GenericSUd
