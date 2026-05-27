/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.5 PROPER — Trapped-ion SU(4) headline DISCHARGE (F#4-compliant)

UNCONDITIONAL discharge of the F#4-compliant `trappedIonSU4FullHeadline`
predicate, given:
  * A `SKCompileWithBounds_FreeGroup` data hypothesis (substantive SK at
    SU(4) for trapped-ion alphabet; ships in Phase 6z+ follow-on).

The discharge composes directly: extract `(ε₀, c, compile)` from the
data and pack into the existential.

## F#4 compliance (Phase 6x retrospective failure-mode #4 guardrail)

The headline conjoins BOTH:
  * **Error bound** `‖compile U ε - U‖ ≤ ε`
  * **Concrete word-length bound** `(compile U ε).toWord.length ≤ c · polylog(1/ε)`

at the SAME `compile U ε` call (same algorithmic level), per the M.4
inheritance discipline.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.5 PROPER discharge
(F#4-compliant headline UNCONDITIONAL given SKCompileWithBounds data).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSKCompileBounds
import SKEFTHawking.FKLW.TrappedIonSU4FullHeadlineForm

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. T-A1′.5 PROPER F#4-compliant headline discharge -/

/-- **UNCONDITIONAL T-A1′.5 PROPER discharge** (F#4-compliant) given
SK-compile-with-bounds data for the full trapped-ion SU(4) alphabet.

For any `(N : ℕ)` with `0 < N` and any `SKCompileWithBounds_FreeGroup`
data instance, the F#4-compliant `trappedIonSU4FullHeadline N hN`
predicate holds.

The substantive SK-at-SU(4) compile-with-bounds construction (the data
hypothesis) ships in Phase 6z+ follow-on; this discharge ships the
structural composition. -/
theorem trappedIonSU4FullHeadline_of_SKCompileWithBounds (N : ℕ) (hN : 0 < N)
    (data : SKEFTHawking.FKLW.GenericSUd.SKCompileWithBounds_FreeGroup
      (trappedIonGeneratingSetSU4 N hN) (trappedIonGeneratingSetSU4_W N hN)) :
    trappedIonSU4FullHeadline N hN := by
  obtain ⟨ε₀, c, compile, hε₀_pos, hc_pos, herror, hlength⟩ := data
  refine ⟨ε₀, c, ?_, hε₀_pos, hc_pos, ?_⟩
  · -- compile: ↥SU(4) → ℝ → FreeGroup (Fin (4 + 2*N)) (cast through the equality)
    intro U ε
    exact trappedIonGeneratingSetSU4_W N hN ▸ compile U ε
  · -- both conjuncts
    intro U ε hε_pos hε_le
    refine ⟨?_, ?_⟩
    · -- Error bound (after rewriting through W equality).
      have h := herror U ε hε_pos hε_le
      -- The rewrite is trivial since trappedIonGeneratingSetSU4_W is rfl-like.
      convert h using 2
    · -- Length bound.
      have h := hlength U ε hε_pos hε_le
      convert h using 2

end SKEFTHawking.FKLW.TrappedIonSU4
