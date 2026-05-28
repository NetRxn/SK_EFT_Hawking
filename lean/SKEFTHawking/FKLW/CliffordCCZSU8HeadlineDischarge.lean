/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.5 PROPER — Clifford+CCZ SU(8) headline DISCHARGE (F#4-compliant)

UNCONDITIONAL discharge of the F#4-compliant `cliffordCCZSU8Headline`
predicate, given a `SKCompileWithBounds_FreeGroup` data hypothesis for
the Clifford+CCZ SU(8) alphabet.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.5 PROPER discharge
(F#4-compliant headline UNCONDITIONAL given SKCompileWithBounds data).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSKCompileBounds
import SKEFTHawking.FKLW.CliffordCCZSU8HeadlineForm

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- `cliffordCCZGeneratingSetSU8.W = FreeGroup (Fin 10)` (by definition). -/
theorem cliffordCCZGeneratingSetSU8_W :
    cliffordCCZGeneratingSetSU8.W = FreeGroup (Fin 10) := rfl

/-! ## 1. T-A2′.5 PROPER F#4-compliant headline discharge -/

/-- **UNCONDITIONAL T-A2′.5 PROPER discharge** (F#4-compliant) given
SK-compile-with-bounds data for the Clifford+CCZ SU(8) alphabet. -/
theorem cliffordCCZSU8Headline_of_SKCompileWithBounds
    (data : SKEFTHawking.FKLW.GenericSUd.SKCompileWithBounds_FreeGroup
      cliffordCCZGeneratingSetSU8 cliffordCCZGeneratingSetSU8_W) :
    cliffordCCZSU8Headline := by
  obtain ⟨ε₀, c, compile, hε₀_pos, hc_pos, herror, hlength⟩ := data
  refine ⟨ε₀, c, ?_, hε₀_pos, hc_pos, ?_⟩
  · intro U ε
    exact cliffordCCZGeneratingSetSU8_W ▸ compile U ε
  · intro U ε hε_pos hε_le
    refine ⟨?_, ?_⟩
    · have h := herror U ε hε_pos hε_le
      convert h using 2
    · have h := hlength U ε hε_pos hε_le
      convert h using 2

end SKEFTHawking.FKLW.CliffordCCZSU8
