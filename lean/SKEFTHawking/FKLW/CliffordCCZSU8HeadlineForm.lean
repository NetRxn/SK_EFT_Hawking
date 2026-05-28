/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.5 statement — Clifford+CCZ SU(8) headline form

The Phase 6y T-A2′.5 final bundled-strict Solovay-Kitaev headline
for the SU(8) Clifford+CCZ alphabet. Predicate-level statement form
matching the M.4-inheritance discipline (F#4 guardrail).

The full UNCONDITIONAL discharge composes Phase 6y:
  * T-A2′.1 PROPER (cliffordCCZGeneratingSetSU8 instance, shipped ✓)
  * S.2g final discharge (CartanFinalStep_SUd_v4_holds at d=8, pending)
  * T-A2′.2 closure-density witness (Aaronson-Gottesman 2004, pending)
  * S.5 generic SU(d) discharge (composed for d=8, pending)
  * T-A2′.4 calibration (Wave 4b at d=8 substrate, pending)

## Headline shape (M.4 inheritance — F#4 guardrail compliant)

For the SU(8) Clifford+CCZ alphabet `cliffordCCZGeneratingSetSU8`,
there exists `ε₀, c > 0` and a compilation function
`compile : ↥SU(8) → ℝ → FreeGroup (Fin 10)` such that for any
`U ∈ SU(8)` and any `ε ∈ (0, ε₀]`:

  * Error: `‖(ρ_hom (compile U ε)).val - U.val‖ ≤ ε`
  * Length: `(compile U ε).toWord.length ≤ c · log(1/ε)^(log 5 / log (3/2))`

Both conjuncts at the SAME algorithmic compile level (M.4
inheritance, satisfying F#4).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.5 (headline
statement).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdHeadlineForm
import SKEFTHawking.FKLW.CliffordCCZGeneratingSetSU8Full

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The T-A2′.5 headline statement

The Phase 6y T-A2′.5 final Solovay-Kitaev headline for SU(8) Clifford+CCZ
compilation. -/

/-- **The T-A2′.5 headline predicate** at `cliffordCCZGeneratingSetSU8`.

This is the structural target shape of T-A2′.5: the SolovayKitaev
quantitative bundled-strict headline at SU(8) for the Clifford+CCZ
alphabet, with FreeGroup-word length as the concrete length metric. -/
def cliffordCCZSU8Headline : Prop :=
  ∃ (ε₀ : ℝ) (c : ℝ)
    (compile : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) → ℝ →
      FreeGroup (Fin 10)),
    0 < ε₀ ∧ 0 < c ∧
    ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ))
      (ε : ℝ) (_hε_pos : 0 < ε) (_hε_le : ε ≤ ε₀),
      -- Error bound: ‖ρ_hom(compile U ε) - U‖ ≤ ε
      -- Note: cliffordCCZGeneratingSetSU8.W = FreeGroup (Fin 10) by definition.
      ‖((cliffordCCZGeneratingSetSU8.ρ_hom (compile U ε) :
            ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ) -
        (U : Matrix (Fin 8) (Fin 8) ℂ)‖ ≤ ε ∧
      -- Concrete word-length bound: |compile U ε| ≤ c · log(1/ε)^(log 5 / log (3/2))
      ((compile U ε).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))

end SKEFTHawking.FKLW.CliffordCCZSU8
