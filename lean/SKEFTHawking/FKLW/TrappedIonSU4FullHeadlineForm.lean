/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.5 PROPER — Trapped-ion SU(4) FULL-alphabet headline form

Headline predicate for the FULL trapped-ion SU(4) compilation (MS gates
+ 1Q rotations BOTH compiled, per the Phase 6y T-A1′ roadmap), at the
PROPER alphabet level (not the 1Q-only sub-alphabet partial of
`trappedIonSU4_1QHeadline`).

Predicate level (no axioms, no tracked Props; F#4 guardrail compliant
with both M.4 conjuncts).

## Headline shape (M.4 inheritance — F#4 guardrail)

For the full trapped-ion SU(4) alphabet at MS-grid resolution `N`,
shaped as `trappedIonGeneratingSetSU4 N hN`, the headline asserts:

There exist `ε₀, c > 0` and a compilation function
`compile : ↥SU(4) → ℝ → FreeGroup (Fin (4 + 2*N))` such that for any
`U ∈ SU(4)` and any `ε ∈ (0, ε₀]`:

  * Error: `‖(ρ_hom (compile U ε)).val - U.val‖ ≤ ε`
  * Length: `(compile U ε).toWord.length ≤ c · log(1/ε)^(log 5 / log (3/2))`

Both conjuncts at the SAME algorithmic compile level (M.4 inheritance,
satisfying F#4).

## Discharge plan

UNCONDITIONAL discharge composes:
  * T-A1′.1 PROPER (`trappedIonGeneratingSetSU4` — shipped ✓)
  * T-A1′.2 closure-density at SU(4) (pending — needs S.2g unconditional)
  * T-A1′.3 ε₀-net algorithmic (pending)
  * T-A1′.4 calibration (pending)
  * S.5 generic SU(d) discharge composed for d=4 (pending)

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.5 PROPER (full
alphabet headline form, supersedes the 1Q-only partial).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdHeadlineForm
import SKEFTHawking.FKLW.TrappedIonGeneratingSetSU4Full

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The T-A1′.5 PROPER headline statement at the FULL alphabet -/

/-- **The T-A1′.5 PROPER headline predicate** at the full
`trappedIonGeneratingSetSU4 N hN` alphabet (with MS at rational-π/N
grid).

The structural target shape of T-A1′.5 PROPER: SolovayKitaev quantitative
bundled-strict headline at SU(4) for the FULL trapped-ion alphabet
(4 single-qubit gates + 2N MS gates), with `FreeGroup (Fin (4 + 2*N))`
word length as the concrete length metric.

Supersedes the 1Q-only `trappedIonSU4_1QHeadline` partial (which used
the sub-alphabet without MS). The full alphabet IS the production
trapped-ion gate set (Quantinuum / IonQ / AQT). -/
def trappedIonSU4FullHeadline (N : ℕ) (hN : 0 < N) : Prop :=
  ∃ (ε₀ : ℝ) (c : ℝ)
    (compile : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ) → ℝ →
      FreeGroup (Fin (4 + 2 * N))),
    0 < ε₀ ∧ 0 < c ∧
    ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ))
      (ε : ℝ) (_hε_pos : 0 < ε) (_hε_le : ε ≤ ε₀),
      -- Error bound: ‖ρ_hom(compile U ε) - U‖ ≤ ε
      ‖(((trappedIonGeneratingSetSU4 N hN).ρ_hom (compile U ε) :
            ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
          Matrix (Fin 4) (Fin 4) ℂ) -
        (U : Matrix (Fin 4) (Fin 4) ℂ)‖ ≤ ε ∧
      -- Concrete word-length bound (M.4 inheritance, F#4 guardrail)
      ((compile U ε).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))

/-! ## 2. Bridge: 1Q-only sub-alphabet is a special case at N = 0

For consumers needing the 1Q-only sub-alphabet headline (the existing
`trappedIonSU4_1QHeadline` from `TrappedIonSU4HeadlineForm`), there
is a structural relationship: the 1Q sub-alphabet uses
`FreeGroup (Fin 4)`, while the full alphabet at `N = 1` (minimal MS
grid) uses `FreeGroup (Fin 6)`. The 1Q ⊆ full inclusion is by
`Fin.castLE 4 6` on the generator level.

A direct biconditional bridge is not provided here because the two
headlines have different word types; consumers should use whichever
shape matches their alphabet. -/

end SKEFTHawking.FKLW.TrappedIonSU4
