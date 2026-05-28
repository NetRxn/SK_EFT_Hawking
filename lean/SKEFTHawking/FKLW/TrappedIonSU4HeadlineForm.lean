/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.5 statement — Trapped-ion SU(4) headline form

The Phase 6y T-A1′.5 final bundled-strict Solovay-Kitaev headline
for the SU(4) trapped-ion 1Q sub-alphabet (the substantively-shipped
T-A1′.1-partial alphabet). Predicate-level statement form satisfying
the M.4-inheritance discipline (F#4 guardrail).

The full UNCONDITIONAL discharge composes:
  * T-A1′.1-partial (trappedIonGeneratingSetSU4_1Q instance, shipped ✓)
  * S.2g final discharge at d=4 (pending — needs Trotter sum)
  * T-A1′.2 closure-density at SU(4) (pending)
  * S.5 generic SU(d) discharge composed for d=4 (pending)
  * T-A1′.4 calibration (pending)

When MSGate SU(4) membership ships and trappedIonGeneratingSetSU4
proper (with MS in alphabet) is constructed, this T-A1′.5 statement
extends to that fuller alphabet via the same predicate shape.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.5 statement.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdHeadlineForm
import SKEFTHawking.FKLW.TrappedIonGeneratingSetSU4Partial

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The T-A1′.5 headline statement at the 1Q sub-alphabet -/

/-- **The T-A1′.5 headline predicate** at `trappedIonGeneratingSetSU4_1Q`.

The structural target shape of T-A1′.5: SolovayKitaev quantitative
bundled-strict headline at SU(4) for the trapped-ion 1Q sub-alphabet,
with FreeGroup (Fin 4)-word length as the concrete length metric.

The sub-alphabet is the 4-generator 1Q-only alphabet
{H_SU_on_ion1, T_SU_on_ion1, H_SU_on_ion2, T_SU_on_ion2}. The full
alphabet with MS(θ) at rational-π/N grid ships via a parametric
extension once MSGateMat SU(4) membership is shipped. -/
def trappedIonSU4_1QHeadline : Prop :=
  ∃ (ε₀ : ℝ) (c : ℝ)
    (compile : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ) → ℝ →
      FreeGroup (Fin 4)),
    0 < ε₀ ∧ 0 < c ∧
    ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ))
      (ε : ℝ) (_hε_pos : 0 < ε) (_hε_le : ε ≤ ε₀),
      -- Error bound: ‖ρ_hom(compile U ε) - U‖ ≤ ε
      ‖((trappedIonGeneratingSetSU4_1Q.ρ_hom (compile U ε) :
            ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
          Matrix (Fin 4) (Fin 4) ℂ) -
        (U : Matrix (Fin 4) (Fin 4) ℂ)‖ ≤ ε ∧
      -- Concrete word-length bound (M.4 inheritance)
      ((compile U ε).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))

/-! ## 2. Future extension to full alphabet with MS

When MSGateMat SU(4) membership ships, the full trapped-ion alphabet
(with MS(θ) at rational-π/N grid) ships as a parametric
`trappedIonGeneratingSetSU4 (N : ℕ)`, and the T-A1′.5 headline extends
accordingly with `FreeGroup (Fin (4 + 2*N))` word type. -/

end SKEFTHawking.FKLW.TrappedIonSU4
