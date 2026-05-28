/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) SK super-quadratic error bound predicate

The **SU(d) generalization of `SkApproxCSuperQuadraticBound_generic`**
(Phase 6u Wave 4, SU(2)). Predicate form of the super-quadratic error
bound for the `skApproxC_generic_sud` recursion:

  `∀ n U, ‖gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U) - U‖
    ≤ ε_seq K (2·ε₀_sud) n`

where `ε_seq K ε₀ n` is the project's standard super-quadratic sequence
(recursion `ε_seq K ε₀ (n+1) = K · (ε_seq K ε₀ n)^(3/2)`).

The substantive discharge (analog of Phase 6u Wave 4b's ~981-LoC
`SkApproxCSuperQuadraticBound_generic_holds`) ships in follow-on sessions.

## Substantive content shipped

  * `SkApproxCSuperQuadraticBound_generic_sud K ε₀_sud gs baseFinder h_det_pred : Prop`
    — the predicate.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — generic SU(d) SK
super-quadratic bound predicate.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkApproxC
import SKEFTHawking.FKLW.EpsilonSeq

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## The SU(d) super-quadratic bound predicate -/

/-- **The SU(d) super-quadratic bound predicate**.

For every level `n` and every target `U ∈ SU(m+2)`, the recursion
`skApproxC_generic_sud gs baseFinder h_det_pred n U` produces a word
whose `gs.ρ_hom` image is within `ε_seq K (2·ε₀_sud) n` of `U`.

Captures the same shape as Phase 6u Wave 4's
`SkApproxCSuperQuadraticBound_generic` at SU(2), generalized to arbitrary
d = m + 2 ≥ 2. -/
def SkApproxCSuperQuadraticBound_generic_sud {m : ℕ}
    (K ε₀_sud : ℝ)
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2)) : Prop :=
  ∀ (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)),
    ‖((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K (2 * ε₀_sud) n

end SKEFTHawking.FKLW.GenericSUd
