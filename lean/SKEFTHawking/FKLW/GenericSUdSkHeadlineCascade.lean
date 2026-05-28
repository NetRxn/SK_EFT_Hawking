/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) SK headline CASCADE composition

The **cascade composition** of Sessions 41-44 SU(d) substrate into the
SK headline shape. Takes the substantive content as named hypothesis
ingredients and packages them into the F#4-compliant headline form
(error + concrete word length bounds at the SAME algorithmic level).

## The cascade chain

  1. (Session 41) `dnStepFG_sud` — per-step (F, G) extraction at SU(d).
  2. (Session 42) `expIsud_of_det_predicate` — SU(d) matrix exp coercion.
  3. (Session 43) `skApproxC_generic_sud` — SK recursion at SU(d).
  4. (Session 44) `SkApproxCSuperQuadraticBound_generic_sud` — bound predicate.
  5. (Session 45 — this module) cascade composition into the headline.

## Substantive content as hypotheses

The Session 45 cascade takes 4 substantive ingredients:
  * `h_det_pred : ExpIsud_det_eq_one_predicate (m+2)` (substantive content
    for unconditional SU(d) exp into SU(d); analog of SU(2) ~2300 LoC
    `DetExpZeroOnSu2_SU2_discharged`)
  * `h_bound : SkApproxCSuperQuadraticBound_generic_sud K ε₀_sud gs ...`
    (analog of SU(2) ~981 LoC `SkApproxCSuperQuadraticBound_generic_holds`)
  * `levelChooser` + `h_level_spec` (analog of SU(2) `skLevel_polylog` +
    `skLevel_polylog_spec`)
  * Length-bound function + bound (analog of SU(2) `skLength` +
    `skLength_at_skLevel_polylog_le_generic`)

The cascade theorem itself is a STRUCTURAL composition (Lean-level
combinator). The substantive ingredients ship in follow-on sessions per
the AC decomposition.

## Substantive content shipped

  * `skApproxC_generic_sud_error_cascade` — error bound cascade
  * `skHeadline_FreeGroup_SUd_cascade` — F#4-compliant cascade into the
    headline predicate

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — SU(d) SK headline
cascade composition.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkApproxCBound
import SKEFTHawking.FKLW.GenericSUdHeadlineForm
import SKEFTHawking.FKLW.EpsilonSeq

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Error cascade -/

/-- **Error cascade**: composes the super-quadratic bound predicate
(Session 44) with a parametric level-chooser to extract the error bound
`‖ρ_hom (skApproxC_generic_sud ... (levelChooser ε) U) - U‖ ≤ ε`.

The `levelChooser` + `h_level_spec` ingredients are the SU(d) analog of
the SU(2) `skLevel_polylog` + `skLevel_polylog_spec`. Threading them as
parameters decouples the cascade from the substantive polylog-level
construction. -/
theorem skApproxC_generic_sud_error_cascade {m : ℕ}
    (K ε₀_sud : ℝ)
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (h_bound : SkApproxCSuperQuadraticBound_generic_sud K ε₀_sud gs baseFinder
      h_det_pred)
    (levelChooser : ℝ → ℕ)
    (h_level_spec : ∀ (ε : ℝ), 0 < ε → ε ≤ ε₀_sud →
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K (2 * ε₀_sud) (levelChooser ε) ≤ ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀_sud) :
    ‖((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred
            (levelChooser ε) U) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ ε := by
  have h_seq_bound := h_bound (levelChooser ε) U
  exact le_trans h_seq_bound (h_level_spec ε hε_pos hε_le)

/-! ## 2. F#4-compliant cascade into the headline predicate -/

/-- **F#4-compliant cascade**: composes the error bound + a polylog
length-bound function + level-chooser into the SU(d) headline predicate
`SolovayKitaevHeadline_FreeGroup_SUd gs h_eq`.

Takes the FreeGroup α encoding of `gs.W` via `h_eq` (per
`SolovayKitaevHeadline_FreeGroup_SUd`'s shape) and the substantive
ingredients as hypotheses:
  * `h_det_pred` — det predicate discharge (Session 42 hypothesis)
  * `h_bound` — super-quadratic error bound (Session 44 predicate)
  * `levelChooser` + `h_level_spec` — polylog level chooser
  * `wordLength : gs.W → ℕ` + `h_length_bound` — polylog word length

Produces the `SolovayKitaevHeadline_FreeGroup_SUd gs h_eq` predicate
discharge.

The `wordLength` parameter unifies the `FreeGroup α`-specific
`toWord.length` (used in `SolovayKitaevHeadline_FreeGroup_SUd`) with the
abstract `wordLength : gs.W → ℕ` (used in the d-generic form
`SolovayKitaevHeadline_SUd`). Downstream consumers using `FreeGroup`
specialize via `wordLength w := (h_eq ▸ w : FreeGroup α).toWord.length`. -/
theorem skHeadline_FreeGroup_SUd_cascade {m : ℕ}
    {α : Type} [DecidableEq α]
    (K ε₀_sud c : ℝ)
    (hε₀_pos : 0 < ε₀_sud) (hc_pos : 0 < c)
    (gs : GeneratingSet (m + 2)) (h_eq : gs.W = FreeGroup α)
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (h_bound : SkApproxCSuperQuadraticBound_generic_sud K ε₀_sud gs baseFinder
      h_det_pred)
    (levelChooser : ℝ → ℕ)
    (h_level_spec : ∀ (ε : ℝ), 0 < ε → ε ≤ ε₀_sud →
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K (2 * ε₀_sud) (levelChooser ε) ≤ ε)
    (h_length_bound : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ))
      (ε : ℝ), 0 < ε → ε ≤ ε₀_sud →
      ((h_eq ▸ skApproxC_generic_sud gs baseFinder h_det_pred
          (levelChooser ε) U : FreeGroup α).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log 2)) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq := by
  refine ⟨ε₀_sud, c, fun U ε => skApproxC_generic_sud gs baseFinder
      h_det_pred (levelChooser ε) U, hε₀_pos, hc_pos, ?_⟩
  intro U ε hε_pos hε_le
  refine ⟨?_, h_length_bound U ε hε_pos hε_le⟩
  exact skApproxC_generic_sud_error_cascade K ε₀_sud gs baseFinder
    h_det_pred h_bound levelChooser h_level_spec U ε hε_pos hε_le

end SKEFTHawking.FKLW.GenericSUd
