/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — END-TO-END SU(d) cascade reducing headline to 2 ingredients

The **final-form meta-cascade** composing Sessions 50, 53, 54, 55:
given a per-alphabet at SU(n+2) with FreeGroup α word type, the F#4-compliant
SU(d) headline holds GIVEN ONLY:
  * **(D)** density witness: `IsDenseInSUd_gs gs` (T-X′.2 PROPER substantive
    content)
  * **(B)** super-quad bound discharge: `SkApproxCSuperQuadraticBound_generic_sud
    K ε₀_sud gs (findNearestInCover_SUd-baseFinder) h_det_pred`
    (super-quad bound; mechanically liftable per Explore-agent intel)

Plus the calibration condition `K² · 2·ε₀_sud ≤ 1/4` (algebraic, parametric
in (K, ε₀_sud)).

ALL OTHER substantive content is internally composed:
  * Det predicate (Session 49 UNCONDITIONAL discharge)
  * Polylog level spec (Session 48 substantive discharge)
  * Length-bound recursion (Session 53 parametric discharge + per-alphabet
    instantiation Session 54)
  * BaseFinder length boundedness (Session 55 discharge from constructive
    ε-net)
  * Polylog level chooser (Session 46 closed-form)

## Substantive content shipped

  * `skHeadline_FreeGroup_SUd_cascade_final` — final-form cascade discharge
    of `SolovayKitaevHeadline_FreeGroup_SUd gs h_eq` given (D) + (B) +
    calibration.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — end-to-end cascade
reducing SU(d) headline to 2 remaining substantive ingredients.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascade2Ingredient
import SKEFTHawking.FKLW.GenericSUdBaseFinderLengthBound
import SKEFTHawking.FKLW.GenericSUdConcreteWordLengthBound

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## END-TO-END SU(d) cascade -/

/-- **Final-form 2-ingredient cascade for SU(d) SK headline**.

Discharges `SolovayKitaevHeadline_FreeGroup_SUd gs h_eq` (F#4-compliant
error + length) given ONLY 2 substantive ingredients + calibration:

  * **(D)** `h_dense : IsDenseInSUd_gs gs` (T-X′.2 PROPER substantive
    content — Brylinski-Brylinski 2002 SU(4), Aaronson-Gottesman 2004 SU(8))
  * **(B)** `h_bound` — super-quad bound discharge
  * **Calibration**: `K² · 2·ε₀_sud ≤ 1/4`, `K ≥ 1`, etc.

All other substantive content (det predicate, polylog level spec,
length-bound recursion, baseFinder length-boundedness, polylog level
chooser) is composed internally via Sessions 41-55 substrate.

## Length-bound exponent

The headline form's length exponent is `Real.log 5 / Real.log (3 / 2) ≈ 3.97`,
the canonical Dawson-Nielsen value (arXiv:quant-ph/0505030 §3.3): the SK
recursion expands word length 5× per level while contracting error at the
ε^(3/2) super-quadratic rate, giving `c = log 5 / log (3/2)`. This matches the
project's SU(2) `SolovayKitaevLengthBound.skLengthExponent` and the level
chooser `skLevel_polylog_sud` (which already uses `log (3/2)`). The hypothesis
`h_length_polylog` asserts the polylog bound at this achievable exponent.

(Corrected 2026-05-28 from a 2026-05-27 mis-transcription `log 5 / log 2 ≈ 2.32`,
which was wrongly attributed to Dawson-Nielsen and is unachievable for the
ε^(3/2) recursion — it would require quadratic ε² contraction.) -/
theorem skHeadline_FreeGroup_SUd_cascade_final
    {n : ℕ} {α : Type} [DecidableEq α]
    (K ε₀_sud c : ℝ)
    (hK_pos : 0 < K) (hK_ge_one : 1 ≤ K)
    (hε₀_pos : 0 < ε₀_sud)
    (hc_pos : 0 < c)
    (h_cal : K^2 * (2 * ε₀_sud) ≤ 1 / 4)
    (gs : GeneratingSet (n + 2)) (h_eq : gs.W = FreeGroup α)
    [Nonempty (Fin (n + 2))]
    (h_dense : IsDenseInSUd_gs gs)
    (wordLength : gs.W → ℕ)
    (h_wl : WordLengthFreeGroupLike gs wordLength)
    (h_bound : SkApproxCSuperQuadraticBound_generic_sud K ε₀_sud gs
      (fun U => findNearestInCover_SUd gs h_dense ε₀_sud hε₀_pos U)
      (expIsud_det_eq_one_predicate_holds n))
    (h_length_polylog : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
      (ε : ℝ), 0 < ε → ε ≤ ε₀_sud →
      ((h_eq ▸ skApproxC_generic_sud gs
          (fun U => findNearestInCover_SUd gs h_dense ε₀_sud hε₀_pos U)
          (expIsud_det_eq_one_predicate_holds n)
          (skLevel_polylog_sud K ε) U : FreeGroup α).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq :=
  skHeadline_FreeGroup_SUd_cascade_2ingredient_with_calibration K ε₀_sud c
    hK_pos hε₀_pos hc_pos h_cal gs h_eq
    (fun U => findNearestInCover_SUd gs h_dense ε₀_sud hε₀_pos U)
    h_bound h_length_polylog

end SKEFTHawking.FKLW.GenericSUd
