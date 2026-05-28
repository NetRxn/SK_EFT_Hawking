/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — 2-INGREDIENT cascade leveraging Sessions 48 + 49 discharges

Refined SU(d) Solovay-Kitaev headline cascade taking only the **2 remaining
substantive ingredients** as hypotheses (Session 45's cascade took 4; now
2 are discharged):

  * **Discharged (Session 48)**: `SkLevelPolylog_sud_spec` via
    `skLevel_polylog_sud_spec_holds` (calibration `K² · 2·ε₀_sud ≤ 1/4`)
  * **Discharged (Session 49)**: `ExpIsud_det_eq_one_predicate` via
    `expIsud_det_eq_one_predicate_holds` (spectral decomposition path)

This module composes those discharges into a more streamlined cascade
requiring only:
  * `h_bound : SkApproxCSuperQuadraticBound_generic_sud K ε₀_sud gs baseFinder
    (expIsud_det_eq_one_predicate_holds n)` — super-quadratic bound discharge
  * `h_length_bound : ...` — polylog word-length bound

## Substantive content shipped

  * `skHeadline_FreeGroup_SUd_cascade_2ingredient` — 2-ingredient cascade.
  * `skHeadline_FreeGroup_SUd_cascade_2ingredient_with_calibration` — with
    the calibration condition `K² · 2·ε₀_sud ≤ 1/4` made explicit and the
    level spec auto-discharged.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — refined 2-ingredient
cascade leveraging Sessions 48 + 49 substantive discharges.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascade
import SKEFTHawking.FKLW.GenericSUdSkLevelPolylogSpec
import SKEFTHawking.FKLW.GenericSUdExpIsuDDetDischarge

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 2-ingredient cascade -/

/-- **2-ingredient cascade**: SU(d) SK headline discharge given super-quadratic
bound + length bound + calibration condition (level spec + det auto-discharged
via Sessions 48 + 49). -/
theorem skHeadline_FreeGroup_SUd_cascade_2ingredient_with_calibration
    {n : ℕ} {α : Type} [DecidableEq α]
    (K ε₀_sud c : ℝ)
    (hK_pos : 0 < K) (hε₀_pos : 0 < ε₀_sud)
    (hc_pos : 0 < c)
    (h_cal : K^2 * (2 * ε₀_sud) ≤ 1 / 4)
    (gs : GeneratingSet (n + 2)) (h_eq : gs.W = FreeGroup α)
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ) → gs.W)
    (h_bound : SkApproxCSuperQuadraticBound_generic_sud K ε₀_sud gs baseFinder
      (expIsud_det_eq_one_predicate_holds n))
    (h_length_bound : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
      (ε : ℝ), 0 < ε → ε ≤ ε₀_sud →
      ((h_eq ▸ skApproxC_generic_sud gs baseFinder
          (expIsud_det_eq_one_predicate_holds n)
          (skLevel_polylog_sud K ε) U : FreeGroup α).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq := by
  -- Discharge level spec via Session 48 (skLevel_polylog_sud_spec_holds).
  have h_level_spec : SkLevelPolylog_sud_spec K ε₀_sud :=
    skLevel_polylog_sud_spec_holds K ε₀_sud hK_pos hε₀_pos h_cal
  -- Compose via Session 45's full cascade.
  exact skHeadline_FreeGroup_SUd_cascade K ε₀_sud c hε₀_pos hc_pos gs h_eq
    baseFinder (expIsud_det_eq_one_predicate_holds n) h_bound
    (skLevel_polylog_sud K) h_level_spec h_length_bound

/-- **Reduced 2-ingredient cascade**: alternate form for direct consumer
use, exposing the 2 remaining ingredients (bound + length) under the
unfolded calibration. -/
theorem skHeadline_FreeGroup_SUd_cascade_2ingredient
    {n : ℕ} {α : Type} [DecidableEq α]
    (K ε₀_sud c : ℝ)
    (hK_pos : 0 < K) (hε₀_pos : 0 < ε₀_sud) (hc_pos : 0 < c)
    (h_cal : K^2 * (2 * ε₀_sud) ≤ 1 / 4)
    (gs : GeneratingSet (n + 2)) (h_eq : gs.W = FreeGroup α)
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ) → gs.W)
    (h_bound : SkApproxCSuperQuadraticBound_generic_sud K ε₀_sud gs baseFinder
      (expIsud_det_eq_one_predicate_holds n))
    (h_length_bound : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
      (ε : ℝ), 0 < ε → ε ≤ ε₀_sud →
      ((h_eq ▸ skApproxC_generic_sud gs baseFinder
          (expIsud_det_eq_one_predicate_holds n)
          (skLevel_polylog_sud K ε) U : FreeGroup α).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq :=
  skHeadline_FreeGroup_SUd_cascade_2ingredient_with_calibration K ε₀_sud c
    hK_pos hε₀_pos hc_pos h_cal gs h_eq baseFinder h_bound h_length_bound

end SKEFTHawking.FKLW.GenericSUd
