/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.6 — UNCONDITIONAL SU(d) SK headline via the concrete re-point (R4 capstone)

The capstone of the concrete-radius re-point (S109–S139): the SU(d) Solovay-Kitaev headline
`SolovayKitaevHeadline_FreeGroup_SUd gs h_eq`, discharged with **NO `h_regime` hypothesis**.

`SolovayKitaevHeadline_FreeGroup_SUd` is **existential over the compile function**, so the
concrete recursion `skApproxC_generic_sud_concrete` (S133) serves directly as the `compile`
witness. The error bound `‖ρ(compile U ε) − U‖ ≤ ε` follows from the **unconditional** concrete
(B) bound `SkApproxCSuperQuadraticBound_generic_sud_concrete_holds` (S139) — which threads no
existential regime — composed with the polylog level spec `skLevel_polylog_sud_spec_holds`. The
word-length conjunct (F#4) is supplied by `h_length_polylog`.

Compared with the IFT cascade `skHeadline_FreeGroup_SUd_cascade_B_discharged` (S103), this version
**drops the `h_regime` hypothesis entirely** — the whole point of the re-point. The headline now
reduces to exactly **(D) density witness + word-length polylog** (no regime).

## Substantive content shipped

  * `skHeadline_FreeGroup_SUd_cascade_final_concrete` — headline from the concrete (B) bound +
    length-polylog + calibration (auto-discharges the level spec).
  * `skHeadline_FreeGroup_SUd_cascade_B_discharged_concrete` — the **UNCONDITIONAL** headline from
    the (D) density witness + length-polylog, with the constructive-ε-net base finder and the (B)
    bound discharged internally. **No `h_regime`.**

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R4 capstone: the concrete cascade
yielding the UNCONDITIONAL SU(d) headline (eliminating the threaded existential `h_regime`).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkApproxCBoundConcrete
import SKEFTHawking.FKLW.GenericSUdHeadlineForm
import SKEFTHawking.FKLW.GenericSUdSkLevelPolylogSpec
import SKEFTHawking.FKLW.GenericSUdConstructiveEpsilonNet
import SKEFTHawking.FKLW.GenericSUdExpIsuDDetDischarge

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Concrete cascade final**: the SU(d) headline from the concrete (B) bound + the
word-length polylog bound + the calibration `K²·2·ε₀_sud ≤ 1/4`. The compile witness is the
concrete recursion `skApproxC_generic_sud_concrete` at the polylog level; the error bound
chains the concrete (B) bound with `skLevel_polylog_sud_spec_holds`. Concrete counterpart of
`skHeadline_FreeGroup_SUd_cascade_final` (S56). -/
theorem skHeadline_FreeGroup_SUd_cascade_final_concrete {n : ℕ} {α : Type} [DecidableEq α]
    (K ε₀_sud c : ℝ)
    (hK_pos : 0 < K) (hε₀_pos : 0 < ε₀_sud) (hc_pos : 0 < c)
    (h_cal : K ^ 2 * (2 * ε₀_sud) ≤ 1 / 4)
    (gs : GeneratingSet (n + 2)) (h_eq : gs.W = FreeGroup α)
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (n + 2))
    (h_bound : SkApproxCSuperQuadraticBound_generic_sud_concrete K ε₀_sud gs baseFinder h_det_pred)
    (h_length_polylog : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) (ε : ℝ),
      0 < ε → ε ≤ ε₀_sud →
      ((h_eq ▸ skApproxC_generic_sud_concrete gs baseFinder h_det_pred
          (skLevel_polylog_sud K ε) U : FreeGroup α).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log 2)) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq := by
  have h_level_spec : SkLevelPolylog_sud_spec K ε₀_sud :=
    skLevel_polylog_sud_spec_holds K ε₀_sud hK_pos hε₀_pos h_cal
  refine ⟨ε₀_sud, c, fun U ε => skApproxC_generic_sud_concrete gs baseFinder h_det_pred
      (skLevel_polylog_sud K ε) U, hε₀_pos, hc_pos, ?_⟩
  intro U ε hε_pos hε_le
  exact ⟨le_trans (h_bound (skLevel_polylog_sud K ε) U) (h_level_spec ε hε_pos hε_le),
    h_length_polylog U ε hε_pos hε_le⟩

/-- **UNCONDITIONAL SU(d) SK headline** (R4 capstone): the headline
`SolovayKitaevHeadline_FreeGroup_SUd gs h_eq` follows from the **(D) density witness** + the
**word-length polylog bound** — **with NO `h_regime` hypothesis**. The constructive-ε-net base
finder `findNearestInCover_SUd` (its ε₀-net property `< ε₀ ≤ 2·ε₀` discharges the base-finder
hypothesis) and the **unconditional** concrete (B) bound
`SkApproxCSuperQuadraticBound_generic_sud_concrete_holds` (S139) are composed internally. This is
the concrete counterpart of `skHeadline_FreeGroup_SUd_cascade_B_discharged` (S103) with the
existential `h_regime` ELIMINATED — the capstone of the re-point. -/
theorem skHeadline_FreeGroup_SUd_cascade_B_discharged_concrete {n : ℕ} {α : Type} [DecidableEq α]
    (c : ℝ) (hc_pos : 0 < c)
    (gs : GeneratingSet (n + 2)) (h_eq : gs.W = FreeGroup α)
    [Nonempty (Fin (n + 2))]
    (h_dense : IsDenseInSUd_gs gs)
    (h_length_polylog : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) (ε : ℝ),
      0 < ε → ε ≤ ε₀_sud (n + 2) →
      ((h_eq ▸ skApproxC_generic_sud_concrete gs
          (fun U => findNearestInCover_SUd gs h_dense (ε₀_sud (n + 2))
            (ε₀_sud_pos (d := n + 2) (by omega)) U)
          (expIsud_det_eq_one_predicate_holds n)
          (skLevel_polylog_sud (K_compose_sud (n + 2)) ε) U : FreeGroup α).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log 2)) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq := by
  have hε₀_pos : 0 < ε₀_sud (n + 2) := ε₀_sud_pos (by omega)
  have h_baseFinder : BaseFinder_approximates_within_sud gs
      (fun U => findNearestInCover_SUd gs h_dense (ε₀_sud (n + 2)) hε₀_pos U)
      (2 * ε₀_sud (n + 2)) := by
    intro U
    exact lt_of_lt_of_le
      (findNearestInCover_SUd_approx_opNorm gs h_dense (ε₀_sud (n + 2)) hε₀_pos U)
      (by linarith [hε₀_pos])
  have h_bound := SkApproxCSuperQuadraticBound_generic_sud_concrete_holds gs
    (fun U => findNearestInCover_SUd gs h_dense (ε₀_sud (n + 2)) hε₀_pos U)
    (expIsud_det_eq_one_predicate_holds n) h_baseFinder
  exact skHeadline_FreeGroup_SUd_cascade_final_concrete (K_compose_sud (n + 2)) (ε₀_sud (n + 2)) c
    (K_compose_sud_pos (by omega)) hε₀_pos hc_pos
    (K_compose_sud_calibration_le (by omega)) gs h_eq _
    (expIsud_det_eq_one_predicate_holds n) h_bound h_length_polylog

end SKEFTHawking.FKLW.GenericSUd
