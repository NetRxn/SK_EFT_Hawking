/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.6 — Headline cascade with (B) super-quad bound DISCHARGED

Feeds Session 102's `SkApproxCSuperQuadraticBound_generic_sud_holds` (the (B)
ingredient, now substantively discharged) into the Session 56 headline cascade
`skHeadline_FreeGroup_SUd_cascade_final`. This removes the `h_bound` ((B))
hypothesis from the SU(d) headline, reducing it to:

  (D) density witness (`IsDenseInSUd_gs gs`) + the regime hypothesis + the
  word-length polylog bound.

The (B) discharge is instantiated at the calibration `(K_compose_sud(n+2),
ε₀_sud(n+2))` with the constructive-ε-net base finder
`findNearestInCover_SUd gs h_dense (ε₀_sud(n+2))`, whose ε-net property
(`findNearestInCover_SUd_approx_opNorm`, `< ε₀_sud ≤ 2·ε₀_sud`) discharges the
base-finder hypothesis.

## Substantive content shipped

  * `skHeadline_FreeGroup_SUd_cascade_B_discharged` — the SU(d) headline from
    (D) + regime + length-polylog, with (B) internally discharged via S102.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — headline cascade with (B)
discharged (materializes the Session 102 super-quad discharge into the headline).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascade2IngredientFinal
import SKEFTHawking.FKLW.GenericSUdSuperQuadInduction
import SKEFTHawking.FKLW.GenericSUdConstructiveEpsilonNet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **SU(d) headline cascade with (B) discharged**: the SU(d) Solovay-Kitaev
headline follows from the (D) density witness + the regime hypothesis + the
word-length polylog bound, with the (B) super-quad bound discharged internally
via Session 102 at the calibration `(K_compose_sud(n+2), ε₀_sud(n+2))` and the
constructive-ε-net base finder. -/
theorem skHeadline_FreeGroup_SUd_cascade_B_discharged
    {n : ℕ} {α : Type} [DecidableEq α]
    (c : ℝ) (hc_pos : 0 < c)
    (gs : GeneratingSet (n + 2)) (h_eq : gs.W = FreeGroup α)
    [Nonempty (Fin (n + 2))]
    (h_dense : IsDenseInSUd_gs gs)
    (wordLength : gs.W → ℕ)
    (h_wl : WordLengthFreeGroupLike gs wordLength)
    (h_regime : ∀ (V Uu : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)),
        ‖(V : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
          (Uu : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 2 * ε₀_sud (n + 2) →
        ‖((-Complex.I) • matrixLog (n + 2) (V⁻¹ * Uu : ↥(Matrix.specialUnitaryGroup
            (Fin (n + 2)) ℂ)).val : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤
          2 * ((n : ℝ) + 2) * ‖(V : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
            (Uu : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ∧
        (‖((-Complex.I) • matrixLog (n + 2) (V⁻¹ * Uu : ↥(Matrix.specialUnitaryGroup
            (Fin (n + 2)) ℂ)).val : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 ∧
          (((-Complex.I) • matrixLog (n + 2) (V⁻¹ * Uu : ↥(Matrix.specialUnitaryGroup
            (Fin (n + 2)) ℂ)).val : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)).IsHermitian ∧
          (((-Complex.I) • matrixLog (n + 2) (V⁻¹ * Uu : ↥(Matrix.specialUnitaryGroup
            (Fin (n + 2)) ℂ)).val : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)).trace = 0) ∧
        (V⁻¹ * Uu : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val ∈
          (expAmbientPartialHomeo (n + 2)).target)
    (h_length_polylog : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
      (ε : ℝ), 0 < ε → ε ≤ ε₀_sud (n + 2) →
      ((h_eq ▸ skApproxC_generic_sud gs
          (fun U => findNearestInCover_SUd gs h_dense (ε₀_sud (n + 2))
            (ε₀_sud_pos (d := n + 2) (by omega)) U)
          (expIsud_det_eq_one_predicate_holds n)
          (skLevel_polylog_sud (K_compose_sud (n + 2)) ε) U : FreeGroup α).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq := by
  have hε₀_pos : 0 < ε₀_sud (n + 2) := ε₀_sud_pos (by omega)
  have h_baseFinder : BaseFinder_approximates_within_sud gs
      (fun U => findNearestInCover_SUd gs h_dense (ε₀_sud (n + 2)) hε₀_pos U)
      (2 * ε₀_sud (n + 2)) := by
    intro U
    exact lt_of_lt_of_le
      (findNearestInCover_SUd_approx_opNorm gs h_dense (ε₀_sud (n + 2)) hε₀_pos U)
      (by linarith [hε₀_pos])
  have h_bound := SkApproxCSuperQuadraticBound_generic_sud_holds gs
    (fun U => findNearestInCover_SUd gs h_dense (ε₀_sud (n + 2)) hε₀_pos U)
    (expIsud_det_eq_one_predicate_holds n) h_baseFinder h_regime
  exact skHeadline_FreeGroup_SUd_cascade_final (K_compose_sud (n + 2)) (ε₀_sud (n + 2)) c
    (K_compose_sud_pos (d := n + 2) (by omega))
    (le_trans (by norm_num) (K_compose_sud_ge_1024 (d := n + 2) (by omega)))
    hε₀_pos hc_pos
    (K_compose_sud_calibration_le (d := n + 2) (by omega)) gs h_eq h_dense wordLength h_wl
    h_bound h_length_polylog

end SKEFTHawking.FKLW.GenericSUd
