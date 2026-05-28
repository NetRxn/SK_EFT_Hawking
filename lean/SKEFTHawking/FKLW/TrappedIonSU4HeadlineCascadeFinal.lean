/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.5 — SU(4) trapped-ion CASCADE-FINAL headline discharge

Per-alphabet instantiation of Session 56's `skHeadline_FreeGroup_SUd_cascade_final`
at SU(4) trapped-ion. Discharges `trappedIonSU4FullHeadline` (the F#4-compliant
T-A1′.5 headline) given ONLY 2 substantive ingredients + calibration:

  * **(D)** `h_dense : IsDenseInSUd_gs (trappedIonGeneratingSetSU4 N hN)`
    (T-X′.2 PROPER substantive — Brylinski-Brylinski 2002 entangler
    universality at SU(4))
  * **(B)** `h_bound` — super-quad bound discharge at SU(4)

All other substantive content (det predicate, polylog level spec,
length-bound recursion, baseFinder length boundedness, polylog level
chooser) is composed internally via Sessions 41-56 substrate.

## Substantive content shipped

  * `trappedIonSU4FullHeadline_via_cascade_final` — per-alphabet
    instantiation discharge of T-A1′.5 headline.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.5 PROPER — F#4-compliant
headline cascade unblock given remaining 2 substantive ingredients.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascade2IngredientFinal
import SKEFTHawking.FKLW.GenericSUdLengthBoundPerAlphabet
import SKEFTHawking.FKLW.TrappedIonSU4FullHeadlineForm
import SKEFTHawking.FKLW.TrappedIonGeneratingSetSU4Full

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## T-A1′.5 cascade-final per-alphabet headline discharge -/

/-- **T-A1′.5 PROPER cascade-final headline discharge** at SU(4) trapped-ion.

Discharges `trappedIonSU4FullHeadline N hN` (the F#4-compliant
trapped-ion SU(4) Solovay-Kitaev headline) given ONLY:
  * (D) Density witness for `trappedIonGeneratingSetSU4`
  * (B) Super-quad bound discharge at SU(4)
  * Calibration constants + boundedness

All cascade composition (det predicate, polylog level spec, length-bound
recursion, baseFinder length boundedness, polylog level chooser) is
internal via Phase 6y Sessions 41-56 substrate.

For (D), the Phase 6y T-X′.2 PROPER substantive ship is needed
(Brylinski-Brylinski 2002 entangler universality at SU(4)).
For (B), the SU(d) super-quad bound discharge analog is needed (Phase 6u
Wave 4b SU(2) analog, mechanically liftable per Explore-agent intel). -/
theorem trappedIonSU4FullHeadline_via_cascade_final
    (N : ℕ) (hN : 0 < N)
    (K ε₀_sud c : ℝ)
    (hK_pos : 0 < K) (hK_ge_one : 1 ≤ K)
    (hε₀_pos : 0 < ε₀_sud)
    (hc_pos : 0 < c)
    (h_cal : K^2 * (2 * ε₀_sud) ≤ 1 / 4)
    (h_dense : SKEFTHawking.FKLW.GenericSUd.IsDenseInSUd_gs
      (trappedIonGeneratingSetSU4 N hN))
    (h_bound : SKEFTHawking.FKLW.GenericSUd.SkApproxCSuperQuadraticBound_generic_sud
      K ε₀_sud (trappedIonGeneratingSetSU4 N hN)
      (fun U => SKEFTHawking.FKLW.GenericSUd.findNearestInCover_SUd
        (trappedIonGeneratingSetSU4 N hN) h_dense ε₀_sud hε₀_pos U)
      (SKEFTHawking.FKLW.GenericSUd.expIsud_det_eq_one_predicate_holds 2))
    (h_length_polylog : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ))
      (ε : ℝ), 0 < ε → ε ≤ ε₀_sud →
      ((trappedIonGeneratingSetSU4_W N hN ▸
          SKEFTHawking.FKLW.GenericSUd.skApproxC_generic_sud
            (trappedIonGeneratingSetSU4 N hN)
            (fun U => SKEFTHawking.FKLW.GenericSUd.findNearestInCover_SUd
              (trappedIonGeneratingSetSU4 N hN) h_dense ε₀_sud hε₀_pos U)
            (SKEFTHawking.FKLW.GenericSUd.expIsud_det_eq_one_predicate_holds 2)
            (SKEFTHawking.FKLW.GenericSUd.skLevel_polylog_sud K ε) U
          : FreeGroup (Fin (4 + 2 * N))).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log 2))
    -- WordLength bundle hypothesis (auto-discharged via FreeGroup substrate)
    (h_wl : SKEFTHawking.FKLW.GenericSUd.WordLengthFreeGroupLike
      (trappedIonGeneratingSetSU4 N hN)
      (SKEFTHawking.FKLW.GenericSUd.freeGroup_wordLength_su4 N hN)) :
    trappedIonSU4FullHeadline N hN := by
  -- Apply Session 56's end-to-end cascade.
  have h_headline := SKEFTHawking.FKLW.GenericSUd.skHeadline_FreeGroup_SUd_cascade_final
    (n := 2) (α := Fin (4 + 2 * N)) K ε₀_sud c
    hK_pos hK_ge_one hε₀_pos hc_pos h_cal
    (trappedIonGeneratingSetSU4 N hN) (trappedIonGeneratingSetSU4_W N hN)
    h_dense
    (SKEFTHawking.FKLW.GenericSUd.freeGroup_wordLength_su4 N hN)
    h_wl
    h_bound
    h_length_polylog
  -- Convert from SolovayKitaevHeadline_FreeGroup_SUd gs h_eq to
  -- trappedIonSU4FullHeadline N hN. The two have the same content
  -- (existential over ε₀, c, compile with error + length bounds).
  obtain ⟨ε₀, c', compile, hε₀_pos', hc'_pos, h_main⟩ := h_headline
  refine ⟨ε₀, c', fun U ε =>
    trappedIonGeneratingSetSU4_W N hN ▸ compile U ε, hε₀_pos', hc'_pos, ?_⟩
  intro U ε hε_pos hε_le
  obtain ⟨h_err, h_len⟩ := h_main U ε hε_pos hε_le
  refine ⟨?_, ?_⟩
  · -- Error bound: convert via the W equality.
    convert h_err using 2
  · -- Length bound.
    convert h_len using 2

end SKEFTHawking.FKLW.TrappedIonSU4
