/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.5 — SU(8) Clifford+CCZ CASCADE-FINAL headline discharge

Per-alphabet instantiation of Session 56's `skHeadline_FreeGroup_SUd_cascade_final`
at SU(8) Clifford+CCZ. Mirror of Session 57 at SU(4) trapped-ion.

Discharges `cliffordCCZSU8Headline` (the F#4-compliant T-A2′.5 headline)
given ONLY 2 substantive ingredients + calibration:

  * **(D)** `h_dense : IsDenseInSUd_gs cliffordCCZGeneratingSetSU8`
    (T-X′.2 PROPER — Aaronson-Gottesman 2004 lineage)
  * **(B)** `h_bound` — super-quad bound discharge at SU(8)

All other substantive content composed internally via Sessions 41-56.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.5 PROPER —
F#4-compliant headline cascade unblock.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascade2IngredientFinal
import SKEFTHawking.FKLW.GenericSUdLengthBoundPerAlphabet
import SKEFTHawking.FKLW.CliffordCCZSU8HeadlineForm
import SKEFTHawking.FKLW.CliffordCCZSU8HeadlineDischarge
import SKEFTHawking.FKLW.CliffordCCZGeneratingSetSU8Full

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## T-A2′.5 cascade-final per-alphabet headline discharge -/

/-- **T-A2′.5 PROPER cascade-final headline discharge** at SU(8) Clifford+CCZ.

Discharges `cliffordCCZSU8Headline` (the F#4-compliant Clifford+CCZ SU(8)
Solovay-Kitaev headline) given ONLY:
  * (D) Density witness for `cliffordCCZGeneratingSetSU8`
  * (B) Super-quad bound discharge at SU(8)
  * Calibration constants + boundedness

For (D), Phase 6y T-X′.2 PROPER substantive ship needed (Aaronson-Gottesman
2004 lineage). For (B), SU(d) super-quad bound discharge analog needed. -/
theorem cliffordCCZSU8Headline_via_cascade_final
    (K ε₀_sud c : ℝ)
    (hK_pos : 0 < K) (hK_ge_one : 1 ≤ K)
    (hε₀_pos : 0 < ε₀_sud)
    (hc_pos : 0 < c)
    (h_cal : K^2 * (2 * ε₀_sud) ≤ 1 / 4)
    (h_dense : SKEFTHawking.FKLW.GenericSUd.IsDenseInSUd_gs
      cliffordCCZGeneratingSetSU8)
    (h_bound : SKEFTHawking.FKLW.GenericSUd.SkApproxCSuperQuadraticBound_generic_sud
      K ε₀_sud cliffordCCZGeneratingSetSU8
      (fun U => SKEFTHawking.FKLW.GenericSUd.findNearestInCover_SUd
        cliffordCCZGeneratingSetSU8 h_dense ε₀_sud hε₀_pos U)
      (SKEFTHawking.FKLW.GenericSUd.expIsud_det_eq_one_predicate_holds 6))
    (h_length_polylog : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ))
      (ε : ℝ), 0 < ε → ε ≤ ε₀_sud →
      ((cliffordCCZGeneratingSetSU8_W ▸
          SKEFTHawking.FKLW.GenericSUd.skApproxC_generic_sud
            cliffordCCZGeneratingSetSU8
            (fun U => SKEFTHawking.FKLW.GenericSUd.findNearestInCover_SUd
              cliffordCCZGeneratingSetSU8 h_dense ε₀_sud hε₀_pos U)
            (SKEFTHawking.FKLW.GenericSUd.expIsud_det_eq_one_predicate_holds 6)
            (SKEFTHawking.FKLW.GenericSUd.skLevel_polylog_sud K ε) U
          : FreeGroup (Fin 4)).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2)))
    (h_wl : SKEFTHawking.FKLW.GenericSUd.WordLengthFreeGroupLike
      cliffordCCZGeneratingSetSU8
      SKEFTHawking.FKLW.GenericSUd.freeGroup_wordLength_su8) :
    cliffordCCZSU8Headline := by
  have h_headline := SKEFTHawking.FKLW.GenericSUd.skHeadline_FreeGroup_SUd_cascade_final
    (n := 6) (α := Fin 4) K ε₀_sud c
    hK_pos hK_ge_one hε₀_pos hc_pos h_cal
    cliffordCCZGeneratingSetSU8 cliffordCCZGeneratingSetSU8_W
    h_dense
    SKEFTHawking.FKLW.GenericSUd.freeGroup_wordLength_su8
    h_wl
    h_bound
    h_length_polylog
  obtain ⟨ε₀, c', compile, hε₀_pos', hc'_pos, h_main⟩ := h_headline
  refine ⟨ε₀, c', fun U ε =>
    cliffordCCZGeneratingSetSU8_W ▸ compile U ε, hε₀_pos', hc'_pos, ?_⟩
  intro U ε hε_pos hε_le
  obtain ⟨h_err, h_len⟩ := h_main U ε hε_pos hε_le
  refine ⟨?_, ?_⟩
  · convert h_err using 2
  · convert h_len using 2

end SKEFTHawking.FKLW.CliffordCCZSU8
