/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) SK cascade INDEX (Sessions 41-46 substrate chain)

Single import point for the Phase 6y Track S SU(d) Solovay-Kitaev cascade
substrate (Sessions 41-46). Re-exports the key cascade theorems with
documented aliases + summarizes the 4 substantive ingredients
enumeration.

## The cascade substrate chain (Sessions 41-46)

  1. **Session 41** (`GenericSUdDnStepFG.lean`) — `dnStepFG_sud` per-step
     (F, G) extractor via the keystone Session 33.
  2. **Session 42** (`GenericSUdExpIsuD.lean`) — `expIsud_of_det_predicate`
     SU(d) matrix exp coercion conditional on the det predicate.
  3. **Session 43** (`GenericSUdSkApproxC.lean`) — `skApproxC_generic_sud`
     SK recursion engine at SU(d).
  4. **Session 44** (`GenericSUdSkApproxCBound.lean`) —
     `SkApproxCSuperQuadraticBound_generic_sud` super-quadratic bound
     predicate.
  5. **Session 45** (`GenericSUdSkHeadlineCascade.lean`) —
     `skHeadline_FreeGroup_SUd_cascade` F#4-compliant cascade composition
     into `SolovayKitaevHeadline_FreeGroup_SUd`.
  6. **Session 46** (`GenericSUdSkLevelPolylog.lean`) —
     `skLevel_polylog_sud` polylog-level chooser + `SkLevelPolylog_sud_spec`
     predicate.

## The 4 substantive ingredients (enumeration)

The SU(d) SK headline is reduced (via Session 45's cascade) to 4 named
substantive content items:

  1. **Det predicate discharge**: `ExpIsud_det_eq_one_predicate (m+2)` —
     analog of SU(2) ~2300-LoC `DetExpZeroOnSu2_SU2_discharged`. Substantive
     content: `det(exp(I·F)) = exp(I·trace F) = exp 0 = 1` for traceless F.
     Requires Mathlib's matrix-trace ↔ matrix-det exponential identity
     (`det(exp X) = exp(trace X)`), which is NOT currently shipped as a
     single named Mathlib lemma.

  2. **Super-quadratic bound discharge**:
     `SkApproxCSuperQuadraticBound_generic_sud K ε₀_sud gs baseFinder h_det_pred`
     — analog of SU(2) ~981-LoC `SkApproxCSuperQuadraticBound_generic_holds`.
     Substantive content: inductive bound on ‖ρ_hom (skApproxC_generic_sud
     n U) - U‖ at each level n.

  3. **Polylog level spec discharge**: `SkLevelPolylog_sud_spec K ε₀_sud` —
     analog of SU(2) ~110-LoC `skLevel_polylog_spec`. Substantive content:
     `ε_seq K (2·ε₀_sud) (skLevel_polylog_sud K ε) ≤ ε` for ε in valid range,
     conditional on calibration `K² · 2·ε₀_sud ≤ 1/4`.

  4. **Polylog word-length bound**: a `wordLength : gs.W → ℕ` function +
     polylog bound on `wordLength (skApproxC_generic_sud ... (skLevel_polylog_sud
     K ε) U) ≤ c · (log(1/ε))^(log 5 / log (3/2))`. Substantive content:
     recursive word-length tracking through the SK recursion.

## Per-alphabet instantiation (T-A1′.5 + T-A2′.5)

Once the 4 substantive ingredients ship, T-A1′.5 (SU(4) trapped-ion) and
T-A2′.5 (SU(8) Clifford+CCZ) F#4-compliant headlines discharge UNCONDITIONALLY
via:

  ```
  trappedIonSU4FullHeadline N hN :=
    trappedIonSU4FullHeadline_of_SKCompileWithBounds N hN
      (SKCompileWithBounds_FreeGroup.mk
        ε₀_sud_SU4 c_SU4 compile_via_skApproxC_generic_sud_at_SU4
        ε₀_sud_SU4_pos c_SU4_pos
        (error_bound_via_session_45_cascade)
        (length_bound_via_session_45_cascade))
  ```

i.e., per-alphabet `SKCompileWithBounds_FreeGroup` data is constructed
from Session 45's cascade applied at d = 4 (resp. d = 8) with the 4
substantive ingredients discharged.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — SU(d) SK cascade
substrate index (Sessions 41-46 navigation aid).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDnStepFG
import SKEFTHawking.FKLW.GenericSUdExpIsuD
import SKEFTHawking.FKLW.GenericSUdSkApproxC
import SKEFTHawking.FKLW.GenericSUdSkApproxCBound
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascade
import SKEFTHawking.FKLW.GenericSUdSkLevelPolylog

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## Documented aliases (Sessions 41-46 substrate) -/

/-- **Alias for Session 45 cascade**: the F#4-compliant SU(d) SK headline
discharge given the 4 substantive ingredients. Use this as the single
entry point for downstream per-alphabet headline cascade unblock. -/
theorem phase6y_S6_skHeadline_cascade_alias {m : ℕ} {α : Type} [DecidableEq α]
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
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq :=
  skHeadline_FreeGroup_SUd_cascade K ε₀_sud c hε₀_pos hc_pos gs h_eq
    baseFinder h_det_pred h_bound levelChooser h_level_spec h_length_bound

/-- **Alias for Session 46 polylog level chooser**: the canonical level
chooser using the SU(d) parametric K. Specialized at SU(4) and SU(8) for
T-A1′.5 / T-A2′.5 instantiation. -/
noncomputable def phase6y_S6_skLevel_polylog_alias (K ε : ℝ) : ℕ :=
  skLevel_polylog_sud K ε

end SKEFTHawking.FKLW.GenericSUd
