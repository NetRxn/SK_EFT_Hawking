/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.6 — concrete word-length polylog conjunct + headline-from-density

Composes the UNCONDITIONAL length-asymptotic discharge (`skLengthPolylogBound_sud_holds`,
2026-05-28) with the concrete-recursion closed-form length bound S141
(`skApproxC_generic_sud_concrete_length_le_skLength_sud_param`) and the constructive-ε-net
base-finder length bound S55 (`findNearestInCover_SUd_baseFinder_length_bounded`) to discharge
the **F#4 word-length conjunct** `h_length_polylog` required by the concrete headline cascade
`skHeadline_FreeGroup_SUd_cascade_B_discharged_concrete` (S140).

The net effect: the SU(d) Solovay-Kitaev headline `SolovayKitaevHeadline_FreeGroup_SUd` now
reduces to **(D) density witness + a FreeGroup word-length bundle + one numeric constant choice**
— the F#4 length conjunct is fully discharged here, leaving only the (D) density witness as the
remaining substantive ingredient.

## Substantive content shipped

  * `concrete_length_polylog_holds` — discharges the cascade's `h_length_polylog` from the
    word-length bundle + the chosen headline constant `c ≥ 5·N₀` (composes S141 ∘ asymptotic
    ∘ S55).
  * `skHeadline_FreeGroup_SUd_from_density` — the SU(d) headline from **(D) density witness +
    word-length bundle**, with the F#4 length conjunct and the (B) bound discharged internally.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Wave 1" remaining item (a): compose the discharged asymptotic with S141 →
concrete `h_length_polylog`; reduce the headline to the (D) density witness. 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascadeConcrete
import SKEFTHawking.FKLW.GenericSUdSkApproxCConcreteLength
import SKEFTHawking.FKLW.GenericSUdSkLengthPolylogDischarge
import SKEFTHawking.FKLW.GenericSUdBaseFinderLengthBound

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Discharge of the cascade's `h_length_polylog`** (F#4 word-length conjunct).

For the constructive-ε-net base finder `findNearestInCover_SUd` at `ε₀_sud (n+2)`, the concrete
recursion's level-`skLevel_polylog_sud (K_compose_sud (n+2)) ε` output word length is bounded by
`c · (log(1/ε))^(log 5/log(3/2))`, provided `c` dominates `5·N₀` where `N₀` is the cover's max
word length. Composes S141 (closed-form `≤ skLength_sud N₀ 0 level`) ∘ `skLengthPolylogBound_sud_holds`
(asymptotic `skLength_sud N₀ 0 level ≤ c·(log(1/ε))^exp`). -/
theorem concrete_length_polylog_holds
    {n : ℕ} {α : Type} [DecidableEq α] [Nonempty (Fin (n + 2))]
    (gs : GeneratingSet (n + 2)) (h_eq : gs.W = FreeGroup α)
    (h_dense : IsDenseInSUd_gs gs)
    (h_wl : WordLengthFreeGroupLike gs (fun w => (h_eq ▸ w : FreeGroup α).toWord.length))
    (c : ℝ)
    (hc : 5 * ((maxWordLengthInCover_sud (fun w => (h_eq ▸ w : FreeGroup α).toWord.length)
          (constructiveEpsilonCover_SUd gs h_dense (ε₀_sud (n + 2))
            (ε₀_sud_pos (by omega))) : ℕ) : ℝ) ≤ c)
    (U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀_sud (n + 2)) :
    ((h_eq ▸ skApproxC_generic_sud_concrete gs
        (fun U => findNearestInCover_SUd gs h_dense (ε₀_sud (n + 2))
          (ε₀_sud_pos (by omega)) U)
        (expIsud_det_eq_one_predicate_holds n)
        (skLevel_polylog_sud (K_compose_sud (n + 2)) ε) U : FreeGroup α).toWord.length : ℝ) ≤
      c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2)) := by
  set wordLength : gs.W → ℕ := fun w => (h_eq ▸ w : FreeGroup α).toWord.length with hwl_def
  set hε₀_pos := ε₀_sud_pos (d := n + 2) (by omega) with hε₀_def
  set baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ) → gs.W :=
    fun U => findNearestInCover_SUd gs h_dense (ε₀_sud (n + 2)) hε₀_pos U with hbf_def
  set N₀ : ℝ := ((maxWordLengthInCover_sud wordLength
    (constructiveEpsilonCover_SUd gs h_dense (ε₀_sud (n + 2)) hε₀_pos) : ℕ) : ℝ) with hN₀_def
  have hN₀_nn : 0 ≤ N₀ := by rw [hN₀_def]; positivity
  -- base finder length bound (S55)
  have h_bf : BaseFinder_length_bounded_sud_param N₀ wordLength baseFinder := by
    rw [hN₀_def, hbf_def]
    exact findNearestInCover_SUd_baseFinder_length_bounded gs h_dense wordLength
      (ε₀_sud (n + 2)) hε₀_pos
  -- closed-form length bound (S141)
  have h_len := skApproxC_generic_sud_concrete_length_le_skLength_sud_param gs wordLength h_wl
    baseFinder (expIsud_det_eq_one_predicate_holds n) N₀ hN₀_nn h_bf
    (skLevel_polylog_sud (K_compose_sud (n + 2)) ε) U
  -- polylog asymptotic (2026-05-28 discharge), baseCase = N₀, decompCost = 0
  have hK_sq : 1 ≤ (K_compose_sud (n + 2)) ^ 2 := by
    have h1024 : (1024 : ℝ) ≤ K_compose_sud (n + 2) := K_compose_sud_ge_1024 (by omega)
    nlinarith [h1024]
  have hcal : (K_compose_sud (n + 2)) ^ 2 * (2 * ε₀_sud (n + 2)) ≤ 1 / 4 :=
    K_compose_sud_calibration_le (by omega)
  have hc' : 5 * (N₀ + 0 / 4) ≤ c := by
    have : N₀ + 0 / 4 = N₀ := by ring
    rw [this]; rw [hN₀_def] at hc ⊢; exact hc
  have h_asymp := skLengthPolylogBound_sud_holds N₀ 0 (ε₀_sud (n + 2))
    (K_compose_sud (n + 2)) c hN₀_nn le_rfl hK_sq hcal hc' ε hε_pos hε_le
  -- chain: wordLength(level) ≤ skLength_sud N₀ 0 level ≤ c·(log(1/ε))^exp
  have h_chain : (wordLength (skApproxC_generic_sud_concrete gs baseFinder
      (expIsud_det_eq_one_predicate_holds n)
      (skLevel_polylog_sud (K_compose_sud (n + 2)) ε) U) : ℝ) ≤
      c * (Real.log (1 / ε)) ^ skLengthExponent_sud :=
    le_trans h_len h_asymp
  -- the goal's LHS is `(wordLength (...) : ℝ)` by def; exponent literal is `skLengthExponent_sud` by def
  simpa only [hwl_def, hbf_def, skLengthExponent_sud] using h_chain

/-- **SU(d) Solovay-Kitaev headline from the (D) density witness** (+ word-length bundle).

Combines `concrete_length_polylog_holds` (F#4 length conjunct, discharged) with the concrete
cascade `skHeadline_FreeGroup_SUd_cascade_B_discharged_concrete` (S140, (B) discharged internally).
The headline now follows from **(D) density witness + a FreeGroup word-length bundle + `c ≥ 5·N₀`**
— no regime, no (B), no separate length hypothesis. The sole remaining substantive ingredient for
the per-alphabet UNCONDITIONAL headlines is the (D) density witness itself. -/
theorem skHeadline_FreeGroup_SUd_from_density
    {n : ℕ} {α : Type} [DecidableEq α] [Nonempty (Fin (n + 2))]
    (gs : GeneratingSet (n + 2)) (h_eq : gs.W = FreeGroup α)
    (h_dense : IsDenseInSUd_gs gs)
    (h_wl : WordLengthFreeGroupLike gs (fun w => (h_eq ▸ w : FreeGroup α).toWord.length))
    (c : ℝ) (hc_pos : 0 < c)
    (hc : 5 * ((maxWordLengthInCover_sud (fun w => (h_eq ▸ w : FreeGroup α).toWord.length)
          (constructiveEpsilonCover_SUd gs h_dense (ε₀_sud (n + 2))
            (ε₀_sud_pos (by omega))) : ℕ) : ℝ) ≤ c) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq :=
  skHeadline_FreeGroup_SUd_cascade_B_discharged_concrete c hc_pos gs h_eq h_dense
    (fun U ε hε_pos hε_le => concrete_length_polylog_holds gs h_eq h_dense h_wl c hc U ε hε_pos hε_le)

end SKEFTHawking.FKLW.GenericSUd
