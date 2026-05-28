/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — concrete-recursion word-length bound (re-point R4, length ingredient)

The word-length bound for the **concrete** SK recursion `skApproxC_generic_sud_concrete` (S133),
mirroring the IFT `GenericSUdConcreteWordLengthBound.lean` (S53). The word length is
**log-independent**: it depends only on the recursion's group-word shape
(`V_n · A_F A_G A_F⁻¹ A_G⁻¹`), which is identical between `skApproxC_generic_sud` and
`skApproxC_generic_sud_concrete` — so the same per-step recurrence + strong-induction closed-form
bound (`skLength_sud`, log-agnostic) transfer verbatim with the recursion swapped. The
submultiplicative `WordLengthFreeGroupLike` bundle and the length-bounded base-finder predicate
`BaseFinder_length_bounded_sud_param` are reused as-is from S53.

This is the **word-length-polylog ingredient** for the UNCONDITIONAL concrete headline cascade
`skHeadline_FreeGroup_SUd_cascade_B_discharged_concrete` (S140): composed with the polylog
asymptotic of `skLength_sud` at the polylog level chooser, it discharges the F#4 word-length
conjunct.

## Substantive content shipped

  * `skApproxC_generic_sud_concrete_length_succ_param` — per-step length recurrence
    (`≤ length(U) + 2·length(A_F) + 2·length(A_G)`).
  * `skApproxC_generic_sud_concrete_length_le_skLength_sud_param` — strong-induction closed-form
    bound (`≤ skLength_sud N₀ 0 n`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R4: concrete-recursion word-length
bound (length ingredient for the UNCONDITIONAL headline).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkLength
import SKEFTHawking.FKLW.GenericSUdSkApproxCConcrete
import SKEFTHawking.FKLW.GenericSUdConcreteWordLengthBound

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Per-step length recurrence for the concrete recursion** (parametric in `wordLength`).
Concrete counterpart of `skApproxC_generic_sud_length_succ_param` (S53): the level-`(n_lvl+1)`
output word length is `≤ length(at U) + 2·length(at A_F) + 2·length(at A_G)`, via the concrete
recursion's `succ` unfolding + `wordLength` submultiplicativity / inverse invariance. -/
theorem skApproxC_generic_sud_concrete_length_succ_param
    {n : ℕ}
    (gs : GeneratingSet (n + 2))
    (wordLength : gs.W → ℕ)
    (h_wl : WordLengthFreeGroupLike gs wordLength)
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (n + 2))
    (n_lvl : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    let V_n_word := skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl U
    let data := dnStepFG_sud_concrete (gs.ρ_hom V_n_word) U
    let A_F := expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr
    let A_G := expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr
    wordLength (skApproxC_generic_sud_concrete gs baseFinder h_det_pred (n_lvl + 1) U) ≤
      wordLength (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl U)
      + 2 * wordLength (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl A_F)
      + 2 * wordLength (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl A_G) := by
  simp only
  have h_succ := skApproxC_generic_sud_concrete_succ gs baseFinder h_det_pred n_lvl U
  set V := skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl U with hV_def
  set data_local := dnStepFG_sud_concrete (gs.ρ_hom V) U with hdata_def
  set A_F_local :=
    expIsud_of_det_predicate h_det_pred data_local.F data_local.hF_herm
      data_local.hF_tr with hA_F_def
  set A_G_local :=
    expIsud_of_det_predicate h_det_pred data_local.G data_local.hG_herm
      data_local.hG_tr with hA_G_def
  set wF := skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl A_F_local
    with hwF_def
  set wG := skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl A_G_local
    with hwG_def
  have h_eq_recurrence : skApproxC_generic_sud_concrete gs baseFinder h_det_pred (n_lvl + 1) U
      = V * (wF * wG * wF⁻¹ * wG⁻¹) := h_succ
  rw [h_eq_recurrence]
  have h_inv_F : wordLength wF⁻¹ = wordLength wF := h_wl.inv_eq wF
  have h_inv_G : wordLength wG⁻¹ = wordLength wG := h_wl.inv_eq wG
  have h1 : wordLength (wF * wG) ≤ wordLength wF + wordLength wG :=
    h_wl.mul_le wF wG
  have h2 : wordLength (wF * wG * wF⁻¹) ≤
      wordLength (wF * wG) + wordLength wF⁻¹ := h_wl.mul_le _ _
  have h3 : wordLength (wF * wG * wF⁻¹ * wG⁻¹) ≤
      wordLength (wF * wG * wF⁻¹) + wordLength wG⁻¹ := h_wl.mul_le _ _
  have h4 : wordLength (V * (wF * wG * wF⁻¹ * wG⁻¹)) ≤
      wordLength V + wordLength (wF * wG * wF⁻¹ * wG⁻¹) := h_wl.mul_le _ _
  omega

/-- **Closed-form length bound for the concrete recursion** (parametric). Concrete counterpart
of `skApproxC_generic_sud_length_le_skLength_sud_param` (S53): for a length-bounded base finder,
the level-`n_lvl` concrete output word length is `≤ skLength_sud N₀ 0 n_lvl`. Strong induction:
base via `BaseFinder_length_bounded_sud_param` + `skLength_sud_zero`; step via the concrete
per-step recurrence + IH + `skLength_sud_succ`. -/
theorem skApproxC_generic_sud_concrete_length_le_skLength_sud_param
    {n : ℕ}
    (gs : GeneratingSet (n + 2))
    (wordLength : gs.W → ℕ)
    (h_wl : WordLengthFreeGroupLike gs wordLength)
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (n + 2))
    (N₀ : ℝ) (_hN₀_nn : 0 ≤ N₀)
    (h_bf_length : BaseFinder_length_bounded_sud_param N₀ wordLength baseFinder)
    (n_lvl : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    (wordLength (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl U) : ℝ) ≤
      skLength_sud N₀ 0 n_lvl := by
  induction n_lvl generalizing U with
  | zero =>
    have h_zero := skApproxC_generic_sud_concrete_zero gs baseFinder h_det_pred U
    rw [h_zero, skLength_sud_zero]
    exact h_bf_length U
  | succ n_lvl ih =>
    have h_step := skApproxC_generic_sud_concrete_length_succ_param gs wordLength h_wl
      baseFinder h_det_pred n_lvl U
    set data_local := dnStepFG_sud_concrete (gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder
      h_det_pred n_lvl U)) U with hdata_def
    set A_F_local :=
      expIsud_of_det_predicate h_det_pred data_local.F data_local.hF_herm
        data_local.hF_tr with hA_F_def
    set A_G_local :=
      expIsud_of_det_predicate h_det_pred data_local.G data_local.hG_herm
        data_local.hG_tr with hA_G_def
    have h_ih_U : (wordLength (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl U) : ℝ) ≤
        skLength_sud N₀ 0 n_lvl := ih U
    have h_ih_F : (wordLength (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl A_F_local) : ℝ) ≤
        skLength_sud N₀ 0 n_lvl := ih A_F_local
    have h_ih_G : (wordLength (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl A_G_local) : ℝ) ≤
        skLength_sud N₀ 0 n_lvl := ih A_G_local
    have h_step_R : (wordLength (skApproxC_generic_sud_concrete gs baseFinder
        h_det_pred (n_lvl + 1) U) : ℝ) ≤
        (wordLength (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl U) : ℝ)
        + 2 * (wordLength (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl A_F_local) : ℝ)
        + 2 * (wordLength (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n_lvl A_G_local) : ℝ) := by
      exact_mod_cast h_step
    have h_succ_recurrence : skLength_sud N₀ 0 (n_lvl + 1) =
        5 * skLength_sud N₀ 0 n_lvl + 0 := skLength_sud_succ N₀ 0 n_lvl
    linarith

end SKEFTHawking.FKLW.GenericSUd
