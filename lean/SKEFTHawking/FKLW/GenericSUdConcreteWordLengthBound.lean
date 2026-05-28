/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) concrete word-length bound substrate (PARAMETRIC)

The **SU(d) generalization of Phase 6x Track M.4's
`GenericConcreteWordLengthBound`** — adds the closed-form
induction-friendly skLength_sud recurrence to iterate the per-step
concrete word-length recurrence at the SU(d) SK recursion.

To avoid the `gs.W = FreeGroup α` cast complications, this module is
parametric in an abstract `wordLength : gs.W → ℕ` function satisfying:
  * `wordLength_mul_le : ∀ w₁ w₂, wordLength (w₁ * w₂) ≤ wordLength w₁ + wordLength w₂`
  * `wordLength_inv_eq : ∀ w, wordLength w⁻¹ = wordLength w`

Per-alphabet specializations instantiate `wordLength` as
`FreeGroup.toWord.length` via the `gs.W = FreeGroup α` equality.

## Headline theorems (this file)

  * `BaseFinder_length_bounded_sud_param N₀ wordLength bf` — per-alphabet
    length-bounded base-finder predicate at SU(n+2).
  * `skApproxC_generic_sud_length_succ_param` — per-step length recurrence
    parametric in `wordLength`.
  * `skApproxC_generic_sud_length_le_skLength_sud_param` — strong induction
    bound: level-n SU(d) Dawson-Nielsen output word length ≤
    `skLength_sud N₀ 0 n`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — length-bound recursion
discharge (substantive content for 4th of 4 ingredients per Session 47
cascade index).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkLength
import SKEFTHawking.FKLW.GenericSUdSkApproxC
import SKEFTHawking.FKLW.GenericSUdExpIsuDUnconditional

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Length-bounded base-finder predicate (parametric) -/

/-- **Length-bounded SU(d) base-finder predicate** (parametric in word
length function).

For any `wordLength : gs.W → ℕ` and any base finder, asserts that the
output word length is bounded by a constant `N₀`. -/
def BaseFinder_length_bounded_sud_param {n : ℕ}
    (N₀ : ℝ) {gs : GeneratingSet (n + 2)}
    (wordLength : gs.W → ℕ)
    (bf : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ) → gs.W) : Prop :=
  ∀ U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ),
    (wordLength (bf U) : ℝ) ≤ N₀

/-! ## 2. Word-length submultiplicativity hypotheses -/

/-- **Word-length submultiplicativity + inverse invariance hypothesis
bundle**. Captures the two FreeGroup-style properties needed for the
per-step length recurrence:
  * `wordLength_mul_le : wordLength (w₁ * w₂) ≤ wordLength w₁ + wordLength w₂`
  * `wordLength_inv_eq : wordLength w⁻¹ = wordLength w` -/
structure WordLengthFreeGroupLike {n : ℕ} (gs : GeneratingSet (n + 2))
    (wordLength : gs.W → ℕ) where
  /-- Submultiplicativity of word length. -/
  mul_le : ∀ w₁ w₂ : gs.W, wordLength (w₁ * w₂) ≤ wordLength w₁ + wordLength w₂
  /-- Inverse-invariance of word length. -/
  inv_eq : ∀ w : gs.W, wordLength w⁻¹ = wordLength w

/-! ## 3. Per-step length recurrence (parametric) -/

/-- **Per-step length recurrence at any SU(d) GeneratingSet with
submultiplicative wordLength**.

For any SU(n+2) GeneratingSet `gs` with a wordLength function satisfying
FreeGroup-style submultiplicativity + inverse invariance, the level-`(n_lvl+1)`
Dawson-Nielsen output has wordLength bounded by
`length(at U) + 2·length(at A_F) + 2·length(at A_G)`. -/
theorem skApproxC_generic_sud_length_succ_param
    {n : ℕ}
    (gs : GeneratingSet (n + 2))
    (wordLength : gs.W → ℕ)
    (h_wl : WordLengthFreeGroupLike gs wordLength)
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (n + 2))
    (n_lvl : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    let V_n_word := skApproxC_generic_sud gs baseFinder h_det_pred n_lvl U
    let data := dnStepFG_sud (gs.ρ_hom V_n_word) U
    let A_F := expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr
    let A_G := expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr
    wordLength (skApproxC_generic_sud gs baseFinder h_det_pred (n_lvl + 1) U) ≤
      wordLength (skApproxC_generic_sud gs baseFinder h_det_pred n_lvl U)
      + 2 * wordLength (skApproxC_generic_sud gs baseFinder h_det_pred n_lvl A_F)
      + 2 * wordLength (skApproxC_generic_sud gs baseFinder h_det_pred n_lvl A_G) := by
  simp only
  have h_succ := skApproxC_generic_sud_succ gs baseFinder h_det_pred n_lvl U
  set V := skApproxC_generic_sud gs baseFinder h_det_pred n_lvl U with hV_def
  set data_local := dnStepFG_sud (gs.ρ_hom V) U with hdata_def
  set A_F_local :=
    expIsud_of_det_predicate h_det_pred data_local.F data_local.hF_herm
      data_local.hF_tr with hA_F_def
  set A_G_local :=
    expIsud_of_det_predicate h_det_pred data_local.G data_local.hG_herm
      data_local.hG_tr with hA_G_def
  set wF := skApproxC_generic_sud gs baseFinder h_det_pred n_lvl A_F_local
    with hwF_def
  set wG := skApproxC_generic_sud gs baseFinder h_det_pred n_lvl A_G_local
    with hwG_def
  have h_eq_recurrence : skApproxC_generic_sud gs baseFinder h_det_pred (n_lvl + 1) U
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

/-! ## 4. Strong induction bound (parametric) -/

/-- **Closed-form length bound at SU(d)** (parametric in wordLength + N₀).

For any SU(n+2) GeneratingSet, submultiplicative wordLength, base finder
satisfying `BaseFinder_length_bounded_sud_param N₀ wordLength bf`, and
any level n_lvl + target U, the level-`n_lvl` Dawson-Nielsen output's
wordLength is bounded by `skLength_sud N₀ 0 n_lvl`.

Proof: strong induction on n_lvl. Base via `BaseFinder_length_bounded_sud_param`
+ `skLength_sud_zero`. Step via `skApproxC_generic_sud_length_succ_param`
+ induction hypothesis + `skLength_sud_succ`. -/
theorem skApproxC_generic_sud_length_le_skLength_sud_param
    {n : ℕ}
    (gs : GeneratingSet (n + 2))
    (wordLength : gs.W → ℕ)
    (h_wl : WordLengthFreeGroupLike gs wordLength)
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (n + 2))
    (N₀ : ℝ) (hN₀_nn : 0 ≤ N₀)
    (h_bf_length : BaseFinder_length_bounded_sud_param N₀ wordLength baseFinder)
    (n_lvl : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    (wordLength (skApproxC_generic_sud gs baseFinder h_det_pred n_lvl U) : ℝ) ≤
      skLength_sud N₀ 0 n_lvl := by
  induction n_lvl generalizing U with
  | zero =>
    have h_zero := skApproxC_generic_sud_zero gs baseFinder h_det_pred U
    rw [h_zero, skLength_sud_zero]
    exact h_bf_length U
  | succ n_lvl ih =>
    have h_step := skApproxC_generic_sud_length_succ_param gs wordLength h_wl
      baseFinder h_det_pred n_lvl U
    set data_local := dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder
      h_det_pred n_lvl U)) U with hdata_def
    set A_F_local :=
      expIsud_of_det_predicate h_det_pred data_local.F data_local.hF_herm
        data_local.hF_tr with hA_F_def
    set A_G_local :=
      expIsud_of_det_predicate h_det_pred data_local.G data_local.hG_herm
        data_local.hG_tr with hA_G_def
    have h_ih_U : (wordLength (skApproxC_generic_sud gs baseFinder h_det_pred n_lvl U) : ℝ) ≤
        skLength_sud N₀ 0 n_lvl := ih U
    have h_ih_F : (wordLength (skApproxC_generic_sud gs baseFinder h_det_pred n_lvl A_F_local) : ℝ) ≤
        skLength_sud N₀ 0 n_lvl := ih A_F_local
    have h_ih_G : (wordLength (skApproxC_generic_sud gs baseFinder h_det_pred n_lvl A_G_local) : ℝ) ≤
        skLength_sud N₀ 0 n_lvl := ih A_G_local
    have h_step_R : (wordLength (skApproxC_generic_sud gs baseFinder
        h_det_pred (n_lvl + 1) U) : ℝ) ≤
        (wordLength (skApproxC_generic_sud gs baseFinder h_det_pred n_lvl U) : ℝ)
        + 2 * (wordLength (skApproxC_generic_sud gs baseFinder h_det_pred n_lvl A_F_local) : ℝ)
        + 2 * (wordLength (skApproxC_generic_sud gs baseFinder h_det_pred n_lvl A_G_local) : ℝ) := by
      exact_mod_cast h_step
    have h_succ_recurrence : skLength_sud N₀ 0 (n_lvl + 1) =
        5 * skLength_sud N₀ 0 n_lvl + 0 := skLength_sud_succ N₀ 0 n_lvl
    linarith

end SKEFTHawking.FKLW.GenericSUd
