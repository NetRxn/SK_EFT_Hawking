/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) Solovay-Kitaev recursion `skApproxC_generic_sud`

The **SU(d) generalization of `skApproxC_generic`** (Phase 6u Wave 4
alphabet-agnostic SK recursion at SU(2)). Structurally identical to the
SU(2) version with replacements:
  * `dnStepFG_su2` → `dnStepFG_sud` (Phase 6y Session 41)
  * `expIsu2` → `expIsud_of_det_predicate h_det_pred` (Phase 6y Session 42)
  * `Fin 2` → `Fin (m + 2)` (parametric d = m + 2 ≥ 2)

## Construction

For a `GeneratingSet (m + 2)` `gs`, a `baseFinder : ↥SU(m+2) → gs.W`, and
a det-predicate discharge `h_det_pred : ExpIsud_det_eq_one_predicate (m+2)`:

  - Level 0: `baseFinder U`
  - Level (n+1): `V_n_word · groupCommutator (skApproxC_generic_sud n A_F)
    (skApproxC_generic_sud n A_G)` where:
      - `V_n_word := skApproxC_generic_sud gs baseFinder n U`
      - `V_n := gs.ρ_hom V_n_word ∈ SU(d)`
      - `step := dnStepFG_sud V_n U` (extracts (F, G) via the keystone
        Session 33)
      - `A_F := expIsud_of_det_predicate h_det_pred step.F ...`
      - `A_G := expIsud_of_det_predicate h_det_pred step.G ...`

The det-predicate `h_det_pred` is the substantive content for unconditional
SK at SU(d); decoupling it from the recursion's STRUCTURE lets this module
ship now and the substantive det discharge ship in follow-on sessions.

## Substantive content shipped

  * `skApproxC_generic_sud {m : ℕ} (gs : GeneratingSet (m + 2)) ...` — the
    SU(d) SK recursion.
  * `skApproxC_generic_sud_zero` — base-case unfolding.
  * `skApproxC_generic_sud_succ` — successor-case unfolding.
  * `BaseFinder_approximates_within_sud` — base-case ε₀-approximation predicate.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — SU(d) SK recursion lift
(structural recursion engine; substantive bounds + discharge ship in
follow-on sessions).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDnStepFG
import SKEFTHawking.FKLW.GenericSUdExpIsuD
import SKEFTHawking.FKLW.GenericSUdGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The SU(d) SK recursion -/

/-- **Generic constructive Dawson-Nielsen Solovay-Kitaev recursion at SU(d)**.

For every level `n` and target `U ∈ SU(m+2)`, returns a word in `gs.W`
constructed as a level-n Dawson-Nielsen composition.

  - Level 0: the base-case approximation via `baseFinder`.
  - Level (n+1): visible composition
    `V_n_word · (A_F_word · A_G_word · A_F_word⁻¹ · A_G_word⁻¹)`
    where (F, G) is the traceless balanced commutator decomposition of
    the residual matrix log (via `dnStepFG_sud`).

The SU(d) analog of `skApproxC_generic` (Phase 6u Wave 4, SU(2)). Takes
the det-predicate hypothesis `h_det_pred` as a parameter to decouple the
structural recursion from the substantive det = 1 discharge. -/
noncomputable def skApproxC_generic_sud {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2)) :
    ℕ → ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W
  | 0, U => baseFinder U
  | n + 1, U =>
    let V_n_word : gs.W := skApproxC_generic_sud gs baseFinder h_det_pred n U
    let V_n_SUd : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) :=
      gs.ρ_hom V_n_word
    let data : DNStepData_SUd (m + 2) := dnStepFG_sud V_n_SUd U
    let A_F : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) :=
      expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr
    let A_G : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) :=
      expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr
    let A_F_word : gs.W := skApproxC_generic_sud gs baseFinder h_det_pred n A_F
    let A_G_word : gs.W := skApproxC_generic_sud gs baseFinder h_det_pred n A_G
    V_n_word * (A_F_word * A_G_word * A_F_word⁻¹ * A_G_word⁻¹)

/-- Level-0 unfolding: base case is the supplied base finder. -/
lemma skApproxC_generic_sud_zero {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
    skApproxC_generic_sud gs baseFinder h_det_pred 0 U = baseFinder U := rfl

/-- Level-(n+1) unfolding: the visible Dawson-Nielsen composition. -/
lemma skApproxC_generic_sud_succ {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
    skApproxC_generic_sud gs baseFinder h_det_pred (n + 1) U =
      let V_n_word := skApproxC_generic_sud gs baseFinder h_det_pred n U
      let data := dnStepFG_sud (gs.ρ_hom V_n_word) U
      let A_F := expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr
      let A_G := expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr
      V_n_word *
        (skApproxC_generic_sud gs baseFinder h_det_pred n A_F *
          skApproxC_generic_sud gs baseFinder h_det_pred n A_G *
          (skApproxC_generic_sud gs baseFinder h_det_pred n A_F)⁻¹ *
          (skApproxC_generic_sud gs baseFinder h_det_pred n A_G)⁻¹) := rfl

/-! ## 2. Base-case approximation predicate -/

/-- **Base-case ε₀-approximation property** at SU(d): the `baseFinder`'s
output is within `ε` of the target under the linftyOp matrix norm. -/
def BaseFinder_approximates_within_sud {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (ε : ℝ) : Prop :=
  ∀ U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ),
    ‖((gs.ρ_hom (baseFinder U) : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ < ε

end SKEFTHawking.FKLW.GenericSUd
