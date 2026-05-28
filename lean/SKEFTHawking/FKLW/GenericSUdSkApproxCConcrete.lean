/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — concrete-radius SU(d) Solovay-Kitaev recursion `skApproxC_generic_sud_concrete`

The re-pointed counterpart of `skApproxC_generic_sud` (S43): the same Dawson-Nielsen
recursion, but with each level's `(F, G)` extracted by the **concrete-radius** DN step
`dnStepFG_sud_concrete` (S130 — generator from `matrixMercatorLog (Δ.val − 1)`) instead of
the existential-IFT `dnStepFG_sud`. This is the recursion the **UNCONDITIONAL** super-quad
bound + headline will be stated about, because the concrete step's per-level error
ingredients (exp-delta S130, F/G-norm S131, cubic remainder S132) hold on a *named*
calibration ball with no `Δ ∈ target` hypothesis.

The recursion is otherwise identical to `skApproxC_generic_sud` (same base finder, same
`expIsud_of_det_predicate` coercion, same group-commutator composition), so all of the
log-agnostic recursion bookkeeping (S95 combine, S96 stability term, ρ_hom abstraction S87)
transfers; only the per-step regime ingredients change from existential to concrete.

## Substantive content shipped

  * `skApproxC_generic_sud_concrete` — the concrete-step SK recursion.
  * `skApproxC_generic_sud_concrete_zero` / `_succ` — base / successor unfolding (`rfl`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R4: concrete SK recursion
(foundation for the UNCONDITIONAL concrete (B) bound).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkApproxC
import SKEFTHawking.FKLW.GenericSUdDnStepFGConcrete

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Concrete-radius SU(d) Solovay-Kitaev recursion**: the re-pointed `skApproxC_generic_sud`,
extracting each level's `(F, G)` via the concrete DN step `dnStepFG_sud_concrete` (S130)
rather than the existential-IFT `dnStepFG_sud`. Level 0 is the base finder; level `n+1` is
the visible Dawson-Nielsen composition `V_n · ⟦A_F, A_G⟧` with
`A_F = expIsud (skApproxC … n (exp i·F)), A_G = …` and `(F, G) = dnStepFG_sud_concrete V_n U`. -/
noncomputable def skApproxC_generic_sud_concrete {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2)) :
    ℕ → ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W
  | 0, U => baseFinder U
  | n + 1, U =>
    let V_n_word : gs.W := skApproxC_generic_sud_concrete gs baseFinder h_det_pred n U
    let V_n_SUd : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) :=
      gs.ρ_hom V_n_word
    let data : DNStepData_SUd (m + 2) := dnStepFG_sud_concrete V_n_SUd U
    let A_F : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) :=
      expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr
    let A_G : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) :=
      expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr
    let A_F_word : gs.W := skApproxC_generic_sud_concrete gs baseFinder h_det_pred n A_F
    let A_G_word : gs.W := skApproxC_generic_sud_concrete gs baseFinder h_det_pred n A_G
    V_n_word * (A_F_word * A_G_word * A_F_word⁻¹ * A_G_word⁻¹)

/-- Level-0 unfolding: base case is the supplied base finder. -/
lemma skApproxC_generic_sud_concrete_zero {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
    skApproxC_generic_sud_concrete gs baseFinder h_det_pred 0 U = baseFinder U := rfl

/-- Level-(n+1) unfolding: the visible Dawson-Nielsen composition (concrete step). -/
lemma skApproxC_generic_sud_concrete_succ {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
    skApproxC_generic_sud_concrete gs baseFinder h_det_pred (n + 1) U =
      let V_n_word := skApproxC_generic_sud_concrete gs baseFinder h_det_pred n U
      let data := dnStepFG_sud_concrete (gs.ρ_hom V_n_word) U
      let A_F := expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr
      let A_G := expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr
      V_n_word *
        (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n A_F *
          skApproxC_generic_sud_concrete gs baseFinder h_det_pred n A_G *
          (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n A_F)⁻¹ *
          (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n A_G)⁻¹) := rfl

end SKEFTHawking.FKLW.GenericSUd
