/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track M.4 — Concrete-word length-bound coupling (CP2 RC2)

Ships the **concrete FreeGroup-word-length recurrence** for the
Dawson-Nielsen Solovay-Kitaev recursion (`skApproxC_generic`) applied
at the canonical `cliffordTGeneratingSet`-style alphabets — i.e., any
GeneratingSet whose `gs.W` is *definitionally* `FreeGroup (Fin 2)`.

This tightens the Phase 6u Wave 5 length conjunct from the abstract
real-valued `skLength (skLevel_polylog ε)` bound to the concrete
FreeGroup-word-length recurrence at each Dawson-Nielsen recursion
level.

## Headline (per-step concrete recurrence at Clifford+T)

`skApproxC_generic_cliffordT_length_succ` — at the canonical
`cliffordTGeneratingSet`, the level-(n+1) Dawson-Nielsen output's
`FreeGroup (Fin 2)` word length is bounded by the weighted sum of the
level-n word lengths at the three closely-related arguments (V_n at U,
level n at A_F, level n at A_G), with multiplicities `1, 2, 2`. This
gives the geometric `5^n · L_0` growth structure.

The proof reduces to four applications of `FreeGroup.norm_mul_le` plus
two applications of `FreeGroup.norm_inv_eq` for the inverse factors.

## Per-alphabet specialization

The proof depends only on the GeneratingSet's `gs.W = FreeGroup (Fin 2)`
and the recursion structure (`skApproxC_generic_succ`). For other
FreeGroup-based instances (Read-Rezayi `k=5`, `k=7`, ...), the same
statement and proof apply verbatim with the GeneratingSet substituted.
The Clifford+T statement here is the canonical instance.

## Mathlib-PR target

Proposed file: `Mathlib/Analysis/MatrixGroups/SolovayKitaev/LengthBound.lean`,
alongside the generic Solovay-Kitaev recursion if it lands upstream.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.GenericSolovayKitaevRecursion
import SKEFTHawking.FKLW.CliffordTGeneratingSet
import Mathlib.GroupTheory.FreeGroup.Reduce

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix SKEFTHawking.FKLW

/-! ## 1. Length-additivity / inverse helpers (FreeGroup standard) -/

/-- **FreeGroup word-length sub-additivity**: `‖x · y‖ ≤ ‖x‖ + ‖y‖`. -/
theorem freeGroup_toWord_mul_length_le {α : Type*} [DecidableEq α]
    (x y : FreeGroup α) :
    (x * y).toWord.length ≤ x.toWord.length + y.toWord.length :=
  FreeGroup.norm_mul_le x y

/-- **FreeGroup inverse preserves word length**: `‖x⁻¹‖ = ‖x‖`. -/
theorem freeGroup_toWord_inv_length {α : Type*} [DecidableEq α] (x : FreeGroup α) :
    x⁻¹.toWord.length = x.toWord.length :=
  FreeGroup.norm_inv_eq

/-! ## 2. Per-step length recurrence at Clifford+T -/

/-- **Per-step Dawson-Nielsen length recurrence at Clifford+T**.

For the canonical `cliffordTGeneratingSet` (with
`gs.W = FreeGroup (Fin 2)`), any base finder
`bf : SU(2) → FreeGroup (Fin 2)`, level `n`, and target `U ∈ SU(2)`,
the level-(n+1) Dawson-Nielsen output has FreeGroup-word-length bounded
by `(length at U) + 2·(length at A_F) + 2·(length at A_G)`, i.e., the
geometric `5×`-per-level growth structure.

The proof: unfold `skApproxC_generic_succ` to `V · (wF · wG · wF⁻¹ · wG⁻¹)`,
then apply `FreeGroup.norm_mul_le` four times plus `FreeGroup.norm_inv_eq`
for the inverse factors. -/
theorem skApproxC_generic_cliffordT_length_succ
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 2))
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    let V_n_word := skApproxC_generic cliffordTGeneratingSet baseFinder n U
    let data := dnStepFG_su2 (cliffordTGeneratingSet.ρ_hom V_n_word) U
    let A_F := SolovayKitaevPathA.expIsu2 data.F data.hF_herm data.hF_tr
    let A_G := SolovayKitaevPathA.expIsu2 data.G data.hG_herm data.hG_tr
    (skApproxC_generic cliffordTGeneratingSet baseFinder (n + 1) U).toWord.length ≤
      (skApproxC_generic cliffordTGeneratingSet baseFinder n U).toWord.length
      + 2 * (skApproxC_generic cliffordTGeneratingSet baseFinder n A_F).toWord.length
      + 2 * (skApproxC_generic cliffordTGeneratingSet baseFinder n A_G).toWord.length := by
  simp only
  -- Unfold the recursive step.
  have h_succ := skApproxC_generic_succ cliffordTGeneratingSet baseFinder n U
  set V := skApproxC_generic cliffordTGeneratingSet baseFinder n U with hV_def
  set data_local := dnStepFG_su2 (cliffordTGeneratingSet.ρ_hom V) U with hdata_def
  set A_F_local := SolovayKitaevPathA.expIsu2 data_local.F data_local.hF_herm data_local.hF_tr
    with hA_F_def
  set A_G_local := SolovayKitaevPathA.expIsu2 data_local.G data_local.hG_herm data_local.hG_tr
    with hA_G_def
  set wF := skApproxC_generic cliffordTGeneratingSet baseFinder n A_F_local with hwF_def
  set wG := skApproxC_generic cliffordTGeneratingSet baseFinder n A_G_local with hwG_def
  -- skApproxC_generic ... (n + 1) U = V * (wF * wG * wF⁻¹ * wG⁻¹).
  have h_eq : skApproxC_generic cliffordTGeneratingSet baseFinder (n + 1) U
      = V * (wF * wG * wF⁻¹ * wG⁻¹) := h_succ
  rw [h_eq]
  -- Chain four norm_mul_le's plus norm_inv_eq's.
  have h_inv_F : wF⁻¹.toWord.length = wF.toWord.length := freeGroup_toWord_inv_length wF
  have h_inv_G : wG⁻¹.toWord.length = wG.toWord.length := freeGroup_toWord_inv_length wG
  have h1 : (wF * wG).toWord.length ≤ wF.toWord.length + wG.toWord.length :=
    freeGroup_toWord_mul_length_le wF wG
  have h2 : (wF * wG * wF⁻¹).toWord.length ≤
      (wF * wG).toWord.length + wF⁻¹.toWord.length :=
    freeGroup_toWord_mul_length_le (wF * wG) wF⁻¹
  have h3 : (wF * wG * wF⁻¹ * wG⁻¹).toWord.length ≤
      (wF * wG * wF⁻¹).toWord.length + wG⁻¹.toWord.length :=
    freeGroup_toWord_mul_length_le (wF * wG * wF⁻¹) wG⁻¹
  have h4 : (V * (wF * wG * wF⁻¹ * wG⁻¹)).toWord.length ≤
      V.toWord.length + (wF * wG * wF⁻¹ * wG⁻¹).toWord.length :=
    freeGroup_toWord_mul_length_le V (wF * wG * wF⁻¹ * wG⁻¹)
  linarith

end SKEFTHawking.FKLW.GenericSU2
