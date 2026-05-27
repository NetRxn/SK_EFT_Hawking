/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Solovay-Kitaev length bound for FreeGroup-α generating sets (Mathlib-upstream-PR-quality)

**Phase 6x Track M.4 actual extraction (2026-05-26, post-retrospective addendum)**

This file ships the **Mathlib-upstream-PR-quality presentation** of the
project's `skApproxC_generic_cliffordT_length_succ`
(in `SKEFTHawking.FKLW.ConcreteWordLengthBound`, originally at the
`cliffordTGeneratingSet` specialization) **lifted to arbitrary
FreeGroup-α generating sets** via the Phase 6x Track M.4
infrastructure (`GenericConcreteWordLengthBound.lean`).

Per the Phase 6x retrospective addendum (2026-05-26), Mathlib-upstream-PR-
quality requires:
  - de-privatized ✓ (already public),
  - generic-typed ✓ (lifted from `gs.W = FreeGroup (Fin 2)` to
    `gs.W = FreeGroup α` for any `α : Type*` with `DecidableEq`),
  - `Matrix.SolovayKitaev.LengthBound` namespace ✓,
  - filename mirror `Mathlib.Analysis.MatrixGroups.SolovayKitaev.LengthBound` ✓
    (in-project at `SKEFTHawking.SolovayKitaevLengthBoundMathlibPR`),
  - docstrings (Mathlib-style) ✓,
  - examples (Clifford+T at `Fin 2`, trapped-ion at `Fin 3`) ✓.

## Substantive improvement over alias (anti-pattern #3 of Phase 6x addendum)

The deliverable lifts the original `cliffordT`-specialized per-step
length recurrence to a **fully α-polymorphic** statement at any
FreeGroup-α generating set, with the proof factored through the
Phase 6x Track M.4 substrate's `skApproxC_generic_freeGroup_length_succ`
+ `mkFreeGroupGS` infrastructure. The closed-form `≤ skLength n`
length-bound and the parametric `≤ skLength_at_baseCase N₀ n` variant
are both re-exported here under the `Matrix.SolovayKitaev.LengthBound`
namespace.

## Mathlib-upstream target

  Proposed file: `Mathlib/Analysis/MatrixGroups/SolovayKitaev/LengthBound.lean`.

## Headlines

  * `Matrix.SolovayKitaev.LengthBound.freeGroup_norm_mul_le` —
    `(x * y).toWord.length ≤ x.toWord.length + y.toWord.length`
    (de-privatized + α-polymorphic).
  * `Matrix.SolovayKitaev.LengthBound.freeGroup_norm_inv_eq` —
    `x⁻¹.toWord.length = x.toWord.length`.
  * `Matrix.SolovayKitaev.LengthBound.skApprox_length_succ` —
    per-step recurrence at any FreeGroup-α GS.
  * `Matrix.SolovayKitaev.LengthBound.skApprox_length_le_skLength` —
    closed-form `≤ skLength n` (parametric base case = `skLengthBaseCase`).
  * `Matrix.SolovayKitaev.LengthBound.skApprox_length_le_skLength_at_baseCase`
    — closed-form parametric in the base-case bound `N₀`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.GenericConcreteWordLengthBound
import SKEFTHawking.FKLW.ConcreteWordLengthBound

set_option autoImplicit false

namespace Matrix.SolovayKitaev.LengthBound

open SKEFTHawking.FKLW SKEFTHawking.FKLW.GenericSU2
  SKEFTHawking.FKLW.SolovayKitaevLengthBound

/-! ## 1. De-privatized FreeGroup-length helpers (Mathlib-PR-quality aliases)

The two FreeGroup helpers used by the per-step Dawson-Nielsen length
recurrence: sub-additivity under multiplication and inverse-length
preservation. Both are already public in the project; this section
re-exports them under the Mathlib-PR namespace for upstream-PR
presentation. -/

/-- **FreeGroup word-length sub-additivity**: `‖x · y‖ ≤ ‖x‖ + ‖y‖`. -/
theorem freeGroup_norm_mul_le {α : Type*} [DecidableEq α]
    (x y : FreeGroup α) :
    (x * y).toWord.length ≤ x.toWord.length + y.toWord.length :=
  FreeGroup.norm_mul_le x y

/-- **FreeGroup inverse preserves word length**: `‖x⁻¹‖ = ‖x‖`. -/
theorem freeGroup_norm_inv_eq {α : Type*} [DecidableEq α]
    (x : FreeGroup α) :
    x⁻¹.toWord.length = x.toWord.length :=
  FreeGroup.norm_inv_eq

/-! ## 2. Per-step length recurrence at any FreeGroup-α GS

The α-polymorphic version of the project's per-step recurrence
(originally at `cliffordTGeneratingSet`). The Mathlib-PR-quality
deliverable for downstream Solovay-Kitaev consumers. -/

/-- **Per-step Dawson-Nielsen length recurrence at any FreeGroup-α
generating set** (Mathlib-PR-quality presentation).

For any `α : Type*` with `[DecidableEq α]`, any FreeGroup-α-based
generating set (via `mkFreeGroupGS`), any base finder
`bf : SU(2) → FreeGroup α`, level `n`, and target `U ∈ SU(2)`, the
level-`(n+1)` Dawson-Nielsen output has FreeGroup-word-length bounded
by the 5-term weighted sum
`length(at U) + 2·length(at A_F) + 2·length(at A_G)`. -/
theorem skApprox_length_succ
    {α : Type} [DecidableEq α]
    (ρ_hom : FreeGroup α →* ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (gens : Finset (FreeGroup α))
    (h_nonempty : gens.Nonempty)
    (h_generate : Subgroup.closure (gens : Set (FreeGroup α)) = (⊤ : Subgroup _))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → FreeGroup α)
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    let gs := mkFreeGroupGS ρ_hom gens h_nonempty h_generate
    let V_n_word := skApproxC_generic gs baseFinder n U
    let data := dnStepFG_su2 (gs.ρ_hom V_n_word) U
    let A_F := SolovayKitaevPathA.expIsu2 data.F data.hF_herm data.hF_tr
    let A_G := SolovayKitaevPathA.expIsu2 data.G data.hG_herm data.hG_tr
    (skApproxC_generic gs baseFinder (n + 1) U).toWord.length ≤
      (skApproxC_generic gs baseFinder n U).toWord.length
      + 2 * (skApproxC_generic gs baseFinder n A_F).toWord.length
      + 2 * (skApproxC_generic gs baseFinder n A_G).toWord.length :=
  skApproxC_generic_freeGroup_length_succ ρ_hom gens h_nonempty h_generate
    baseFinder n U

/-! ## 3. Closed-form `≤ skLength n` at fixed-skLengthBaseCase

Iterates the per-step recurrence to the closed-form Phase 6t `skLength n`
upper bound, conditional on the base finder satisfying
`BaseFinder_length_bounded` (with `skLengthBaseCase` as the
fixed-100 base-case constant). -/

/-- **Closed-form length bound at fixed `skLengthBaseCase = 100`** at
any FreeGroup-α GS. -/
theorem skApprox_length_le_skLength
    {α : Type} [DecidableEq α]
    (ρ_hom : FreeGroup α →* ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (gens : Finset (FreeGroup α))
    (h_nonempty : gens.Nonempty)
    (h_generate : Subgroup.closure (gens : Set (FreeGroup α)) = (⊤ : Subgroup _))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → FreeGroup α)
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ((skApproxC_generic (mkFreeGroupGS ρ_hom gens h_nonempty h_generate)
        baseFinder n U).toWord.length : ℝ) ≤ skLength n :=
  skApproxC_generic_freeGroup_length_le_skLength
    ρ_hom gens h_nonempty h_generate baseFinder h_bf_length n U

/-- **Closed-form length bound parametric in base-case bound `N₀`** at
any FreeGroup-α GS. Lets per-alphabet base finders with non-optimal
base-case length ship a length-bound headline directly. -/
theorem skApprox_length_le_skLength_at_baseCase
    {α : Type} [DecidableEq α]
    (ρ_hom : FreeGroup α →* ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (gens : Finset (FreeGroup α))
    (h_nonempty : gens.Nonempty)
    (h_generate : Subgroup.closure (gens : Set (FreeGroup α)) = (⊤ : Subgroup _))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → FreeGroup α)
    (N₀ : ℝ)
    (h_bf_length : BaseFinder_length_bounded_by N₀ baseFinder)
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ((skApproxC_generic (mkFreeGroupGS ρ_hom gens h_nonempty h_generate)
        baseFinder n U).toWord.length : ℝ) ≤ skLength_at_baseCase N₀ n :=
  skApproxC_generic_freeGroup_length_le_skLength_at_baseCase
    ρ_hom gens h_nonempty h_generate baseFinder N₀ h_bf_length n U

/-! ## 4. Examples

The α-polymorphic version applies to all the FreeGroup-based per-alphabet
generating sets:
  - Clifford+T (`α = Fin 2`): single-qubit Solovay-Kitaev compilation
    (Phase 6u Track T-S).
  - Read-Rezayi `SU(2)_5`, `SU(2)_7` (`α = Fin 2`): topological-quantum-
    computing universal anyon families (Phase 6x Track T-B).
  - Trapped-ion lift/shift (`α = Fin 3`): production-aligned per-ion
    1Q compilation (Phase 6x Track T-A1). -/

/-- **Example at Clifford+T (α = Fin 2)**: the canonical single-qubit
Solovay-Kitaev compilation. The closed-form length bound at fixed
`skLengthBaseCase` lifts directly. -/
example
    (ρ_hom : FreeGroup (Fin 2) →* ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (gens : Finset (FreeGroup (Fin 2)))
    (h_nonempty : gens.Nonempty)
    (h_generate : Subgroup.closure (gens : Set (FreeGroup (Fin 2))) = (⊤ : Subgroup _))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 2))
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ((skApproxC_generic (mkFreeGroupGS ρ_hom gens h_nonempty h_generate)
        baseFinder n U).toWord.length : ℝ) ≤ skLength n :=
  skApprox_length_le_skLength ρ_hom gens h_nonempty h_generate
    baseFinder h_bf_length n U

/-- **Example at trapped-ion lift/shift (α = Fin 3)**: the production-
aligned per-ion 1Q + MS-primitive alphabet. -/
example
    (ρ_hom : FreeGroup (Fin 3) →* ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (gens : Finset (FreeGroup (Fin 3)))
    (h_nonempty : gens.Nonempty)
    (h_generate : Subgroup.closure (gens : Set (FreeGroup (Fin 3))) = (⊤ : Subgroup _))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 3))
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ((skApproxC_generic (mkFreeGroupGS ρ_hom gens h_nonempty h_generate)
        baseFinder n U).toWord.length : ℝ) ≤ skLength n :=
  skApprox_length_le_skLength ρ_hom gens h_nonempty h_generate
    baseFinder h_bf_length n U

end Matrix.SolovayKitaev.LengthBound
