/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track M.4 (headline integration) — Generic concrete-word length-bound substrate

Adds the **closed-form induction-friendly skLength recurrence** required
to iterate the existing per-step concrete word-length recurrence
(`skApproxC_generic_cliffordT_length_succ` in `ConcreteWordLengthBound.lean`)
to the headline level `skLevel_polylog ε`. Together with the per-alphabet
length-bounded base finder hypothesis
`BaseFinder_length_bounded gs bf`, this lets each alphabet's
bundled-strict Solovay-Kitaev headline carry a **third conjunct** of the
form

  `((compile U ε).toWord.length : ℝ) ≤ skLength (skLevel_polylog ε)`

closing the substrate-vs-headline gap (Phase 6x retrospective addendum
anti-pattern #4) for the four `FreeGroup`-based per-alphabet instances:
Clifford+T, Read-Rezayi `k=5`, Read-Rezayi `k=7`, trapped-ion lift/shift.

## Headlines (this file)

  * `skLength_zero_eq` — `skLength 0 = skLengthBaseCase` (`= 100`).
  * `skLength_succ_eq` — `skLength (n+1) = 5 · skLength n + skBalancedDecompCost`.
  * `skLength_succ_ge_five_mul` — `5 · skLength n ≤ skLength (n+1)` (the
    arithmetic content needed in the induction step).

## Per-alphabet length-bound predicate

The predicate `BaseFinder_length_bounded_alpha α gs bf` (defined directly
at each per-alphabet quantitative file, NOT as a polymorphic generic
because `gs.W = FreeGroup α` is per-alphabet structural information
rather than universally-quantified parametric content):

  `∀ U : SU(2), ((bf U).toWord.length : ℝ) ≤ skLengthBaseCase`

## Closed-form iteration (template, instantiated per alphabet)

The induction template, applied at each FreeGroup-α alphabet:

  - Base: by `BaseFinder_length_bounded` + `skLength_zero_eq`.
  - Step: by `skApproxC_generic_succ` + four `FreeGroup.norm_mul_le` + two
    `FreeGroup.norm_inv_eq` + `skLength_succ_eq`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.SolovayKitaevLengthBound
import SKEFTHawking.FKLW.GenericSolovayKitaevRecursion
import Mathlib.GroupTheory.FreeGroup.Reduce

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix SKEFTHawking.FKLW
open SKEFTHawking.FKLW.SolovayKitaevLengthBound

/-! ## 1. Closed-form skLength arithmetic

The `skLength n = 100 · 5^n + 100 · (5^n - 1) / 4` closed form satisfies
the linear recurrence `skLength (n+1) = 5 · skLength n + 100`. This is
the arithmetic content needed for the inductive step of the per-alphabet
length-bound proofs. -/

/-- `skLength 0 = skLengthBaseCase` (`= 100`). -/
theorem skLength_zero_eq : skLength 0 = skLengthBaseCase := by
  unfold skLength
  simp

/-- **Linear recurrence**: `skLength (n+1) = 5 · skLength n + skBalancedDecompCost`. -/
theorem skLength_succ_eq (n : ℕ) :
    skLength (n + 1) = 5 * skLength n + skBalancedDecompCost := by
  unfold skLength skBalancedDecompCost
  -- LHS: 100 * 5^(n+1) + 100 * (5^(n+1) - 1) / 4
  -- RHS: 5 * (100 * 5^n + 100 * (5^n - 1) / 4) + 100
  --    = 500 * 5^n + 125 * (5^n - 1) + 100
  --    = 500 * 5^n + 125 * 5^n - 125 + 100
  --    = 625 * 5^n - 25
  -- LHS: 100 * 5 * 5^n + 100 * (5 * 5^n - 1) / 4
  --    = 500 * 5^n + 25 * (5 * 5^n - 1)
  --    = 500 * 5^n + 125 * 5^n - 25
  --    = 625 * 5^n - 25
  have h : (5 : ℝ) ^ (n + 1) = 5 * (5 : ℝ) ^ n := by
    rw [pow_succ]; ring
  rw [h]
  ring

/-- **The arithmetic content of the inductive step**:
`5 · skLength n ≤ skLength (n+1)`. Follows from `skLength_succ_eq` since
`skBalancedDecompCost ≥ 0`. -/
theorem skLength_succ_ge_five_mul (n : ℕ) :
    5 * skLength n ≤ skLength (n + 1) := by
  rw [skLength_succ_eq]
  have h_pos : (0 : ℝ) ≤ skBalancedDecompCost := by
    unfold skBalancedDecompCost; norm_num
  linarith

/-! ## 2. Base-finder length-bound predicate

A polymorphic predicate stating that the base finder produces words of
bounded FreeGroup-word-length. Per-alphabet, the base finder type-restricts
to `FreeGroup (Fin k)` for the alphabet's specific `k`. -/

/-- **Base finder length-bounded predicate** (FreeGroup-α variant).

The polymorphic predicate `∀ U, ((bf U).toWord.length : ℝ) ≤ skLengthBaseCase`
on a FreeGroup-α-typed base finder. Per-alphabet, this is the
load-bearing hypothesis that lets the per-step length recurrence
iterate to a closed-form `≤ skLength n` bound. -/
def BaseFinder_length_bounded {α : Type} [DecidableEq α]
    (bf : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup α) : Prop :=
  ∀ U : ↥(specialUnitaryGroup (Fin 2) ℂ),
    ((bf U).toWord.length : ℝ) ≤ skLengthBaseCase

/-- **Parametric base finder length-bounded predicate** (FreeGroup-α
variant, parametric in the base-case bound `N₀`).

Variant of `BaseFinder_length_bounded` that takes the base-case
length bound `N₀` as a parameter rather than fixing it at
`skLengthBaseCase`. This lets per-alphabet base finders ship with
their actual length bound (e.g., the Clifford+T constructive base
finder via `cliffordTFiniteCover_maxLength`) without requiring the
bound to be ≤ `skLengthBaseCase = 100` (the Ross-Selinger-optimal
calibration constant). The polylog-asymptotic structure is preserved
— only the leading constant differs. -/
def BaseFinder_length_bounded_by {α : Type} [DecidableEq α]
    (N₀ : ℝ) (bf : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup α) : Prop :=
  ∀ U : ↥(specialUnitaryGroup (Fin 2) ℂ),
    ((bf U).toWord.length : ℝ) ≤ N₀

/-! ## 2b. Parametric closed-form skLength (in base-case bound `N₀`)

The level-`n` closed form `N₀ · 5^n + skBalancedDecompCost · (5^n − 1) / 4`
parameterized in the base-case bound `N₀`. -/

/-- **The level-`n` braid-word length closed form, parametric in
base-case bound `N₀`**. -/
noncomputable def skLength_at_baseCase (N₀ : ℝ) (n : ℕ) : ℝ :=
  N₀ * (5 : ℝ) ^ n + skBalancedDecompCost * ((5 : ℝ) ^ n - 1) / 4

/-- `skLength_at_baseCase N₀ 0 = N₀`. -/
theorem skLength_at_baseCase_zero (N₀ : ℝ) :
    skLength_at_baseCase N₀ 0 = N₀ := by
  unfold skLength_at_baseCase; simp

/-- **Linear recurrence (parametric)**: `skLength_at_baseCase N₀ (n+1) =
5 · skLength_at_baseCase N₀ n + skBalancedDecompCost`. -/
theorem skLength_at_baseCase_succ_eq (N₀ : ℝ) (n : ℕ) :
    skLength_at_baseCase N₀ (n + 1) =
      5 * skLength_at_baseCase N₀ n + skBalancedDecompCost := by
  unfold skLength_at_baseCase
  have h : (5 : ℝ) ^ (n + 1) = 5 * (5 : ℝ) ^ n := by rw [pow_succ]; ring
  rw [h]
  ring

/-- **Arithmetic inductive step (parametric)**:
`5 · skLength_at_baseCase N₀ n ≤ skLength_at_baseCase N₀ (n+1)`. -/
theorem skLength_at_baseCase_succ_ge_five_mul (N₀ : ℝ) (n : ℕ) :
    5 * skLength_at_baseCase N₀ n ≤ skLength_at_baseCase N₀ (n + 1) := by
  rw [skLength_at_baseCase_succ_eq]
  have h_pos : (0 : ℝ) ≤ skBalancedDecompCost := by
    unfold skBalancedDecompCost; norm_num
  linarith

/-! ## 3. FreeGroup-α generating-set constructor

A bundled helper that constructs a `GeneratingSet` from a FreeGroup-α
representation. Lets us state the per-step + closed-form length bounds
polymorphically in α; per-alphabet specializations apply the bound at
the named generating set via the definitional equality
`<named GS> = mkFreeGroupGS <ρ_hom> <gens> ...`. -/

/-- **Constructor**: build a `GeneratingSet` from a FreeGroup-α
representation and generator data. The result satisfies
`(mkFreeGroupGS ρ_hom gens h_ne h_gen).W = FreeGroup α` definitionally. -/
@[reducible] noncomputable def mkFreeGroupGS
    {α : Type} [DecidableEq α]
    (ρ_hom : FreeGroup α →* ↥(specialUnitaryGroup (Fin 2) ℂ))
    (gens : Finset (FreeGroup α))
    (h_nonempty : gens.Nonempty)
    (h_generate : Subgroup.closure (gens : Set (FreeGroup α)) = (⊤ : Subgroup _)) :
    GeneratingSet :=
  { W := FreeGroup α
    Wgroup := inferInstance
    ρ_hom := ρ_hom
    gens := gens
    gens_nonempty := h_nonempty
    gens_generate := h_generate }

/-! ## 4. Per-step length recurrence (polymorphic in α)

The per-step Dawson-Nielsen length recurrence at any FreeGroup-α
`GeneratingSet`. Generalizes the existing
`skApproxC_generic_cliffordT_length_succ` in
`ConcreteWordLengthBound.lean` from `α = Fin 2` to arbitrary `α`. -/

/-- **Per-step length recurrence at any FreeGroup-α GeneratingSet**.

For any `α : Type` with `DecidableEq α`, any FreeGroup-α GS
`gs := mkFreeGroupGS ρ_hom gens h_ne h_gen`, any base finder
`bf : SU(2) → FreeGroup α`, level `n`, and target `U ∈ SU(2)`,
the level-`(n+1)` Dawson-Nielsen output has FreeGroup-word-length
bounded by `length(at U) + 2·length(at A_F) + 2·length(at A_G)`.

Same proof structure as `skApproxC_generic_cliffordT_length_succ`:
unfold `skApproxC_generic_succ` to `V · (wF · wG · wF⁻¹ · wG⁻¹)`, then
four `FreeGroup.norm_mul_le` + two `FreeGroup.norm_inv_eq` chains. -/
theorem skApproxC_generic_freeGroup_length_succ
    {α : Type} [DecidableEq α]
    (ρ_hom : FreeGroup α →* ↥(specialUnitaryGroup (Fin 2) ℂ))
    (gens : Finset (FreeGroup α))
    (h_nonempty : gens.Nonempty)
    (h_generate : Subgroup.closure (gens : Set (FreeGroup α)) = (⊤ : Subgroup _))
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup α)
    (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    let gs := mkFreeGroupGS ρ_hom gens h_nonempty h_generate
    let V_n_word := skApproxC_generic gs baseFinder n U
    let data := dnStepFG_su2 (gs.ρ_hom V_n_word) U
    let A_F := SolovayKitaevPathA.expIsu2 data.F data.hF_herm data.hF_tr
    let A_G := SolovayKitaevPathA.expIsu2 data.G data.hG_herm data.hG_tr
    (skApproxC_generic gs baseFinder (n + 1) U).toWord.length ≤
      (skApproxC_generic gs baseFinder n U).toWord.length
      + 2 * (skApproxC_generic gs baseFinder n A_F).toWord.length
      + 2 * (skApproxC_generic gs baseFinder n A_G).toWord.length := by
  simp only
  set gs := mkFreeGroupGS ρ_hom gens h_nonempty h_generate with hgs_def
  have h_succ := skApproxC_generic_succ gs baseFinder n U
  set V := skApproxC_generic gs baseFinder n U with hV_def
  set data_local := dnStepFG_su2 (gs.ρ_hom V) U with hdata_def
  set A_F_local := SolovayKitaevPathA.expIsu2
    data_local.F data_local.hF_herm data_local.hF_tr with hA_F_def
  set A_G_local := SolovayKitaevPathA.expIsu2
    data_local.G data_local.hG_herm data_local.hG_tr with hA_G_def
  set wF := skApproxC_generic gs baseFinder n A_F_local with hwF_def
  set wG := skApproxC_generic gs baseFinder n A_G_local with hwG_def
  have h_eq : skApproxC_generic gs baseFinder (n + 1) U
      = V * (wF * wG * wF⁻¹ * wG⁻¹) := h_succ
  rw [h_eq]
  have h_inv_F : wF⁻¹.toWord.length = wF.toWord.length := FreeGroup.norm_inv_eq
  have h_inv_G : wG⁻¹.toWord.length = wG.toWord.length := FreeGroup.norm_inv_eq
  have h1 : (wF * wG).toWord.length ≤ wF.toWord.length + wG.toWord.length :=
    FreeGroup.norm_mul_le wF wG
  have h2 : (wF * wG * wF⁻¹).toWord.length ≤
      (wF * wG).toWord.length + wF⁻¹.toWord.length :=
    FreeGroup.norm_mul_le (wF * wG) wF⁻¹
  have h3 : (wF * wG * wF⁻¹ * wG⁻¹).toWord.length ≤
      (wF * wG * wF⁻¹).toWord.length + wG⁻¹.toWord.length :=
    FreeGroup.norm_mul_le (wF * wG * wF⁻¹) wG⁻¹
  have h4 : (V * (wF * wG * wF⁻¹ * wG⁻¹)).toWord.length ≤
      V.toWord.length + (wF * wG * wF⁻¹ * wG⁻¹).toWord.length :=
    FreeGroup.norm_mul_le V (wF * wG * wF⁻¹ * wG⁻¹)
  linarith

/-! ## 5. Closed-form length bound by induction

Iterates the per-step recurrence to a closed-form `≤ skLength n` bound,
given the base finder satisfies `BaseFinder_length_bounded`. -/

/-- **Closed-form length bound for any FreeGroup-α `skApproxC_generic`**.

Given a FreeGroup-α GS and a length-bounded base finder
(`BaseFinder_length_bounded bf`), the level-`n` Dawson-Nielsen output's
FreeGroup-word-length is bounded by `skLength n` for all `n` and `U`.

**Proof**: strong induction on `n`. Base case (`n = 0`) by the length-bound
hypothesis + `skLength_zero_eq`. Step case (`n + 1`) by
`skApproxC_generic_freeGroup_length_succ` + induction hypothesis applied
to all three RHS terms (U, A_F, A_G) + `skLength_succ_ge_five_mul`. -/
theorem skApproxC_generic_freeGroup_length_le_skLength
    {α : Type} [DecidableEq α]
    (ρ_hom : FreeGroup α →* ↥(specialUnitaryGroup (Fin 2) ℂ))
    (gens : Finset (FreeGroup α))
    (h_nonempty : gens.Nonempty)
    (h_generate : Subgroup.closure (gens : Set (FreeGroup α)) = (⊤ : Subgroup _))
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup α)
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    ((skApproxC_generic (mkFreeGroupGS ρ_hom gens h_nonempty h_generate)
        baseFinder n U).toWord.length : ℝ) ≤ skLength n := by
  -- Induct on `n` with universal U (strong induction on the level).
  induction n generalizing U with
  | zero =>
    -- skApproxC_generic gs bf 0 U = baseFinder U by skApproxC_generic_zero.
    rw [skApproxC_generic_zero]
    rw [skLength_zero_eq]
    exact h_bf_length U
  | succ n ih =>
    -- Per-step recurrence:
    -- length(n+1 U) ≤ length(n U) + 2 · length(n A_F) + 2 · length(n A_G)
    have h_step := skApproxC_generic_freeGroup_length_succ
      ρ_hom gens h_nonempty h_generate baseFinder n U
    set gs := mkFreeGroupGS ρ_hom gens h_nonempty h_generate with hgs_def
    set V := skApproxC_generic gs baseFinder n U with hV_def
    set data_local := dnStepFG_su2 (gs.ρ_hom V) U with hdata_def
    set A_F_local := SolovayKitaevPathA.expIsu2
      data_local.F data_local.hF_herm data_local.hF_tr with hA_F_def
    set A_G_local := SolovayKitaevPathA.expIsu2
      data_local.G data_local.hG_herm data_local.hG_tr with hA_G_def
    have h_ih_U : ((skApproxC_generic gs baseFinder n U).toWord.length : ℝ) ≤ skLength n :=
      ih U
    have h_ih_F : ((skApproxC_generic gs baseFinder n A_F_local).toWord.length : ℝ)
                    ≤ skLength n := ih A_F_local
    have h_ih_G : ((skApproxC_generic gs baseFinder n A_G_local).toWord.length : ℝ)
                    ≤ skLength n := ih A_G_local
    -- The per-step bound `h_step` is in ℕ; lift to ℝ.
    have h_step_R : ((skApproxC_generic gs baseFinder (n + 1) U).toWord.length : ℝ) ≤
        (skApproxC_generic gs baseFinder n U).toWord.length
        + 2 * (skApproxC_generic gs baseFinder n A_F_local).toWord.length
        + 2 * (skApproxC_generic gs baseFinder n A_G_local).toWord.length := by
      exact_mod_cast h_step
    -- Chain: h_step_R + 5·skLength n ≤ skLength (n+1).
    have h_five_mul : 5 * skLength n ≤ skLength (n + 1) := skLength_succ_ge_five_mul n
    linarith

/-! ## 6. Parametric closed-form length bound (in base-case bound `N₀`)

Same induction structure as `skApproxC_generic_freeGroup_length_le_skLength`,
but with the parametric `BaseFinder_length_bounded_by N₀` hypothesis
yielding the parametric `skLength_at_baseCase N₀ n` bound. -/

/-- **Closed-form length bound parametric in base-case bound `N₀`**.

For any `α : Type` with `DecidableEq α`, any FreeGroup-α GS via
`mkFreeGroupGS`, any base finder `bf` satisfying
`BaseFinder_length_bounded_by N₀ bf`, and any level `n` and target
`U ∈ SU(2)`, the level-`n` Dawson-Nielsen output's FreeGroup-word-length
is bounded by `skLength_at_baseCase N₀ n`.

This is the parametric version of `skApproxC_generic_freeGroup_length_le_skLength`
that handles arbitrary base-case bounds `N₀` (not necessarily ≤
`skLengthBaseCase`). -/
theorem skApproxC_generic_freeGroup_length_le_skLength_at_baseCase
    {α : Type} [DecidableEq α]
    (ρ_hom : FreeGroup α →* ↥(specialUnitaryGroup (Fin 2) ℂ))
    (gens : Finset (FreeGroup α))
    (h_nonempty : gens.Nonempty)
    (h_generate : Subgroup.closure (gens : Set (FreeGroup α)) = (⊤ : Subgroup _))
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup α)
    (N₀ : ℝ)
    (h_bf_length : BaseFinder_length_bounded_by N₀ baseFinder)
    (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    ((skApproxC_generic (mkFreeGroupGS ρ_hom gens h_nonempty h_generate)
        baseFinder n U).toWord.length : ℝ) ≤ skLength_at_baseCase N₀ n := by
  induction n generalizing U with
  | zero =>
    rw [skApproxC_generic_zero]
    rw [skLength_at_baseCase_zero]
    exact h_bf_length U
  | succ n ih =>
    have h_step := skApproxC_generic_freeGroup_length_succ
      ρ_hom gens h_nonempty h_generate baseFinder n U
    set gs := mkFreeGroupGS ρ_hom gens h_nonempty h_generate with hgs_def
    set V := skApproxC_generic gs baseFinder n U with hV_def
    set data_local := dnStepFG_su2 (gs.ρ_hom V) U with hdata_def
    set A_F_local := SolovayKitaevPathA.expIsu2
      data_local.F data_local.hF_herm data_local.hF_tr with hA_F_def
    set A_G_local := SolovayKitaevPathA.expIsu2
      data_local.G data_local.hG_herm data_local.hG_tr with hA_G_def
    have h_ih_U : ((skApproxC_generic gs baseFinder n U).toWord.length : ℝ)
                    ≤ skLength_at_baseCase N₀ n := ih U
    have h_ih_F : ((skApproxC_generic gs baseFinder n A_F_local).toWord.length : ℝ)
                    ≤ skLength_at_baseCase N₀ n := ih A_F_local
    have h_ih_G : ((skApproxC_generic gs baseFinder n A_G_local).toWord.length : ℝ)
                    ≤ skLength_at_baseCase N₀ n := ih A_G_local
    have h_step_R : ((skApproxC_generic gs baseFinder (n + 1) U).toWord.length : ℝ) ≤
        (skApproxC_generic gs baseFinder n U).toWord.length
        + 2 * (skApproxC_generic gs baseFinder n A_F_local).toWord.length
        + 2 * (skApproxC_generic gs baseFinder n A_G_local).toWord.length := by
      exact_mod_cast h_step
    have h_five_mul : 5 * skLength_at_baseCase N₀ n
                        ≤ skLength_at_baseCase N₀ (n + 1) :=
      skLength_at_baseCase_succ_ge_five_mul N₀ n
    linarith

end SKEFTHawking.FKLW.GenericSU2
