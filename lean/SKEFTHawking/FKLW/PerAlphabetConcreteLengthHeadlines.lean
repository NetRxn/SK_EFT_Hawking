/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track M.4 (headline integration) — Per-alphabet 3-conjunct bundled-strict headlines

Strengthens the existing 2-conjunct bundled-strict Solovay-Kitaev
headlines at each of the four FreeGroup-based per-alphabet generating
sets (Clifford+T, Read-Rezayi `k=5`, Read-Rezayi `k=7`, trapped-ion
lift/shift) by adding a **third conjunct** of the form

  `((compile U ε).toWord.length : ℝ) ≤ skLength (skLevel_polylog ε)`

closing the **substrate-vs-headline gap** flagged in the Phase 6x
retrospective addendum as anti-pattern #4. The third conjunct binds the
compiled output's CONCRETE FreeGroup word length (the thing downstream
quantum-compiler consumers actually need) to the abstract closed-form
length `skLength (skLevel_polylog ε)` already bounded in the existing
2-conjunct headlines.

## Hypothesis posture

The third conjunct depends on the per-alphabet base finder satisfying

  `BaseFinder_length_bounded baseFinder := ∀ U, ((bf U).toWord.length : ℝ) ≤ skLengthBaseCase`

The substantive per-alphabet discharge of this hypothesis (constructing
a length-bounded base finder) is Phase 6x Track T-S′ (Ross-Selinger for
Clifford+T) and follow-on per-alphabet work for Read-Rezayi `k=5/7` and
trapped-ion. This file ships the **headline statements taking
`h_bf_length` as an explicit hypothesis**, which closes the
substrate-vs-headline gap at the headline level: the third conjunct is
now present in ALL bundled-strict per-alphabet headlines.

## Headlines (per-alphabet 3-conjunct strict, conditional on `h_bf_length`)

  * `solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_concrete`
  * `solovayKitaev_dawson_nielsen_quantitative_readRezayiK5_strict_concrete`
  * `solovayKitaev_dawson_nielsen_quantitative_readRezayiK7_strict_concrete`
  * `solovayKitaev_dawson_nielsen_quantitative_trappedIon_strict_concrete`

Each headline conjoins:
  - **Error**: `‖ρ_<alphabet> (compile U ε) - U‖ ≤ ε`.
  - **Abstract length**: `skLength (skLevel_polylog ε) ≤ skLengthConst · …`.
  - **Concrete length**: `((compile U ε).toWord.length : ℝ) ≤ skLength (skLevel_polylog ε)`.

at the SAME algorithmic compile level `skLevel_polylog ε`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.GenericConcreteWordLengthBound
import SKEFTHawking.FKLW.CliffordTV4WitnessUnconditional
import SKEFTHawking.FKLW.ReadRezayiK5V4WitnessUnconditional
import SKEFTHawking.FKLW.ReadRezayiK7V4WitnessUnconditional
import SKEFTHawking.FKLW.TrappedIonGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Per-alphabet GS = mkFreeGroupGS reductions

Each named per-alphabet generating set is definitionally equal to the
`mkFreeGroupGS` constructor's output. The `rfl` proofs make this
explicit, enabling the generic length bound to specialize directly. -/

/-- `cliffordTGeneratingSet = mkFreeGroupGS ρ_CliffT cliffordTGens …`
(definitionally). -/
theorem cliffordTGeneratingSet_eq_mkFreeGroupGS :
    cliffordTGeneratingSet
      = mkFreeGroupGS (α := Fin 2) ρ_CliffT cliffordTGens
          cliffordTGens_nonempty cliffordTGens_generate := rfl

/-- `trappedIonGeneratingSet = mkFreeGroupGS ρ_TI trappedIonGens …`
(definitionally). -/
theorem trappedIonGeneratingSet_eq_mkFreeGroupGS :
    trappedIonGeneratingSet
      = mkFreeGroupGS (α := Fin 3) ρ_TI trappedIonGens
          trappedIonGens_nonempty trappedIonGens_generate := rfl

/-! ## 2. Per-alphabet concrete length bounds at any level

Specializes `skApproxC_generic_freeGroup_length_le_skLength` to each
named per-alphabet GS via the `rfl` equality above. -/

/-- **Clifford+T concrete length bound at any level**.

For any length-bounded Clifford+T base finder, the level-`n`
Dawson-Nielsen output's FreeGroup-word-length is bounded by `skLength n`.
Direct specialization of the generic FreeGroup-α length bound via the
definitional equality `cliffordTGeneratingSet = mkFreeGroupGS …` (rfl). -/
theorem skApproxC_generic_cliffordT_length_le_skLength
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 2))
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    ((skApproxC_generic cliffordTGeneratingSet baseFinder n U).toWord.length : ℝ)
      ≤ skLength n :=
  skApproxC_generic_freeGroup_length_le_skLength
    ρ_CliffT cliffordTGens cliffordTGens_nonempty cliffordTGens_generate
    baseFinder h_bf_length n U

/-- **Trapped-ion concrete length bound at any level**.

For any length-bounded trapped-ion base finder, the level-`n`
Dawson-Nielsen output's FreeGroup-word-length is bounded by `skLength n`.
Direct specialization of the generic FreeGroup-α length bound via the
definitional equality `trappedIonGeneratingSet = mkFreeGroupGS …` (rfl). -/
theorem skApproxC_generic_trappedIon_length_le_skLength
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 3))
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    ((skApproxC_generic trappedIonGeneratingSet baseFinder n U).toWord.length : ℝ)
      ≤ skLength n :=
  skApproxC_generic_freeGroup_length_le_skLength
    ρ_TI trappedIonGens trappedIonGens_nonempty trappedIonGens_generate
    baseFinder h_bf_length n U

/-- **Read-Rezayi `SU(2)_5` concrete length bound at any level**. -/
theorem skApproxC_generic_readRezayiK5_length_le_skLength
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 2))
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    ((skApproxC_generic readRezayiK5GeneratingSet baseFinder n U).toWord.length : ℝ)
      ≤ skLength n :=
  skApproxC_generic_freeGroup_length_le_skLength
    ρ_RR5 readRezayiK5Gens readRezayiK5Gens_nonempty readRezayiK5Gens_generate
    baseFinder h_bf_length n U

/-- **Read-Rezayi `SU(2)_7` concrete length bound at any level**. -/
theorem skApproxC_generic_readRezayiK7_length_le_skLength
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 2))
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    ((skApproxC_generic readRezayiK7GeneratingSet baseFinder n U).toWord.length : ℝ)
      ≤ skLength n :=
  skApproxC_generic_freeGroup_length_le_skLength
    ρ_RR7 readRezayiK7Gens readRezayiK7Gens_nonempty readRezayiK7Gens_generate
    baseFinder h_bf_length n U

/-! ## 3. Per-alphabet 3-conjunct bundled-strict headlines (CONDITIONAL on `h_bf_length`)

Each headline conjoins the existing 2-conjunct unconditional headline
output with the concrete-length-bound third conjunct, taking
`h_bf_length` as an explicit hypothesis. -/

/-- **Phase 6x Track M.4 — Clifford+T 3-conjunct headline**.

For any length-bounded Clifford+T base finder `bf`, target `U ∈ SU(2)`,
and precision `ε ∈ (0, ε₀]`, the constructive Dawson-Nielsen
Solovay-Kitaev compiler returns a `FreeGroup (Fin 2)` word with:

  - **Error**: `‖ρ_CliffT (compile U ε) - U‖ ≤ ε`.
  - **Abstract length**: `skLength (skLevel_polylog ε) ≤ skLengthConst · …`.
  - **Concrete length**: `((compile U ε).toWord.length : ℝ) ≤ skLength (skLevel_polylog ε)`.

All three bounds at the SAME algorithmic compile level
`skLevel_polylog ε`. Closes the substrate-vs-headline gap (Phase 6x
retrospective addendum anti-pattern #4) for Clifford+T. -/
theorem solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_concrete
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 2))
    (h_bf_approx : BaseFinder_approximates_within cliffordTGeneratingSet baseFinder (2 * ε₀))
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((cliffordTGeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              cliffordTGeneratingSet baseFinder U ε) :
          ↥(specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent ∧
    ((solovayKitaev_compile_strict_constructive_generic
        cliffordTGeneratingSet baseFinder U ε).toWord.length : ℝ)
        ≤ skLength (skLevel_polylog ε) := by
  -- First two conjuncts: the existing 2-conjunct UNCONDITIONAL headline.
  have h12 := solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional
    cliffordTGeneratingSet baseFinder h_bf_approx U ε hε_pos hε_le
  -- Third conjunct: the new concrete length bound at level skLevel_polylog ε.
  -- `solovayKitaev_compile_strict_constructive_generic gs bf U ε
  --   = skApproxC_generic gs bf (skLevel_polylog ε) U` by definition.
  have h3 := skApproxC_generic_cliffordT_length_le_skLength
    baseFinder h_bf_length (skLevel_polylog ε) U
  exact ⟨h12.1, h12.2, h3⟩

/-- **Clifford+T 3-conjunct headline AT THE ACTUAL Dawson–Nielsen compiler** (the honest
output-word-length form).

Instantiates the generic 3-conjunct headline at the project's actual unconditional Clifford+T base
finder `cliffordTBaseFinder cliffordT_v4_witness_discharged`. The **error** and **abstract-length**
conjuncts are UNCONDITIONAL (the base-finder approximation is discharged via
`cliffordTBaseFinder_approximates_within_two_ε₀`); the **concrete output-word-length** conjunct
`((compile U ε).toWord.length : ℝ) ≤ skLength (skLevel_polylog ε)` is conditional on the SINGLE
explicit hypothesis `h_bf_length : BaseFinder_length_bounded (cliffordTBaseFinder …)`.

This makes the output-word-length coupling explicit and honest. The shipped `cliffordTBaseFinder` is
the existential ε₀-net finder (`epsilonNet_findNearest_of_witness`, a `Classical.choose` extraction),
which carries NO length control, so `h_bf_length` is genuinely undischarged here (and unprovable for
that finder). Discharging it requires a length-bounded base finder — a constructive finite ε₀-net or
the Ross-Selinger grid-synth finder (Phase 6x Item I / Track T-S′) with ∀-`U` coverage — the same
documented grid-completeness residual that gates Item I's ∀-target completeness. By contrast the
`*_strict_constructive_tight*` headlines bound only `skLength (skLevel_polylog ε)` (the SK
recursion-LEVEL count, which grows polylog), NOT the returned word's length; this theorem supplies the
genuine output-word-length coupling with that single residual hypothesis named. -/
theorem solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_concrete_at_basefinder
    (h_bf_length : BaseFinder_length_bounded
      (cliffordTBaseFinder cliffordT_v4_witness_discharged))
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((cliffordTGeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              cliffordTGeneratingSet
              (cliffordTBaseFinder cliffordT_v4_witness_discharged) U ε) :
          ↥(specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent ∧
    ((solovayKitaev_compile_strict_constructive_generic
        cliffordTGeneratingSet
        (cliffordTBaseFinder cliffordT_v4_witness_discharged) U ε).toWord.length : ℝ)
        ≤ skLength (skLevel_polylog ε) :=
  solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_concrete
    (cliffordTBaseFinder cliffordT_v4_witness_discharged)
    (cliffordTBaseFinder_approximates_within_two_ε₀ cliffordT_v4_witness_discharged)
    h_bf_length U ε hε_pos hε_le

/-- **Phase 6x Track M.4 — Read-Rezayi `SU(2)_5` 3-conjunct headline**. -/
theorem solovayKitaev_dawson_nielsen_quantitative_readRezayiK5_strict_concrete
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 2))
    (h_bf_approx : BaseFinder_approximates_within readRezayiK5GeneratingSet baseFinder (2 * ε₀))
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((readRezayiK5GeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              readRezayiK5GeneratingSet baseFinder U ε) :
          ↥(specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent ∧
    ((solovayKitaev_compile_strict_constructive_generic
        readRezayiK5GeneratingSet baseFinder U ε).toWord.length : ℝ)
        ≤ skLength (skLevel_polylog ε) := by
  have h12 := solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional
    readRezayiK5GeneratingSet baseFinder h_bf_approx U ε hε_pos hε_le
  -- Third conjunct: specialize the generic length bound at level skLevel_polylog ε.
  have h3 := skApproxC_generic_readRezayiK5_length_le_skLength
    baseFinder h_bf_length (skLevel_polylog ε) U
  exact ⟨h12.1, h12.2, h3⟩

/-- **Phase 6x Track M.4 — Read-Rezayi `SU(2)_7` 3-conjunct headline**. -/
theorem solovayKitaev_dawson_nielsen_quantitative_readRezayiK7_strict_concrete
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 2))
    (h_bf_approx : BaseFinder_approximates_within readRezayiK7GeneratingSet baseFinder (2 * ε₀))
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((readRezayiK7GeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              readRezayiK7GeneratingSet baseFinder U ε) :
          ↥(specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent ∧
    ((solovayKitaev_compile_strict_constructive_generic
        readRezayiK7GeneratingSet baseFinder U ε).toWord.length : ℝ)
        ≤ skLength (skLevel_polylog ε) := by
  have h12 := solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional
    readRezayiK7GeneratingSet baseFinder h_bf_approx U ε hε_pos hε_le
  have h3 := skApproxC_generic_readRezayiK7_length_le_skLength
    baseFinder h_bf_length (skLevel_polylog ε) U
  exact ⟨h12.1, h12.2, h3⟩

/-- **Phase 6x Track M.4 — Trapped-ion lift/shift 3-conjunct headline**. -/
theorem solovayKitaev_dawson_nielsen_quantitative_trappedIon_strict_concrete
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 3))
    (h_bf_approx : BaseFinder_approximates_within trappedIonGeneratingSet baseFinder (2 * ε₀))
    (h_bf_length : BaseFinder_length_bounded baseFinder)
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((trappedIonGeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              trappedIonGeneratingSet baseFinder U ε) :
          ↥(specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent ∧
    ((solovayKitaev_compile_strict_constructive_generic
        trappedIonGeneratingSet baseFinder U ε).toWord.length : ℝ)
        ≤ skLength (skLevel_polylog ε) := by
  have h12 := solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional
    trappedIonGeneratingSet baseFinder h_bf_approx U ε hε_pos hε_le
  have h3 := skApproxC_generic_trappedIon_length_le_skLength
    baseFinder h_bf_length (skLevel_polylog ε) U
  exact ⟨h12.1, h12.2, h3⟩

end SKEFTHawking.FKLW.GenericSU2
