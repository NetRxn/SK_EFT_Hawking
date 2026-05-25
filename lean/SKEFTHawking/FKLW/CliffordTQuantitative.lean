/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Track T-S.3-T-S.5 — Clifford+T ε₀-net, calibration, bundled-strict headline

Composes the Phase 6u substrate (Waves 1-6 + T-S.1 + T-S.2 conditional)
into the Clifford+T-specific bundled-strict headline. All ships in this
module are CONDITIONAL on:

  1. `cliffordT_v4_witness_tracked` (T-S.2): closure-density at Clifford+T.
  2. `SkApproxCSuperQuadraticBound_generic K_compose cliffordTGeneratingSet
     cliffordTBaseFinder` (T-S.4 calibration): super-quadratic discharge
     at the Clifford+T base finder. Discharged by Wave 4b's generic
     discharge `SkApproxCSuperQuadraticBound_generic_holds` once that
     ships (substantive multi-session port of Phase 6t Path A Option C).

## Headline definitions

  * **T-S.3** `cliffordTBaseFinder` — the existential Clifford+T ε₀-net
    findNearest via Classical extraction from T-S.2's conditional density.

  * **T-S.4** `cliffordTBaseFinder_approximates_within_two_ε₀` — the
    Clifford+T base finder satisfies `BaseFinder_approximates_within ... (2·ε₀)`.
    With Wave 4b's `SkApproxCSuperQuadraticBound_generic_holds`, this is the
    UNCONDITIONAL calibration discharge (no tracked Prop needed beyond T-S.2).

  * **T-S.5** `solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight`
    — bundled-strict Clifford+T headline. Conditional ONLY on T-S.2's
    closure-density tracked Prop. Error AND length bound at the SAME
    compile level `skLevel_polylog ε`.

## Discharge plan summary

  - T-S.2 tracked Prop discharge: Phase 6u Session 2+ work (BMPRV 1999 in Lean).
  - T-S.4 calibration: ✅ DISCHARGED via Wave 4b's
    `SkApproxCSuperQuadraticBound_generic_holds`.
  - T-S.5 fully unconditional headline: lands automatically once T-S.2 is
    substantively discharged.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected (only tracked Props, no axioms).
- **Strengthening discipline**: T-S.3 ε₀-net is non-trivial (Classical
  extraction from density); T-S.4 calibration is a load-bearing
  Wave-4-bridge predicate; T-S.5 headline is the substantive composition
  shipped at the Track T-S deliverable level.

-/

import SKEFTHawking.FKLW.CliffordTClosureDenseWitness
import SKEFTHawking.FKLW.GenericEpsilonNet
import SKEFTHawking.FKLW.GenericSolovayKitaevRecursion
import SKEFTHawking.FKLW.GenericSolovayKitaevQuantitative
import SKEFTHawking.FKLW.GenericSolovayKitaevRecursionDischarge

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound

/-! ## T-S.3 — Clifford+T base finder (ε₀-net)

The Wave-3 existential ε₀-net specialized to Clifford+T, conditional on
T-S.2's tracked closure-density witness. -/

/-- **Clifford+T base finder** (conditional on T-S.2's tracked Prop).

For any `U ∈ SU(2)`, returns a `FreeGroup (Fin 2)` word whose `ρ_CliffT`
image approximates `U` to within `ε₀` in the operator norm. Built via
the generic Wave-3 ε₀-net from Wave 2's density-from-witness chain. -/
noncomputable def cliffordTBaseFinder
    (h_tracked : cliffordT_v4_witness_tracked)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : FreeGroup (Fin 2) :=
  epsilonNet_findNearest_of_witness cliffordTGeneratingSet
    (cliffordTClosureDenseWitness_of_tracked h_tracked) U ε₀ ε₀_pos

/-- **Correctness of `cliffordTBaseFinder`**: the returned word's `ρ_CliffT`
image is within `ε₀` of `U` in the operator norm. -/
theorem cliffordTBaseFinder_approx_opNorm
    (h_tracked : cliffordT_v4_witness_tracked)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖((cliffordTGeneratingSet.ρ_hom (cliffordTBaseFinder h_tracked U) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
  epsilonNet_findNearest_of_witness_approx_opNorm cliffordTGeneratingSet
    (cliffordTClosureDenseWitness_of_tracked h_tracked) U ε₀ ε₀_pos

/-! ## T-S.4 — Clifford+T calibration discharge (via Wave 4b)

With Wave 4b's `SkApproxCSuperQuadraticBound_generic_holds` shipped, the
calibration becomes a theorem (no tracked Prop). Hypothesis: only T-S.2's
closure-density witness. -/

/-- The Clifford+T base finder satisfies `BaseFinder_approximates_within`
at `2 * ε₀`. Follows from the `< ε₀ < 2 * ε₀` transitivity. -/
theorem cliffordTBaseFinder_approximates_within_two_ε₀
    (h_tracked : cliffordT_v4_witness_tracked) :
    BaseFinder_approximates_within cliffordTGeneratingSet
      (cliffordTBaseFinder h_tracked) (2 * ε₀) := by
  intro U
  have h1 : ‖((cliffordTGeneratingSet.ρ_hom (cliffordTBaseFinder h_tracked U) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
    cliffordTBaseFinder_approx_opNorm h_tracked U
  have h2 : ε₀ < 2 * ε₀ := by
    have := ε₀_pos; linarith
  linarith

/-- **Clifford+T super-quadratic calibration (DISCHARGED via Wave 4b)**.

`SkApproxCSuperQuadraticBound_generic K_compose cliffordTGS cliffordTBaseFinder`
holds unconditionally, by composing Wave 4b's generic discharge with
`cliffordTBaseFinder_approximates_within_two_ε₀`. The only remaining
hypothesis is T-S.2's `cliffordT_v4_witness_tracked` (which feeds into
the base finder definition). -/
theorem cliffordT_calibration_holds
    (h_tracked : cliffordT_v4_witness_tracked) :
    SkApproxCSuperQuadraticBound_generic K_compose
      cliffordTGeneratingSet (cliffordTBaseFinder h_tracked) :=
  SkApproxCSuperQuadraticBound_generic_holds cliffordTGeneratingSet
    (cliffordTBaseFinder h_tracked)
    (cliffordTBaseFinder_approximates_within_two_ε₀ h_tracked)

/-! ## T-S.5 — Clifford+T bundled-strict headline

Composes T-S.2 (tracked Prop) + T-S.3 (base finder) + T-S.4 (calibration)
with Wave 6 (generic conditional headline) into the canonical Clifford+T
bundled-strict statement. -/

/-- **Phase 6u Track T-S.5 HEADLINE (CONDITIONAL ONLY on T-S.2's tracked Prop)**.

For any target `U ∈ SU(2)` and precision `ε ∈ (0, ε₀]`, the Clifford+T
constructive Dawson-Nielsen Solovay-Kitaev compiler returns a
`FreeGroup (Fin 2)` word over `{of 0 ↦ H_SU, of 1 ↦ T_SU}` with BOTH:

  - **Error**: `‖ρ_CliffT (compile U ε) - U‖ ≤ ε`
  - **Length**: polylog `O(log(1/ε)^skLengthExponent)` word length

Both bounds at the SAME algorithmic compile level `skLevel_polylog ε`.

This is the canonical Clifford+T Solovay-Kitaev statement, matching the
Dawson-Nielsen 2006 form, instantiated via the Phase 6u generic
substrate (Waves 1-6 + Wave 4b). The calibration is discharged
unconditionally by Wave 4b's `SkApproxCSuperQuadraticBound_generic_holds`
through `cliffordT_calibration_holds`; the only remaining tracked
Prop hypothesis is `cliffordT_v4_witness_tracked` (Track T-S.2).

Once T-S.2's tracked Prop is substantively discharged (BMPRV 1999 in
Lean), this headline becomes fully UNCONDITIONAL — the canonical
Clifford+T quantitative Solovay-Kitaev statement, kernel-only. -/
theorem solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight
    (h_tracked : cliffordT_v4_witness_tracked)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((cliffordTGeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              cliffordTGeneratingSet (cliffordTBaseFinder h_tracked) U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent :=
  solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional
    cliffordTGeneratingSet (cliffordTBaseFinder h_tracked)
    (cliffordTBaseFinder_approximates_within_two_ε₀ h_tracked)
    U ε hε_pos hε_le

end SKEFTHawking.FKLW.GenericSU2
