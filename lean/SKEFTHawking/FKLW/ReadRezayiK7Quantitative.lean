/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-B.5.3-T-B.5.5 — Read-Rezayi SU(2)_7 ε₀-net, calibration, bundled-strict headline

Composes the Phase 6u substrate (Waves 1-6 + Wave 4b) with the Phase 6x
Track T-B.5 substrate (`ReadRezayiK7GeneratingSet` through
`ReadRezayiK7V4WitnessUnconditional`) into the canonical Read-Rezayi
SU(2)_7 bundled-strict Solovay-Kitaev headline.

The Phase 6u Track T-S template is mirrored exactly, with:
  - `cliffordTGeneratingSet` → `readRezayiK7GeneratingSet`
  - `cliffordT_v4_witness_tracked` → `rr7_v4_witness_tracked`
  - `cliffordTBaseFinder` → `rr7BaseFinder`
  - Niven-on-π/8 obstruction (Clifford+T) → Chebyshev-cubic-on-π/9
    obstruction (SU(2)_7) — discharged in `ReadRezayiK7InfiniteOrder.lean`.

## Headline definitions

  * **T-B.5.3** `rr7BaseFinder` — existential ε₀-net via T-B.5.2's
    unconditional density.

  * **T-B.5.4** `rr7BaseFinder_approximates_within_two_ε₀` +
    `rr7_calibration_holds` — calibration discharge via Wave 4b's
    generic helper.

  * **T-B.5.5** `solovayKitaev_dawson_nielsen_quantitative_rr7_strict_constructive_tight`
    — bundled-strict SU(2)_7 headline. UNCONDITIONAL (T-B.5.2's tracked
    Prop is substantively discharged in
    `ReadRezayiK7V4WitnessUnconditional.lean`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.

-/

import SKEFTHawking.FKLW.ReadRezayiK7ClosureDenseWitness
import SKEFTHawking.FKLW.ReadRezayiK7V4WitnessUnconditional
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

/-! ## T-B.5.3 — SU(2)_7 base finder (ε₀-net) -/

/-- **SU(2)_7 base finder**.

For any `U ∈ SU(2)`, returns a `FreeGroup (Fin 2)` word whose `ρ_RR7`
image approximates `U` to within `ε₀` in the operator norm. Built via
the generic Wave-3 ε₀-net composed with T-B.5.2's unconditional
closure-density witness. -/
noncomputable def rr7BaseFinder
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : FreeGroup (Fin 2) :=
  epsilonNet_findNearest_of_witness readRezayiK7GeneratingSet
    (rr7ClosureDenseWitness_of_tracked rr7_v4_witness_discharged) U ε₀ ε₀_pos

/-- **Correctness of `rr7BaseFinder`**: the returned word's `ρ_RR7`
image is within `ε₀` of `U`. -/
theorem rr7BaseFinder_approx_opNorm
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖((readRezayiK7GeneratingSet.ρ_hom (rr7BaseFinder U) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
  epsilonNet_findNearest_of_witness_approx_opNorm readRezayiK7GeneratingSet
    (rr7ClosureDenseWitness_of_tracked rr7_v4_witness_discharged) U ε₀ ε₀_pos

/-! ## T-B.5.4 — SU(2)_7 calibration discharge (via Wave 4b) -/

/-- The SU(2)_7 base finder satisfies `BaseFinder_approximates_within` at `2 * ε₀`. -/
theorem rr7BaseFinder_approximates_within_two_ε₀ :
    BaseFinder_approximates_within readRezayiK7GeneratingSet rr7BaseFinder (2 * ε₀) := by
  intro U
  have h1 := rr7BaseFinder_approx_opNorm U
  have h2 : ε₀ < 2 * ε₀ := by
    have := ε₀_pos; linarith
  linarith

/-- **SU(2)_7 super-quadratic calibration (DISCHARGED via Wave 4b)**. -/
theorem rr7_calibration_holds :
    SkApproxCSuperQuadraticBound_generic K_compose
      readRezayiK7GeneratingSet rr7BaseFinder :=
  SkApproxCSuperQuadraticBound_generic_holds readRezayiK7GeneratingSet
    rr7BaseFinder rr7BaseFinder_approximates_within_two_ε₀

/-! ## T-B.5.5 — SU(2)_7 bundled-strict headline -/

/-- **Phase 6x Track T-B.5.5 HEADLINE (UNCONDITIONAL)**.

For any target `U ∈ SU(2)` and precision `ε ∈ (0, ε₀]`, the SU(2)_7
constructive Dawson-Nielsen Solovay-Kitaev compiler returns a
`FreeGroup (Fin 2)` word over `{of 0 ↦ H_SU, of 1 ↦ T_RR7}` with BOTH:

  - **Error**: `‖ρ_RR7 (compile U ε) − U‖ ≤ ε`
  - **Length**: polylog `O(log(1/ε)^skLengthExponent)` word length

Both bounds at the SAME algorithmic compile level `skLevel_polylog ε`.

This is the canonical Read-Rezayi `SU(2)_7` Solovay-Kitaev statement,
instantiated via the Phase 6u generic substrate (Waves 1-6 + Wave 4b)
and the Phase 6x T-B.5 substrate (ReadRezayiK7GeneratingSet through
ReadRezayiK7V4WitnessUnconditional). UNCONDITIONAL — the tracked Prop
`rr7_v4_witness_tracked` is substantively discharged via the cos(π/9)
Chebyshev-cubic Niven obstruction in `ReadRezayiK7InfiniteOrder.lean`
composed with the Pauli case analysis in
`ReadRezayiK7GeneratorCaseAnalysis.lean`. -/
theorem solovayKitaev_dawson_nielsen_quantitative_rr7_strict_constructive_tight
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((readRezayiK7GeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              readRezayiK7GeneratingSet rr7BaseFinder U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent :=
  solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional
    readRezayiK7GeneratingSet rr7BaseFinder
    rr7BaseFinder_approximates_within_two_ε₀
    U ε hε_pos hε_le

end SKEFTHawking.FKLW.GenericSU2
