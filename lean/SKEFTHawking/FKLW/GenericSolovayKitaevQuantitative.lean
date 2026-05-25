/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Wave 6 — Generic bundled-strict Solovay-Kitaev headline

The culmination of Phase 6u's substrate refactor: a single bundled
strict-headline theorem that, given any `GeneratingSet`, any base finder
satisfying the super-quadratic bound, any target `U ∈ SU(2)`, and any
precision `ε ∈ (0, ε₀]`, produces BOTH:

  - **Error bound**: `‖gs.ρ_hom (compile U ε) - U‖ ≤ ε`
  - **Length bound**: `skLength (skLevel_polylog ε) ≤
    skLengthConst · (log(1/ε))^skLengthExponent`

both at the SAME algorithmic compile level. This is the
**alphabet-independent canonical quantitative Solovay-Kitaev statement**
— matches the classical Dawson-Nielsen 2006 form, parametrized over the
generating-set abstraction.

## Headline theorems

  * `solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight`
    — the generic conditional headline, parametric over
    `SkApproxCSuperQuadraticBound_generic`.

  * `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight_via_generic`
    — Fibonacci-instance validation: unconditional via
    `SkApproxCSuperQuadraticBound_generic_fibonacci` (Wave 4a Fibonacci
    bridge). Demonstrates the generic substrate RECOVERS the existing
    Phase 6t Path A Option C result.

## Status

This file's generic headline closes Phase 6u's substrate refactor for
ALL alphabets admitting a base finder + super-quadratic discharge. For
non-Fibonacci alphabets (Track T-S Clifford+T), the per-alphabet
discharge enters through `h_calibration`. The substantive generic
discharge (alphabet-agnostic proof of
`SkApproxCSuperQuadraticBound_generic K_compose`) is shipped in Wave 4b
follow-up.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
- **Strengthening discipline**: the generic headline is non-trivial
  (it conjoins two substantive bounds at the same algorithmic level),
  load-bearing (consumed by all Track instantiations), and validated
  by the Fibonacci specialization.

-/

import SKEFTHawking.FKLW.GenericSolovayKitaevRecursion
import SKEFTHawking.FKLW.GenericSolovayKitaevLengthBound

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound
  SKEFTHawking.FKLW.SolovayKitaevPathA

/-! ## 1. Generic conditional headline (CONDITIONAL on `SkApproxCSuperQuadraticBound_generic`) -/

/-- **Phase 6u Wave 6 GENERIC HEADLINE (conditional)**.

For any `GeneratingSet gs`, any base finder, any super-quadratic bound
discharge, any target `U ∈ SU(2)`, and any precision `ε ∈ (0, ε₀]`,
the generic constructive Dawson-Nielsen Solovay-Kitaev compiler
`solovayKitaev_compile_strict_constructive_generic gs baseFinder U ε`
achieves BOTH:

  - **Error**: `‖gs.ρ_hom (compile U ε) - U‖ ≤ ε`
  - **Length**: polylog `O(log(1/ε)^skLengthExponent)` word length

Both bounds at the SAME algorithmic compile level `skLevel_polylog ε`.

This is the canonical strict-headline form: takes the super-quadratic
bound as a `Prop` hypothesis (`h_calibration`), so per-alphabet
discharges close the headline unconditionally for each alphabet. -/
theorem solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight
    (gs : GeneratingSet)
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → gs.W)
    (h_calibration : SkApproxCSuperQuadraticBound_generic K_compose gs baseFinder)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((gs.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic gs baseFinder U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent := by
  refine ⟨?_, skLength_at_skLevel_polylog_le_generic gs ε hε_pos hε_le⟩
  -- Apply the tracked bound at level skLevel_polylog ε.
  have h_seq_bound :=
    h_calibration (skLevel_polylog ε) U
  -- The ε_seq value at this level is ≤ ε by skLevel_polylog_spec.
  have h_polylog_spec := skLevel_polylog_spec ε hε_pos hε_le
  exact le_trans h_seq_bound h_polylog_spec

/-! ## 2. Fibonacci-instance UNCONDITIONAL headline (via generic substrate)

Closes the generic conditional headline at the Fibonacci instance via the
Wave 4a Fibonacci bridge, recovering Phase 6t Path A Option C's
unconditional ship. -/

/-- **UNCONDITIONAL Fibonacci strict headline via generic substrate**.

Composes `solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight`
with the Fibonacci-instance discharge `SkApproxCSuperQuadraticBound_generic_fibonacci`.

This is the Phase 6u re-derivation of Phase 6t's
`solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight`
through the generic substrate, validating that the abstraction recovers
the canonical Fibonacci result. -/
theorem solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight_via_generic
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((fibonacciGeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              fibonacciGeneratingSet fibonacciBaseFinder U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent :=
  solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight
    fibonacciGeneratingSet fibonacciBaseFinder
    SkApproxCSuperQuadraticBound_generic_fibonacci
    U ε hε_pos hε_le

end SKEFTHawking.FKLW.GenericSU2
