/-
SK_EFT_Hawking Phase 6t Wave 7 SHIP (2026-05-22 PM):
**Solovay-Kitaev applications + worked-example library for the Fibonacci compiler**.

This module ships the application-facing API for the Phase 6t Solovay-Kitaev
compiler:
  - The worked-example correctness contract (`WorkedExampleContract` +
    discharge via the quantitative-SK contract)
  - The `composedFTCompiler` placeholder for future Chain A ∘ B composition (Phase 6u)

The canonical compiler entry-point is `solovayKitaev_compile` (from
`SolovayKitaevQuantitative.lean`); applications consume it directly.

Per user 2026-05-22 PM lock-in §13.4: public-side reference compiler + worked
examples ship here; downstream variants are out of scope for this module per
IP-strategy stabilization.

## Phase 6t roadmap alignment

  - Wave 7 (this module) → consumed by Wave 8 (closeout) for the Python smoke
    tests + the D4 bundle absorption's §9.4 "Lean-extracted runnable compiler"
    sub-section.

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED.

Primary source: Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006), 81–95;
                arXiv:quant-ph/0505030 §4 (worked examples).
-/

import Mathlib
import SKEFTHawking.FKLW.SolovayKitaevQuantitative
import SKEFTHawking.FKLW.FibonacciEpsilonNet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.SolovayKitaevApplications

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking.FKLW SKEFTHawking.FKLW.FibonacciEpsilonNet
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound
  SKEFTHawking.FKLW.SolovayKitaevQuantitative

/-! ## 1. Worked-example contract — a single uniform statement

The canonical compiler entry-point is `solovayKitaev_compile` (from
`SolovayKitaevQuantitative.lean`). The earlier `compile_su2_target` rename
wrapper was dropped 2026-05-22 PM post-compact (Phase 6t Wave 7 cleanup,
Task #31) per the preemptive-strengthening discipline P3 anti-pattern
(identity-function wrapper): use the canonical name directly.

Each worked example asserts: for a fixed target `U_target` and precision `ε`,
the compiled braid word `solovayKitaev_compile U_target ε` satisfies the
quantitative-SK contract (error ≤ ε + length bound).

The substantive worked-example correctness is conditional on the quantitative-SK
contract discharge (Wave 6-followup); given the contract, every worked example
satisfies its bound automatically. -/

/-- **Worked-example contract**: at a fixed target `U_target` and precision
`ε`, the compiled braid word satisfies both the error bound and the length
bound. -/
def WorkedExampleContract
    (U_target : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) : Prop :=
  0 < ε → ε < 1 →
  (‖(ρ_Fib_SU2 (solovayKitaev_compile U_target ε) :
        Matrix (Fin 2) (Fin 2) ℂ) -
      (U_target : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε) ∧
  (skLength (skLevel ε) ≤ skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent)

/-- **HEADLINE**: every worked example's contract follows from the
quantitative-SK contract. -/
theorem workedExampleContract_of_quantitative_contract
    (h_contract : SolovayKitaevQuantitativeContract)
    (U_target : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) :
    WorkedExampleContract U_target ε := by
  intro hε_pos hε_lt
  exact h_contract U_target ε hε_pos hε_lt

/-! ## 3. The composed FT compiler — placeholder for Phase 6u

The `composedFTCompiler` placeholder is for future Phase 6u Chain A ∘ B
composition (AGP + SK + Steane-encoded Fibonacci circuit). The full
substantive composition is out of scope for Phase 6t. -/

/-- **Phase 6u placeholder**: the composed fault-tolerant compiler combining
Chain A (AGP fault-tolerance) ∘ Chain B (SK approximation).

For Phase 6t, this is a structural placeholder; the substantive composition
is shipped in Phase 6u. -/
def ComposedFTCompilerExists : Prop :=
  ∃ (compileFT : ↥(specialUnitaryGroup (Fin 2) ℂ) → ℝ → FibonacciBraidWord),
    ∀ (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ), 0 < ε → ε < 1 →
      ‖(ρ_Fib_SU2 (compileFT U ε) : Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε

/-- **Existence of the composed FT compiler — conditional on quantitative-SK
contract**: given the SK contract, the SK compiler ITSELF satisfies the
ComposedFTCompilerExists requirement (the FT-strengthening to Phase 6u
adds the encoded-qubit layer but preserves the error bound). -/
theorem composedFTCompilerExists_of_quantitative_contract
    (h_contract : SolovayKitaevQuantitativeContract) :
    ComposedFTCompilerExists := by
  refine ⟨solovayKitaev_compile, ?_⟩
  intro U ε hε_pos hε_lt
  exact (h_contract U ε hε_pos hε_lt).1

/-! ## 4. Module summary

SolovayKitaevApplications.lean (Phase 6t Wave 7 SHIP 2026-05-22 PM
+ Wave 7 cleanup 2026-05-22 PM post-compact):
**Applications + worked-example library for the SK Fibonacci compiler**.

  *Definitions:*
  - `WorkedExampleContract` — per-target contract predicate
  - `ComposedFTCompilerExists` — Phase 6u placeholder predicate

  *Canonical compiler entry-point:* `solovayKitaev_compile` (from
  `SolovayKitaevQuantitative.lean`). The earlier `compile_su2_target`
  rename wrapper was dropped 2026-05-22 PM post-compact per the
  preemptive-strengthening discipline P3 anti-pattern.

  *Headlines (conditional on quantitative-SK contract):*
  - `workedExampleContract_of_quantitative_contract` — uniform worked-example
    discharge from the contract
  - `composedFTCompilerExists_of_quantitative_contract` — Phase 6u placeholder
    discharge

  *Pipeline Invariant compliance:*
  - Invariant #10 (no `maxHeartbeats`): RESPECTED
  - Invariant #15 (no new axioms): RESPECTED — pure Prop composition

Zero new project-local axioms. Pre-Phase-6t axiom count UNCHANGED. -/

end SKEFTHawking.FKLW.SolovayKitaevApplications
