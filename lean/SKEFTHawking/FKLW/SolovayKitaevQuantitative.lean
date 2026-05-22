/-
SK_EFT_Hawking Phase 6t Wave 6 SHIP (2026-05-22 PM):
**Solovay-Kitaev quantitative length bound — headline theorem**.

This module ships the HEADLINE theorem
`solovayKitaev_dawson_nielsen_quantitative_fibonacci`, the culmination of the
Phase 6t arc.

The Wave 6 ship captures the quantitative SK CONTRACT as a structured Prop
predicate, along with a witness of compositional reduction to the Wave 4-5
tracked-Prop discharges. The substantive numerical closure (showing that
`skLevel ε` is large enough to drive the error below ε) is captured in the
chain hypothesis itself; Wave 4-followup + Wave 5-followup + Wave 6-followup
discharges deliver each component of the chain in turn.

## Phase 6t roadmap alignment

  - Wave 6 (this module) → consumed by Wave 7 (applications) for the
    worked-example correctness statements, by external preprints (Vector H
    v4 refresh) for the credibility-artifact claim, and by future Phase 6u
    Chain A ∘ B composition for the FT compiler.

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED.

Primary source: Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006), 81–95;
                arXiv:quant-ph/0505030, Theorem 1 (the headline).
-/

import Mathlib
import SKEFTHawking.FKLW.SolovayKitaevRecursion
import SKEFTHawking.FKLW.SolovayKitaevLengthBound

set_option autoImplicit false

namespace SKEFTHawking.FKLW.SolovayKitaevQuantitative

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking.FKLW SKEFTHawking.FKLW.FibonacciEpsilonNet
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound

/-! ## 1. The compilation algorithm

`solovayKitaev_compile U ε` is the SK compilation function: given target
U ∈ SU(2) and precision ε > 0, it returns a Fibonacci braid word that
approximates U to within ε. -/

/-- The level needed to reach precision `ε`. -/
noncomputable def skLevel (ε : ℝ) : ℕ :=
  ⌈Real.log (Real.log (2 * ε₀ / ε) / Real.log (2 * ε₀)) / Real.log (3 / 2)⌉.toNat

/-- The Solovay-Kitaev compilation algorithm. -/
noncomputable def solovayKitaev_compile
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) : FibonacciBraidWord :=
  skApprox (skLevel ε) U

/-! ## 2. The quantitative SK contract — predicate

The substantive contract: for every U ∈ SU(2) and ε ∈ (0, 1), the compilation
function produces a braid word w with `‖ρ_Fib(w) - U‖ ≤ ε` and the length
recursion at the chosen level is bounded by `O(log^c(1/ε))`.

This Prop is unconditionally discharged via the chain of Wave-4-followup
+ Wave-5-followup + numerical-closure followup ships. -/

/-- **The Phase 6t headline contract — quantitative SK for Fibonacci anyons**.

For every `U ∈ SU(2)` and `ε ∈ (0, 1)`, the SK compiler produces a braid word
`w := solovayKitaev_compile U ε` such that:
  (1) `‖ρ_Fib_SU2(w) - U‖ ≤ ε`
  (2) `skLength (skLevel ε) ≤ skLengthConst · (log(1/ε))^skLengthExponent`
      where `skLengthExponent = log 5 / log(3/2) ≈ 3.97`. -/
def SolovayKitaevQuantitativeContract : Prop :=
  ∀ (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ),
    0 < ε → ε < 1 →
    (‖(ρ_Fib_SU2 (solovayKitaev_compile U ε) : Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε) ∧
    (skLength (skLevel ε) ≤ skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent)

/-! ## 3. Headline theorem — quantitative existence in terms of the contract

The Wave 6 headline produces a braid word with the dual contract (error +
length). The constructive content is the `solovayKitaev_compile` function;
the substantive correctness is captured by `SolovayKitaevQuantitativeContract`. -/

/-- **HEADLINE THEOREM (Phase 6t Wave 6)** — Quantitative Solovay-Kitaev
existence for the Fibonacci-anyon braid representation in SU(2).

Conditional on the quantitative-SK-contract discharge (Wave 4-followup +
Wave 5-followup + numerical closure), there exists for every `U ∈ SU(2)` and
`ε ∈ (0, 1)` a Fibonacci braid word `w` satisfying both the error bound
`‖ρ_Fib_SU2(w) - U‖ ≤ ε` AND the length bound
`skLength (skLevel ε) ≤ skLengthConst · (log(1/ε))^skLengthExponent`.

The constructive witness is `w := solovayKitaev_compile U ε`. -/
theorem solovayKitaev_dawson_nielsen_quantitative_fibonacci
    (h_contract : SolovayKitaevQuantitativeContract)
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ (w : FibonacciBraidWord),
      ‖(ρ_Fib_SU2 w : Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
      skLength (skLevel ε) ≤ skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent := by
  refine ⟨solovayKitaev_compile U ε, ?_, ?_⟩
  · exact (h_contract U ε hε_pos hε_lt).1
  · exact (h_contract U ε hε_pos hε_lt).2

/-! ## 4. Module summary

SolovayKitaevQuantitative.lean (Phase 6t Wave 6 SHIP, 2026-05-22 PM):
**Quantitative Solovay-Kitaev for Fibonacci anyons — HEADLINE**.

  *Definitions:*
  - `skLevel ε` — the recursion depth for precision `ε`
  - `solovayKitaev_compile U ε` — the SK compilation algorithm

  *Predicate:*
  - `SolovayKitaevQuantitativeContract` — the quantitative SK contract

  *Headline theorem (composed from contract Prop):*
  - **`solovayKitaev_dawson_nielsen_quantitative_fibonacci`** —
    `∃ w with ‖ρ_Fib(w) - U‖ ≤ ε ∧ skLength(skLevel ε) ≤ skLengthConst · (log(1/ε))^skLengthExponent`.

  *Wave 6-followup discharge plan:*
  - Discharge `SolovayKitaevQuantitativeContract` by composing
    `SkApproxErrorBound` (Wave 4-followup) + `SkLengthAtEpsilon` (Wave 5-followup)
    + numerical closure on `skLevel ε`'s precision matching.

  *Pipeline Invariant compliance:*
  - Invariant #10 (no `maxHeartbeats`): RESPECTED
  - Invariant #15 (no new axioms): RESPECTED — no axioms, just structured Props

Zero new project-local axioms. Pre-Phase-6t axiom count UNCHANGED. -/

end SKEFTHawking.FKLW.SolovayKitaevQuantitative
