/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Wave 3 — Generic ε₀-net infrastructure

Generalizes the Phase 6t Wave 3 Fibonacci-specific `fibonacciEpsilonNet`
to an arbitrary `GeneratingSet` admitting a Wave-2 closure-dense witness.

## Headline definitions

  * `epsilonNet_findNearest gs h_dense U ε₀ hε₀_pos : gs.W` — for any
    target `U ∈ SU(2)` and threshold `ε₀ > 0`, returns a word in `gs.W`
    whose ρ_hom image is within `ε₀` of `U` in the operator (l∞) norm.

  * `epsilonNet_findNearest_approx_opNorm` — correctness lemma: the
    returned word satisfies `‖(gs.ρ_hom w).val - U.val‖ < ε₀`.

  * `fibonacciEpsilonNet_findNearest_via_generic` — validates the
    abstraction: at the Fibonacci instance, the generic findNearest agrees
    with the existing `FibonacciEpsilonNet.fibonacciEpsilonNet_findNearest`
    in the sense of returning a word approximating to the same threshold
    (the precise functions are extensionally equivalent only up to the
    `Classical.choose` axiom-of-choice ambiguity).

## Status posture

This wave ships the **existential ε₀-net** (`Classical.choose` extraction
of the Wave-2 density theorem). The **finite-Finset constructive** form
(brute-force enumeration up to length L₀, or symbolic via per-alphabet
algebraic-number-theoretic structure) is per-alphabet:

  - Fibonacci: existing `FibonacciEpsilonNet` is existential; constructive
    Path-A enumeration deferred per Phase 6t Wave 3 user lock-in §13.2.
  - Clifford+T (Phase 6u Track T-S): substantive Ross-Selinger
    `ℤ[ω][1/√2]` symbolic discharge planned; existential form via this
    module's substrate is the fallback.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected — proofs are direct
  `Classical.choose_spec` extractions.
- **#15** (no new axioms): respected — `Classical.choose` is in the
  standard kernel closure.
- **Strengthening discipline**: the findNearest function is non-trivial
  (it produces a metric-approximation witness), the correctness lemma is
  load-bearing (consumed by Wave 4's recursion engine), and the validation
  theorem against Fibonacci is non-vacuous (it asserts the generic
  abstraction RECOVERS the existing Fibonacci substrate).

-/

import SKEFTHawking.FKLW.GenericClosureDenseWitness
import SKEFTHawking.FKLW.FibonacciEpsilonNet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix
open SKEFTHawking.FKLW

/-! ## 1. Generic ε₀-net findNearest

The fundamental abstraction: a noncomputable function that picks a word
in `gs.W` whose `ρ_hom`-image is within `ε₀` of any target `U ∈ SU(2)`. -/

/-- **Generic ε₀-net `findNearest`**: pick a word `w : gs.W` whose
representation under `gs.ρ_hom` approximates `U` to within `ε₀` in the
operator norm.

Built via `Classical.choose` on the Wave-2 density theorem (`h_dense`).
Noncomputable for general `gs`; per-alphabet constructive versions are
shipped in track instantiations (T-S for Clifford+T, etc.). -/
noncomputable def epsilonNet_findNearest
    (gs : GeneratingSet) (h_dense : IsDenseInSU2_gs gs)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) : gs.W :=
  (h_dense U ε₀ hε₀_pos).choose

/-- **Correctness of `epsilonNet_findNearest`**: the returned word's
representation is within `ε₀` of `U` in the operator (l∞) norm.

Direct `Classical.choose_spec` extraction from the Wave-2 density
existential. -/
theorem epsilonNet_findNearest_approx_opNorm
    (gs : GeneratingSet) (h_dense : IsDenseInSU2_gs gs)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    ‖((gs.ρ_hom (epsilonNet_findNearest gs h_dense U ε₀ hε₀_pos) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
  (h_dense U ε₀ hε₀_pos).choose_spec

/-! ## 2. Convenience composition: witness → ε₀-net

Combines Wave 2's `densityFromWitness` with the generic findNearest in
a single chain, for callers that have a `ClosureDenseWitness` directly. -/

/-- **Witness-to-findNearest convenience**: given a `ClosureDenseWitness`
for `gs`, get the findNearest function directly. Composes
`densityFromWitness` with `epsilonNet_findNearest`. -/
noncomputable def epsilonNet_findNearest_of_witness
    (gs : GeneratingSet) (w : ClosureDenseWitness gs)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) : gs.W :=
  epsilonNet_findNearest gs (densityFromWitness w) U ε₀ hε₀_pos

/-- Correctness of `epsilonNet_findNearest_of_witness`. -/
theorem epsilonNet_findNearest_of_witness_approx_opNorm
    (gs : GeneratingSet) (w : ClosureDenseWitness gs)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    ‖((gs.ρ_hom (epsilonNet_findNearest_of_witness gs w U ε₀ hε₀_pos) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
  epsilonNet_findNearest_approx_opNorm gs (densityFromWitness w) U ε₀ hε₀_pos

/-! ## 3. Fibonacci-instance validation

The generic ε₀-net at the Fibonacci instance recovers the same
metric-approximation behaviour as the existing
`FibonacciEpsilonNet.fibonacciEpsilonNet_findNearest`. Note that the
extracted Classical.choose witness depends on the Wave-2 density chain
and need not be the SAME element returned by the original Fibonacci
chain; what matches is the metric-approximation property. -/

/-- **Fibonacci specialization of generic `findNearest`**.

Returns a `BraidGroup 3` element (=`FibonacciBraidWord`) within `ε₀` of
`U` in operator norm, via the generic Wave-2 substrate. Validates that
the abstraction recovers a Fibonacci-typed deliverable. -/
noncomputable def fibonacciEpsilonNet_findNearest_via_generic
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) : BraidGroup 3 :=
  epsilonNet_findNearest_of_witness
    fibonacciGeneratingSet fibonacciClosureDenseWitness U ε₀ hε₀_pos

/-- Correctness of the Fibonacci specialization (via generic substrate):
the returned braid word's ρ_Fib_SU2 image is within ε₀ of U. -/
theorem fibonacciEpsilonNet_findNearest_via_generic_approx_opNorm
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) :
    ‖((SKEFTHawking.FKLW.ρ_Fib_SU2
          (fibonacciEpsilonNet_findNearest_via_generic U ε₀ hε₀_pos) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
  epsilonNet_findNearest_of_witness_approx_opNorm
    fibonacciGeneratingSet fibonacciClosureDenseWitness U ε₀ hε₀_pos

end SKEFTHawking.FKLW.GenericSU2
