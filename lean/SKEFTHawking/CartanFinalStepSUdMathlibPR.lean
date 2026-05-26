/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Cartan-final-step density-from-witness at SU(2) (Mathlib-upstream-PR presentation)

Phase 6x Track M.2 ships a Mathlib-upstream-PR-ready presentation of
the project's `CartanFinalStep_SU2_v4` predicate (in
`SKEFTHawking.FKLW.CartanSubstrate`) and its substantive discharge
(`CartanFinalStep_SU2_v4_holds` in
`SKEFTHawking.FKLW.SU2BCHBracketClosure`).

## Headline

  * `Matrix.SpecialUnitary.Cartan.finalStepV2` — Mathlib-namespace
    presentation of the predicate.
  * `Matrix.SpecialUnitary.Cartan.finalStepV2_holds` — the discharge,
    consuming the project's existing substantive proof.

## Mathematical content

Any closed subgroup `H ≤ SU(2)` containing the 1-parameter-subgroup
flow lines of two ℝ-linearly-independent traceless skew-Hermitian
tangents `X₁, X₂ ∈ 𝔰𝔲(2)` equals the whole group `H = ⊤`.

This is the Cartan closed-subgroup theorem specialized to compact
connected matrix Lie groups, refined at SU(2). It is the load-bearing
density theorem for the FKLW closure-density chain (Fibonacci k=3,
Clifford+T, Read-Rezayi k∈{5,7}, ...): every alphabet's closure-density
witness consumes this theorem.

The discharge composes four steps:

  1. **BCH bracket closure (Trotter limit)** via the cubic estimate
     `Matrix.BCH.bchOrder2Cubic` (Phase 6x M.1, generic over d).
     Derives `exp(ℝ·[X₁, X₂]) ⊆ H`.

  2. **Spanning**: `{X₁, X₂, [X₁, X₂]}` is a basis of `𝔰𝔲(2)` whenever
     `X₁, X₂` are ℝ-LI (standard linear algebra).

  3. **Local diffeomorphism `𝔰𝔲(2) → SU(2)` near 1** via the project's
     `SU2_nhd_one_covered_by_exp_ts` (Bloch-sphere parametrization).

  4. **Open subgroup containing 1 in its interior ⟹ `⊤`** via the
     project's `SU2_subgroup_eq_top_of_one_mem_interior` (generic
     topological group fact).

## Mathlib-upstream target

Proposed file: `Mathlib/Analysis/MatrixGroups/SpecialUnitary/Cartan.lean`.

## SU(d) extension (Phase 6x Track T-A2.0)

For `d > 2`, the predicate and discharge require additional substrate:

  - **(d²−1)-tangent spanning**: generalize from the SU(2) two-tangent
    + bracket-closure form to a (d²−1)-tangent linearly-independent
    spanning condition, or equivalently a Lie-theoretic generation
    condition (two-tangent suffices for generic pairs in compact simple
    Lie groups; in SU(d) for d > 2 this requires verifying Lie closure).

  - **Local diffeomorphism `𝔰𝔲(d) → SU(d)`**: generalize from the
    SU(2)-Bloch-sphere argument to the inverse function theorem applied
    to `expMap : 𝔰𝔲(d) → SU(d)` at `0`. Mathlib's `NormedSpace.exp` and
    `HasStrictFDerivAt.exp` provide the substrate (the derivative of
    `exp` at `0` is the identity continuous linear map, so IFT applies).

The full SU(d) substrate is the Phase 6x Track T-A2.0 deliverable
(coordinated explicitly with M.2 per the Phase 6x Roadmap).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected (the discharge
  consumes the existing project lemma `CartanFinalStep_SU2_v4_holds`,
  itself proved without axioms).

-/

import SKEFTHawking.FKLW.CartanSubstrate
import SKEFTHawking.FKLW.SU2BCHBracketClosure
import SKEFTHawking.MatrixBCHCubicMathlibPR

set_option autoImplicit false

namespace Matrix.SpecialUnitary.Cartan

open Matrix SKEFTHawking.FKLW

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Cartan-final-step density-from-witness at SU(2)**: any closed
subgroup of SU(2) containing two ℝ-linearly-independent traceless
skew-Hermitian tangent flow lines equals the whole group.

For each pair `X₁, X₂ ∈ 𝔰𝔲(2) := tracelessSkewHermitian (Fin 2) ⊆
Matrix (Fin 2) (Fin 2) ℂ` that is ℝ-linearly-independent, and any
closed subgroup `H ≤ SU(2)` with the all-`t` flow-line identities
`∀ t : ℝ, ∃ M ∈ H, M.val = exp((t : ℂ) • X_i)` for `i ∈ {1, 2}`,
the conclusion is `H = ⊤`.

Mathlib-PR alias for `SKEFTHawking.FKLW.CartanFinalStep_SU2_v4`. -/
def finalStepV2 : Prop := SKEFTHawking.FKLW.CartanFinalStep_SU2_v4

/-- **Discharge of the SU(2) Cartan-final-step v4**: the predicate
holds unconditionally.

Composes the project's substantive discharge via the four-step plan
described in the module docstring (BCH bracket closure + spanning +
local diffeomorphism + open subgroup). Mathlib-PR-ready alias for the
project's `CartanFinalStep_SU2_v4_holds`. -/
theorem finalStepV2_holds : finalStepV2 :=
  SKEFTHawking.FKLW.CartanFinalStep_SU2_v4_holds

/-- Illustrative example: any closed subgroup of SU(2) with the two
ℝ-LI flow-line witnesses equals `⊤`. -/
example
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_closed : IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    (h_witness : ∃ X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ,
        X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) ∧
        X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) ∧
        (∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
            M ∈ H ∧ M.val
            = SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • X₁)) ∧
        (∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
            M ∈ H ∧ M.val
            = SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • X₂)) ∧
        (∀ a b : ℝ, (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0)) :
    H = ⊤ :=
  finalStepV2_holds H h_closed h_witness

end Matrix.SpecialUnitary.Cartan
