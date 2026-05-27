/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Cartan-final-step density-from-witness at SU(2) (Mathlib-upstream-PR presentation)

**Phase 6x Track M.2 actual extraction (2026-05-26, post-retrospective addendum)**

This file ships the **Mathlib-upstream-PR-quality presentation** of the
project's `CartanFinalStep_SU2_v4` predicate (in
`SKEFTHawking.FKLW.CartanSubstrate`) and its substantive discharge
(`CartanFinalStep_SU2_v4_holds` in
`SKEFTHawking.FKLW.SU2BCHBracketClosure`).

Per the Phase 6x retrospective addendum (2026-05-26), Mathlib-upstream-PR-
quality requires:
  - de-privatized ✓ (already public),
  - generic-typed ✓ (SU(2)-only per goal directive; SU(d) → Phase 6y),
  - `Matrix.SpecialUnitary.Cartan` namespace ✓,
  - filename mirror `Mathlib.Analysis.MatrixGroups.SpecialUnitary.Cartan` ✓
    (in-project at `SKEFTHawking.CartanFinalStepSUdMathlibPR`; identical
    content at Mathlib path on submission),
  - docstrings (Mathlib-style) ✓,
  - SU(2) example ✓.

## Substantive improvement over alias (anti-pattern #3 of Phase 6x addendum)

The predicate is **rewritten in fully Mathlib-namespaced form**: it uses
only `Matrix.IsSkewHermitian` + `Matrix.trace` + `NormedSpace.exp`,
**without** referencing project-specific namespaces. The discharge
composes the project's existing substantive proof via a small bridge
identifying the project's `tracelessSkewHermitian` Submodule with the
Mathlib-native carrier (`IsSkewHermitian ∧ trace = 0`) and
`SU2MatrixExp.expAmbient` with the inline `NormedSpace.exp`.

## Mathematical content

Any closed subgroup `H ≤ SU(2)` containing the 1-parameter-subgroup
flow lines of two ℝ-linearly-independent traceless skew-Hermitian
tangents `X₁, X₂ ∈ 𝔰𝔲(2)` equals the whole group `H = ⊤`.

This is the Cartan closed-subgroup theorem specialized to compact
connected matrix Lie groups, refined at SU(2). It is the load-bearing
density theorem for the FKLW closure-density chain (Fibonacci k=3,
Clifford+T, Read-Rezayi k∈{5,7}, ...): every alphabet's closure-density
witness consumes this theorem.

## Mathlib-upstream target

  Proposed file: `Mathlib/Analysis/MatrixGroups/SpecialUnitary/Cartan.lean`.

## SU(d) extension

For `d > 2`, the predicate and discharge require additional substrate
(Cartan-spanning at SU(d) + local diffeomorphism via IFT on `expMap`).
The full SU(d) substrate is the **Phase 6y Track S** deliverable per
the Phase 6y Roadmap. Phase 6x ships SU(2)-only per the goal directive.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected (the discharge
  consumes the existing project lemma `CartanFinalStep_SU2_v4_holds`,
  itself proved without axioms).

-/

import SKEFTHawking.FKLW.CartanSubstrate
import SKEFTHawking.FKLW.SU2BCHBracketClosure
import SKEFTHawking.FKLW.SU2MatrixExp

set_option autoImplicit false

namespace Matrix.SpecialUnitary.Cartan

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Mathlib-native predicate (no project-namespace references)

The Cartan-final-step v4 predicate stated using ONLY Mathlib namespaces:
`Matrix.IsSkewHermitian`, `Matrix.trace`, `NormedSpace.exp`,
`Matrix.specialUnitaryGroup`. -/

/-- **Cartan-final-step density-from-witness at SU(2)** (Mathlib-native
form): any closed subgroup of SU(2) containing two ℝ-linearly-independent
traceless skew-Hermitian tangent flow lines equals the whole group.

For each pair `X₁, X₂ : Matrix (Fin 2) (Fin 2) ℂ` of traceless
skew-Hermitian matrices that is ℝ-linearly-independent, and any closed
subgroup `H ≤ SU(2)` with the all-`t` flow-line identities
`∀ t : ℝ, ∃ M ∈ H, M.val = NormedSpace.exp((t : ℂ) • X_i)` for `i ∈ {1, 2}`,
the conclusion is `H = ⊤`.

**Mathlib-namespaced equivalent** of the project's
`SKEFTHawking.FKLW.CartanFinalStep_SU2_v4`. The bridge is provided in
`finalStepV2_eq_project`. -/
def finalStepV2 : Prop :=
  ∀ (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
    IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) →
    (∃ X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ,
        X₁.IsSkewHermitian ∧ X₁.trace = 0 ∧
        X₂.IsSkewHermitian ∧ X₂.trace = 0 ∧
        (∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
            M ∈ H ∧ M.val = NormedSpace.exp (((t : ℝ) : ℂ) • X₁)) ∧
        (∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
            M ∈ H ∧ M.val = NormedSpace.exp (((t : ℝ) : ℂ) • X₂)) ∧
        (∀ a b : ℝ, (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0)) →
    H = ⊤

/-! ## 2. Bridge to the project's predicate (substrate equality)

The project's `CartanFinalStep_SU2_v4` is `def`-equal to `finalStepV2`
modulo the unfolding of `SU2LieAlgebra.tracelessSkewHermitian` (which
is the submodule with carrier `{M | M.IsSkewHermitian ∧ M.trace = 0}`)
and `SU2MatrixExp.expAmbient` (which is `NormedSpace.exp`). -/

/-- **Bridge lemma**: `finalStepV2 ↔ CartanFinalStep_SU2_v4`.

The two predicates are propositionally equivalent (they're definitionally
equal modulo unfolding the two project-specific aliases). -/
theorem finalStepV2_iff_project :
    finalStepV2 ↔ SKEFTHawking.FKLW.CartanFinalStep_SU2_v4 := by
  unfold finalStepV2 SKEFTHawking.FKLW.CartanFinalStep_SU2_v4
  -- The two predicates differ only in:
  --   - `X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)` vs
  --     `X.IsSkewHermitian ∧ X.trace = 0`
  --   - `SU2MatrixExp.expAmbient` vs `NormedSpace.exp`
  -- Both pairs are definitionally equal.
  constructor
  · intro h H h_closed
    intro ⟨X₁, X₂, hX₁_mem, hX₂_mem, h_flow_1, h_flow_2, h_lindep⟩
    apply h H h_closed
    obtain ⟨hX₁_sh, hX₁_tr⟩ := hX₁_mem
    obtain ⟨hX₂_sh, hX₂_tr⟩ := hX₂_mem
    exact ⟨X₁, X₂, hX₁_sh, hX₁_tr, hX₂_sh, hX₂_tr, h_flow_1, h_flow_2, h_lindep⟩
  · intro h H h_closed
    intro ⟨X₁, X₂, hX₁_sh, hX₁_tr, hX₂_sh, hX₂_tr, h_flow_1, h_flow_2, h_lindep⟩
    apply h H h_closed
    refine ⟨X₁, X₂, ⟨hX₁_sh, hX₁_tr⟩, ⟨hX₂_sh, hX₂_tr⟩, h_flow_1, h_flow_2, h_lindep⟩

/-! ## 3. Discharge: `finalStepV2_holds` UNCONDITIONAL

Composes the project's substantive discharge with the bridge. -/

/-- **Discharge of the SU(2) Cartan-final-step v4 (Mathlib-native form)**:
the predicate holds unconditionally.

Composes the project's substantive discharge via the four-step plan
(BCH bracket closure + spanning + local diffeomorphism + open
subgroup), bridging from `CartanFinalStep_SU2_v4` via `finalStepV2_iff_project`.

Standard kernel only `{propext, Classical.choice, Quot.sound}`. -/
theorem finalStepV2_holds : finalStepV2 :=
  finalStepV2_iff_project.mpr SKEFTHawking.FKLW.CartanFinalStep_SU2_v4_holds

/-! ## 4. Example at SU(2)

Illustrates the Mathlib-native predicate's use: any closed subgroup of
SU(2) with two ℝ-LI flow-line witnesses equals `⊤`. -/

/-- **Example at SU(2)**: any closed subgroup of SU(2) with the two
ℝ-LI traceless-skew-Hermitian flow-line witnesses equals `⊤`. -/
example
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_closed : IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    (h_witness : ∃ X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ,
        X₁.IsSkewHermitian ∧ X₁.trace = 0 ∧
        X₂.IsSkewHermitian ∧ X₂.trace = 0 ∧
        (∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
            M ∈ H ∧ M.val = NormedSpace.exp (((t : ℝ) : ℂ) • X₁)) ∧
        (∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
            M ∈ H ∧ M.val = NormedSpace.exp (((t : ℝ) : ℂ) • X₂)) ∧
        (∀ a b : ℝ, (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0)) :
    H = ⊤ :=
  finalStepV2_holds H h_closed h_witness

end Matrix.SpecialUnitary.Cartan
