/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.6 substrate — Generic SU(d) SK compile-with-polylog-length-bound data

A typeclass-free data structure capturing the **Solovay-Kitaev compile +
polylog length bound** at SU(d) for a generating set `gs`. Mirrors Phase
6u's `BaseFinder` + length-bound hypothesis but at the headline level: the
caller supplies a compile + bounds, and the predicate-shape headlines
(S.6, T-A1′.5, T-A2′.5) discharge directly.

This decouples the **structural headlines** from the **substantive SK-at-SU(d)
implementation**: consumers/tests/papers can use the headline predicates
immediately by providing concrete `SKCompileWithBounds gs` data, and the
substantive Phase 6y / Phase 6z+ SK-at-SU(d) work ships a concrete instance
later.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 substrate (compile-with-bounds
data structure).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdHeadlineForm

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. `SKCompileWithBounds` for `gs.W` = `FreeGroup α` -/

/-- **SK compile-with-polylog-length-bound data** for a generating set
`gs : GeneratingSet d` whose word type is `FreeGroup α`.

Bundles:
  * `ε₀ : ℝ` (positive threshold below which compile is well-behaved)
  * `c : ℝ` (positive length-bound constant)
  * `compile : ↥SU(d) → ℝ → gs.W` (the SK compile function)
  * Error bound at every `(U, ε)` with `0 < ε ≤ ε₀`
  * Concrete word-length bound `(compile U ε).toWord.length ≤ c · polylog(1/ε)`

This is the **substrate hypothesis** for Phase 6y headlines: T-A1′.5
(trapped-ion) and T-A2′.5 (Clifford+CCZ) discharge via providing a
concrete instance of this structure.

The Dawson-Nielsen 2006 SK polylog exponent `log_2(5) ≈ 2.32` appears via
`Real.log 5 / Real.log 2`. -/
structure SKCompileWithBounds_FreeGroup
    {d : ℕ} {α : Type} [DecidableEq α]
    (gs : GeneratingSet d) (h_eq : gs.W = FreeGroup α) where
  /-- Positive threshold below which compile is well-behaved. -/
  ε₀ : ℝ
  /-- Positive length-bound constant. -/
  c : ℝ
  /-- SK compile function. -/
  compile : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) → ℝ → gs.W
  /-- ε₀ positive. -/
  ε₀_pos : 0 < ε₀
  /-- c positive. -/
  c_pos : 0 < c
  /-- Error bound: compile output is within ε of target. -/
  error : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) (ε : ℝ),
    0 < ε → ε ≤ ε₀ →
    ‖((gs.ρ_hom (compile U ε) : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) -
      (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ε
  /-- Concrete word-length polylog bound. -/
  length : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) (ε : ℝ),
    0 < ε → ε ≤ ε₀ →
    ((h_eq ▸ compile U ε : FreeGroup α).toWord.length : ℝ) ≤
      c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log 2)

/-! ## 2. Discharge of `SolovayKitaevHeadline_FreeGroup_SUd` predicate -/

/-- **`SolovayKitaevHeadline_FreeGroup_SUd` discharge** from a
`SKCompileWithBounds_FreeGroup` data hypothesis.

Directly extracts the `(ε₀, c, compile)` triple and packs it into the
existential predicate satisfying both conjuncts. -/
theorem solovayKitaevHeadline_FreeGroup_SUd_of_SKCompileWithBounds
    {d : ℕ} {α : Type} [DecidableEq α]
    {gs : GeneratingSet d} (h_eq : gs.W = FreeGroup α)
    (data : SKCompileWithBounds_FreeGroup gs h_eq) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq := by
  refine ⟨data.ε₀, data.c, data.compile, data.ε₀_pos, data.c_pos, ?_⟩
  intro U ε hε_pos hε_le
  exact ⟨data.error U ε hε_pos hε_le, data.length U ε hε_pos hε_le⟩

/-! ## 3. `SKCompileWithBounds` for abstract `gs.W` (no FreeGroup) -/

/-- **SK compile-with-polylog-length-bound data** for a generating set
`gs : GeneratingSet d` with abstract `gs.W` (no FreeGroup specialization).

Takes an abstract `wordLength : gs.W → ℕ` as a consumer parameter. -/
structure SKCompileWithBounds_SUd
    {d : ℕ} (gs : GeneratingSet d) (wordLength : gs.W → ℕ) where
  /-- Positive threshold. -/
  ε₀ : ℝ
  /-- Positive length-bound constant. -/
  c : ℝ
  /-- SK compile function. -/
  compile : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) → ℝ → gs.W
  /-- ε₀ positive. -/
  ε₀_pos : 0 < ε₀
  /-- c positive. -/
  c_pos : 0 < c
  /-- Error bound. -/
  error : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) (ε : ℝ),
    0 < ε → ε ≤ ε₀ →
    ‖((gs.ρ_hom (compile U ε) : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) -
      (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ε
  /-- Length polylog bound (abstract wordLength). -/
  length : ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) (ε : ℝ),
    0 < ε → ε ≤ ε₀ →
    (wordLength (compile U ε) : ℝ) ≤
      c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log 2)

/-- **`SolovayKitaevHeadline_SUd` discharge** from abstract
`SKCompileWithBounds_SUd` data. -/
theorem solovayKitaevHeadline_SUd_of_SKCompileWithBounds
    {d : ℕ} {gs : GeneratingSet d} {wordLength : gs.W → ℕ}
    (data : SKCompileWithBounds_SUd gs wordLength) :
    SolovayKitaevHeadline_SUd gs wordLength := by
  refine ⟨data.ε₀, data.c, data.compile, data.ε₀_pos, data.c_pos, ?_⟩
  intro U ε hε_pos hε_le
  exact ⟨data.error U ε hε_pos hε_le, data.length U ε hε_pos hε_le⟩

end SKEFTHawking.FKLW.GenericSUd
