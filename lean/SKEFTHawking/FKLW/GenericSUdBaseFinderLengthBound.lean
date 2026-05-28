/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Length-bounded baseFinder from constructive ε-net

Shows that the constructive ε-net's `findNearestInCover_SUd` output is
length-bounded by the maximum word length over the cover Finset. This
discharges `BaseFinder_length_bounded_sud_param` (Session 53 predicate)
given any per-alphabet finite cover.

Composes:
  * `findNearestInCover_SUd_mem_cover` (Phase 6y T-X′.3 substrate)
  * `Finset.le_sup` (Mathlib finite-Finset max)
  * `BaseFinder_length_bounded_sud_param` (Session 53 predicate)

## Substantive content shipped

  * `maxWordLengthInCover_sud` — max word length over a Finset gs.W (via Finset.sup)
  * `findNearestInCover_SUd_length_le_maxWordLengthInCover` — bound theorem
  * `findNearestInCover_SUd_baseFinder_length_bounded` —
    `BaseFinder_length_bounded_sud_param` discharge from constructive ε-net

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — length-bounded baseFinder
from constructive ε-net (substrate for T-A1′.5/T-A2′.5 cascade unblock).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdConstructiveEpsilonNet
import SKEFTHawking.FKLW.GenericSUdConcreteWordLengthBound

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Max word length over a Finset -/

/-- **Max word length over a Finset of gs.W elements** (parametric in
wordLength function). -/
noncomputable def maxWordLengthInCover_sud {d : ℕ} {gs : GeneratingSet d}
    (wordLength : gs.W → ℕ) (cover : Finset gs.W) : ℕ :=
  cover.sup wordLength

/-! ## 2. Bound theorem -/

/-- **`findNearestInCover_SUd` word length is bounded by cover max**.

For any U ∈ SU(d), the wordLength of `findNearestInCover_SUd` output is
≤ `maxWordLengthInCover_sud wordLength cover`. -/
theorem findNearestInCover_SUd_length_le_maxWordLengthInCover
    {d : ℕ} [Nonempty (Fin d)] (gs : GeneratingSet d)
    (h_dense : IsDenseInSUd_gs gs)
    (wordLength : gs.W → ℕ)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    wordLength (findNearestInCover_SUd gs h_dense ε hε_pos U) ≤
      maxWordLengthInCover_sud wordLength
        (constructiveEpsilonCover_SUd gs h_dense ε hε_pos) := by
  unfold maxWordLengthInCover_sud
  apply Finset.le_sup
  exact findNearestInCover_SUd_mem_cover gs h_dense ε hε_pos U

/-! ## 3. BaseFinder_length_bounded_sud_param discharge -/

/-- **`BaseFinder_length_bounded_sud_param` discharge** for the constructive
ε-net baseFinder.

Given a generating set at SU(n+2), density witness, wordLength function,
and ε > 0, the `findNearestInCover_SUd ... ε` baseFinder satisfies the
length-bounded predicate at `N₀ := maxWordLengthInCover_sud wordLength cover`. -/
theorem findNearestInCover_SUd_baseFinder_length_bounded
    {n : ℕ} (gs : GeneratingSet (n + 2)) (h_dense : IsDenseInSUd_gs gs)
    (wordLength : gs.W → ℕ)
    (ε : ℝ) (hε_pos : 0 < ε) :
    BaseFinder_length_bounded_sud_param
      ((maxWordLengthInCover_sud wordLength
        (constructiveEpsilonCover_SUd gs h_dense ε hε_pos) : ℕ) : ℝ)
      wordLength
      (fun U => findNearestInCover_SUd gs h_dense ε hε_pos U) := by
  intro U
  exact_mod_cast findNearestInCover_SUd_length_le_maxWordLengthInCover
    gs h_dense wordLength ε hε_pos U

end SKEFTHawking.FKLW.GenericSUd
