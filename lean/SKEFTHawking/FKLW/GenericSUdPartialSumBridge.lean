/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Partial sum bridge lemmas for real-coerced sequences

For a real-valued sequence `a : Fin (n + 1) → ℝ` coerced to ℂ via `(a · : ℂ)`,
the `partialSumCoeff` (defined as a complex sum) satisfies:

  * **`partialSumCoeff_real_im_zero`**: `(partialSumCoeff (a ·) p).im = 0`
  * **`partialSumCoeff_real_re_eq_real_sum`**: `(partialSumCoeff (a ·) p).re = ∑_j a_j`

These are the bridge lemmas that allow combining Session 24's
`symmetric_balanced_commutator_diagonal_nonneg_partials` discharge
(which requires hypotheses on `(partialSumCoeff (a coerced)).re ≥ 0` and
`.im = 0`) with Session 25's `partial_sums_nonneg_of_decreasing_traceless`
(which works with real partial sums directly).

## Substantive content shipped

  * `partialSumCoeff_real_im_zero`
  * `partialSumCoeff_real_re_eq_finset_range_real_sum`

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (bridge lemmas
between the partialSumCoeff (ℂ-valued) and real partial sums for the
Session 29 final discharge assembly).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDiagonalDecomp

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Finset

/-! ## 1. partialSumCoeff for real-coerced sequence: imaginary part zero -/

/-- **partialSumCoeff for real-coerced sequence has zero imaginary part**. -/
theorem partialSumCoeff_real_im_zero {n : ℕ} (a : Fin (n + 1) → ℝ) (p : Fin n) :
    (partialSumCoeff (fun k => (a k : ℂ)) p).im = 0 := by
  unfold partialSumCoeff
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j _
  -- (if h : j < n + 1 then ((a ⟨j, h⟩ : ℝ) : ℂ) else 0).im = 0
  split_ifs with h
  · -- (↑(a ⟨j, h⟩) : ℂ).im = 0 by Complex.ofReal_im
    exact Complex.ofReal_im _
  · exact Complex.zero_im

/-! ## 2. partialSumCoeff for real-coerced sequence: real part equals real partial sum -/

/-- **partialSumCoeff for real-coerced sequence has real part equal to the
corresponding real partial sum** (range form with same if-then-else
structure as `partialSumCoeff`'s internal form):

  `(partialSumCoeff (a ·) p).re = ∑_{j ∈ range (p.val + 1)}
        (if h : j < n + 1 then a ⟨j, h⟩ else 0)`. -/
theorem partialSumCoeff_real_re_eq_finset_range_real_sum {n : ℕ}
    (a : Fin (n + 1) → ℝ) (p : Fin n) :
    (partialSumCoeff (fun k => (a k : ℂ)) p).re =
      ∑ j ∈ Finset.range (p.val + 1),
        (if h : j < n + 1 then a ⟨j, h⟩ else 0) := by
  unfold partialSumCoeff
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · exact Complex.ofReal_re _
  · exact Complex.zero_re

end SKEFTHawking.FKLW.GenericSUd
