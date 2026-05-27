/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Range/filter sum equivalence for partial sums

For a real-valued `a : Fin (n + 1) → ℝ` and `p : Fin n`:

  `∑_{j ∈ range (p.val + 1)} (if h : j < n + 1 then a ⟨j, h⟩ else 0)
   = ∑_{j ∈ univ.filter (· ≤ p.castSucc)} a j`

This bridges the `Finset.range`-based partial sum (used internally by
`partialSumCoeff`) to the `Finset.filter`-based partial sum (used by
Session 25's `partial_sums_nonneg_of_decreasing_traceless`). Both sums
have `p.val + 1` terms summing the same values.

## Substantive content shipped

  * `sum_range_eq_sum_filter_le_castSucc` — the range ↔ filter equivalence.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (range/filter
bridge for connecting S25's natural form to S24's partialSumCoeff form).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Finset

/-- **Range/filter sum equivalence**: for real `a : Fin (n + 1) → ℝ` and
`p : Fin n`,

  `∑_{j ∈ range (p.val + 1)} (if h : j < n + 1 then a ⟨j, h⟩ else 0)
   = ∑_{j ∈ univ.filter (· ≤ p.castSucc)} a j`. -/
theorem sum_range_eq_sum_filter_le_castSucc {n : ℕ}
    (a : Fin (n + 1) → ℝ) (p : Fin n) :
    (∑ j ∈ Finset.range (p.val + 1),
      (if h : j < n + 1 then a ⟨j, h⟩ else 0)) =
      ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).filter (· ≤ p.castSucc), a j := by
  -- Use Finset.sum_bij with bijection range → filter.
  apply Finset.sum_bij
    (fun (j : ℕ) (hj : j ∈ Finset.range (p.val + 1)) =>
      (⟨j, by have := p.isLt; rw [Finset.mem_range] at hj; omega⟩ : Fin (n + 1)))
  · -- Membership in filter: j ≤ p.castSucc.
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show (⟨j, _⟩ : Fin (n + 1)).val ≤ p.castSucc.val
    show j ≤ p.val
    omega
  · -- Injectivity.
    intro j₁ _ j₂ _ h_eq
    have := congr_arg Fin.val h_eq
    simpa using this
  · -- Surjectivity.
    intro j hj
    rw [Finset.mem_filter] at hj
    refine ⟨j.val, ?_, ?_⟩
    · rw [Finset.mem_range]
      have h_le : j ≤ p.castSucc := hj.2
      show j.val < p.val + 1
      have : j.val ≤ p.val := by
        have h_val_le : j.val ≤ p.castSucc.val := h_le
        simpa using h_val_le
      omega
    · apply Fin.ext; rfl
  · -- Value preservation: a ⟨j, _⟩ = a (Fin.mk j _).
    intro j hj
    rw [Finset.mem_range] at hj
    have hj_lt : j < n + 1 := by have := p.isLt; omega
    rw [dif_pos hj_lt]

end SKEFTHawking.FKLW.GenericSUd
