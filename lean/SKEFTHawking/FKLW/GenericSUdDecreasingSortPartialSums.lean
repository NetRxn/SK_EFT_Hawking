/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Decreasing-sorted traceless ⟹ partial sums non-negative

For `a : Fin (n + 1) → ℝ` that is **sorted in non-increasing order** AND
**traceless** (`∑ a = 0`), all partial sums `S_k := ∑_{j ≤ k} a_j` satisfy
`S_k ≥ 0`.

This is the **partial sums sign substrate** for the eigenvalue-sort approach
to S.3 d≥3 PROPER. Given an arbitrary traceless `a : Fin (n + 1) → ℝ`, the
permutation `σ := Tuple.sort (-a)` produces a non-increasingly-sorted
sequence `a ∘ σ` whose partial sums are all `≥ 0` (this theorem).

## Substantive content shipped

  * `partial_sums_nonneg_of_decreasing_traceless` — the main result.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (partial sums
non-negativity for decreasingly-sorted traceless sequences — eigenvalue
sort substrate).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Finset

/-- **Partial sums non-negative for decreasing-sorted traceless sequence**:
For `a : Fin (n + 1) → ℝ` that is non-increasing (`∀ i ≤ j, a j ≤ a i`) and
traceless (`∑ a = 0`), all partial sums are non-negative:

  `∀ k : Fin (n + 1), 0 ≤ ∑_{j ≤ k} a j`

(sum over `Finset.univ.filter (· ≤ k)`).

Proof: contradiction. If S_k < 0, then ∑_{j > k} a_j = -S_k > 0, so some
a_j' > 0 for j' > k. By non-increasing: a_k ≥ a_j' > 0. All a_j (j ≤ k)
are ≥ a_k > 0, so S_k ≥ (k+1) · a_k > 0. Contradicts S_k < 0. -/
theorem partial_sums_nonneg_of_decreasing_traceless {n : ℕ}
    (a : Fin (n + 1) → ℝ)
    (h_dec : ∀ i j : Fin (n + 1), i ≤ j → a j ≤ a i)
    (h_tr : ∑ k, a k = 0) :
    ∀ k : Fin (n + 1), 0 ≤ ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).filter (· ≤ k), a j := by
  intro k
  by_contra h_neg
  push_neg at h_neg
  -- Set up the partial sum and its complement.
  set S_k := ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).filter (· ≤ k), a j with hS_def
  -- Split total sum into S_k + (sum over j > k).
  set T_k := ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).filter (k < ·), a j with hT_def
  have h_split : S_k + T_k = ∑ j : Fin (n + 1), a j := by
    rw [hS_def, hT_def]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ k) a]
    congr 1
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  -- T_k = -S_k > 0.
  have h_T_k_pos : 0 < T_k := by
    have h1 : S_k + T_k = 0 := by rw [h_split]; exact h_tr
    linarith
  -- ∃ j > k with a j > 0 (else T_k ≤ 0).
  have h_ex_pos : ∃ j ∈ (Finset.univ : Finset (Fin (n + 1))).filter (k < ·), 0 < a j := by
    by_contra h_all_nn
    push_neg at h_all_nn
    have : T_k ≤ 0 := by
      rw [hT_def]
      apply Finset.sum_nonpos
      intro j hj
      exact h_all_nn j hj
    linarith
  obtain ⟨j', hj'_mem, hj'_pos⟩ := h_ex_pos
  rw [Finset.mem_filter] at hj'_mem
  -- By non-increasing: a k ≥ a j' > 0, so a k > 0.
  have h_a_k_pos : 0 < a k := by
    have h_k_le_j' : k ≤ j' := le_of_lt hj'_mem.2
    have h1 : a j' ≤ a k := h_dec k j' h_k_le_j'
    linarith
  -- All a_j (j ≤ k) ≥ a k > 0.
  have h_all_ge_a_k : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))).filter (· ≤ k), a k ≤ a j := by
    intro j hj
    rw [Finset.mem_filter] at hj
    exact h_dec j k hj.2
  -- S_k ≥ |filter| · a_k > 0.
  have h_filter_card_pos : 0 < ((Finset.univ : Finset (Fin (n + 1))).filter (· ≤ k)).card := by
    rw [Finset.card_pos]
    refine ⟨k, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ k, le_refl k⟩
  have h_S_k_bound : ((Finset.univ : Finset (Fin (n + 1))).filter (· ≤ k)).card • a k ≤ S_k := by
    rw [hS_def, ← Finset.sum_const]
    apply Finset.sum_le_sum
    exact h_all_ge_a_k
  have h_card_smul_pos : 0 < ((Finset.univ : Finset (Fin (n + 1))).filter (· ≤ k)).card • a k := by
    rw [nsmul_eq_mul]
    apply mul_pos
    · exact_mod_cast h_filter_card_pos
    · exact h_a_k_pos
  linarith

end SKEFTHawking.FKLW.GenericSUd
