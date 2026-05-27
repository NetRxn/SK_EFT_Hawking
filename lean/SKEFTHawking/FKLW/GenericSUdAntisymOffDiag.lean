/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Antisymmetric off-diagonal sum vanishes

For `f : Fin n → Fin n → M` (M a ℂ-module) satisfying the antisymmetric
condition `f p q + f q p = 0` for all `p ≠ q`, the off-diagonal sum

  `∑_p ∑_{q ≠ p} f p q = 0`

via the doubling trick: 2S = S + S(swap) = ∑_p ∑_{q ≠ p} (f p q + f q p) = 0.

This is the **algebraic substrate** for the F·G − G·F double-sum reduction:
when `f p q = γ_p γ_q · [σ_y(p), σ_x(q)]`, Session 19's pair-swap gives
the antisymmetry, so the off-diagonal sum vanishes.

## Substantive content shipped

  * `sum_antisymmetric_off_diag_eq_zero` — generic antisymmetric off-diagonal
    sum vanishing.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (antisymmetric
sum vanishing for double-sum cross-term cancellation).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Finset

/-- **Antisymmetric off-diagonal sum vanishes**: for `f : Fin n → Fin n → M`
with M a complex vector space, if `f p q + f q p = 0` for all distinct
`p, q ∈ Fin n`, then

  `∑_p ∑_{q ∈ univ \ {p}} f p q = 0`.

Proof: doubling trick using `Finset.sum_comm` (Fubini) plus diagonal extraction.
The ℂ-module structure provides division by 2. -/
theorem sum_antisymmetric_off_diag_eq_zero
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f : Fin n → Fin n → M)
    (h_anti : ∀ p q : Fin n, p ≠ q → f p q + f q p = 0) :
    ∑ p, ∑ q ∈ (Finset.univ : Finset (Fin n)).erase p, f p q = 0 := by
  -- Step 1: ∑_p ∑_q f p q = ∑_p f p p + (off-diag sum) via Finset.add_sum_erase.
  have h_full_split : (∑ p, ∑ q, f p q) = (∑ p, f p p) +
      ∑ p, ∑ q ∈ (Finset.univ : Finset (Fin n)).erase p, f p q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ p)).symm
  -- Step 2: ∑_p ∑_q f q p = ∑_p f p p + (off-diag swap sum).
  have h_full_swap_split : (∑ p, ∑ q, f q p) = (∑ p, f p p) +
      ∑ p, ∑ q ∈ (Finset.univ : Finset (Fin n)).erase p, f q p := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ p)).symm
  -- Step 3: ∑_p ∑_q f p q = ∑_p ∑_q f q p (Fubini).
  have h_fubini : (∑ p, ∑ q, f p q) = ∑ p, ∑ q, f q p :=
    Finset.sum_comm
  -- Step 4: cancel diagonals to get off-diag sum = off-diag swap sum.
  have h_offdiag_eq_swap :
      ∑ p, ∑ q ∈ (Finset.univ : Finset (Fin n)).erase p, f p q =
      ∑ p, ∑ q ∈ (Finset.univ : Finset (Fin n)).erase p, f q p := by
    have h1 : (∑ p, f p p) +
        (∑ p, ∑ q ∈ (Finset.univ : Finset (Fin n)).erase p, f p q) =
        (∑ p, f p p) +
        (∑ p, ∑ q ∈ (Finset.univ : Finset (Fin n)).erase p, f q p) := by
      rw [← h_full_split, h_fubini, h_full_swap_split]
    exact add_left_cancel h1
  -- Step 5: doubled sum equals sum of pair-swap terms (which are all 0).
  set S := ∑ p, ∑ q ∈ (Finset.univ : Finset (Fin n)).erase p, f p q with hS_def
  have h_2S_zero : S + S = 0 := by
    nth_rewrite 1 [h_offdiag_eq_swap]
    rw [hS_def]
    -- Now: (∑_p ∑_{q ∈ erase p} f q p) + (∑_p ∑_{q ∈ erase p} f p q) = 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro p _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro q hq
    rw [Finset.mem_erase] at hq
    -- q ≠ p (from hq.1)
    have h_swap_term : f q p + f p q = 0 := by
      rw [add_comm]
      exact h_anti p q (fun h => hq.1 h.symm)
    exact h_swap_term
  -- Step 6: 2 • S = 0 in ℂ-module → S = 0.
  have h_two_S : (2 : ℂ) • S = 0 := by
    rw [two_smul]
    exact h_2S_zero
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp h_two_S).resolve_left h_two_ne

end SKEFTHawking.FKLW.GenericSUd
