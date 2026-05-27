/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Cross-term pair-swap cancellation

For DISTINCT pairs `p, q : Fin (n + 1)` (with `p ≠ q`), the sum of
the "forward" and "backward" cross-term commutators VANISHES:

  `[σ_y(p.castSucc, p.succ), σ_x(q.castSucc, q.succ)]
   + [σ_y(q.castSucc, q.succ), σ_x(p.castSucc, p.succ)] = 0`

This is the **algebraic key** to the cross-term-free Aharonov-Arad
balanced commutator construction at SU(d): for `F = Σ α_p · σ_y(p)`
and `G = Σ α_p · σ_x(p)` (SAME coefficient in F and G), the cross-term
sum in [F, G] pairs up as:

  `Σ_{p ≠ q} α_p α_q [σ_y(p), σ_x(q)]
   = Σ_{unordered pairs} α_p α_q ([σ_y(p), σ_x(q)] + [σ_y(q), σ_x(p)])
   = Σ_{unordered pairs} α_p α_q · 0 = 0`

The cross-terms cancel automatically — no counterterms needed — provided
F and G share the same coefficient function.

## Substantive content shipped

  * `sigmaY_sigmaX_pair_swap_cancel_adjacent_forward_backward` —
    for adjacent (`|p.val - q.val| = 1`) pairs.
  * `sigmaY_sigmaX_pair_swap_cancel_disjoint` —
    for non-adjacent (`|p.val - q.val| ≥ 2`) pairs.
  * `sigmaY_sigmaX_pair_swap_cancel` — combined: vanishing for any
    `p ≠ q ∈ Fin (n + 1)`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (cross-term
cancellation for the symmetric α_p coefficient Aharonov-Arad construction).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock
import SKEFTHawking.FKLW.GenericSUdSigmaCrossTerm
import SKEFTHawking.FKLW.GenericSUdSigmaClassification

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Helpers for the adjacent and disjoint conditions

For pairs `(p, q)` with `p ≠ q ∈ Fin (n + 1)`, the indices
`p.castSucc, p.succ, q.castSucc, q.succ` may share at most one index
(at the adjacent case). The cases:

  * `q = p + 1` (forward adjacent): `p.succ = q.castSucc`, so shared index `p.succ`
  * `p = q + 1` (backward adjacent): `q.succ = p.castSucc`, so shared index `q.succ`
  * `|p.val - q.val| ≥ 2`: disjoint

We package the four-index distinctness arguments for the disjoint case. -/

/-- For `p, q : Fin (n + 1)` with `q.val ≥ p.val + 2`, the four indices
`p.castSucc, p.succ, q.castSucc, q.succ` are pairwise distinct. -/
theorem four_indices_distinct_of_far {n : ℕ} {p q : Fin (n + 1)}
    (h_far : p.val + 2 ≤ q.val) :
    (p.castSucc : Fin (n + 2)) ≠ q.castSucc ∧
    p.castSucc ≠ q.succ ∧
    p.succ ≠ q.castSucc ∧
    p.succ ≠ q.succ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals {
    intro h
    have := congr_arg Fin.val h
    simp [Fin.val_succ, Fin.coe_castSucc] at this
    omega
  }

/-! ## 2. Disjoint case: cross-term commutator vanishes

For `p, q : Fin (n + 1)` with `|p.val - q.val| ≥ 2`, both
`[σ_y(p.castSucc, p.succ), σ_x(q.castSucc, q.succ)]` and the swap
are zero individually. -/

/-- **Pair-swap cancellation, disjoint case**: for `p, q : Fin (n + 1)`
with `p.val + 2 ≤ q.val`, both cross-terms vanish. -/
theorem sigmaY_sigmaX_pair_swap_cancel_disjoint_forward {n : ℕ}
    {p q : Fin (n + 1)} (h_far : p.val + 2 ≤ q.val) :
    (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ *
       sigmaXBlock q.castSucc q.succ -
     sigmaXBlock q.castSucc q.succ *
       sigmaYBlock p.castSucc p.succ) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := four_indices_distinct_of_far h_far
  exact sigmaY_sigmaX_commutator_disjoint h1 h2 h3 h4

/-- **Pair-swap cancellation, disjoint case, backward**: by `_far` symmetry. -/
theorem sigmaY_sigmaX_pair_swap_cancel_disjoint_backward {n : ℕ}
    {p q : Fin (n + 1)} (h_far : p.val + 2 ≤ q.val) :
    (sigmaYBlock (q.castSucc : Fin (n + 2)) q.succ *
       sigmaXBlock p.castSucc p.succ -
     sigmaXBlock p.castSucc p.succ *
       sigmaYBlock q.castSucc q.succ) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := four_indices_distinct_of_far h_far
  -- Disjoint with (a, b) = (q.castSucc, q.succ), (c, e) = (p.castSucc, p.succ)
  exact sigmaY_sigmaX_commutator_disjoint h1.symm h3.symm h2.symm h4.symm

/-- **Pair-swap cancellation, disjoint case sum**: for `|p.val - q.val| ≥ 2`,
both commutators are individually 0, so their sum is 0. -/
theorem sigmaY_sigmaX_pair_swap_cancel_disjoint {n : ℕ}
    {p q : Fin (n + 1)} (h_far : p.val + 2 ≤ q.val) :
    (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ *
       sigmaXBlock q.castSucc q.succ -
     sigmaXBlock q.castSucc q.succ *
       sigmaYBlock p.castSucc p.succ) +
    (sigmaYBlock q.castSucc q.succ *
       sigmaXBlock p.castSucc p.succ -
     sigmaXBlock p.castSucc p.succ *
       sigmaYBlock q.castSucc q.succ) = 0 := by
  rw [sigmaY_sigmaX_pair_swap_cancel_disjoint_forward h_far,
      sigmaY_sigmaX_pair_swap_cancel_disjoint_backward h_far]
  exact add_zero 0

/-! ## 3. Forward-adjacent case: `q = p + 1`

For `q.val = p.val + 1`, we have `p.succ = q.castSucc` (shared index).
The two cross-terms compute to `±i · σ_x(p.castSucc, q.succ)` with
opposite signs, hence cancel.

  * `[σ_y(p.castSucc, p.succ), σ_x(p.succ, q.succ)] = -i · σ_x(p.castSucc, q.succ)`
    (Session 17 shared-middle)
  * `[σ_y(p.succ, q.succ), σ_x(p.castSucc, p.succ)] = +i · σ_x(p.castSucc, q.succ)`
    (Session 18 shared-first, with σ_x symmetric) -/

/-- **Forward-adjacent case**: when `q.val = p.val + 1` (so `p.succ = q.castSucc`),
the two cross-terms cancel. -/
theorem sigmaY_sigmaX_pair_swap_cancel_adjacent {n : ℕ}
    {p q : Fin (n + 1)} (h_adj : q.val = p.val + 1) :
    (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ *
       sigmaXBlock q.castSucc q.succ -
     sigmaXBlock q.castSucc q.succ *
       sigmaYBlock p.castSucc p.succ) +
    (sigmaYBlock q.castSucc q.succ *
       sigmaXBlock p.castSucc p.succ -
     sigmaXBlock p.castSucc p.succ *
       sigmaYBlock q.castSucc q.succ) = 0 := by
  -- Substitute q.castSucc = p.succ using h_adj.
  have h_eq_castSucc : (q.castSucc : Fin (n + 2)) = p.succ := by
    apply Fin.ext
    show q.val = p.val + 1
    exact h_adj
  -- Three indices: a = p.castSucc, b = p.succ = q.castSucc, c = q.succ
  set a : Fin (n + 2) := p.castSucc with ha_def
  set b : Fin (n + 2) := p.succ with hb_def
  set c : Fin (n + 2) := q.succ with hc_def
  have h_ab : a ≠ b := by
    intro h
    have := congr_arg Fin.val h
    simp [ha_def, hb_def, Fin.coe_castSucc, Fin.val_succ] at this
  have h_bc : b ≠ c := by
    intro h
    have := congr_arg Fin.val h
    simp [hb_def, hc_def, Fin.val_succ] at this
    omega
  have h_ac : a ≠ c := by
    intro h
    have := congr_arg Fin.val h
    simp [ha_def, hc_def, Fin.coe_castSucc, Fin.val_succ] at this
    omega
  -- Rewrite using h_eq_castSucc
  rw [h_eq_castSucc]
  -- Goal in terms of a, b, c:
  -- [σ_y(a, b), σ_x(b, c)] + [σ_y(b, c), σ_x(a, b)] = 0
  -- Session 17: [σ_y(a, b), σ_x(b, c)] = -i · σ_x(a, c)
  -- Session 17 mirror (or Session 18 via σ_x symmetric):
  --   [σ_y(b, c), σ_x(a, b)] = +i · σ_x(a, c)
  -- Sum: 0
  rw [sigmaY_sigmaX_cross_term_share_middle h_ab h_bc h_ac]
  -- Goal: -I · σ_x(a, c) + (σ_y(b, c) * σ_x(a, b) - σ_x(a, b) * σ_y(b, c)) = 0
  -- For the second commutator: use Session 17 mirror form
  -- [σ_y(b, c), σ_x(a, b)] — relabel: σ_y at (b, c), σ_x at (a, b). Shared index b.
  -- Using Session 17 with (a' = b, b' = a, c' = ?)... wait the formula was [σ_y(a, b), σ_x(b, c)].
  -- Here σ_y(b, c) has indices (b, c), σ_x(a, b) has indices (a, b). Shared b is at σ_y's first and σ_x's second.
  -- Use σ_x symmetric: σ_x(a, b) = σ_x(b, a). Now σ_y(b, c) and σ_x(b, a) share b at σ_y's first and σ_x's first.
  -- Session 18 share_first: [σ_y(b, c), σ_x(b, a)] = +i · σ_x(c, a) = +i · σ_x(a, c).
  -- But σ_x(a, b) ≠ σ_x(b, a) as written terms (they're EQUAL matrices but different syntactic forms).
  -- Session 18 share_first formula needs σ_x(a, c) form.
  have h_sym_swap : sigmaXBlock a b = sigmaXBlock b a := by
    ext x y
    simp only [sigmaXBlock_apply]
    grind
  rw [h_sym_swap]
  -- Now goal: -I • σ_x(a, c) + (σ_y(b, c) * σ_x(b, a) - σ_x(b, a) * σ_y(b, c)) = 0
  -- Apply Session 18 share_first formula `[σ_y(a', b'), σ_x(a', c')] = i · σ_x(b', c')`
  -- with mapping a' := b, b' := c, c' := a. Result: [σ_y(b, c), σ_x(b, a)] = i · σ_x(c, a).
  rw [show sigmaYBlock b c * sigmaXBlock b a - sigmaXBlock b a * sigmaYBlock b c =
        Complex.I • sigmaXBlock c a from
      sigmaY_sigmaX_cross_term_share_first_first h_bc h_ac.symm h_ab.symm]
  -- Goal: -I • σ_x(a, c) + i • σ_x(c, a) = 0
  -- σ_x is symmetric: σ_x(a, c) = σ_x(c, a).
  have h_sym_ac : sigmaXBlock a c = sigmaXBlock c a := by
    ext x y
    simp only [sigmaXBlock_apply]
    grind
  rw [h_sym_ac]
  -- Goal: -I • σ_x(c, a) + I • σ_x(c, a) = 0
  rw [← add_smul]
  simp

/-! ## 4. Backward-adjacent case: `p = q + 1`

Symmetric to §3 with p, q swapped. -/

/-- **Backward-adjacent case**: when `p.val = q.val + 1`, the two cross-terms
cancel by §3 with `(p, q)` swapped. -/
theorem sigmaY_sigmaX_pair_swap_cancel_adjacent_backward {n : ℕ}
    {p q : Fin (n + 1)} (h_adj : p.val = q.val + 1) :
    (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ *
       sigmaXBlock q.castSucc q.succ -
     sigmaXBlock q.castSucc q.succ *
       sigmaYBlock p.castSucc p.succ) +
    (sigmaYBlock q.castSucc q.succ *
       sigmaXBlock p.castSucc p.succ -
     sigmaXBlock p.castSucc p.succ *
       sigmaYBlock q.castSucc q.succ) = 0 := by
  have this' := sigmaY_sigmaX_pair_swap_cancel_adjacent (p := q) (q := p) h_adj
  -- this' has the same terms in opposite order. Use Matrix add_comm.
  exact (add_comm _ _).trans this'

/-! ## 5. Combined pair-swap cancellation

For any `p ≠ q ∈ Fin (n + 1)`, the sum of forward and backward
cross-term commutators is zero. -/

/-- **MAIN cross-term pair-swap cancellation theorem**: for any distinct
`p, q : Fin (n + 1)`, the forward and backward cross-term commutators
cancel each other. -/
theorem sigmaY_sigmaX_pair_swap_cancel {n : ℕ}
    {p q : Fin (n + 1)} (h_ne : p ≠ q) :
    (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ *
       sigmaXBlock q.castSucc q.succ -
     sigmaXBlock q.castSucc q.succ *
       sigmaYBlock p.castSucc p.succ) +
    (sigmaYBlock q.castSucc q.succ *
       sigmaXBlock p.castSucc p.succ -
     sigmaXBlock p.castSucc p.succ *
       sigmaYBlock q.castSucc q.succ) = 0 := by
  -- Case on |p.val - q.val|: adjacent or far.
  have h_val_ne : p.val ≠ q.val := fun h => h_ne (Fin.ext h)
  rcases lt_or_gt_of_ne h_val_ne with h_lt | h_gt
  · -- p.val < q.val
    rcases Nat.lt_or_ge (p.val + 2) (q.val + 1) with h_far | h_close
    · -- p.val + 2 ≤ q.val: disjoint
      have h_far' : p.val + 2 ≤ q.val := by omega
      exact sigmaY_sigmaX_pair_swap_cancel_disjoint h_far'
    · -- p.val + 1 < p.val + 2 ≥ q.val + 1, combined with p.val < q.val ⟹ q.val = p.val + 1
      have h_adj : q.val = p.val + 1 := by omega
      exact sigmaY_sigmaX_pair_swap_cancel_adjacent h_adj
  · -- q.val < p.val: symmetric
    rcases Nat.lt_or_ge (q.val + 2) (p.val + 1) with h_far | h_close
    · have h_far' : q.val + 2 ≤ p.val := by omega
      -- Symmetric form: the disjoint conclusion is symmetric
      have h := sigmaY_sigmaX_pair_swap_cancel_disjoint h_far'
      exact (add_comm _ _).trans h
    · have h_adj : p.val = q.val + 1 := by omega
      exact sigmaY_sigmaX_pair_swap_cancel_adjacent_backward h_adj

end SKEFTHawking.FKLW.GenericSUd
