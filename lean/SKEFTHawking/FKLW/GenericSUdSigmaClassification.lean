/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Complete classification of σ_y/σ_x 2-block commutators at SU(d)

The complete classification of pairwise commutators `[σ_y(a, b), σ_x(c, d)]`
for arbitrary pairs `(a, b)` and `(c, d)` of distinct indices in `Fin d`.

**Classification** (by overlap of `{a, b}` and `{c, d}`):
  * **Same pair** `{a, b} = {c, d}`: `[σ_y(a, b), σ_x(a, b)] = -2i · σ_z(a, b)`
    (Session 11 substrate).
  * **Disjoint supports** `{a, b} ∩ {c, d} = ∅`: commutator is `0`
    (this module §1).
  * **Shared one index** — 4 sub-cases (this module §2 + Session 17):
    - `[σ_y(a, b), σ_x(b, c)] = -i · σ_x(a, c)` (Session 17)
    - `[σ_y(a, b), σ_x(a, c)] = +i · σ_x(b, c)` (this module)
    - `[σ_y(a, b), σ_x(c, b)] = +i · σ_x(c, a)` (this module; via σ_x symmetry)
    - `[σ_y(a, b), σ_x(c, a)] = -i · σ_x(c, b)` (this module; via σ_x symmetry)

These identities exhaust all 2-block commutator cases, providing the
complete cross-term substrate for the Aharonov-Arad balanced commutator
construction at SU(d).

## Substantive content shipped

  * `sigmaY_sigmaX_commutator_disjoint` — disjoint supports ⟹ commutator = 0.
  * `sigmaY_sigmaX_cross_term_share_first_first` —
    `[σ_y(a, b), σ_x(a, c)] = +i · σ_x(b, c)`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (cross-term
classification for Aharonov-Arad SU(d) construction).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock
import SKEFTHawking.FKLW.GenericSUdSigmaCrossTerm

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Disjoint-supports commutator vanishing

For pairs `(a, b)` and `(c, d)` with `{a, b} ∩ {c, d} = ∅`, the σ_y and σ_x
blocks have non-overlapping nonzero supports, so the product (and hence
commutator) vanishes. -/

/-- **`σ_y(a, b) * σ_x(c, d) = 0`** when `{a, b} ∩ {c, d} = ∅`. -/
theorem sigmaYBlock_mul_sigmaXBlock_disjoint {d : ℕ}
    {a b c e : Fin d} (h_ac : a ≠ c) (h_ae : a ≠ e)
    (h_bc : b ≠ c) (h_be : b ≠ e) :
    sigmaYBlock a b * sigmaXBlock c e = 0 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [sigmaYBlock_apply, sigmaXBlock_apply]
  -- σ_y(a, b)_{p, k} nonzero only at (p, k) ∈ {(a, b), (b, a)}.
  -- σ_x(c, e)_{k, q} nonzero only at (k, q) ∈ {(c, e), (e, c)}.
  -- For a product to be nonzero, k must match BOTH constraints.
  -- σ_y requires k ∈ {a, b}; σ_x requires k ∈ {c, e}. Disjoint ⟹ no overlap.
  grind

/-- **`σ_x(c, e) * σ_y(a, b) = 0`** when `{a, b} ∩ {c, d} = ∅` (mirror). -/
theorem sigmaXBlock_mul_sigmaYBlock_disjoint {d : ℕ}
    {a b c e : Fin d} (h_ac : a ≠ c) (h_ae : a ≠ e)
    (h_bc : b ≠ c) (h_be : b ≠ e) :
    sigmaXBlock c e * sigmaYBlock a b = 0 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [sigmaXBlock_apply, sigmaYBlock_apply]
  grind

/-- **Disjoint commutator vanishing**: For `{a, b} ∩ {c, e} = ∅`,
`[σ_y(a, b), σ_x(c, e)] = 0`. -/
theorem sigmaY_sigmaX_commutator_disjoint {d : ℕ}
    {a b c e : Fin d} (h_ac : a ≠ c) (h_ae : a ≠ e)
    (h_bc : b ≠ c) (h_be : b ≠ e) :
    sigmaYBlock a b * sigmaXBlock c e - sigmaXBlock c e * sigmaYBlock a b = 0 := by
  rw [sigmaYBlock_mul_sigmaXBlock_disjoint h_ac h_ae h_bc h_be,
      sigmaXBlock_mul_sigmaYBlock_disjoint h_ac h_ae h_bc h_be]
  exact sub_zero 0

/-! ## 2. Cross-term: shared at first position of both σ blocks

For distinct `a, b, c`: `[σ_y(a, b), σ_x(a, c)] = +i · σ_x(b, c)`. -/

/-- **`σ_y(a, b) * σ_x(a, c)` entry at `(b, c)` is `+i`** for distinct `a, b, c`. -/
theorem sigmaYBlock_mul_sigmaXBlock_share_first_apply_bc {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c) :
    (sigmaYBlock a b * sigmaXBlock a c) b c = Complex.I := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single a]
  · rw [sigmaYBlock_apply, sigmaXBlock_apply]
    -- σ_y(a, b)_{b, a}: (if a=b∧b=a then -I) + (if b=b∧a=a then I) = 0 + I = I
    have h_yba1 : ¬ ((a : Fin d) = b ∧ b = a) := fun ⟨h, _⟩ => h_ab h
    have h_yba2 : (b : Fin d) = b ∧ a = a := ⟨rfl, rfl⟩
    rw [if_neg h_yba1, if_pos h_yba2, zero_add]
    -- σ_x(a, c)_{a, c}: (if a=a∧c=c then 1) + (if c=a∧a=c then 1) = 1 + 0 = 1
    have h_xac1 : (a : Fin d) = a ∧ c = c := ⟨rfl, rfl⟩
    have h_xac2 : ¬ ((c : Fin d) = a ∧ a = c) := fun ⟨h, _⟩ => h_ac h.symm
    rw [if_pos h_xac1, if_neg h_xac2, add_zero]
    ring
  · intro k _ h_ka
    rw [sigmaYBlock_apply, sigmaXBlock_apply]
    have h_y1 : ¬ ((a : Fin d) = b ∧ b = k) := fun ⟨h, _⟩ => h_ab h
    have h_y2 : ¬ ((b : Fin d) = b ∧ a = k) := fun ⟨_, h⟩ => h_ka h.symm
    rw [if_neg h_y1, if_neg h_y2]
    ring
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **`σ_y(a, b) * σ_x(a, c)` off-`(b, c)` entries are zero**. -/
theorem sigmaYBlock_mul_sigmaXBlock_share_first_apply_off {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c)
    {p q : Fin d} (h_not_bc : ¬ (p = b ∧ q = c)) :
    (sigmaYBlock a b * sigmaXBlock a c) p q = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [sigmaYBlock_apply, sigmaXBlock_apply]
  grind

/-- **Full product identity**: `σ_y(a, b) * σ_x(a, c) = single b c i`
for distinct `a, b, c`. -/
theorem sigmaYBlock_mul_sigmaXBlock_share_first {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c) :
    sigmaYBlock a b * sigmaXBlock a c = Matrix.single b c Complex.I := by
  ext p q
  by_cases h_pb : p = b
  · by_cases h_qc : q = c
    · rw [h_pb, h_qc]
      rw [sigmaYBlock_mul_sigmaXBlock_share_first_apply_bc h_ab h_bc h_ac]
      rw [Matrix.single_apply]
      simp
    · have h_not_bc : ¬ (p = b ∧ q = c) := fun ⟨_, h⟩ => h_qc h
      rw [sigmaYBlock_mul_sigmaXBlock_share_first_apply_off h_ab h_bc h_ac h_not_bc]
      rw [Matrix.single_apply]
      rw [h_pb]
      have h_qc_swap : ¬ (c = q) := fun h => h_qc h.symm
      simp [if_neg h_qc_swap]
  · have h_not_bc : ¬ (p = b ∧ q = c) := fun ⟨h, _⟩ => h_pb h
    rw [sigmaYBlock_mul_sigmaXBlock_share_first_apply_off h_ab h_bc h_ac h_not_bc]
    rw [Matrix.single_apply]
    have h_bp : b ≠ p := fun h => h_pb h.symm
    simp [if_neg h_bp]
    intro h
    exact absurd h h_bp

/-- **`σ_x(a, c) * σ_y(a, b)` entry at `(c, b)` is `-i`** for distinct `a, b, c`. -/
theorem sigmaXBlock_mul_sigmaYBlock_share_first_apply_cb {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c) :
    (sigmaXBlock a c * sigmaYBlock a b) c b = -Complex.I := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single a]
  · rw [sigmaXBlock_apply, sigmaYBlock_apply]
    -- σ_x(a, c)_{c, a}: (if a=c∧c=a then 1) + (if c=c∧a=a then 1) = 0 + 1 = 1
    have h_xca1 : ¬ ((a : Fin d) = c ∧ c = a) := fun ⟨h, _⟩ => h_ac h
    have h_xca2 : (c : Fin d) = c ∧ a = a := ⟨rfl, rfl⟩
    rw [if_neg h_xca1, if_pos h_xca2, zero_add]
    -- σ_y(a, b)_{a, b}: (if a=a∧b=b then -I) + (if b=a∧a=b then I) = -I + 0 = -I
    have h_yab1 : (a : Fin d) = a ∧ b = b := ⟨rfl, rfl⟩
    have h_yab2 : ¬ ((b : Fin d) = a ∧ a = b) := fun ⟨h, _⟩ => h_ab h.symm
    rw [if_pos h_yab1, if_neg h_yab2, add_zero]
    ring
  · intro k _ h_ka
    rw [sigmaXBlock_apply, sigmaYBlock_apply]
    have h_x1 : ¬ ((a : Fin d) = c ∧ c = k) := fun ⟨h, _⟩ => h_ac h
    have h_x2 : ¬ ((c : Fin d) = c ∧ a = k) := fun ⟨_, h⟩ => h_ka h.symm
    rw [if_neg h_x1, if_neg h_x2]
    ring
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **`σ_x(a, c) * σ_y(a, b)` off-`(c, b)` entries are zero**. -/
theorem sigmaXBlock_mul_sigmaYBlock_share_first_apply_off {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c)
    {p q : Fin d} (h_not_cb : ¬ (p = c ∧ q = b)) :
    (sigmaXBlock a c * sigmaYBlock a b) p q = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [sigmaXBlock_apply, sigmaYBlock_apply]
  grind

/-- **Full mirror product identity**: `σ_x(a, c) * σ_y(a, b) = single c b (-i)`. -/
theorem sigmaXBlock_mul_sigmaYBlock_share_first {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c) :
    sigmaXBlock a c * sigmaYBlock a b = Matrix.single c b (-Complex.I) := by
  ext p q
  by_cases h_pc : p = c
  · by_cases h_qb : q = b
    · rw [h_pc, h_qb]
      rw [sigmaXBlock_mul_sigmaYBlock_share_first_apply_cb h_ab h_bc h_ac]
      rw [Matrix.single_apply]
      simp
    · have h_not_cb : ¬ (p = c ∧ q = b) := fun ⟨_, h⟩ => h_qb h
      rw [sigmaXBlock_mul_sigmaYBlock_share_first_apply_off h_ab h_bc h_ac h_not_cb]
      rw [Matrix.single_apply]
      rw [h_pc]
      have h_qb_swap : ¬ (b = q) := fun h => h_qb h.symm
      simp [if_neg h_qb_swap]
  · have h_not_cb : ¬ (p = c ∧ q = b) := fun ⟨h, _⟩ => h_pc h
    rw [sigmaXBlock_mul_sigmaYBlock_share_first_apply_off h_ab h_bc h_ac h_not_cb]
    rw [Matrix.single_apply]
    have h_cp : c ≠ p := fun h => h_pc h.symm
    simp [if_neg h_cp]
    intro h
    exact absurd h h_cp

/-- **Cross-term commutator identity for shared FIRST position**:
`[σ_y(a, b), σ_x(a, c)] = +i · σ_x(b, c)` for distinct `a, b, c ∈ Fin d`. -/
theorem sigmaY_sigmaX_cross_term_share_first_first {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c) :
    sigmaYBlock a b * sigmaXBlock a c - sigmaXBlock a c * sigmaYBlock a b =
      Complex.I • sigmaXBlock b c := by
  rw [sigmaYBlock_mul_sigmaXBlock_share_first h_ab h_bc h_ac,
      sigmaXBlock_mul_sigmaYBlock_share_first h_ab h_bc h_ac]
  -- Goal: single b c i - single c b (-i) = i · σ_x(b, c)
  -- σ_x(b, c) = single b c 1 + single c b 1.
  -- i · σ_x(b, c) = single b c i + single c b i.
  -- LHS: single b c i - single c b (-i) = single b c i + single c b i ✓
  ext p q
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply,
             sigmaXBlock_apply, smul_eq_mul]
  by_cases hbc_pq : b = p ∧ c = q
  · obtain ⟨rfl, rfl⟩ := hbc_pq
    have h_cb_pq : ¬ (c = b ∧ b = c) := fun ⟨h, _⟩ => h_bc h.symm
    simp [if_neg h_cb_pq]
  · by_cases hcb_pq : c = p ∧ b = q
    · obtain ⟨rfl, rfl⟩ := hcb_pq
      have h_bc_pq : ¬ (b = c ∧ c = b) := fun ⟨h, _⟩ => h_bc h
      simp [if_neg h_bc_pq]
    · simp [if_neg hbc_pq, if_neg hcb_pq]

end SKEFTHawking.FKLW.GenericSUd
