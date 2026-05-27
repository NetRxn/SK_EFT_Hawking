/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Cross-term commutators for σ_y/σ_x blocks

For ANY three distinct indices `a, b, c ∈ Fin d`, the commutator
`[σ_y(a, b), σ_x(b, c)]` (sharing index `b`) equals `-i · σ_x(a, c)`.

This is the **cross-term identity** that explains the obstruction in
the naive σ_y/σ_x sum construction for the d-generic balanced commutator:
when F = ∑_p α_p · σ_y(p.castSucc, p.succ) and G = ∑_p β_p · σ_x(p.castSucc, p.succ),
the commutator [F, G] contains both:
  - "diagonal" same-pair terms `α_p β_p · [σ_y(p), σ_x(p)] = -2i α_p β_p · σ_z(p)`
  - "cross" adjacent-pair terms `α_p β_{p+1} · [σ_y(p), σ_x(p+1)] = -i α_p β_{p+1} · σ_x(p.castSucc, p+1.succ)`

The cross terms have nonzero off-diagonal entries at `(p.castSucc, p+1.succ)` and
must be cancelled by counterterms in the Aharonov-Arad construction.

## Substantive content shipped

  * `sigmaYBlock_mul_sigmaXBlock_share_middle` — explicit form of
    `σ_y(a, b) * σ_x(b, c)` (single entry at `(a, c)`).
  * `sigmaXBlock_mul_sigmaYBlock_share_middle` — mirror.
  * `sigmaY_sigmaX_cross_term_share_middle` — the cross-term identity
    `[σ_y(a, b), σ_x(b, c)] = -i · σ_x(a, c)` for distinct a, b, c.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (cross-term
analysis for the Aharonov-Arad SU(d) construction).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. `σ_y(a, b) * σ_x(b, c)` for three distinct indices

For distinct `a, b, c`, the product has a single nonzero entry at `(a, c)`
with value `-i`. -/

/-- **`σ_y(a, b) * σ_x(b, c)` entry at `(a, c)` is `-i`** for distinct
indices `a, b, c`. -/
theorem sigmaYBlock_mul_sigmaXBlock_share_middle_apply_ac {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c) :
    (sigmaYBlock a b * sigmaXBlock b c) a c = -Complex.I := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single b]
  · rw [sigmaYBlock_apply, sigmaXBlock_apply]
    -- σ_y(a, b)_{a, b}: (if a=a∧b=b then -I) + (if b=a∧a=b then I) = -I + 0 = -I
    have h_yab1 : (a : Fin d) = a ∧ b = b := ⟨rfl, rfl⟩
    have h_yab2 : ¬ ((b : Fin d) = a ∧ a = b) := fun ⟨h, _⟩ => h_ab h.symm
    rw [if_pos h_yab1, if_neg h_yab2, add_zero]
    -- σ_x(b, c)_{b, c}: (if b=b∧c=c then 1) + (if c=b∧b=c then 1) = 1 + 0 = 1
    have h_xbc1 : (b : Fin d) = b ∧ c = c := ⟨rfl, rfl⟩
    have h_xbc2 : ¬ ((c : Fin d) = b ∧ b = c) := fun ⟨h, _⟩ => h_bc h.symm
    rw [if_pos h_xbc1, if_neg h_xbc2, add_zero]
    ring
  · intro k _ h_kb
    rw [sigmaYBlock_apply, sigmaXBlock_apply]
    -- For k ≠ b: σ_y(a, b)_{a, k} = 0 (needs k = b in either ite)
    have h_y1 : ¬ ((a : Fin d) = a ∧ b = k) := fun ⟨_, h⟩ => h_kb h.symm
    have h_y2 : ¬ ((b : Fin d) = a ∧ a = k) := fun ⟨h, _⟩ => h_ab h.symm
    rw [if_neg h_y1, if_neg h_y2]
    ring
  · intro h; exact absurd (Finset.mem_univ b) h

/-- **`σ_y(a, b) * σ_x(b, c)` off-`(a,c)` entries are zero** for distinct
indices `a, b, c`. -/
theorem sigmaYBlock_mul_sigmaXBlock_share_middle_apply_off {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c)
    {p q : Fin d} (h_not_ac : ¬ (p = a ∧ q = c)) :
    (sigmaYBlock a b * sigmaXBlock b c) p q = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [sigmaYBlock_apply, sigmaXBlock_apply]
  grind

/-- **Full product identity**: `σ_y(a, b) * σ_x(b, c) = -i · single a c 1`
for distinct `a, b, c`. -/
theorem sigmaYBlock_mul_sigmaXBlock_share_middle {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c) :
    sigmaYBlock a b * sigmaXBlock b c = Matrix.single a c (-Complex.I) := by
  ext p q
  by_cases h_pa : p = a
  · by_cases h_qc : q = c
    · rw [h_pa, h_qc]
      rw [sigmaYBlock_mul_sigmaXBlock_share_middle_apply_ac h_ab h_bc h_ac]
      rw [Matrix.single_apply]
      simp
    · have h_not_ac : ¬ (p = a ∧ q = c) := fun ⟨_, h⟩ => h_qc h
      rw [sigmaYBlock_mul_sigmaXBlock_share_middle_apply_off h_ab h_bc h_ac h_not_ac]
      rw [Matrix.single_apply]
      rw [h_pa]
      have h_qc_swap : ¬ (c = q) := fun h => h_qc h.symm
      simp [if_neg h_qc_swap]
  · have h_not_ac : ¬ (p = a ∧ q = c) := fun ⟨h, _⟩ => h_pa h
    rw [sigmaYBlock_mul_sigmaXBlock_share_middle_apply_off h_ab h_bc h_ac h_not_ac]
    rw [Matrix.single_apply]
    have h_ap : a ≠ p := fun h => h_pa h.symm
    simp [if_neg h_ap]
    intro h
    exact absurd h h_ap

/-! ## 2. Mirror: `σ_x(b, c) * σ_y(a, b)` for three distinct indices

For distinct `a, b, c`, the mirror product `σ_x(b, c) * σ_y(a, b)` has
a single nonzero entry at `(c, a)` with value `+i`. -/

/-- **`σ_x(b, c) * σ_y(a, b)` entry at `(c, a)` is `+i`** for distinct
indices `a, b, c`. -/
theorem sigmaXBlock_mul_sigmaYBlock_share_middle_apply_ca {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c) :
    (sigmaXBlock b c * sigmaYBlock a b) c a = Complex.I := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single b]
  · rw [sigmaXBlock_apply, sigmaYBlock_apply]
    -- σ_x(b, c)_{c, b}: (if b=c∧c=b then 1) + (if c=c∧b=b then 1) = 0 + 1 = 1
    have h_xcb1 : ¬ ((b : Fin d) = c ∧ c = b) := fun ⟨h, _⟩ => h_bc h
    have h_xcb2 : (c : Fin d) = c ∧ b = b := ⟨rfl, rfl⟩
    rw [if_neg h_xcb1, if_pos h_xcb2, zero_add]
    -- σ_y(a, b)_{b, a}: (if a=b∧b=a then -I) + (if b=b∧a=a then I) = 0 + I = I
    have h_yba1 : ¬ ((a : Fin d) = b ∧ b = a) := fun ⟨h, _⟩ => h_ab h
    have h_yba2 : (b : Fin d) = b ∧ a = a := ⟨rfl, rfl⟩
    rw [if_neg h_yba1, if_pos h_yba2, zero_add]
    ring
  · intro k _ h_kb
    rw [sigmaXBlock_apply, sigmaYBlock_apply]
    have h_x1 : ¬ ((b : Fin d) = c ∧ c = k) := fun ⟨h, _⟩ => h_bc h
    have h_x2 : ¬ ((c : Fin d) = c ∧ b = k) := fun ⟨_, h⟩ => h_kb h.symm
    rw [if_neg h_x1, if_neg h_x2]
    ring
  · intro h; exact absurd (Finset.mem_univ b) h

/-- **`σ_x(b, c) * σ_y(a, b)` off-`(c,a)` entries are zero** for distinct
indices `a, b, c`. -/
theorem sigmaXBlock_mul_sigmaYBlock_share_middle_apply_off {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c)
    {p q : Fin d} (h_not_ca : ¬ (p = c ∧ q = a)) :
    (sigmaXBlock b c * sigmaYBlock a b) p q = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [sigmaXBlock_apply, sigmaYBlock_apply]
  grind

/-- **Full mirror product identity**: `σ_x(b, c) * σ_y(a, b) = i · single c a 1`
for distinct `a, b, c`. -/
theorem sigmaXBlock_mul_sigmaYBlock_share_middle {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c) :
    sigmaXBlock b c * sigmaYBlock a b = Matrix.single c a Complex.I := by
  ext p q
  by_cases h_pc : p = c
  · by_cases h_qa : q = a
    · rw [h_pc, h_qa]
      rw [sigmaXBlock_mul_sigmaYBlock_share_middle_apply_ca h_ab h_bc h_ac]
      rw [Matrix.single_apply]
      simp
    · have h_not_ca : ¬ (p = c ∧ q = a) := fun ⟨_, h⟩ => h_qa h
      rw [sigmaXBlock_mul_sigmaYBlock_share_middle_apply_off h_ab h_bc h_ac h_not_ca]
      rw [Matrix.single_apply]
      rw [h_pc]
      have h_qa_swap : ¬ (a = q) := fun h => h_qa h.symm
      simp [if_neg h_qa_swap]
  · have h_not_ca : ¬ (p = c ∧ q = a) := fun ⟨h, _⟩ => h_pc h
    rw [sigmaXBlock_mul_sigmaYBlock_share_middle_apply_off h_ab h_bc h_ac h_not_ca]
    rw [Matrix.single_apply]
    have h_cp : c ≠ p := fun h => h_pc h.symm
    simp [if_neg h_cp]
    intro h
    exact absurd h h_cp

/-! ## 3. The cross-term commutator identity

**The keystone lemma**: For distinct indices `a, b, c ∈ Fin d`,

  `[σ_y(a, b), σ_x(b, c)] = -i · σ_x(a, c)`

This shows that the cross-term of the σ_y/σ_x sum construction in the
Aharonov-Arad balanced commutator approach equals `-i · σ_x` at the
non-shared indices — an OFF-DIAGONAL contribution that must be cancelled
by counterterms. -/

/-- **Cross-term commutator identity** for σ_y/σ_x adjacent-block pair:
`[σ_y(a, b), σ_x(b, c)] = -i · σ_x(a, c)` for distinct `a, b, c ∈ Fin d`. -/
theorem sigmaY_sigmaX_cross_term_share_middle {d : ℕ}
    {a b c : Fin d} (h_ab : a ≠ b) (h_bc : b ≠ c) (h_ac : a ≠ c) :
    sigmaYBlock a b * sigmaXBlock b c - sigmaXBlock b c * sigmaYBlock a b =
      (-Complex.I) • sigmaXBlock a c := by
  rw [sigmaYBlock_mul_sigmaXBlock_share_middle h_ab h_bc h_ac,
      sigmaXBlock_mul_sigmaYBlock_share_middle h_ab h_bc h_ac]
  -- Goal: single a c (-I) - single c a I = -I · σ_x(a, c)
  -- σ_x(a, c) = single a c 1 + single c a 1
  -- -I · σ_x(a, c) = single a c (-I) + single c a (-I)
  -- LHS: single a c (-I) - single c a I = single a c (-I) + single c a (-I) ✓
  ext p q
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply,
             sigmaXBlock_apply, smul_eq_mul]
  -- Goal: (if a=p∧c=q then -I else 0) - (if c=p∧a=q then I else 0)
  --       = -I · ((if a=p∧c=q then 1 else 0) + (if c=p∧a=q then 1 else 0))
  by_cases hac_pq : a = p ∧ c = q
  · obtain ⟨rfl, rfl⟩ := hac_pq
    have h_ca_pq : ¬ (c = a ∧ a = c) := fun ⟨h, _⟩ => h_ac h.symm
    simp [if_neg h_ca_pq]
  · by_cases hca_pq : c = p ∧ a = q
    · obtain ⟨rfl, rfl⟩ := hca_pq
      have h_ac_pq : ¬ (a = c ∧ c = a) := fun ⟨h, _⟩ => h_ac h
      simp [if_neg h_ac_pq]
    · simp [if_neg hac_pq, if_neg hca_pq]

end SKEFTHawking.FKLW.GenericSUd
