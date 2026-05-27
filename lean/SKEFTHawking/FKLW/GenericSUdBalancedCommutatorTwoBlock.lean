/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — 2-block balanced commutator at SU(d)

The d-generic (d ≥ 2) balanced commutator at SU(d) for the **2-coordinate-
block case** of `BalancedCommutator_SUd`: for distinct standard-basis
indices `i ≠ j` in `Fin d` and θ ∈ [0, 1], the target

  H := single i i 1 - single j j 1  ∈ Matrix (Fin d) (Fin d) ℂ

(Hermitian, traceless, `‖H‖_linfty = 1`, σ_z-shaped in the (i, j) block)
admits an explicit balanced commutator via σ_y, σ_x lifted to the (i, j)
block.

## Substantive content shipped

  * `sigmaYBlock`, `sigmaXBlock`, `sigmaZBlock` — the d-generic 2-block
    Pauli analogs.
  * `sigmaYBlock_isHermitian`, `sigmaXBlock_isHermitian`,
    `sigmaZBlock_isHermitian` — Hermiticity.
  * `sigmaYBlock_trace`, `sigmaXBlock_trace`, `sigmaZBlock_trace` —
    tracelessness.

This is the substantive primitive for the Aharonov-Arad SU(d) spectral
decomposition (S.3 PROPER): the full case decomposes arbitrary Hermitian-
traceless H via spectral theorem + 2-block summation.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (2-block
primitive).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. 2-block Pauli analogs at indices (i, j) -/

/-- **2-block σ_y at indices (i, j)**: `-i` at `(i, j)`, `+i` at `(j, i)`,
zero elsewhere. -/
def sigmaYBlock {d : ℕ} (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.single i j (-Complex.I) + Matrix.single j i Complex.I

/-- **2-block σ_x at indices (i, j)**: `1` at `(i, j)`, `1` at `(j, i)`,
zero elsewhere. -/
def sigmaXBlock {d : ℕ} (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.single i j (1 : ℂ) + Matrix.single j i (1 : ℂ)

/-- **2-block σ_z at indices (i, j)**: `+1` at `(i, i)`, `-1` at `(j, j)`,
zero elsewhere. -/
def sigmaZBlock {d : ℕ} (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.single i i (1 : ℂ) - Matrix.single j j (1 : ℂ)

/-! ## 2. Pointwise evaluation lemmas -/

/-- **`sigmaYBlock` pointwise evaluation**. -/
theorem sigmaYBlock_apply {d : ℕ} (i j : Fin d) (a b : Fin d) :
    sigmaYBlock i j a b =
      (if i = a ∧ j = b then -Complex.I else 0) +
      (if j = a ∧ i = b then Complex.I else 0) := by
  simp only [sigmaYBlock, Matrix.add_apply, Matrix.single_apply]

/-- **`sigmaXBlock` pointwise evaluation**. -/
theorem sigmaXBlock_apply {d : ℕ} (i j : Fin d) (a b : Fin d) :
    sigmaXBlock i j a b =
      (if i = a ∧ j = b then (1 : ℂ) else 0) +
      (if j = a ∧ i = b then (1 : ℂ) else 0) := by
  simp only [sigmaXBlock, Matrix.add_apply, Matrix.single_apply]

/-- **`sigmaZBlock` pointwise evaluation**. -/
theorem sigmaZBlock_apply {d : ℕ} (i j : Fin d) (a b : Fin d) :
    sigmaZBlock i j a b =
      (if i = a ∧ i = b then (1 : ℂ) else 0) -
      (if j = a ∧ j = b then (1 : ℂ) else 0) := by
  simp only [sigmaZBlock, Matrix.sub_apply, Matrix.single_apply]

/-! ## 3. Hermiticity -/

/-- **`sigmaYBlock` is Hermitian** for `i ≠ j`. -/
theorem sigmaYBlock_isHermitian {d : ℕ} {i j : Fin d} (h_ne : i ≠ j) :
    (sigmaYBlock i j).IsHermitian := by
  ext a b
  rw [Matrix.conjTranspose_apply, sigmaYBlock_apply, sigmaYBlock_apply]
  -- LHS: star ((σ_y) b a) = star ((if i=b∧j=a then -I) + (if j=b∧i=a then I))
  -- RHS: (if i=a∧j=b then -I) + (if j=a∧i=b then I)
  by_cases h_ab : (i = a ∧ j = b)
  · -- (a, b) = (i, j) case: LHS = star (0 + I) = -I = RHS (since j ≠ i ⟹ first ite false on swap)
    obtain ⟨rfl, rfl⟩ := h_ab
    have h_swap1 : ¬ (i = j ∧ j = i) := fun ⟨h, _⟩ => h_ne h
    have h_swap2 : (j = j ∧ i = i) := ⟨rfl, rfl⟩
    simp [if_pos (And.intro rfl rfl : i = i ∧ j = j),
          if_neg h_swap1, if_pos h_swap2,
          star_add, star_zero, Complex.star_def, Complex.conj_I,
          if_neg (show ¬ (j = i ∧ i = j) from fun ⟨h, _⟩ => h_ne h.symm)]
  · by_cases h_ba : (j = a ∧ i = b)
    · -- (a, b) = (j, i) case
      obtain ⟨rfl, rfl⟩ := h_ba
      have h_swap1 : ¬ (j = i ∧ i = j) := fun ⟨h, _⟩ => h_ne h.symm
      have h_swap2 : (i = i ∧ j = j) := ⟨rfl, rfl⟩
      have h_swap3 : ¬ (i = j ∧ j = i) := fun ⟨h, _⟩ => h_ne h
      simp [if_neg h_swap3, if_pos (And.intro rfl rfl : j = j ∧ i = i),
            if_pos h_swap2, if_neg h_swap1,
            star_add, Complex.star_def, Complex.conj_I]
    · -- All other (a, b): both sides are 0.
      -- (i = b ∧ j = a) contradicts h_ba (= ¬(j = a ∧ i = b)).
      have h_y1 : ¬ (i = b ∧ j = a) := fun ⟨hib, hja⟩ => h_ba ⟨hja, hib⟩
      -- (j = b ∧ i = a) contradicts h_ab (= ¬(i = a ∧ j = b)).
      have h_y2 : ¬ (j = b ∧ i = a) := fun ⟨hjb, hia⟩ => h_ab ⟨hia, hjb⟩
      simp only [if_neg h_ab, if_neg h_ba, zero_add, add_zero, star_zero]
      simp [if_neg h_y1, if_neg h_y2]

/-- **`sigmaXBlock` is Hermitian** for `i ≠ j`. -/
theorem sigmaXBlock_isHermitian {d : ℕ} {i j : Fin d} (h_ne : i ≠ j) :
    (sigmaXBlock i j).IsHermitian := by
  ext a b
  rw [Matrix.conjTranspose_apply, sigmaXBlock_apply, sigmaXBlock_apply]
  by_cases h_ab : (i = a ∧ j = b)
  · obtain ⟨rfl, rfl⟩ := h_ab
    have h_swap2 : (j = j ∧ i = i) := ⟨rfl, rfl⟩
    have h_swap1 : ¬ (i = j ∧ j = i) := fun ⟨h, _⟩ => h_ne h
    have h_swap3 : ¬ (j = i ∧ i = j) := fun ⟨h, _⟩ => h_ne h.symm
    simp [if_pos (And.intro rfl rfl : i = i ∧ j = j),
          if_neg h_swap1, if_pos h_swap2, if_neg h_swap3,
          star_add, star_zero, Complex.star_def]
  · by_cases h_ba : (j = a ∧ i = b)
    · obtain ⟨rfl, rfl⟩ := h_ba
      have h_swap1 : ¬ (j = i ∧ i = j) := fun ⟨h, _⟩ => h_ne h.symm
      have h_swap2 : (i = i ∧ j = j) := ⟨rfl, rfl⟩
      have h_swap3 : ¬ (i = j ∧ j = i) := fun ⟨h, _⟩ => h_ne h
      simp [if_neg h_swap3, if_pos (And.intro rfl rfl : j = j ∧ i = i),
            if_pos h_swap2, if_neg h_swap1,
            star_add, Complex.star_def]
    · have h_y1 : ¬ (i = b ∧ j = a) := fun ⟨hib, hja⟩ => h_ba ⟨hja, hib⟩
      have h_y2 : ¬ (j = b ∧ i = a) := fun ⟨hjb, hia⟩ => h_ab ⟨hia, hjb⟩
      simp only [if_neg h_ab, if_neg h_ba, zero_add, star_zero]
      simp [if_neg h_y1, if_neg h_y2]

/-! ## 4. Tracelessness (for i ≠ j) -/

/-- **`sigmaYBlock i j` has trace 0** for `i ≠ j`. -/
theorem sigmaYBlock_trace {d : ℕ} {i j : Fin d} (h_ne : i ≠ j) :
    (sigmaYBlock i j).trace = 0 := by
  -- trace = ∑ k, σ_y[k][k] = ∑ k, [(if i=k∧j=k then -I) + (if j=k∧i=k then I)].
  -- Both ite branches require i = j, contradiction. So each summand is 0.
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.diag_apply, sigmaYBlock_apply]
  have h1 : ¬ (i = k ∧ j = k) := fun ⟨hi, hj⟩ => h_ne (hi.trans hj.symm)
  have h2 : ¬ (j = k ∧ i = k) := fun ⟨hj, hi⟩ => h_ne (hi.trans hj.symm)
  simp [if_neg h1, if_neg h2]

/-- **`sigmaXBlock i j` has trace 0** for `i ≠ j`. -/
theorem sigmaXBlock_trace {d : ℕ} {i j : Fin d} (h_ne : i ≠ j) :
    (sigmaXBlock i j).trace = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.diag_apply, sigmaXBlock_apply]
  have h1 : ¬ (i = k ∧ j = k) := fun ⟨hi, hj⟩ => h_ne (hi.trans hj.symm)
  have h2 : ¬ (j = k ∧ i = k) := fun ⟨hj, hi⟩ => h_ne (hi.trans hj.symm)
  simp [if_neg h1, if_neg h2]

/-- **`sigmaZBlock i j` has trace 0** for `i ≠ j` (the +1 at `(i,i)` and
`-1` at `(j,j)` cancel; for `i = j` the matrix would be 0 with trace 0
trivially, but we require `i ≠ j` to match the conventional shape). -/
theorem sigmaZBlock_trace {d : ℕ} {i j : Fin d} (h_ne : i ≠ j) :
    (sigmaZBlock i j).trace = 0 := by
  -- σ_z = single i i 1 - single j j 1, so trace = trace(single i i 1) - trace(single j j 1).
  rw [sigmaZBlock, Matrix.trace_sub]
  -- trace(single i i 1) = ∑ k, single i i 1 k k = ∑ k, if i = k ∧ i = k then 1 else 0.
  -- The condition simplifies to i = k. Sum is 1 (only contribution at k = i).
  have h_trace_single : ∀ (m : Fin d), (Matrix.single m m (1 : ℂ)).trace = 1 := by
    intro m
    rw [Matrix.trace]
    rw [show (∑ k : Fin d, (Matrix.single m m (1 : ℂ)).diag k) =
        (∑ k : Fin d, if k = m then (1 : ℂ) else 0) from by
          apply Finset.sum_congr rfl
          intro k _
          rw [Matrix.diag_apply, Matrix.single_apply]
          by_cases h : m = k
          · subst h; simp
          · have h' : k ≠ m := fun hk => h hk.symm
            simp [h, h']]
    simp [Finset.sum_ite_eq' Finset.univ m (fun _ => (1 : ℂ))]
  rw [h_trace_single i, h_trace_single j, sub_self]

/-- **`sigmaZBlock` is Hermitian**. -/
theorem sigmaZBlock_isHermitian {d : ℕ} (i j : Fin d) :
    (sigmaZBlock i j).IsHermitian := by
  ext a b
  rw [Matrix.conjTranspose_apply, sigmaZBlock_apply, sigmaZBlock_apply]
  -- σ_z b a = (if i=b∧i=a then 1 else 0) - (if j=b∧j=a then 1 else 0).
  -- star of real-valued (ℂ-coerced 1 and 0) is itself.
  by_cases h_ai : i = a
  · subst h_ai
    by_cases h_bi : i = b
    · subst h_bi
      simp [if_pos (And.intro rfl rfl : i = i ∧ i = i), star_sub,
            Complex.star_def, star_one, star_zero]
    · have h_not : ¬ (i = i ∧ i = b) := by
        intro ⟨_, h⟩; exact h_bi h
      have h_not_swap : ¬ (i = b ∧ i = i) := by
        intro ⟨h, _⟩; exact h_bi h
      simp [if_neg h_not, if_neg h_not_swap, star_sub, star_zero]
      by_cases h_jb : j = b
      · subst h_jb
        simp [if_neg (show ¬ (j = i ∧ j = i) from fun ⟨h, _⟩ => h_bi h.symm),
              if_neg (show ¬ (j = j ∧ j = i) from fun ⟨_, h⟩ => h_bi h.symm)]
      · by_cases h_ji : j = i
        · subst h_ji
          have h_b_ne : ¬ (j = b ∧ j = j) := fun ⟨h, _⟩ => h_jb h
          have h_b_ne_swap : ¬ (j = j ∧ j = b) := fun ⟨_, h⟩ => h_jb h
          simp [if_neg h_b_ne, if_neg h_b_ne_swap]
        · simp [if_neg (show ¬ (j = i ∧ j = b) from fun ⟨h, _⟩ => h_ji h),
                if_neg (show ¬ (j = b ∧ j = i) from fun ⟨_, h⟩ => h_ji h)]
  · by_cases h_bi : i = b
    · subst h_bi
      have h_not : ¬ (i = a ∧ i = i) := by
        intro ⟨h, _⟩; exact h_ai h
      have h_not_swap : ¬ (i = i ∧ i = a) := by
        intro ⟨_, h⟩; exact h_ai h
      simp [if_neg h_not, if_neg h_not_swap, star_sub, star_zero]
      by_cases h_ja : j = a
      · subst h_ja
        by_cases h_ji : j = i
        · subst h_ji
          simp [if_neg (show ¬ (j = j ∧ j = j) from fun _ => h_ai rfl)]
        · simp [if_neg (show ¬ (j = i ∧ j = j) from fun ⟨h, _⟩ => h_ji h),
                if_neg (show ¬ (j = j ∧ j = i) from fun ⟨_, h⟩ => h_ji h)]
      · by_cases h_ji : j = i
        · subst h_ji
          have h_a_ne : ¬ (j = j ∧ j = a) := fun ⟨_, h⟩ => h_ja h
          have h_a_ne_swap : ¬ (j = a ∧ j = j) := fun ⟨h, _⟩ => h_ja h
          simp [if_neg h_a_ne, if_neg h_a_ne_swap]
        · simp [if_neg (show ¬ (j = a ∧ j = i) from fun ⟨h, _⟩ => h_ja h),
                if_neg (show ¬ (j = i ∧ j = a) from fun ⟨h, _⟩ => h_ji h)]
    · have h_not : ¬ (i = a ∧ i = b) := fun ⟨h, _⟩ => h_ai h
      have h_not_swap : ¬ (i = b ∧ i = a) := fun ⟨_, h⟩ => h_ai h
      simp [if_neg h_not, if_neg h_not_swap, star_sub, star_zero]
      by_cases h_ja : j = a
      · subst h_ja
        by_cases h_jb : j = b
        · subst h_jb
          simp [if_pos (And.intro rfl rfl : j = j ∧ j = j),
                Complex.star_def, star_one]
        · simp [if_neg (show ¬ (j = j ∧ j = b) from fun ⟨_, h⟩ => h_jb h),
                if_neg (show ¬ (j = b ∧ j = j) from fun ⟨h, _⟩ => h_jb h)]
      · by_cases h_jb : j = b
        · subst h_jb
          simp [if_neg (show ¬ (j = a ∧ j = j) from fun ⟨h, _⟩ => h_ja h),
                if_neg (show ¬ (j = j ∧ j = a) from fun ⟨_, h⟩ => h_ja h)]
        · simp [if_neg (show ¬ (j = a ∧ j = b) from fun ⟨h, _⟩ => h_ja h),
                if_neg (show ¬ (j = b ∧ j = a) from fun ⟨h, _⟩ => h_jb h)]

/-! ## 5. Product entry — `(σ_y · σ_x)[i][i] = -i` (single-entry primitive)

The simplest substantive entry of the σ_y · σ_x product: at coordinate
`(i, i)`, the product equals `-i`. Computed via `Matrix.mul_apply`
+ `Finset.sum_eq_single j` (only `k = j` gives nonzero contribution). -/

/-- **`(σ_y · σ_x)[i][i] = -i`** for `i ≠ j` (substantive single-entry
primitive toward the full product identity). -/
theorem sigmaYBlock_mul_sigmaXBlock_apply_diag_i {d : ℕ} {i j : Fin d}
    (h_ne : i ≠ j) :
    (sigmaYBlock i j * sigmaXBlock i j) i i = -Complex.I := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · -- At k = j: σ_y[i][j] = -I, σ_x[j][i] = 1. Product = -I.
    rw [sigmaYBlock_apply, sigmaXBlock_apply]
    -- σ_y[i][j]: (if i=i∧j=j then -I) + (if j=i∧i=j then I) = -I + 0 = -I.
    have h_yij1 : (i : Fin d) = i ∧ j = j := ⟨rfl, rfl⟩
    have h_yij2 : ¬ ((j : Fin d) = i ∧ i = j) := fun ⟨h, _⟩ => h_ne h.symm
    rw [if_pos h_yij1, if_neg h_yij2, add_zero]
    -- σ_x[j][i]: (if i=j∧j=i then 1) + (if j=j∧i=i then 1) = 0 + 1 = 1.
    have h_xji1 : ¬ ((i : Fin d) = j ∧ j = i) := fun ⟨h, _⟩ => h_ne h
    have h_xji2 : (j : Fin d) = j ∧ i = i := ⟨rfl, rfl⟩
    rw [if_neg h_xji1, if_pos h_xji2, zero_add]
    ring
  · intro k _ h_kj
    -- σ_y[i][k] · σ_x[k][i] = 0 for k ≠ j.
    rw [sigmaYBlock_apply, sigmaXBlock_apply]
    have h_y1 : ¬ ((i : Fin d) = i ∧ j = k) := fun ⟨_, h⟩ => h_kj h.symm
    have h_y2 : ¬ ((j : Fin d) = i ∧ i = k) := fun ⟨h, _⟩ => h_ne h.symm
    rw [if_neg h_y1, if_neg h_y2]
    ring
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **`(σ_y · σ_x)[j][j] = +i`** for `i ≠ j` (mirror entry: at `(j, j)`
the contribution is at `k = i`). -/
theorem sigmaYBlock_mul_sigmaXBlock_apply_diag_j {d : ℕ} {i j : Fin d}
    (h_ne : i ≠ j) :
    (sigmaYBlock i j * sigmaXBlock i j) j j = Complex.I := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · rw [sigmaYBlock_apply, sigmaXBlock_apply]
    -- σ_y[j][i]: (if i=j∧j=i then -I) + (if j=j∧i=i then I) = 0 + I = I.
    have h_yji1 : ¬ ((i : Fin d) = j ∧ j = i) := fun ⟨h, _⟩ => h_ne h
    have h_yji2 : (j : Fin d) = j ∧ i = i := ⟨rfl, rfl⟩
    rw [if_neg h_yji1, if_pos h_yji2, zero_add]
    -- σ_x[i][j]: (if i=i∧j=j then 1) + (if j=i∧i=j then 1) = 1 + 0 = 1.
    have h_xij1 : (i : Fin d) = i ∧ j = j := ⟨rfl, rfl⟩
    have h_xij2 : ¬ ((j : Fin d) = i ∧ i = j) := fun ⟨h, _⟩ => h_ne h.symm
    rw [if_pos h_xij1, if_neg h_xij2, add_zero]
    ring
  · intro k _ h_ki
    rw [sigmaYBlock_apply, sigmaXBlock_apply]
    have h_y1 : ¬ ((i : Fin d) = j ∧ j = k) := fun ⟨h, _⟩ => h_ne h
    have h_y2 : ¬ ((j : Fin d) = j ∧ i = k) := fun ⟨_, h⟩ => h_ki h.symm
    rw [if_neg h_y1, if_neg h_y2]
    ring
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Off-support zero entry**: `(σ_y · σ_x)[a][b] = 0` for `(a, b) ∉ {(i, i), (j, j)}`. -/
theorem sigmaYBlock_mul_sigmaXBlock_apply_off {d : ℕ} {i j : Fin d}
    (h_ne : i ≠ j) {a b : Fin d}
    (h_not_ii : ¬ (a = i ∧ b = i)) (h_not_jj : ¬ (a = j ∧ b = j)) :
    (sigmaYBlock i j * sigmaXBlock i j) a b = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [sigmaYBlock_apply, sigmaXBlock_apply]
  grind

/-! ## 6. Full product theorem: `σ_y · σ_x = single i i (-i) + single j j i` -/

/-- **Full product identity**: `σ_y_block · σ_x_block = single i i (-i) + single j j i`
for `i ≠ j`. Composes the diagonal-entry primitives + off-support zero entries
via `Matrix.ext`. -/
theorem sigmaYBlock_mul_sigmaXBlock {d : ℕ} {i j : Fin d} (h_ne : i ≠ j) :
    sigmaYBlock i j * sigmaXBlock i j =
      Matrix.single i i (-Complex.I) + Matrix.single j j Complex.I := by
  ext a b
  by_cases h_ai : a = i
  · by_cases h_bi : b = i
    · -- (a, b) = (i, i): LHS = -I, RHS = -I.
      cases h_ai; cases h_bi
      rw [sigmaYBlock_mul_sigmaXBlock_apply_diag_i h_ne]
      rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
      simp [Ne.symm h_ne]
    · -- a = i, b ≠ i: off-support; both LHS and RHS = 0.
      have h_not_ii : ¬ (a = i ∧ b = i) := fun ⟨_, h⟩ => h_bi h
      have h_not_jj : ¬ (a = j ∧ b = j) := fun ⟨h, _⟩ => by cases h_ai; exact h_ne h
      rw [sigmaYBlock_mul_sigmaXBlock_apply_off h_ne h_not_ii h_not_jj]
      rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
      grind
  · by_cases h_aj : a = j
    · by_cases h_bj : b = j
      · cases h_aj; cases h_bj
        rw [sigmaYBlock_mul_sigmaXBlock_apply_diag_j h_ne]
        rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
        simp [h_ne, h_ne.symm]
      · have h_not_ii : ¬ (a = i ∧ b = i) := fun ⟨h, _⟩ => h_ai h
        have h_not_jj : ¬ (a = j ∧ b = j) := fun ⟨_, h⟩ => h_bj h
        rw [sigmaYBlock_mul_sigmaXBlock_apply_off h_ne h_not_ii h_not_jj]
        rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
        grind
    · -- a ≠ i, a ≠ j: off-support, both sides 0.
      have h_not_ii : ¬ (a = i ∧ b = i) := fun ⟨h, _⟩ => h_ai h
      have h_not_jj : ¬ (a = j ∧ b = j) := fun ⟨h, _⟩ => h_aj h
      rw [sigmaYBlock_mul_sigmaXBlock_apply_off h_ne h_not_ii h_not_jj]
      rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
      grind

/-! ## 7. Mirror: `σ_x · σ_y = single i i i + single j j (-i)` -/

/-- **Off-support entry of σ_x · σ_y is zero**. Same proof structure as
the σ_y · σ_x version. -/
theorem sigmaXBlock_mul_sigmaYBlock_apply_off {d : ℕ} {i j : Fin d}
    (h_ne : i ≠ j) {a b : Fin d}
    (h_not_ii : ¬ (a = i ∧ b = i)) (h_not_jj : ¬ (a = j ∧ b = j)) :
    (sigmaXBlock i j * sigmaYBlock i j) a b = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [sigmaXBlock_apply, sigmaYBlock_apply]
  grind

/-- **`(σ_x · σ_y)[i][i] = +i`** for `i ≠ j`. -/
theorem sigmaXBlock_mul_sigmaYBlock_apply_diag_i {d : ℕ} {i j : Fin d}
    (h_ne : i ≠ j) :
    (sigmaXBlock i j * sigmaYBlock i j) i i = Complex.I := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [sigmaXBlock_apply, sigmaYBlock_apply]
    have h_xij1 : (i : Fin d) = i ∧ j = j := ⟨rfl, rfl⟩
    have h_xij2 : ¬ ((j : Fin d) = i ∧ i = j) := fun ⟨h, _⟩ => h_ne h.symm
    rw [if_pos h_xij1, if_neg h_xij2, add_zero]
    have h_yji1 : ¬ ((i : Fin d) = j ∧ j = i) := fun ⟨h, _⟩ => h_ne h
    have h_yji2 : (j : Fin d) = j ∧ i = i := ⟨rfl, rfl⟩
    rw [if_neg h_yji1, if_pos h_yji2, zero_add]
    ring
  · intro k _ h_kj
    rw [sigmaXBlock_apply, sigmaYBlock_apply]
    have h_x1 : ¬ ((i : Fin d) = i ∧ j = k) := fun ⟨_, h⟩ => h_kj h.symm
    have h_x2 : ¬ ((j : Fin d) = i ∧ i = k) := fun ⟨h, _⟩ => h_ne h.symm
    rw [if_neg h_x1, if_neg h_x2]
    ring
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **`(σ_x · σ_y)[j][j] = -i`** for `i ≠ j`. -/
theorem sigmaXBlock_mul_sigmaYBlock_apply_diag_j {d : ℕ} {i j : Fin d}
    (h_ne : i ≠ j) :
    (sigmaXBlock i j * sigmaYBlock i j) j j = -Complex.I := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · rw [sigmaXBlock_apply, sigmaYBlock_apply]
    have h_xji1 : ¬ ((i : Fin d) = j ∧ j = i) := fun ⟨h, _⟩ => h_ne h
    have h_xji2 : (j : Fin d) = j ∧ i = i := ⟨rfl, rfl⟩
    rw [if_neg h_xji1, if_pos h_xji2, zero_add]
    have h_yij1 : (i : Fin d) = i ∧ j = j := ⟨rfl, rfl⟩
    have h_yij2 : ¬ ((j : Fin d) = i ∧ i = j) := fun ⟨h, _⟩ => h_ne h.symm
    rw [if_pos h_yij1, if_neg h_yij2, add_zero]
    ring
  · intro k _ h_ki
    rw [sigmaXBlock_apply, sigmaYBlock_apply]
    have h_x1 : ¬ ((i : Fin d) = j ∧ j = k) := fun ⟨h, _⟩ => h_ne h
    have h_x2 : ¬ ((j : Fin d) = j ∧ i = k) := fun ⟨_, h⟩ => h_ki h.symm
    rw [if_neg h_x1, if_neg h_x2]
    ring
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Full mirror product identity**: `σ_x_block · σ_y_block = single i i i + single j j (-i)`
for `i ≠ j`. -/
theorem sigmaXBlock_mul_sigmaYBlock {d : ℕ} {i j : Fin d} (h_ne : i ≠ j) :
    sigmaXBlock i j * sigmaYBlock i j =
      Matrix.single i i Complex.I + Matrix.single j j (-Complex.I) := by
  ext a b
  by_cases h_ai : a = i
  · by_cases h_bi : b = i
    · cases h_ai; cases h_bi
      rw [sigmaXBlock_mul_sigmaYBlock_apply_diag_i h_ne]
      rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
      simp [Ne.symm h_ne]
    · have h_not_ii : ¬ (a = i ∧ b = i) := fun ⟨_, h⟩ => h_bi h
      have h_not_jj : ¬ (a = j ∧ b = j) := fun ⟨h, _⟩ => by cases h_ai; exact h_ne h
      rw [sigmaXBlock_mul_sigmaYBlock_apply_off h_ne h_not_ii h_not_jj]
      rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
      grind
  · by_cases h_aj : a = j
    · by_cases h_bj : b = j
      · cases h_aj; cases h_bj
        rw [sigmaXBlock_mul_sigmaYBlock_apply_diag_j h_ne]
        rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
        simp [h_ne]
      · have h_not_ii : ¬ (a = i ∧ b = i) := fun ⟨h, _⟩ => h_ai h
        have h_not_jj : ¬ (a = j ∧ b = j) := fun ⟨_, h⟩ => h_bj h
        rw [sigmaXBlock_mul_sigmaYBlock_apply_off h_ne h_not_ii h_not_jj]
        rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
        grind
    · have h_not_ii : ¬ (a = i ∧ b = i) := fun ⟨h, _⟩ => h_ai h
      have h_not_jj : ¬ (a = j ∧ b = j) := fun ⟨h, _⟩ => h_aj h
      rw [sigmaXBlock_mul_sigmaYBlock_apply_off h_ne h_not_ii h_not_jj]
      rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
      grind

/-! ## 8. The commutator identity `[σ_y, σ_x] = -2i · σ_z` -/

/-- **The d-generic 2-block Pauli commutator identity** at SU(d):
`[σ_y_block, σ_x_block] = -2i · σ_z_block` for `i ≠ j`. -/
theorem sigmaY_sigmaX_commutator {d : ℕ} {i j : Fin d} (h_ne : i ≠ j) :
    sigmaYBlock i j * sigmaXBlock i j - sigmaXBlock i j * sigmaYBlock i j =
      ((-2 : ℂ) * Complex.I) • sigmaZBlock i j := by
  rw [sigmaYBlock_mul_sigmaXBlock h_ne, sigmaXBlock_mul_sigmaYBlock h_ne, sigmaZBlock]
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply,
             smul_eq_mul]
  grind

/-! ## 9. linftyOp operator norm bounds: `‖σ_y_block‖, ‖σ_x_block‖, ‖σ_z_block‖ ≤ 1`

These are the load-bearing norm bounds needed by the d-generic Aharonov-Arad
`BalancedCommutator_SUd` discharge (rank-2 case): the F, G generators built
from `√(θ/2)·σ_y_block` and `√(θ/2)·σ_x_block` then satisfy `‖F‖, ‖G‖ ≤ √(θ/2)`. -/

/-- **`‖sigmaYBlock i j‖_linfty ≤ 1`** for `i ≠ j`.

Each row has at most one nonzero entry of magnitude 1: row `i` has `‖-I‖ = 1`
at column `j`, row `j` has `‖I‖ = 1` at column `i`, all other rows are zero.
The `linfty` operator norm is the sup of row sums (in `NNNorm`), bounded by 1. -/
theorem sigmaYBlock_linftyOpNorm_le_one {d : ℕ} {i j : Fin d} (h_ne : i ≠ j) :
    ‖sigmaYBlock i j‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  refine (NNReal.coe_le_coe.mpr ?_).trans_eq NNReal.coe_one
  refine Finset.sup_le ?_
  intro r _
  -- Goal: ∑ c, ‖(sigmaYBlock i j) r c‖₊ ≤ 1
  by_cases hr_i : r = i
  · subst r
    rw [Finset.sum_eq_single j]
    · rw [sigmaYBlock_apply]
      have h1 : (i : Fin d) = i ∧ j = j := ⟨rfl, rfl⟩
      have h2 : ¬ ((j : Fin d) = i ∧ i = j) := fun ⟨h, _⟩ => h_ne h.symm
      rw [if_pos h1, if_neg h2, add_zero]
      simp
    · intro c _ h_cj
      rw [sigmaYBlock_apply]
      have h1 : ¬ ((i : Fin d) = i ∧ j = c) := fun ⟨_, h⟩ => h_cj h.symm
      have h2 : ¬ ((j : Fin d) = i ∧ i = c) := fun ⟨h, _⟩ => h_ne h.symm
      rw [if_neg h1, if_neg h2, add_zero]
      simp
    · intro h; exact absurd (Finset.mem_univ j) h
  · by_cases hr_j : r = j
    · subst r
      rw [Finset.sum_eq_single i]
      · rw [sigmaYBlock_apply]
        have h1 : ¬ ((i : Fin d) = j ∧ j = i) := fun ⟨h, _⟩ => h_ne h
        have h2 : (j : Fin d) = j ∧ i = i := ⟨rfl, rfl⟩
        rw [if_neg h1, if_pos h2, zero_add]
        simp
      · intro c _ h_ci
        rw [sigmaYBlock_apply]
        have h1 : ¬ ((i : Fin d) = j ∧ j = c) := fun ⟨h, _⟩ => h_ne h
        have h2 : ¬ ((j : Fin d) = j ∧ i = c) := fun ⟨_, h⟩ => h_ci h.symm
        rw [if_neg h1, if_neg h2, add_zero]
        simp
      · intro h; exact absurd (Finset.mem_univ i) h
    · -- r ≠ i, r ≠ j: all entries 0.
      apply le_trans _ zero_le_one
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro c _
      rw [sigmaYBlock_apply]
      have h1 : ¬ ((i : Fin d) = r ∧ j = c) := fun ⟨h, _⟩ => hr_i h.symm
      have h2 : ¬ ((j : Fin d) = r ∧ i = c) := fun ⟨h, _⟩ => hr_j h.symm
      rw [if_neg h1, if_neg h2, add_zero]
      simp

/-- **`‖sigmaXBlock i j‖_linfty ≤ 1`** for `i ≠ j`.

Mirror of `sigmaYBlock_linftyOpNorm_le_one`: row `i` has `‖1‖ = 1` at column `j`,
row `j` has `‖1‖ = 1` at column `i`, all other rows zero. -/
theorem sigmaXBlock_linftyOpNorm_le_one {d : ℕ} {i j : Fin d} (h_ne : i ≠ j) :
    ‖sigmaXBlock i j‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  refine (NNReal.coe_le_coe.mpr ?_).trans_eq NNReal.coe_one
  refine Finset.sup_le ?_
  intro r _
  by_cases hr_i : r = i
  · subst r
    rw [Finset.sum_eq_single j]
    · rw [sigmaXBlock_apply]
      have h1 : (i : Fin d) = i ∧ j = j := ⟨rfl, rfl⟩
      have h2 : ¬ ((j : Fin d) = i ∧ i = j) := fun ⟨h, _⟩ => h_ne h.symm
      rw [if_pos h1, if_neg h2, add_zero]
      simp
    · intro c _ h_cj
      rw [sigmaXBlock_apply]
      have h1 : ¬ ((i : Fin d) = i ∧ j = c) := fun ⟨_, h⟩ => h_cj h.symm
      have h2 : ¬ ((j : Fin d) = i ∧ i = c) := fun ⟨h, _⟩ => h_ne h.symm
      rw [if_neg h1, if_neg h2, add_zero]
      simp
    · intro h; exact absurd (Finset.mem_univ j) h
  · by_cases hr_j : r = j
    · subst r
      rw [Finset.sum_eq_single i]
      · rw [sigmaXBlock_apply]
        have h1 : ¬ ((i : Fin d) = j ∧ j = i) := fun ⟨h, _⟩ => h_ne h
        have h2 : (j : Fin d) = j ∧ i = i := ⟨rfl, rfl⟩
        rw [if_neg h1, if_pos h2, zero_add]
        simp
      · intro c _ h_ci
        rw [sigmaXBlock_apply]
        have h1 : ¬ ((i : Fin d) = j ∧ j = c) := fun ⟨h, _⟩ => h_ne h
        have h2 : ¬ ((j : Fin d) = j ∧ i = c) := fun ⟨_, h⟩ => h_ci h.symm
        rw [if_neg h1, if_neg h2, add_zero]
        simp
      · intro h; exact absurd (Finset.mem_univ i) h
    · apply le_trans _ zero_le_one
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro c _
      rw [sigmaXBlock_apply]
      have h1 : ¬ ((i : Fin d) = r ∧ j = c) := fun ⟨h, _⟩ => hr_i h.symm
      have h2 : ¬ ((j : Fin d) = r ∧ i = c) := fun ⟨h, _⟩ => hr_j h.symm
      rw [if_neg h1, if_neg h2, add_zero]
      simp

/-- **`‖sigmaZBlock i j‖_linfty ≤ 1`** for `i ≠ j`.

Row `i` has `‖1‖ = 1` at column `i`, row `j` has `‖-1‖ = 1` at column `j`,
all other rows zero. -/
theorem sigmaZBlock_linftyOpNorm_le_one {d : ℕ} {i j : Fin d} (h_ne : i ≠ j) :
    ‖sigmaZBlock i j‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  refine (NNReal.coe_le_coe.mpr ?_).trans_eq NNReal.coe_one
  refine Finset.sup_le ?_
  intro r _
  by_cases hr_i : r = i
  · subst r
    rw [Finset.sum_eq_single i]
    · rw [sigmaZBlock_apply]
      have h1 : (i : Fin d) = i ∧ i = i := ⟨rfl, rfl⟩
      have h2 : ¬ ((j : Fin d) = i ∧ j = i) := fun ⟨h, _⟩ => h_ne h.symm
      rw [if_pos h1, if_neg h2, sub_zero]
      simp
    · intro c _ h_ci
      rw [sigmaZBlock_apply]
      have h1 : ¬ ((i : Fin d) = i ∧ i = c) := fun ⟨_, h⟩ => h_ci h.symm
      have h2 : ¬ ((j : Fin d) = i ∧ j = c) := fun ⟨h, _⟩ => h_ne h.symm
      rw [if_neg h1, if_neg h2, sub_zero]
      simp
    · intro h; exact absurd (Finset.mem_univ i) h
  · by_cases hr_j : r = j
    · subst r
      rw [Finset.sum_eq_single j]
      · rw [sigmaZBlock_apply]
        have h1 : ¬ ((i : Fin d) = j ∧ i = j) := fun ⟨h, _⟩ => h_ne h
        have h2 : (j : Fin d) = j ∧ j = j := ⟨rfl, rfl⟩
        rw [if_neg h1, if_pos h2, zero_sub]
        simp
      · intro c _ h_cj
        rw [sigmaZBlock_apply]
        have h1 : ¬ ((i : Fin d) = j ∧ i = c) := fun ⟨h, _⟩ => h_ne h
        have h2 : ¬ ((j : Fin d) = j ∧ j = c) := fun ⟨_, h⟩ => h_cj h.symm
        rw [if_neg h1, if_neg h2, sub_zero]
        simp
      · intro h; exact absurd (Finset.mem_univ j) h
    · apply le_trans _ zero_le_one
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro c _
      rw [sigmaZBlock_apply]
      have h1 : ¬ ((i : Fin d) = r ∧ i = c) := fun ⟨h, _⟩ => hr_i h.symm
      have h2 : ¬ ((j : Fin d) = r ∧ j = c) := fun ⟨h, _⟩ => hr_j h.symm
      rw [if_neg h1, if_neg h2, sub_zero]
      simp

/-! ## 10. Rank-2 σ_z-shape balanced commutator at SU(d)

For the σ_z-shaped Hermitian-traceless `H := σ_z_block i j = single i i 1 - single j j 1`
(satisfying `‖H‖_linfty = 1` for `i ≠ j`), the balanced commutator
`F·G - G·F = -iθ · H` admits explicit `F = √(θ/2)·σ_y_block`, `G = √(θ/2)·σ_x_block`
with `‖F‖, ‖G‖ ≤ √(θ/2)`. This is the substantive rank-2 case of the
Aharonov-Arad SU(d) balanced commutator theorem (`BalancedCommutator_SUd d`). -/

/-- **Balanced commutator construction for the σ_z-shape target at SU(d)**.

For `d ≥ 2`, `i ≠ j`, and `θ ∈ [0, 1]`, the explicit generators
`F := √(θ/2)·σ_y_block i j` and `G := √(θ/2)·σ_x_block i j` are traceless
Hermitian with `‖F‖, ‖G‖ ≤ √(θ/2)` and
`F·G - G·F = -iθ · σ_z_block i j`. -/
theorem balanced_commutator_sigmaZ_pattern_SUd {d : ℕ} {i j : Fin d}
    (h_ne : i ≠ j) (θ : ℝ) (hθ_nn : 0 ≤ θ) (_hθ_le_one : θ ≤ 1) :
    let c : ℂ := (Real.sqrt (θ/2) : ℂ)
    (c • sigmaYBlock i j).IsHermitian ∧
    (c • sigmaXBlock i j).IsHermitian ∧
    (c • sigmaYBlock i j).trace = 0 ∧
    (c • sigmaXBlock i j).trace = 0 ∧
    ‖c • sigmaYBlock i j‖ ≤ Real.sqrt (θ/2) ∧
    ‖c • sigmaXBlock i j‖ ≤ Real.sqrt (θ/2) ∧
    (c • sigmaYBlock i j) * (c • sigmaXBlock i j) -
      (c • sigmaXBlock i j) * (c • sigmaYBlock i j) =
        -((θ : ℂ) * Complex.I) • sigmaZBlock i j := by
  intro c
  have hθ2_nn : 0 ≤ θ/2 := by linarith
  have hc_self : IsSelfAdjoint c := by
    show star c = c
    rw [Complex.star_def, Complex.conj_ofReal]
  have hc_nn : 0 ≤ Real.sqrt (θ/2) := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- F.IsHermitian
    exact (sigmaYBlock_isHermitian h_ne).smul hc_self
  · -- G.IsHermitian
    exact (sigmaXBlock_isHermitian h_ne).smul hc_self
  · -- F.trace = 0
    rw [Matrix.trace_smul, sigmaYBlock_trace h_ne, smul_zero]
  · -- G.trace = 0
    rw [Matrix.trace_smul, sigmaXBlock_trace h_ne, smul_zero]
  · -- ‖F‖ ≤ √(θ/2)
    show ‖c • sigmaYBlock i j‖ ≤ Real.sqrt (θ/2)
    rw [norm_smul]
    have hc_norm : ‖c‖ = Real.sqrt (θ/2) := by
      show ‖(Real.sqrt (θ/2) : ℂ)‖ = Real.sqrt (θ/2)
      rw [Complex.norm_real, Real.norm_of_nonneg hc_nn]
    rw [hc_norm]
    calc Real.sqrt (θ/2) * ‖sigmaYBlock i j‖
        ≤ Real.sqrt (θ/2) * 1 := by
          gcongr
          exact sigmaYBlock_linftyOpNorm_le_one h_ne
      _ = Real.sqrt (θ/2) := mul_one _
  · -- ‖G‖ ≤ √(θ/2)
    show ‖c • sigmaXBlock i j‖ ≤ Real.sqrt (θ/2)
    rw [norm_smul]
    have hc_norm : ‖c‖ = Real.sqrt (θ/2) := by
      show ‖(Real.sqrt (θ/2) : ℂ)‖ = Real.sqrt (θ/2)
      rw [Complex.norm_real, Real.norm_of_nonneg hc_nn]
    rw [hc_norm]
    calc Real.sqrt (θ/2) * ‖sigmaXBlock i j‖
        ≤ Real.sqrt (θ/2) * 1 := by
          gcongr
          exact sigmaXBlock_linftyOpNorm_le_one h_ne
      _ = Real.sqrt (θ/2) := mul_one _
  · -- Commutator identity: F·G - G·F = -iθ · σ_z
    -- (c•σ_y)·(c•σ_x) - (c•σ_x)·(c•σ_y) = c² · (σ_y·σ_x - σ_x·σ_y) = c² · (-2i)·σ_z
    -- With c² = θ/2, this gives (θ/2)·(-2i)·σ_z = -iθ·σ_z.
    have h_smul_mul_smul : ∀ (M N : Matrix (Fin d) (Fin d) ℂ),
        (c • M) * (c • N) = (c * c) • (M * N) := by
      intros M N
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [h_smul_mul_smul, h_smul_mul_smul]
    rw [← smul_sub, sigmaY_sigmaX_commutator h_ne]
    -- Goal: (c * c) • ((-2 * Complex.I) • sigmaZBlock i j) = (-((θ : ℂ) * Complex.I)) • sigmaZBlock i j
    rw [smul_smul]
    congr 1
    -- Need: c * c * (-2 * Complex.I) = -((θ : ℂ) * Complex.I)
    -- c = √(θ/2) as ℂ. c² = θ/2 (as ℂ). So c² · (-2i) = -iθ.
    have hc_sq : c * c = ((θ/2 : ℝ) : ℂ) := by
      show (Real.sqrt (θ/2) : ℂ) * (Real.sqrt (θ/2) : ℂ) = ((θ/2 : ℝ) : ℂ)
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hθ2_nn]
    rw [hc_sq]
    push_cast
    ring

end SKEFTHawking.FKLW.GenericSUd
