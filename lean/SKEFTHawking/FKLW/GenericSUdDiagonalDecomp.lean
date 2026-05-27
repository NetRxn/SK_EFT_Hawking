/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Diagonal-traceless H = Σ b_k · σ_z(k, k+1) decomposition

For a diagonal traceless `H = diag(a)` over `Fin (n+1)` (`n : ℕ`) with `∑ a = 0`,

  H = ∑_{k : Fin n} b_k · σ_z(k.castSucc, k.succ)

where `b_k = ∑_{j ≤ k} a_j` are the partial sums of `a`.

## Substantive content shipped

  * `partialSumCoeff` — partial-sum coefficient `b_k := ∑_{j ≤ k} a_j`.
  * `partialSumCoeff_zero`, `partialSumCoeff_succ`,
    `partialSumCoeff_last_of_traceless` — recurrence lemmas.
  * `castSucc_iverson_sum_eq` / `succ_iverson_sum_eq` — pointwise Iverson sums.
  * `diagonal_traceless_eq_sum_sigmaZ_pattern` — main decomposition theorem.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

/-! ## 1. Partial-sum coefficient -/

/-- **Partial-sum coefficient** for the σ_z-pair decomposition. Uses
if-then-else to handle index bounds at definition time. -/
noncomputable def partialSumCoeff {n : ℕ} (a : Fin (n + 1) → ℂ) (k : Fin n) : ℂ :=
  ∑ j ∈ Finset.range (k.val + 1), (if h : j < n + 1 then a ⟨j, h⟩ else 0)

/-- **First partial sum** at index 0: `b_0 = a_0`. -/
theorem partialSumCoeff_zero_apply {n : ℕ} (a : Fin (n + 2) → ℂ) :
    partialSumCoeff a (0 : Fin (n + 1)) = a 0 := by
  unfold partialSumCoeff
  show ∑ j ∈ Finset.range ((0 : Fin (n + 1)).val + 1),
        (if h : j < n + 2 then a ⟨j, h⟩ else 0) = a 0
  rw [show ((0 : Fin (n + 1)).val + 1) = 1 from rfl]
  rw [Finset.sum_range_one]
  rw [dif_pos (by omega : (0 : ℕ) < n + 2)]
  rfl

/-- **Successor recurrence**: `b_{k+1} = b_k + a_{k+1}`. -/
theorem partialSumCoeff_succ_apply {n : ℕ} (a : Fin (n + 2) → ℂ) (k : Fin n) :
    partialSumCoeff a (k.succ : Fin (n + 1)) =
      partialSumCoeff a (k.castSucc : Fin (n + 1)) +
        a ⟨k.val + 1, by have := k.isLt; omega⟩ := by
  unfold partialSumCoeff
  rw [show ((k.succ : Fin (n + 1)) : ℕ) + 1 = k.val + 2 from by simp [Fin.val_succ],
      show ((k.castSucc : Fin (n + 1)) : ℕ) + 1 = k.val + 1 from by simp [Fin.coe_castSucc]]
  rw [Finset.sum_range_succ]
  congr 1
  rw [dif_pos (by have := k.isLt; omega : k.val + 1 < n + 2)]

/-- **Last partial sum equals negative of last element** (for traceless `a`). -/
theorem partialSumCoeff_last_of_traceless {n : ℕ} (a : Fin (n + 2) → ℂ)
    (h_tr : ∑ k, a k = 0) :
    partialSumCoeff a (Fin.last n) = -a (Fin.last (n + 1)) := by
  have h_full : (∑ k : Fin (n + 2), a k) = 0 := h_tr
  rw [Fin.sum_univ_castSucc] at h_full
  -- h_full : ∑ k : Fin (n + 1), a k.castSucc + a (Fin.last (n + 1)) = 0
  have h_eq : partialSumCoeff a (Fin.last n) = ∑ k : Fin (n + 1), a k.castSucc := by
    unfold partialSumCoeff
    rw [show ((Fin.last n : Fin (n + 1)).val + 1) = n + 1 from rfl]
    -- Goal: ∑ j ∈ range (n + 1), (if h : j < n + 2 then a ⟨j, h⟩ else 0) = ∑ k, a k.castSucc
    rw [Finset.sum_range
        (fun j => (if h : j < n + 2 then a ⟨j, h⟩ else 0))]
    -- Goal: ∑ i : Fin (n + 1), (if h : i.val < n + 2 then a ⟨i.val, h⟩ else 0)
    --        = ∑ k : Fin (n + 1), a k.castSucc
    apply Finset.sum_congr rfl
    intro k _
    rw [dif_pos (by have := k.isLt; omega : k.val < n + 2)]
    rfl
  rw [h_eq]
  -- h_full : ∑ i, a i.castSucc + a (Fin.last (n + 1)) = 0
  -- Goal: ∑ k, a k.castSucc = -a (Fin.last (n + 1))
  linear_combination h_full

/-! ## 2. Pointwise Iverson sums -/

/-- **First Iverson sum**: `Σ k : Fin n, b_k · [k.castSucc = p]`. -/
theorem castSucc_iverson_sum_eq {n : ℕ} (b : Fin n → ℂ) (p : Fin (n + 1)) :
    (∑ k : Fin n, b k * (if k.castSucc = p then (1 : ℂ) else 0)) =
      (if h : p.val < n then b ⟨p.val, h⟩ else 0) := by
  by_cases hp : p.val < n
  · rw [dif_pos hp]
    rw [Finset.sum_eq_single ⟨p.val, hp⟩]
    · rw [if_pos]
      · ring
      · apply Fin.ext
        show (⟨p.val, hp⟩ : Fin n).castSucc.val = p.val
        rfl
    · intro k _ hk_ne
      rw [if_neg]
      · ring
      · intro h
        apply hk_ne
        apply Fin.ext
        show k.val = p.val
        have h_val : k.castSucc.val = p.val := by rw [h]
        simpa [Fin.coe_castSucc] using h_val
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hp]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    · ring
    · intro h
      apply hp
      have h_val : k.castSucc.val = p.val := by rw [h]
      have hk_lt : k.val < n := k.isLt
      have hcs : k.castSucc.val = k.val := rfl
      omega

/-- **Second Iverson sum**: `Σ k : Fin n, b_k · [k.succ = p]`. -/
theorem succ_iverson_sum_eq {n : ℕ} (b : Fin n → ℂ) (p : Fin (n + 1)) :
    (∑ k : Fin n, b k * (if k.succ = p then (1 : ℂ) else 0)) =
      (if h : 0 < p.val then b ⟨p.val - 1, by have := p.isLt; omega⟩ else 0) := by
  by_cases hp : 0 < p.val
  · have hp_le : p.val ≤ n := by have := p.isLt; omega
    have hp_sub : p.val - 1 < n := by omega
    rw [dif_pos hp]
    rw [Finset.sum_eq_single ⟨p.val - 1, hp_sub⟩]
    · rw [if_pos]
      · ring
      · apply Fin.ext
        show ((⟨p.val - 1, hp_sub⟩ : Fin n).succ : ℕ) = p.val
        show p.val - 1 + 1 = p.val
        omega
    · intro k _ hk_ne
      rw [if_neg]
      · ring
      · intro h
        apply hk_ne
        apply Fin.ext
        show k.val = p.val - 1
        have h_val : k.succ.val = p.val := by rw [h]
        have : k.val + 1 = p.val := by simpa [Fin.val_succ] using h_val
        omega
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hp]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    · ring
    · intro h
      apply hp
      have h_val : k.succ.val = p.val := by rw [h]
      have : k.val + 1 = p.val := by simpa [Fin.val_succ] using h_val
      omega

/-! ## 3. Matrix-level helpers -/

/-- **Sum of diagonal matrices is the diagonal of the sum**. -/
theorem matrix_diagonal_sum {d : ℕ} {m : Type*} [Fintype m]
    (f : m → Fin d → ℂ) :
    (∑ k, Matrix.diagonal (f k)) = Matrix.diagonal (∑ k, f k) := by
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, Matrix.sum_apply]
    simp only [Matrix.diagonal_apply_eq]
    rw [Finset.sum_apply]
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.diagonal_apply_ne _ hab]

/-! ## 4. Main decomposition theorem -/

/-- **Diagonal-traceless decomposition into σ_z-pair basis**.

For diagonal `H = diag(a)` with `a : Fin (n+2) → ℂ` and `∑ a = 0`,
we have `H = ∑_{k : Fin (n+1)} b_k · σ_z(k.castSucc, k.succ)` where
`b_k := a_0 + a_1 + ... + a_{k}` are the partial sums.

(We use `Fin (n+2)` parametrization so the σ_z-pair index set
`Fin (n+1)` is nonempty when applied substantively.) -/
theorem diagonal_traceless_eq_sum_sigmaZ_pattern {n : ℕ}
    (a : Fin (n + 2) → ℂ) (h_tr : ∑ k, a k = 0) :
    (Matrix.diagonal a : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) =
      ∑ k : Fin (n + 1), partialSumCoeff a k •
        sigmaZBlock k.castSucc k.succ := by
  ext p q
  rw [Matrix.diagonal_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, sigmaZBlock_apply, smul_eq_mul, mul_sub]
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl]
    -- Goal: a p = ∑ k, (b_k * (if k.castSucc = p ∧ k.castSucc = p then 1 else 0)
    --                 - b_k * (if k.succ = p ∧ k.succ = p then 1 else 0))
    -- Simplify and_self via simp_rw.
    simp_rw [and_self]
    rw [Finset.sum_sub_distrib]
    rw [castSucc_iverson_sum_eq, succ_iverson_sum_eq]
    -- Goal: a p = (if h : p.val < n+1 then b_⟨p.val, h⟩ else 0)
    --           - (if h : 0 < p.val then b_⟨p.val - 1, _⟩ else 0)
    -- Case on p.val.
    rcases Nat.eq_zero_or_pos p.val with hp0 | hp_pos
    · -- p.val = 0: first sum b_0, second sum 0
      have hp_lt : p.val < n + 1 := by have := p.isLt; omega
      rw [dif_pos hp_lt, dif_neg (by omega : ¬ 0 < p.val)]
      -- a p = b_⟨p.val, _⟩ - 0 = b_⟨0, _⟩ = a 0
      have hp_eq : p = (0 : Fin (n + 2)) := by
        apply Fin.ext; show p.val = 0; exact hp0
      rw [show (⟨p.val, hp_lt⟩ : Fin (n + 1)) = (0 : Fin (n + 1)) from by
        apply Fin.ext; show p.val = 0; exact hp0]
      rw [partialSumCoeff_zero_apply, hp_eq]
      ring
    · -- p.val ≥ 1
      by_cases hp_lt : p.val < n + 1
      · -- 0 < p.val < n+1 (could be n+1 - 1 = n, the second-to-last index, or earlier)
        rw [dif_pos hp_lt, dif_pos hp_pos]
        -- a p = b_⟨p.val, _⟩ - b_⟨p.val - 1, _⟩
        -- Set k := ⟨p.val - 1, ...⟩ : Fin n (since p.val - 1 < n when p.val < n + 1).
        have hpm1_lt_n : p.val - 1 < n := by omega
        have hk_succ_eq :
            ((⟨p.val - 1, hpm1_lt_n⟩ : Fin n).succ : Fin (n + 1)) =
              (⟨p.val, hp_lt⟩ : Fin (n + 1)) := by
          apply Fin.ext
          show p.val - 1 + 1 = p.val
          omega
        have hk_castSucc_eq :
            ((⟨p.val - 1, hpm1_lt_n⟩ : Fin n).castSucc : Fin (n + 1)) =
              (⟨p.val - 1, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext; rfl
        -- partialSumCoeff a ⟨p.val, _⟩ = partialSumCoeff a (⟨p.val-1, _⟩).succ
        rw [show (⟨p.val, hp_lt⟩ : Fin (n + 1)) =
              ((⟨p.val - 1, hpm1_lt_n⟩ : Fin n).succ : Fin (n + 1)) from hk_succ_eq.symm]
        rw [partialSumCoeff_succ_apply]
        rw [hk_castSucc_eq]
        -- Goal: a p = (b_⟨p.val-1, _⟩ + a ⟨p.val - 1 + 1, _⟩) - b_⟨p.val-1, _⟩
        rw [show a ⟨(⟨p.val - 1, hpm1_lt_n⟩ : Fin n).val + 1, by have := p.isLt; omega⟩ = a p
            from by
          congr 1; apply Fin.ext; show p.val - 1 + 1 = p.val; omega]
        ring
      · -- p.val = n + 1 (i.e., p = Fin.last (n+1))
        push_neg at hp_lt
        have hp_eq_n : p.val = n + 1 := by have := p.isLt; omega
        rw [dif_neg (by omega : ¬ p.val < n + 1), dif_pos hp_pos]
        -- a p = 0 - b_⟨p.val - 1, _⟩ = -b_⟨n, _⟩ = -b_(Fin.last n)
        have hp_last : p = Fin.last (n + 1) := by
          apply Fin.ext
          show p.val = n + 1
          exact hp_eq_n
        rw [show (⟨p.val - 1, by have := p.isLt; omega⟩ : Fin (n + 1)) =
              Fin.last n from by
          apply Fin.ext; show p.val - 1 = n; omega]
        rw [partialSumCoeff_last_of_traceless a h_tr, hp_last]
        ring
  · rw [if_neg hpq]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have h1 : ¬ (k.castSucc = p ∧ k.castSucc = q) := by
      intro ⟨hp, hq⟩; exact hpq (hp.symm.trans hq)
    have h2 : ¬ (k.succ = p ∧ k.succ = q) := by
      intro ⟨hp, hq⟩; exact hpq (hp.symm.trans hq)
    simp [if_neg h1, if_neg h2]

end SKEFTHawking.FKLW.GenericSUd
