/-
SK_EFT_Hawking Phase 6t Iteration 2 sub-ship 3a (2026-05-22 PM late):
**The Dawson-Nielsen `ε_seq` error sequence**.

For a `(3/2)`-power recurrence `ε_{n+1} = K · ε_n^(3/2)`, define the sequence
recursively and prove the convergence properties needed by `skApprox_exists`
(forthcoming sub-ship 3b).

## Recursive definition + closed-form correspondence

  - `ε_seq K ε₀ 0 = ε₀`
  - `ε_seq K ε₀ (n+1) = K · (ε_seq K ε₀ n)^(3/2)`

The closed form (used in inductive bounds) is:

  `ε_seq K ε₀ n = (K^2 · ε₀)^((3/2)^n) / K^2`

with the convention that `f_n := K^2 · ε_seq K ε₀ n` satisfies `f_{n+1} =
f_n^(3/2)`. Under `f_0 = K^2 · ε₀ < 1`, `f_n → 0` super-quadratically.

## Phase 6t roadmap alignment

  - Sub-ship 3a (this module) → consumed by sub-ship 3b
    (`skApprox_exists` inductive proof). The recurrence form drives the
    induction; the closed form bounds give the asymptotic precision.

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED.

Primary source: Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006), 81–95;
                arXiv:quant-ph/0505030, §3.1.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.EpsilonSeq

/-! ## 1. Recursive definition -/

/-- **The Dawson-Nielsen error sequence (recursive form)**.

For parameters `K > 0` (the recursion's composite constant) and `ε₀ > 0`
(the base-case precision):
  - `ε_seq K ε₀ 0 = ε₀`
  - `ε_seq K ε₀ (n+1) = K · (ε_seq K ε₀ n)^(3/2)`. -/
noncomputable def ε_seq (K ε₀ : ℝ) : ℕ → ℝ
  | 0 => ε₀
  | n + 1 => K * (ε_seq K ε₀ n) ^ (3 / 2 : ℝ)

/-- Base-case unfolding (defeq). -/
lemma ε_seq_zero (K ε₀ : ℝ) : ε_seq K ε₀ 0 = ε₀ := rfl

/-- Successor-case unfolding (defeq). -/
lemma ε_seq_succ (K ε₀ : ℝ) (n : ℕ) :
    ε_seq K ε₀ (n + 1) = K * (ε_seq K ε₀ n) ^ (3 / 2 : ℝ) := rfl

/-! ## 2. Positivity + monotonicity

Under the convergence condition `K^2 · ε₀ < 1` (equivalently
`K · √ε₀ < 1`), the sequence is positive and `≤ ε₀` for all `n`. -/

/-- For `0 < K` and `0 < ε₀`, every `ε_seq K ε₀ n` is positive. -/
lemma ε_seq_pos (K ε₀ : ℝ) (hK_pos : 0 < K) (hε₀_pos : 0 < ε₀) :
    ∀ (n : ℕ), 0 < ε_seq K ε₀ n
  | 0 => hε₀_pos
  | n + 1 => by
      rw [ε_seq_succ]
      have h_pos := ε_seq_pos K ε₀ hK_pos hε₀_pos n
      have h_rpow_pos : 0 < (ε_seq K ε₀ n) ^ (3 / 2 : ℝ) :=
        Real.rpow_pos_of_pos h_pos _
      exact mul_pos hK_pos h_rpow_pos

/-- For `0 < K` and `0 < ε₀`, `ε_seq K ε₀ n` is non-negative. -/
lemma ε_seq_nonneg (K ε₀ : ℝ) (hK_pos : 0 < K) (hε₀_pos : 0 < ε₀) (n : ℕ) :
    0 ≤ ε_seq K ε₀ n :=
  le_of_lt (ε_seq_pos K ε₀ hK_pos hε₀_pos n)

/-- **Decreasingness step**: if `0 < K · ε^(1/2) ≤ 1`, then `K · ε^(3/2) ≤ ε`.

This is the per-step shrinkage: the next-level precision is `≤` current. -/
lemma ε_seq_step_le
    (K ε : ℝ) (hK_pos : 0 < K) (hε_pos : 0 < ε)
    (h_conv : K * ε ^ (1 / 2 : ℝ) ≤ 1) :
    K * ε ^ (3 / 2 : ℝ) ≤ ε := by
  -- `K · ε^(3/2) = (K · ε^(1/2)) · ε^1`.
  -- If `K · ε^(1/2) ≤ 1`, then `(K · ε^(1/2)) · ε ≤ 1 · ε = ε`.
  have h_split : K * ε ^ (3 / 2 : ℝ) = (K * ε ^ (1 / 2 : ℝ)) * ε := by
    have h_split_rpow : ε ^ (3 / 2 : ℝ) = ε ^ (1 / 2 : ℝ) * ε ^ (1 : ℝ) := by
      rw [← Real.rpow_add hε_pos]
      norm_num
    rw [h_split_rpow, Real.rpow_one]
    ring
  rw [h_split]
  calc K * ε ^ (1 / 2 : ℝ) * ε
      ≤ 1 * ε := mul_le_mul_of_nonneg_right h_conv hε_pos.le
    _ = ε := one_mul ε

/-- **Decreasing**: under the convergence condition `K · √ε₀ ≤ 1`, the
sequence is monotonically non-increasing: `ε_seq K ε₀ (n+1) ≤ ε_seq K ε₀ n`.

Note: the convergence condition `K^2 · ε₀ ≤ 1` (used in `ε_seq_le_ε_zero`)
is equivalent to `K · √ε₀ ≤ 1` via `K^2 · ε₀ = (K · √ε₀)^2`. -/
lemma ε_seq_decreasing
    (K ε₀ : ℝ) (hK_pos : 0 < K) (hε₀_pos : 0 < ε₀)
    (h_conv : K * ε₀ ^ (1 / 2 : ℝ) ≤ 1) :
    ∀ (n : ℕ), ε_seq K ε₀ (n + 1) ≤ ε_seq K ε₀ n := by
  intro n
  -- Induction shows each ε_seq K ε₀ n satisfies the same convergence form
  -- (since K · (ε_seq K ε₀ n)^(1/2) ≤ K · ε₀^(1/2) ≤ 1 for ε_seq n ≤ ε₀).
  rw [ε_seq_succ]
  have h_pos : 0 < ε_seq K ε₀ n := ε_seq_pos K ε₀ hK_pos hε₀_pos n
  -- We need `K · (ε_seq K ε₀ n)^(1/2) ≤ 1`. Bootstrap via induction.
  have h_bound_aux : ∀ m, ε_seq K ε₀ m ≤ ε₀ ∧
                          K * (ε_seq K ε₀ m) ^ (1 / 2 : ℝ) ≤ 1 := by
    intro m
    induction m with
    | zero =>
      refine ⟨le_refl _, ?_⟩
      simpa [ε_seq_zero] using h_conv
    | succ k ih =>
      obtain ⟨h_le, h_K_sqrt⟩ := ih
      have h_k_pos : 0 < ε_seq K ε₀ k := ε_seq_pos K ε₀ hK_pos hε₀_pos k
      -- ε_seq (k+1) = K · ε_k^(3/2) ≤ ε_k (by step_le) ≤ ε₀ (IH).
      have h_step : K * (ε_seq K ε₀ k) ^ (3 / 2 : ℝ) ≤ ε_seq K ε₀ k :=
        ε_seq_step_le K (ε_seq K ε₀ k) hK_pos h_k_pos h_K_sqrt
      refine ⟨?_, ?_⟩
      · rw [ε_seq_succ]; exact le_trans h_step h_le
      · -- K · ε_{k+1}^(1/2) ≤ K · ε_k^(1/2) ≤ 1 (since ε_{k+1} ≤ ε_k).
        have h_succ_le_k : ε_seq K ε₀ (k + 1) ≤ ε_seq K ε₀ k := by
          rw [ε_seq_succ]; exact h_step
        have h_succ_pos : 0 < ε_seq K ε₀ (k + 1) :=
          ε_seq_pos K ε₀ hK_pos hε₀_pos (k + 1)
        have h_rpow_mono :
            (ε_seq K ε₀ (k + 1)) ^ (1 / 2 : ℝ) ≤ (ε_seq K ε₀ k) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow h_succ_pos.le h_succ_le_k (by norm_num)
        calc K * (ε_seq K ε₀ (k + 1)) ^ (1 / 2 : ℝ)
            ≤ K * (ε_seq K ε₀ k) ^ (1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_left h_rpow_mono hK_pos.le
          _ ≤ 1 := h_K_sqrt
  exact ε_seq_step_le K (ε_seq K ε₀ n) hK_pos h_pos (h_bound_aux n).2

/-- **Bounded by ε₀**: under the convergence condition, every level satisfies
`ε_seq K ε₀ n ≤ ε₀`. -/
lemma ε_seq_le_ε_zero
    (K ε₀ : ℝ) (hK_pos : 0 < K) (hε₀_pos : 0 < ε₀)
    (h_conv : K * ε₀ ^ (1 / 2 : ℝ) ≤ 1)
    (n : ℕ) :
    ε_seq K ε₀ n ≤ ε₀ := by
  induction n with
  | zero => exact le_refl _
  | succ k ih =>
      have h_step : ε_seq K ε₀ (k + 1) ≤ ε_seq K ε₀ k :=
        ε_seq_decreasing K ε₀ hK_pos hε₀_pos h_conv k
      exact le_trans h_step ih

/-! ## 3. Half-shrinkage + existence-of-level

Under the STRICTER convergence condition `K · √a ≤ 1/2` (used by Phase 6t
Iteration 2 sub-ship 3b's `K_compose_sqrt_two_ε₀_lt_one`), the sequence
shrinks by a factor of at least `1/2` per step. This gives geometric
shrinkage `ε_seq K a n ≤ (1/2)^n · a`, which (via Archimedean property
on `(1/2)^n → 0`) gives ∃ a level `n` for any target precision `ε > 0`. -/

/-- **Per-step half-shrinkage**: under `K · √a ≤ 1/2`, the sequence shrinks
by a factor of at least 1/2 each step: `ε_seq K a (n+1) ≤ (1/2) · ε_seq K a n`. -/
lemma ε_seq_step_half_le
    (K a : ℝ) (hK_pos : 0 < K) (ha_pos : 0 < a)
    (h_conv_half : K * a ^ (1 / 2 : ℝ) ≤ 1 / 2) (n : ℕ) :
    ε_seq K a (n + 1) ≤ (1 / 2) * ε_seq K a n := by
  rw [ε_seq_succ]
  have h_n_pos : 0 < ε_seq K a n := ε_seq_pos K a hK_pos ha_pos n
  have h_n_le : ε_seq K a n ≤ a := by
    apply ε_seq_le_ε_zero K a hK_pos ha_pos
    linarith
  have h_split : (ε_seq K a n) ^ (3 / 2 : ℝ) =
      ε_seq K a n * (ε_seq K a n) ^ (1 / 2 : ℝ) := by
    have h_decomp : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [h_decomp, Real.rpow_add h_n_pos, Real.rpow_one]
  rw [h_split]
  have h_sqrt_le : (ε_seq K a n) ^ (1 / 2 : ℝ) ≤ a ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow h_n_pos.le h_n_le (by norm_num)
  have h_K_sqrt : K * (ε_seq K a n) ^ (1 / 2 : ℝ) ≤ 1 / 2 := by
    calc K * (ε_seq K a n) ^ (1 / 2 : ℝ)
        ≤ K * a ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left h_sqrt_le hK_pos.le
      _ ≤ 1 / 2 := h_conv_half
  calc K * (ε_seq K a n * (ε_seq K a n) ^ (1 / 2 : ℝ))
      = (K * (ε_seq K a n) ^ (1 / 2 : ℝ)) * ε_seq K a n := by ring
    _ ≤ (1 / 2) * ε_seq K a n :=
        mul_le_mul_of_nonneg_right h_K_sqrt h_n_pos.le

/-- **Geometric upper bound**: under `K · √a ≤ 1/2`, `ε_seq K a n ≤ (1/2)^n · a`. -/
lemma ε_seq_le_half_pow
    (K a : ℝ) (hK_pos : 0 < K) (ha_pos : 0 < a)
    (h_conv_half : K * a ^ (1 / 2 : ℝ) ≤ 1 / 2) :
    ∀ (n : ℕ), ε_seq K a n ≤ (1 / 2) ^ n * a := by
  intro n
  induction n with
  | zero =>
      rw [ε_seq_zero, pow_zero, one_mul]
  | succ k ih =>
      have h_step := ε_seq_step_half_le K a hK_pos ha_pos h_conv_half k
      calc ε_seq K a (k + 1)
          ≤ (1 / 2) * ε_seq K a k := h_step
        _ ≤ (1 / 2) * ((1 / 2) ^ k * a) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2) ^ (k + 1) * a := by ring

/-- **Existence of a level**: under `K · √a ≤ 1/2`, for any target precision
`ε > 0`, there exists a level `n` such that `ε_seq K a n ≤ ε`.

This is the key substrate for `skLevel_compose ε := Classical.choose`-based
selection in `SolovayKitaevRecursion.lean` (Phase 6t Iteration 2 sub-ship 4). -/
lemma exists_n_ε_seq_le
    (K a : ℝ) (hK_pos : 0 < K) (ha_pos : 0 < a)
    (h_conv_half : K * a ^ (1 / 2 : ℝ) ≤ 1 / 2)
    (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ n : ℕ, ε_seq K a n ≤ ε := by
  -- Find `n` such that `(1/2)^n < ε/a`.
  have hεa_pos : 0 < ε / a := div_pos hε_pos ha_pos
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hεa_pos (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have h_bound := ε_seq_le_half_pow K a hK_pos ha_pos h_conv_half n
  have h_strict : ε_seq K a n < ε := by
    calc ε_seq K a n
        ≤ (1 / 2) ^ n * a := h_bound
      _ < (ε / a) * a := mul_lt_mul_of_pos_right hn ha_pos
      _ = ε := div_mul_cancel₀ ε (ne_of_gt ha_pos)
  exact h_strict.le

/-! ## 4. Closed form

The recurrence `ε_seq K a (n+1) = K · ε_seq K a n ^ (3/2)` solves explicitly
as `ε_seq K a n = (K² · a)^((3/2)^n) / K²`. This is the substantive Dawson-
Nielsen closed form needed by Phase 6t Iteration 2 sub-ship 4 (polylog
skLevel formula).

Equivalent form using `f_n := K² · ε_seq K a n`: `f_{n+1} = f_n^(3/2)` with
`f_0 = K² · a`, hence `f_n = f_0^((3/2)^n)`. -/

/-- **Closed form of `ε_seq`**: `ε_seq K a n = (K² · a)^((3/2)^n) / K²`. -/
lemma ε_seq_closed_form
    (K a : ℝ) (hK_pos : 0 < K) (ha_pos : 0 < a) :
    ∀ n : ℕ, ε_seq K a n = (K^2 * a) ^ ((3/2 : ℝ)^n) / K^2 := by
  intro n
  induction n with
  | zero =>
      rw [ε_seq_zero, pow_zero, Real.rpow_one]
      have hK_sq_pos : 0 < K^2 := pow_pos hK_pos 2
      field_simp
  | succ k ih =>
      rw [ε_seq_succ, ih]
      have h_K_sq_pos : 0 < K^2 := pow_pos hK_pos 2
      have h_K2_a_pos : 0 < K^2 * a := mul_pos h_K_sq_pos ha_pos
      have h_K2_a_nn : 0 ≤ K^2 * a := h_K2_a_pos.le
      have h_K2_nn : 0 ≤ K^2 := h_K_sq_pos.le
      have h_K_nn : 0 ≤ K := hK_pos.le
      have h_rpow_pos : 0 < (K^2 * a) ^ ((3/2 : ℝ)^k) :=
        Real.rpow_pos_of_pos h_K2_a_pos _
      -- Step 1: ((K^2*a)^((3/2)^k) / K^2) ^ (3/2 : ℝ)
      --       = ((K^2*a)^((3/2)^k))^(3/2) / (K^2)^(3/2)
      rw [Real.div_rpow h_rpow_pos.le h_K2_nn]
      -- Step 2: ((K^2*a)^((3/2)^k))^(3/2) = (K^2*a)^((3/2)^k * 3/2)
      rw [← Real.rpow_mul h_K2_a_nn]
      have h_exp_succ : ((3/2 : ℝ))^k * (3/2 : ℝ) = (3/2 : ℝ)^(k + 1) := by
        rw [pow_succ]
      rw [h_exp_succ]
      -- Step 3: (K^2)^(3/2) = K^3.
      have h_K2_rpow_three_half : (K^2 : ℝ) ^ (3/2 : ℝ) = K^3 := by
        rw [show (K^2 : ℝ) = K ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast K 2).symm]
        rw [← Real.rpow_mul h_K_nn]
        rw [show ((2 : ℕ) : ℝ) * (3 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
        rw [Real.rpow_natCast]
      rw [h_K2_rpow_three_half]
      -- Step 4: K * (X / K^3) = X / K^2.
      have h_K_ne : (K : ℝ) ≠ 0 := ne_of_gt hK_pos
      field_simp

end SKEFTHawking.FKLW.EpsilonSeq

/-! ## 3. Module summary

EpsilonSeq.lean (Phase 6t Iteration 2 sub-ship 3a, 2026-05-22 PM late):
**The Dawson-Nielsen error sequence (recursive form)**.

  *Definition:*
  - `ε_seq K ε₀ n` — recursive: `0 ↦ ε₀`, `n+1 ↦ K · ε_seq K ε₀ n ^ (3/2)`

  *Headlines:*
  - `ε_seq_zero`, `ε_seq_succ` — defeq unfoldings
  - `ε_seq_pos`, `ε_seq_nonneg` — positivity
  - `ε_seq_step_le` — per-step shrinkage `K · ε^(3/2) ≤ ε` under `K · √ε ≤ 1`
  - `ε_seq_decreasing` — `ε_seq K ε₀ (n+1) ≤ ε_seq K ε₀ n` under `K · √ε₀ ≤ 1`
  - `ε_seq_le_ε_zero` — `ε_seq K ε₀ n ≤ ε₀` under the same condition

  *Pipeline Invariant compliance:*
  - Invariant #10 (no `maxHeartbeats`): RESPECTED
  - Invariant #15 (no new axioms): RESPECTED

Zero new project-local axioms. Pre-Phase-6t axiom count UNCHANGED. -/
