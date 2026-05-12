/-
SK_EFT_Hawking Phase 6p Wave 1b.4: Double-Exponential Recursion

Lean wrapper for the closed-form double-exponential bound derived from a
quadratic recursion. Used to close out the AGP concatenated-Steane threshold
theorem at Wave 1b.3 AGP/Threshold.lean.

The substantive lemma: if non-negative reals (ε_L)_{L≥0} satisfy
  ε_{L+1} ≤ A · ε_L²    (∀ L ≥ 0)
with A > 0 and 0 ≤ ε_0, then
  A · ε_L ≤ (A · ε_0)^(2^L)   (∀ L ≥ 0).

When A · ε_0 < 1 (the AGP threshold condition), this gives double-exponential
decay: A · ε_L ≤ exp(-c · 2^L) for c = -log(A · ε_0) > 0.

Primary source: Aliferis-Gottesman-Preskill 2006, arXiv:quant-ph/0504218
                §1 (the closed-form bound is standard).
-/

import Mathlib
import SKEFTHawking.FaultTolerance.Chernoff

namespace SKEFTHawking.FaultTolerance

/-! ## 1. The quadratic recursion closure

We work with non-negative sequences (ε : ℕ → ℝ) satisfying the AGP-form
recursion `ε (L+1) ≤ A · (ε L)²`.

The closed-form bound `A · ε L ≤ (A · ε 0)^(2^L)` follows by induction on L:
  - L = 0: A · ε 0 ≤ (A · ε 0)^(2^0) = A · ε 0 (refl).
  - L → L+1:
      A · ε (L+1) ≤ A · (A · (ε L)²) = (A · ε L)²
                  ≤ ((A · ε 0)^(2^L))² = (A · ε 0)^(2^(L+1))    (by IH and monotonicity)
-/

/-- The AGP closed-form double-exponential bound.

If `ε : ℕ → ℝ` satisfies non-negativity and the quadratic recursion
`ε (L+1) ≤ A · (ε L)²` for all `L`, with `A` non-negative, then
`A · ε L ≤ (A · ε 0)^(2^L)` for all `L`.

This is the standard closed-form bound from a quadratic recursion. When
`A · ε 0 < 1`, the right-hand side decays double-exponentially in `L`. -/
theorem agp_double_exp_bound
    (A : ℝ) (ε : ℕ → ℝ) (hA : 0 ≤ A)
    (hε_nn : ∀ L, 0 ≤ ε L)
    (hrec : ∀ L, ε (L + 1) ≤ A * (ε L) ^ 2) :
    ∀ L, A * ε L ≤ (A * ε 0) ^ (2 ^ L) := by
  intro L
  induction L with
  | zero =>
    simp
  | succ k ih =>
    -- Goal: A * ε (k+1) ≤ (A * ε 0)^(2^(k+1))
    have h_pos_AεL : 0 ≤ A * ε k := mul_nonneg hA (hε_nn k)
    -- Step 1: A * ε (k+1) ≤ A * (A * (ε k)²) = (A * ε k)²
    have h_step : A * ε (k + 1) ≤ (A * ε k) ^ 2 := by
      have h1 : A * ε (k + 1) ≤ A * (A * (ε k) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (hrec k) hA
      have h2 : A * (A * (ε k) ^ 2) = (A * ε k) ^ 2 := by ring
      linarith
    -- Step 2: (A * ε k)² ≤ ((A * ε 0)^(2^k))² = (A * ε 0)^(2^(k+1))
    have h_sq : (A * ε k) ^ 2 ≤ ((A * ε 0) ^ (2 ^ k)) ^ 2 := by
      have h_pos_target : 0 ≤ (A * ε 0) ^ (2 ^ k) := by
        apply pow_nonneg
        exact mul_nonneg hA (hε_nn 0)
      exact pow_le_pow_left₀ h_pos_AεL ih 2
    -- Step 3: combine
    have h_exp : ((A * ε 0) ^ (2 ^ k)) ^ 2 = (A * ε 0) ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, ← pow_succ, Nat.pow_succ, Nat.mul_comm]
    linarith

/-! ## 2. The AGP threshold condition

The natural strict form: if `A · ε 0 < 1`, the bound on the right-hand side
strictly decays to zero. -/

/-- Under the AGP threshold condition `A · ε 0 < 1` with `0 ≤ A · ε 0`,
    the right-hand-side bound is strictly less than 1, so logical-error
    suppression by concatenation is sustainable. -/
theorem agp_double_exp_bound_lt_one
    (A : ℝ) (ε : ℕ → ℝ) (hA : 0 ≤ A)
    (hε_nn : ∀ L, 0 ≤ ε L)
    (hrec : ∀ L, ε (L + 1) ≤ A * (ε L) ^ 2)
    (h_below_threshold : A * ε 0 < 1) :
    ∀ L, 1 ≤ L → A * ε L < 1 := by
  intro L hL
  have h_bound := agp_double_exp_bound A ε hA hε_nn hrec L
  have h_pos : 0 ≤ A * ε 0 := mul_nonneg hA (hε_nn 0)
  -- (A * ε 0)^(2^L) ≤ A * ε 0 < 1 for L ≥ 1 (since 2^L ≥ 2 ≥ 1 and base < 1)
  have h_pow : (A * ε 0) ^ (2 ^ L) ≤ A * ε 0 := by
    have h2L : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have h_pow_mono : (A * ε 0) ^ (2 ^ L) ≤ (A * ε 0) ^ 1 := by
      apply pow_le_pow_of_le_one h_pos (le_of_lt h_below_threshold)
      exact h2L
    simpa using h_pow_mono
  linarith

/-! ## 3. The pre-threshold case

If A · ε 0 ≥ 1, the recursion does NOT decay; we get a non-decreasing bound.
This case is OUTSIDE the AGP regime and the statement reflects that. -/

/-- The unconditional bound holds regardless of whether `A · ε 0 < 1`. -/
theorem agp_double_exp_bound_unconditional
    (A : ℝ) (ε : ℕ → ℝ) (hA : 0 ≤ A)
    (hε_nn : ∀ L, 0 ≤ ε L)
    (hrec : ∀ L, ε (L + 1) ≤ A * (ε L) ^ 2) :
    ∀ L, A * ε L ≤ (A * ε 0) ^ (2 ^ L) :=
  agp_double_exp_bound A ε hA hε_nn hrec

/-! ## 4. Module summary

DoubleExp.lean: closed-form double-exponential bound for AGP recursion.

  - `agp_double_exp_bound`: from `ε (L+1) ≤ A · (ε L)²` with `0 ≤ A`,
    `0 ≤ ε L`, derive `A · ε L ≤ (A · ε 0)^(2^L)`.
  - `agp_double_exp_bound_lt_one`: under threshold condition `A · ε 0 < 1`,
    `A · ε L < 1` for all `L ≥ 1`.
  - `agp_double_exp_bound_unconditional`: alias for the unconditional bound.

Consumed by Wave 1b.3 AGP/Threshold.lean — the AGP main theorem is exactly
this bound applied to the concatenated-Steane recursion `ε_{L+1} ≤ A_CNOT · ε_L²`.

Zero sorry. Zero axioms.
-/

end SKEFTHawking.FaultTolerance
