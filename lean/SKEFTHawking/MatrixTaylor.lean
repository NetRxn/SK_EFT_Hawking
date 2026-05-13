/-
SK_EFT_Hawking Phase 6p Wave 2d.2-followup: Matrix Taylor remainder bound.

This module lifts the scalar matrix-Taylor remainder
`Complex.norm_exp_sub_sum_le_exp_norm_sub_sum` to the matrix algebra
`Matrix (Fin d) (Fin d) ℂ` (under the `linftyOp` norm). The matrix Taylor
remainder is **Sub-lemma A** of the Dawson-Nielsen Lemma 3 discharge plan
documented in `MatrixBCH.lean §4`.

The statement (Theorem `norm_exp_sub_taylor_le`):

  For any `X : Matrix (Fin d) (Fin d) ℂ` and any `n : ℕ`:

    ‖NormedSpace.exp X − Σ k<n, (k!)⁻¹ • X^k‖
      ≤ Real.exp ‖X‖ − Σ k<n, ‖X‖^k / k!

This is the matrix analog of `Complex.norm_exp_sub_sum_le_exp_norm_sub_sum`
(Mathlib4: `Mathlib.Analysis.Complex.Exponential`). The proof strategy:

  1. Express `NormedSpace.exp X = ∑' k, (k!)⁻¹ • X^k` via
     `NormedSpace.exp_eq_tsum 𝕂 := ℂ` (matrix algebra over ℂ inherits
     `NormedAlgebra ℂ`).
  2. Split the `tsum` at `n` via `Summable.sum_add_tsum_nat_add`.
  3. Bound the tail in operator norm by the scalar tail using
     `norm_tsum_le_tsum_norm` and termwise
     `‖(k!)⁻¹ • X^k‖ ≤ ‖X‖^k / k!`.
  4. Identify the scalar tail with `Real.exp ‖X‖ − Σ k<n, ‖X‖^k / k!`
     via the real exponential series expansion.

This file is **substrate** for `MatrixBCH.lean`: zero project-local axioms,
zero sorries, in-tree per the amended Phase 6p axiom-sign-off policy
(2026-05-12 PM — substantive in-tree work implicitly authorized).

Primary source for the consumer: Dawson & Nielsen 2005 §5.2 Lemma 3
(arXiv:quant-ph/0505030), citing Rossmann 2002 Proposition 2, §1.3, p. 25.
The Dawson-Nielsen proof reads "easily verified using the standard series
expansion for matrix exponentials" — this file ships that series-expansion
remainder bound rigorously.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.MatrixTaylor

open NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Matrix Taylor remainder bound

For a complex matrix `X : Matrix (Fin d) (Fin d) ℂ` and any natural-number
truncation index `n`, the difference between the matrix exponential and its
truncated Taylor expansion is bounded in operator norm by the corresponding
scalar tail of the real exponential. -/

variable {d : ℕ} [Nonempty (Fin d)]

/-- Termwise norm bound: `‖(k!)⁻¹ • X^k‖ ≤ ‖X‖^k / k!`. -/
private lemma norm_smul_pow_le
    (X : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    ‖((k.factorial : ℂ)⁻¹) • X ^ k‖ ≤ ‖X‖ ^ k / k.factorial := by
  rw [norm_smul]
  have h_norm_inv :
      ‖((k.factorial : ℂ)⁻¹)‖ = (k.factorial : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [h_norm_inv]
  have h_pow : ‖X ^ k‖ ≤ ‖X‖ ^ k := norm_pow_le X k
  have h_inv_nonneg : (0 : ℝ) ≤ (k.factorial : ℝ)⁻¹ := by positivity
  calc (k.factorial : ℝ)⁻¹ * ‖X ^ k‖
      ≤ (k.factorial : ℝ)⁻¹ * ‖X‖ ^ k :=
        mul_le_mul_of_nonneg_left h_pow h_inv_nonneg
    _ = ‖X‖ ^ k / k.factorial := by
        rw [div_eq_inv_mul]

/-- The real-scalar exponential series identity:
    `Real.exp r = ∑' k, r^k / k!`. -/
private lemma real_exp_eq_tsum (r : ℝ) :
    Real.exp r = ∑' k : ℕ, r ^ k / k.factorial := by
  rw [Real.exp_eq_exp_ℝ]
  have h := NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)
  exact congrFun h r

/-- **Matrix Taylor remainder bound.** For any `X : Matrix (Fin d) (Fin d) ℂ`
and any `n : ℕ`:

  `‖exp X − Σ_{k<n} (k!)⁻¹ • X^k‖ ≤ Real.exp ‖X‖ − Σ_{k<n} ‖X‖^k / k!`.

This is the matrix analog of `Complex.norm_exp_sub_sum_le_exp_norm_sub_sum`.

**Proof.** Split `exp X = ∑' k, (k!)⁻¹ • X^k` (via `exp_eq_tsum 𝕂 := ℂ`)
into the partial sum plus the tail. The tail is `∑' k, ((k+n)!)⁻¹ • X^(k+n)`
by `Summable.sum_add_tsum_nat_add`. Bound the norm of the tail by
`∑' k, ‖X‖^(k+n) / (k+n)!` using `norm_tsum_le_tsum_norm` and the termwise
bound `‖(k!)⁻¹ • X^k‖ ≤ ‖X‖^k / k!`. Finally identify the scalar tail with
`Real.exp ‖X‖ − Σ_{k<n} ‖X‖^k / k!` via `Real.exp_eq_exp_ℝ`. -/
theorem norm_exp_sub_taylor_le (X : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    ‖NormedSpace.exp X -
        ∑ k ∈ Finset.range n, ((k.factorial : ℂ)⁻¹) • X ^ k‖
      ≤ Real.exp ‖X‖ - ∑ k ∈ Finset.range n, ‖X‖ ^ k / k.factorial := by
  -- (1) Express `exp X` as an absolutely-convergent power series.
  have h_exp_eq :
      NormedSpace.exp X = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • X ^ k := by
    have h := NormedSpace.exp_eq_tsum (𝕂 := ℂ) (𝔸 := Matrix (Fin d) (Fin d) ℂ)
    exact congrFun h X
  -- (2) Summability of the absolute (norm) series.
  have h_summ_norm :
      Summable fun k : ℕ => ‖((k.factorial : ℂ)⁻¹) • X ^ k‖ :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℂ)
      (𝔸 := Matrix (Fin d) (Fin d) ℂ) X
  -- Hence the matrix-valued series is summable.
  have h_summ :
      Summable fun k : ℕ => ((k.factorial : ℂ)⁻¹) • X ^ k :=
    h_summ_norm.of_norm
  -- (3) Split the `tsum` at `n`.
  have h_split :
      (∑ i ∈ Finset.range n, ((i.factorial : ℂ)⁻¹) • X ^ i)
        + ∑' i : ℕ, (((i + n).factorial : ℂ)⁻¹) • X ^ (i + n)
        = ∑' i : ℕ, ((i.factorial : ℂ)⁻¹) • X ^ i :=
    h_summ.sum_add_tsum_nat_add (k := n)
  -- (4) The matrix-valued tail equals the difference exp X − partial sum.
  have h_diff :
      NormedSpace.exp X
        - ∑ k ∈ Finset.range n, ((k.factorial : ℂ)⁻¹) • X ^ k
      = ∑' k : ℕ, (((k + n).factorial : ℂ)⁻¹) • X ^ (k + n) := by
    rw [h_exp_eq, ← h_split]; abel
  -- (5) Termwise norm bound on the shifted series.
  have h_term_bound : ∀ k : ℕ,
      ‖(((k + n).factorial : ℂ)⁻¹) • X ^ (k + n)‖
        ≤ ‖X‖ ^ (k + n) / (k + n).factorial :=
    fun k => norm_smul_pow_le X (k + n)
  -- (6) Summability of the scalar shifted series.
  have h_scalar_summ :
      Summable fun k : ℕ => ‖X‖ ^ k / k.factorial :=
    Real.summable_pow_div_factorial ‖X‖
  -- (7) Summability of the shifted scalar tail and the shifted matrix tail.
  have h_shift_matrix_summ :
      Summable fun k : ℕ =>
        ‖(((k + n).factorial : ℂ)⁻¹) • X ^ (k + n)‖ := by
    have := h_summ_norm
    rw [← summable_nat_add_iff n] at this
    convert this using 1
  -- (8) Bound `‖matrix tail‖ ≤ scalar tail`.
  have h_matrix_tail_norm :
      ‖∑' k : ℕ, (((k + n).factorial : ℂ)⁻¹) • X ^ (k + n)‖
        ≤ ∑' k : ℕ, ‖X‖ ^ (k + n) / (k + n).factorial := by
    -- First: norm of matrix tsum ≤ tsum of norms.
    have h1 :
        ‖∑' k : ℕ, (((k + n).factorial : ℂ)⁻¹) • X ^ (k + n)‖
          ≤ ∑' k : ℕ, ‖(((k + n).factorial : ℂ)⁻¹) • X ^ (k + n)‖ :=
      norm_tsum_le_tsum_norm h_shift_matrix_summ
    -- Second: scalar shifted summable.
    have h_scalar_shift_summ :
        Summable fun k : ℕ => ‖X‖ ^ (k + n) / (k + n).factorial := by
      have := h_scalar_summ
      rw [← summable_nat_add_iff n] at this
      convert this using 1
    -- Third: termwise → tsum monotonicity.
    have h2 :
        ∑' k : ℕ, ‖(((k + n).factorial : ℂ)⁻¹) • X ^ (k + n)‖
          ≤ ∑' k : ℕ, ‖X‖ ^ (k + n) / (k + n).factorial :=
      Summable.tsum_le_tsum h_term_bound h_shift_matrix_summ
        h_scalar_shift_summ
    exact h1.trans h2
  -- (9) Identify the scalar tail with `Real.exp ‖X‖ − Σ k<n, ‖X‖^k/k!`.
  have h_scalar_split :
      (∑ i ∈ Finset.range n, ‖X‖ ^ i / i.factorial)
        + ∑' i : ℕ, ‖X‖ ^ (i + n) / (i + n).factorial
        = ∑' i : ℕ, ‖X‖ ^ i / i.factorial :=
    h_scalar_summ.sum_add_tsum_nat_add (k := n)
  have h_real_exp : Real.exp ‖X‖ = ∑' k : ℕ, ‖X‖ ^ k / k.factorial :=
    real_exp_eq_tsum ‖X‖
  -- (10) Combine: rewrite the goal using (4), (8), (9), (then 10).
  rw [h_diff, h_real_exp, ← h_scalar_split]
  linarith [h_matrix_tail_norm]

/-! ## 2. Specialized order-2 bound (consumed by MatrixBCH.lean for Sub-lemma C) -/

/-- **Matrix Taylor remainder at order 2** specialized form. For any
`X : Matrix (Fin d) (Fin d) ℂ`:

  `‖exp X − (1 + X)‖ ≤ Real.exp ‖X‖ − (1 + ‖X‖)`.

This is the specific instance of `norm_exp_sub_taylor_le` at `n = 2`,
written with the Taylor sum expanded for downstream consumers in
`MatrixBCH.lean` (Sub-lemma C: bounding `exp(-[F,G]) - (1 - [F,G])`). -/
theorem norm_exp_sub_order2_le (X : Matrix (Fin d) (Fin d) ℂ) :
    ‖NormedSpace.exp X - (1 + X)‖
      ≤ Real.exp ‖X‖ - (1 + ‖X‖) := by
  have h := norm_exp_sub_taylor_le X 2
  -- Σ_{k<2} (k!)⁻¹ • X^k = 1 + X
  have h_lhs_sum :
      ∑ k ∈ Finset.range 2, ((k.factorial : ℂ)⁻¹) • X ^ k
        = 1 + X := by
    simp [Finset.sum_range_succ, Nat.factorial]
  have h_rhs_sum :
      ∑ k ∈ Finset.range 2, ‖X‖ ^ k / k.factorial
        = 1 + ‖X‖ := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [h_lhs_sum, h_rhs_sum] at h
  exact h

/-- **Loose quantitative quadratic bound on the matrix Taylor remainder at
order 2.** For any `X : Matrix (Fin d) (Fin d) ℂ`:

  `‖exp X − (1 + X)‖ ≤ ‖X‖² · exp(‖X‖)`.

This is the order-2 analog of `norm_exp_sub_order3_le_loose`. Consumed by
`MatrixBCH.lean` Sub-lemma C completion: applied to `X := -⁅F, G⁆` with
`‖⁅F, G⁆‖ ≤ 2δ²` (from `hermitian_commutator_norm_le`), it gives
`‖exp(-[F,G]) - (1 - [F,G])‖ ≤ (2δ²)² · exp(2δ²) = 4δ⁴ · exp(2δ²)`. -/
theorem norm_exp_sub_order2_le_loose (X : Matrix (Fin d) (Fin d) ℂ) :
    ‖NormedSpace.exp X - (1 + X)‖
      ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by
  have h_step1 := norm_exp_sub_order2_le X
  -- Real.exp ‖X‖ − (1 + ‖X‖) ≤ ‖X‖² · exp(‖X‖).
  -- Apply the complex Taylor remainder bound on the diagonal.
  have h_complex :
      ‖Complex.exp (‖X‖ : ℂ) -
          ∑ m ∈ Finset.range 2, ((‖X‖ : ℂ)) ^ m / (m.factorial : ℂ)‖
        ≤ ‖((‖X‖ : ℂ))‖ ^ 2 * Real.exp ‖((‖X‖ : ℂ))‖ :=
    Complex.norm_exp_sub_sum_le_norm_mul_exp ‖X‖ 2
  have h_norm_cast : ‖((‖X‖ : ℂ))‖ = ‖X‖ := by
    rw [Complex.norm_real]; exact abs_of_nonneg (norm_nonneg X)
  rw [h_norm_cast] at h_complex
  -- Σ_{k<2} ‖X‖^k/k! = 1 + ‖X‖
  have h_sum_real :
      ∑ m ∈ Finset.range 2, ((‖X‖ : ℂ)) ^ m / (m.factorial : ℂ)
        = ((1 + ‖X‖ : ℝ) : ℂ) := by
    push_cast
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [h_sum_real] at h_complex
  have h_complex_exp :
      Complex.exp (‖X‖ : ℂ) = ((Real.exp ‖X‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
  rw [h_complex_exp, ← Complex.ofReal_sub, Complex.norm_real] at h_complex
  -- Real.exp r − (1 + r) is nonneg for r ≥ 0.
  have h_diff_nn :
      (0 : ℝ) ≤ Real.exp ‖X‖ - (1 + ‖X‖) := by
    have := Real.add_one_le_exp ‖X‖
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg h_diff_nn] at h_complex
  exact h_step1.trans h_complex

/-! ## 3. Specialized order-3 bound (consumed by MatrixBCH.lean) -/

/-- **Matrix Taylor remainder at order 3** specialized form. For any
`X : Matrix (Fin d) (Fin d) ℂ`:

  `‖exp X − (1 + X + X²/2)‖ ≤ Real.exp ‖X‖ − (1 + ‖X‖ + ‖X‖²/2)`.

This is the specific instance of `norm_exp_sub_taylor_le` at `n = 3`,
written with the Taylor sum expanded for downstream consumers in
`MatrixBCH.lean`. -/
theorem norm_exp_sub_order3_le (X : Matrix (Fin d) (Fin d) ℂ) :
    ‖NormedSpace.exp X - (1 + X + ((2 : ℂ)⁻¹) • X ^ 2)‖
      ≤ Real.exp ‖X‖ - (1 + ‖X‖ + ‖X‖ ^ 2 / 2) := by
  have h := norm_exp_sub_taylor_le X 3
  -- Σ_{k<3} (k!)⁻¹ • X^k = 1 + X + (1/2) X²
  have h_lhs_sum :
      ∑ k ∈ Finset.range 3, ((k.factorial : ℂ)⁻¹) • X ^ k
        = 1 + X + ((2 : ℂ)⁻¹) • X ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  -- Σ_{k<3} ‖X‖^k / k! = 1 + ‖X‖ + ‖X‖²/2
  have h_rhs_sum :
      ∑ k ∈ Finset.range 3, ‖X‖ ^ k / k.factorial
        = 1 + ‖X‖ + ‖X‖ ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [h_lhs_sum, h_rhs_sum] at h
  exact h

/-- **Loose quantitative cubic bound on the matrix Taylor remainder at order 3.**
For any `X : Matrix (Fin d) (Fin d) ℂ`:

  `‖exp X − (1 + X + X²/2)‖ ≤ ‖X‖^3 · exp(‖X‖)`.

This is the always-valid form (no division by `n!`); for the BCH consumer the
constant absorption into `K ≤ 4` is sufficient. (The tighter `/6` form
requires `‖X‖ ≤ 1` via `Complex.exp_bound`, which holds in the BCH small-δ
regime but is not strictly needed for the K ≤ 4 absolute bound.) -/
theorem norm_exp_sub_order3_le_loose (X : Matrix (Fin d) (Fin d) ℂ) :
    ‖NormedSpace.exp X - (1 + X + ((2 : ℂ)⁻¹) • X ^ 2)‖
      ≤ ‖X‖ ^ 3 * Real.exp ‖X‖ := by
  have h_step1 := norm_exp_sub_order3_le X
  -- Real.exp ‖X‖ − (1 + ‖X‖ + ‖X‖²/2) ≤ ‖X‖³ · exp(‖X‖).
  -- Apply the complex Taylor remainder bound on the diagonal.
  have h_complex :
      ‖Complex.exp (‖X‖ : ℂ) -
          ∑ m ∈ Finset.range 3, ((‖X‖ : ℂ)) ^ m / (m.factorial : ℂ)‖
        ≤ ‖((‖X‖ : ℂ))‖ ^ 3 * Real.exp ‖((‖X‖ : ℂ))‖ :=
    Complex.norm_exp_sub_sum_le_norm_mul_exp ‖X‖ 3
  -- Now `‖(‖X‖ : ℂ)‖ = ‖X‖` (real cast).
  have h_norm_cast : ‖((‖X‖ : ℂ))‖ = ‖X‖ := by
    rw [Complex.norm_real]; exact abs_of_nonneg (norm_nonneg X)
  rw [h_norm_cast] at h_complex
  -- And the sum is real: Σ_{k<3} ‖X‖^k/k! = 1 + ‖X‖ + ‖X‖²/2 (as a real number).
  have h_sum_real :
      ∑ m ∈ Finset.range 3, ((‖X‖ : ℂ)) ^ m / (m.factorial : ℂ)
        = ((1 + ‖X‖ + ‖X‖ ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [h_sum_real] at h_complex
  -- Use Real.exp = (Complex.exp on ℝ).re and that ‖a − b‖ for ℝ casts coincides.
  have h_complex_exp :
      Complex.exp (‖X‖ : ℂ) = ((Real.exp ‖X‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
  rw [h_complex_exp, ← Complex.ofReal_sub, Complex.norm_real] at h_complex
  -- Now: ‖Real.exp ‖X‖ − (1 + ‖X‖ + ‖X‖²/2)‖ ≤ ‖X‖^3 · exp ‖X‖
  -- where the outer ‖·‖ is the real norm (= abs).
  -- The expression Real.exp r − (1 + r + r²/2) is nonneg for r ≥ 0,
  -- so the real norm equals the value itself.
  have h_diff_nn :
      (0 : ℝ) ≤ Real.exp ‖X‖ - (1 + ‖X‖ + ‖X‖ ^ 2 / 2) := by
    nlinarith [Real.quadratic_le_exp_of_nonneg (norm_nonneg X),
      sq_nonneg ‖X‖]
  rw [Real.norm_eq_abs, abs_of_nonneg h_diff_nn] at h_complex
  exact h_step1.trans h_complex

end SKEFTHawking.MatrixTaylor
