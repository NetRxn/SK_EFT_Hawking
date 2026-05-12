/-
SK_EFT_Hawking Phase 6p Wave 1b.4: Chernoff (Union-Bound) Wrappers

Lean wrappers for the elementary pair-failure union bound used in the AGP
concatenated-Steane threshold theorem (Wave 1b.3 AGP/Threshold.lean).

Substantive content: for n iid Bernoulli(p ≤ ε) trials, the probability that
at least 2 of them succeed is at most C(n,2) · ε² (elementary union bound +
independence). This is what the AGP concatenation level recursion consumes;
sub-Gaussian Chernoff (Mathlib.Probability.Moments.SubGaussian) is the
substrate-level statement but the AGP proof only uses the pairwise form.

Module name retained for DR §6 module-decomposition compatibility; the
"Chernoff" label here refers to the abstract pair-failure bound class, not
specifically the moment-generating-function (MGF) variant. The Bernoulli→SubGaussian
instance + MeasureTheory wiring is deferred to a follow-up sub-wave.

Relation to existing libraries:
  - Mathlib.Probability.Moments.SubGaussian (Lean): provides MGF-based Chernoff
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun) at the MeasureTheory level.
    AGP threshold proof does NOT route through this; the elementary pair-failure
    bound below suffices.
  - Isabelle/HOL AFP 2023: Bennett/McDiarmid/Bernstein concentration formalized
    but no connected threshold theorem.

Primary source: Aliferis-Gottesman-Preskill 2006, arXiv:quant-ph/0504218
                (Quantum Inf. Comput. 6, 97–165), §§3–5.
-/

import Mathlib

namespace SKEFTHawking.FaultTolerance

open scoped BigOperators

/-! ## 1. The pair-failure bound (abstract form)

For n iid trials, each succeeding with probability ≤ ε, the probability that
*at least two* trials succeed is bounded by C(n,2) · ε².

This is provable from union bound + independence:
  P[∃ i < j, X_i = 1 ∧ X_j = 1] ≤ Σ_{i<j} P[X_i = 1] · P[X_j = 1] ≤ C(n,2) · ε².

At the Lean level, we abstract this as a real-valued upper-bound function and
prove the properties the AGP recursion consumes. The concrete MeasureTheory
instantiation is deferred.
-/

/-- The abstract pair-failure bound: C(n,2) · ε².

This is the upper bound on the probability that at least two of n iid Bernoulli(ε)
trials succeed. Used as the per-location failure rate in the AGP level recursion.
-/
noncomputable def pairFailureBound (n : ℕ) (ε : ℝ) : ℝ :=
  (n.choose 2 : ℝ) * ε ^ 2

/-- Pair-failure bound is non-negative (since `ε²` is always non-negative). -/
theorem pairFailureBound_nonneg (n : ℕ) (ε : ℝ) :
    0 ≤ pairFailureBound n ε := by
  unfold pairFailureBound
  positivity

/-- Pair-failure bound at n = 0 or n = 1: zero (no pairs exist).
    n = 0: choose 2 = 0. n = 1: choose 2 = 0. -/
theorem pairFailureBound_zero_when_n_lt_two (n : ℕ) (ε : ℝ) (hn : n < 2) :
    pairFailureBound n ε = 0 := by
  unfold pairFailureBound
  interval_cases n <;> simp

/-- Pair-failure bound is monotone in n (the count of trials).
    `ε²` is non-negative, so we only need monotonicity of `Nat.choose 2`. -/
theorem pairFailureBound_mono_n (m n : ℕ) (ε : ℝ) (hmn : m ≤ n) :
    pairFailureBound m ε ≤ pairFailureBound n ε := by
  unfold pairFailureBound
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast Nat.choose_le_choose 2 hmn
  · positivity

/-- Pair-failure bound is monotone in ε (for non-negative ε). -/
theorem pairFailureBound_mono_eps (n : ℕ) (ε₁ ε₂ : ℝ) (h₁ : 0 ≤ ε₁) (h₁₂ : ε₁ ≤ ε₂) :
    pairFailureBound n ε₁ ≤ pairFailureBound n ε₂ := by
  unfold pairFailureBound
  apply mul_le_mul_of_nonneg_left
  · exact sq_le_sq' (by linarith) h₁₂
  · positivity

/-- Coarse explicit upper bound: C(n,2) ≤ n²/2 ≤ n². -/
theorem pairFailureBound_le_nsq (n : ℕ) (ε : ℝ) :
    pairFailureBound n ε ≤ (n : ℝ)^2 * ε^2 := by
  unfold pairFailureBound
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h_nat : 2 * n.choose 2 ≤ n^2 := by
    induction n with
    | zero => simp
    | succ m _ =>
      rw [Nat.choose_two_right, Nat.succ_sub_one]
      have h1 : 2 * ((m + 1) * m / 2) ≤ (m + 1) * m := by
        rw [Nat.mul_comm 2 _]; exact Nat.div_mul_le_self _ _
      have h2 : (m + 1) * m ≤ (m + 1) ^ 2 := by
        rw [sq]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
      linarith
  have hch : (2 * n.choose 2 : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast h_nat
  linarith

/-! ## 2. Bridge to the AGP per-ex-Rec failure rate

The AGP threshold theorem at level L bounds the per-ex-Rec failure rate as:
  ε_{L+1} ≤ A · ε_L²
where A = A_CNOT is the malignant-pair count over the Steane CNOT ex-Rec.

This is exactly pairFailureBound(M, ε_L) for M the number of locations in the
ex-Rec — the malignant-pair count being a refinement that counts only pairs
whose simultaneous failure exits the recovery condition, A ≤ C(M,2).

The AGP recursion (Wave 1b.3 AGP/Threshold.lean) consumes the abstract form:
-/

/-- The AGP per-level recursion bound: ε_{L+1} ≤ A · ε_L². -/
def agpRecursionStep (A : ℝ) (εL : ℝ) : ℝ := A * εL ^ 2

/-- The recursion step is non-negative for non-negative A. -/
theorem agpRecursionStep_nonneg (A εL : ℝ) (hA : 0 ≤ A) :
    0 ≤ agpRecursionStep A εL := by
  unfold agpRecursionStep
  positivity

/-- The recursion step is monotone in the input failure rate ε_L
    (for non-negative ε_L and non-negative A). -/
theorem agpRecursionStep_mono (A : ℝ) (εL εL' : ℝ) (hA : 0 ≤ A) (h₀ : 0 ≤ εL) (h : εL ≤ εL') :
    agpRecursionStep A εL ≤ agpRecursionStep A εL' := by
  unfold agpRecursionStep
  apply mul_le_mul_of_nonneg_left _ hA
  exact sq_le_sq' (by linarith) h

/-! ## 3. Module summary

Chernoff.lean: elementary pair-failure union bound for AGP level recursion.

  - `pairFailureBound n ε := C(n,2) · ε²` — the abstract bound.
  - `pairFailureBound_nonneg`, `pairFailureBound_zero_when_n_lt_two`,
    `pairFailureBound_mono_n`, `pairFailureBound_mono_eps`, `pairFailureBound_le_nsq`
    — basic properties consumed by Wave 1b.3.
  - `agpRecursionStep A εL := A · εL²` — the AGP per-level recursion bound;
    A = A_CNOT (malignant-pair count) per ex-Rec.
  - `agpRecursionStep_nonneg`, `agpRecursionStep_mono` — properties consumed
    by Wave 1b.3 level induction.

Substrate-only: no Mathlib MeasureTheory dependency in this module. The
MeasureTheory connection (Bernoulli → SubGaussian instance + iid sum bound) is
deferred to a future sub-wave; the AGP proof at Wave 1b.3 uses only the
abstract real-valued form above.

Zero sorry. Zero axioms.
-/

end SKEFTHawking.FaultTolerance
