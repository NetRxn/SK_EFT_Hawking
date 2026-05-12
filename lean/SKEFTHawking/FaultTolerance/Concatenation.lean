/-
SK_EFT_Hawking Phase 6p Wave 1b.3: Concatenated Code Recursion

The concatenated code at level `L` is the Steane [[7,1,3]] code applied `L`
times recursively: each level-1 qubit is itself encoded in a Steane block,
and each level-1 gate is implemented as a level-1 extended rectangle.

The level-L logical error rate satisfies the AGP recursion:
  ε_{L+1} ≤ A · ε_L²
with `A = A_CNOT` as the dominant malignant-pair count for the concatenated
CNOT ex-Rec. This module formalizes the recursion at the abstract real-valued
level (the input rate ε_L → output rate ε_{L+1}); the closed-form double-
exponential bound is supplied by `DoubleExp.lean`.

Primary source: AGP 2006 (arXiv:quant-ph/0504218) §4.
-/

import Mathlib
import SKEFTHawking.FaultTolerance.Basic
import SKEFTHawking.FaultTolerance.NoiseModel
import SKEFTHawking.FaultTolerance.ExRec
import SKEFTHawking.FaultTolerance.Chernoff
import SKEFTHawking.FaultTolerance.DoubleExp

set_option autoImplicit false

namespace SKEFTHawking.FaultTolerance

/-! ## 1. The level-recursion sequence

Given a malignant-pair count `A` and initial failure rate `ε₀`, the AGP
recursion defines a sequence `(εL : ℕ → ℝ)` by `εL 0 = ε₀` and
`εL (L+1) = A · (εL L)²`.

For the threshold analysis we need both the *exact* recursion and an *upper
bound* sequence satisfying `≤` instead of `=` at each step. The exact
recursion is simpler and we use it directly.
-/

/-- The AGP exact level-recursion sequence: `εL 0 = ε₀`, `εL (L+1) = A · (εL L)²`. -/
noncomputable def agpLevelSequence (A ε₀ : ℝ) : ℕ → ℝ
  | 0 => ε₀
  | L + 1 => A * (agpLevelSequence A ε₀ L) ^ 2

/-- The recursion equation, definitionally. -/
theorem agpLevelSequence_succ (A ε₀ : ℝ) (L : ℕ) :
    agpLevelSequence A ε₀ (L + 1) = A * (agpLevelSequence A ε₀ L) ^ 2 := rfl

/-- The recursion at level 0 returns the initial rate. -/
theorem agpLevelSequence_zero (A ε₀ : ℝ) :
    agpLevelSequence A ε₀ 0 = ε₀ := rfl

/-- The recursion preserves non-negativity. -/
theorem agpLevelSequence_nonneg (A ε₀ : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε₀) :
    ∀ L, 0 ≤ agpLevelSequence A ε₀ L := by
  intro L
  induction L with
  | zero => exact hε
  | succ k ih =>
    rw [agpLevelSequence_succ]
    exact mul_nonneg hA (sq_nonneg _)

/-! ## 2. Connecting the level recursion to the double-exp closed form

The recursion `εL (L+1) ≤ A · (εL L)²` is exactly the hypothesis of
`agp_double_exp_bound`. We derive the closed-form bound for the AGP recursion.
-/

/-- The AGP closed-form bound on the level-recursion sequence:
    `A · εL L ≤ (A · ε₀)^(2^L)`. -/
theorem agpLevelSequence_double_exp_bound
    (A ε₀ : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε₀) :
    ∀ L, A * agpLevelSequence A ε₀ L ≤ (A * ε₀) ^ (2 ^ L) := by
  apply agp_double_exp_bound A (agpLevelSequence A ε₀) hA
  · exact agpLevelSequence_nonneg A ε₀ hA hε
  · intro L
    rw [agpLevelSequence_succ]

/-! ## 3. The AGP threshold condition for the concatenated code

If `A · ε₀ < 1`, the level-L logical error rate decays double-exponentially.
This is the AGP threshold condition: it gives `ε_L < 1/A` for all `L ≥ 1`.
-/

/-- Under the AGP threshold condition `A · ε₀ < 1`, the level-L rate satisfies
    `A · εL L < 1` for all `L ≥ 1`, i.e., the logical error rate stays below
    the threshold inverse-A. -/
theorem agpLevelSequence_below_threshold
    (A ε₀ : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε₀) (h_thr : A * ε₀ < 1) :
    ∀ L, 1 ≤ L → A * agpLevelSequence A ε₀ L < 1 := by
  apply agp_double_exp_bound_lt_one A (agpLevelSequence A ε₀) hA
  · exact agpLevelSequence_nonneg A ε₀ hA hε
  · intro L
    rw [agpLevelSequence_succ]
  · exact h_thr

/-! ## 4. Module summary

Concatenation.lean: level-recursion sequence + closed-form double-exp bound.

  - `agpLevelSequence A ε₀ L`: the level-L logical error rate.
  - `agpLevelSequence_succ`, `agpLevelSequence_zero`, `agpLevelSequence_nonneg`.
  - `agpLevelSequence_double_exp_bound`: `A · εL L ≤ (A · ε₀)^(2^L)`.
  - `agpLevelSequence_below_threshold`: under `A · ε₀ < 1`, the level-L rate
    is strictly below `1/A` for all `L ≥ 1`.

Consumed by Wave 1b.3 AGP/Threshold.lean (the main theorem).

Zero sorry. Zero axioms.
-/

end SKEFTHawking.FaultTolerance
