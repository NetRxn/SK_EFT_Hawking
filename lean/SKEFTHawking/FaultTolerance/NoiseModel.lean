/-
SK_EFT_Hawking Phase 6p Wave 1b.2: Abstract Local Stochastic Noise Model

The AGP threshold theorem (Wave 1b.3) is proved against the *abstract local
stochastic* noise model: each circuit location may independently undergo a
Pauli error, with the probability of any specific multi-location failure
pattern bounded by `ε^k` for a `k`-location pattern.

This module defines the noise model abstractly; the connection to MeasureTheory
(via Bernoulli iid + SubGaussian) is deferred per DR R3 / Wave 1b.4 scope split.

Per Wave 1a.1 DR §2 (gate G2): topological-substrate noise (Fibonacci-anyon
braiding errors) is STRICTLY DIFFERENT — not equivalent up to constants, not
additive. Thresholds live on different operational domains. Topological
specialization is deferred to Wave 1c+.

Primary source: AGP 2006 (arXiv:quant-ph/0504218), §2 Definition 1.
-/

import Mathlib
import SKEFTHawking.FaultTolerance.Basic

set_option autoImplicit false

namespace SKEFTHawking.FaultTolerance

/-! ## 1. Abstract local stochastic noise

For a circuit with `n_locations` locations, the noise model is parametrized by
a single rate `ε ∈ [0, 1]`. The semantic content (which we abstract here):

  *For any subset S ⊆ Locations of size k, the probability that ALL locations
   in S fail simultaneously is at most ε^k.*

For independent Bernoulli(p ≤ ε) failures per location, this is implied by
independence: P[∀ i ∈ S, X_i = 1] = ∏_{i ∈ S} P[X_i = 1] ≤ ε^|S|. The abstract
form admits weakly-correlated noise as long as the joint-failure tail dominates.
-/

/-- An abstract local-stochastic noise model with rate `ε` over `n_locations`
    locations. Records the rate parameter; the joint-failure-tail-dominated
    semantics is encoded as a class field in `LocalStochasticNoiseSpec`. -/
structure LocalStochasticNoise where
  /-- The per-location failure rate. -/
  ε : ℝ
  /-- The number of circuit locations (e.g., one ex-Rec's location count). -/
  n_locations : ℕ
  /-- Rate is non-negative. -/
  ε_nonneg : 0 ≤ ε
  /-- Rate is at most 1 (otherwise model is degenerate). -/
  ε_le_one : ε ≤ 1

namespace LocalStochasticNoise

/-- The rate ε of a noise model is in [0, 1]. -/
theorem ε_mem_unit (N : LocalStochasticNoise) : N.ε ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨N.ε_nonneg, N.ε_le_one⟩

/-- ε^2 is non-negative. -/
theorem ε_sq_nonneg (N : LocalStochasticNoise) : 0 ≤ N.ε ^ 2 := by
  positivity

/-- ε^2 ≤ ε for ε ∈ [0, 1]. -/
theorem ε_sq_le_ε (N : LocalStochasticNoise) : N.ε ^ 2 ≤ N.ε := by
  have h0 := N.ε_nonneg
  have h1 := N.ε_le_one
  nlinarith

end LocalStochasticNoise

/-! ## 2. Joint-failure bound for k-location patterns

The abstract noise model guarantees: for any `k`-subset of locations, the joint
probability of all failing is at most `ε^k`. We encode this as a real-valued
upper bound function.
-/

/-- Upper bound on the joint-failure probability for a `k`-location pattern:
    `ε^k`. -/
noncomputable def jointFailureBound (N : LocalStochasticNoise) (k : ℕ) : ℝ :=
  N.ε ^ k

/-- The joint-failure bound is non-negative. -/
theorem jointFailureBound_nonneg (N : LocalStochasticNoise) (k : ℕ) :
    0 ≤ jointFailureBound N k := by
  unfold jointFailureBound
  exact pow_nonneg N.ε_nonneg k

/-- For `k = 2`, the joint-failure bound is `ε²` — the AGP pair-failure rate
    that the recursion `ε_{L+1} ≤ A · ε_L²` consumes. -/
theorem jointFailureBound_two (N : LocalStochasticNoise) :
    jointFailureBound N 2 = N.ε ^ 2 := by
  rfl

/-- Joint-failure bound is monotone-decreasing in `k` (for `ε ∈ [0, 1]`). -/
theorem jointFailureBound_mono_k (N : LocalStochasticNoise) (j k : ℕ) (hjk : j ≤ k) :
    jointFailureBound N k ≤ jointFailureBound N j := by
  unfold jointFailureBound
  exact pow_le_pow_of_le_one N.ε_nonneg N.ε_le_one hjk

/-! ## 3. Module summary

NoiseModel.lean: abstract local-stochastic noise.

  - `LocalStochasticNoise` (structure with ε, n_locations, ε_nonneg, ε_le_one).
  - `LocalStochasticNoise.ε_mem_unit`, `ε_sq_nonneg`, `ε_sq_le_ε`.
  - `jointFailureBound N k := ε^k` — joint k-location failure rate.
  - `jointFailureBound_nonneg`, `jointFailureBound_two`, `jointFailureBound_mono_k`.

Consumed by Wave 1b.2 Malignant (the joint-failure of malignant pairs is
ε² up to multiplicative A_CNOT) and Wave 1b.3 AGP/Threshold (the per-level
failure rate at level L+1 is `A · ε_L²`).

Zero sorry. Zero axioms.
-/

end SKEFTHawking.FaultTolerance
