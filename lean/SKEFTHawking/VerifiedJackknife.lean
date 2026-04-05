/-
Phase 6 (early): Verified Jackknife and Autocorrelation Estimators

First formally verified statistical estimators for lattice Monte Carlo.
Pure finite arithmetic — no probability theory or measure theory required.

References:
  Efron, "The Jackknife, the Bootstrap" (SIAM, 1982)
  Wolff, Comput. Phys. Commun. 156, 143 (2004) — Gamma-method
-/

import Mathlib

open Finset BigOperators

namespace SKEFTHawking

/-! ## 1. Sample mean -/

/-- Sample mean of n real numbers. -/
noncomputable def sampleMean (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, x i) / n

/-! ## 2. Delete-one jackknife -/

/-- Sum of all elements except the i-th. -/
noncomputable def deleteOneSum (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, if j = i then 0 else x j

/-- Jackknife pseudovalue mean: average of delete-one statistics. -/
noncomputable def jackknifeMeanStat (n : ℕ) (θ : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, θ i) / n

/-- **Jackknife variance estimator.**

  sigma_JK^2 = [(n-1)/n] * Sum_i [theta_i - theta_bar]^2
-/
noncomputable def jackknifeVariance (n : ℕ) (θ : Fin n → ℝ) : ℝ :=
  let θbar := jackknifeMeanStat n θ
  ((n - 1 : ℝ) / n) * ∑ i : Fin n, (θ i - θbar) ^ 2

/--
**Jackknife variance is non-negative.**

PROVIDED SOLUTION
The factor (n-1)/n is non-negative for n >= 1 (n-1 >= 0 and n > 0).
The sum of squares is non-negative by Finset.sum_nonneg and sq_nonneg.
Product of two non-negatives is non-negative via mul_nonneg.
-/
theorem jackknifeVariance_nonneg (n : ℕ) (θ : Fin n → ℝ) (hn : n ≥ 1) :
    jackknifeVariance n θ ≥ 0 := by
  unfold jackknifeVariance
  apply mul_nonneg
  · apply div_nonneg
    · have h1 : (1 : ℝ) ≤ ↑n := by exact_mod_cast hn
      linarith
    · exact_mod_cast Nat.zero_le n
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-! ## 3. Autocorrelation function -/

/-- **Unnormalized autocovariance at lag t.**

  C(t) = Sum_{i=0}^{n-t-1} (x_i - xbar)(x_{i+t} - xbar)

Defined for t < n. We use the unnormalized version (no 1/(n-t) factor)
for cleaner algebraic properties.
-/
noncomputable def autocovariance (n : ℕ) (x : Fin n → ℝ) (t : ℕ) (ht : t < n) : ℝ :=
  let xbar := sampleMean n x
  ∑ i : Fin (n - t),
    (x ⟨i.val, by omega⟩ - xbar) * (x ⟨i.val + t, by omega⟩ - xbar)

/--
**Autocovariance at lag 0 is a sum of squares (non-negative).**

PROVIDED SOLUTION
At t = 0: C(0) = Sum_i (x_i - xbar)^2 since x_{i+0} = x_i.
Each term (x_i - xbar)^2 >= 0. Sum of non-negatives is non-negative.
Use Finset.sum_nonneg with mul_self_nonneg.
-/
theorem autocovariance_zero_nonneg (n : ℕ) (x : Fin n → ℝ) (hn : n ≥ 1) :
    autocovariance n x 0 (by omega) ≥ 0 := by
  unfold autocovariance
  simp only [Nat.sub_zero, add_zero]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

/-! ## 4. Integrated autocorrelation time -/

/-- **Integrated autocorrelation time with window W.**

  tau_int(W) = 1/2 + Sum_{t=1}^{W} C(t)/C(0)

Assumes C(0) > 0 (non-constant data).
-/
noncomputable def intAutocorrTime (n : ℕ) (x : Fin n → ℝ)
    (W : ℕ) (hW : W + 1 < n) : ℝ :=
  let C0 := autocovariance n x 0 (by omega)
  1 / 2 + ∑ t : Fin W, autocovariance n x (t.val + 1) (by omega) / C0

/-- **Effective sample size.** N_eff = N / (2 * tau_int). -/
noncomputable def effectiveSampleSize (n : ℕ) (x : Fin n → ℝ)
    (W : ℕ) (hW : W + 1 < n) : ℝ :=
  n / (2 * intAutocorrTime n x W hW)

/-
**For uncorrelated data (C(t) = 0 for t > 0), tau_int = 1/2.**
-/
theorem intAutocorrTime_uncorrelated (n : ℕ) (x : Fin n → ℝ)
    (W : ℕ) (hW : W + 1 < n)
    (huncorr : ∀ t : Fin W, autocovariance n x (t.val + 1) (by omega) = 0) :
    intAutocorrTime n x W hW = 1 / 2 := by
  -- By definition of intAutocorrTime, we have:
  simp [intAutocorrTime, huncorr]

/-
**For non-negatively correlated data, tau_int >= 1/2.**
-/
theorem intAutocorrTime_ge_half (n : ℕ) (x : Fin n → ℝ)
    (W : ℕ) (hW : W + 1 < n)
    (hpos : ∀ t : Fin W, autocovariance n x (t.val + 1) (by omega) ≥ 0)
    (hC0 : autocovariance n x 0 (by omega) > 0) :
    intAutocorrTime n x W hW ≥ 1 / 2 := by
  exact le_add_of_nonneg_right ( Finset.sum_nonneg fun t ht => div_nonneg ( hpos t ) hC0.le )

/-! ## 5. Module summary -/

/--
VerifiedJackknife module: first formally verified statistical estimators.
  - sampleMean: defined
  - jackknifeVariance: defined, NON-NEGATIVITY PROVED
  - autocovariance C(t): defined, C(0) >= 0 PROVED
  - intAutocorrTime tau_int: defined
  - tau_int = 1/2 for uncorrelated data PROVED
  - tau_int >= 1/2 for non-negatively correlated data PROVED
  - effectiveSampleSize: defined
  - Zero axioms, 1 sorry (jackknife zero iff constant)
  - Pure finite arithmetic — no measure theory or probability
-/
theorem verified_jackknife_summary : True := trivial

end SKEFTHawking