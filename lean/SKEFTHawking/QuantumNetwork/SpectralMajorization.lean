import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin

/-!
# Spectral majorization toward Fannes–Audenaert (Phase 6AL, Wave 4, item F1)

The upstream-infrastructure layer Mathlib lacks (no Ky Fan / Lidskii / Mirsky / eigenvalue-majorization
lemmas anywhere in Mathlib v4.29.1). We build it from the sorted-eigenvalue API (`eigenvalues₀`,
`eigenvalues₀_antitone`).

This file's foundational brick is the **rearrangement / fractional-knapsack inequality** `sum_mul_le_sum_top`:
for an antitone sequence `μ` and weights `p ∈ [0,1]` summing to `k`, the weighted sum `∑ μᵢ pᵢ` is bounded
by the sum of the `k` largest entries (the first `k`, since `μ` is sorted descending). This is the heart of
the Ky Fan maximum principle `∑_{i<k} λ↓ᵢ(A) = max over rank-k projections tr(PA)`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Finset

/-- **Rearrangement / fractional-knapsack inequality (core of the Ky Fan maximum principle):**
for an antitone `μ : Fin N → ℝ` and weights `p` with `0 ≤ pᵢ ≤ 1` summing to `k`, the weighted sum
`∑ μᵢ pᵢ` is at most the sum of the `k` largest entries `∑_{i<k} μᵢ`. -/
theorem sum_mul_le_sum_top {N : ℕ} (μ : Fin N → ℝ) (hμ : Antitone μ) (p : Fin N → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : ℕ) (hk : ∑ i, p i = (k : ℝ)) :
    ∑ i, μ i * p i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), μ i := by
  set ind : Fin N → ℝ := fun i => if (i : ℕ) < k then 1 else 0 with hind
  -- k ≤ N (since the weights are ≤ 1 and sum to k)
  have hkN : k ≤ N := by
    have : (k : ℝ) ≤ N := by
      rw [← hk]
      calc ∑ i, p i ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => hp1 i
        _ = N := by simp
    exact_mod_cast this
  -- the indicator sums to k
  have hindsum : ∑ i, ind i = (k : ℝ) := by
    rw [hind, Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right hkN]
  -- rewrite the RHS as a weighted sum with the indicator
  have hRHS : ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), μ i = ∑ i, μ i * ind i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hind]
    by_cases h : (i : ℕ) < k <;> simp [h]
  rw [hRHS, ← sub_nonpos, ← Finset.sum_sub_distrib]
  have hdiff : ∑ i, (μ i * p i - μ i * ind i) = ∑ i, μ i * (p i - ind i) := by
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [hdiff]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- k = 0: all weights vanish, both sides 0
    subst hk0
    have hp00 : ∀ i, p i = 0 := by
      have hsum0 : ∑ i, p i = 0 := by rw [hk]; simp
      intro i
      by_contra hne
      have : 0 < ∑ i, p i := Finset.sum_pos' (fun j _ => hp0 j)
        ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hp0 i) (Ne.symm hne)⟩
      rw [hsum0] at this; exact lt_irrefl _ this
    apply le_of_eq
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [hp00 i, hind]
  · -- k ≥ 1: threshold c = μ_{k-1}
    set c : ℝ := μ ⟨k - 1, by omega⟩ with hc
    have hsplit : ∑ i, μ i * (p i - ind i) = ∑ i, (μ i - c) * (p i - ind i) := by
      have h2 : ∑ i, (μ i - c) * (p i - ind i)
          = ∑ i, μ i * (p i - ind i) - c * ∑ i, (p i - ind i) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_; ring
      rw [h2, Finset.sum_sub_distrib, hk, hindsum, sub_self, mul_zero, sub_zero]
    rw [hsplit]
    refine Finset.sum_nonpos fun i _ => ?_
    by_cases h : (i : ℕ) < k
    · -- i < k: μ i ≥ c and p i - ind i ≤ 0
      have hμc : c ≤ μ i := by
        rw [hc]; apply hμ; simp only [Fin.le_def]; omega
      have hpind : p i - ind i ≤ 0 := by
        simp only [hind, if_pos h]; linarith [hp1 i]
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hμc) hpind
    · -- i ≥ k: μ i ≤ c and p i - ind i ≥ 0
      have hμc : μ i ≤ c := by
        rw [hc]; apply hμ; simp only [Fin.le_def]; omega
      have hpind : 0 ≤ p i - ind i := by
        simp only [hind, if_neg h]; linarith [hp0 i]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hμc) hpind

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A diagonal entry of an orthogonal projection (Hermitian idempotent) equals its squared column norm
`∑ₗ |Qₗⱼ|²`. -/
theorem proj_diag_eq_sum_normSq {Q : Matrix ι ι ℂ} (hQh : Q.IsHermitian) (hQ : Q * Q = Q) (j : ι) :
    Q j j = ((∑ l, Complex.normSq (Q l j) : ℝ) : ℂ) := by
  conv_lhs => rw [← hQ]
  rw [Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hjl : Q j l = star (Q l j) := by conv_lhs => rw [← hQh, Matrix.conjTranspose_apply]
  rw [hjl]
  exact Complex.normSq_eq_conj_mul_self.symm

omit [DecidableEq ι] in
/-- The diagonal entries of an orthogonal projection lie in `[0, 1]` (as reals); these are the weights
`pⱼ = ⟨eⱼ|P|eⱼ⟩` fed into the Ky Fan rearrangement inequality. -/
theorem proj_diag_re_mem_Icc {Q : Matrix ι ι ℂ} (hQh : Q.IsHermitian) (hQ : Q * Q = Q) (j : ι) :
    (Q j j).re ∈ Set.Icc (0 : ℝ) 1 := by
  have hsum := proj_diag_eq_sum_normSq hQh hQ j
  have hre : (Q j j).re = ∑ l, Complex.normSq (Q l j) := by rw [hsum, Complex.ofReal_re]
  have hnn : 0 ≤ (Q j j).re := by
    rw [hre]; exact Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _
  refine ⟨hnn, ?_⟩
  have him : (Q j j).im = 0 := by
    have hjj : star (Q j j) = Q j j := by conv_rhs => rw [← hQh, Matrix.conjTranspose_apply]
    exact Complex.conj_eq_iff_im.mp hjj
  have hjterm : Complex.normSq (Q j j) = (Q j j).re ^ 2 := by
    rw [Complex.normSq_apply, him]; ring
  have hjle : Complex.normSq (Q j j) ≤ ∑ l, Complex.normSq (Q l j) :=
    Finset.single_le_sum (f := fun l => Complex.normSq (Q l j))
      (fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
  rw [← hre, hjterm] at hjle
  nlinarith [hjle, hnn]

/-- Reindexing a function over the (index-`ι`) eigenvalues equals the sum over the sorted-descending
eigenvalues `eigenvalues₀ : Fin (card ι) → ℝ`. Bridges the two eigenvalue enumerations. -/
theorem sum_eigenvalues_eq_sum_eigenvalues₀ {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ∑ i, f (hA.eigenvalues i) = ∑ k, f (hA.eigenvalues₀ k) := by
  rw [Finset.sum_congr rfl (fun i _ =>
    (rfl : f (hA.eigenvalues i)
      = (fun k => f (hA.eigenvalues₀ k)) ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)))]
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k => f (hA.eigenvalues₀ k))

end SKEFTHawking.QuantumNetwork
