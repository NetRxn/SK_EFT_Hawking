/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 1(d) — the SHARP 1-D grid existence (Ross–Selinger Lemma 4.4, product form)

`GridProblem.lean` ships the center-rounding existence, which needs BOTH interval widths
`≥ 1+√2`. The paper's **Lemma 4.4** (arXiv:1403.2975v3; proof cited to Selinger arXiv:1212.6253
Lemmas 16–17) needs only the PRODUCT: `δ·Δ ≥ (1+√2)²` — the asymmetric form that the two-disk
bound (paper Lemma 5.23) consumes with a TINY ε-region width against a HUGE disk width, giving
the quantitative `k₂ ≤ 2 + 2log₂(1+√2) + 2log₂(1/ε)` seed-exponent bound (paper eq. (21)).

## The proof (Selinger's rescaling argument, formalized)

`OneDimCoverage δ Δ` = every position pair `(x, y)` admits `α = a + b√2 ∈ ℤ[√2]` with
`α ∈ [x, x+δ]` and `α• ∈ [y, y+Δ]`. Moves:
  * **monotone** in both widths;
  * **λ-rescale**: `Coverage δ Δ ↔ Coverage (λδ) (Δ/λ)` via `α ↦ λα` (`λ• = −λ⁻¹` flips and
    shrinks the conjugate interval — the flip is absorbed by the universally quantified `y`);
  * **swap**: `Coverage δ Δ → Coverage Δ δ` via `α ↦ α•`.
The **base case** `Coverage (1+√2) (√2)` is an explicit three-candidate analysis: with
`a := ⌊(x+y+√2)/2⌋ + 1`, `b := ⌊(x−y−√2)/(2√2)⌋ + 1`, one of `(a,b)`, `(a,b+1)`, `(a−1,b)`
always fits. Assembly: bracket `δ/(1+√2)` between consecutive `λ`-powers `λ^j ≤ · < λ^{j+1}`;
if `Δ ≥ √2·λ^{−j}` the un-swapped family at `j` dominates; otherwise `δΔ ≥ λ²` forces the
swapped family at `j+1` to dominate (using `λ ≥ 2`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.

## References

  * Ross–Selinger, arXiv:1403.2975v3, Lemma 4.4 (+ Lemma 5.23 / eq. (21) for the consumer).
  * Selinger, arXiv:1212.6253, Lemmas 16–17 (the rescaling proof formalized here).
-/

import SKEFTHawking.FKLW.RossSelinger.GridProblem
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger.GridProblem

/-! ### Coverage and the elementary moves -/

/-- `OneDimCoverage δ Δ`: every position pair admits a `ℤ[√2]`-point with value in the
`δ`-interval and conjugate in the `Δ`-interval. -/
def OneDimCoverage (δ Δ : ℝ) : Prop :=
  ∀ x y : ℝ, ∃ a b : ℤ,
    x ≤ (a : ℝ) + b * Real.sqrt 2 ∧ (a : ℝ) + b * Real.sqrt 2 ≤ x + δ ∧
    y ≤ (a : ℝ) - b * Real.sqrt 2 ∧ (a : ℝ) - b * Real.sqrt 2 ≤ y + Δ

theorem coverage_mono {δ Δ δ' Δ' : ℝ} (hδ : δ ≤ δ') (hΔ : Δ ≤ Δ')
    (h : OneDimCoverage δ Δ) : OneDimCoverage δ' Δ' := by
  intro x y
  obtain ⟨a, b, h1, h2, h3, h4⟩ := h x y
  exact ⟨a, b, h1, by linarith, h3, by linarith⟩

theorem coverage_swap {δ Δ : ℝ} (h : OneDimCoverage δ Δ) : OneDimCoverage Δ δ := by
  intro x y
  obtain ⟨a, b, h1, h2, h3, h4⟩ := h y x
  exact ⟨a, -b, by push_cast; linarith, by push_cast; linarith,
    by push_cast; linarith, by push_cast; linarith⟩

/-- λ-rescale up: `α ↦ λα = (a+2b) + (a+b)√2`; the conjugate scales by `λ• = −λ⁻¹ = 1−√2`. -/
theorem coverage_scale_up {δ Δ : ℝ} (h : OneDimCoverage δ Δ) :
    OneDimCoverage ((1 + Real.sqrt 2) * δ) (Δ / (1 + Real.sqrt 2)) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hl : (0 : ℝ) < 1 + Real.sqrt 2 := by linarith
  have hs1 : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have hΔeq : Δ / (1 + Real.sqrt 2) = (Real.sqrt 2 - 1) * Δ := by
    rw [div_eq_iff (ne_of_gt hl)]
    linear_combination (-Δ) * hsq
  intro x y
  obtain ⟨a, b, h1, h2, h3, h4⟩ :=
    h ((Real.sqrt 2 - 1) * x) (-(1 + Real.sqrt 2) * y - Δ)
  have h1' := mul_le_mul_of_nonneg_left h1 hl.le
  have h2' := mul_le_mul_of_nonneg_left h2 hl.le
  have h3' := mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ Real.sqrt 2 - 1)
  have h4' := mul_le_mul_of_nonneg_left h4 (by linarith : (0:ℝ) ≤ Real.sqrt 2 - 1)
  have hx : (1 + Real.sqrt 2) * ((Real.sqrt 2 - 1) * x) = x := by linear_combination x * hsq
  have hkey : (1 + Real.sqrt 2) * ((a : ℝ) + b * Real.sqrt 2)
      = ((a : ℝ) + 2 * b) + ((a : ℝ) + b) * Real.sqrt 2 := by linear_combination (b : ℝ) * hsq
  have hkey2 : (Real.sqrt 2 - 1) * ((a : ℝ) - b * Real.sqrt 2)
      = -(((a : ℝ) + 2 * b) - ((a : ℝ) + b) * Real.sqrt 2) := by
    linear_combination (-(b : ℝ)) * hsq
  have hy : (Real.sqrt 2 - 1) * (-(1 + Real.sqrt 2) * y - Δ)
      = -y - (Real.sqrt 2 - 1) * Δ := by linear_combination (-y) * hsq
  have hy2 : (Real.sqrt 2 - 1) * (-(1 + Real.sqrt 2) * y - Δ + Δ) = -y := by
    linear_combination (-y) * hsq
  refine ⟨a + 2 * b, a + b, ?_, ?_, ?_, ?_⟩
  · push_cast
    linarith [h1', hx, hkey]
  · push_cast
    nlinarith [h2', hx, hkey]
  · push_cast
    linarith [h4', hkey2, hy2]
  · push_cast
    rw [hΔeq]
    linarith [h3', hkey2, hy]

/-- λ-rescale down: `α ↦ λ⁻¹α = (−a+2b) + (a−b)√2`; the conjugate scales by `−λ`. -/
theorem coverage_scale_down {δ Δ : ℝ} (h : OneDimCoverage δ Δ) :
    OneDimCoverage (δ / (1 + Real.sqrt 2)) ((1 + Real.sqrt 2) * Δ) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hl : (0 : ℝ) < 1 + Real.sqrt 2 := by linarith
  have hs1 : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have hδeq : δ / (1 + Real.sqrt 2) = (Real.sqrt 2 - 1) * δ := by
    rw [div_eq_iff (ne_of_gt hl)]
    linear_combination (-δ) * hsq
  intro x y
  obtain ⟨a, b, h1, h2, h3, h4⟩ :=
    h ((1 + Real.sqrt 2) * x) ((Real.sqrt 2 - 1) * (-y) - Δ)
  have h1' := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ Real.sqrt 2 - 1)
  have h2' := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ Real.sqrt 2 - 1)
  have h3' := mul_le_mul_of_nonneg_left h3 hl.le
  have h4' := mul_le_mul_of_nonneg_left h4 hl.le
  have hx : (Real.sqrt 2 - 1) * ((1 + Real.sqrt 2) * x) = x := by linear_combination x * hsq
  have hkey : (Real.sqrt 2 - 1) * ((a : ℝ) + b * Real.sqrt 2)
      = (-(a : ℝ) + 2 * b) + ((a : ℝ) - b) * Real.sqrt 2 := by
    linear_combination (b : ℝ) * hsq
  have hkey2 : (1 + Real.sqrt 2) * ((a : ℝ) - b * Real.sqrt 2)
      = -((-(a : ℝ) + 2 * b) - ((a : ℝ) - b) * Real.sqrt 2) := by
    linear_combination (-(b : ℝ)) * hsq
  have hy : (1 + Real.sqrt 2) * ((Real.sqrt 2 - 1) * (-y) - Δ)
      = -y - (1 + Real.sqrt 2) * Δ := by linear_combination (-y) * hsq
  have hy2 : (1 + Real.sqrt 2) * ((Real.sqrt 2 - 1) * (-y) - Δ + Δ) = -y := by
    linear_combination (-y) * hsq
  refine ⟨-a + 2 * b, a - b, ?_, ?_, ?_, ?_⟩
  · push_cast
    linarith [h1', hx, hkey]
  · push_cast
    rw [hδeq]
    linarith [h2', hx, hkey]
  · push_cast
    linarith [h4', hkey2, hy2]
  · push_cast
    linarith [h3', hkey2, hy]

/-! ### The base case `(1+√2, √2)` -/

/-- **The base coverage** `(δ, Δ) = (1+√2, √2)` (Selinger arXiv:1212.6253 Lemma 17(d)): with
`a := ⌊(x+y+√2)/2⌋ + 1`, `b := ⌊(x−y−√2)/(2√2)⌋ + 1`, one of `(a, b)`, `(a, b+1)`, `(a−1, b)`
always fits. -/
theorem coverage_base : OneDimCoverage (1 + Real.sqrt 2) (Real.sqrt 2) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  intro x y
  set u : ℝ := (x + y + Real.sqrt 2) / 2 with hu
  set v : ℝ := (x - y - Real.sqrt 2) / (2 * Real.sqrt 2) with hv
  set a : ℤ := ⌊u⌋ + 1 with ha
  set b : ℤ := ⌊v⌋ + 1 with hb
  -- bracketing
  have hua : u < (a : ℝ) := by
    rw [ha]
    push_cast
    exact Int.lt_floor_add_one u
  have hua' : (a : ℝ) ≤ u + 1 := by
    rw [ha]
    push_cast
    have := Int.floor_le u
    linarith
  have hvb : v < (b : ℝ) := by
    rw [hb]
    push_cast
    exact Int.lt_floor_add_one v
  have hvb' : (b : ℝ) ≤ v + 1 := by
    rw [hb]
    push_cast
    have := Int.floor_le v
    linarith
  -- value/conjugate seeds and their a-priori window
  have hbs : v * Real.sqrt 2 < (b : ℝ) * Real.sqrt 2 := by nlinarith
  have hbs' : (b : ℝ) * Real.sqrt 2 ≤ v * Real.sqrt 2 + Real.sqrt 2 := by nlinarith
  have hv2 : v * Real.sqrt 2 = (x - y - Real.sqrt 2) / 2 := by
    rw [hv]
    field_simp
  -- s := a + b√2 ∈ (x, x + 1 + √2]; t := a − b√2 ∈ (y, y + 1 + √2]
  have hslo : x < (a : ℝ) + b * Real.sqrt 2 := by
    have : u + v * Real.sqrt 2 = x - Real.sqrt 2 / 2 + Real.sqrt 2 / 2 := by
      rw [hu, hv2]; ring
    nlinarith
  have hshi : (a : ℝ) + b * Real.sqrt 2 ≤ x + 1 + Real.sqrt 2 := by
    have : u + v * Real.sqrt 2 = x := by rw [hu, hv2]; ring
    nlinarith
  have htlo : y < (a : ℝ) - b * Real.sqrt 2 := by
    have : u - (v * Real.sqrt 2 + Real.sqrt 2) = y := by rw [hu, hv2]; ring
    nlinarith
  have hthi : (a : ℝ) - b * Real.sqrt 2 ≤ y + 1 + Real.sqrt 2 := by
    have : u - v * Real.sqrt 2 = y + Real.sqrt 2 := by rw [hu, hv2]; ring
    nlinarith
  by_cases hc1 : (a : ℝ) - b * Real.sqrt 2 ≤ y + Real.sqrt 2
  · -- candidate (a, b)
    exact ⟨a, b, le_of_lt hslo, by linarith, le_of_lt htlo, by linarith⟩
  by_cases hc2 : (a : ℝ) + b * Real.sqrt 2 ≤ x + 1
  · -- candidate (a, b+1): value up by √2, conjugate down by √2
    rw [not_le] at hc1
    refine ⟨a, b + 1, ?_, ?_, ?_, ?_⟩
    · push_cast
      nlinarith
    · push_cast
      nlinarith
    · push_cast
      nlinarith
    · push_cast
      nlinarith
  · -- candidate (a−1, b): both down by 1
    rw [not_le] at hc1 hc2
    refine ⟨a - 1, b, ?_, ?_, ?_, ?_⟩
    · push_cast
      nlinarith
    · push_cast
      nlinarith
    · push_cast
      nlinarith
    · push_cast
      nlinarith

/-! ### The λ-power families -/

/-- The un-swapped family: `Coverage ((1+√2)·λ^j) (√2·λ^{−j})` for every `j : ℤ`. -/
theorem coverage_family (j : ℤ) :
    OneDimCoverage ((1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ j)
      (Real.sqrt 2 * (1 + Real.sqrt 2) ^ (-j)) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hl : (0 : ℝ) < 1 + Real.sqrt 2 := by linarith
  have hlne : (1 + Real.sqrt 2 : ℝ) ≠ 0 := ne_of_gt hl
  induction j using Int.induction_on with
  | zero => simpa using coverage_base
  | succ i ih =>
    have h := coverage_scale_up ih
    have e1 : (1 + Real.sqrt 2) * ((1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ (i : ℤ))
        = (1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ ((i : ℤ) + 1) := by
      rw [zpow_add₀ hlne, zpow_one]
      ring
    have e2 : Real.sqrt 2 * (1 + Real.sqrt 2) ^ (-(i : ℤ)) / (1 + Real.sqrt 2)
        = Real.sqrt 2 * (1 + Real.sqrt 2) ^ (-((i : ℤ) + 1)) := by
      rw [show -((i : ℤ) + 1) = -(i : ℤ) + (-1) by ring, zpow_add₀ hlne, zpow_neg_one]
      field_simp
    rw [e1, e2] at h
    exact h
  | pred i ih =>
    have h := coverage_scale_down ih
    have e1 : (1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ (-(i : ℤ)) / (1 + Real.sqrt 2)
        = (1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ (-(i : ℤ) - 1) := by
      rw [show -(i : ℤ) - 1 = -(i : ℤ) + (-1) by ring, zpow_add₀ hlne, zpow_neg_one]
      field_simp
    have e2 : (1 + Real.sqrt 2) * (Real.sqrt 2 * (1 + Real.sqrt 2) ^ (-(-(i : ℤ))))
        = Real.sqrt 2 * (1 + Real.sqrt 2) ^ (-(-(i : ℤ) - 1)) := by
      rw [show -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 by ring, zpow_add₀ hlne, zpow_one]
      ring
    rw [e1, e2] at h
    exact h

/-- The swapped family: `Coverage (√2·λ^j) ((1+√2)·λ^{−j})` for every `j : ℤ`. -/
theorem coverage_family_swap (j : ℤ) :
    OneDimCoverage (Real.sqrt 2 * (1 + Real.sqrt 2) ^ j)
      ((1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ (-j)) := by
  have h := coverage_swap (coverage_family (-j))
  rwa [neg_neg] at h

/-! ### The sharp existence (Lemma 4.4, product form) -/

/-- **Ross–Selinger Lemma 4.4 (sharp product form)**: if `δ·Δ ≥ (1+√2)²` then the 1-D grid
problem for `[x, x+δ] × [y, y+Δ]` has a solution — for EVERY position. The asymmetric form the
two-disk bound (paper Lemma 5.23 / eq. (21)) requires. -/
theorem oneDim_grid_exists_product {δ Δ : ℝ} (hδ : 0 < δ)
    (h : (1 + Real.sqrt 2) ^ 2 ≤ δ * Δ) : OneDimCoverage δ Δ := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have hl1 : (1 : ℝ) < 1 + Real.sqrt 2 := by linarith
  have hl : (0 : ℝ) < 1 + Real.sqrt 2 := by linarith
  have hΔ : 0 < Δ := by
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hδ.le hcon]
  -- bracket δ/(1+√2) between consecutive λ-powers
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow (x := δ / (1 + Real.sqrt 2)) (y := 1 + Real.sqrt 2)
    (by positivity) hl1
  obtain ⟨hj1, hj2⟩ := hj
  have hδ1 : (1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ j ≤ δ := by
    rw [le_div_iff₀ hl] at hj1
    linarith [hj1]
  have hδ2 : δ < (1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ (j + 1) := by
    rw [div_lt_iff₀ hl] at hj2
    nlinarith [hj2]
  have hzpos : (0 : ℝ) < (1 + Real.sqrt 2) ^ j := zpow_pos hl j
  have hzpos' : (0 : ℝ) < (1 + Real.sqrt 2) ^ (-j) := zpow_pos hl (-j)
  have hzmul : (1 + Real.sqrt 2) ^ j * (1 + Real.sqrt 2) ^ (-j) = 1 := by
    rw [← zpow_add₀ (ne_of_gt hl)]
    simp
  by_cases hcase : Real.sqrt 2 * (1 + Real.sqrt 2) ^ (-j) ≤ Δ
  · -- the un-swapped family at j dominates
    exact coverage_mono hδ1 hcase (coverage_family j)
  · -- the swapped family at j+1 dominates
    rw [not_le] at hcase
    have hzpos'' : (0 : ℝ) < (1 + Real.sqrt 2) ^ (j + 1) := zpow_pos hl (j + 1)
    have hsucc : (1 + Real.sqrt 2) ^ (j + 1) = (1 + Real.sqrt 2) ^ j * (1 + Real.sqrt 2) := by
      rw [zpow_add₀ (ne_of_gt hl), zpow_one]
    have hsucc' : (1 + Real.sqrt 2) ^ (-(j + 1)) * ((1 + Real.sqrt 2) ^ j * (1 + Real.sqrt 2))
        = 1 := by
      rw [← hsucc, ← zpow_add₀ (ne_of_gt hl)]
      simp
    refine coverage_mono ?_ ?_ (coverage_family_swap (j + 1))
    · -- √2·λ^{j+1} ≤ δ: from δΔ ≥ λ² and Δ < √2λ^{−j}, using λ ≥ 2
      -- δ ≥ λ²/Δ > λ²·λ^j/√2 = λ^{j+2}/√2 ≥ √2·λ^{j+1}  ⟸  λ ≥ 2
      have hkey : (1 + Real.sqrt 2) ^ 2 ≤ δ * (Real.sqrt 2 * (1 + Real.sqrt 2) ^ (-j)) := by
        calc (1 + Real.sqrt 2) ^ 2 ≤ δ * Δ := h
          _ ≤ δ * (Real.sqrt 2 * (1 + Real.sqrt 2) ^ (-j)) := by nlinarith
      -- multiply through by λ^j > 0 and divide by √2
      have h2 : (1 + Real.sqrt 2) ^ 2 * (1 + Real.sqrt 2) ^ j ≤ δ * Real.sqrt 2 := by
        have := mul_le_mul_of_nonneg_right hkey hzpos.le
        calc (1 + Real.sqrt 2) ^ 2 * (1 + Real.sqrt 2) ^ j
            ≤ δ * (Real.sqrt 2 * (1 + Real.sqrt 2) ^ (-j)) * (1 + Real.sqrt 2) ^ j := this
          _ = δ * Real.sqrt 2 * ((1 + Real.sqrt 2) ^ j * (1 + Real.sqrt 2) ^ (-j)) := by ring
          _ = δ * Real.sqrt 2 := by rw [hzmul]; ring
      -- λ² ≥ 2λ (λ ≥ 2), so λ²λ^j ≥ 2λ^{j+1} = √2·√2·λ^{j+1}
      have hlam2 : (2 : ℝ) ≤ 1 + Real.sqrt 2 := by nlinarith
      have h3 : Real.sqrt 2 * (1 + Real.sqrt 2) ^ (j + 1) * Real.sqrt 2
          ≤ δ * Real.sqrt 2 := by
        calc Real.sqrt 2 * (1 + Real.sqrt 2) ^ (j + 1) * Real.sqrt 2
            = 2 * ((1 + Real.sqrt 2) ^ j * (1 + Real.sqrt 2)) := by rw [hsucc]; nlinarith
          _ ≤ (1 + Real.sqrt 2) * ((1 + Real.sqrt 2) ^ j * (1 + Real.sqrt 2)) := by nlinarith
          _ = (1 + Real.sqrt 2) ^ 2 * (1 + Real.sqrt 2) ^ j := by ring
          _ ≤ δ * Real.sqrt 2 := h2
      nlinarith
    · -- (1+√2)·λ^{−(j+1)} ≤ Δ: from Δ > λ^{−j} (forced by δ < (1+√2)λ^{j+1} and δΔ ≥ λ²)
      have hΔlow : (1 + Real.sqrt 2) ^ (-j) ≤ Δ := by
        by_contra hcon
        rw [not_le] at hcon
        have hlt : δ * Δ < ((1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ (j + 1))
            * (1 + Real.sqrt 2) ^ (-j) :=
          mul_lt_mul'' hδ2 hcon hδ.le hΔ.le
        rw [hsucc] at hlt
        have hcollapse : (1 + Real.sqrt 2) * ((1 + Real.sqrt 2) ^ j * (1 + Real.sqrt 2))
            * (1 + Real.sqrt 2) ^ (-j) = (1 + Real.sqrt 2) ^ 2 := by
          calc (1 + Real.sqrt 2) * ((1 + Real.sqrt 2) ^ j * (1 + Real.sqrt 2))
              * (1 + Real.sqrt 2) ^ (-j)
              = (1 + Real.sqrt 2) ^ 2 * ((1 + Real.sqrt 2) ^ j * (1 + Real.sqrt 2) ^ (-j)) := by
                ring
            _ = (1 + Real.sqrt 2) ^ 2 := by rw [hzmul]; ring
        rw [hcollapse] at hlt
        linarith
      calc (1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ (-(j + 1))
          = (1 + Real.sqrt 2) ^ (-j) := by
            rw [show -(j + 1) = -j + (-1) by ring, zpow_add₀ (ne_of_gt hl), zpow_neg_one]
            field_simp
        _ ≤ Δ := hΔlow

/-- **Lemma 4.4 in interval form**: closed intervals `[x₀, x₁]`, `[y₀, y₁]` with
`(x₁−x₀)(y₁−y₀) ≥ (1+√2)²` contain a grid point and its conjugate. -/
theorem oneDim_grid_exists_of_mul_le {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁)
    (h : (1 + Real.sqrt 2) ^ 2 ≤ (x₁ - x₀) * (y₁ - y₀)) :
    ∃ a b : ℤ, x₀ ≤ (a : ℝ) + b * Real.sqrt 2 ∧ (a : ℝ) + b * Real.sqrt 2 ≤ x₁ ∧
      y₀ ≤ (a : ℝ) - b * Real.sqrt 2 ∧ (a : ℝ) - b * Real.sqrt 2 ≤ y₁ := by
  obtain ⟨a, b, h1, h2, h3, h4⟩ :=
    oneDim_grid_exists_product (by linarith) h x₀ y₀
  exact ⟨a, b, h1, by linarith, h3, by linarith⟩

end SKEFTHawking.RossSelinger.GridProblem
