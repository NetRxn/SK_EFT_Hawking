/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item H — Ross-Selinger grid-problem FINDER completeness (existence core)

The last analytic input for orphan #2: the guarantee that for any target and precision ε, the
grid search region CONTAINS a `ℤ[ω]` solution (so the verified synthesis back-end — `gridFindT`
→ `gridSynthWord`, KMMCompleteness/GridSolver — can convert it to an exact Clifford+T word).

Grounded in Ross, *Algebraic and Logical Methods in Quantum Computation* (PhD thesis, Dalhousie
2015, arXiv:1510.02198), Chapter 5 ("Grid problems"). DR-verified (Lit-Search/Phase-6x). The DR
made three load-bearing corrections to the earlier dossier: the skew-reduction factor is `9/10`
(not √2; thesis Lemma 5.2.19), the z-rotation T-count slope is `3` typical / `4` simple (not 12;
the 12 is arbitrary-SU(2) = 3 z-rotations), and grid operators have entries in `½·ℤ[√2]` (thesis
Lemma 5.2.12), not `SL(2,ℤ[√2])`.

## The existence keystone (this file)

`oneDim_grid_exists` — the **1-D grid existence** (balanced form of thesis Lemma 5.2.7): if both
the value-interval and the Galois-conjugate-interval have half-width ≥ `(1+√2)/2`, a point
`m + n√2 ∈ ℤ[√2]` lands in the value-interval with its conjugate `m − n√2` in the
conjugate-interval. Proof: **center-rounding** — round the `(1, √2)`-coordinates of the box centre
to the nearest integers; the rounding error in each coordinate is `≤ 1/2`, propagating to a
combined error `≤ (1+√2)/2` in both `m ± n√2`.

This is the constant-independent existence core. The full thesis enumeration (the Step-operator
uprightness machinery, Lemma 5.2.19 / Prop 5.2.20) is needed only for *efficient enumeration*
(Item H's `O(log(1/M))` bound), NOT for *existence*: the scaled two-disk bound (thesis Lemma
5.2.38) inflates both regions by `√2^k` so that at `k = Θ(log(1/ε))` each region's width clears
`1+√2`, and the simple center-rounding above produces the solution. The 2-D `ℤ[ω]` problem splits
into two independent 1-D `ℤ[√2]` problems via `ℤ[ω] = ℤ[√2][i]` (`i = ω²`; thesis Prop 5.2.9),
real and imaginary parts — so this 1-D existence composes directly to the 2-D FINDER existence.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new axioms): respected.

-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Round

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger.GridProblem

open scoped Real

/-- **1-D grid existence** (balanced center-rounding form of Ross thesis Lemma 5.2.7). For real
interval centres `cA, cB` and widths `δ, Δ ≥ 1+√2`, there is a `ℤ[√2]` element `m + n√2` within
`δ/2` of `cA` whose Galois conjugate `m − n√2` is within `Δ/2` of `cB`.

`m := round((cA+cB)/2)`, `n := round((cA−cB)/(2√2))`. Then `m ± n√2 − c_{A/B}` is the rounding
error `(m − (cA+cB)/2) ± √2·(n − (cA−cB)/(2√2))`, bounded by `1/2 + √2·(1/2) = (1+√2)/2`. -/
theorem oneDim_grid_exists (cA cB δ Δ : ℝ) (hδ : 1 + Real.sqrt 2 ≤ δ) (hΔ : 1 + Real.sqrt 2 ≤ Δ) :
    ∃ m n : ℤ, |(m : ℝ) + n * Real.sqrt 2 - cA| ≤ δ / 2 ∧
      |(m : ℝ) - n * Real.sqrt 2 - cB| ≤ Δ / 2 := by
  have s2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  set M := round ((cA + cB) / 2) with hM
  set N := round ((cA - cB) / (2 * Real.sqrt 2)) with hN
  have hm : |(M : ℝ) - (cA + cB) / 2| ≤ 1 / 2 := by rw [abs_sub_comm]; exact abs_sub_round _
  have hn : |(N : ℝ) - (cA - cB) / (2 * Real.sqrt 2)| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round _
  refine ⟨M, N, ?_, ?_⟩
  · have key : (M : ℝ) + N * Real.sqrt 2 - cA
        = ((M : ℝ) - (cA + cB) / 2) + Real.sqrt 2 * ((N : ℝ) - (cA - cB) / (2 * Real.sqrt 2)) := by
      field_simp; ring
    rw [key]
    calc |((M : ℝ) - (cA + cB) / 2) + Real.sqrt 2 * ((N : ℝ) - (cA - cB) / (2 * Real.sqrt 2))|
        ≤ |(M : ℝ) - (cA + cB) / 2|
          + |Real.sqrt 2 * ((N : ℝ) - (cA - cB) / (2 * Real.sqrt 2))| := abs_add_le _ _
      _ ≤ 1 / 2 + Real.sqrt 2 * (1 / 2) := by rw [abs_mul, abs_of_nonneg s2]; gcongr
      _ = (1 + Real.sqrt 2) / 2 := by ring
      _ ≤ δ / 2 := by linarith
  · have key : (M : ℝ) - N * Real.sqrt 2 - cB
        = ((M : ℝ) - (cA + cB) / 2) - Real.sqrt 2 * ((N : ℝ) - (cA - cB) / (2 * Real.sqrt 2)) := by
      field_simp; ring
    rw [key]
    calc |((M : ℝ) - (cA + cB) / 2) - Real.sqrt 2 * ((N : ℝ) - (cA - cB) / (2 * Real.sqrt 2))|
        ≤ |(M : ℝ) - (cA + cB) / 2|
          + |Real.sqrt 2 * ((N : ℝ) - (cA - cB) / (2 * Real.sqrt 2))| := abs_sub _ _
      _ ≤ 1 / 2 + Real.sqrt 2 * (1 / 2) := by rw [abs_mul, abs_of_nonneg s2]; gcongr
      _ = (1 + Real.sqrt 2) / 2 := by ring
      _ ≤ Δ / 2 := by linarith

/-- **2-D grid existence** (`ℤ[ω] = ℤ[√2][i]` decomposition, thesis Prop 5.2.9): the real and
imaginary `ℤ[√2]` components solve independent 1-D grid problems. For target centres
`(cAr, cAi)` (value) and `(cBr, cBi)` (Galois conjugate) with all four widths `≥ 1+√2`, there
exist `ℤ[√2]` components `p = pm + pn√2` (real part) and `q = qm + qn√2` (imag part) with
`p, q` near `(cAr, cAi)` and `σp, σq` near `(cBr, cBi)`. This is the `ℤ[ω]` existence the FINDER
needs (the column numerator `u = p + qi ∈ ℤ[ω]`). -/
theorem twoDim_grid_exists (cAr cAi cBr cBi δr δi Δr Δi : ℝ)
    (hδr : 1 + Real.sqrt 2 ≤ δr) (hδi : 1 + Real.sqrt 2 ≤ δi)
    (hΔr : 1 + Real.sqrt 2 ≤ Δr) (hΔi : 1 + Real.sqrt 2 ≤ Δi) :
    ∃ pm pn qm qn : ℤ,
      |(pm : ℝ) + pn * Real.sqrt 2 - cAr| ≤ δr / 2 ∧
      |(pm : ℝ) - pn * Real.sqrt 2 - cBr| ≤ Δr / 2 ∧
      |(qm : ℝ) + qn * Real.sqrt 2 - cAi| ≤ δi / 2 ∧
      |(qm : ℝ) - qn * Real.sqrt 2 - cBi| ≤ Δi / 2 := by
  obtain ⟨pm, pn, hp1, hp2⟩ := oneDim_grid_exists cAr cBr δr Δr hδr hΔr
  obtain ⟨qm, qn, hq1, hq2⟩ := oneDim_grid_exists cAi cBi δi Δi hδi hΔi
  exact ⟨pm, pn, qm, qn, hp1, hp2, hq1, hq2⟩

/-- **Scaled column existence** (the FINDER existence at the value level; thesis Lemma 5.2.38
applied to the ε-region × disk). For ANY complex target column `(tr, ti)` and precision `ε > 0`,
at some denominator exponent `k = Θ(log(1/ε))` there is a `ℤ[ω]` column numerator `u = p + qi`
(real component `p = pm + pn√2`, imaginary `q = qm + qn√2`) whose cleared value `u/√2^k` is within
`ε` of the target, AND whose Galois conjugate `u•/√2^k` lies in the unit box `[−1,1]²` (⊂ the unit
disk, so `|u•| ≤ √2·√2^k` — the §6 total-positivity / disk membership that makes the residual `t`
admissible). Proof: choose `k` with `√2^k ≥ max((1+√2)/ε, 1+√2)` so both the (scaled) ε-region
half-width `ε√2^k` and the disk half-width `√2^k` clear `1+√2`, then apply `twoDim_grid_exists`.
The Step-operator/uprightness machinery is NOT needed for this existence — scaling suffices. -/
theorem scaledColumn_exists (tr ti ε : ℝ) (hε : 0 < ε) :
    ∃ (k : ℕ) (pm pn qm qn : ℤ),
      |((pm : ℝ) + pn * Real.sqrt 2) / Real.sqrt 2 ^ k - tr| ≤ ε ∧
      |((qm : ℝ) + qn * Real.sqrt 2) / Real.sqrt 2 ^ k - ti| ≤ ε ∧
      |((pm : ℝ) - pn * Real.sqrt 2) / Real.sqrt 2 ^ k| ≤ 1 ∧
      |((qm : ℝ) - qn * Real.sqrt 2) / Real.sqrt 2 ^ k| ≤ 1 := by
  have h1lt : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set C := max ((1 + Real.sqrt 2) / ε) (1 + Real.sqrt 2) with hC
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C h1lt
  set s := Real.sqrt 2 ^ k with hs
  have hspos : 0 < s := by positivity
  have hsC : C ≤ s := le_of_lt hk
  have hsge : 1 + Real.sqrt 2 ≤ s := le_trans (le_max_right _ _) hsC
  have hεs : 1 + Real.sqrt 2 ≤ ε * s := by
    have h := le_trans (le_max_left _ _) hsC
    rw [div_le_iff₀ hε] at h; linarith
  have hes_nn : (0 : ℝ) ≤ ε * s := by positivity
  obtain ⟨pm, pn, qm, qn, hp1, hp2, hq1, hq2⟩ :=
    twoDim_grid_exists (s * tr) (s * ti) 0 0 (ε * s) (ε * s) s s hεs hεs hsge hsge
  refine ⟨k, pm, pn, qm, qn, ?_, ?_, ?_, ?_⟩
  · rw [show ((pm : ℝ) + pn * Real.sqrt 2) / s - tr
          = ((pm + pn * Real.sqrt 2) - tr * s) / s from by field_simp,
        abs_div, abs_of_pos hspos, div_le_iff₀ hspos, mul_comm tr s]
    calc |(pm : ℝ) + pn * Real.sqrt 2 - s * tr| ≤ ε * s / 2 := hp1
      _ ≤ ε * s := by linarith
  · rw [show ((qm : ℝ) + qn * Real.sqrt 2) / s - ti
          = ((qm + qn * Real.sqrt 2) - ti * s) / s from by field_simp,
        abs_div, abs_of_pos hspos, div_le_iff₀ hspos, mul_comm ti s]
    calc |(qm : ℝ) + qn * Real.sqrt 2 - s * ti| ≤ ε * s / 2 := hq1
      _ ≤ ε * s := by linarith
  · rw [abs_div, abs_of_pos hspos, div_le_iff₀ hspos, one_mul]
    have := hp2; rw [sub_zero] at this; linarith
  · rw [abs_div, abs_of_pos hspos, div_le_iff₀ hspos, one_mul]
    have := hq2; rw [sub_zero] at this; linarith

end SKEFTHawking.RossSelinger.GridProblem
