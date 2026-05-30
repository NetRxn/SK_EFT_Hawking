/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item H — the Ross-Selinger 2D grid SOLVER (combinatorial enumeration)

`GridProblem.lean` shipped the grid-problem *existence* (`scaledColumn_exists`, center-rounding);
`GridSolutions.lean` exposed the single center-rounding *witness* as a runnable function. This file
ships the **enumeration** of ALL grid solutions in the upright case — Ross-Selinger 2014 §5 Thm 2
for an axis-aligned (value-interval × Galois-conjugate-interval) region:

  given `[lo, hi]` (for the value `m + n√2`) and `[lo', hi']` (for its Galois conjugate `m − n√2`),
  `gridSolutions1D lo hi lo' hi'` is the FINITE set of all `(m, n) ∈ ℤ²` with
  `lo ≤ m + n√2 ≤ hi` and `lo' ≤ m − n√2 ≤ hi'`.

The enumeration is the standard upright-rectangle scan: the sum of the two value-bounds bounds `2m`
(so `m` ranges over a finite interval `⌈(lo+lo')/2⌉ … ⌊(hi+hi')/2⌋`), and for each `m` the two
constraints bound `n√2` (so `n` ranges over `⌈max …⌉ … ⌊min …⌋`). `gridSolutions1D_mem_iff` is the
combined **correctness + completeness**: membership is *exactly equivalent* to the four real bounds
(soundness = →, completeness = ←). `gridSolutions1D_card_le` bounds the solution count by the box
side-lengths (Thm 2's `O(width · width')` count). This is the deterministic-branch grid solver;
the Step-operator `O(log(1/M))` per-solution refinement is the efficiency layer, not needed for the
runnable optimal-length compile (Item I already ships via the single witness).

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.GridProblem

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger.GridProblem

open scoped Real

/-- Lower bound on the integer `m` (the `1`-coordinate of `m + n√2`): `m ≥ ⌈(lo+lo')/2⌉`, forced by
`lo ≤ m+n√2` and `lo' ≤ m−n√2` (their sum gives `lo+lo' ≤ 2m`). -/
noncomputable def gridMLo (lo lo' : ℝ) : ℤ := ⌈(lo + lo') / 2⌉
/-- Upper bound on `m`: `m ≤ ⌊(hi+hi')/2⌋` (from `m+n√2 ≤ hi`, `m−n√2 ≤ hi'`). -/
noncomputable def gridMHi (hi hi' : ℝ) : ℤ := ⌊(hi + hi') / 2⌋
/-- Lower bound on `n` for a fixed `m`: `n ≥ ⌈max((lo−m)/√2, (m−hi')/√2)⌉`. -/
noncomputable def gridNLo (lo hi' : ℝ) (m : ℤ) : ℤ :=
  ⌈max ((lo - m) / Real.sqrt 2) ((m - hi') / Real.sqrt 2)⌉
/-- Upper bound on `n` for a fixed `m`: `n ≤ ⌊min((hi−m)/√2, (m−lo')/√2)⌋`. -/
noncomputable def gridNHi (hi lo' : ℝ) (m : ℤ) : ℤ :=
  ⌊min ((hi - m) / Real.sqrt 2) ((m - lo') / Real.sqrt 2)⌋

/-- **The Ross-Selinger upright 2-D grid solver** (enumeration form): the finite set of all
`(m, n) ∈ ℤ²` whose `ℤ[√2]` value `m + n√2 ∈ [lo, hi]` and Galois conjugate `m − n√2 ∈ [lo', hi']`.
Scans `m ∈ [⌈(lo+lo')/2⌉, ⌊(hi+hi')/2⌋]`, and per `m`, `n ∈ [gridNLo m, gridNHi m]`. -/
noncomputable def gridSolutions1D (lo hi lo' hi' : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (gridMLo lo lo') (gridMHi hi hi')).biUnion fun m =>
    (Finset.Icc (gridNLo lo hi' m) (gridNHi hi lo' m)).image fun n => (m, n)

/-- **Correctness + completeness of the upright grid solver.** `(m, n)` is enumerated by
`gridSolutions1D` **iff** the `ℤ[√2]` element `m + n√2` lies in `[lo, hi]` and its Galois conjugate
`m − n√2` lies in `[lo', hi']`. (→ soundness: every enumerated pair solves the grid problem;
← completeness: every grid solution is enumerated.) -/
theorem gridSolutions1D_mem_iff (lo hi lo' hi' : ℝ) (m n : ℤ) :
    (m, n) ∈ gridSolutions1D lo hi lo' hi' ↔
      (lo ≤ (m : ℝ) + n * Real.sqrt 2 ∧ (m : ℝ) + n * Real.sqrt 2 ≤ hi ∧
        lo' ≤ (m : ℝ) - n * Real.sqrt 2 ∧ (m : ℝ) - n * Real.sqrt 2 ≤ hi') := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  -- the four per-coordinate bridges (value/conjugate ↔ scaled-n inequalities)
  have hA : (lo - m) / Real.sqrt 2 ≤ (n : ℝ) ↔ lo ≤ (m : ℝ) + n * Real.sqrt 2 := by
    rw [div_le_iff₀ h2]; constructor <;> intro h <;> nlinarith [h]
  have hB : (m - hi') / Real.sqrt 2 ≤ (n : ℝ) ↔ (m : ℝ) - n * Real.sqrt 2 ≤ hi' := by
    rw [div_le_iff₀ h2]; constructor <;> intro h <;> nlinarith [h]
  have hC : (n : ℝ) ≤ (hi - m) / Real.sqrt 2 ↔ (m : ℝ) + n * Real.sqrt 2 ≤ hi := by
    rw [le_div_iff₀ h2]; constructor <;> intro h <;> nlinarith [h]
  have hD : (n : ℝ) ≤ (m - lo') / Real.sqrt 2 ↔ lo' ≤ (m : ℝ) - n * Real.sqrt 2 := by
    rw [le_div_iff₀ h2]; constructor <;> intro h <;> nlinarith [h]
  -- the n-range membership is exactly the four bounds
  have hn : (gridNLo lo hi' m ≤ n ∧ n ≤ gridNHi hi lo' m) ↔
      (lo ≤ (m : ℝ) + n * Real.sqrt 2 ∧ (m : ℝ) + n * Real.sqrt 2 ≤ hi ∧
        lo' ≤ (m : ℝ) - n * Real.sqrt 2 ∧ (m : ℝ) - n * Real.sqrt 2 ≤ hi') := by
    rw [gridNLo, gridNHi, Int.ceil_le, Int.le_floor, max_le_iff, le_min_iff, hA, hB, hC, hD]
    tauto
  -- the m-range is implied by the four bounds (needed for completeness; free for soundness)
  have hmlo : gridMLo lo lo' ≤ m ↔ lo + lo' ≤ 2 * (m : ℝ) := by
    rw [gridMLo, Int.ceil_le, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]; constructor <;> intro h <;> linarith
  have hmhi : m ≤ gridMHi hi hi' ↔ 2 * (m : ℝ) ≤ hi + hi' := by
    rw [gridMHi, Int.le_floor, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]; constructor <;> intro h <;> linarith
  rw [gridSolutions1D, Finset.mem_biUnion]
  constructor
  · rintro ⟨m', hm', hmem⟩
    rw [Finset.mem_image] at hmem
    obtain ⟨n', hn', heq⟩ := hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
    rw [Finset.mem_Icc] at hn'
    exact hn.mp hn'
  · intro hbounds
    refine ⟨m, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      refine ⟨hmlo.mpr ?_, hmhi.mpr ?_⟩
      · nlinarith [hbounds.1, hbounds.2.2.1, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), h2]
      · nlinarith [hbounds.2.1, hbounds.2.2.2, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), h2]
    · rw [Finset.mem_image]
      exact ⟨n, Finset.mem_Icc.mpr (hn.mpr hbounds), rfl⟩

/-- **Count bound** (Ross-Selinger §5 Thm 2, upright case): the number of grid solutions is at most
`(⌊(hi+hi')/2⌋ − ⌈(lo+lo')/2⌉ + 1)` (the `m`-range size) times the largest per-`m` `n`-range size.
Each enumerated `m` contributes `≤ (gridNHi − gridNLo + 1)` solutions; bounding the `m`-range gives a
finite `O(width · width')` count. Here stated as the clean cardinality-of-`biUnion` bound. -/
theorem gridSolutions1D_card_le (lo hi lo' hi' : ℝ) :
    (gridSolutions1D lo hi lo' hi').card ≤
      ∑ m ∈ Finset.Icc (gridMLo lo lo') (gridMHi hi hi'),
        (Finset.Icc (gridNLo lo hi' m) (gridNHi hi lo' m)).card := by
  refine le_trans (Finset.card_biUnion_le) ?_
  apply Finset.sum_le_sum
  intro m _
  exact Finset.card_image_le

/-- **The Ross-Selinger 2-D `ℤ[ω]` grid solver** (`ℤ[ω] = ℤ[√2][i]` split, Ross thesis Prop 5.2.9):
the finite set of `ℤ[ω]` column numerators `u = (pm + pn√2) + (qm + qn√2)·i` (encoded
`((pm,pn),(qm,qn))`) whose real `ℤ[√2]` component solves the real grid problem
`[loR,hiR]×[loR',hiR']` and whose imaginary component solves the imaginary grid problem
`[loI,hiI]×[loI',hiI']`. The product of two independent 1-D upright enumerations. -/
noncomputable def gridSolutions2D (loR hiR loR' hiR' loI hiI loI' hiI' : ℝ) :
    Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  gridSolutions1D loR hiR loR' hiR' ×ˢ gridSolutions1D loI hiI loI' hiI'

/-- **Correctness + completeness of the 2-D grid solver**: `((pm,pn),(qm,qn))` is enumerated **iff**
both the real component `pm + pn√2` and the imaginary component `qm + qn√2` solve their respective
1-D grid problems (value and Galois conjugate each in the prescribed interval). Conjunction of the
two `gridSolutions1D_mem_iff`. -/
theorem gridSolutions2D_mem_iff (loR hiR loR' hiR' loI hiI loI' hiI' : ℝ) (p q : ℤ × ℤ) :
    (p, q) ∈ gridSolutions2D loR hiR loR' hiR' loI hiI loI' hiI' ↔
      (loR ≤ (p.1 : ℝ) + p.2 * Real.sqrt 2 ∧ (p.1 : ℝ) + p.2 * Real.sqrt 2 ≤ hiR ∧
        loR' ≤ (p.1 : ℝ) - p.2 * Real.sqrt 2 ∧ (p.1 : ℝ) - p.2 * Real.sqrt 2 ≤ hiR') ∧
      (loI ≤ (q.1 : ℝ) + q.2 * Real.sqrt 2 ∧ (q.1 : ℝ) + q.2 * Real.sqrt 2 ≤ hiI ∧
        loI' ≤ (q.1 : ℝ) - q.2 * Real.sqrt 2 ∧ (q.1 : ℝ) - q.2 * Real.sqrt 2 ≤ hiI') := by
  rw [gridSolutions2D, Finset.mem_product, gridSolutions1D_mem_iff, gridSolutions1D_mem_iff]

/-- **2-D count**: the number of `ℤ[ω]` grid solutions is the product of the two 1-D solution
counts (`Finset.card_product`). -/
theorem gridSolutions2D_card (loR hiR loR' hiR' loI hiI loI' hiI' : ℝ) :
    (gridSolutions2D loR hiR loR' hiR' loI hiI loI' hiI').card =
      (gridSolutions1D loR hiR loR' hiR').card * (gridSolutions1D loI hiI loI' hiI').card := by
  rw [gridSolutions2D, Finset.card_product]

end SKEFTHawking.RossSelinger.GridProblem
