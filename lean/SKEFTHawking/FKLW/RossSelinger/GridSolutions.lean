/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item H — the Ross-Selinger grid SOLVER (constructive)

`GridProblem.lean` shipped the grid-problem *existence* (`oneDim_grid_exists`,
`twoDim_grid_exists`, `scaledColumn_exists`) via center-rounding. This file turns that
existence into a runnable **solver**: the explicit center-rounding witness exposed as a
function (`oneDimGridSolution`, `twoDimGridSolution`) with its correctness bound. These are
the Ross-Selinger §5 grid solutions for the upright case (the constant-size center-rounding
neighbourhood; the Step-operator `O(log(1/M))` enumeration is the efficiency refinement, not
needed for the runnable optimal-length compile). Composes with `gridFindT` (residual `t`) and
`assembleUnitary` → `kmmReduce` (the soundness backbone, `compile_correct_core`) for the
target-level `compile`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.GridProblem

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger.GridProblem

open scoped Real

/-- **The constructive 1-D grid solution** (center-rounding witness of Ross thesis Lemma 5.2.7).
For interval centres `cA` (value) and `cB` (Galois conjugate), the `ℤ[√2]` element
`m + n√2 = oneDimGridSolution cA cB` rounds the `(1, √2)`-coordinates of the box centre:
`m = ⌊(cA+cB)/2⌉`, `n = ⌊(cA−cB)/(2√2)⌉`. The runnable counterpart of `oneDim_grid_exists`. -/
noncomputable def oneDimGridSolution (cA cB : ℝ) : ℤ × ℤ :=
  (round ((cA + cB) / 2), round ((cA - cB) / (2 * Real.sqrt 2)))

/-- **Correctness of the 1-D grid solver**: when both half-widths clear `(1+√2)/2`
(i.e. `δ, Δ ≥ 1+√2`), the rounded `m + n√2` is within `δ/2` of `cA` and its conjugate
`m − n√2` within `Δ/2` of `cB`. (Each coordinate rounding error is `≤ 1/2`; the combined error
in `m ± n√2` is `≤ (1+√2)/2`.) -/
theorem oneDimGridSolution_spec (cA cB δ Δ : ℝ)
    (hδ : 1 + Real.sqrt 2 ≤ δ) (hΔ : 1 + Real.sqrt 2 ≤ Δ) :
    |((oneDimGridSolution cA cB).1 : ℝ) + (oneDimGridSolution cA cB).2 * Real.sqrt 2 - cA|
        ≤ δ / 2 ∧
      |((oneDimGridSolution cA cB).1 : ℝ) - (oneDimGridSolution cA cB).2 * Real.sqrt 2 - cB|
        ≤ Δ / 2 := by
  have s2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  simp only [oneDimGridSolution]
  set M := round ((cA + cB) / 2) with hM
  set N := round ((cA - cB) / (2 * Real.sqrt 2)) with hN
  have hm : |(M : ℝ) - (cA + cB) / 2| ≤ 1 / 2 := by rw [abs_sub_comm]; exact abs_sub_round _
  have hn : |(N : ℝ) - (cA - cB) / (2 * Real.sqrt 2)| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round _
  refine ⟨?_, ?_⟩
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

/-- **The constructive 2-D grid solution** (`ℤ[ω] = ℤ[√2][i]` split, Ross thesis Prop 5.2.9):
solve the real-part 1-D problem `(cAr, cBr)` and the imaginary-part 1-D problem `(cAi, cBi)`
independently. Returns `(pm, pn, qm, qn)` — the real `ℤ[√2]` component `pm + pn√2` and the
imaginary component `qm + qn√2` of the `ℤ[ω]` column numerator `u = p + q·i`. -/
noncomputable def twoDimGridSolution (cAr cAi cBr cBi : ℝ) : ℤ × ℤ × ℤ × ℤ :=
  let p := oneDimGridSolution cAr cBr
  let q := oneDimGridSolution cAi cBi
  (p.1, p.2, q.1, q.2)

/-- **Correctness of the 2-D grid solver**: the real and imaginary `ℤ[√2]` components each solve
their 1-D grid problem (value within `δ/2` of the target centre, conjugate within `Δ/2`). -/
theorem twoDimGridSolution_spec (cAr cAi cBr cBi δr δi Δr Δi : ℝ)
    (hδr : 1 + Real.sqrt 2 ≤ δr) (hδi : 1 + Real.sqrt 2 ≤ δi)
    (hΔr : 1 + Real.sqrt 2 ≤ Δr) (hΔi : 1 + Real.sqrt 2 ≤ Δi) :
    let s := twoDimGridSolution cAr cAi cBr cBi
    |(s.1 : ℝ) + s.2.1 * Real.sqrt 2 - cAr| ≤ δr / 2 ∧
      |(s.1 : ℝ) - s.2.1 * Real.sqrt 2 - cBr| ≤ Δr / 2 ∧
      |(s.2.2.1 : ℝ) + s.2.2.2 * Real.sqrt 2 - cAi| ≤ δi / 2 ∧
      |(s.2.2.1 : ℝ) - s.2.2.2 * Real.sqrt 2 - cBi| ≤ Δi / 2 := by
  obtain ⟨hp1, hp2⟩ := oneDimGridSolution_spec cAr cBr δr Δr hδr hΔr
  obtain ⟨hq1, hq2⟩ := oneDimGridSolution_spec cAi cBi δi Δi hδi hΔi
  exact ⟨hp1, hp2, hq1, hq2⟩

end SKEFTHawking.RossSelinger.GridProblem
