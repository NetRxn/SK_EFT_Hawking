/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — σ_y-block sum linftyOp norm bound

The triangle bound on a Finset sum of scalar-multiplied σ_y-blocks:

  `‖∑ p ∈ s, (γ p : ℂ) • sigmaYBlock (a p) (b p)‖_linftyOp ≤ ∑ p ∈ s, |γ p|`

(using `‖sigmaYBlock i j‖ ≤ 1` from Session 10 + triangle inequality +
`norm_smul`). This is the substrate for bounding `‖F_inner‖` (the inner
diagonal-case witness in Session 24/37), which is the remaining gap for
the super-quad bound's F/G-norm ingredient.

For the symmetric F=αG construction, `F_inner = ∑_p γ_p · σ_y(p)` with
`γ_p² = θ·b_p/2`, so `‖F_inner‖ ≤ ∑_p |γ_p|`. Combined with the spectral
partial-sum bound on `b_p`, gives `‖F_inner‖ ≤ K_inner(n) · √(θ/2)`.

## Substantive content shipped

  * `sigmaYBlock_sum_linftyOpNorm_le` — `‖∑ p ∈ s, γ p • σ_y(a p)(b p)‖ ≤ ∑ |γ p|`
  * `sigmaXBlock_sum_linftyOpNorm_le` — mirror for σ_x

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — F_inner norm bound substrate.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **σ_y-block sum linftyOp norm bound** via triangle inequality + per-block
norm ≤ 1.

For any Finset `s`, real coefficients `γ`, and index maps `a, b` with
`a p ≠ b p` for each `p ∈ s`:
  `‖∑ p ∈ s, (γ p : ℂ) • sigmaYBlock (a p) (b p)‖ ≤ ∑ p ∈ s, |γ p|`. -/
theorem sigmaYBlock_sum_linftyOpNorm_le {d : ℕ} {ι : Type*}
    (s : Finset ι) (γ : ι → ℝ) (a b : ι → Fin d)
    (h_ne : ∀ p ∈ s, a p ≠ b p) :
    ‖∑ p ∈ s, ((γ p : ℂ)) • sigmaYBlock (a p) (b p)‖ ≤ ∑ p ∈ s, |γ p| := by
  calc ‖∑ p ∈ s, ((γ p : ℂ)) • sigmaYBlock (a p) (b p)‖
      ≤ ∑ p ∈ s, ‖((γ p : ℂ)) • sigmaYBlock (a p) (b p)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ s, |γ p| := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        calc |γ p| * ‖sigmaYBlock (a p) (b p)‖
            ≤ |γ p| * 1 :=
              mul_le_mul_of_nonneg_left (sigmaYBlock_linftyOpNorm_le_one (h_ne p hp))
                (abs_nonneg _)
          _ = |γ p| := mul_one _

/-- **σ_x-block sum linftyOp norm bound** (mirror of σ_y). -/
theorem sigmaXBlock_sum_linftyOpNorm_le {d : ℕ} {ι : Type*}
    (s : Finset ι) (γ : ι → ℝ) (a b : ι → Fin d)
    (h_ne : ∀ p ∈ s, a p ≠ b p) :
    ‖∑ p ∈ s, ((γ p : ℂ)) • sigmaXBlock (a p) (b p)‖ ≤ ∑ p ∈ s, |γ p| := by
  calc ‖∑ p ∈ s, ((γ p : ℂ)) • sigmaXBlock (a p) (b p)‖
      ≤ ∑ p ∈ s, ‖((γ p : ℂ)) • sigmaXBlock (a p) (b p)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ s, |γ p| := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        calc |γ p| * ‖sigmaXBlock (a p) (b p)‖
            ≤ |γ p| * 1 :=
              mul_le_mul_of_nonneg_left (sigmaXBlock_linftyOpNorm_le_one (h_ne p hp))
                (abs_nonneg _)
          _ = |γ p| := mul_one _

end SKEFTHawking.FKLW.GenericSUd
