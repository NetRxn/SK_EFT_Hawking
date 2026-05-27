/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2f-substrate — `|tr Y| ≤ d * ‖Y‖` for matrix Y

A small substrate lemma needed for the Phase 6y traceless conclusion
(S.2g): for `Y : Matrix (Fin d) (Fin d) ℂ` with the linftyOp norm,
`|tr Y| ≤ d * ‖Y‖`. Combined with `exp(tr Y) = 1` and `Y` near 0, this
gives `tr Y = 0` (via small-norm injectivity of `Complex.exp` near 0).

## Mathematical content

For Y : Matrix (Fin d) (Fin d) ℂ:
- `|Y i i| ≤ ∑_j ‖Y i j‖ ≤ ‖Y‖` (per row, linftyOp norm).
- `|tr Y| = |∑_i Y i i| ≤ ∑_i |Y i i| ≤ d · ‖Y‖`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2g substrate (trace bound).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Diagonal entry bound: `‖Y i i‖ ≤ ‖Y‖` for linftyOp norm -/

/-- **Diagonal entry bound (linftyOp)**: `‖Y i i‖ ≤ ‖Y‖`.

The linftyOp matrix norm dominates each entry: each entry is bounded
by its row-sum, which is bounded by the sup over rows of row-sums. -/
theorem norm_apply_diag_le_linftyOpNorm {d : ℕ} [Nonempty (Fin d)]
    (Y : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    ‖Y i i‖ ≤ ‖Y‖ := by
  rw [Matrix.linfty_opNorm_def]
  -- Goal: ‖Y i i‖ ≤ ↑(Finset.univ.sup (fun i => ∑ j, ‖Y i j‖₊))
  have h1 : ‖Y i i‖₊ ≤ ∑ j, ‖Y i j‖₊ := by
    apply Finset.single_le_sum (f := fun j => ‖Y i j‖₊)
    · intro j _; exact zero_le _
    · exact Finset.mem_univ i
  have h2 : (∑ j, ‖Y i j‖₊) ≤ Finset.univ.sup (fun i => ∑ j, ‖Y i j‖₊) :=
    Finset.le_sup (f := fun i => ∑ j, ‖Y i j‖₊) (Finset.mem_univ i)
  have h3 : ‖Y i i‖₊ ≤ Finset.univ.sup (fun i => ∑ j, ‖Y i j‖₊) := le_trans h1 h2
  exact_mod_cast h3

/-! ## 2. Trace norm bound: `‖tr Y‖ ≤ d * ‖Y‖` -/

/-- **Trace norm bound**: for `Y : Matrix (Fin d) (Fin d) ℂ`,
`‖tr Y‖ ≤ d * ‖Y‖` in the linftyOp norm. -/
theorem norm_trace_le_dim_mul_norm {d : ℕ} [Nonempty (Fin d)]
    (Y : Matrix (Fin d) (Fin d) ℂ) :
    ‖Y.trace‖ ≤ d * ‖Y‖ := by
  -- tr Y = ∑ Y i i (via Matrix.trace definition).
  have h_trace_eq : Y.trace = ∑ i, Y i i := by
    show Matrix.trace Y = ∑ i, Y i i
    rfl
  rw [h_trace_eq]
  -- Apply triangle inequality for sum of norms.
  calc ‖∑ i, Y i i‖
      ≤ ∑ i, ‖Y i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i, ‖Y‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact norm_apply_diag_le_linftyOpNorm Y i
    _ = d * ‖Y‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end SKEFTHawking.FKLW.GenericSUd
