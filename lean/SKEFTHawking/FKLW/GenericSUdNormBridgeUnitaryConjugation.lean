/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Norm bridge for unitary conjugation (loose d² bound)

For unitary `U : Matrix.unitaryGroup (Fin n) ℂ` and any matrix
`A : Matrix (Fin n) (Fin n) ℂ`:

  `‖U · A · star U‖_linftyOp ≤ n² · ‖A‖_linftyOp`

via `Matrix.linfty_opNorm_mul` (submultiplicativity) + the entry bound
`entry_norm_bound_of_unitary` (each entry of a unitary has norm ≤ 1).

This is the **loose norm bridge** for the symmetric F=αG conjugation:
combined with Session 26's U(d) commutator invariance, gives a `n²`-loose
bound on `‖F‖_linftyOp` after conjugation (e.g., for F = U · F' · U* with
‖F'‖ ≤ √(θ/2), we get ‖F‖ ≤ n² · √(θ/2)).

The tighter `n` bound (via Cauchy-Schwarz on rows: ‖U‖_linftyOp ≤ √n)
ships in a follow-on commit; this module ships the simpler loose form.

## Substantive content shipped

  * `linftyOpNorm_unitary_le` — `‖U‖_linftyOp ≤ n` for U unitary
  * `linftyOpNorm_unitary_conj_bound` — `‖U · A · star U‖_linftyOp ≤ n² · ‖A‖_linftyOp`

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" — norm bridge for unitary conjugation
(connects S33 + S26 conjugation with linftyOp norm bound).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. `‖U‖_linftyOp ≤ n` for unitary U at SU(n) -/

/-- **`‖U‖_linftyOp ≤ n` for U unitary**. By `entry_norm_bound_of_unitary`,
each entry has norm ≤ 1, so each row sum is ≤ n. -/
theorem linftyOpNorm_unitary_le {n : ℕ} [Nonempty (Fin n)]
    (U : ↥(Matrix.unitaryGroup (Fin n) ℂ)) :
    ‖U.val‖ ≤ (n : ℝ) := by
  rw [Matrix.linfty_opNorm_def]
  rw [show ((n : ℝ) : ℝ) = ((n : NNReal) : ℝ) from by simp]
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i _
  -- ∑ j, ‖U.val i j‖₊ ≤ n via entry bound
  calc (∑ j, ‖U.val i j‖₊)
      ≤ (∑ _j : Fin n, (1 : NNReal)) := by
        apply Finset.sum_le_sum
        intro j _
        have h_entry : ‖U.val i j‖ ≤ 1 := entry_norm_bound_of_unitary U.2 i j
        exact_mod_cast h_entry
    _ = (n : NNReal) := by simp

/-! ## 2. `‖U · A · star U‖_linftyOp ≤ n² · ‖A‖_linftyOp` -/

/-- **Loose unitary conjugation norm bridge**: for U unitary at SU(n) and any
matrix A, `‖U · A · star U‖_linftyOp ≤ n² · ‖A‖_linftyOp`.

Proof: apply `Matrix.linfty_opNorm_mul` twice to get
`‖U · A · star U‖ ≤ ‖U‖ · ‖A‖ · ‖star U‖`. Then `‖U‖ ≤ n` (from §1) and
`‖star U‖ ≤ n` (star U = conjTranspose U is also unitary).

The tighter `n`-bound (via Cauchy-Schwarz) requires more refined analysis;
this module provides the loose `n²` bound suitable for cascade purposes. -/
theorem linftyOpNorm_unitary_conj_bound {n : ℕ} [Nonempty (Fin n)]
    (U : ↥(Matrix.unitaryGroup (Fin n) ℂ))
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖U.val * A * star U.val‖ ≤ (n : ℝ)^2 * ‖A‖ := by
  -- Step 1: ‖U · A · star U‖ ≤ ‖U‖ · ‖A‖ · ‖star U‖ via submultiplicativity
  have h1 : ‖U.val * A * star U.val‖ ≤ ‖U.val * A‖ * ‖star U.val‖ :=
    Matrix.linfty_opNorm_mul _ _
  have h2 : ‖U.val * A‖ ≤ ‖U.val‖ * ‖A‖ := Matrix.linfty_opNorm_mul _ _
  have h_U_norm : ‖U.val‖ ≤ (n : ℝ) := linftyOpNorm_unitary_le U
  -- star U is also unitary: ‖star U‖ ≤ n
  have h_starU_mem : star U.val ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.star_mem_iff.mpr U.2
  have h_starU_norm : ‖star U.val‖ ≤ (n : ℝ) :=
    linftyOpNorm_unitary_le ⟨star U.val, h_starU_mem⟩
  -- Combine
  have h_A_nn : 0 ≤ ‖A‖ := norm_nonneg _
  have h_starU_nn : 0 ≤ ‖star U.val‖ := norm_nonneg _
  calc ‖U.val * A * star U.val‖
      ≤ ‖U.val * A‖ * ‖star U.val‖ := h1
    _ ≤ (‖U.val‖ * ‖A‖) * ‖star U.val‖ := by
        gcongr
    _ ≤ ((n : ℝ) * ‖A‖) * (n : ℝ) := by
        gcongr
    _ = (n : ℝ)^2 * ‖A‖ := by ring

end SKEFTHawking.FKLW.GenericSUd
