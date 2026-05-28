/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — expIsud near-identity norm bounds

The SU(d) analogs of SU(2)'s `expIsu2_norm_sub_one_le` /
`expIsu2_inv_norm_sub_one_le`: for Hermitian-traceless `F` with `‖F‖ ≤ δ`,

  `‖(expIsud n F).val − 1‖ ≤ δ · exp δ`        (forward)
  `‖exp(−(i·F)) − 1‖ ≤ δ · exp δ`              (inverse, since (expIsud).val⁻¹ = exp(−iF))

These are the near-identity exp bounds the super-quad main induction needs
for the group-commutator stability + cubic-remainder step. Both follow
directly from the **dimension-generic** `MatrixBCH.norm_exp_pm_I_smul_sub_one_le_delta`
(already `{d : ℕ} [Nonempty (Fin d)]`), so no SU(2)-specific reproof is needed —
just the `expIsud_val` bridge `(expIsud n F).val = exp(i·F)`.

## Substantive content shipped

  * `expIsud_norm_sub_one_le` — `‖(expIsud n F).val − 1‖ ≤ δ · exp δ`.
  * `expIsud_neg_exp_norm_sub_one_le` — `‖exp(−(i·F)) − 1‖ ≤ δ · exp δ`.
  * `expIsud_inv_val_eq_exp_neg` — `(expIsud n F).val⁻¹ = exp(−(i·F))`.
  * `expIsud_inv_norm_sub_one_le` — `‖(expIsud n F).val⁻¹ − 1‖ ≤ δ · exp δ`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — expIsud near-identity
norm bounds (super-quad main induction substrate).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdExpIsuDUnconditional
import SKEFTHawking.MatrixBCH

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **expIsud forward near-identity bound**: `‖(expIsud n F).val − 1‖ ≤ δ·exp δ`
for Hermitian-traceless `F` with `‖F‖ ≤ δ`. Mirrors SU(2)'s
`expIsu2_norm_sub_one_le`; uses the dimension-generic
`MatrixBCH.norm_exp_pm_I_smul_sub_one_le_delta`. -/
lemma expIsud_norm_sub_one_le {n : ℕ}
    (F : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (hF : F.IsHermitian) (htr : F.trace = 0)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hF_norm : ‖F‖ ≤ δ) :
    ‖((expIsud n F hF htr : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) - 1‖ ≤ δ * Real.exp δ := by
  rw [expIsud_val]
  exact (MatrixBCH.norm_exp_pm_I_smul_sub_one_le_delta F δ hδ_nn hF_norm).1

/-- **exp(−iF) near-identity bound**: `‖exp(−(i·F)) − 1‖ ≤ δ·exp δ`. -/
lemma expIsud_neg_exp_norm_sub_one_le {n : ℕ}
    (F : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (δ : ℝ) (hδ_nn : 0 ≤ δ) (hF_norm : ‖F‖ ≤ δ) :
    ‖NormedSpace.exp (-(Complex.I • F)) - 1‖ ≤ δ * Real.exp δ :=
  (MatrixBCH.norm_exp_pm_I_smul_sub_one_le_delta F δ hδ_nn hF_norm).2

/-- **expIsud matrix inverse equals exp(−iF)**: `(expIsud n F).val⁻¹ = exp(−(i·F))`.

For the unitary `A := exp(i·F) ∈ SU(d)`, the matrix inverse `A⁻¹` equals
`exp(−(i·F))` since `exp(i·F)·exp(−(i·F)) = exp(0) = 1` (the exponents commute).
Uses `Matrix.inv_eq_right_inv`. -/
lemma expIsud_inv_val_eq_exp_neg {n : ℕ}
    (F : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (hF : F.IsHermitian) (htr : F.trace = 0) :
    ((expIsud n F hF htr : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)⁻¹ =
      NormedSpace.exp (-(Complex.I • F)) := by
  rw [expIsud_val]
  apply Matrix.inv_eq_right_inv
  rw [← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]
  rw [add_neg_cancel, NormedSpace.exp_zero]

/-- **expIsud matrix-inverse near-identity bound**: `‖(expIsud n F).val⁻¹ − 1‖ ≤ δ·exp δ`.

Combines `expIsud_inv_val_eq_exp_neg` with `expIsud_neg_exp_norm_sub_one_le`.
Tighter than the SU(2) `√2·δ·exp δ` bound (no linftyOp inverse-norm looseness),
because `A⁻¹ = exp(−iF)` exactly. -/
lemma expIsud_inv_norm_sub_one_le {n : ℕ}
    (F : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (hF : F.IsHermitian) (htr : F.trace = 0)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hF_norm : ‖F‖ ≤ δ) :
    ‖((expIsud n F hF htr : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)⁻¹ - 1‖ ≤ δ * Real.exp δ := by
  rw [expIsud_inv_val_eq_exp_neg]
  exact expIsud_neg_exp_norm_sub_one_le F δ hδ_nn hF_norm

end SKEFTHawking.FKLW.GenericSUd
