/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Hermitian eigenvalue bounded by linftyOp norm (Gershgorin)

For a Hermitian `A : Matrix (Fin n) (Fin n) ℂ`, each eigenvalue satisfies
`|eigenvalue| ≤ ‖A‖_linftyOp` (Gershgorin circle theorem: every eigenvalue
lies within the max row sum of |entries|).

This is the last mathematical ingredient for the F_inner norm bound: the
partial sums `b_p = ∑_{j≤p} a_j` (where `a_j` are sorted eigenvalues)
satisfy `b_p ≤ (p+1)·max|a_j| ≤ (p+1)·‖H‖_linftyOp`, so `B = d·‖H‖`.

## Substantive content shipped

  * `isHermitian_eigenvalue_abs_le_linftyOpNorm` — `|hA.eigenvalues i| ≤ ‖A‖`

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — eigenvalue linftyOp bound
(F_inner norm bound, B = d·‖H‖ ingredient via Gershgorin).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Hermitian eigenvalue absolute value bounded by linftyOp norm** (Gershgorin).

For Hermitian `A : Matrix (Fin n) (Fin n) ℂ`, `|hA.eigenvalues i| ≤ ‖A‖_linftyOp`.

Proof: `(hA.eigenvalues i : ℂ)` is a root of `A.charpoly` (from the
spectral factorization `charpoly_eq`), hence an eigenvalue of `toLin' A`;
Gershgorin (`eigenvalue_mem_ball`) places it within the row-`k` Gershgorin
disc, so `|μ| ≤ |A k k| + ∑_{j≠k} ‖A k j‖ = ∑_j ‖A k j‖ ≤ ‖A‖_linftyOp`. -/
theorem isHermitian_eigenvalue_abs_le_linftyOpNorm {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i : Fin n) :
    |hA.eigenvalues i| ≤ ‖A‖ := by
  -- The complex coercion of the eigenvalue is a root of the charpoly.
  have h_root : A.charpoly.IsRoot ((hA.eigenvalues i : ℝ) : ℂ) := by
    rw [hA.charpoly_eq]
    rw [Polynomial.IsRoot, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  -- Root of charpoly ⟹ eigenvalue of toLin' A.
  have h_eig : Module.End.HasEigenvalue (Matrix.toLin' A) ((hA.eigenvalues i : ℝ) : ℂ) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    rwa [Matrix.charpoly_toLin']
  -- Gershgorin: μ ∈ closedBall (A k k) (∑_{j≠k} ‖A k j‖).
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball h_eig
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  -- |μ| ≤ |μ - A k k| + |A k k| ≤ (∑_{j≠k} ‖A k j‖) + ‖A k k‖ = ∑_j ‖A k j‖.
  have h_mu_norm : ‖((hA.eigenvalues i : ℝ) : ℂ)‖ ≤ ∑ j, ‖A k j‖ := by
    calc ‖((hA.eigenvalues i : ℝ) : ℂ)‖
        = ‖(((hA.eigenvalues i : ℝ) : ℂ) - A k k) + A k k‖ := by ring_nf
      _ ≤ ‖((hA.eigenvalues i : ℝ) : ℂ) - A k k‖ + ‖A k k‖ := norm_add_le _ _
      _ ≤ (∑ j ∈ Finset.univ.erase k, ‖A k j‖) + ‖A k k‖ := by gcongr
      _ = ∑ j, ‖A k j‖ :=
          Finset.sum_erase_add Finset.univ (fun j => ‖A k j‖) (Finset.mem_univ k)
  -- ‖μ‖ = |eigenvalue| (norm of real coercion).
  have h_norm_eq : ‖((hA.eigenvalues i : ℝ) : ℂ)‖ = |hA.eigenvalues i| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h_norm_eq] at h_mu_norm
  -- ∑_j ‖A k j‖ ≤ ‖A‖_linftyOp (row-k sum ≤ max row sum).
  have h_row_le : ∑ j, ‖A k j‖ ≤ ‖A‖ := by
    rw [Matrix.linfty_opNorm_def]
    have h_nn : (∑ j, ‖A k j‖₊) ≤ Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) :=
      Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ k)
    calc ∑ j, ‖A k j‖
        = ((∑ j, ‖A k j‖₊ : NNReal) : ℝ) := by
          push_cast; rfl
      _ ≤ ((Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) : NNReal) : ℝ) :=
          NNReal.coe_le_coe.mpr h_nn
  exact le_trans h_mu_norm h_row_le

end SKEFTHawking.FKLW.GenericSUd
