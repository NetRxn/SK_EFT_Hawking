/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2d — `det(exp Y) = exp(tr Y)` for skew-Hermitian Y

Jacobi formula specialized to skew-Hermitian matrices. The general
case is not in Mathlib v4.29.1 (TODO in `MatrixExponential.lean`); the
skew-Hermitian specialization uses the spectral diagonalization of
`iY` (Hermitian) via `Matrix.IsHermitian.spectral_theorem`.

This file ships the load-bearing inputs needed for the Phase 6y SU(d)
discharge:

  * `isHermitian_I_smul_of_isSkewHermitian` — iY Hermitian when Y skew-Herm.
  * `trace_I_smul` — `tr(I • Y) = I * tr Y`.

Composition into the full `det_exp_skewHermitian` formula proceeds in
follow-on sub-waves; this file ships the foundational helpers that
unblock those sub-waves.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2d (Jacobi for
skew-Hermitian, foundational helpers).

-/

import Mathlib
import SKEFTHawking.FKLW.SU2LieAlgebra

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. `iY` is Hermitian when `Y` is skew-Hermitian -/

/-- **`iY` is Hermitian when `Y` is skew-Hermitian** (substantive).

`IsHermitian M ↔ M.conjTranspose = M`. We compute:
`(i • Y)ᴴ = (star i) • Yᴴ = (-i) • (-Y) = i • Y`.

Load-bearing for the spectral-decomposition route to the Jacobi formula
`det(exp Y) = exp(tr Y)` for skew-Hermitian Y: the Mathlib spectral
theorem applies to the Hermitian iY. -/
theorem isHermitian_I_smul_of_isSkewHermitian {d : ℕ}
    {Y : Matrix (Fin d) (Fin d) ℂ} (hY : Y.IsSkewHermitian) :
    (Complex.I • Y).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul]
  have h_star_I : (star Complex.I : ℂ) = -Complex.I := Complex.conj_I
  rw [h_star_I]
  have hY' : Y.conjTranspose = -Y := hY
  rw [hY']
  -- Goal: -Complex.I • -Y = Complex.I • Y
  module

/-! ## 2. Trace is ℂ-linear -/

/-- Trace is ℂ-linear (specialization): `tr (I • Y) = I * tr Y`. -/
theorem trace_I_smul {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℂ) :
    (Complex.I • Y).trace = Complex.I * Y.trace := by
  rw [Matrix.trace_smul, smul_eq_mul]

/-! ## 3. Helper: `exp` of conjugation by unitary -/

/-- For unitary `U`, `exp(U * A * star U) = U * exp A * star U`. -/
theorem exp_unitaryConj {d : ℕ} (U : ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (A : Matrix (Fin d) (Fin d) ℂ) :
    NormedSpace.exp (U.val * A * star U.val) =
      U.val * NormedSpace.exp A * star U.val := by
  have h_U_unit : IsUnit U.val := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact Matrix.UnitaryGroup.det_isUnit U
  -- For unitary U: matrix-level (U.val)⁻¹ = star U.val via U.val * star U.val = 1.
  have h_inv_eq : U.val⁻¹ = star U.val :=
    Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp U.property)
  rw [← h_inv_eq]
  exact Matrix.exp_conj _ _ h_U_unit

/-! ## 4. Helper: det of conjugation by unitary -/

/-- For unitary `U` and any `A`,
`det(U * A * star U) = det A`. -/
theorem det_unitaryConj {d : ℕ} (U : ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (U.val * A * star U.val).det = A.det := by
  rw [Matrix.det_mul, Matrix.det_mul]
  have h_uu_eq_one : U.val * star U.val = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.property
  have h_det_uu : U.val.det * (star U.val).det = 1 := by
    rw [← Matrix.det_mul, h_uu_eq_one, Matrix.det_one]
  rw [show U.val.det * A.det * (star U.val).det
      = (U.val.det * (star U.val).det) * A.det from by ring]
  rw [h_det_uu, one_mul]

/-! ## 5. Trace of conjugation by unitary -/

/-- For unitary `U` and any `A`, `tr(U * A * star U) = tr A` (cyclic). -/
theorem trace_unitaryConj {d : ℕ} (U : ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (U.val * A * star U.val).trace = A.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have h_star_uu : star U.val * U.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [h_star_uu, Matrix.one_mul]

/-! ## 6. Full Jacobi formula for skew-Hermitian matrices

`det(exp Y) = exp(tr Y)` for skew-Hermitian Y. Proof: spectral
decomposition of iY (Hermitian) into `U * diag(real eigenvalues) * star U`,
push the `-Complex.I` scalar through to get Y as `U * diag(-i evals) * star U`,
then apply `exp_unitaryConj` + `Matrix.exp_diagonal` to compute exp Y,
and finally `det_unitaryConj` + `Matrix.det_diagonal` + `Complex.exp_sum`
+ `trace_unitaryConj` + `Matrix.trace_diagonal` to compute det. -/

/-- **Jacobi formula for skew-Hermitian matrices**:
`det(exp Y) = exp(tr Y)` for `Y : Matrix (Fin d) (Fin d) ℂ` skew-Hermitian.

Proof composes the helpers in §1-5 via the spectral decomposition of
the Hermitian iY (`Matrix.IsHermitian.spectral_theorem`). -/
theorem det_exp_skewHermitian {d : ℕ}
    (Y : Matrix (Fin d) (Fin d) ℂ) (hY : Y.IsSkewHermitian) :
    (NormedSpace.exp Y : Matrix (Fin d) (Fin d) ℂ).det = Complex.exp Y.trace := by
  -- Step 1: iY is Hermitian.
  have h_iY_herm : (Complex.I • Y).IsHermitian :=
    isHermitian_I_smul_of_isSkewHermitian hY
  -- Step 2: Spectral decomposition iY = U * diag(↑evals) * star U.
  set U := h_iY_herm.eigenvectorUnitary with hU_def
  set evals : Fin d → ℝ := h_iY_herm.eigenvalues with hevals_def
  have h_spectral := h_iY_herm.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spectral
  -- h_spectral: I • Y = U.val * diag(RCLike.ofReal ∘ evals) * star U.val
  -- Step 3: Y = -I • (I • Y) = U.val * diag(-I * ↑evals) * star U.val.
  set evalsC : Fin d → ℂ := fun j => -Complex.I * (evals j : ℂ) with hevalsC_def
  have h_Y_conj : Y = U.val * Matrix.diagonal evalsC * star U.val := by
    have h_Y_eq : Y = (-Complex.I) • (Complex.I • Y) := by
      rw [smul_smul]
      have h_calc : -Complex.I * Complex.I = (1 : ℂ) := by
        rw [neg_mul, Complex.I_mul_I, neg_neg]
      rw [h_calc, one_smul]
    rw [h_Y_eq, h_spectral]
    -- Goal: -I • (U.val * diag (↑evals) * star U.val) = U.val * diag evalsC * star U.val.
    -- Push -I through to the diagonal factor.
    have h_push : (-Complex.I) •
        ((U.val : Matrix (Fin d) (Fin d) ℂ) *
          Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ evals) * star U.val) =
        U.val * ((-Complex.I) • Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ evals)) *
          star U.val := by
      rw [← smul_mul_assoc, ← mul_smul_comm]
    rw [h_push]
    -- Goal: U.val * (-I • diag (↑evals)) * star U.val = U.val * diag evalsC * star U.val
    congr 2
    rw [← Matrix.diagonal_smul]
    -- Goal: diag (-I • (RCLike.ofReal ∘ evals)) = diag evalsC.
    -- The two sides are def-equal modulo evalsC's unfolding.
    rfl
  -- Step 4: exp Y = U * diag(exp(-I · evals)) * star U.
  have h_exp_Y : NormedSpace.exp Y =
      U.val * Matrix.diagonal (fun j => Complex.exp (evalsC j)) * star U.val := by
    rw [h_Y_conj]
    rw [exp_unitaryConj]
    congr 1
    congr 1
    -- Goal: NormedSpace.exp (diagonal evalsC) = diagonal (fun j => Complex.exp (evalsC j))
    rw [Matrix.exp_diagonal]
    -- Goal: diagonal (NormedSpace.exp evalsC) = diagonal (fun j => Complex.exp (evalsC j))
    congr 1
    funext j
    -- Pi.exp evalsC j = NormedSpace.exp (evalsC j) = Complex.exp (evalsC j)
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  -- Step 5: det(exp Y) = det(diag(exp(evalsC))) (via det_unitaryConj).
  rw [h_exp_Y, det_unitaryConj, Matrix.det_diagonal]
  -- Step 6: ∏ exp(evalsC j) = exp(∑ evalsC j) = exp(tr Y) (via trace_unitaryConj).
  rw [← Complex.exp_sum]
  congr 1
  -- tr Y = tr(U * diag evalsC * star U) = tr(diag evalsC) = ∑ evalsC.
  rw [h_Y_conj, trace_unitaryConj, Matrix.trace_diagonal]

end SKEFTHawking.FKLW.GenericSUd
