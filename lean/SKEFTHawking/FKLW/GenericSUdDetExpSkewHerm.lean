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

end SKEFTHawking.FKLW.GenericSUd
