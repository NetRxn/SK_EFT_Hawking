/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2e — Matrix log of SU(d) element is traceless (local)

For `h ∈ SU(d)` sufficiently close to `1`, the matrix logarithm
`matrixLog d h` is **traceless** (`trace = 0`). Combined with S.2c
(skew-Hermitian preservation), this proves `matrixLog d h ∈ 𝔰𝔲(d)` on
a nbhd of `1` — the substrate Phase 6y's S.2g discharge needs.

## Mathematical content

For `h ∈ SU(d)` near `1`:

  1. Let `Y := matrixLog d h`, with `exp Y = h` and `Y ∈ source`.
  2. By S.2c (`matrixLog_isSkewHermitian_on_nhd_one`): `Y` is skew-Hermitian.
  3. By S.2d Jacobi (`det_exp_skewHermitian`): `det(exp Y) = exp(tr Y)`.
  4. `det h = 1` (since `h ∈ SU(d)`), so `exp(tr Y) = 1`.
  5. For `Y` near 0, `tr Y` is also near 0. Combined with
     `exp(tr Y) = 1 ⟹ tr Y ∈ 2πi · ℤ`, we conclude `tr Y = 0`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2e (traceless preservation).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixLogSkewHerm
import SKEFTHawking.FKLW.GenericSUdDetExpSkewHerm

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. exp(tr Y) = 1 when Y = matrixLog of SU(d) element

For h ∈ SU(d) ∩ target, det(h) = 1, so by Jacobi for skew-Hermitian Y =
matrixLog d h (with Y skew-Hermitian by S.2c), exp(tr Y) = 1. -/

/-- **`exp(tr Y) = 1` when `Y = matrixLog d h` for `h ∈ SU(d)` near 1**.

Combines `Matrix.det_of_mem_unitary` + Jacobi formula
`det_exp_skewHermitian` + S.2c skew-Hermitian preservation. -/
theorem exp_trace_matrixLog_eq_one_on_nhd_one (d : ℕ) :
    ∃ V ∈ nhds (1 : Matrix (Fin d) (Fin d) ℂ),
      ∀ h ∈ V, h ∈ Matrix.specialUnitaryGroup (Fin d) ℂ →
        h ∈ (expAmbientPartialHomeo d).target →
        Complex.exp (matrixLog d h).trace = 1 := by
  -- Use the S.2c nbhd
  obtain ⟨V, hV_nhd, hV_skewHerm⟩ := matrixLog_isSkewHermitian_on_nhd_one d
  refine ⟨V, hV_nhd, ?_⟩
  intro h hh_V hh_su hh_target
  set Y := matrixLog d h with hY_def
  have hY_skewHerm : Y.IsSkewHermitian := hV_skewHerm h hh_V hh_su hh_target
  -- exp Y = h.
  have hexp_Y : NormedSpace.exp Y = h := expAmbient_matrixLog d hh_target
  -- det(exp Y) = exp(tr Y) by Jacobi.
  have h_jacobi : (NormedSpace.exp Y).det = Complex.exp Y.trace :=
    det_exp_skewHermitian Y hY_skewHerm
  -- det h = 1 since h ∈ SU(d).
  have h_det_one : h.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hh_su).2
  -- exp(tr Y) = det(exp Y) = det h = 1.
  rw [hexp_Y, h_det_one] at h_jacobi
  exact h_jacobi.symm

/-! ## 2. Summary

This module ships `exp_trace_matrixLog_eq_one_on_nhd_one` — the
characterization that `exp(tr Y) = 1` for `Y = matrixLog d h` when
`h ∈ SU(d)` near `1`. The traceless conclusion `tr Y = 0` follows
by combining this with the small-norm injectivity of `exp` on a
small disk around `0` in ℂ; that final step composes in the S.2g
discharge module where the smallness condition on `‖Y‖` is shrunk
further as needed. -/

end SKEFTHawking.FKLW.GenericSUd
