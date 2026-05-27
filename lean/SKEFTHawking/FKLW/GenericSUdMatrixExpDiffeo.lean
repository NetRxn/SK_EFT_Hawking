/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2b — Generic SU(d) matrix-exp local diffeomorphism

d-parametric lift of `SU2LocalDiffeo` (the Phase 6u SU(2)-specific
matrix-exp IFT setup) to arbitrary `d : ℕ`. Ships:

  * `expAmbient d : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ`
    — alias for `NormedSpace.exp` at type `Matrix (Fin d) (Fin d) ℂ`;
  * `expAmbient_hasStrictFDerivAt_zero_equiv d` — the matrix exp has
    strict Fréchet derivative `ContinuousLinearEquiv.refl ℝ _` at 0,
    a direct alias of Mathlib's `hasStrictFDerivAt_exp_zero`;
  * `expAmbientPartialHomeo d : OpenPartialHomeomorph (Matrix _ _ ℂ) (Matrix _ _ ℂ)`
    — the IFT-derived open partial homeomorphism with `source ∋ 0`,
    `target ∋ 1`, `0 ↦ 1`, and `.symm` acting as a local matrix
    logarithm near `1`;
  * `matrixLog d : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ`
    — local matrix log via `expAmbientPartialHomeo.symm`;
  * `expAmbient_matrixLog`, `matrixLog_expAmbient` — round-trip
    identities on the local source/target;
  * `expAmbient_injOn_source` — local injectivity of exp.

These are the d-generic counterparts of `SU2LocalDiffeo` (~250 LoC)
and the §§1-2 of `OneParameterSubgroupSU2` (~170 LoC). Since the
underlying Mathlib substrate (`NormedSpace.exp`, `hasStrictFDerivAt_exp_zero`,
`HasStrictFDerivAt.toOpenPartialHomeomorph`) is already d-generic, the
generalization is mechanical type-parametrization.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2 (substrate part).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. `expAmbient d` alias for `NormedSpace.exp` on `Matrix (Fin d) (Fin d) ℂ`

A d-generic alias for `NormedSpace.exp` at the matrix algebra
`Matrix (Fin d) (Fin d) ℂ`. Matches the project's `SU2MatrixExp.expAmbient`
naming convention but parametric in `d`. -/

/-- **d-generic matrix exp**: `expAmbient d` is `NormedSpace.exp` at type
`Matrix (Fin d) (Fin d) ℂ`. Convenience alias for downstream
readability + Lean type-class resolution. -/
noncomputable def expAmbient (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ :=
  NormedSpace.exp

/-- `expAmbient d 0 = 1`. -/
@[simp]
theorem expAmbient_zero (d : ℕ) : expAmbient d 0 = 1 :=
  NormedSpace.exp_zero

/-! ## 2. F-derivative at 0 (CLE form, ready for IFT)

The matrix exp has strict Fréchet derivative equal to the identity at
the zero matrix; viewing the identity continuous linear map as a
`ContinuousLinearEquiv` (the IFT API requirement) is a direct cast. -/

/-- **`expAmbient` has strict Fréchet derivative `1` at `0`** (CLM form).
Direct specialization of Mathlib's `hasStrictFDerivAt_exp_zero`. -/
theorem expAmbient_hasStrictFDerivAt_zero (d : ℕ) :
    HasStrictFDerivAt (expAmbient d)
      (1 : Matrix (Fin d) (Fin d) ℂ →L[ℝ] Matrix (Fin d) (Fin d) ℂ) 0 :=
  hasStrictFDerivAt_exp_zero

/-- **`expAmbient` has strict Fréchet derivative `ContinuousLinearEquiv.refl ℝ _` at `0`**
— the CLE form required by `HasStrictFDerivAt.toOpenPartialHomeomorph` (IFT). -/
theorem expAmbient_hasStrictFDerivAt_zero_equiv (d : ℕ) :
    HasStrictFDerivAt (expAmbient d)
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin d) (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ →L[ℝ] Matrix (Fin d) (Fin d) ℂ) 0 :=
  expAmbient_hasStrictFDerivAt_zero d

/-! ## 3. The IFT-derived open partial homeomorphism

The matrix exp restricted to a small ball around `0` is a homeomorphism
onto a small ball around `1`; this is precisely the inverse function
theorem applied to `expAmbient_hasStrictFDerivAt_zero_equiv`. -/

/-- **The local IFT homeomorphism for `expAmbient d` at `0`** —
an `OpenPartialHomeomorph` on `Matrix (Fin d) (Fin d) ℂ` with:

  * `0 ∈ source`, `1 ∈ target`,
  * `(coercion) = expAmbient d` on `source`,
  * `0 ↦ 1`,
  * `.symm` acts as a local matrix logarithm near `1`.

Produced by Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph` on
the CLE-form derivative. -/
noncomputable def expAmbientPartialHomeo (d : ℕ) :
    OpenPartialHomeomorph (Matrix (Fin d) (Fin d) ℂ)
                          (Matrix (Fin d) (Fin d) ℂ) :=
  HasStrictFDerivAt.toOpenPartialHomeomorph (expAmbient d)
    (expAmbient_hasStrictFDerivAt_zero_equiv d)

/-- `0` is in the source of the local homeomorphism. -/
theorem zero_mem_expAmbientPartialHomeo_source (d : ℕ) :
    (0 : Matrix (Fin d) (Fin d) ℂ) ∈ (expAmbientPartialHomeo d).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    (expAmbient_hasStrictFDerivAt_zero_equiv d)

/-- On its source, the local homeomorphism coincides with `expAmbient d`. -/
theorem expAmbientPartialHomeo_coe (d : ℕ) :
    ((expAmbientPartialHomeo d) :
      Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) =
      expAmbient d :=
  HasStrictFDerivAt.toOpenPartialHomeomorph_coe
    (expAmbient_hasStrictFDerivAt_zero_equiv d)

/-- The homeomorphism sends `0` to `1`. -/
theorem expAmbientPartialHomeo_zero (d : ℕ) :
    (expAmbientPartialHomeo d) (0 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  rw [expAmbientPartialHomeo_coe]
  exact expAmbient_zero d

/-- `1` is in the target of the local homeomorphism. -/
theorem one_mem_expAmbientPartialHomeo_target (d : ℕ) :
    (1 : Matrix (Fin d) (Fin d) ℂ) ∈ (expAmbientPartialHomeo d).target := by
  rw [← expAmbientPartialHomeo_zero d]
  exact (expAmbientPartialHomeo d).map_source
    (zero_mem_expAmbientPartialHomeo_source d)

/-- The local-homeomorphism source is open. -/
theorem expAmbientPartialHomeo_source_isOpen (d : ℕ) :
    IsOpen (expAmbientPartialHomeo d).source :=
  (expAmbientPartialHomeo d).open_source

/-- The local-homeomorphism target is open. -/
theorem expAmbientPartialHomeo_target_isOpen (d : ℕ) :
    IsOpen (expAmbientPartialHomeo d).target :=
  (expAmbientPartialHomeo d).open_target

/-- The target of the local homeomorphism is a neighborhood of `1`. -/
theorem expAmbientPartialHomeo_target_mem_nhds_one (d : ℕ) :
    (expAmbientPartialHomeo d).target ∈ nhds (1 : Matrix (Fin d) (Fin d) ℂ) :=
  IsOpen.mem_nhds (expAmbientPartialHomeo_target_isOpen d)
    (one_mem_expAmbientPartialHomeo_target d)

/-! ## 4. `matrixLog d` — the local matrix logarithm

Defined as the `.symm` of the IFT homeomorphism. On `target` (a nbhd
of `1`) it is the local inverse of `expAmbient d`. -/

/-- **`matrixLog d`** — the local matrix logarithm near `1`, defined as
the `.symm` of `expAmbientPartialHomeo d`. Defined on
`(expAmbientPartialHomeo d).target` (a neighborhood of `1` in
`Matrix (Fin d) (Fin d) ℂ`); on this domain it is a right-inverse of
`expAmbient d`.

For `h` outside the target, `matrixLog d h` returns the partial inverse's
extension (unspecified value), so meaningful predicates always carry
`h ∈ (expAmbientPartialHomeo d).target` as a hypothesis. -/
noncomputable def matrixLog (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ :=
  (expAmbientPartialHomeo d).symm

/-- `matrixLog d 1 = 0`. -/
@[simp]
theorem matrixLog_one (d : ℕ) : matrixLog d (1 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
  show (expAmbientPartialHomeo d).symm 1 = 0
  rw [← expAmbientPartialHomeo_zero d]
  exact (expAmbientPartialHomeo d).left_inv
    (zero_mem_expAmbientPartialHomeo_source d)

/-- For `h ∈ target`, `expAmbient d (matrixLog d h) = h` (right inverse). -/
theorem expAmbient_matrixLog (d : ℕ) {h : Matrix (Fin d) (Fin d) ℂ}
    (hh : h ∈ (expAmbientPartialHomeo d).target) :
    expAmbient d (matrixLog d h) = h := by
  show expAmbient d ((expAmbientPartialHomeo d).symm h) = h
  rw [← expAmbientPartialHomeo_coe d]
  exact (expAmbientPartialHomeo d).right_inv hh

/-- For `Y ∈ source`, `matrixLog d (expAmbient d Y) = Y` (left inverse). -/
theorem matrixLog_expAmbient (d : ℕ) {Y : Matrix (Fin d) (Fin d) ℂ}
    (hY : Y ∈ (expAmbientPartialHomeo d).source) :
    matrixLog d (expAmbient d Y) = Y := by
  show (expAmbientPartialHomeo d).symm (expAmbient d Y) = Y
  rw [← expAmbientPartialHomeo_coe d]
  exact (expAmbientPartialHomeo d).left_inv hY

/-! ## 5. Local injectivity of exp

For `A, B ∈ source` with `expAmbient d A = expAmbient d B`, conclude
`A = B`. Building block for uniqueness arguments downstream. -/

/-- **`expAmbient d` injective on source**. -/
theorem expAmbient_injOn_source (d : ℕ) :
    Set.InjOn (expAmbient d) (expAmbientPartialHomeo d).source := by
  intro A hA B hB h_eq
  have h_A : matrixLog d (expAmbient d A) = A := matrixLog_expAmbient d hA
  have h_B : matrixLog d (expAmbient d B) = B := matrixLog_expAmbient d hB
  rw [← h_A, h_eq, h_B]

/-! ## 6. The image of exp near 0 covers a nbhd of 1

Consumer-friendly form: every neighborhood of `0` maps to a set
containing a neighborhood of `1` under `expAmbient d`. -/

/-- **`expAmbient d` maps nbhd(0) to nbhd(1)**. -/
theorem expAmbient_map_nhds_zero (d : ℕ) :
    Filter.map (expAmbient d) (nhds (0 : Matrix (Fin d) (Fin d) ℂ)) =
      nhds (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have h_map : Filter.map (expAmbient d)
      (nhds (0 : Matrix (Fin d) (Fin d) ℂ)) =
      nhds (expAmbient d (0 : Matrix (Fin d) (Fin d) ℂ)) :=
    (expAmbient_hasStrictFDerivAt_zero_equiv d).map_nhds_eq_of_equiv
  rw [h_map, expAmbient_zero]

end SKEFTHawking.FKLW.GenericSUd
