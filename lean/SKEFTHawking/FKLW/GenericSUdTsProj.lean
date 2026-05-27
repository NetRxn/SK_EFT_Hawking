/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2g-substrate — d-generic `tsProj` (projection onto `𝔰𝔲(d)`)

d-parametric lift of `SU2BCHBracketClosure.tsProj` (SU(2)-specific
projection onto `↥𝔰𝔲(2)`) to the d-generic setting. Ships the
continuous linear projection `tsProj_d : Matrix (Fin d) (Fin d) ℂ →L[ℝ]
↥(tracelessSkewHermitian (Fin d))` and its key identity property.

Used downstream in the multi-parameter IFT-on-subspace chain for the
S.2g unconditional discharge:

  * `tsProj_d ∘ matrixLog ∘ multiDirExpProduct X : ℝ^n → ↥𝔰𝔲(d)`
    has strict F-derivative `tsProj_d ∘ multiDirDerivCLM X` at 0.
  * For a basis {X_i}, this derivative is a `ContinuousLinearEquiv`
    ℝ^{d²-1} ≃L ↥𝔰𝔲(d), enabling IFT in subspace.
  * IFT gives local diffeo; transferred back via `expAmbient` gives
    an open nbhd of `1` in SU(d) contained in `H.val`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected; `Classical.choose`
    on `Submodule.exists_isCompl` (in standard kernel closure).

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2g (substrate part —
d-generic tsProj for IFT-on-subspace).

-/

import Mathlib
import SKEFTHawking.FKLW.SU2LieAlgebra

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix SU2LieAlgebra

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Real-linear complement of `𝔰𝔲(d)` in Matrix space -/

/-- **A real-linear complement of `𝔰𝔲(d)` in `Matrix (Fin d) (Fin d) ℂ`**.

Existence via `Submodule.exists_isCompl`. Used to define the projection
onto `↥𝔰𝔲(d)`. -/
noncomputable def tsCompl_d (d : ℕ) :
    Submodule ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  Classical.choose (Submodule.exists_isCompl
    (SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian (Fin d)))

/-- `tsCompl_d d` is a complement of `𝔰𝔲(d)`. -/
theorem ts_isCompl_tsCompl_d (d : ℕ) :
    IsCompl (SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian (Fin d))
            (tsCompl_d d) :=
  Classical.choose_spec (Submodule.exists_isCompl
    (SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian (Fin d)))

/-! ## 2. The continuous linear projection -/

/-- **d-generic projection** `tsProj_d : Matrix _ _ ℂ →L[ℝ] ↥𝔰𝔲(d)`.

Built from the linear projection onto the first component of the
direct-sum decomposition `Matrix = 𝔰𝔲(d) ⊕ tsCompl_d`. Auto-continuous
since `Matrix _ _ ℂ` is finite-dimensional over ℝ. -/
noncomputable def tsProj_d (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →L[ℝ]
      ↥(SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian (Fin d)) :=
  LinearMap.toContinuousLinearMap
    ((SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian (Fin d)).linearProjOfIsCompl
      (tsCompl_d d) (ts_isCompl_tsCompl_d d))

/-- **`tsProj_d` is identity on `↥𝔰𝔲(d)`** (after the subtype inclusion).

For `Y ∈ 𝔰𝔲(d)`, `tsProj_d Y = ⟨Y, hY⟩`. -/
theorem tsProj_d_apply_of_mem (d : ℕ)
    {Y : Matrix (Fin d) (Fin d) ℂ}
    (hY : Y ∈ SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian (Fin d)) :
    tsProj_d d Y = ⟨Y, hY⟩ := by
  show LinearMap.toContinuousLinearMap _ Y = _
  rw [LinearMap.coe_toContinuousLinearMap']
  exact Submodule.linearProjOfIsCompl_apply_left (ts_isCompl_tsCompl_d d) ⟨Y, hY⟩

/-- **`tsProj_d` of a value already in `↥𝔰𝔲(d)`**: the subtype value is preserved. -/
theorem tsProj_d_val_of_mem (d : ℕ)
    {Y : Matrix (Fin d) (Fin d) ℂ}
    (hY : Y ∈ SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian (Fin d)) :
    (tsProj_d d Y : Matrix (Fin d) (Fin d) ℂ) = Y := by
  rw [tsProj_d_apply_of_mem d hY]

/-- **`tsProj_d` of 0 is 0**. -/
@[simp]
theorem tsProj_d_zero (d : ℕ) : tsProj_d d 0 = 0 := by
  rw [tsProj_d_apply_of_mem d (Submodule.zero_mem _)]
  rfl

end SKEFTHawking.FKLW.GenericSUd
