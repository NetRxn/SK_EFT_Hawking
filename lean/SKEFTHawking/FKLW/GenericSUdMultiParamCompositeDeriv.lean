/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2g — Composite strict F-derivative for IFT-on-subspace

The composition
`tsProj_d ∘ matrixLog ∘ multiDirExpProduct X : (Fin n → ℝ) → ↥𝔰𝔲(d)`
admits a strict Fréchet derivative at `0`, equal to the composition
`tsProj_d ∘ multiDirDerivCLM X` at the linear level.

This is the load-bearing composite needed for the IFT-on-subspace
discharge of S.2g unconditional: when the composed derivative is a
`ContinuousLinearEquiv` (which holds when `{X_i}` is an ℝ-basis of
`𝔰𝔲(d)`), Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph` gives
a local diffeomorphism, and the image of the composite map covers a
nbhd of `0` in `↥𝔰𝔲(d)`. Transferred back via `exp` gives an open
nbhd of `1` in SU(d) contained in `H.val`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2g (substrate part —
composite derivative for IFT-on-subspace).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo
import SKEFTHawking.FKLW.GenericSUdMultiParamExpProduct
import SKEFTHawking.FKLW.GenericSUdMultiParamExpProductDeriv
import SKEFTHawking.FKLW.GenericSUdTsProj

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. matrixLog (= expAmbientPartialHomeo.symm) has strict F-derivative
identity at `1`

`matrixLog d` is the local inverse of `expAmbient d`. Since
`expAmbient d` has strict F-derivative `1` (identity) at `0`,
`matrixLog d` has strict F-derivative `1` (identity) at `expAmbient d 0 = 1`.

Via Mathlib's IFT round-trip: the partial homeomorphism's `.symm` has
strict F-derivative equal to the inverse of the forward derivative. -/

/-- **`matrixLog d` has strict F-derivative `id` at `1`** (substantive).

Via the IFT round-trip on `expAmbientPartialHomeo d`. -/
theorem matrixLog_hasStrictFDerivAt_one (d : ℕ) :
    HasStrictFDerivAt (matrixLog d)
      (ContinuousLinearMap.id ℝ (Matrix (Fin d) (Fin d) ℂ))
      (1 : Matrix (Fin d) (Fin d) ℂ) := by
  -- matrixLog d = expAmbientPartialHomeo.symm.
  -- Mathlib provides HasStrictFDerivAt.toOpenPartialHomeomorph_symm or similar.
  -- Use the .symm derivative formula: symm of a local diffeo at its image point
  -- has derivative equal to the inverse of the forward derivative.
  -- The forward expAmbient has strict F-deriv = ContinuousLinearEquiv.refl at 0.
  -- So matrixLog has strict F-deriv = (refl).symm = refl at expAmbient 0 = 1.
  have h_forward := expAmbient_hasStrictFDerivAt_zero_equiv d
  -- HasStrictFDerivAt.localInverse / .toOpenPartialHomeomorph.symm derivative.
  -- Use Mathlib's `HasStrictFDerivAt.to_localLeftInverse` or
  -- `OpenPartialHomeomorph.symm.hasStrictFDerivAt` chain.
  -- Equivalent route: use `HasStrictFDerivAt.toOpenPartialHomeomorph_symm`.
  have h_symm :
      HasStrictFDerivAt (expAmbientPartialHomeo d).symm
        (((ContinuousLinearEquiv.refl ℝ (Matrix (Fin d) (Fin d) ℂ)).symm) :
          Matrix (Fin d) (Fin d) ℂ →L[ℝ] Matrix (Fin d) (Fin d) ℂ)
        ((expAmbientPartialHomeo d) 0) := by
    -- Use the partial-homeomorph .symm strict F-derivative.
    exact h_forward.to_localInverse
  -- Cast to matrixLog and 1.
  show HasStrictFDerivAt (matrixLog d)
    (ContinuousLinearMap.id ℝ (Matrix (Fin d) (Fin d) ℂ)) 1
  have h_eq_one : (expAmbientPartialHomeo d) 0 = 1 :=
    expAmbientPartialHomeo_zero d
  rw [show matrixLog d = (expAmbientPartialHomeo d).symm from rfl]
  -- ContinuousLinearEquiv.refl.symm = refl, and its CLM coercion = id.
  have h_clm_eq :
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin d) (Fin d) ℂ)).symm :
        Matrix (Fin d) (Fin d) ℂ →L[ℝ] Matrix (Fin d) (Fin d) ℂ)
      = ContinuousLinearMap.id ℝ (Matrix (Fin d) (Fin d) ℂ) := by
    ext v
    simp
  rw [← h_clm_eq, ← h_eq_one]
  exact h_symm

/-! ## 2. The composed `matrixLog ∘ multiDirExpProduct` has strict F-derivative
`multiDirDerivCLM` at 0 -/

/-- **`matrixLog ∘ multiDirExpProduct X` has strict F-derivative
`multiDirDerivCLM X` at `0`** (substantive composition).

Via chain rule: `multiDirExpProduct X` has strict F-derivative
`multiDirDerivCLM X` at 0 (just shipped in
`multiDirExpProduct_hasStrictFDerivAt_zero`), and `matrixLog d` has
strict F-derivative `id` at `multiDirExpProduct X 0 = 1`. Composition
gives `id ∘ multiDirDerivCLM X = multiDirDerivCLM X`. -/
theorem matrixLog_comp_multiDirExpProduct_hasStrictFDerivAt_zero {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    HasStrictFDerivAt (matrixLog d ∘ multiDirExpProduct X)
      (multiDirDerivCLM X) (0 : Fin n → ℝ) := by
  have h_inner := multiDirExpProduct_hasStrictFDerivAt_zero X
  have h_outer : HasStrictFDerivAt (matrixLog d)
      (ContinuousLinearMap.id ℝ (Matrix (Fin d) (Fin d) ℂ))
      (multiDirExpProduct X (0 : Fin n → ℝ)) := by
    have h_value : multiDirExpProduct X (0 : Fin n → ℝ) = 1 := by
      show multiDirExpProduct X (fun _ : Fin n => (0 : ℝ)) = 1
      exact multiDirExpProduct_zero X
    rw [h_value]
    exact matrixLog_hasStrictFDerivAt_one d
  have h_comp := h_outer.comp (0 : Fin n → ℝ) h_inner
  -- h_comp: HasStrictFDerivAt (matrixLog d ∘ multiDirExpProduct X)
  --   (ContinuousLinearMap.id.comp multiDirDerivCLM X) 0
  -- id.comp f = f.
  have h_id_comp :
      (ContinuousLinearMap.id ℝ (Matrix (Fin d) (Fin d) ℂ)).comp
        (multiDirDerivCLM X) = multiDirDerivCLM X :=
    ContinuousLinearMap.id_comp _
  rw [h_id_comp] at h_comp
  exact h_comp

/-! ## 3. The full composite `tsProj_d ∘ matrixLog ∘ multiDirExpProduct` -/

/-- **`tsProj_d ∘ matrixLog ∘ multiDirExpProduct X` has strict F-derivative
`tsProj_d ∘ multiDirDerivCLM X` at `0`** (substantive headline).

The composite map lands in `↥(tracelessSkewHermitian (Fin d))` and is
the load-bearing setup for the IFT-on-subspace discharge of S.2g
unconditional. Chain rule applied to the §2 composition + `tsProj_d`'s
constant strict F-derivative (it's already linear). -/
theorem tsProj_matrixLog_multiDirExpProduct_hasStrictFDerivAt_zero {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    HasStrictFDerivAt
      (fun t : Fin n → ℝ =>
        tsProj_d d ((matrixLog d ∘ multiDirExpProduct X) t))
      ((tsProj_d d).comp (multiDirDerivCLM X)) (0 : Fin n → ℝ) := by
  have h_inner := matrixLog_comp_multiDirExpProduct_hasStrictFDerivAt_zero X
  -- tsProj_d is a CLM, hence its own strict F-derivative.
  have h_outer : HasStrictFDerivAt (tsProj_d d) (tsProj_d d)
      ((matrixLog d ∘ multiDirExpProduct X) (0 : Fin n → ℝ)) :=
    (tsProj_d d).hasStrictFDerivAt
  exact h_outer.comp (0 : Fin n → ℝ) h_inner

/-! ## 4. Surjectivity of the composite derivative when `{X_i}` spans

When the tangents `{X_i}` span `𝔰𝔲(d)`, the composite derivative
`tsProj_d ∘ multiDirDerivCLM X` is **surjective** onto `↥𝔰𝔲(d)`.

This is the load-bearing input to Mathlib's `map_nhds_eq_of_surj`
(`InverseFunctionTheorem/FDeriv.lean:84`), which converts surjectivity
of the strict F-derivative into "image of nbhd of 0 is a nbhd of 0
in `↥𝔰𝔲(d)`". -/

/-- **Composite derivative range = `⊤` of `↥𝔰𝔲(d)` when `{X_i}` spans**
(substantive).

If every `Y ∈ 𝔰𝔲(d)` is an ℝ-linear combination of `{X_i}` (the
Phase 6y S.2 spanning hypothesis), then the composite CLM
`tsProj_d.comp (multiDirDerivCLM X)` has range equal to all of
`↥𝔰𝔲(d)`. -/
theorem tsProj_multiDirDerivCLM_range_top_of_spans {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (_hX_in_sud : ∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0)
    (hX_spans : ∀ Y : Matrix (Fin d) (Fin d) ℂ,
      Y.IsSkewHermitian → Y.trace = 0 →
      ∃ c : Fin n → ℝ, Y = ∑ i, ((c i : ℝ) : ℂ) • X i) :
    ((tsProj_d d).comp (multiDirDerivCLM X)).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro Y_sub
  -- Y_sub : ↥(tracelessSkewHermitian (Fin d))
  -- Use spanning to get coefficients, then build the preimage.
  set Y_val := (Y_sub : Matrix (Fin d) (Fin d) ℂ) with hY_val_def
  have h_Y_sh : Y_val.IsSkewHermitian := Y_sub.property.1
  have h_Y_tr : Y_val.trace = 0 := Y_sub.property.2
  obtain ⟨c, hc⟩ := hX_spans Y_val h_Y_sh h_Y_tr
  refine ⟨c, ?_⟩
  -- Goal: (tsProj_d.comp (multiDirDerivCLM X)) c = Y_sub.
  -- LHS = tsProj_d (multiDirDerivCLM X c) = tsProj_d (∑ c i • X i) = tsProj_d Y_val.
  show ((tsProj_d d).comp (multiDirDerivCLM X)) c = Y_sub
  rw [ContinuousLinearMap.comp_apply, multiDirDerivCLM_apply]
  -- Goal: tsProj_d (∑ i, c i • X i) = Y_sub.
  have h_eq : (∑ i, (c i : ℝ) • X i : Matrix (Fin d) (Fin d) ℂ)
              = ∑ i, ((c i : ℝ) : ℂ) • X i := by
    apply Finset.sum_congr rfl
    intro i _
    exact (Complex.coe_smul (c i) (X i)).symm
  rw [h_eq, ← hc]
  -- Goal: tsProj_d Y_val = Y_sub.
  -- Y_val ∈ tracelessSkewHermitian, so tsProj_d gives ⟨Y_val, _⟩ = Y_sub.
  exact tsProj_d_apply_of_mem d Y_sub.property

end SKEFTHawking.FKLW.GenericSUd
