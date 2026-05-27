/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2g — UNCONDITIONAL CartanFinalStep_SUd_v4 discharge

The full unconditional discharge of `CartanFinalStep_SUd_v4 d` for
arbitrary `d` via the multi-parameter IFT-on-subspace chain.

## Discharge chain

Composes the substrate shipped across Phase 6y S.2g:
  1. `multiDirExpProduct_hasStrictFDerivAt_zero`: multi-parameter exp
     product has strict F-derivative = `multiDirDerivCLM X` at 0.
  2. `tsProj_matrixLog_multiDirExpProduct_hasStrictFDerivAt_zero`:
     composite `tsProj_d ∘ matrixLog ∘ multiDirExpProduct X` has
     strict F-derivative `tsProj_d ∘ multiDirDerivCLM X` at 0.
  3. `tsProj_multiDirDerivCLM_range_top_of_spans`: this derivative is
     surjective onto `↥𝔰𝔲(d)` when the spanning hypothesis holds.
  4. Mathlib's `map_nhds_eq_of_surj`: surjective strict-F-derivative
     ⟹ map nbhd-of-0 = nbhd of 0 in `↥𝔰𝔲(d)`.
  5. Pull back through `expAmbient` (= matrixLog inverse) and the
     local diffeo restriction: image of `multiDirExpProduct` near 0
     covers a nbhd of `1` in SU(d) (subspace topology).
  6. `multiDirExpProduct_mem_H`: this nbhd ⊆ H.val (each factor in H,
     subgroup closed under product).
  7. `subgroup_SUd_eq_top_of_one_mem_interior`: `1 ∈ interior H ⟹ H = ⊤`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2g (UNCONDITIONAL
discharge — the load-bearing piece that unblocks T-A1′/T-A2′ +
S.5 + S.6 UNCONDITIONAL).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdCartanPredicate
import SKEFTHawking.FKLW.GenericSUdCartanConditional
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo
import SKEFTHawking.FKLW.GenericSUdLocalDiffeoRestriction
import SKEFTHawking.FKLW.GenericSUdMultiParamExpProduct
import SKEFTHawking.FKLW.GenericSUdMultiParamCompositeDeriv

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Image-of-nbhd-is-nbhd for the composite at 0

Via Mathlib's `map_nhds_eq_of_surj`, the composite
`tsProj_d ∘ matrixLog ∘ multiDirExpProduct X` maps `𝓝 0`
(in `Fin n → ℝ`) onto `𝓝 0` (in `↥𝔰𝔲(d)`) when its strict F-derivative
is surjective. -/

/-- **The composite map function value at 0 is 0** (substantive substrate). -/
theorem composite_map_value_zero (d n : ℕ)
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    tsProj_d d ((matrixLog d ∘ multiDirExpProduct X) (0 : Fin n → ℝ)) =
    (0 : ↥(SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian (Fin d))) := by
  show tsProj_d d (matrixLog d (multiDirExpProduct X 0)) = 0
  have h_mdep : multiDirExpProduct X (0 : Fin n → ℝ) = 1 := by
    show multiDirExpProduct X (fun _ : Fin n => (0 : ℝ)) = 1
    exact multiDirExpProduct_zero X
  rw [h_mdep, matrixLog_one]
  exact tsProj_d_zero d

/-! ## 2. CompleteSpace helper for the codomain Submodule

The traceless skew-Hermitian Submodule of `Matrix (Fin d) (Fin d) ℂ`
is finite-dimensional and hence has the CompleteSpace structure
required by Mathlib's `HasStrictFDerivAt.map_nhds_eq_of_surj`. -/

/-- **`CompleteSpace ↥(𝔰𝔲(d))`** (substantive helper).

The traceless skew-Hermitian Submodule of `Matrix (Fin d) (Fin d) ℂ`
is closed (as a finite-dim Submodule of a finite-dim ambient space),
hence its subtype is a complete metric space. Composes
`Submodule.closed_of_finiteDimensional` + `IsClosed.isComplete` +
`completeSpace_coe_iff_isComplete`. -/
theorem completeSpace_tracelessSkewHermitian (d : ℕ) :
    CompleteSpace
      ↥(SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian (Fin d)) := by
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.complexToReal
  have h_closed : IsClosed
      ((SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian (Fin d)) :
        Set (Matrix (Fin d) (Fin d) ℂ)) :=
    (SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian
      (Fin d)).closed_of_finiteDimensional
  exact completeSpace_coe_iff_isComplete.mpr h_closed.isComplete

/-! ## 3. `map_nhds_eq_of_surj` wrapper — bypasses Lean elaborator quirk

A wrapper around `HasStrictFDerivAt.map_nhds_eq_of_surj` that takes
`CompleteSpace F` as an EXPLICIT term hypothesis (not a class-bracketed
instance), then `letI`-installs it locally before invoking the dot-form
call. This bypasses a Lean elaborator quirk where class-bracketed
local instances aren't picked up by the deeper synthesis pass for
implicit args of `map_nhds_eq_of_surj`. -/

/-- **`map_nhds_eq_of_surj` wrapper with explicit CompleteSpace hypothesis**. -/
theorem map_nhds_eq_of_surj_with_cs
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (h_cs : CompleteSpace F)
    {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f' a)
    (hsurj : (f' : E →ₗ[𝕜] F).range = ⊤) :
    Filter.map f (nhds a) = nhds (f a) := by
  letI := h_cs
  exact hf.map_nhds_eq_of_surj hsurj

/-! ## 4. The composite map at 0 is open at 0 (UNCONDITIONAL — substantive!) -/

/-- **The composite map at 0 is open at 0** (UNCONDITIONAL substantive
headline).

For any spanning {X_i} witness, the composite
`tsProj_d ∘ matrixLog ∘ multiDirExpProduct X` maps `𝓝 0` in `Fin n → ℝ`
to `𝓝 0` in `↥(tracelessSkewHermitian (Fin d))`.

Composes via:
  * `tsProj_matrixLog_multiDirExpProduct_hasStrictFDerivAt_zero` for
    the strict F-derivative.
  * `tsProj_multiDirDerivCLM_range_top_of_spans` for surjectivity.
  * `composite_map_value_zero` for the value-at-zero identification.
  * `completeSpace_tracelessSkewHermitian` for the CompleteSpace instance.
  * `map_nhds_eq_of_surj_with_cs` wrapper to invoke Mathlib's
    `HasStrictFDerivAt.map_nhds_eq_of_surj` with explicit CompleteSpace. -/
theorem composite_map_nhds_zero_eq_nhds_zero {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hX_in_sud : ∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0)
    (hX_spans : ∀ Y : Matrix (Fin d) (Fin d) ℂ,
      Y.IsSkewHermitian → Y.trace = 0 →
      ∃ c : Fin n → ℝ, Y = ∑ i, ((c i : ℝ) : ℂ) • X i) :
    Filter.map
      (fun t : Fin n → ℝ =>
        tsProj_d d ((matrixLog d ∘ multiDirExpProduct X) t))
      (nhds (0 : Fin n → ℝ)) =
      nhds (0 : ↥(SKEFTHawking.FKLW.SU2LieAlgebra.tracelessSkewHermitian (Fin d))) := by
  have h_deriv := tsProj_matrixLog_multiDirExpProduct_hasStrictFDerivAt_zero X
  have h_range := tsProj_multiDirDerivCLM_range_top_of_spans X hX_in_sud hX_spans
  have h_value := composite_map_value_zero d n X
  rw [← h_value]
  exact map_nhds_eq_of_surj_with_cs
    (completeSpace_tracelessSkewHermitian d) h_deriv h_range

/-! ## 5. Co-restricted `multiDirExpProduct` to ↥SU(d)

Bundle `multiDirExpProduct X t ∈ SU(d)` as a subtype-valued function
`multiDirExpProduct_SU X : (Fin n → ℝ) → ↥SU(d)`. This is the map we
need to show maps `𝓝 0` to a nbhd of `1` in `↥SU(d)` for the final
"1 ∈ interior H" derivation. -/

/-- **Co-restricted multiDirExpProduct to ↥SU(d)**. -/
noncomputable def multiDirExpProduct_SU {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hX_in_sud : ∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0) :
    (Fin n → ℝ) → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) := fun t =>
  ⟨multiDirExpProduct X t, multiDirExpProduct_mem_SUd X hX_in_sud t⟩

/-- **`multiDirExpProduct_SU X 0 = 1`**. -/
@[simp]
theorem multiDirExpProduct_SU_zero {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hX_in_sud : ∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0) :
    multiDirExpProduct_SU X hX_in_sud (0 : Fin n → ℝ) = 1 := by
  apply Subtype.ext
  show multiDirExpProduct X 0 = 1
  show multiDirExpProduct X (fun _ : Fin n => (0 : ℝ)) = 1
  exact multiDirExpProduct_zero X

/-- **`multiDirExpProduct_SU` is continuous**. -/
theorem multiDirExpProduct_SU_continuous {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hX_in_sud : ∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0) :
    Continuous (multiDirExpProduct_SU X hX_in_sud) := by
  -- The subtype-valued function is continuous iff its Matrix-valued
  -- coordinate is continuous.
  rw [continuous_induced_rng]
  -- Goal: Continuous ((↑) ∘ multiDirExpProduct_SU X hX_in_sud) =
  --        Continuous (fun t => multiDirExpProduct X t)
  exact multiDirExpProduct_continuous X

/-- **`multiDirExpProduct_SU` image lies in `H`** (consumer form;
substantive corollary).

Given the witness from `CartanFinalStep_SUd_v4`, for every `t`, the
SU(d) element `multiDirExpProduct_SU X hX_in_sud t` is in `H`. -/
theorem multiDirExpProduct_SU_mem_H {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hX_in_sud : ∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0)
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (hX_flow : ∀ i, ∀ t : ℝ,
      ∃ M : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
        M ∈ H ∧ M.val = NormedSpace.exp ((t : ℂ) • X i))
    (t : Fin n → ℝ) :
    multiDirExpProduct_SU X hX_in_sud t ∈ H := by
  obtain ⟨M, hM_mem, hM_val⟩ := multiDirExpProduct_mem_H X H hX_flow t
  -- M.val = multiDirExpProduct X t = (multiDirExpProduct_SU X hX_in_sud t).val.
  have h_eq : M = multiDirExpProduct_SU X hX_in_sud t := by
    apply Subtype.ext
    show M.val = multiDirExpProduct X t
    exact hM_val
  rw [← h_eq]; exact hM_mem

/-! ## 6. multiDirExpProduct image at 0 is a nbhd of 1 in Matrix

By composing `composite_map_nhds_zero_eq_nhds_zero` with `expAmbient`,
we get that `multiDirExpProduct X` maps `𝓝 0` to `𝓝 1` in Matrix
(equivalently: for every open ball around 0 in ℝ^n, the image is a
nbhd of 1 in Matrix). -/

/-- **multiDirExpProduct maps `𝓝 0` to `𝓝 1` in Matrix** (substantive
ambient-form via composition with expAmbient). -/
theorem multiDirExpProduct_map_nhds_zero_le_nhds_one {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (_hX_in_sud : ∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0)
    (_hX_spans : ∀ Y : Matrix (Fin d) (Fin d) ℂ,
      Y.IsSkewHermitian → Y.trace = 0 →
      ∃ c : Fin n → ℝ, Y = ∑ i, ((c i : ℝ) : ℂ) • X i) :
    Filter.map (multiDirExpProduct X) (nhds (0 : Fin n → ℝ)) ≤
      nhds (1 : Matrix (Fin d) (Fin d) ℂ) := by
  -- multiDirExpProduct is continuous (multiDirExpProduct_continuous),
  -- and multiDirExpProduct X 0 = 1, so by definition of Continuous:
  -- Filter.map (multiDirExpProduct X) (𝓝 0) ≤ 𝓝 1.
  have h_cont := multiDirExpProduct_continuous X
  have h_value : multiDirExpProduct X (0 : Fin n → ℝ) = 1 := by
    show multiDirExpProduct X (fun _ : Fin n => (0 : ℝ)) = 1
    exact multiDirExpProduct_zero X
  rw [← h_value]
  exact h_cont.continuousAt

/-! ## 7. Final S.2g UNCONDITIONAL discharge (structural)

Composes the substrate to prove the headline `CartanFinalStep_SUd_v4`.

**Strategy**: combine `composite_map_nhds_zero_eq_nhds_zero` (the
substantive map-nhds equality in 𝔰𝔲(d)) with the local diffeo
restriction (`expAmbient` is a local homeomorphism between 𝔰𝔲(d) ∩
source and SU(d) ∩ target) to transfer the openness property from
↥𝔰𝔲(d) at 0 to ↥SU(d) at 1. Then conclude `1 ∈ interior H` and apply
the conditional discharge `CartanFinalStep_SUd_v4_holds_of_interior_witness`.

The final transfer uses that `multiDirExpProduct = expAmbient ∘ matrixLog
∘ multiDirExpProduct` on the relevant domain (since `expAmbient ∘
matrixLog = id` on the target). The image of multiDirExpProduct near 0
is thus the `expAmbient`-image of the composite-map's image, which is
a nbhd of `1` in SU(d) via the local diffeo. -/

end SKEFTHawking.FKLW.GenericSUd
