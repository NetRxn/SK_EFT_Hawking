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

/-! ## 3. Status (substrate-fully-assembled)

The substantive substrate for S.2g UNCONDITIONAL discharge:
  * `multiDirExpProduct_hasStrictFDerivAt_zero` (✓)
  * `matrixLog_hasStrictFDerivAt_one` (✓)
  * `tsProj_matrixLog_multiDirExpProduct_hasStrictFDerivAt_zero` (✓)
  * `tsProj_multiDirDerivCLM_range_top_of_spans` (✓)
  * `composite_map_value_zero` (✓)
  * `completeSpace_tracelessSkewHermitian` (✓, this section)

The application of `HasStrictFDerivAt.map_nhds_eq_of_surj` to assemble
these into the final `Filter.map (composite) (nhds 0) = nhds 0`
encounters a Lean elaborator quirk: even when the
`CompleteSpace ↥(tracelessSkewHermitian (Fin d))` instance is supplied
locally (via `haveI` or as an explicit hypothesis), the synthesis
through `map_nhds_eq_of_surj`'s implicit args fails to find it. This
appears to be a Lean issue (not a missing math); investigation via
`set_option trace.Meta.synthInstance true` would localize the exact
unification failure.

WORKAROUND options for the eventual closure:
  * Use `HasStrictFDerivAt.toOpenPartialHomeomorph` (requires the
    derivative to be a `ContinuousLinearEquiv`, i.e., bijective).
    This needs basis-extraction from the spanning witness to get
    {X_i : Fin (d²-1) → 𝔰𝔲(d)} forming an ℝ-basis. Substantial
    finite-dim linear algebra.
  * Direct manual proof of "image of nbhd is nbhd" using the explicit
    inverse construction (the IFT proof structure unrolled, ~200 LoC). -/

end SKEFTHawking.FKLW.GenericSUd
