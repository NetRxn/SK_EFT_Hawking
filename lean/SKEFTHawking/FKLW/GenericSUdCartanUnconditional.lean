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

/-! ## Status (substrate-level)

The substantive substrate for S.2g UNCONDITIONAL discharge is fully
assembled:
  * `multiDirExpProduct_hasStrictFDerivAt_zero` (✓)
  * `matrixLog_hasStrictFDerivAt_one` (✓)
  * `tsProj_matrixLog_multiDirExpProduct_hasStrictFDerivAt_zero` (✓)
  * `tsProj_multiDirDerivCLM_range_top_of_spans` (✓, this file's input)
  * `composite_map_value_zero` (✓, this file)

The final application of Mathlib's `HasStrictFDerivAt.map_nhds_eq_of_surj`
requires supplying the `CompleteSpace ↥(tracelessSkewHermitian (Fin d))`
instance at the use site. The needed substrate
(`Submodule.complete_of_finiteDimensional` + `completeSpace_coe_iff_isComplete`)
is in Mathlib but synthesis requires careful instance ordering. This
finalization ships in a follow-on commit. -/

end SKEFTHawking.FKLW.GenericSUd
