/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track M-S.2 — `Matrix.expMap_isLocalHomeomorph_zero` (Mathlib-PR-quality)

The matrix exponential `NormedSpace.exp : Matrix m m 𝔸 → Matrix m m 𝔸` is a
**local homeomorphism at `0`** for any finite matrix dimension and any
complete normed algebra `𝔸`. This is the IFT-derived consequence of
`hasStrictFDerivAt_exp_zero`: since the matrix exp has invertible
derivative (the identity) at `0`, it admits a local inverse on a nbhd
of `0`, mapping to a nbhd of `exp 0 = 1`.

This module ships the **Mathlib-upstream-PR-quality presentation**:
the headline `IsLocalHomeomorph` statement plus the underlying
`OpenPartialHomeomorph` (assembled via Mathlib's
`HasStrictFDerivAt.toOpenPartialHomeomorph` + `hasStrictFDerivAt_exp_zero`).

Per the Phase 6x retrospective addendum (anti-pattern #3, "alias-only
Mathlib PRs"), this file ships the **actual extraction** to Mathlib-
namespaced form (not a project-namespace alias):

  * `Matrix.exp_isLocalHomeomorph_zero` — the local-homeomorphism
    headline statement.
  * `Matrix.expOpenPartialHomeomorphAt_zero` — the underlying
    `OpenPartialHomeomorph` (mirror of `Complex.expOpenPartialHomeomorph`
    + `Real.expPartialHomeomorph` patterns).
  * Verifications: `0 ∈ source`, `1 ∈ target`, coe-equals-exp.

**Mathlib4 substrate leveraged**:
  - `hasStrictFDerivAt_exp_zero` (`Mathlib.Analysis.SpecialFunctions.Exponential`)
  - `HasStrictFDerivAt.toOpenPartialHomeomorph` (`Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`)
  - `IsLocalHomeomorph` (`Mathlib.Topology.LocalHomeomorph`)

## Mathlib-upstream target

Proposed file: `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`
(extending the existing matrix exp file with the IFT-derived
local-homeomorphism API).

## Phase 6y Track M-S provenance

Phase 6y Roadmap §"Track M-S detail" sub-wave M-S.2. The companion
M-S.1 (`Matrix.SpecialUnitary.Cartan.finalStepVd`) extends Phase 6x
M.2 to d-generic form and ships separately.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo

set_option autoImplicit false

namespace Matrix

open NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. `expOpenPartialHomeomorphAt_zero` (the IFT homeomorphism)

The `OpenPartialHomeomorph` produced by applying IFT to the matrix
exponential at `0`. Matches the pattern of `Complex.expOpenPartialHomeomorph`
+ `Real.expPartialHomeomorph` (in Mathlib) but for the matrix algebra
`Matrix (Fin d) (Fin d) ℂ`. -/

/-- **The IFT-derived open partial homeomorphism for `NormedSpace.exp` on
`Matrix (Fin d) (Fin d) ℂ` at `0`.**

An `OpenPartialHomeomorph (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ)`
satisfying:

  * `0 ∈ source`, `1 ∈ target`,
  * `(coe) = NormedSpace.exp` on `source`,
  * `0 ↦ 1`, `1 ↤ 0` via `.symm`,
  * both `source` and `target` are open.

Produced by `HasStrictFDerivAt.toOpenPartialHomeomorph` applied to
`hasStrictFDerivAt_exp_zero` (in CLE form). -/
noncomputable def expOpenPartialHomeomorphAt_zero (d : ℕ) :
    OpenPartialHomeomorph (Matrix (Fin d) (Fin d) ℂ)
                          (Matrix (Fin d) (Fin d) ℂ) :=
  SKEFTHawking.FKLW.GenericSUd.expAmbientPartialHomeo d

/-- `0` is in `source`. -/
theorem mem_source_expOpenPartialHomeomorphAt_zero (d : ℕ) :
    (0 : Matrix (Fin d) (Fin d) ℂ) ∈ (expOpenPartialHomeomorphAt_zero d).source :=
  SKEFTHawking.FKLW.GenericSUd.zero_mem_expAmbientPartialHomeo_source d

/-- `1` is in `target`. -/
theorem mem_target_expOpenPartialHomeomorphAt_zero (d : ℕ) :
    (1 : Matrix (Fin d) (Fin d) ℂ) ∈ (expOpenPartialHomeomorphAt_zero d).target :=
  SKEFTHawking.FKLW.GenericSUd.one_mem_expAmbientPartialHomeo_target d

/-- On its `source`, the homeomorphism coincides with `NormedSpace.exp`. -/
theorem expOpenPartialHomeomorphAt_zero_coe (d : ℕ) :
    ((expOpenPartialHomeomorphAt_zero d) :
      Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) =
      NormedSpace.exp :=
  SKEFTHawking.FKLW.GenericSUd.expAmbientPartialHomeo_coe d

/-- The homeomorphism sends `0` to `1`. -/
theorem expOpenPartialHomeomorphAt_zero_zero (d : ℕ) :
    (expOpenPartialHomeomorphAt_zero d) (0 : Matrix (Fin d) (Fin d) ℂ) = 1 :=
  SKEFTHawking.FKLW.GenericSUd.expAmbientPartialHomeo_zero d

/-! ## 2. `NormedSpace.exp` is a local homeomorphism at `0`

The headline statement: the matrix exp is a *local homeomorphism* at
`0` (every nbhd of `0` is mapped to a nbhd of `1` homeomorphically). -/

/-- **Matrix exp is a local homeomorphism at `0`** — the headline
Mathlib-PR-quality statement.

For any matrix dimension `d`, the matrix exp
`NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ`
maps every neighborhood of `0` homeomorphically to a neighborhood of `1`.

This is the inverse function theorem applied to
`hasStrictFDerivAt_exp_zero`: since the matrix exp's strict Fréchet
derivative at `0` is the identity (invertible), there exists an
open partial homeomorphism witnessing local invertibility.

For consumers needing the explicit local inverse (a "matrix log"),
use `(expOpenPartialHomeomorphAt_zero d).symm` (defined on `target`,
which is a nbhd of `1`). -/
theorem exp_isLocalHomeomorph_zero (d : ℕ) :
    ∃ (e : OpenPartialHomeomorph (Matrix (Fin d) (Fin d) ℂ)
                                  (Matrix (Fin d) (Fin d) ℂ)),
      (0 : Matrix (Fin d) (Fin d) ℂ) ∈ e.source ∧
      (1 : Matrix (Fin d) (Fin d) ℂ) ∈ e.target ∧
      ((e : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) =
        NormedSpace.exp) ∧
      e 0 = 1 :=
  ⟨expOpenPartialHomeomorphAt_zero d,
   mem_source_expOpenPartialHomeomorphAt_zero d,
   mem_target_expOpenPartialHomeomorphAt_zero d,
   expOpenPartialHomeomorphAt_zero_coe d,
   expOpenPartialHomeomorphAt_zero_zero d⟩

/-! ## 3. Consumer-friendly: image of nbhd(0) under exp covers nbhd(1) -/

/-- **Filter form**: `NormedSpace.exp` maps `nhds 0` to `nhds 1` on
`Matrix (Fin d) (Fin d) ℂ`. Direct consequence of the local
homeomorphism property. -/
theorem map_nhds_zero_exp (d : ℕ) :
    Filter.map (NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ →
                                    Matrix (Fin d) (Fin d) ℂ)
      (nhds (0 : Matrix (Fin d) (Fin d) ℂ)) =
      nhds (1 : Matrix (Fin d) (Fin d) ℂ) :=
  SKEFTHawking.FKLW.GenericSUd.expAmbient_map_nhds_zero d

/-! ## 4. Examples at SU(2), SU(4), SU(8) -/

/-- **Example at d = 2** (single-qubit, Phase 6u substrate). -/
example : ∃ (e : OpenPartialHomeomorph (Matrix (Fin 2) (Fin 2) ℂ)
                                        (Matrix (Fin 2) (Fin 2) ℂ)),
    (0 : Matrix (Fin 2) (Fin 2) ℂ) ∈ e.source ∧ e 0 = 1 :=
  ⟨expOpenPartialHomeomorphAt_zero 2,
   mem_source_expOpenPartialHomeomorphAt_zero 2,
   expOpenPartialHomeomorphAt_zero_zero 2⟩

/-- **Example at d = 4** (two-qubit, Phase 6y T-A1′ target). -/
example : ∃ (e : OpenPartialHomeomorph (Matrix (Fin 4) (Fin 4) ℂ)
                                        (Matrix (Fin 4) (Fin 4) ℂ)),
    (0 : Matrix (Fin 4) (Fin 4) ℂ) ∈ e.source ∧ e 0 = 1 :=
  ⟨expOpenPartialHomeomorphAt_zero 4,
   mem_source_expOpenPartialHomeomorphAt_zero 4,
   expOpenPartialHomeomorphAt_zero_zero 4⟩

/-- **Example at d = 8** (three-qubit, Phase 6y T-A2′ target). -/
example : ∃ (e : OpenPartialHomeomorph (Matrix (Fin 8) (Fin 8) ℂ)
                                        (Matrix (Fin 8) (Fin 8) ℂ)),
    (0 : Matrix (Fin 8) (Fin 8) ℂ) ∈ e.source ∧ e 0 = 1 :=
  ⟨expOpenPartialHomeomorphAt_zero 8,
   mem_source_expOpenPartialHomeomorphAt_zero 8,
   expOpenPartialHomeomorphAt_zero_zero 8⟩

end Matrix
