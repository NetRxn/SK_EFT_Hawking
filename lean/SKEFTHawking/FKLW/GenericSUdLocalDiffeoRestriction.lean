/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2g-substrate — Local diffeo restriction `𝔰𝔲(d) ↔ SU(d)` near (0, 1)

The S.2g substrate that lifts the ambient matrix-exp local diffeo
(S.2b) to a **Lie-algebra-to-Lie-group local diffeomorphism**:

  * Forward: `Y ∈ 𝔰𝔲(d) ∩ source ⟹ expAmbient d Y ∈ SU(d) ∩ target`
    (uses skew-Hermitian-exp-is-unitary + S.2d Jacobi for det=1).
  * Backward: `h ∈ SU(d) ∩ small_nbhd ⟹ matrixLog d h ∈ 𝔰𝔲(d)`
    (uses S.2c skew-Hermitian preservation + S.2e PROPER traceless
    preservation = `matrixLog_in_su_d_on_nhd_one`).

The combined bijection on these restricted domains is the substantive
substrate that:

  * Phase 6y **S.2g** unconditional discharge consumes (the Cartan v4
    closer needs an open nbhd of `1` in SU(d), and this local diffeo
    transfers openness from `𝔰𝔲(d)` to `SU(d)`).
  * Phase 6y **T-A1′.2** SU(4) closure-density consumes (transferring
    spanning-set openness in `𝔰𝔲(4)` to openness at `1` in SU(4)).
  * Phase 6y **T-A2′.2** SU(8) closure-density consumes (analogously).
  * Phase 6y **S.5** generic SU(d) discharge consumes.
  * Phase 6y **S.6** UNCONDITIONAL headline consumes.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2g (substrate part —
local diffeo restriction).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo
import SKEFTHawking.FKLW.GenericSUdMatrixLogTraceless
import SKEFTHawking.FKLW.GenericSUdDetExpSkewHerm
import SKEFTHawking.FKLW.SU2MatrixExp
import SKEFTHawking.FKLW.SU2LieAlgebra

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Forward: `exp` of `𝔰𝔲(d)` lands in SU(d)

For `Y : Matrix (Fin d) (Fin d) ℂ` skew-Hermitian and traceless,
`expAmbient d Y ∈ SU(d)`. The skew-Hermitian part gives unitarity
(`Matrix.IsSkewHermitian.exp_mem_unitaryGroup`); the traceless part
combined with S.2d Jacobi (`det_exp_skewHermitian`) gives `det = 1`. -/

/-- **Exp of `𝔰𝔲(d)` element is in SU(d)** (substantive forward direction).

For `Y ∈ Matrix (Fin d) (Fin d) ℂ` with both `Y.IsSkewHermitian` and
`Y.trace = 0`, `expAmbient d Y ∈ Matrix.specialUnitaryGroup (Fin d) ℂ`. -/
theorem exp_of_su_d_mem_SUd {d : ℕ}
    {Y : Matrix (Fin d) (Fin d) ℂ}
    (hY_sh : Y.IsSkewHermitian) (hY_tr : Y.trace = 0) :
    expAmbient d Y ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · -- Unitary via skew-Hermitian-exp-is-unitary.
    show NormedSpace.exp Y ∈ Matrix.unitaryGroup (Fin d) ℂ
    exact Matrix.IsSkewHermitian.exp_mem_unitaryGroup hY_sh
  · -- det(exp Y) = exp(tr Y) = exp 0 = 1.
    show (NormedSpace.exp Y : Matrix (Fin d) (Fin d) ℂ).det = 1
    rw [det_exp_skewHermitian Y hY_sh, hY_tr, Complex.exp_zero]

/-! ## 2. Backward: matrixLog of SU(d) near 1 lands in `𝔰𝔲(d)`

Re-export of `matrixLog_in_su_d_on_nhd_one` (already shipped in
S.2e PROPER combined headline). -/

/-- **MatrixLog of SU(d) near 1 is in `𝔰𝔲(d)`** (re-export of S.2e
combined headline; substantive backward direction).

For `h ∈ SU(d)` sufficiently close to `1`, `matrixLog d h` is skew-
Hermitian and traceless. -/
theorem matrixLog_of_SUd_in_su_d (d : ℕ) [Nonempty (Fin d)] (hd_pos : 0 < d) :
    ∃ V ∈ nhds (1 : Matrix (Fin d) (Fin d) ℂ),
      ∀ h ∈ V, h ∈ Matrix.specialUnitaryGroup (Fin d) ℂ →
        h ∈ (expAmbientPartialHomeo d).target →
        (matrixLog d h).IsSkewHermitian ∧ (matrixLog d h).trace = 0 :=
  matrixLog_in_su_d_on_nhd_one d hd_pos

/-! ## 3. Forward openness: exp of 𝔰𝔲(d)-nbhd is in SU(d)

Combines §1 (forward direction) with the existing ambient local diffeo
(S.2b) to show: an exp-image of any nbhd of 0 in `𝔰𝔲(d)` ∩ source
sits entirely inside SU(d). -/

/-- **Exp-image of `𝔰𝔲(d)` ∩ source is in SU(d) ∩ target**.

If `Y ∈ source ∩ (skew-Hermitian + traceless)`, then `expAmbient d Y`
is in `SU(d) ∩ target`. This is the load-bearing forward-openness
statement: `expAmbient d` maps the `𝔰𝔲(d)`-restriction of source
INTO SU(d) ∩ target. -/
theorem expAmbient_su_d_subset_SUd {d : ℕ}
    {Y : Matrix (Fin d) (Fin d) ℂ}
    (hY_source : Y ∈ (expAmbientPartialHomeo d).source)
    (hY_sh : Y.IsSkewHermitian) (hY_tr : Y.trace = 0) :
    expAmbient d Y ∈ Matrix.specialUnitaryGroup (Fin d) ℂ ∧
    expAmbient d Y ∈ (expAmbientPartialHomeo d).target := by
  refine ⟨exp_of_su_d_mem_SUd hY_sh hY_tr, ?_⟩
  -- exp maps source to target.
  rw [← expAmbientPartialHomeo_coe d]
  exact (expAmbientPartialHomeo d).map_source hY_source

/-! ## 4. Combined bijection on the restricted domain

For `Y ∈ source` skew-Hermitian + traceless, the local diffeo round-trip
`matrixLog d (expAmbient d Y) = Y` recovers Y. And for
`h ∈ SU(d) ∩ small_nbhd`, the round-trip `expAmbient d (matrixLog d h) = h`
recovers h. -/

/-- **Round-trip `matrixLog ∘ expAmbient = id` on `𝔰𝔲(d)` ∩ source**.

Direct corollary of `matrixLog_expAmbient` (S.2b); the `𝔰𝔲(d)`
hypotheses (`Y.IsSkewHermitian ∧ Y.trace = 0`) are not used in the
round-trip itself, but are documented here for downstream
consumer-friendly invocation. -/
theorem matrixLog_expAmbient_on_su_d (d : ℕ)
    {Y : Matrix (Fin d) (Fin d) ℂ}
    (hY_source : Y ∈ (expAmbientPartialHomeo d).source)
    (_hY_sh : Y.IsSkewHermitian) (_hY_tr : Y.trace = 0) :
    matrixLog d (expAmbient d Y) = Y :=
  matrixLog_expAmbient d hY_source

/-- **Round-trip `expAmbient ∘ matrixLog = id` on SU(d) ∩ target**
(direct corollary of `expAmbient_matrixLog`). -/
theorem expAmbient_matrixLog_on_SUd (d : ℕ)
    {h : Matrix (Fin d) (Fin d) ℂ}
    (_h_SUd : h ∈ Matrix.specialUnitaryGroup (Fin d) ℂ)
    (h_target : h ∈ (expAmbientPartialHomeo d).target) :
    expAmbient d (matrixLog d h) = h :=
  expAmbient_matrixLog d h_target

/-! ## 5. Source intersected with the `𝔰𝔲(d)` predicate is nonempty

`0 ∈ source` (by S.2b) and `0 ∈ 𝔰𝔲(d)` (skew-Hermitian + traceless),
so the restricted domain is non-trivial. -/

/-- **The zero matrix is in the restricted source `𝔰𝔲(d) ∩ source`**. -/
theorem zero_in_restricted_source (d : ℕ) :
    (0 : Matrix (Fin d) (Fin d) ℂ) ∈ (expAmbientPartialHomeo d).source ∧
    (0 : Matrix (Fin d) (Fin d) ℂ).IsSkewHermitian ∧
    (0 : Matrix (Fin d) (Fin d) ℂ).trace = 0 := by
  refine ⟨zero_mem_expAmbientPartialHomeo_source d, ?_, ?_⟩
  · -- (0 : Matrix _ _ ℂ).IsSkewHermitian ↔ (0)ᴴ = -0, both 0.
    show (0 : Matrix (Fin d) (Fin d) ℂ).conjTranspose = -0
    simp [Matrix.conjTranspose_zero]
  · exact Matrix.trace_zero _ _

end SKEFTHawking.FKLW.GenericSUd
