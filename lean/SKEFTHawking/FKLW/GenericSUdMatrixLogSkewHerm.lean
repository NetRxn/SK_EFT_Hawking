/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2c — Matrix log of unitary is skew-Hermitian (local)

For `h ∈ SU(d)` sufficiently close to `1`, the matrix logarithm
`matrixLog d h` (defined via IFT on `NormedSpace.exp` in `S.2b`) is
skew-Hermitian. This is half of the substrate needed for `S.2d`'s
discharge of `CartanFinalStep_SUd_v4`; the matching traceless
preservation ships separately.

## Mathematical content

For `h ∈ SU(d)` near `1`, write `Y := matrixLog d h ∈ source` with
`exp Y = h`. Then:

  * `exp Y.conjTranspose = (exp Y).conjTranspose = h.conjTranspose = h⁻¹`
    (using `Matrix.exp_conjTranspose` and unitarity `h.conjTranspose = h⁻¹`).
  * `exp (-Y) = (exp Y)⁻¹ = h⁻¹` (using `Matrix.exp_neg`).
  * So `exp Y.conjTranspose = exp (-Y)`.
  * By `expAmbient_injOn_source` (with both `Y.conjTranspose, -Y ∈ source`),
    `Y.conjTranspose = -Y`, i.e., `Y.IsSkewHermitian`.

The "both in source" condition is ensured by the topological nbhd argument:
`Y ∈ source ∩ ((·).conjTranspose ⁻¹' source) ∩ ((-·) ⁻¹' source)`
holds in a nbhd of 0 (intersection of three open nbhds of 0; the
preimages are open by continuity of `conjTranspose` and `neg`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2c (skew-Hermitian half).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo
import SKEFTHawking.FKLW.SU2LieAlgebra

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Symmetric source nbhd

The set of `Y` such that `Y, -Y, Y.conjTranspose` are all in source is
a nbhd of 0 in `Matrix (Fin d) (Fin d) ℂ`. Intersection of three open
nbhds of 0 (using continuity of `neg` and `conjTranspose`). -/

/-- **The symmetric source nbhd** at `0`: the intersection of `source`
with its preimage under `neg` and `conjTranspose`. -/
def symmetricSourceNbhd (d : ℕ) : Set (Matrix (Fin d) (Fin d) ℂ) :=
  (expAmbientPartialHomeo d).source ∩
    (Neg.neg ⁻¹' (expAmbientPartialHomeo d).source) ∩
    (Matrix.conjTranspose ⁻¹' (expAmbientPartialHomeo d).source)

/-- `0 ∈ symmetricSourceNbhd d`. -/
theorem zero_mem_symmetricSourceNbhd (d : ℕ) :
    (0 : Matrix (Fin d) (Fin d) ℂ) ∈ symmetricSourceNbhd d := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact zero_mem_expAmbientPartialHomeo_source d
  · simpa using zero_mem_expAmbientPartialHomeo_source d
  · simpa using zero_mem_expAmbientPartialHomeo_source d

/-- `symmetricSourceNbhd d` is open. -/
theorem isOpen_symmetricSourceNbhd (d : ℕ) :
    IsOpen (symmetricSourceNbhd d) := by
  refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
  · exact expAmbientPartialHomeo_source_isOpen d
  · exact (continuous_neg).isOpen_preimage _ (expAmbientPartialHomeo_source_isOpen d)
  · exact (Continuous.matrix_conjTranspose continuous_id).isOpen_preimage _
            (expAmbientPartialHomeo_source_isOpen d)

/-- `symmetricSourceNbhd d` is a nbhd of `0`. -/
theorem symmetricSourceNbhd_mem_nhds_zero (d : ℕ) :
    symmetricSourceNbhd d ∈ nhds (0 : Matrix (Fin d) (Fin d) ℂ) :=
  (isOpen_symmetricSourceNbhd d).mem_nhds (zero_mem_symmetricSourceNbhd d)

/-! ## 2. Matrix log is continuous at 1

The IFT-derived `expAmbientPartialHomeo.symm` is continuous on its
target. Combined with `matrixLog 1 = 0`, this gives `matrixLog d` is
continuous at `1` with value `0`. -/

/-- `matrixLog d` is continuous at `1`. -/
theorem matrixLog_continuousAt_one (d : ℕ) :
    ContinuousAt (matrixLog d) 1 := by
  apply ContinuousOn.continuousAt
    (s := (expAmbientPartialHomeo d).target)
    ((expAmbientPartialHomeo d).continuousOn_symm)
    (expAmbientPartialHomeo_target_mem_nhds_one d)

/-- The preimage of any nbhd of `0` under `matrixLog d` is a nbhd of `1`. -/
theorem matrixLog_preimage_nhds_zero_mem_nhds_one
    (d : ℕ) {S : Set (Matrix (Fin d) (Fin d) ℂ)} (hS : S ∈ nhds (0 : Matrix (Fin d) (Fin d) ℂ)) :
    (matrixLog d ⁻¹' S) ∈ nhds (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have h_cont := matrixLog_continuousAt_one d
  unfold ContinuousAt at h_cont
  rw [matrixLog_one] at h_cont
  exact h_cont hS

/-! ## 3. Skew-Hermitian preservation on a small nbhd of 1

The substantive result: for `h ∈ SU(d)` close enough to `1`,
`matrixLog d h` is skew-Hermitian. -/

/-- **Matrix log of unitary near 1 is skew-Hermitian** (substantive).

For `h ∈ SU(d)` in a sufficiently small neighborhood of `1`, the local
matrix logarithm `Y := matrixLog d h` satisfies `Y.IsSkewHermitian`. -/
theorem matrixLog_isSkewHermitian_on_nhd_one (d : ℕ) :
    ∃ V ∈ nhds (1 : Matrix (Fin d) (Fin d) ℂ),
      ∀ h ∈ V, h ∈ Matrix.specialUnitaryGroup (Fin d) ℂ →
        h ∈ (expAmbientPartialHomeo d).target →
        Matrix.IsSkewHermitian (matrixLog d h) := by
  refine ⟨(matrixLog d ⁻¹' symmetricSourceNbhd d) ∩
            (expAmbientPartialHomeo d).target, ?_, ?_⟩
  · exact Filter.inter_mem
            (matrixLog_preimage_nhds_zero_mem_nhds_one d
              (symmetricSourceNbhd_mem_nhds_zero d))
            (expAmbientPartialHomeo_target_mem_nhds_one d)
  · intro h hh_V hh_su hh_target
    set Y := matrixLog d h with hY_def
    have hY_sym : Y ∈ symmetricSourceNbhd d := hh_V.1
    obtain ⟨⟨hY_source, hnegY_source⟩, hYstar_source⟩ := hY_sym
    -- Unfold the preimage memberships.
    have hnegY_source' : (-Y) ∈ (expAmbientPartialHomeo d).source := hnegY_source
    have hYstar_source' : Y.conjTranspose ∈ (expAmbientPartialHomeo d).source :=
      hYstar_source
    -- exp Y = h.
    have hexp_Y : expAmbient d Y = h := expAmbient_matrixLog d hh_target
    have hexp_Y' : NormedSpace.exp Y = h := hexp_Y
    -- exp Y.conjTranspose = h.conjTranspose (via Matrix.exp_conjTranspose).
    have h_conj : expAmbient d Y.conjTranspose = h.conjTranspose := by
      show NormedSpace.exp Y.conjTranspose = h.conjTranspose
      rw [Matrix.exp_conjTranspose, hexp_Y']
    -- exp (-Y) = h⁻¹ (via Matrix.exp_neg).
    have h_neg : expAmbient d (-Y) = h⁻¹ := by
      show NormedSpace.exp (-Y) = h⁻¹
      rw [Matrix.exp_neg, hexp_Y']
    -- h.conjTranspose = h⁻¹ (from h ∈ unitary).
    have h_star_eq_inv : h.conjTranspose = h⁻¹ := by
      have h_unitary : h ∈ Matrix.unitaryGroup (Fin d) ℂ :=
        (Matrix.mem_specialUnitaryGroup_iff.mp hh_su).1
      have h_left_inv : h.conjTranspose * h = 1 := by
        have := Matrix.mem_unitaryGroup_iff'.mp h_unitary
        simpa [Matrix.star_eq_conjTranspose] using this
      exact (Matrix.inv_eq_left_inv h_left_inv).symm
    -- exp Y.conjTranspose = exp (-Y).
    have h_exp_eq : expAmbient d Y.conjTranspose = expAmbient d (-Y) := by
      rw [h_conj, h_neg, h_star_eq_inv]
    -- By injectivity: Y.conjTranspose = -Y.
    have h_eq : Y.conjTranspose = -Y :=
      expAmbient_injOn_source d hYstar_source' hnegY_source' h_exp_eq
    -- Y.IsSkewHermitian unfolds to Y.conjTranspose = -Y.
    exact h_eq

end SKEFTHawking.FKLW.GenericSUd
