/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.4 PROPER — Explicit `matrixLog d` Lipschitz constant K = 2

The **explicit d-dependent Lipschitz constant** for the IFT-derived matrix
log `matrixLog d` (Phase 6y S.2b), refining the existential
`matrixLog_smallness_on_nhd_one` in `GenericSUdMatrixLogLipschitz.lean`.

## Substantive content

Composes the **strict F-derivative of `matrixLog d` at 1** (shipped as
`matrixLog_hasStrictFDerivAt_one` in `GenericSUdMultiParamCompositeDeriv.lean`)
with Mathlib's strict-F-derivative ε-δ characterization to produce the
explicit bound `‖matrixLog d h‖ ≤ 2 · ‖h - 1‖` on a neighborhood of 1.

This is the **d-generic counterpart** of the Phase 6u SU(2)-specific
`Y_h_norm_le_four_norm_sub_one` (Bloch-sphere parametrization, K=4); the
d-generic argument via IFT theory gives the tighter K=2 bound but
applies for all d (not just d=2).

The Phase 6y S.4 roadmap intent is satisfied: an EXPLICIT d-dependent
constant (constant in d, equal to 2, via IFT derivative inverse).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.4 PROPER (explicit Lipschitz
constant via IFT theory).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo
import SKEFTHawking.FKLW.GenericSUdMultiParamCompositeDeriv

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Explicit Lipschitz constant K = 2 -/

/-- **EXPLICIT Lipschitz bound `‖matrixLog d h‖ ≤ 2 · ‖h - 1‖`** on a
neighborhood of 1 (S.4 PROPER substantive ship; d-generic constant K=2).

The strict F-derivative `D matrixLog (1) = id` gives, by Mathlib's
strict-F-derivative ε-δ characterization:

  ∀ ε > 0, eventually in 𝓝 (1, 1):
    ‖matrixLog d x.2 - matrixLog d x.1 - id (x.2 - x.1)‖ ≤ ε · ‖x.2 - x.1‖

Specialize to (x.1 = 1, x.2 = h), pull back via the continuous diagonal
embedding x ↦ (1, x), simplify using `matrixLog 1 = 0` and `id (h - 1) =
h - 1`, then apply triangle inequality:

  ‖matrixLog d h‖ ≤ ‖matrixLog d h - (h - 1)‖ + ‖h - 1‖ ≤ ε·‖h-1‖ + ‖h-1‖

With ε = 1 this gives the K = 2 bound. -/
theorem matrixLog_lipschitz_K_two_near_one (d : ℕ) :
    ∃ δ > (0 : ℝ), ∀ h : Matrix (Fin d) (Fin d) ℂ,
      ‖h - 1‖ < δ →
      ‖matrixLog d h‖ ≤ 2 * ‖h - 1‖ := by
  -- Strict F-derivative of matrixLog d at 1 is id.
  have h_deriv := matrixLog_hasStrictFDerivAt_one d
  have h_isLittleO := h_deriv.isLittleO
  have h_one_pos : (1 : ℝ) > 0 := one_pos
  have h_eventually :
      ∀ᶠ x : Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ in nhds (1, 1),
        ‖matrixLog d x.1 - matrixLog d x.2 -
            (ContinuousLinearMap.id ℝ (Matrix (Fin d) (Fin d) ℂ))
              (x.1 - x.2)‖ ≤
          1 * ‖x.1 - x.2‖ := h_isLittleO.bound h_one_pos
  -- Pull back via the diagonal map x ↦ (x, 1), so the bound becomes
  -- ‖matrixLog d x - matrixLog d 1 - id (x - 1)‖ ≤ ‖x - 1‖.
  set diag : Matrix (Fin d) (Fin d) ℂ →
      Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ :=
    fun x => (x, (1 : Matrix (Fin d) (Fin d) ℂ)) with hdiag_def
  have h_cont_diag : Continuous diag := continuous_id.prodMk continuous_const
  have h_at_1 : diag 1 = ((1, 1) : Matrix (Fin d) (Fin d) ℂ × Matrix _ _ ℂ) := rfl
  have h_pullback : ∀ᶠ x in nhds (1 : Matrix (Fin d) (Fin d) ℂ),
      ‖matrixLog d x - matrixLog d 1 -
          (ContinuousLinearMap.id ℝ (Matrix (Fin d) (Fin d) ℂ)) (x - 1)‖ ≤
        1 * ‖x - 1‖ := by
    have h_pre :
        diag ⁻¹'
          {p : Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ |
            ‖matrixLog d p.1 - matrixLog d p.2 -
              (ContinuousLinearMap.id ℝ (Matrix (Fin d) (Fin d) ℂ)) (p.1 - p.2)‖ ≤
              1 * ‖p.1 - p.2‖} ∈ nhds (1 : Matrix (Fin d) (Fin d) ℂ) := by
      apply h_cont_diag.continuousAt.preimage_mem_nhds
      rw [h_at_1]; exact h_eventually
    exact h_pre
  -- Simplify: matrixLog d 1 = 0, id (x - 1) = x - 1, 1 * ‖x - 1‖ = ‖x - 1‖.
  have h_simp : ∀ᶠ x in nhds (1 : Matrix (Fin d) (Fin d) ℂ),
      ‖matrixLog d x - (x - 1)‖ ≤ ‖x - 1‖ := by
    filter_upwards [h_pullback] with x hx
    rw [matrixLog_one, sub_zero, one_mul] at hx
    exact hx
  -- Convert eventually to metric ball.
  obtain ⟨δ, hδ_pos, hδ_subset⟩ := Metric.mem_nhds_iff.mp h_simp
  refine ⟨δ, hδ_pos, fun h hh_dist => ?_⟩
  have h_in_ball : h ∈ Metric.ball (1 : Matrix (Fin d) (Fin d) ℂ) δ := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hh_dist
  have h_bound_at_h : ‖matrixLog d h - (h - 1)‖ ≤ ‖h - 1‖ := hδ_subset h_in_ball
  -- Triangle: ‖matrixLog d h‖ ≤ ‖matrixLog d h - (h - 1)‖ + ‖h - 1‖.
  have h_tri : ‖matrixLog d h‖ ≤ ‖matrixLog d h - (h - 1)‖ + ‖h - 1‖ := by
    calc ‖matrixLog d h‖
        = ‖(matrixLog d h - (h - 1)) + (h - 1)‖ := by rw [sub_add_cancel]
      _ ≤ ‖matrixLog d h - (h - 1)‖ + ‖h - 1‖ := norm_add_le _ _
  linarith

end SKEFTHawking.FKLW.GenericSUd
