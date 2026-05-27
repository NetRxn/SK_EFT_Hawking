/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.4 — Matrix log Lipschitz-style bound (d-generic, local)

For the IFT-derived matrix log `matrixLog d` (Phase 6y S.2b), this
module ships a Lipschitz-style locally-bounded property:

  * For any `ε > 0`, there exists `δ > 0` such that
    `‖h - 1‖ < δ ⟹ ‖matrixLog d h‖ < ε`.

This is the **continuity restatement** in the (h - 1) → 0 sense,
useful for Phase 6y consumers needing matrix-log smallness bounds.

The Phase 6u SU(2) version `Y_h_norm_le_four_norm_sub_one` ships an
explicit Lipschitz constant `K = 4` for SU(2); the d-generic analog
here ships the existential Lipschitz form, with the explicit
d-dependent constant a follow-up via the IFT-derived `matrixLog`'s
differentiability at `1` (`D matrixLog (1) = identity`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.4 (Y_h Lipschitz).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo
import SKEFTHawking.FKLW.GenericSUdMatrixLogSkewHerm

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. matrixLog continuity at 1, in (h - 1) → 0 form

Restates the continuity of matrixLog d at 1 as: for any ε > 0, there
exists δ > 0 such that ‖h - 1‖ < δ AND h ∈ target ⟹ ‖matrixLog d h‖ < ε. -/

/-- **Matrix log smallness on a nbhd of 1** (Lipschitz-style local form). -/
theorem matrixLog_smallness_on_nhd_one (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : Matrix (Fin d) (Fin d) ℂ,
      ‖h - 1‖ < δ → h ∈ (expAmbientPartialHomeo d).target →
      ‖matrixLog d h‖ < ε := by
  -- matrixLog d is continuous at 1, with value matrixLog d 1 = 0.
  have h_cont : ContinuousAt (matrixLog d) 1 := matrixLog_continuousAt_one d
  have h_lim : Tendsto (matrixLog d) (nhds 1) (nhds 0) := by
    rw [← matrixLog_one d]; exact h_cont
  -- ‖matrixLog d h‖ → ‖0‖ = 0 as h → 1.
  have h_norm_lim : Tendsto (fun h => ‖matrixLog d h‖) (nhds 1) (nhds 0) := by
    have := (continuous_norm.continuousAt
      (x := (0 : Matrix (Fin d) (Fin d) ℂ))).tendsto.comp h_lim
    rwa [norm_zero] at this
  -- Extract the δ via metric tendsto characterization.
  have h_ev : ∀ᶠ h in nhds (1 : Matrix (Fin d) (Fin d) ℂ),
      ‖matrixLog d h‖ < ε := by
    have h_open_ball := h_norm_lim (Metric.ball_mem_nhds (0 : ℝ) hε)
    filter_upwards [h_open_ball] with h hh
    -- hh : ‖matrixLog d h‖ ∈ Metric.ball (0 : ℝ) ε
    simpa [Real.norm_eq_abs] using hh
  -- Convert eventually-in-nhds-1 to a metric ball.
  obtain ⟨δ, hδ_pos, hδ_subset⟩ := Metric.mem_nhds_iff.mp h_ev
  refine ⟨δ, hδ_pos, fun h hh_dist _ => ?_⟩
  apply hδ_subset
  rwa [Metric.mem_ball, dist_eq_norm]

end SKEFTHawking.FKLW.GenericSUd
