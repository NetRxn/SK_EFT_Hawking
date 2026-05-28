/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Regime guards: H = (-i)·matrixLog Δ Hermitian-traceless on nhd 1

The valid-branch guards `H.IsHermitian ∧ H.trace = 0` (where
`H := (-i)·matrixLog (d) Δ`) of `dnStepFG_sud`, established on a
neighborhood of `1` from the matrixLog-in-`𝔰𝔲(d)` substrate
(`matrixLog_in_su_d_on_nhd_one`):

  * `matrixLog Δ` skew-Hermitian ⟹ `(-i)·matrixLog Δ` Hermitian
    (since `((-i)·Y)ᴴ = conj(-i)·Yᴴ = i·(-Y) = (-i)·Y`).
  * `matrixLog Δ` traceless ⟹ `(-i)·matrixLog Δ` traceless.

This is the Hermitian/traceless component of the `h_regime` hypothesis carried
by the (B) super-quad discharge (Session 102) and its headline cascade
(Session 103). The neighborhood is existential (the matrixLog is the IFT local
inverse); the per-alphabet headline composes this with the θ-bound (Session 60)
and the constructive ε-net to discharge `h_regime`.

## Substantive content shipped

  * `negI_matrixLog_isHermitian_traceless_on_nhd_one` — `∃ V ∈ nhds 1, ∀ Δ ∈ V ∩ SU(d) ∩ target,
    ((-i)·matrixLog Δ).IsHermitian ∧ ((-i)·matrixLog Δ).trace = 0`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — regime guards (Hermitian/
traceless component of the h_regime discharge).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixLogTraceless
import SKEFTHawking.FKLW.GenericSUdSuperQuadSubstrate

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **`(-i)·Y` is Hermitian when `Y` is skew-Hermitian**: `((-i)·Y)ᴴ = (-i)·Y`
since `((-i)·Y)ᴴ = conj(-i)·Yᴴ = i·(-Y) = (-i)·Y`. -/
lemma negI_smul_isHermitian_of_isSkewHermitian {d : ℕ}
    {Y : Matrix (Fin d) (Fin d) ℂ} (hY : Y.IsSkewHermitian) :
    (((-Complex.I) : ℂ) • Y).IsHermitian := by
  show (((-Complex.I) : ℂ) • Y).conjTranspose = ((-Complex.I) : ℂ) • Y
  rw [Matrix.conjTranspose_smul]
  have hYstar : Y.conjTranspose = -Y := hY
  rw [hYstar]
  rw [show (star ((-Complex.I) : ℂ)) = (Complex.I : ℂ) from by
    rw [star_neg, Complex.star_def, Complex.conj_I, neg_neg]]
  rw [smul_neg, neg_smul]

/-- **Regime guards on a neighborhood of 1**: for `Δ ∈ SU(d)` near `1` (and in
the matrixLog `target`), `H := (-i)·matrixLog d Δ` is Hermitian and traceless. -/
theorem negI_matrixLog_isHermitian_traceless_on_nhd_one (d : ℕ) [Nonempty (Fin d)]
    (hd_pos : 0 < d) :
    ∃ V ∈ nhds (1 : Matrix (Fin d) (Fin d) ℂ),
      ∀ h ∈ V, h ∈ Matrix.specialUnitaryGroup (Fin d) ℂ →
        h ∈ (expAmbientPartialHomeo d).target →
        (((-Complex.I) : ℂ) • matrixLog d h).IsHermitian ∧
        (((-Complex.I) : ℂ) • matrixLog d h).trace = 0 := by
  obtain ⟨V, hV_nhd, hV⟩ := matrixLog_in_su_d_on_nhd_one d hd_pos
  refine ⟨V, hV_nhd, ?_⟩
  intro h hh_V hh_su hh_target
  obtain ⟨h_skew, h_tr⟩ := hV h hh_V hh_su hh_target
  refine ⟨negI_smul_isHermitian_of_isSkewHermitian h_skew, ?_⟩
  rw [Matrix.trace_smul, h_tr, smul_zero]

/-- **Regime guards in residual form**: there is a radius `δ > 0` such that for
all `V, U ∈ SU(n+2)` with `‖V − U‖ < δ`, the residual generator
`H := (-i)·matrixLog (n+2) (V⁻¹·U)` is Hermitian and traceless.

Lifts `negI_matrixLog_isHermitian_traceless_on_nhd_one` (S104, in "Δ near 1"
form) to the residual `‖V − U‖` form used by the `h_regime` hypothesis, via the
residual bridge `‖Δ − 1‖ ≤ (n+2)·‖V − U‖` (Session 60) + extracting a ball from
the (nbhd-of-1) intersection of S104's neighborhood with the matrixLog `target`.
The radius `δ` is existential (the matrixLog is the IFT local inverse). -/
theorem negI_matrixLog_herm_traceless_on_residual_nhd (n : ℕ) :
    ∃ δ > (0 : ℝ), ∀ (V U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)),
      ‖(V : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
        (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ < δ →
      (((-Complex.I) : ℂ) • matrixLog (n + 2)
          (V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val).IsHermitian ∧
      (((-Complex.I) : ℂ) • matrixLog (n + 2)
          (V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val).trace = 0 := by
  obtain ⟨W, hW_nhd, hW⟩ :=
    negI_matrixLog_isHermitian_traceless_on_nhd_one (n + 2) (by omega)
  have h_inter : W ∩ (expAmbientPartialHomeo (n + 2)).target ∈
      nhds (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :=
    Filter.inter_mem hW_nhd (expAmbientPartialHomeo_target_mem_nhds_one (n + 2))
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.mem_nhds_iff.mp h_inter
  refine ⟨r / ((n : ℝ) + 2), by positivity, ?_⟩
  intro V U h_lt
  set Δ := (V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) with hΔ_def
  have h_res : ‖(Δ : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) - 1‖ ≤
      ((n : ℝ) + 2) * ‖(V : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
        (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ := by
    have h := residual_norm_le_d_mul V U
    rwa [show ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 from by push_cast; ring] at h
  have h_Δ_ball : (Δ : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) ∈
      Metric.ball (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖(Δ : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) - 1‖
        ≤ ((n : ℝ) + 2) * ‖(V : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
            (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ := h_res
      _ < ((n : ℝ) + 2) * (r / ((n : ℝ) + 2)) :=
          mul_lt_mul_of_pos_left h_lt (by positivity)
      _ = r := by field_simp
  have h_Δ_in := hr_subset h_Δ_ball
  exact hW Δ.val h_Δ_in.1 Δ.property h_Δ_in.2

end SKEFTHawking.FKLW.GenericSUd
