/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — log-agnostic dnStep F/G-norm bound (re-point R4)

The F/G-norm bound `‖F‖, ‖G‖ ≤ K_F·√(θ/2)` (with `K_F = (n+2)²·(n+1)·√(n+2)`,
`θ = ‖H‖`) is, like the commutator identity (S129), **log-agnostic**: it is the
bounded keystone's norm conjunct extracted at the DN-step level, and depends only on the
generator `H = (-i)·M` through `θ = ‖H‖` — not on *which* matrix `M` plays the role of the
residual log. This module lifts `dnStepFG_sud_F_norm_le` / `dnStepFG_sud_G_norm_le` (S85)
to the log-agnostic `dnStepFG_fromLog` (S129), so the concrete re-pointed step
(`dnStepFG_sud_concrete`, S130) inherits the same norm bound on the named calibration ball
via the concrete-radius `‖matrixMercatorLog (Δ−1)‖ ≤ 2‖Δ−1‖` (S109) — without re-deriving
the keystone extraction.

## Substantive content shipped

  * `dnStepFG_fromLog_F_norm_le` / `dnStepFG_fromLog_G_norm_le` — `‖F‖, ‖G‖ ≤ K_F·√(θ/2)`
    for `dnStepFG_fromLog M`, generic in `M` (`θ = ‖(-i)·M‖`).
  * `dnStepFG_sud_concrete_F_norm_le` / `dnStepFG_sud_concrete_G_norm_le` — the concrete
    re-pointed instantiation at `M = matrixMercatorLog ((V_n⁻¹U).val − 1)`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R4: log-agnostic F/G-norm bound
(super-quad bound F/G-norm ingredient, re-pointed).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDnStepFGFromLog
import SKEFTHawking.FKLW.GenericSUdDnStepFGConcrete
import SKEFTHawking.FKLW.GenericSUdDnStepFGNormBound

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **`dnStepFG_fromLog` F-norm bound** (log-agnostic): `‖(dnStepFG_fromLog M).F‖ ≤
K_F·√(θ/2)` with `K_F = (n+2)²·(n+1)·√(n+2)` (= `dnStepFG_sud_K_F n`) and `θ = ‖(-i)·M‖`.
Log-agnostic generalization of `dnStepFG_sud_F_norm_le` (S85): the valid branch extracts the
bounded keystone's norm conjunct (`choose_spec`), the else branch is `‖0‖ = 0`. -/
lemma dnStepFG_fromLog_F_norm_le {n : ℕ} (M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    ‖(dnStepFG_fromLog M).F‖ ≤ dnStepFG_sud_K_F n *
      Real.sqrt (‖((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ / 2) := by
  simp only [dnStepFG_fromLog, dnStepFG_sud_K_F]
  split_ifs with h_valid
  · set H_local : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ := ((-Complex.I) : ℂ) • M with hH
    set θ_local : ℝ := ‖H_local‖ with hθ
    have h_ex_spec := (symmetric_balanced_commutator_hermitian_unconditional_bounded
        (((1 / θ_local : ℝ) : ℂ) • H_local)
        (IsHermitian_real_smul_sud h_valid.2.2.1 (1 / θ_local))
        (smul_trace_zero_sud h_valid.2.2.2 _)
        (le_of_eq (by
          rw [norm_smul, Complex.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / θ_local), one_div]
          exact inv_mul_cancel₀ (ne_of_gt h_valid.1)))
        θ_local h_valid.1.le h_valid.2.1).choose_spec.choose_spec
    exact h_ex_spec.2.2.2.2.2.1
  · show ‖(0 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ _
    rw [norm_zero]
    positivity

/-- **`dnStepFG_fromLog` G-norm bound** (log-agnostic, mirror of F). -/
lemma dnStepFG_fromLog_G_norm_le {n : ℕ} (M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    ‖(dnStepFG_fromLog M).G‖ ≤ dnStepFG_sud_K_F n *
      Real.sqrt (‖((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ / 2) := by
  simp only [dnStepFG_fromLog, dnStepFG_sud_K_F]
  split_ifs with h_valid
  · set H_local : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ := ((-Complex.I) : ℂ) • M with hH
    set θ_local : ℝ := ‖H_local‖ with hθ
    have h_ex_spec := (symmetric_balanced_commutator_hermitian_unconditional_bounded
        (((1 / θ_local : ℝ) : ℂ) • H_local)
        (IsHermitian_real_smul_sud h_valid.2.2.1 (1 / θ_local))
        (smul_trace_zero_sud h_valid.2.2.2 _)
        (le_of_eq (by
          rw [norm_smul, Complex.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / θ_local), one_div]
          exact inv_mul_cancel₀ (ne_of_gt h_valid.1)))
        θ_local h_valid.1.le h_valid.2.1).choose_spec.choose_spec
    exact h_ex_spec.2.2.2.2.2.2
  · show ‖(0 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ _
    rw [norm_zero]
    positivity

/-- **Concrete DN step F-norm bound**: `‖(dnStepFG_sud_concrete V_n U).F‖ ≤ K_F·√(θ/2)`
with `θ = ‖(-i)·matrixMercatorLog ((V_n⁻¹U).val − 1)‖`. The re-pointed instantiation of
`dnStepFG_fromLog_F_norm_le` at the concrete log — the F/G-norm ingredient of the concrete
super-quad bound. -/
lemma dnStepFG_sud_concrete_F_norm_le {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    ‖(dnStepFG_sud_concrete V_n U).F‖ ≤ dnStepFG_sud_K_F n *
      Real.sqrt (‖((-Complex.I) • matrixMercatorLog
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ / 2) :=
  dnStepFG_fromLog_F_norm_le _

/-- **Concrete DN step G-norm bound** (mirror of F). -/
lemma dnStepFG_sud_concrete_G_norm_le {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    ‖(dnStepFG_sud_concrete V_n U).G‖ ≤ dnStepFG_sud_K_F n *
      Real.sqrt (‖((-Complex.I) • matrixMercatorLog
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ / 2) :=
  dnStepFG_fromLog_G_norm_le _

end SKEFTHawking.FKLW.GenericSUd
