/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — dnStepFG_sud F/G-norm bound discharge

Now that `dnStepFG_sud` (Session 41, re-wired in Session 82) extracts its
(F, G) from the BOUNDED keystone
`symmetric_balanced_commutator_hermitian_unconditional_bounded` (Session 81),
the chosen witnesses carry the concrete linftyOp norm bound. This module
extracts that bound at the `dnStep` level and discharges the F/G-norm
predicates:

  `‖(dnStepFG_sud V_n U).F‖ ≤ K_F · √(θ/2)`  with  `K_F = (n+2)²·(n+1)·√(n+2)`

(and mirror for G), where `θ = ‖(-i)·matrixLog (V_n⁻¹·U)‖`.

This discharges `DnStepFG_sud_F_norm_bound_predicate` and
`DnStepFG_sud_G_norm_bound_predicate` (Session 67) at the concrete
`K_F = (n+2)²·(n+1)·√(n+2)` — the SU(d) analog of the SU(2) implicit
`‖F‖ ≤ √(θ/2)` (`dnStepFG_su2_F_norm_le_sqrt_theta_half`). This is the
super-quad bound's F/G-norm ingredient.

## Substantive content shipped

  * `dnStepFG_sud_F_norm_le` / `dnStepFG_sud_G_norm_le` — the dnStep-level
    norm bound (valid branch via the bounded keystone's choose-spec, else
    branch via `‖0‖ = 0`).
  * `dnStepFG_sud_F_norm_bound_holds` / `dnStepFG_sud_G_norm_bound_holds` —
    discharge of the F/G-norm predicates at `K_F = (n+2)²·(n+1)·√(n+2)`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — dnStep-level F/G-norm
bound discharge (super-quad bound F/G-norm ingredient).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDnStepFG
import SKEFTHawking.FKLW.GenericSUdSuperQuadSubstrate

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- The concrete F/G-norm constant `K_F = (n+2)²·(n+1)·√(n+2)`. -/
noncomputable def dnStepFG_sud_K_F (n : ℕ) : ℝ :=
  ((n + 2 : ℕ) : ℝ)^2 * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2))

/-- **dnStepFG_sud F-norm bound**: `‖(dnStepFG_sud V_n U).F‖ ≤ K_F·√(θ/2)`
where `K_F = (n+2)²·(n+1)·√(n+2)` and `θ = ‖(-i)·matrixLog (V_n⁻¹·U)‖`.

Valid branch: the bounded keystone (Session 81) constrains the chosen F's
norm; extract via `choose_spec`. Else branch: `F = 0`, so `‖0‖ = 0 ≤ K_F·√(θ/2)`. -/
lemma dnStepFG_sud_F_norm_le {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    let Δ := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    let H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
      ((-Complex.I) : ℂ) • matrixLog (n + 2) Δ.val
    let θ : ℝ := ‖H‖
    ‖(dnStepFG_sud V_n U).F‖ ≤ dnStepFG_sud_K_F n * Real.sqrt (θ / 2) := by
  simp only [dnStepFG_sud, dnStepFG_sud_K_F]
  split_ifs with h_valid
  · set H_local : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
      ((-Complex.I) : ℂ) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val with hH
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

/-- **dnStepFG_sud G-norm bound** (mirror of F-norm). -/
lemma dnStepFG_sud_G_norm_le {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    let Δ := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    let H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
      ((-Complex.I) : ℂ) • matrixLog (n + 2) Δ.val
    let θ : ℝ := ‖H‖
    ‖(dnStepFG_sud V_n U).G‖ ≤ dnStepFG_sud_K_F n * Real.sqrt (θ / 2) := by
  simp only [dnStepFG_sud, dnStepFG_sud_K_F]
  split_ifs with h_valid
  · set H_local : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
      ((-Complex.I) : ℂ) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val with hH
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

/-- **F-norm predicate discharge** at `K_F = (n+2)²·(n+1)·√(n+2)`. -/
theorem dnStepFG_sud_F_norm_bound_holds {n : ℕ} :
    DnStepFG_sud_F_norm_bound_predicate (n := n) (dnStepFG_sud_K_F n) := by
  intro V_n U Δ H θ _h_guard
  exact dnStepFG_sud_F_norm_le V_n U

/-- **G-norm predicate discharge** at `K_F = (n+2)²·(n+1)·√(n+2)`. -/
theorem dnStepFG_sud_G_norm_bound_holds {n : ℕ} :
    DnStepFG_sud_G_norm_bound_predicate (n := n) (dnStepFG_sud_K_F n) := by
  intro V_n U Δ H θ _h_guard
  exact dnStepFG_sud_G_norm_le V_n U

end SKEFTHawking.FKLW.GenericSUd
