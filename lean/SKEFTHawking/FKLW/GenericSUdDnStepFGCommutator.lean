/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — dnStepFG_sud commutator identity + invalid-branch lemmas

Structural extraction lemmas for the SU(d) Dawson-Nielsen step
`dnStepFG_sud` (Session 41, re-wired in Session 82 to the bounded keystone),
mirroring the SU(2) `dnStepFG_su2_commutator_identity_valid` /
`dnStepFG_su2_invalid_F_zero`:

  * **Valid branch** (`0 < θ ≤ 1 ∧ H Hermitian ∧ H traceless`):
    `[F, G] = -matrixLog (n+2) Δ.val`  (the residual generator).
  * **Invalid branch**: `F = G = 0`.

These are the SU(d) analogs of the SU(2) structural extraction lemmas needed
by the super-quad main induction (the `exp(-[F,G]) = Δ` identity and the
error-accumulation telescoping). The commutator identity follows from the
bounded keystone's commutator conjunct
`F·G − G·F = -(θ·i)•H_unit` with `H_unit = (1/θ)•H`, `H = (-i)·matrixLog Δ`,
collapsing the scalar `-(θ·i)·(1/θ)·(-i) = -1` to give `-matrixLog Δ`.

## Substantive content shipped

  * `dnStepFG_sud_commutator_identity_valid` — `[F,G] = -matrixLog (n+2) Δ.val`.
  * `dnStepFG_sud_invalid_F_G_zero` — invalid branch gives `F = G = 0`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — dnStep structural
extraction (super-quad main induction substrate).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDnStepFG

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **dnStepFG_sud commutator identity (valid branch)**: for the valid
recursion regime, `[F, G] = -matrixLog (n+2) Δ.val`.

Mirrors SU(2)'s `dnStepFG_su2_commutator_identity_valid`. The bounded keystone
gives `F·G − G·F = -((θ:ℂ)·I) • ((1/θ)•H)` with `H = (-i)·matrixLog Δ`; the
scalar collapses: `-(θ·i)·(1/θ) = -i`, then `-i•((-i)•M) = (i²)•M = -M`. -/
lemma dnStepFG_sud_commutator_identity_valid {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    (h_valid : 0 < ‖((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ∧
        ‖((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 ∧
        (((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)).IsHermitian ∧
        (((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)).trace = 0) :
    (dnStepFG_sud V_n U).F * (dnStepFG_sud V_n U).G -
        (dnStepFG_sud V_n U).G * (dnStepFG_sud V_n U).F =
      -matrixLog (n + 2) (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val := by
  simp only [dnStepFG_sud]
  set Δ_local := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) with hΔ_def
  set H_local : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
    ((-Complex.I) : ℂ) • matrixLog (n + 2) Δ_local.val with hH_def
  set θ_local : ℝ := ‖H_local‖ with hθ_def
  rw [dif_pos h_valid]
  set ex_data := symmetric_balanced_commutator_hermitian_unconditional_bounded
      (((1 / θ_local : ℝ) : ℂ) • H_local)
      (IsHermitian_real_smul_sud h_valid.2.2.1 (1 / θ_local))
      (smul_trace_zero_sud h_valid.2.2.2 _)
      (normalize_smul_norm_le_one H_local h_valid.1)
      θ_local h_valid.1.le h_valid.2.1 with hex_def
  have h_comm_eq : ex_data.choose * ex_data.choose_spec.choose -
                   ex_data.choose_spec.choose * ex_data.choose =
                   -((θ_local : ℂ) * Complex.I) • (((1 / θ_local : ℝ) : ℂ) • H_local) :=
    ex_data.choose_spec.choose_spec.2.2.2.2.1
  have h_theta_pos : (0 : ℝ) < θ_local := h_valid.1
  have h_theta_ne : (θ_local : ℂ) ≠ 0 := by
    have : (θ_local : ℝ) ≠ 0 := ne_of_gt h_theta_pos
    exact_mod_cast this
  have h_scalar : -((θ_local : ℂ) * Complex.I) * (((1 / θ_local : ℝ) : ℂ)) =
                  -Complex.I := by
    have h_div : ((1 / θ_local : ℝ) : ℂ) = ((θ_local : ℂ))⁻¹ := by
      push_cast
      rw [one_div]
    rw [h_div]
    field_simp
  rw [h_comm_eq, smul_smul, h_scalar]
  show -Complex.I • ((-Complex.I : ℂ) • matrixLog (n + 2) Δ_local.val) =
    -matrixLog (n + 2) Δ_local.val
  rw [smul_smul]
  ring_nf
  simp [Complex.I_sq]

/-- **dnStepFG_sud invalid branch gives F = G = 0**: outside the valid
recursion regime, the SU(d) step falls back to `(0, 0)`. Mirrors SU(2)'s
`dnStepFG_su2_invalid_F_zero`. -/
lemma dnStepFG_sud_invalid_F_G_zero {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    (h_invalid : ¬(0 < ‖((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ∧
        ‖((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 ∧
        (((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)).IsHermitian ∧
        (((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)).trace = 0)) :
    (dnStepFG_sud V_n U).F = 0 ∧ (dnStepFG_sud V_n U).G = 0 := by
  simp only [dnStepFG_sud]
  rw [dif_neg h_invalid]
  exact ⟨rfl, rfl⟩

end SKEFTHawking.FKLW.GenericSUd
