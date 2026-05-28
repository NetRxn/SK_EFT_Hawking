/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y (D) witness substrate — conjugation transports tangent flow lines

A `ClosureDenseWitness` flow line `∀ t, exp(t • X) ∈ H` can be **transported by conjugation**:
for any `R ∈ H`, the conjugated tangent `R·X·R⁻¹` also has its flow line in `H`, because

  `exp(t • (R·X·R⁻¹)) = R · exp(t • X) · R⁻¹`  (`Matrix.exp_conj`, unitaries are units)

and `H` is closed under multiplication and inversion. This is the **structural action** that lets
the per-ion-conjugated entangling directions inherit flow lines from a single entangling-direction
flow line — replacing the (much heavier) Trotter bracket-generation route of the DR blueprint §3.1
for the trapped-ion SU(4) witness: every `(σ_a ⊗ σ_b)` direction is a per-ion `SU(2)×SU(2)`
conjugate of `(σ_x ⊗ σ_x)`, and `SU(2)×SU(2) ⊆ H` already (per-ion containment).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ / T-A2′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness flow transport.
DR blueprint §5.3 L_8-4 (conjugation closure). Generic in `d` (reused by SU(4) and SU(8)).
2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Conjugation transports a flow line**. If `R ∈ H` and the tangent `X` has its
one-parameter subgroup `exp(t • X)` in `H` for all `t`, then the conjugated tangent
`R.val · X · R.val⁻¹` also has its one-parameter subgroup in `H` for all `t`. -/
theorem flow_conj_mem {d : ℕ}
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (R : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) (hR : R ∈ H)
    {X : Matrix (Fin d) (Fin d) ℂ}
    (hflow : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
        M ∈ H ∧ (M : Matrix (Fin d) (Fin d) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • X))
    (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
      M ∈ H ∧ (M : Matrix (Fin d) (Fin d) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) •
          ((R : Matrix (Fin d) (Fin d) ℂ) * X * (R : Matrix (Fin d) (Fin d) ℂ)⁻¹)) := by
  obtain ⟨M, hM_mem, hM_val⟩ := hflow t
  refine ⟨R * M * R⁻¹, H.mul_mem (H.mul_mem hR hM_mem) (H.inv_mem hR), ?_⟩
  have hRinv : (R⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val =
      ((R : Matrix (Fin d) (Fin d) ℂ))⁻¹ := by
    have hmul : (R : Matrix (Fin d) (Fin d) ℂ) *
        (R⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val = 1 := by
      rw [show (R : Matrix (Fin d) (Fin d) ℂ) *
            (R⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val
          = (R * R⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val from rfl,
        mul_inv_cancel]
      rfl
    exact (Matrix.inv_eq_right_inv hmul).symm
  have hRunit : IsUnit (R : Matrix (Fin d) (Fin d) ℂ) := by
    rw [Matrix.isUnit_iff_isUnit_det, (Matrix.mem_specialUnitaryGroup_iff.mp R.property).2]
    exact isUnit_one
  show (R : Matrix (Fin d) (Fin d) ℂ) * (M : Matrix (Fin d) (Fin d) ℂ) *
      (R⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val = _
  rw [hM_val, hRinv, ← Matrix.exp_conj (R : Matrix (Fin d) (Fin d) ℂ) (((t : ℝ) : ℂ) • X) hRunit]
  congr 1
  rw [mul_smul_comm, smul_mul_assoc]

end SKEFTHawking.FKLW.GenericSUd
