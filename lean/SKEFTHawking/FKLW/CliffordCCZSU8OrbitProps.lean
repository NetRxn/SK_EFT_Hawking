/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4h.2 — the Clifford orbit elements are 𝔰𝔲(8) tangents with flows

Each element `M = R·X₀·R⁻¹` of the Clifford orbit (`cliffOrbitSet X₀`, `R ∈ H_of_G`) inherits the three
`ClosureDenseWitness` properties from the seed tangent `X₀`:

  * **skew-Hermitian** (`cliffOrbit_mem_skew`): `R` is unitary (`R⁻¹ = R†`), so `(R·X₀·R⁻¹)† =
    R·X₀†·R⁻¹ = -(R·X₀·R⁻¹)`.
  * **traceless** (`cliffOrbit_mem_trace`): `tr(R·X₀·R⁻¹) = tr(R⁻¹·R·X₀) = tr X₀ = 0` (trace cyclicity).
  * **flow line in `H_of_G`** (`cliffOrbit_mem_flow`): directly `flow_conj_mem` — `exp(t·(R·X₀·R⁻¹)) =
    R·exp(t·X₀)·R⁻¹ ∈ H_of_G`.

Together with `cliffOrbit_spans_su8` (the orbit spans 𝔰𝔲(8)) these are the `hX_in_sud` + `hX_flow`
ingredients of the witness.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4h.2 (Clifford orbit element properties). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8OrbitWitness
import SKEFTHawking.FKLW.GenericSUdFlowConj

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.GenericSUd

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- For `R ∈ SU(8)` the matrix inverse is the conjugate transpose: `R⁻¹ = R†`. -/
theorem su8_val_inv_eq_star (R : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
    (R.val)⁻¹ = star R.val := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.star_eq_conjTranspose]
  exact (Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp R.2).1)

/-- Every Clifford orbit element is skew-Hermitian (unitary conjugation preserves skew-Hermitian). -/
theorem cliffOrbit_mem_skew (X0 : Matrix (Fin 8) (Fin 8) ℂ) (hX0 : X0.IsSkewHermitian)
    (M : Matrix (Fin 8) (Fin 8) ℂ) (hM : M ∈ cliffOrbitSet X0) : M.IsSkewHermitian := by
  obtain ⟨R, hR, rfl⟩ := hM
  show (R.val * X0 * (R.val)⁻¹)ᴴ = -(R.val * X0 * (R.val)⁻¹)
  rw [su8_val_inv_eq_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX0]
  noncomm_ring

/-- Every Clifford orbit element is traceless (trace cyclicity). -/
theorem cliffOrbit_mem_trace (X0 : Matrix (Fin 8) (Fin 8) ℂ) (hX0 : X0.trace = 0)
    (M : Matrix (Fin 8) (Fin 8) ℂ) (hM : M ∈ cliffOrbitSet X0) : M.trace = 0 := by
  obtain ⟨R, hR, rfl⟩ := hM
  have hRinv : (R.val)⁻¹ * R.val = 1 := by
    rw [su8_val_inv_eq_star]
    exact (Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp R.2).1)
  rw [Matrix.trace_mul_cycle, hRinv, Matrix.one_mul, hX0]

/-- Every Clifford orbit element carries a one-parameter flow line in `H_of_G` (transported from the seed
flow by `flow_conj_mem`). -/
theorem cliffOrbit_mem_flow (X0 : Matrix (Fin 8) (Fin 8) ℂ)
    (hflow : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ Hlit ∧ (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • X0))
    (M : Matrix (Fin 8) (Fin 8) ℂ) (hM : M ∈ cliffOrbitSet X0) :
    ∀ t : ℝ, ∃ M' : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M' ∈ Hlit ∧ (M' : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • M) := by
  obtain ⟨R, hR, rfl⟩ := hM
  intro t
  exact flow_conj_mem Hlit R hR hflow t

end SKEFTHawking.FKLW.CliffordCCZSU8
