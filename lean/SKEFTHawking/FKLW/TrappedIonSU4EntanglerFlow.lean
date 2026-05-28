/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness — the first entangling tangent flow `exp(t·X₂₁) ∈ H_of_G`

Composes the entangler conjugation identity `MS(π/2)·X₃₀·MS(π/2)⁻¹ = −X₂₁` with the shipped
per-ion `X₃₀` flow (D1) and the generic `flow_conj_mem`: conjugating the `X₃₀` one-parameter
subgroup by `MS(π/2) ∈ H_of_G` (a grid generator at even `N`, `k = N/2`) yields the continuous
flow `exp(t · X₂₁) ∈ H_of_G`. This is the first of the 9 entangling directions; the remaining 8
follow by per-ion Clifford conjugation of this one.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness first entangling
flow. 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4EntanglerConj
import SKEFTHawking.FKLW.GenericSUdFlowConj

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix Complex SKEFTHawking.FKLW.GenericSUd

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- For even `N`, the maximally-entangling `MS(π/2)` is a grid generator, hence in `H_of_G`. -/
theorem MS_halfPi_mem (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) :
    MSGate_SU4 (Real.pi / 2) ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) := by
  obtain ⟨m, hm⟩ := hN2
  have hm_pos : 0 < m := by omega
  have hk : m < 2 * N := by omega
  have h := MSGate_grid_mem_H_of_G N hN m hk
  rwa [show ((m : ℝ) * Real.pi / (N : ℝ)) = Real.pi / 2 by
    rw [hm]; push_cast; field_simp] at h

/-- **First entangling flow**: for even `N`, `exp(t · X₂₁) ∈ H_of_G` for all `t`. -/
theorem suFourTangentAux_X21_flow (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ),
      M ∈ H_of_G (trappedIonGeneratingSetSU4 N hN) ∧
      (M : Matrix (Fin 4) (Fin 4) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • suFourTangentAux 2 1) := by
  obtain ⟨M, hM_mem, hM_val⟩ :=
    flow_conj_mem (H_of_G (trappedIonGeneratingSetSU4 N hN)) (MSGate_SU4 (Real.pi / 2))
      (MS_halfPi_mem N hN hN2)
      (suFourTangentAux_ion1_flow N hN 3 (by decide)) (-t)
  refine ⟨M, hM_mem, ?_⟩
  rw [hM_val, MS_conj_X30]
  congr 1
  rw [Complex.ofReal_neg, neg_smul, smul_neg]
  exact neg_neg _

end SKEFTHawking.FKLW.TrappedIonSU4
