/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness — the MS gate IS the `X₁₁` entangler flow (grid points)

The entangling tangent of the SU(4) `ClosureDenseWitness` is `X₁₁ = (i/2)·(σ_x ⊗ σ_x)`
(`suFourTangentAux 1 1`). This module proves the **bridge identity**

  `MSGate_SU4 θ = exp((-θ) • X₁₁)`     (i.e. `msGenerator θ = (-θ) • X₁₁`)

so the alphabet's Mølmer-Sørensen generators are exactly the `X₁₁` one-parameter subgroup
**sampled at the rational grid** `θ ∈ {k·π/N : k}`, and those grid points lie in
`H_of_G (trappedIonGeneratingSetSU4 N hN)` (they are images of the alphabet tokens).

## The honest scope marker (D2 frontier)

This is the substrate, **not** the full `hX_flow` for `X₁₁`. The witness needs
`exp(t • X₁₁) ∈ H_of_G` for *all* `t ∈ ℝ`; this module supplies it only for the rational grid
`t = -k·π/N`. Since `σ_x ⊗ σ_x` has eigenvalues `±1`, `exp(t • X₁₁)` has period `4π`, so the
grid points `MS(k π/N) = MS(π/N)^k` form a *finite* cyclic subgroup of the flow circle — the
continuous flow does **not** follow from elementary closure of the grid. Completing `X₁₁`'s
continuous flow is the genuine Brylinski-Brylinski universality content (discrete entangler +
dense per-ion `SU(2)×SU(2)` ⇒ dense in `SU(4)`), the remaining research-grade crux of Track
T-A1′.2. Once it lands, the 8 other entangling flows follow by `GenericSUd.flow_conj_mem`
(per-ion conjugation), and the 6 per-ion flows are already shipped.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness MS↔X₁₁ bridge +
grid-point flow membership. 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4Tangents
import SKEFTHawking.FKLW.MSGateExpForm
import SKEFTHawking.FKLW.TrappedIonGeneratingSetSU4Full

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix Complex SKEFTHawking.FKLW.GenericSUd

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The MS generator is the `X₁₁` tangent rescaled -/

/-- **Bridge identity**: `msGenerator θ = (-θ) • X₁₁`, where `X₁₁ = suFourTangentAux 1 1`. -/
theorem msGenerator_eq_smul_suFourTangent (θ : ℝ) :
    msGenerator θ = ((-θ : ℝ) : ℂ) • suFourTangentAux 1 1 := by
  unfold msGenerator suFourTangentAux
  show (-(Complex.I * (θ : ℂ) / 2)) • xKronX
      = ((-θ : ℝ) : ℂ) • ((Complex.I / 2) • kronSU4 (pauli4 1) (pauli4 1))
  rw [smul_smul]
  show (-(Complex.I * (θ : ℂ) / 2)) • xKronX
      = (((-θ : ℝ) : ℂ) * (Complex.I / 2)) • kronSU4 (pauli4 1) (pauli4 1)
  rw [show kronSU4 (pauli4 1) (pauli4 1) = xKronX from rfl]
  congr 1
  push_cast; ring

/-- **MS gate as the `X₁₁` flow**: `(MSGate_SU4 θ).val = exp((-θ) • X₁₁)`. -/
theorem MSGate_SU4_eq_exp_smul_suFourTangent (θ : ℝ) :
    (MSGate_SU4 θ : Matrix (Fin 4) (Fin 4) ℂ) =
      NormedSpace.exp (((-θ : ℝ) : ℂ) • suFourTangentAux 1 1) := by
  show MSGateExp θ = _
  unfold MSGateExp
  rw [msGenerator_eq_smul_suFourTangent]

/-! ## 2. The grid points of the `X₁₁` flow lie in `H_of_G` -/

/-- **MS grid flow membership**: for `k < 2N`, the flow point `exp((-(k·π/N)) • X₁₁) = MS(kπ/N)`
is the image of the alphabet token `4 + k`, hence lies in `H_of_G (trappedIonGeneratingSetSU4 N hN)`. -/
theorem MSGate_grid_mem_H_of_G (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : k < 2 * N) :
    MSGate_SU4 ((k : ℝ) * Real.pi / (N : ℝ)) ∈
      H_of_G (trappedIonGeneratingSetSU4 N hN) := by
  -- The token `⟨4 + k, _⟩` maps to `MSGate_SU4 (k·π/N)` under the generator map.
  have hidx : (4 + k) < 4 + 2 * N := by omega
  have h_gen : trappedIonRho_full N hN (FreeGroup.of ⟨4 + k, hidx⟩) =
      MSGate_SU4 ((k : ℝ) * Real.pi / (N : ℝ)) := by
    rw [trappedIonRho_full, FreeGroup.lift_apply_of]
    show trappedIonGenMap_full N hN ⟨4 + k, hidx⟩ = MSGate_SU4 ((k : ℝ) * Real.pi / (N : ℝ))
    unfold trappedIonGenMap_full
    have hval : (⟨4 + k, hidx⟩ : Fin (4 + 2 * N)).val = 4 + k := rfl
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show (⟨4 + k, hidx⟩ : Fin (4 + 2 * N)).val - 4 = k from by omega]
  -- It is `ρ_hom (of ⟨4+k, _⟩) ∈ range ρ_hom ⊆ topologicalClosure = H_of_G`.
  have h_mem : MSGate_SU4 ((k : ℝ) * Real.pi / (N : ℝ)) ∈
      (trappedIonGeneratingSetSU4 N hN).ρ_hom.range :=
    MonoidHom.mem_range.mpr ⟨FreeGroup.of ⟨4 + k, hidx⟩, h_gen⟩
  exact Subgroup.le_topologicalClosure _ h_mem

end SKEFTHawking.FKLW.TrappedIonSU4
