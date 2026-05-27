/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.1 PROPER — `trappedIonGeneratingSetSU4` (full, MS-included)

The full SU(4) trapped-ion alphabet, parameterized by an MS-grid
resolution `N : ℕ` (with `0 < N`):

  * 4 single-qubit gates: `{H_SU on ion 1, T_SU on ion 1, H_SU on ion 2, T_SU on ion 2}`
  * `2 N` Mølmer-Sørensen entangling gates: `MS(k·π/N)` for `k ∈ {0, …, 2N-1}`

Total: `4 + 2 N` generators. Word type `FreeGroup (Fin (4 + 2*N))`.

This is the **substantive T-A1′.1 PROPER ship** that the prior partial
ship (`trappedIonGeneratingSetSU4_1Q`, 1Q-only sub-alphabet) deferred.
Closure-density for the full alphabet at SU(4) ships in T-A1′.2 via
Phase 6y S.2g (Cartan v4 at SU(d=4)).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.1 PROPER (full
alphabet with MS at rational-π/N grid).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdGeneratingSet
import SKEFTHawking.FKLW.TrappedIonSU4Substrate
import SKEFTHawking.FKLW.MSGateExpForm

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The `(4 + 2*N)`-element generator-token map

Tokens `0,1,2,3` ↦ packaged single-qubit gates `{H_1, T_1, H_2, T_2}`.
Tokens `4, …, 4 + 2N − 1` ↦ `MS(k·π/N)` for `k = 0, …, 2N − 1`. -/

/-- The full trapped-ion 4 + 2N-element generator map at grid
resolution `N` (with `0 < N`).

Indices 0-3 are the 1Q gates; indices 4 to (4 + 2N − 1) are the MS
gates parameterized by `θ_k := k·π/N` for `k = 0, …, 2N−1`. -/
noncomputable def trappedIonGenMap_full (N : ℕ) (_hN : 0 < N) :
    Fin (4 + 2 * N) → ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ) := fun i =>
  if i.val = 0 then H_SU_on_ion1_SU4
  else if i.val = 1 then T_SU_on_ion1_SU4
  else if i.val = 2 then H_SU_on_ion2_SU4
  else if i.val = 3 then T_SU_on_ion2_SU4
  else
    -- i.val ≥ 4; map to MS(k·π/N) with k := i.val - 4.
    MSGate_SU4 (((i.val - 4 : ℕ) : ℝ) * Real.pi / (N : ℝ))

/-- The full trapped-ion representation: `FreeGroup (Fin (4 + 2*N)) →* ↥SU(4)`
lifted from `trappedIonGenMap_full`. -/
noncomputable def trappedIonRho_full (N : ℕ) (hN : 0 < N) :
    FreeGroup (Fin (4 + 2 * N)) →*
      ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ) :=
  FreeGroup.lift (trappedIonGenMap_full N hN)

/-! ## 2. The finite generator Finset -/

/-- The `(4 + 2*N)` free-group generators as a Finset. -/
noncomputable def trappedIonGens_full (N : ℕ) :
    Finset (FreeGroup (Fin (4 + 2 * N))) :=
  (Finset.univ : Finset (Fin (4 + 2 * N))).image FreeGroup.of

theorem trappedIonGens_full_nonempty (N : ℕ) (hN : 0 < N) :
    (trappedIonGens_full N).Nonempty := by
  unfold trappedIonGens_full
  -- 4 + 2N > 0 since 4 > 0 (regardless of N).
  have h_pos : 0 < 4 + 2 * N := by omega
  refine ⟨FreeGroup.of ⟨0, h_pos⟩, ?_⟩
  rw [Finset.mem_image]
  exact ⟨⟨0, h_pos⟩, Finset.mem_univ _, rfl⟩

theorem trappedIonGens_full_generate (N : ℕ) :
    Subgroup.closure ((trappedIonGens_full N) :
        Set (FreeGroup (Fin (4 + 2 * N)))) =
      (⊤ : Subgroup (FreeGroup (Fin (4 + 2 * N)))) := by
  unfold trappedIonGens_full
  -- trappedIonGens_full N as Set = Set.range FreeGroup.of
  have h_eq : (((Finset.univ : Finset (Fin (4 + 2 * N))).image FreeGroup.of :
                Finset (FreeGroup (Fin (4 + 2 * N)))) :
                Set (FreeGroup (Fin (4 + 2 * N)))) =
              Set.range (FreeGroup.of :
                Fin (4 + 2 * N) → FreeGroup (Fin (4 + 2 * N))) := by
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [h_eq]
  exact FreeGroup.closure_range_of _

/-! ## 3. The full trapped-ion `GeneratingSet 4` instance (with MS) -/

/-- **Full trapped-ion `GeneratingSet 4` with MS at rational-π/N grid**
(substantive T-A1′.1 PROPER ship).

Alphabet:
  * 4 single-qubit gates `{H_1, T_1, H_2, T_2}` (per Phase 6y T-A1′.1
    substrate `kronSU4_mem_specialUnitaryGroup`).
  * 2N Mølmer-Sørensen entangling gates `MS(k·π/N)` for k = 0, …, 2N-1
    (per Phase 6y T-A1′.1 `MSGateExp_mem_specialUnitaryGroup` via
    skew-Hermitian-exp-is-unitary + Jacobi formula).

Word type `FreeGroup (Fin (4 + 2*N))`. -/
noncomputable def trappedIonGeneratingSetSU4 (N : ℕ) (hN : 0 < N) :
    SKEFTHawking.FKLW.GenericSUd.GeneratingSet 4 where
  W := FreeGroup (Fin (4 + 2 * N))
  Wgroup := inferInstance
  ρ_hom := trappedIonRho_full N hN
  gens := trappedIonGens_full N
  gens_nonempty := trappedIonGens_full_nonempty N hN
  gens_generate := trappedIonGens_full_generate N

/-- The full trapped-ion alphabet at grid resolution N has carrier word
type `FreeGroup (Fin (4 + 2*N))`. -/
@[simp]
theorem trappedIonGeneratingSetSU4_W (N : ℕ) (hN : 0 < N) :
    (trappedIonGeneratingSetSU4 N hN).W = FreeGroup (Fin (4 + 2 * N)) := rfl

end SKEFTHawking.FKLW.TrappedIonSU4
