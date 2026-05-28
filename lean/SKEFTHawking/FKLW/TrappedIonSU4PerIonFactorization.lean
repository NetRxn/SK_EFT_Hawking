/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness substrate — per-ion representation factorization

The Clifford+T representation `ρ_CliffT`, post-composed with the per-ion embedding
`ion{1,2}Embed`, factors through the full trapped-ion representation `trappedIonRho_full`
via the free-group token inclusion `incl{1,2}` (`Fin 2 ↪ Fin (4+2N)`, sending the two
Clifford+T tokens to the two per-ion 1Q tokens of the trapped-ion alphabet):

  `trappedIonRho_full ∘ (FreeGroup.map incl₁) = ion1Embed ∘ ρ_CliffT`   (ion 1: tokens 0,1)
  `trappedIonRho_full ∘ (FreeGroup.map incl₂) = ion2Embed ∘ ρ_CliffT`   (ion 2: tokens 2,3)

Mirrors the SU(2) lift/shift factorization `ρ_TI_factorization`. This is the algebraic core
of the per-ion density transfer: it puts the embedded Clifford+T representation's range inside
the trapped-ion representation's range, so the SU(2) Clifford+T density flows into
`H_of_G (trappedIonGeneratingSetSU4 N hN)`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness substrate
(per-ion representation factorization). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4PerIonBridge
import SKEFTHawking.FKLW.TrappedIonGeneratingSetSU4Full

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix SKEFTHawking.FKLW.GenericSU2

/-- Token inclusion for ion 1: `Fin 2 ↪ Fin (4+2N)`, `i ↦ i` (tokens 0,1 = ion-1 1Q gates). -/
def incl1 (N : ℕ) : Fin 2 → Fin (4 + 2 * N) := fun i => ⟨i.val, by have := i.isLt; omega⟩

/-- Token inclusion for ion 2: `Fin 2 ↪ Fin (4+2N)`, `i ↦ i+2` (tokens 2,3 = ion-2 1Q gates). -/
def incl2 (N : ℕ) : Fin 2 → Fin (4 + 2 * N) := fun i => ⟨i.val + 2, by have := i.isLt; omega⟩

/-- **Ion-1 representation factorization**:
`trappedIonRho_full ∘ (FreeGroup.map incl₁) = ion1Embed ∘ ρ_CliffT`. -/
theorem trappedIonRho_full_comp_map_incl1 (N : ℕ) (hN : 0 < N) :
    (trappedIonRho_full N hN).comp (FreeGroup.map (incl1 N)) =
      ion1Embed.comp ρ_CliffT := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply, FreeGroup.map.of]
  show trappedIonRho_full N hN (FreeGroup.of (incl1 N i)) =
    ion1Embed (ρ_CliffT (FreeGroup.of i))
  rw [trappedIonRho_full, FreeGroup.lift_apply_of]
  fin_cases i
  · rw [ρ_CliffT_of_0, ion1Embed_H_SU]
    rfl
  · rw [ρ_CliffT_of_1, ion1Embed_T_SU]
    rfl

/-- **Ion-2 representation factorization**:
`trappedIonRho_full ∘ (FreeGroup.map incl₂) = ion2Embed ∘ ρ_CliffT`. -/
theorem trappedIonRho_full_comp_map_incl2 (N : ℕ) (hN : 0 < N) :
    (trappedIonRho_full N hN).comp (FreeGroup.map (incl2 N)) =
      ion2Embed.comp ρ_CliffT := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply, FreeGroup.map.of]
  show trappedIonRho_full N hN (FreeGroup.of (incl2 N i)) =
    ion2Embed (ρ_CliffT (FreeGroup.of i))
  rw [trappedIonRho_full, FreeGroup.lift_apply_of]
  fin_cases i
  · rw [ρ_CliffT_of_0, ion2Embed_H_SU]
    rfl
  · rw [ρ_CliffT_of_1, ion2Embed_T_SU]
    rfl

end SKEFTHawking.FKLW.TrappedIonSU4
