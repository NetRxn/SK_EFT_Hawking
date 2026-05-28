/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness — per-ion containment `ionEmbed(SU(2)) ⊆ H_of_G(trappedIon)`

The density-transfer culmination of the per-ion substrate: the entire embedded SU(2)
(`ion{1,2}Embed '' univ`) lies in the closed subgroup `H_of_G (trappedIonGeneratingSetSU4 N hN)`.

Proof: the shipped UNCONDITIONAL SU(2) Clifford+T density gives
`closure (range ρ_CliffT) = univ`; the per-ion embedding is continuous, so it carries that
closure into `closure (ionEmbed '' range ρ_CliffT)`; the factorization
(`ionEmbed ∘ ρ_CliffT = trappedIonRho_full ∘ FreeGroup.map incl`) puts that image inside
`range trappedIonRho_full`, whose closure is exactly `H_of_G (trappedIon)`.

This is the per-ion half of the Brylinski-Brylinski `ClosureDenseWitness`: it yields that every
per-ion 𝔰𝔲(2) one-parameter subgroup `exp(t · ionEmbed-tangent) = ionEmbed (exp(t·x))` is in
`H_of_G`, i.e. the `hX_flow` condition for the 6 per-ion tangents.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness per-ion
containment (density transfer). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4PerIonFactorization
import SKEFTHawking.FKLW.CliffordTV4WitnessUnconditional

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix SKEFTHawking.FKLW.GenericSU2

/-- The Clifford+T representation has dense range in `SU(2)`:
`closure (Set.range ρ_CliffT) = Set.univ`. (Coe of the unconditional `H_of_G = ⊤`.) -/
theorem closure_range_ρCliffT_eq_univ :
    closure (Set.range ρ_CliffT) =
      (Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  have h := cliffordT_H_of_G_eq_top_unconditional
  have hcoe := congrArg (fun S : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
      (S : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) h
  simpa only [SKEFTHawking.FKLW.GenericSU2.H_of_G, Subgroup.topologicalClosure_coe,
    MonoidHom.coe_range, Subgroup.coe_top] using hcoe

/-- **Per-ion-1 containment**: `ion1Embed A ∈ H_of_G (trappedIonGeneratingSetSU4 N hN)`
for every `A ∈ SU(2)`. -/
theorem ion1Embed_mem_H_of_G (N : ℕ) (hN : 0 < N)
    (A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ion1Embed A ∈ SKEFTHawking.FKLW.GenericSUd.H_of_G (trappedIonGeneratingSetSU4 N hN) := by
  have hA : A ∈ closure (Set.range ρ_CliffT) := by
    rw [closure_range_ρCliffT_eq_univ]; trivial
  have h1 : ion1Embed A ∈ closure (ion1Embed '' Set.range ρ_CliffT) :=
    image_closure_subset_closure_image ion1Embed_continuous ⟨A, hA, rfl⟩
  have h2 : ion1Embed '' Set.range ρ_CliffT ⊆ Set.range (trappedIonRho_full N hN) := by
    rintro x ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨FreeGroup.map (incl1 N) w, ?_⟩
    have hfac := DFunLike.congr_fun (trappedIonRho_full_comp_map_incl1 N hN) w
    simpa only [MonoidHom.comp_apply] using hfac
  have h3 : closure (ion1Embed '' Set.range ρ_CliffT) ⊆
      closure (Set.range (trappedIonRho_full N hN)) := closure_mono h2
  rw [← SetLike.mem_coe, SKEFTHawking.FKLW.GenericSUd.H_of_G,
    Subgroup.topologicalClosure_coe, MonoidHom.coe_range]
  exact h3 h1

/-- **Per-ion-2 containment**: `ion2Embed A ∈ H_of_G (trappedIonGeneratingSetSU4 N hN)`. -/
theorem ion2Embed_mem_H_of_G (N : ℕ) (hN : 0 < N)
    (A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ion2Embed A ∈ SKEFTHawking.FKLW.GenericSUd.H_of_G (trappedIonGeneratingSetSU4 N hN) := by
  have hA : A ∈ closure (Set.range ρ_CliffT) := by
    rw [closure_range_ρCliffT_eq_univ]; trivial
  have h1 : ion2Embed A ∈ closure (ion2Embed '' Set.range ρ_CliffT) :=
    image_closure_subset_closure_image ion2Embed_continuous ⟨A, hA, rfl⟩
  have h2 : ion2Embed '' Set.range ρ_CliffT ⊆ Set.range (trappedIonRho_full N hN) := by
    rintro x ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨FreeGroup.map (incl2 N) w, ?_⟩
    have hfac := DFunLike.congr_fun (trappedIonRho_full_comp_map_incl2 N hN) w
    simpa only [MonoidHom.comp_apply] using hfac
  have h3 : closure (ion2Embed '' Set.range ρ_CliffT) ⊆
      closure (Set.range (trappedIonRho_full N hN)) := closure_mono h2
  rw [← SetLike.mem_coe, SKEFTHawking.FKLW.GenericSUd.H_of_G,
    Subgroup.topologicalClosure_coe, MonoidHom.coe_range]
  exact h3 h1

end SKEFTHawking.FKLW.TrappedIonSU4
