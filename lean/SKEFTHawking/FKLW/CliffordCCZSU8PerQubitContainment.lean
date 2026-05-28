/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2 (D) witness — per-qubit containment `qubit_iEmbed(SU(2)) ⊆ H_of_G`

The 3-qubit analog of `TrappedIonSU4PerIonContainment`: the entire embedded SU(2)
(`qubit_iEmbed '' univ`) lies in the closed subgroup `H_of_G cliffordCCZGeneratingSetSU8` (the
universal Clifford+CCZ+T alphabet's closure).

Proof: the shipped UNCONDITIONAL SU(2) Clifford+T density gives `closure (range ρ_CliffT) = univ`
(Phase 6u, via `cliffordT_H_of_G_eq_top_unconditional`); the per-qubit embedding `qubit_iEmbed` is a
continuous monoid hom, so it carries that closure into `closure (qubit_iEmbed '' range ρ_CliffT)`;
the **factorization** `cliffordCCZRho ∘ (FreeGroup.map incl_i) = qubit_iEmbed ∘ ρ_CliffT` (where
`incl_i : Fin 2 ↪ Fin 10` sends the two Clifford+T tokens `{H_SU, T_SU}` to the qubit-`i` `{H, T}`
tokens of the universal alphabet) puts that image inside `range cliffordCCZRho`, whose closure is
exactly `H_of_G cliffordCCZGeneratingSetSU8`.

This is the per-qubit half of the SU(8) `ClosureDenseWitness`: it yields that every per-qubit
`𝔰𝔲(2)` one-parameter subgroup `exp(t · qubit_iEmbed-tangent) = qubit_iEmbed (exp(t·x))` is in
`H_of_G`, i.e. the `hX_flow` condition for the 9 single-qubit tangents (next module).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 PROPER — (D) witness per-qubit
containment (density transfer). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZGeneratingSetSU8Full
import SKEFTHawking.FKLW.CliffordCCZSU8UniversalGates
import SKEFTHawking.FKLW.TrappedIonSU4PerIonContainment

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.GenericSU2

/-! ## 1. Token inclusions `Fin 2 ↪ Fin 10` (Clifford+T tokens → per-qubit {H,T} tokens) -/

/-- Qubit-1 token inclusion: `0 ↦ 0` (H_q1), `1 ↦ 3` (T_q1). -/
def incl1 : Fin 2 → Fin 10
  | 0 => 0
  | 1 => 3

/-- Qubit-2 token inclusion: `0 ↦ 1` (H_q2), `1 ↦ 4` (T_q2). -/
def incl2 : Fin 2 → Fin 10
  | 0 => 1
  | 1 => 4

/-- Qubit-3 token inclusion: `0 ↦ 2` (H_q3), `1 ↦ 5` (T_q3). -/
def incl3 : Fin 2 → Fin 10
  | 0 => 2
  | 1 => 5

/-! ## 2. Per-qubit representation factorizations -/

/-- **Qubit-1 factorization**: `cliffordCCZRho ∘ (FreeGroup.map incl1) = qubit1Embed ∘ ρ_CliffT`. -/
theorem cliffordCCZRho_comp_map_incl1 :
    cliffordCCZRho.comp (FreeGroup.map incl1) = qubit1Embed.comp ρ_CliffT := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply, FreeGroup.map.of]
  show cliffordCCZRho (FreeGroup.of (incl1 i)) = qubit1Embed (ρ_CliffT (FreeGroup.of i))
  rw [cliffordCCZRho, FreeGroup.lift_apply_of]
  fin_cases i
  · rw [ρ_CliffT_of_0]; exact H_SU_on_qubit1_SU8_eq_embed
  · rw [ρ_CliffT_of_1]; rfl

/-- **Qubit-2 factorization**. -/
theorem cliffordCCZRho_comp_map_incl2 :
    cliffordCCZRho.comp (FreeGroup.map incl2) = qubit2Embed.comp ρ_CliffT := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply, FreeGroup.map.of]
  show cliffordCCZRho (FreeGroup.of (incl2 i)) = qubit2Embed (ρ_CliffT (FreeGroup.of i))
  rw [cliffordCCZRho, FreeGroup.lift_apply_of]
  fin_cases i
  · rw [ρ_CliffT_of_0]; exact H_SU_on_qubit2_SU8_eq_embed
  · rw [ρ_CliffT_of_1]; rfl

/-- **Qubit-3 factorization**. -/
theorem cliffordCCZRho_comp_map_incl3 :
    cliffordCCZRho.comp (FreeGroup.map incl3) = qubit3Embed.comp ρ_CliffT := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply, FreeGroup.map.of]
  show cliffordCCZRho (FreeGroup.of (incl3 i)) = qubit3Embed (ρ_CliffT (FreeGroup.of i))
  rw [cliffordCCZRho, FreeGroup.lift_apply_of]
  fin_cases i
  · rw [ρ_CliffT_of_0]; exact H_SU_on_qubit3_SU8_eq_embed
  · rw [ρ_CliffT_of_1]; rfl

/-! ## 3. Per-qubit containment `qubit_iEmbed(SU(2)) ⊆ H_of_G` -/

/-- **Qubit-1 containment**: `qubit1Embed A ∈ H_of_G cliffordCCZGeneratingSetSU8`. -/
theorem qubit1Embed_mem_H_of_G (A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    qubit1Embed A ∈ SKEFTHawking.FKLW.GenericSUd.H_of_G cliffordCCZGeneratingSetSU8 := by
  have hA : A ∈ closure (Set.range ρ_CliffT) := by
    rw [SKEFTHawking.FKLW.TrappedIonSU4.closure_range_ρCliffT_eq_univ]; trivial
  have h1 : qubit1Embed A ∈ closure (qubit1Embed '' Set.range ρ_CliffT) :=
    image_closure_subset_closure_image qubit1Embed_continuous ⟨A, hA, rfl⟩
  have h2 : qubit1Embed '' Set.range ρ_CliffT ⊆ Set.range cliffordCCZRho := by
    rintro x ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨FreeGroup.map incl1 w, ?_⟩
    have hfac := DFunLike.congr_fun cliffordCCZRho_comp_map_incl1 w
    simpa only [MonoidHom.comp_apply] using hfac
  have h3 : closure (qubit1Embed '' Set.range ρ_CliffT) ⊆ closure (Set.range cliffordCCZRho) :=
    closure_mono h2
  rw [← SetLike.mem_coe, SKEFTHawking.FKLW.GenericSUd.H_of_G,
    Subgroup.topologicalClosure_coe, MonoidHom.coe_range]
  exact h3 h1

/-- **Qubit-2 containment**. -/
theorem qubit2Embed_mem_H_of_G (A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    qubit2Embed A ∈ SKEFTHawking.FKLW.GenericSUd.H_of_G cliffordCCZGeneratingSetSU8 := by
  have hA : A ∈ closure (Set.range ρ_CliffT) := by
    rw [SKEFTHawking.FKLW.TrappedIonSU4.closure_range_ρCliffT_eq_univ]; trivial
  have h1 : qubit2Embed A ∈ closure (qubit2Embed '' Set.range ρ_CliffT) :=
    image_closure_subset_closure_image qubit2Embed_continuous ⟨A, hA, rfl⟩
  have h2 : qubit2Embed '' Set.range ρ_CliffT ⊆ Set.range cliffordCCZRho := by
    rintro x ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨FreeGroup.map incl2 w, ?_⟩
    have hfac := DFunLike.congr_fun cliffordCCZRho_comp_map_incl2 w
    simpa only [MonoidHom.comp_apply] using hfac
  have h3 : closure (qubit2Embed '' Set.range ρ_CliffT) ⊆ closure (Set.range cliffordCCZRho) :=
    closure_mono h2
  rw [← SetLike.mem_coe, SKEFTHawking.FKLW.GenericSUd.H_of_G,
    Subgroup.topologicalClosure_coe, MonoidHom.coe_range]
  exact h3 h1

/-- **Qubit-3 containment**. -/
theorem qubit3Embed_mem_H_of_G (A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    qubit3Embed A ∈ SKEFTHawking.FKLW.GenericSUd.H_of_G cliffordCCZGeneratingSetSU8 := by
  have hA : A ∈ closure (Set.range ρ_CliffT) := by
    rw [SKEFTHawking.FKLW.TrappedIonSU4.closure_range_ρCliffT_eq_univ]; trivial
  have h1 : qubit3Embed A ∈ closure (qubit3Embed '' Set.range ρ_CliffT) :=
    image_closure_subset_closure_image qubit3Embed_continuous ⟨A, hA, rfl⟩
  have h2 : qubit3Embed '' Set.range ρ_CliffT ⊆ Set.range cliffordCCZRho := by
    rintro x ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨FreeGroup.map incl3 w, ?_⟩
    have hfac := DFunLike.congr_fun cliffordCCZRho_comp_map_incl3 w
    simpa only [MonoidHom.comp_apply] using hfac
  have h3 : closure (qubit3Embed '' Set.range ρ_CliffT) ⊆ closure (Set.range cliffordCCZRho) :=
    closure_mono h2
  rw [← SetLike.mem_coe, SKEFTHawking.FKLW.GenericSUd.H_of_G,
    Subgroup.topologicalClosure_coe, MonoidHom.coe_range]
  exact h3 h1

end SKEFTHawking.FKLW.CliffordCCZSU8
