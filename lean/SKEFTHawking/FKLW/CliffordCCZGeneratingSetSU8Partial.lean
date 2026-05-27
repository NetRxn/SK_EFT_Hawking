/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.1-partial — `cliffordCCZGeneratingSetSU8_H3` (3-Hadamard instance)

A `GeneratingSet 8` instance for the Clifford+CCZ alphabet restricted
to the **three Hadamard-on-qubit-i gates only**. Uses Phase 6y
T-A2′.1-substrate's packaged SU(8) subtype elements
`H_SU_on_qubit{1,2,3}_SU8`.

This is the **Clifford-only sub-alphabet** — a substantive intermediate
ship toward the full T-A2′.1 (which adds CCZ_SU once
`CCZ_SU_mem_specialUnitaryGroup` ships).

The 3 Hadamards alone generate a small subgroup of SU(8); the full
Clifford+CCZ alphabet adds the doubly-controlled-Z entangling gate
for SU(8)-density via the Aaronson-Gottesman 2004 lineage.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.1 partial.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdGeneratingSet
import SKEFTHawking.FKLW.CliffordCCZSU8Substrate

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The 3-generator word type and representation -/

/-- The 3-element generator-token map for the Clifford-only sub-alphabet. -/
noncomputable def cliffordH3GenMap :
    Fin 3 → ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)
  | ⟨0, _⟩ => H_SU_on_qubit1_SU8
  | ⟨1, _⟩ => H_SU_on_qubit2_SU8
  | ⟨2, _⟩ => H_SU_on_qubit3_SU8

/-- The 3-Hadamard representation:
`FreeGroup (Fin 3) →* ↥(SU(8))`. -/
noncomputable def cliffordH3Rho :
    FreeGroup (Fin 3) →* ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  FreeGroup.lift cliffordH3GenMap

/-! ## 2. The finite generator Finset -/

/-- The 3 free-group generators as a Finset. -/
noncomputable def cliffordH3Gens : Finset (FreeGroup (Fin 3)) :=
  (Finset.univ : Finset (Fin 3)).image FreeGroup.of

theorem cliffordH3Gens_nonempty : cliffordH3Gens.Nonempty := by
  unfold cliffordH3Gens
  refine ⟨FreeGroup.of ⟨0, by decide⟩, ?_⟩
  rw [Finset.mem_image]
  exact ⟨⟨0, by decide⟩, Finset.mem_univ _, rfl⟩

theorem cliffordH3Gens_generate :
    Subgroup.closure (cliffordH3Gens : Set (FreeGroup (Fin 3))) =
      (⊤ : Subgroup (FreeGroup (Fin 3))) := by
  unfold cliffordH3Gens
  have h_eq : (((Finset.univ : Finset (Fin 3)).image FreeGroup.of :
                Finset (FreeGroup (Fin 3))) : Set (FreeGroup (Fin 3))) =
              Set.range (FreeGroup.of : Fin 3 → FreeGroup (Fin 3)) := by
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [h_eq]
  exact FreeGroup.closure_range_of _

/-! ## 3. The 3-Hadamard Clifford GeneratingSet 8 instance -/

/-- **Clifford-only 3-Hadamard `GeneratingSet 8` instance** (substantive
intermediate ship toward T-A2′.1 proper).

Alphabet = {H on qubit 1, H on qubit 2, H on qubit 3} as 8×8 matrices.
Word type `FreeGroup (Fin 3)`. The full T-A2′.1 adds CCZ_SU as a 4th
generator (once `CCZ_SU_mem_specialUnitaryGroup` ships). -/
noncomputable def cliffordCCZGeneratingSetSU8_H3 :
    SKEFTHawking.FKLW.GenericSUd.GeneratingSet 8 where
  W := FreeGroup (Fin 3)
  Wgroup := inferInstance
  ρ_hom := cliffordH3Rho
  gens := cliffordH3Gens
  gens_nonempty := cliffordH3Gens_nonempty
  gens_generate := cliffordH3Gens_generate

end SKEFTHawking.FKLW.CliffordCCZSU8
