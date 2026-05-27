/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.1 — `cliffordCCZGeneratingSetSU8` (full 4-generator instance)

The full `GeneratingSet 8` instance for the Clifford+CCZ alphabet:
3 Hadamards on each qubit + phase-corrected CCZ_SU. All 4 generators
packaged as SU(8) subtype elements.

This is the **substantive ship for T-A2′.1**: the full SU(8) Clifford+CCZ
alphabet at the GeneratingSet level. Closure-density at SU(8) (T-A2′.2)
ships separately via the Aaronson-Gottesman 2004 lineage; the ε₀-net +
calibration + bundled-strict headline (T-A2′.{3,4,5}) follow once
S.2g final discharge ships.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.1 (proper).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdGeneratingSet
import SKEFTHawking.FKLW.CliffordCCZSU8Substrate
import SKEFTHawking.FKLW.CCZ_SU

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The 4-element generator-token map for the full alphabet -/

/-- The 4-element generator-token map for the full Clifford+CCZ alphabet
on SU(8): tokens 0,1,2,3 ↦ {H_qubit1, H_qubit2, H_qubit3, CCZ_SU}. -/
noncomputable def cliffordCCZGenMap :
    Fin 4 → ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)
  | ⟨0, _⟩ => H_SU_on_qubit1_SU8
  | ⟨1, _⟩ => H_SU_on_qubit2_SU8
  | ⟨2, _⟩ => H_SU_on_qubit3_SU8
  | ⟨3, _⟩ => SKEFTHawking.FKLW.CCZSUExtension.CCZ_SU_subtype

/-- The full Clifford+CCZ representation: `FreeGroup (Fin 4) →* ↥(SU(8))`. -/
noncomputable def cliffordCCZRho :
    FreeGroup (Fin 4) →* ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  FreeGroup.lift cliffordCCZGenMap

/-! ## 2. The finite generator Finset -/

/-- The 4 free-group generators as a Finset. -/
noncomputable def cliffordCCZGens : Finset (FreeGroup (Fin 4)) :=
  (Finset.univ : Finset (Fin 4)).image FreeGroup.of

theorem cliffordCCZGens_nonempty : cliffordCCZGens.Nonempty := by
  unfold cliffordCCZGens
  refine ⟨FreeGroup.of ⟨0, by decide⟩, ?_⟩
  rw [Finset.mem_image]
  exact ⟨⟨0, by decide⟩, Finset.mem_univ _, rfl⟩

theorem cliffordCCZGens_generate :
    Subgroup.closure (cliffordCCZGens : Set (FreeGroup (Fin 4))) =
      (⊤ : Subgroup (FreeGroup (Fin 4))) := by
  unfold cliffordCCZGens
  have h_eq : (((Finset.univ : Finset (Fin 4)).image FreeGroup.of :
                Finset (FreeGroup (Fin 4))) : Set (FreeGroup (Fin 4))) =
              Set.range (FreeGroup.of : Fin 4 → FreeGroup (Fin 4)) := by
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [h_eq]
  exact FreeGroup.closure_range_of _

/-! ## 3. The full T-A2′.1 GeneratingSet 8 instance -/

/-- **`cliffordCCZGeneratingSetSU8`** — the **full T-A2′.1
GeneratingSet 8 instance** for the Clifford+CCZ alphabet on SU(8).

Alphabet (4 generators):
  * `H_SU_on_qubit1` — Hadamard on qubit 1 (lifted SU(2) → SU(8) via Kronecker)
  * `H_SU_on_qubit2` — Hadamard on qubit 2
  * `H_SU_on_qubit3` — Hadamard on qubit 3
  * `CCZ_SU` — phase-corrected doubly-controlled-Z (e^(iπ/8) • CCZ_mat)

All 4 generators packaged as `↥(specialUnitaryGroup (Fin 8) ℂ)` via
Phase 6y T-A2′.1-substrate's kron membership lemmas + the CCZ_SU
phase-correction shipped in `CCZ_SU.lean`.

Word type `FreeGroup (Fin 4)`. The closure-density at SU(8) is the
T-A2′.2 ship (via Aaronson-Gottesman 2004 lineage); ε₀-net + calibration
+ bundled-strict headline are T-A2′.{3,4,5}. -/
noncomputable def cliffordCCZGeneratingSetSU8 :
    SKEFTHawking.FKLW.GenericSUd.GeneratingSet 8 where
  W := FreeGroup (Fin 4)
  Wgroup := inferInstance
  ρ_hom := cliffordCCZRho
  gens := cliffordCCZGens
  gens_nonempty := cliffordCCZGens_nonempty
  gens_generate := cliffordCCZGens_generate

end SKEFTHawking.FKLW.CliffordCCZSU8
