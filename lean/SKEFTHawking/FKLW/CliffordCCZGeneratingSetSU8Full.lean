/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.1 — `cliffordCCZGeneratingSetSU8` (universal Clifford+CCZ+T, 10 generators)

The `GeneratingSet 8` instance for the **universal Clifford+CCZ+T** alphabet (10 generators):
per-qubit Hadamards `H_q{1,2,3}`, per-qubit T-gates `T_q{1,2,3}`, cross-qubit CNOTs
`CNOT_{12,13,23}`, and the phase-corrected `CCZ_SU`.

**Why not just `{H_q1,H_q2,H_q3, CCZ}`?** That literal alphabet is non-universal (OF-1): every
word is a global phase times a real orthogonal matrix, so the generated group is dense only in
`SO(8)`, never `SU(8)` — a `ClosureDenseWitness` for it would be false. The fix (DR blueprint
`Lit-Search/Phase-6y/...ClosureDenseWitness...Blueprint.md`, OF-1; user-delegated 2026-05-28) is the
genuine universal Clifford+CCZ set augmented with `T`: `T` is the single-qubit infinite-order gate
({H,S} alone is the *finite* Clifford group → no continuous per-qubit flow lines), which lets the
per-qubit `𝔰𝔲(2)` flow lines reuse the Phase 6u Clifford+T SU(2) density
(`cliffordT_H_of_G_eq_top_unconditional`) pushed through `qubit{1,2,3}Embed`; the entangling-tangent
spread is then explicit conjugation transport — `CNOT`-conjugation produces the base entanglers
(`σ_x⊗σ_x` etc.) and per-qubit Clifford conjugation rotates each factor to reach all 63 Paulis (NOT
an abstract `Sp(6,𝔽₂)` orbit argument). CCZ is retained so the alphabet literally contains
Clifford+CCZ. (Note `{H,T,CNOT}` is already Clifford+T = universal; CCZ is over-complete and is
unused in the witness construction — this ships Clifford+T at SU(8), not the CCZ-essential headline.)

Per-qubit generators are the embedded images of the Clifford+T generators
(`H_SU_on_qubit_i_SU8 = qubit_iEmbed H_SU`, `T_SU_on_qubit_i_SU8 = qubit_iEmbed T_SU`); this is the
hook for the per-qubit-flow factorization (T-A2′.2). The closure-density witness ships separately.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.1 (proper).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdGeneratingSet
import SKEFTHawking.FKLW.CliffordCCZSU8Substrate
import SKEFTHawking.FKLW.CliffordCCZSU8UniversalGates
import SKEFTHawking.FKLW.CliffordCCZSU8CNOT
import SKEFTHawking.FKLW.CCZ_SU

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The 10-element generator-token map for the universal alphabet -/

/-- The 10-element generator-token map for the universal Clifford+CCZ+T alphabet on SU(8):
tokens `0,1,2 ↦ H_q{1,2,3}`, `3,4,5 ↦ T_q{1,2,3}`, `6,7,8 ↦ CNOT_{12,13,23}`, `9 ↦ CCZ_SU`. -/
noncomputable def cliffordCCZGenMap :
    Fin 10 → ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)
  | ⟨0, _⟩ => H_SU_on_qubit1_SU8
  | ⟨1, _⟩ => H_SU_on_qubit2_SU8
  | ⟨2, _⟩ => H_SU_on_qubit3_SU8
  | ⟨3, _⟩ => T_SU_on_qubit1_SU8
  | ⟨4, _⟩ => T_SU_on_qubit2_SU8
  | ⟨5, _⟩ => T_SU_on_qubit3_SU8
  | ⟨6, _⟩ => CNOT_12_SU8
  | ⟨7, _⟩ => CNOT_13_SU8
  | ⟨8, _⟩ => CNOT_23_SU8
  | ⟨9, _⟩ => SKEFTHawking.FKLW.CCZSUExtension.CCZ_SU_subtype

/-- The universal Clifford+CCZ+T representation: `FreeGroup (Fin 10) →* ↥(SU(8))`. -/
noncomputable def cliffordCCZRho :
    FreeGroup (Fin 10) →* ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  FreeGroup.lift cliffordCCZGenMap

/-! ## 2. The finite generator Finset -/

/-- The 10 free-group generators as a Finset. -/
noncomputable def cliffordCCZGens : Finset (FreeGroup (Fin 10)) :=
  (Finset.univ : Finset (Fin 10)).image FreeGroup.of

theorem cliffordCCZGens_nonempty : cliffordCCZGens.Nonempty := by
  unfold cliffordCCZGens
  refine ⟨FreeGroup.of ⟨0, by decide⟩, ?_⟩
  rw [Finset.mem_image]
  exact ⟨⟨0, by decide⟩, Finset.mem_univ _, rfl⟩

theorem cliffordCCZGens_generate :
    Subgroup.closure (cliffordCCZGens : Set (FreeGroup (Fin 10))) =
      (⊤ : Subgroup (FreeGroup (Fin 10))) := by
  unfold cliffordCCZGens
  have h_eq : (((Finset.univ : Finset (Fin 10)).image FreeGroup.of :
                Finset (FreeGroup (Fin 10))) : Set (FreeGroup (Fin 10))) =
              Set.range (FreeGroup.of : Fin 10 → FreeGroup (Fin 10)) := by
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [h_eq]
  exact FreeGroup.closure_range_of _

/-! ## 3. The full T-A2′.1 GeneratingSet 8 instance -/

/-- **`cliffordCCZGeneratingSetSU8`** — the **universal Clifford+CCZ+T
GeneratingSet 8 instance** on SU(8).

Alphabet (10 generators):
  * `H_SU_on_qubit{1,2,3}_SU8` — Hadamards (= `qubit_iEmbed H_SU`)
  * `T_SU_on_qubit{1,2,3}_SU8` — T-gates (= `qubit_iEmbed T_SU`); the single-qubit ∞-order resource
  * `CNOT_{12,13,23}_SU8` — cross-qubit Cliffords (even-permutation SU(8) matrices)
  * `CCZ_SU` — phase-corrected doubly-controlled-Z (e^(iπ/8) • CCZ_mat)

Word type `FreeGroup (Fin 10)`. The closure-density at SU(8) is the T-A2′.2 ship: per-qubit flows
from the Phase 6u Clifford+T SU(2) density (via the embeddings), spread to the 63 entangling tangents
by explicit Clifford/CNOT conjugation transport. ε₀-net + calibration + bundled-strict headline
are T-A2′.{3,4,5}. (Density rests on the `{H,T,CNOT}` sub-alphabet; CCZ is over-complete.) -/
noncomputable def cliffordCCZGeneratingSetSU8 :
    SKEFTHawking.FKLW.GenericSUd.GeneratingSet 8 where
  W := FreeGroup (Fin 10)
  Wgroup := inferInstance
  ρ_hom := cliffordCCZRho
  gens := cliffordCCZGens
  gens_nonempty := cliffordCCZGens_nonempty
  gens_generate := cliffordCCZGens_generate

end SKEFTHawking.FKLW.CliffordCCZSU8
