/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 1 — the literal Clifford+CCZ (no-`T`) generating set `⟨H, S, CNOT, CCZ⟩` on SU(8)

The faithful, CCZ-essential headline targets the **literal** alphabet `{H_qi, S_qi, CNOT_ij, CCZ}`
with **no `T`** — every generator is finite-order (`{H,S}` is the finite single-qubit Clifford group,
`CCZ` has order 2). This is the genuine Phase-6z alphabet (vs. Phase 6y's universal Clifford+CCZ+`T`,
where `T` supplied per-qubit continuous flows). Density here comes from the irrational-angle seed
(`CliffordCCZSU8Irrationality.lean`) plus Clifford-conjugation spread (Gate 2 = BEST: the Clifford
orbit of `log g₀` spans `𝔰𝔲(8)` by itself), not per-qubit flows.

This module ships the `GenericSUd.GeneratingSet 8` instance `cliffordCCZLiteralGeneratingSetSU8`
(10 generators: `H_q{1,2,3}`, `S_q{1,2,3}`, `CNOT_{12,13,23}`, `CCZ_SU`). The Clifford `S`-gate is
shipped here as a genuinely `T`-free element: `S_SU := diag(e^{−iπ/4}, e^{iπ/4})` with a direct SU(2)
membership proof (no reference to `T`), so the alphabet's `T`-freedom is manifest even in the proof.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6z provenance

Phase 6z Wave 1 — literal generating set (Substrate_Inventory B1). 2026-05-28.
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

/-! ## 1. The Clifford `S`-gate as an SU(2)/SU(8) element (genuinely `T`-free) -/

/-- For real `c`, `exp(c·i) · conj(exp(c·i)) = 1` (the modulus-1 fact for a phase). -/
private theorem cexp_imag_mul_conj_one (c : ℝ) :
    Complex.exp ((c : ℂ) * Complex.I) * (starRingEnd ℂ) (Complex.exp ((c : ℂ) * Complex.I)) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add,
    show (c : ℂ) * Complex.I + (starRingEnd ℂ) ((c : ℂ) * Complex.I) = 0 by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring,
    Complex.exp_zero]

/-- `S_SU_mat = diag(e^{−iπ/4}, e^{iπ/4}) ∈ SU(2)` — direct diagonal proof, no `T`. -/
theorem S_SU_mat_mem_specialUnitaryGroup :
    SKEFTHawking.FKLW.GenericSU2.S_SU_mat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SKEFTHawking.FKLW.GenericSU2.S_SU_mat, Matrix.mul_apply, Fin.sum_univ_two]
    · rw [show -(Complex.I * (Real.pi : ℂ) / 4) = (-(Real.pi / 4) : ℝ) * Complex.I by push_cast; ring]
      exact cexp_imag_mul_conj_one _
    · rw [show Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4) : ℝ) * Complex.I by push_cast; ring]
      exact cexp_imag_mul_conj_one _
  · rw [show SKEFTHawking.FKLW.GenericSU2.S_SU_mat
        = !![Complex.exp (-(Complex.I * (Real.pi : ℂ) / 4)), 0;
             0, Complex.exp (Complex.I * (Real.pi : ℂ) / 4)] from rfl,
      Matrix.det_fin_two_of, mul_zero, sub_zero, ← Complex.exp_add,
      show -(Complex.I * (Real.pi : ℂ) / 4) + Complex.I * (Real.pi : ℂ) / 4 = 0 by ring,
      Complex.exp_zero]

/-- **The SU(2)-bundled Clifford `S`-gate** `diag(e^{−iπ/4}, e^{iπ/4})`. -/
noncomputable def S_SU : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨SKEFTHawking.FKLW.GenericSU2.S_SU_mat, S_SU_mat_mem_specialUnitaryGroup⟩

/-- **S-gate on qubit 1 (SU(8))** = `qubit1Embed S_SU`. -/
noncomputable def S_SU_on_qubit1_SU8 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) := qubit1Embed S_SU

/-- **S-gate on qubit 2 (SU(8))** = `qubit2Embed S_SU`. -/
noncomputable def S_SU_on_qubit2_SU8 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) := qubit2Embed S_SU

/-- **S-gate on qubit 3 (SU(8))** = `qubit3Embed S_SU`. -/
noncomputable def S_SU_on_qubit3_SU8 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) := qubit3Embed S_SU

/-! ## 2. The 10-element literal generator-token map (no `T`) -/

/-- The literal Clifford+CCZ token map: `0,1,2 ↦ H_q{1,2,3}`, `3,4,5 ↦ S_q{1,2,3}`,
`6,7,8 ↦ CNOT_{12,13,23}`, `9 ↦ CCZ_SU`. -/
noncomputable def cliffordCCZLiteralGenMap :
    Fin 10 → ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)
  | ⟨0, _⟩ => H_SU_on_qubit1_SU8
  | ⟨1, _⟩ => H_SU_on_qubit2_SU8
  | ⟨2, _⟩ => H_SU_on_qubit3_SU8
  | ⟨3, _⟩ => S_SU_on_qubit1_SU8
  | ⟨4, _⟩ => S_SU_on_qubit2_SU8
  | ⟨5, _⟩ => S_SU_on_qubit3_SU8
  | ⟨6, _⟩ => CNOT_12_SU8
  | ⟨7, _⟩ => CNOT_13_SU8
  | ⟨8, _⟩ => CNOT_23_SU8
  | ⟨9, _⟩ => SKEFTHawking.FKLW.CCZSUExtension.CCZ_SU_subtype

/-- The literal Clifford+CCZ representation `FreeGroup (Fin 10) →* ↥(SU(8))`. -/
noncomputable def cliffordCCZLiteralRho :
    FreeGroup (Fin 10) →* ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  FreeGroup.lift cliffordCCZLiteralGenMap

/-! ## 3. The finite generator Finset + closure facts -/

/-- The 10 free-group generators as a Finset. -/
noncomputable def cliffordCCZLiteralGens : Finset (FreeGroup (Fin 10)) :=
  (Finset.univ : Finset (Fin 10)).image FreeGroup.of

theorem cliffordCCZLiteralGens_nonempty : cliffordCCZLiteralGens.Nonempty := by
  refine ⟨FreeGroup.of ⟨0, by decide⟩, ?_⟩
  rw [cliffordCCZLiteralGens, Finset.mem_image]
  exact ⟨⟨0, by decide⟩, Finset.mem_univ _, rfl⟩

theorem cliffordCCZLiteralGens_generate :
    Subgroup.closure (cliffordCCZLiteralGens : Set (FreeGroup (Fin 10))) =
      (⊤ : Subgroup (FreeGroup (Fin 10))) := by
  have h_eq : ((cliffordCCZLiteralGens : Finset (FreeGroup (Fin 10))) :
        Set (FreeGroup (Fin 10))) = Set.range (FreeGroup.of : Fin 10 → FreeGroup (Fin 10)) := by
    rw [cliffordCCZLiteralGens]
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [h_eq]
  exact FreeGroup.closure_range_of _

/-! ## 4. The literal `GeneratingSet 8` instance -/

/-- **`cliffordCCZLiteralGeneratingSetSU8`** — the literal Clifford+CCZ (no-`T`) `GeneratingSet 8`
instance on SU(8), word type `FreeGroup (Fin 10)`. Density at SU(8) is via the irrational-angle seed
+ Clifford-conjugation spread (Gate 2 = BEST), with `CCZ` the essential non-Clifford resource. -/
noncomputable def cliffordCCZLiteralGeneratingSetSU8 :
    SKEFTHawking.FKLW.GenericSUd.GeneratingSet 8 where
  W := FreeGroup (Fin 10)
  Wgroup := inferInstance
  ρ_hom := cliffordCCZLiteralRho
  gens := cliffordCCZLiteralGens
  gens_nonempty := cliffordCCZLiteralGens_nonempty
  gens_generate := cliffordCCZLiteralGens_generate

end SKEFTHawking.FKLW.CliffordCCZSU8
