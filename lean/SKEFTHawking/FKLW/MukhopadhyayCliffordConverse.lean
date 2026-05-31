/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x′ capstone — the 6z CCZ-essentiality converse (`⟨H,S,CNOT⟩` is not dense in SU(8))

The positive Phase-6z headline (`cliffordCCZLiteral_dense`) shows the literal Clifford+CCZ generating
set `{H_qi, S_qi, CNOT_ij, CCZ}` is dense in SU(8), with `CCZ` the essential non-Clifford resource. This
file ships the **converse**: the Clifford-only generating set `⟨H,S,CNOT⟩` (the same alphabet *without*
`CCZ`) is **not** dense.

The mechanism is Mukhopadhyay's Fact 3.9, made rigorous via the channel representation `channelRep`
(a monoid homomorphism, `channelRep_mul`/`channelRep_one`):

  * Each Clifford generator conjugates every Pauli to `±` a Pauli, so its channel rep is a **signed
    permutation** matrix (`channelRep_cliffordOnlyGen_isSignedPerm`, from the Phase 6x′ B corollaries).
  * The channel rep is a homomorphism, so the channel rep of *every word* in `⟨H,S,CNOT⟩` is a signed
    permutation (`cliffordWord_channelRep_signedPerm`, by `FreeGroup` induction).
  * The signed permutations are a **finite** set (`signedPermSet_finite`).

So the channel-rep image of `⟨H,S,CNOT⟩` lands in a finite set, while the channel-rep image of all of
SU(8) is infinite — hence `⟨H,S,CNOT⟩` cannot be dense. The infinitude + density-contradiction is
completed in `MukhopadhyayCliffordNotDense.lean` (next increment); this file ships the generating set and
the "every Clifford word is a signed permutation" half.

PUBLIC math layer only.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected. Kernel-pure;
  the only `decide` calls are over the finite `PauliLabel = Fin 4 × Fin 4 × Fin 4` (plain kernel
  `decide`, never `decide`).

-/

import SKEFTHawking.FKLW.MukhopadhyaySignedPerm
import SKEFTHawking.FKLW.MukhopadhyayChannelRepClifford
import SKEFTHawking.FKLW.CliffordCCZSU8LiteralGeneratingSet

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix
open SKEFTHawking.FKLW.CliffordCCZSU8
open SKEFTHawking.FKLW.GenericSU2 (H_SU)

/-! ## 1. Each Clifford generator's channel rep is a signed permutation (Fact 3.9 ⟹) -/

/-- `hSign` is `±1`-valued. -/
theorem hSign_pm (x : Fin 4) : hSign x = 1 ∨ hSign x = -1 := by
  fin_cases x <;> simp [hSign]

/-- `sSign` is `±1`-valued. -/
theorem sSign_pm (x : Fin 4) : sSign x = 1 ∨ sSign x = -1 := by
  fin_cases x <;> simp [sSign]

/-- `cnotSign` is `±1`-valued. -/
theorem cnotSign_pm (v1 v2 : Fin 4) : cnotSign v1 v2 = 1 ∨ cnotSign v1 v2 = -1 := by
  unfold cnotSign
  split_ifs <;> simp

/-- **Signed-permutation channel rep from a signed-permutation conjugation table.** If
`channelRep g r s = if r = lbl s then sgn s else 0` for an involutive label map `lbl` and a `±1`-valued
sign `sgn`, then `channelRep g` is a signed permutation matrix. -/
theorem isSignedPerm_of_conj_table {g : Matrix (Fin 8) (Fin 8) ℂ}
    {lbl : PauliLabel → PauliLabel} (hlbl : Function.Involutive lbl)
    {sgn : PauliLabel → ℂ} (hsgn : ∀ s, sgn s = 1 ∨ sgn s = -1)
    (htable : ∀ r s, channelRep g r s = if r = lbl s then sgn s else 0) :
    IsSignedPerm (channelRep g) := by
  refine ⟨hlbl.toPerm, sgn, hsgn, ?_⟩
  ext r s
  rw [htable r s]
  simp [signedPermMatrix, hlbl.coe_toPerm]

/-! ## 2. The Clifford-only generating set `⟨H, S, CNOT⟩` (no `CCZ`) -/

/-- The 9-element Clifford-only token map: `0,1,2 ↦ H_q{1,2,3}`, `3,4,5 ↦ S_q{1,2,3}`,
`6,7,8 ↦ CNOT_{12,13,23}` — the literal Clifford+CCZ alphabet **without** `CCZ`. -/
noncomputable def cliffordOnlyGenMap :
    Fin 9 → ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)
  | ⟨0, _⟩ => H_SU_on_qubit1_SU8
  | ⟨1, _⟩ => H_SU_on_qubit2_SU8
  | ⟨2, _⟩ => H_SU_on_qubit3_SU8
  | ⟨3, _⟩ => S_SU_on_qubit1_SU8
  | ⟨4, _⟩ => S_SU_on_qubit2_SU8
  | ⟨5, _⟩ => S_SU_on_qubit3_SU8
  | ⟨6, _⟩ => CNOT_12_SU8
  | ⟨7, _⟩ => CNOT_13_SU8
  | ⟨8, _⟩ => CNOT_23_SU8

/-- The Clifford-only representation `FreeGroup (Fin 9) →* ↥(SU(8))`. -/
noncomputable def cliffordOnlyRho :
    FreeGroup (Fin 9) →* ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  FreeGroup.lift cliffordOnlyGenMap

/-- The 9 free-group generators as a Finset. -/
noncomputable def cliffordOnlyGens : Finset (FreeGroup (Fin 9)) :=
  (Finset.univ : Finset (Fin 9)).image FreeGroup.of

theorem cliffordOnlyGens_nonempty : cliffordOnlyGens.Nonempty := by
  refine ⟨FreeGroup.of ⟨0, by decide⟩, ?_⟩
  rw [cliffordOnlyGens, Finset.mem_image]
  exact ⟨⟨0, by decide⟩, Finset.mem_univ _, rfl⟩

theorem cliffordOnlyGens_generate :
    Subgroup.closure (cliffordOnlyGens : Set (FreeGroup (Fin 9))) =
      (⊤ : Subgroup (FreeGroup (Fin 9))) := by
  have h_eq : ((cliffordOnlyGens : Finset (FreeGroup (Fin 9))) : Set (FreeGroup (Fin 9)))
      = Set.range (FreeGroup.of : Fin 9 → FreeGroup (Fin 9)) := by
    rw [cliffordOnlyGens]
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [h_eq]
  exact FreeGroup.closure_range_of _

/-- **`cliffordOnlyGeneratingSetSU8`** — the Clifford-only (no-`CCZ`) `GeneratingSet 8` instance on
SU(8), word type `FreeGroup (Fin 9)`. The negative companion to `cliffordCCZLiteralGeneratingSetSU8`. -/
noncomputable def cliffordOnlyGeneratingSetSU8 :
    SKEFTHawking.FKLW.GenericSUd.GeneratingSet 8 where
  W := FreeGroup (Fin 9)
  Wgroup := inferInstance
  ρ_hom := cliffordOnlyRho
  gens := cliffordOnlyGens
  gens_nonempty := cliffordOnlyGens_nonempty
  gens_generate := cliffordOnlyGens_generate

/-- `cliffordOnlyRho (of i) = cliffordOnlyGenMap i` (the `FreeGroup.lift` β-rule). -/
@[simp] theorem cliffordOnlyRho_of (i : Fin 9) :
    cliffordOnlyRho (FreeGroup.of i) = cliffordOnlyGenMap i :=
  FreeGroup.lift_apply_of

/-! ## 3. The channel rep of each Clifford generator is a signed permutation -/

/-- **Fact 3.9 (⟹) for every Clifford generator**: the channel rep of each of the 9 literal Clifford
generators (`H_qi, S_qi, CNOT_ij`) is a signed permutation matrix. -/
theorem channelRep_cliffordOnlyGen_isSignedPerm (i : Fin 9) :
    IsSignedPerm (channelRep (cliffordOnlyGenMap i).val) := by
  fin_cases i
  · exact isSignedPerm_of_conj_table (by unfold Function.Involutive; decide)
      (fun s => hSign_pm s.1) channelRep_hsu_q1
  · exact isSignedPerm_of_conj_table (by unfold Function.Involutive; decide)
      (fun s => hSign_pm s.2.1) channelRep_hsu_q2
  · exact isSignedPerm_of_conj_table (by unfold Function.Involutive; decide)
      (fun s => hSign_pm s.2.2) channelRep_hsu_q3
  · exact isSignedPerm_of_conj_table (by unfold Function.Involutive; decide)
      (fun s => sSign_pm s.1) channelRep_ssu_q1
  · exact isSignedPerm_of_conj_table (by unfold Function.Involutive; decide)
      (fun s => sSign_pm s.2.1) channelRep_ssu_q2
  · exact isSignedPerm_of_conj_table (by unfold Function.Involutive; decide)
      (fun s => sSign_pm s.2.2) channelRep_ssu_q3
  · exact isSignedPerm_of_conj_table (by unfold Function.Involutive; decide)
      (fun s => cnotSign_pm s.1 s.2.1) channelRep_cnot12
  · exact isSignedPerm_of_conj_table (by unfold Function.Involutive; decide)
      (fun s => cnotSign_pm s.1 s.2.2) channelRep_cnot13
  · exact isSignedPerm_of_conj_table (by unfold Function.Involutive; decide)
      (fun s => cnotSign_pm s.2.1 s.2.2) channelRep_cnot23

/-! ## 4. Every Clifford-only word has a signed-permutation channel rep -/

/-- **The channel rep of every word in `⟨H,S,CNOT⟩` is a signed permutation** (Fact 3.9 ⟹, lifted
across the free group by the homomorphism law). The Clifford-only image lands in the finite set of
signed permutation matrices — the heart of the CCZ-essentiality converse. -/
theorem cliffordWord_channelRep_signedPerm (w : FreeGroup (Fin 9)) :
    IsSignedPerm (channelRep (cliffordOnlyRho w).val) := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      rw [map_one, OneMemClass.coe_one, channelRep_one]
      exact isSignedPerm_one
  | of i =>
      rw [cliffordOnlyRho_of]
      exact channelRep_cliffordOnlyGen_isSignedPerm i
  | inv_of i _ =>
      apply isSignedPerm_of_mul_eq_one (channelRep_cliffordOnlyGen_isSignedPerm i)
      rw [← channelRep_mul, ← Submonoid.coe_mul, map_inv, cliffordOnlyRho_of,
        mul_inv_cancel, OneMemClass.coe_one, channelRep_one]
  | mul x y hx hy =>
      rw [map_mul, Submonoid.coe_mul, channelRep_mul]
      exact isSignedPerm_mul hx hy

end SKEFTHawking.FKLW.MukhopadhyayCCZ
