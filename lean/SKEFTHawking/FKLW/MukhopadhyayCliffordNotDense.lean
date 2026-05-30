/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x′ capstone — `⟨H,S,CNOT⟩` is not dense in SU(8) (the 6z CCZ-essentiality converse)

PUBLIC math layer only.
-/

import SKEFTHawking.FKLW.MukhopadhyayCliffordConverse
import SKEFTHawking.FKLW.CliffordCCZSU8SeedNotFiniteOrder
import SKEFTHawking.FKLW.GenericSUdClosureDenseWitness

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix
open SKEFTHawking.FKLW.CliffordCCZSU8

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **The channel representation is continuous** (a polynomial map in the entries of `U` and `Uᴴ`). -/
theorem continuous_channelRep :
    Continuous (channelRep : Matrix (Fin 8) (Fin 8) ℂ → Matrix PauliLabel PauliLabel ℂ) := by
  apply continuous_matrix
  intro r s
  simp only [channelRep_eq_trace]
  fun_prop

/-! ## 2. Faithfulness (up to scalar): `Û = 1 ⟹ U` is a scalar -/

/-- **The channel rep is faithful up to a global scalar**: if a unitary `M`'s channel representation is
the identity, then `M` is a scalar multiple of the identity. (`Û = 1` says `M` conjugates every Pauli to
itself, so `M` commutes with the Pauli basis, hence with everything — the center of `M₈(ℂ)` is the
scalars.) -/
theorem channelRep_eq_one_imp_scalar {M : Matrix (Fin 8) (Fin 8) ℂ} (hM : Mᴴ * M = 1)
    (h : channelRep M = 1) : ∃ c : ℂ, M = c • 1 := by
  have hconj : ∀ s, M * kronK8 s * Mᴴ = kronK8 s := by
    intro s
    rw [channelRep_conjAction_eq M s, h, Finset.sum_eq_single s]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro t _ ht; rw [Matrix.one_apply_ne ht, zero_smul]
    · intro hcontra; exact absurd (Finset.mem_univ s) hcontra
  have hcomm : ∀ s, M * kronK8 s = kronK8 s * M := by
    intro s
    have h2 : (M * kronK8 s * Mᴴ) * M = kronK8 s * M := by rw [hconj s]
    rwa [Matrix.mul_assoc (M * kronK8 s) Mᴴ M, hM, Matrix.mul_one] at h2
  have hcenter : M ∈ Set.center (Matrix (Fin 8) (Fin 8) ℂ) := by
    rw [Semigroup.mem_center_iff]
    intro X
    conv_lhs => rw [← kronK8Basis_sum_repr X]
    conv_rhs => rw [← kronK8Basis_sum_repr X]
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by
      rw [Matrix.smul_mul, Matrix.mul_smul, hcomm s]
  rw [Matrix.center_eq_range ℂ] at hcenter
  obtain ⟨c, hc⟩ := hcenter
  refine ⟨c, ?_⟩
  rw [← hc]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.diagonal_apply]

/-! ## 3. The channel rep of the seed has infinite order -/

/-- `channelRep` respects powers (it is a monoid homomorphism). -/
theorem channelRep_pow (A : Matrix (Fin 8) (Fin 8) ℂ) (n : ℕ) :
    channelRep (A ^ n) = channelRep A ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, channelRep_one]
  | succ k ih => rw [pow_succ, pow_succ, channelRep_mul, ih]

/-- **The channel rep of the seed has infinite order**: `(channelRep g_lit)ᵐ ≠ 1` for every `0 < m`.
If some power were `1`, faithfulness would force `g_litᵐ` to be a scalar `c • 1` with `c⁸ = 1`
(determinant), whence `g_lit^(8m) = 1` — contradicting the seed's infinite order
(`seedSU8_val_pow_ne_one`). -/
theorem channelRep_seedSU8_pow_ne_one (m : ℕ) (hm : 0 < m) :
    channelRep seedSU8.val ^ m ≠ 1 := by
  intro he
  rw [← channelRep_pow] at he
  have hunit : (seedSU8.val ^ m)ᴴ * (seedSU8.val ^ m) = 1 := by
    have hmem : (seedSU8 ^ m).val ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
      (Matrix.mem_specialUnitaryGroup_iff.mp (seedSU8 ^ m).2).1
    have hpow : (seedSU8 ^ m).val = seedSU8.val ^ m := SubmonoidClass.coe_pow seedSU8 m
    rw [← hpow, ← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hmem
  obtain ⟨c, hc⟩ := channelRep_eq_one_imp_scalar hunit he
  -- determinant: c^8 = 1
  have hdet1 : (seedSU8.val ^ m).det = 1 := by
    rw [Matrix.det_pow, (Matrix.mem_specialUnitaryGroup_iff.mp seedSU8.2).2, one_pow]
  have hc8 : c ^ 8 = 1 := by
    have := hdet1
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one] at this
    simpa using this
  -- (seedSU8.val ^ m) ^ 8 = 1
  have hpow8 : seedSU8.val ^ (m * 8) = 1 := by
    rw [pow_mul, hc, smul_pow, one_pow, hc8, one_smul]
  exact seedSU8_val_pow_ne_one (m * 8) (by positivity) hpow8

/-! ## 4. The capstone: `⟨H, S, CNOT⟩` is not dense in SU(8) -/

/-- **Every `SU(8)` matrix reachable as a limit of Clifford-only words has a signed-permutation channel
rep.** If `⟨H,S,CNOT⟩` were dense, then `channelRep U` (for *any* `U ∈ SU(8)`) would lie in the closure
of the channel-rep image of the Clifford-only words; that image is contained in the finite (hence closed)
set of signed permutations, so `channelRep U` is a signed permutation. -/
theorem channelRep_mem_signedPermSet_of_dense
    (hdense : SKEFTHawking.FKLW.GenericSUd.IsDenseInSUd_gs cliffordOnlyGeneratingSetSU8)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
    channelRep U.val ∈ (signedPermSet : Set (Matrix PauliLabel PauliLabel ℂ)) := by
  have hUclos : U.val ∈ closure (Set.range (fun w : FreeGroup (Fin 9) => (cliffordOnlyRho w).val)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨w, hw⟩ := hdense U ε hε
    refine ⟨(cliffordOnlyRho w).val, Set.mem_range_self w, ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    exact hw
  have hmem1 : channelRep U.val ∈
      closure (channelRep '' Set.range (fun w : FreeGroup (Fin 9) => (cliffordOnlyRho w).val)) :=
    image_closure_subset_closure_image continuous_channelRep ⟨U.val, hUclos, rfl⟩
  have hsubset : channelRep '' Set.range (fun w : FreeGroup (Fin 9) => (cliffordOnlyRho w).val)
      ⊆ signedPermSet := by
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact cliffordWord_channelRep_signedPerm w
  have hclosed : IsClosed (signedPermSet : Set (Matrix PauliLabel PauliLabel ℂ)) :=
    signedPermSet_finite.isClosed
  have := closure_mono hsubset hmem1
  rwa [hclosed.closure_eq] at this

/-- **Phase 6x′ capstone — the 6z CCZ-essentiality converse**: the literal Clifford-only generating set
`⟨H, S, CNOT⟩` (the Phase-6z alphabet with `CCZ` removed) is **not dense** in SU(8). This is the genuine
converse to the positive headline `cliffordCCZLiteral_dense`: `CCZ` is *essential* for density.

Mechanism (Mukhopadhyay Fact 3.9): the channel rep is a monoid homomorphism carrying every Clifford-only
word to a signed permutation matrix (`cliffordWord_channelRep_signedPerm`), of which there are only
finitely many (`signedPermSet_finite`). Were `⟨H,S,CNOT⟩` dense, continuity of `channelRep`
(`continuous_channelRep`) would force the channel rep of *every* `SU(8)` element into that finite set —
in particular every power of the infinite-order seed `g_lit = CCZ·H₁H₂H₃`. But the seed's channel rep has
infinite order (`channelRep_seedSU8_pow_ne_one`), giving infinitely many distinct signed permutations: a
contradiction. -/
theorem cliffordOnly_not_dense :
    ¬ SKEFTHawking.FKLW.GenericSUd.IsDenseInSUd_gs cliffordOnlyGeneratingSetSU8 := by
  intro hdense
  -- The powers of the seed's channel rep all land in the finite signed-permutation set …
  have hrange_sub : Set.range (fun n : ℕ => channelRep seedSU8.val ^ n)
      ⊆ (signedPermSet : Set (Matrix PauliLabel PauliLabel ℂ)) := by
    rintro _ ⟨n, rfl⟩
    show channelRep seedSU8.val ^ n ∈ signedPermSet
    rw [← channelRep_pow, ← SubmonoidClass.coe_pow]
    exact channelRep_mem_signedPermSet_of_dense hdense (seedSU8 ^ n)
  have hfin : (Set.range (fun n : ℕ => channelRep seedSU8.val ^ n)).Finite :=
    signedPermSet_finite.subset hrange_sub
  -- … yet there are infinitely many of them (the seed's channel rep has infinite order).
  have hunit : IsUnit (channelRep seedSU8.val) := by
    have hmem : seedSU8.val ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
      (Matrix.mem_specialUnitaryGroup_iff.mp seedSU8.2).1
    refine channelRep_isUnit seedSU8.val ?_ ?_
    · rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hmem
    · rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hmem
  have hcontra : ∀ p q : ℕ, p < q →
      channelRep seedSU8.val ^ p = channelRep seedSU8.val ^ q → False := by
    intro p q hpq hpq_eq
    have hstep : channelRep seedSU8.val ^ p * channelRep seedSU8.val ^ (q - p)
        = channelRep seedSU8.val ^ p := by
      rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hpq), ← hpq_eq]
    have hkey : channelRep seedSU8.val ^ (q - p) = 1 :=
      ((hunit.pow p).mul_right_inj).mp (by rw [hstep, mul_one])
    exact channelRep_seedSU8_pow_ne_one (q - p) (by omega) hkey
  have hni : ¬ Function.Injective (fun n : ℕ => channelRep seedSU8.val ^ n) :=
    fun hinj => Set.infinite_range_of_injective hinj hfin
  rw [Function.not_injective_iff] at hni
  obtain ⟨a, b, heq, hne⟩ := hni
  rcases lt_or_gt_of_ne hne with h | h
  · exact hcontra a b h heq
  · exact hcontra b a h heq.symm

end SKEFTHawking.FKLW.MukhopadhyayCCZ
