/-
# Phase 5q.H (E1 integral topology) — the relative cohomology MV connecting map δ (torsion-safe)

Integral (`ZMod 2 → ℤ`) construction of the relative cohomology Mayer–Vietoris connecting map + the two
remaining exactness spots — the **torsion-safe** route (the mod-2 `SingularRelativeCohomologyMVConnecting`
dualizes the homology connecting through the PERFECT Kronecker pairing `relKroneckerHEquiv`, field-only; see
the DECISIONS entry). Here the connecting map is the **snake of the cochain-level MV SES**
`0 → C*(M,U∪V) --Δ--> C*(M,U)⊕C*(M,V) --Σ--> C*(M,U∩V) → 0`, whose exactness is the field-UC-free
`SingularRelativeCochainMVExactInt.mvCochain_dual_exact`.

This module (brick 1) builds the **cochain-level MV maps** `relCochainMvDiagInt` (`Δ`, the restriction from
`U∪V`; injective — restriction is the antitone *inclusion* `relCochainsInt(U∪V) ↪ relCochainsInt(U)`) and
`relCochainMvSumInt` (`Σ`, the honest ℤ-difference of the restrictions to `U∩V`; surjective via the explicit
indicator split `relCochainMvSum_surjectiveInt`), plus the cochain-complex condition `Σ ∘ Δ = 0`. These are
the top/bottom of the snake; the connecting map + exactness follow.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomologyRestrictInt
import SKEFTHawking.SingularRelativeCochainMVSurjInt
import SKEFTHawking.SingularExcisionIsoInt

open CategoryTheory Opposite
open scoped Classical
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularRelativeCohomologyRestrictInt
open SKEFTHawking.SingularRelativeCochainMVSurjInt

namespace SKEFTHawking.SingularRelativeCohomologyMVConnectingInt

variable {M : TopCat}

/-- **The cochain-level relative MV diagonal** `Δ : Cⁿ(M,U∪V;ℤ) → Cⁿ(M,U;ℤ) ⊕ Cⁿ(M,V;ℤ)`, the pair of
cochain restrictions `U∪V ↠ U`, `U∪V ↠ V`. -/
noncomputable def relCochainMvDiagInt (U V : Set ↑M) (n : ℕ) :
    relCochainsInt (U ∪ V) n →ₗ[ℤ] relCochainsInt U n × relCochainsInt V n :=
  (relCochainRestrictInt Set.subset_union_left n).prod (relCochainRestrictInt Set.subset_union_right n)

/-- **The cochain-level relative MV sum** `Σ : Cⁿ(M,U;ℤ) ⊕ Cⁿ(M,V;ℤ) → Cⁿ(M,U∩V;ℤ)`, the honest
ℤ-DIFFERENCE of the restrictions `U ↠ U∩V`, `V ↠ U∩V`. -/
noncomputable def relCochainMvSumInt (U V : Set ↑M) (n : ℕ) :
    relCochainsInt U n × relCochainsInt V n →ₗ[ℤ] relCochainsInt (U ∩ V) n :=
  (relCochainRestrictInt Set.inter_subset_left n).coprod
    (-relCochainRestrictInt Set.inter_subset_right n)

@[simp] theorem relCochainMvSumInt_apply (U V : Set ↑M) (n : ℕ)
    (x : relCochainsInt U n) (y : relCochainsInt V n) :
    relCochainMvSumInt U V n (x, y)
      = relCochainRestrictInt Set.inter_subset_left n x
        - relCochainRestrictInt Set.inter_subset_right n y := by
  rw [relCochainMvSumInt, LinearMap.coprod_apply, LinearMap.neg_apply, sub_eq_add_neg]

@[simp] theorem relCochainMvDiagInt_apply (U V : Set ↑M) (n : ℕ) (f : relCochainsInt (U ∪ V) n) :
    relCochainMvDiagInt U V n f
      = (relCochainRestrictInt Set.subset_union_left n f,
          relCochainRestrictInt Set.subset_union_right n f) :=
  rfl

/-- **`Δ` is injective**: its first component `relCochainRestrictInt (U ⊆ U∪V)` is the antitone submodule
inclusion, itself injective (identity on the underlying cochain). -/
theorem relCochainMvDiagInt_injective (U V : Set ↑M) (n : ℕ) :
    Function.Injective (relCochainMvDiagInt U V n) := by
  intro f g h
  apply Subtype.ext
  have h1 := congrArg Prod.fst h
  simpa only [relCochainMvDiagInt_apply, relCochainRestrictInt_coe] using congrArg Subtype.val h1

/-- **`Σ` is surjective**: every `g : Cⁿ(M,U∩V;ℤ)` is `gU − gV` (the explicit indicator split
`relCochainMvSum_surjectiveInt`). -/
theorem relCochainMvSumInt_surjective (U V : Set ↑M) (n : ℕ) :
    Function.Surjective (relCochainMvSumInt U V n) := by
  intro g
  obtain ⟨gU, gV, hg⟩ := relCochainMvSum_surjectiveInt U V n g
  refine ⟨(gU, gV), ?_⟩
  apply Subtype.ext
  rw [relCochainMvSumInt_apply, AddSubgroupClass.coe_sub, relCochainRestrictInt_coe,
    relCochainRestrictInt_coe, hg]

/-- **The cochain-complex condition `Σ ∘ Δ = 0`**: both routes `(M,U∪V) → (M,U∩V)` are the single
restriction, so the ℤ-difference is `c − c = 0`. -/
theorem relCochainMvSumInt_relCochainMvDiagInt (U V : Set ↑M) (n : ℕ)
    (f : relCochainsInt (U ∪ V) n) :
    relCochainMvSumInt U V n (relCochainMvDiagInt U V n f) = 0 := by
  apply Subtype.ext
  rw [relCochainMvDiagInt_apply, relCochainMvSumInt_apply, ZeroMemClass.coe_zero,
    AddSubgroupClass.coe_sub]
  simp only [relCochainRestrictInt_coe]
  rw [sub_self]

/-! ## §2. The linear indicator section of `Σ` (the split feeding the connecting-map snake) -/

/-- The **indicator `U`-part** of a cochain: `σ ↦ (if σ's image ⊆ U then 0 else g σ)`. Linear in `g`, always a
`U`-relative cochain; the `U`-component of the linear section of `relCochainMvSumInt`. -/
noncomputable def indUf (U : Set ↑M) (n : ℕ) (g : SingularCochainInt M n) : SingularCochainInt M n :=
  fun σ => if Set.range (M.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ U then 0 else g σ

theorem indUf_apply (U : Set ↑M) (n : ℕ) (g : SingularCochainInt M n)
    (σ : (TopCat.toSSet.obj M).obj (op (SimplexCategory.mk n))) :
    indUf U n g σ = if Set.range (M.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ U then 0 else g σ :=
  rfl

theorem indUf_add (U : Set ↑M) (n : ℕ) (f g : SingularCochainInt M n) :
    indUf U n (f + g) = indUf U n f + indUf U n g := by
  funext σ; simp only [indUf_apply, Pi.add_apply]; split_ifs <;> ring

theorem indUf_smul (U : Set ↑M) (n : ℕ) (s : ℤ) (g : SingularCochainInt M n) :
    indUf U n (s • g) = s • indUf U n g := by
  funext σ; simp only [indUf_apply, Pi.smul_apply]; split_ifs <;> simp

theorem indUf_mem (U : Set ↑M) (n : ℕ) (g : SingularCochainInt M n) :
    indUf U n g ∈ relCochainsInt U n := by
  rw [mem_relCochainsInt]
  intro c hc
  refine kronecker_eq_zero_of_support _ _ (fun σ hσ => ?_)
  rw [indUf_apply, if_pos (range_of_mem_subspaceChainsInt hc hσ)]

theorem indVf_mem (U V : Set ↑M) (n : ℕ) (g : relCochainsInt (U ∩ V) n) :
    indUf U n (g : SingularCochainInt M n) - (g : SingularCochainInt M n) ∈ relCochainsInt V n := by
  rw [mem_relCochainsInt]
  intro c hc
  refine kronecker_eq_zero_of_support _ _ (fun σ hσ => ?_)
  have hVσ := range_of_mem_subspaceChainsInt hc hσ
  simp only [Pi.sub_apply, indUf_apply]
  by_cases hPσ : Set.range (M.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ U
  · have hUV : Finsupp.single σ (1 : ℤ) ∈ subspaceChainsInt (U ∩ V) n :=
      mem_subspaceChainsInt_of_support (fun τ hτ => by
        rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hτ
        subst hτ; exact Set.subset_inter hPσ hVσ)
    have hg0 : (g : SingularCochainInt M n) σ = 0 := by
      have := g.2 _ hUV; rwa [kronecker_single, one_mul] at this
    rw [if_pos hPσ, hg0, sub_zero]
  · rw [if_neg hPσ, sub_self]

/-- **The linear indicator section** `relCochainsInt(U∩V) n →ₗ relCochainsInt(U) n × relCochainsInt(V) n` of
`relCochainMvSumInt`: `g ↦ (indUf g, indUf g − g)`. Linear (the indicator `indUf` is linear in `g`) and a
genuine section: `relCochainMvSumInt ∘ section = id`. -/
noncomputable def relCochainMvSectionInt (U V : Set ↑M) (n : ℕ) :
    relCochainsInt (U ∩ V) n →ₗ[ℤ] relCochainsInt U n × relCochainsInt V n where
  toFun g := (⟨indUf U n g, indUf_mem U n g⟩,
    ⟨indUf U n g - (g : SingularCochainInt M n), indVf_mem U V n g⟩)
  map_add' g₁ g₂ := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show indUf U n ((g₁ + g₂ : relCochainsInt (U ∩ V) n) : SingularCochainInt M n)
          = indUf U n (g₁ : SingularCochainInt M n) + indUf U n (g₂ : SingularCochainInt M n)
      rw [Submodule.coe_add, indUf_add]
    · show indUf U n ((g₁ + g₂ : relCochainsInt (U ∩ V) n) : SingularCochainInt M n)
            - ((g₁ + g₂ : relCochainsInt (U ∩ V) n) : SingularCochainInt M n)
          = (indUf U n (g₁ : SingularCochainInt M n) - (g₁ : SingularCochainInt M n))
            + (indUf U n (g₂ : SingularCochainInt M n) - (g₂ : SingularCochainInt M n))
      rw [Submodule.coe_add, indUf_add]; abel
  map_smul' s g := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show indUf U n ((s • g : relCochainsInt (U ∩ V) n) : SingularCochainInt M n)
          = s • indUf U n (g : SingularCochainInt M n)
      rw [SetLike.val_smul, indUf_smul]
    · show indUf U n ((s • g : relCochainsInt (U ∩ V) n) : SingularCochainInt M n)
            - ((s • g : relCochainsInt (U ∩ V) n) : SingularCochainInt M n)
          = s • (indUf U n (g : SingularCochainInt M n) - (g : SingularCochainInt M n))
      rw [SetLike.val_smul, indUf_smul, smul_sub]

/-- **The indicator section is a section** of `relCochainMvSumInt`: `Σ ∘ section = id`. -/
theorem relCochainMvSumInt_section (U V : Set ↑M) (n : ℕ) (g : relCochainsInt (U ∩ V) n) :
    relCochainMvSumInt U V n (relCochainMvSectionInt U V n g) = g := by
  have hfst : (relCochainMvSectionInt U V n g).1 = ⟨indUf U n g, indUf_mem U n g⟩ := rfl
  have hsnd : (relCochainMvSectionInt U V n g).2
      = ⟨indUf U n g - (g : SingularCochainInt M n), indVf_mem U V n g⟩ := rfl
  apply Subtype.ext
  rw [show relCochainMvSectionInt U V n g
      = ((relCochainMvSectionInt U V n g).1, (relCochainMvSectionInt U V n g).2) from rfl,
    relCochainMvSumInt_apply, hfst, hsnd, AddSubgroupClass.coe_sub, relCochainRestrictInt_coe,
    relCochainRestrictInt_coe]
  exact sub_sub_cancel _ _

end SKEFTHawking.SingularRelativeCohomologyMVConnectingInt
