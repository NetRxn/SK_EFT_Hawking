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
import SKEFTHawking.SingularQCohomologyInt
import SKEFTHawking.SingularQCohomologyExcisionInt

open CategoryTheory Opposite
open scoped Classical
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularRelativeCohomologyRestrictInt
open SKEFTHawking.SingularRelativeCochainMVSurjInt
open SKEFTHawking.SingularRelativeMVInt
open SKEFTHawking.SingularQCohomologyInt
open SKEFTHawking.SingularQCohomologyExcisionInt
open SKEFTHawking.SingularRelativeCohomologyMVInt
open SKEFTHawking.SingularCohomMvMiddleInt (mk_eq_of_coboundary_diff)

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

/-! ## §3. The middle map `ω ↦ [coboundary(indUf ω)] ∈ QCohom` and the connecting map δ -/

/-- `coboundary(indUf ω) ∈ relCochainsInt(U)` — `indUf ω` is a `U`-relative cochain, `δ` preserves. -/
theorem coboundary_indUf_mem_U (U : Set ↑M) (n : ℕ) (ω : SingularCochainInt M n) :
    coboundary M n (indUf U n ω) ∈ relCochainsInt U (n + 1) :=
  coboundary_mem_relCochainsInt U n (indUf U n ω) (indUf_mem U n ω)

/-- `coboundary(indUf ω) ∈ relCochainsInt(V)` for `ω` a cocycle: `= coboundary(indUf ω − ω)` (since `δω=0`)
and `indUf ω − ω` is a `V`-relative cochain (`indVf_mem`). -/
theorem coboundary_indUf_mem_V (U V : Set ↑M) (n : ℕ) (ω : relCochainsInt (U ∩ V) n)
    (hω : coboundary M n (ω : SingularCochainInt M n) = 0) :
    coboundary M n (indUf U n (ω : SingularCochainInt M n)) ∈ relCochainsInt V (n + 1) := by
  have hval : coboundary M n (indUf U n (ω : SingularCochainInt M n))
      = coboundary M n (indUf U n (ω : SingularCochainInt M n) - (ω : SingularCochainInt M n)) := by
    show coboundaryₗ M n (indUf U n (ω : SingularCochainInt M n))
        = coboundaryₗ M n (indUf U n (ω : SingularCochainInt M n) - (ω : SingularCochainInt M n))
    rw [map_sub]
    show coboundary M n (indUf U n (ω : SingularCochainInt M n))
        = coboundary M n (indUf U n (ω : SingularCochainInt M n)) - coboundary M n (ω : SingularCochainInt M n)
    rw [hω, sub_zero]
  rw [hval]
  exact coboundary_mem_relCochainsInt V n _ (indVf_mem U V n ω)

/-- `coboundary(indUf ω) ∈ mvUnionCochains` for `ω` a cocycle (vanishes on `C(U)` and `C(V)`). -/
theorem coboundary_indUf_mem_mvUnion (U V : Set ↑M) (n : ℕ) (ω : relCochainsInt (U ∩ V) n)
    (hω : coboundary M n (ω : SingularCochainInt M n) = 0) :
    coboundary M n (indUf U n (ω : SingularCochainInt M n)) ∈ mvUnionCochainsInt U V (n + 1) := by
  rw [mem_mvUnionCochainsInt]
  intro c hc
  rw [mvUnionChainsInt, Submodule.add_eq_sup, Submodule.mem_sup] at hc
  obtain ⟨cU, hcU, cV, hcV, rfl⟩ := hc
  rw [kronecker_add_right, coboundary_indUf_mem_U U n (ω : SingularCochainInt M n) cU hcU,
    coboundary_indUf_mem_V U V n ω hω cV hcV, add_zero]

/-- The indicator `U`-part as a `LinearMap`. -/
noncomputable def indUfₗ (U : Set ↑M) (n : ℕ) : SingularCochainInt M n →ₗ[ℤ] SingularCochainInt M n where
  toFun := indUf U n
  map_add' := indUf_add U n
  map_smul' := indUf_smul U n

/-- The raw middle cochain `ω ↦ coboundary(indUf ω)` on cocycles (a plain ℤ-linear map). -/
noncomputable def midCochainRawInt (U V : Set ↑M) (n : ℕ) :
    LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (n + 1)) →ₗ[ℤ] SingularCochainInt M (n + 2) :=
  (coboundaryₗ M (n + 1)).comp ((indUfₗ U (n + 1)).comp
    ((relCochainsInt (U ∩ V) (n + 1)).subtype.comp
      (LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (n + 1))).subtype))

theorem midCochainRawInt_apply (U V : Set ↑M) (n : ℕ)
    (ω : LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (n + 1))) :
    midCochainRawInt U V n ω
      = coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1))) :=
  rfl

theorem midCochainRawInt_mem (U V : Set ↑M) (n : ℕ)
    (ω : LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (n + 1))) :
    midCochainRawInt U V n ω ∈ mvUnionCochainsInt U V (n + 2) := by
  rw [midCochainRawInt_apply]
  refine coboundary_indUf_mem_mvUnion U V (n + 1) ω.1 ?_
  have h := ω.2
  rw [LinearMap.mem_ker] at h
  have h2 := congrArg (fun x : relCochainsInt (U ∩ V) (n + 2) => (x : SingularCochainInt M (n + 2))) h
  simp only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] at h2
  exact h2

/-- The middle map on cocycles `ω ↦ ⟨coboundary(indUf ω), Q-cocycle⟩ : ker δ_{U∩V} → ker δ_Q`. -/
noncomputable def midCocycleInt (U V : Set ↑M) (n : ℕ) :
    LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (n + 1)) →ₗ[ℤ]
      LinearMap.ker (qCoboundaryIntₗ U V (n + 2)) :=
  ((midCochainRawInt U V n).codRestrict (mvUnionCochainsInt U V (n + 2))
    (midCochainRawInt_mem U V n)).codRestrict (LinearMap.ker (qCoboundaryIntₗ U V (n + 2))) (fun ω => by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      show coboundary M (n + 2) (midCochainRawInt U V n ω) = 0
      rw [midCochainRawInt_apply, coboundary_comp_coboundary])

@[simp] theorem midCocycleInt_coe (U V : Set ↑M) (n : ℕ)
    (ω : LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (n + 1))) :
    ((midCocycleInt U V n ω : mvUnionCochainsInt U V (n + 2)) : SingularCochainInt M (n + 2))
      = coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1))) :=
  rfl

/-- **The snake well-definedness** (`midCocycleInt` sends coboundaries to Q-coboundaries): if `ω.1 = δτ`
then `coboundary(indUf(δτ)) = qCoboundary(w)` with `w := indUf(δτ) − δ(indUf τ) ∈ relC(U) ∩ relC(V) =
mvUnion` (the `relC(V)` leg uses `w = (indUf(δτ)−δτ) − δ(indUf τ − τ)` + `δτ = coboundary τ`). -/
theorem midCocycleInt_submoduleOf_le (U V : Set ↑M) (n : ℕ) :
    (relCoboundaryRangeInt (U ∩ V) (n + 1)).submoduleOf
        (LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (n + 1))) ≤
      Submodule.comap (midCocycleInt U V n)
        ((qCoboundaryRangeInt U V (n + 2)).submoduleOf
          (LinearMap.ker (qCoboundaryIntₗ U V (n + 2)))) := by
  intro ω hω
  rw [Submodule.mem_comap]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hω ⊢
  rw [show relCoboundaryRangeInt (U ∩ V) (n + 1) = LinearMap.range (relCoboundaryIntₗ (U ∩ V) n) from rfl,
    LinearMap.mem_range] at hω
  obtain ⟨τ, hτ⟩ := hω
  have hτcob : coboundary M n (τ : SingularCochainInt M n) = (ω : SingularCochainInt M (n + 1)) := by
    have h := congrArg (fun x : relCochainsInt (U ∩ V) (n + 1) => (x : SingularCochainInt M (n + 1))) hτ
    simpa only [relCoboundaryIntₗ_coe] using h
  set w : SingularCochainInt M (n + 1) :=
    indUf U (n + 1) (ω : SingularCochainInt M (n + 1))
      - coboundary M n (indUf U n (τ : SingularCochainInt M n)) with hw
  have hwU : w ∈ relCochainsInt U (n + 1) :=
    Submodule.sub_mem _ (indUf_mem U (n + 1) _) (coboundary_indUf_mem_U U n _)
  have hwV : w ∈ relCochainsInt V (n + 1) := by
    have hid : w = (indUf U (n + 1) (ω : SingularCochainInt M (n + 1)) - (ω : SingularCochainInt M (n + 1)))
        - coboundary M n (indUf U n (τ : SingularCochainInt M n) - (τ : SingularCochainInt M n)) := by
      have hsub : coboundary M n (indUf U n (τ : SingularCochainInt M n) - (τ : SingularCochainInt M n))
          = coboundary M n (indUf U n (τ : SingularCochainInt M n))
            - coboundary M n (τ : SingularCochainInt M n) := by
        show coboundaryₗ M n (indUf U n (τ : SingularCochainInt M n) - (τ : SingularCochainInt M n))
            = coboundaryₗ M n (indUf U n (τ : SingularCochainInt M n)) - coboundaryₗ M n (τ : SingularCochainInt M n)
        exact map_sub _ _ _
      rw [hw, hsub, hτcob]; abel
    rw [hid]
    exact Submodule.sub_mem _ (indVf_mem U V (n + 1) ω)
      (coboundary_mem_relCochainsInt V n _ (indVf_mem U V n τ))
  have hwmv : w ∈ mvUnionCochainsInt U V (n + 1) := by
    rw [mem_mvUnionCochainsInt]
    intro c hc
    rw [mvUnionChainsInt, Submodule.add_eq_sup, Submodule.mem_sup] at hc
    obtain ⟨cU, hcU, cV, hcV, rfl⟩ := hc
    rw [kronecker_add_right, hwU cU hcU, hwV cV hcV, add_zero]
  rw [show qCoboundaryRangeInt U V (n + 2) = LinearMap.range (qCoboundaryIntₗ U V (n + 1)) from rfl,
    LinearMap.mem_range]
  refine ⟨⟨w, hwmv⟩, ?_⟩
  apply Subtype.ext
  rw [qCoboundaryIntₗ_coe, midCocycleInt_coe]
  show coboundary M (n + 1) w = coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1)))
  rw [hw]
  show coboundaryₗ M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1))
        - coboundary M n (indUf U n (τ : SingularCochainInt M n)))
      = coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1)))
  rw [map_sub]
  show coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1)))
        - coboundary M (n + 1) (coboundary M n (indUf U n (τ : SingularCochainInt M n)))
      = coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1)))
  rw [coboundary_comp_coboundary, sub_zero]

/-- The snake middle on cohomology `RelCohom(U∩V)(n+1) →ₗ QCohom(n+2)` (descends `midCocycleInt`). -/
noncomputable def midCohomInt (U V : Set ↑M) (n : ℕ) :
    RelativeCohomologyInt (U ∩ V) (n + 1) →ₗ[ℤ] QCohomologyInt U V (n + 2) :=
  Submodule.mapQ _ _ (midCocycleInt U V n) (midCocycleInt_submoduleOf_le U V n)

/-- **The relative cohomology Mayer–Vietoris connecting map** `δ : Hᵏ(M|U∩V;ℤ) →ₗ Hᵏ⁺¹(M|U∪V;ℤ)`
(`k = n+1`), torsion-safe: the snake middle `midCohomInt` (into `QCohom`) followed by the **inverse of the
dual excision iso** `dualExcisionEquivInt`. This closes the top row of the integral Poincaré-duality
`5`-lemma without the field-only perfect Kronecker pairing. -/
noncomputable def relCohomMvConnectingInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    RelativeCohomologyInt (U ∩ V) (n + 1) →ₗ[ℤ] RelativeCohomologyInt (U ∪ V) (n + 2) :=
  (dualExcisionEquivInt U V hU hV n).symm.toLinearMap.comp (midCohomInt U V n)

/-! ## §4. The two remaining relative-cohomology MV LES exactness spots (torsion-safe snake) -/

/-- `indUf U g = g` for `g` already a `U`-relative cochain (the indicator zeroes exactly the simplices `g`
already vanishes on). -/
theorem indUf_eq_self_of_mem (U : Set ↑M) (n : ℕ) (g : SingularCochainInt M n)
    (hg : g ∈ relCochainsInt U n) : indUf U n g = g := by
  funext σ
  rw [indUf_apply]
  by_cases hσ : Set.range (M.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ U
  · rw [if_pos hσ]
    have hmem : Finsupp.single σ (1 : ℤ) ∈ subspaceChainsInt U n :=
      mem_subspaceChainsInt_of_support (fun τ hτ => by
        rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hτ
        subst hτ; exact hσ)
    have := (mem_relCochainsInt U n g).mp hg _ hmem
    rw [kronecker_single, one_mul] at this
    exact this.symm
  · rw [if_neg hσ]

/-- The `Q`-cochains sit inside the `U`-relative cochains (vanishing on `C(U)+C(V) ⊇ C(U)`). -/
theorem mvUnionCochainsInt_le_relCochainsInt_left (U V : Set ↑M) (n : ℕ) :
    mvUnionCochainsInt U V n ≤ relCochainsInt U n := by
  intro f hf
  rw [mem_relCochainsInt]
  intro c hc
  exact hf c (by rw [mvUnionChainsInt, Submodule.add_eq_sup]; exact Submodule.mem_sup_left hc)

/-- The `Q`-cochains sit inside the `V`-relative cochains (vanishing on `C(U)+C(V) ⊇ C(V)`). -/
theorem mvUnionCochainsInt_le_relCochainsInt_right (U V : Set ↑M) (n : ℕ) :
    mvUnionCochainsInt U V n ≤ relCochainsInt V n := by
  intro f hf
  rw [mem_relCochainsInt]
  intro c hc
  exact hf c (by rw [mvUnionChainsInt, Submodule.add_eq_sup]; exact Submodule.mem_sup_right hc)

/-- **Workhorse**: for `g` a `V`-relative cochain, `indUf U g` lands in the `Q`-cochains `mvUnion` — it is
`U`-relative (`indUf_mem`) and `V`-relative (`g` and `indUf U g − g` both are, via `indVf_mem`). -/
theorem indUf_mem_mvUnion (U V : Set ↑M) (n : ℕ) (g : SingularCochainInt M n)
    (hg : g ∈ relCochainsInt V n) : indUf U n g ∈ mvUnionCochainsInt U V n := by
  rw [mem_mvUnionCochainsInt]
  intro c hc
  rw [mvUnionChainsInt, Submodule.add_eq_sup, Submodule.mem_sup] at hc
  obtain ⟨cU, hcU, cV, hcV, rfl⟩ := hc
  rw [kronecker_add_right]
  have hU0 : kronecker (indUf U n g) cU = 0 := (mem_relCochainsInt U n _).mp (indUf_mem U n g) cU hcU
  have hgUV : g ∈ relCochainsInt (U ∩ V) n := relCochainsInt_antitone Set.inter_subset_right n hg
  have hindV : indUf U n g ∈ relCochainsInt V n := by
    have hdiff : indUf U n g - g ∈ relCochainsInt V n := indVf_mem U V n ⟨g, hgUV⟩
    have hrw : indUf U n g = (indUf U n g - g) + g := by abel
    rw [hrw]; exact Submodule.add_mem _ hdiff hg
  have hV0 : kronecker (indUf U n g) cV = 0 := (mem_relCochainsInt V n _).mp hindV cV hcV
  rw [hU0, hV0, add_zero]

/-- `midCohomInt` on a class: `midCohomInt [ω] = [midCocycleInt ω]_Q` (the `mapQ` computation rule). -/
theorem midCohomInt_mk (U V : Set ↑M) (n : ℕ)
    (ω : LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (n + 1))) :
    midCohomInt U V n (RelativeCohomologyInt.mk (U ∩ V) (n + 1) ω)
      = QCohomologyInt.mk U V (n + 2) (midCocycleInt U V n ω) := rfl

/-- The connecting map's application rule (`δ = dualExcision⁻¹ ∘ midCohom`). -/
theorem relCohomMvConnectingInt_apply (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (x : RelativeCohomologyInt (U ∩ V) (n + 1)) :
    relCohomMvConnectingInt U V hU hV n x
      = (dualExcisionEquivInt U V hU hV n).symm (midCohomInt U V n x) := rfl

/-- `δ x = 0 ↔ midCohomInt x = 0` (the dual excision iso is injective). -/
theorem relCohomMvConnectingInt_eq_zero_iff (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (x : RelativeCohomologyInt (U ∩ V) (n + 1)) :
    relCohomMvConnectingInt U V hU hV n x = 0 ↔ midCohomInt U V n x = 0 := by
  rw [relCohomMvConnectingInt_apply, LinearEquiv.map_eq_zero_iff]

/-- `indUf` is subtractive (mirror of `indUf_add`). -/
theorem indUf_sub (U : Set ↑M) (n : ℕ) (f g : SingularCochainInt M n) :
    indUf U n (f - g) = indUf U n f - indUf U n g := by
  funext σ; simp only [indUf_apply, Pi.sub_apply]; split_ifs <;> ring

/-- **`δ ∘ Σ = 0`** (`range Σ ⊆ ker δ`): for `β` a `V`-cocycle, `indUf U β ∈ mvUnion`, so the middle cochain
`coboundary(indUf U (α−β)) = −coboundary(indUf U β)` is a `Q`-coboundary, killing the class in `QCohom`. -/
theorem relCohomMvConnectingInt_relCohomMvSumInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (p : RelativeCohomologyInt U (n + 1) × RelativeCohomologyInt V (n + 1)) :
    relCohomMvConnectingInt U V hU hV n (relCohomMvSumInt U V (n + 1) p) = 0 := by
  obtain ⟨A, B⟩ := p
  obtain ⟨α, rfl⟩ := RelativeCohomologyInt.mk_surjective U (n + 1) A
  obtain ⟨β, rfl⟩ := RelativeCohomologyInt.mk_surjective V (n + 1) B
  set ω : LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (n + 1)) :=
    relCocycleRestrictInt Set.inter_subset_left (n + 1) α
      - relCocycleRestrictInt Set.inter_subset_right (n + 1) β with hω
  have hSum : relCohomMvSumInt U V (n + 1)
      (RelativeCohomologyInt.mk U (n + 1) α, RelativeCohomologyInt.mk V (n + 1) β)
      = RelativeCohomologyInt.mk (U ∩ V) (n + 1) ω := by
    rw [relCohomMvSumInt_apply, relCohomRestrictInt_mk, relCohomRestrictInt_mk, hω]
    exact (Submodule.Quotient.mk_sub _).symm
  rw [hSum, relCohomMvConnectingInt_eq_zero_iff, midCohomInt_mk, QCohomologyInt.mk_eq_zero_iff]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
  -- underlying cochain of `ω` is `α − β`; middle cochain `= −coboundary(indUf U β)`, a `Q`-coboundary
  have hβV : (β : SingularCochainInt M (n + 1)) ∈ relCochainsInt V (n + 1) := β.1.2
  have hαcocy : coboundary M (n + 1) (α : SingularCochainInt M (n + 1)) = 0 := by
    have h := α.2; rw [LinearMap.mem_ker] at h
    have h2 := congrArg (fun x : relCochainsInt U (n + 2) => (x : SingularCochainInt M (n + 2))) h
    simpa only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] using h2
  have hωc : (ω : SingularCochainInt M (n + 1))
      = (α : SingularCochainInt M (n + 1)) - (β : SingularCochainInt M (n + 1)) := by
    rw [hω]
    simp only [AddSubgroupClass.coe_sub, relCocycleRestrictInt_coe, relCochainRestrictInt_coe]
  refine ⟨⟨-(indUf U (n + 1) (β : SingularCochainInt M (n + 1))),
    Submodule.neg_mem _ (indUf_mem_mvUnion U V (n + 1) _ hβV)⟩, ?_⟩
  apply Subtype.ext
  rw [qCoboundaryIntₗ_coe, midCocycleInt_coe, hωc, indUf_sub,
    indUf_eq_self_of_mem U (n + 1) (α : SingularCochainInt M (n + 1)) α.1.2]
  show coboundaryₗ M (n + 1) (-(indUf U (n + 1) (β : SingularCochainInt M (n + 1))))
      = coboundaryₗ M (n + 1) ((α : SingularCochainInt M (n + 1))
          - indUf U (n + 1) (β : SingularCochainInt M (n + 1)))
  rw [map_neg, map_sub]
  show -coboundary M (n + 1) (indUf U (n + 1) (β : SingularCochainInt M (n + 1)))
      = coboundary M (n + 1) (α : SingularCochainInt M (n + 1))
        - coboundary M (n + 1) (indUf U (n + 1) (β : SingularCochainInt M (n + 1)))
  rw [hαcocy, zero_sub]

/-- A restricted relative-cohomology class vanishes when its cocycle's cochain is the coboundary of an
`S`-relative cochain (`S ⊆ T`). The workhorse for `Δ ∘ δ = 0` (both restriction legs). -/
theorem relCohomRestrictInt_mk_eq_zero_of_coboundary {S T : Set ↑M} (h : S ⊆ T) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryIntₗ T (n + 1))) (p : SingularCochainInt M n)
    (hp : p ∈ relCochainsInt S n)
    (hzp : (z : SingularCochainInt M (n + 1)) = coboundary M n p) :
    relCohomRestrictInt h (n + 1) (RelativeCohomologyInt.mk T (n + 1) z) = 0 := by
  rw [relCohomRestrictInt_mk, RelativeCohomologyInt.mk_eq_zero_iff]
  simp only [relCoboundaryRangeInt, LinearMap.mem_range]
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  rw [relCoboundaryIntₗ_coe, relCocycleRestrictInt_coe, relCochainRestrictInt_coe]
  exact hzp.symm

/-- **`Δ ∘ δ = 0`** (`range δ ⊆ ker Δ`): a representative `z` of `δ[ω]` has cochain
`coboundary(indUf U ω) + coboundary(k')` = `coboundary(indUf U ω + k')` (a `U`-coboundary, `k' ∈ mvUnion`)
= `coboundary((indUf U ω − ω) + k')` (a `V`-coboundary, since `ω` is a cocycle), so both restrictions vanish. -/
theorem relCohomMvDiagInt_relCohomMvConnectingInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (x : RelativeCohomologyInt (U ∩ V) (n + 1)) :
    relCohomMvDiagInt U V (n + 2) (relCohomMvConnectingInt U V hU hV n x) = 0 := by
  obtain ⟨ω, rfl⟩ := RelativeCohomologyInt.mk_surjective (U ∩ V) (n + 1) x
  obtain ⟨z, hz⟩ := RelativeCohomologyInt.mk_surjective (U ∪ V) (n + 2)
    (relCohomMvConnectingInt U V hU hV n (RelativeCohomologyInt.mk (U ∩ V) (n + 1) ω))
  rw [← hz]
  -- `e (mk z) = midCohom (mk ω)`, giving `[incl z] = [coboundary(indUf U ω)]` in `QCohom`
  have hez : QCohomologyInt.mk U V (n + 2) (relToQCocycleInt U V (n + 2) z)
      = QCohomologyInt.mk U V (n + 2) (midCocycleInt U V n ω) := by
    have h1 : dualExcisionEquivInt U V hU hV n (RelativeCohomologyInt.mk (U ∪ V) (n + 2) z)
        = midCohomInt U V n (RelativeCohomologyInt.mk (U ∩ V) (n + 1) ω) := by
      rw [hz, relCohomMvConnectingInt_apply, LinearEquiv.apply_symm_apply]
    rwa [dualExcisionEquivInt_apply, dualExcisionInt_mk, midCohomInt_mk] at h1
  -- extract the `Q`-coboundary witness `k'`
  have hz0 : QCohomologyInt.mk U V (n + 2)
      (relToQCocycleInt U V (n + 2) z - midCocycleInt U V n ω) = 0 := by
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_sub, sub_eq_zero]; exact hez
  rw [QCohomologyInt.mk_eq_zero_iff] at hz0
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype, qCoboundaryRangeInt,
    LinearMap.mem_range] at hz0
  obtain ⟨k', hk'⟩ := hz0
  have hzc : coboundary M (n + 1) (k' : SingularCochainInt M (n + 1))
      = (z : SingularCochainInt M (n + 2))
        - coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1))) := by
    have h := congrArg (fun x : mvUnionCochainsInt U V (n + 2) => (x : SingularCochainInt M (n + 2))) hk'
    simpa only [qCoboundaryIntₗ_coe, AddSubgroupClass.coe_sub, relToQCocycleInt_coe,
      relToQCochainInt_coe, midCocycleInt_coe] using h
  -- `(z : cochain) = coboundary(indUf U ω + k')`
  have hzU : (z : SingularCochainInt M (n + 2))
      = coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1))
          + (k' : SingularCochainInt M (n + 1))) := by
    show _ = coboundaryₗ M (n + 1) _
    rw [map_add]
    show (z : SingularCochainInt M (n + 2))
        = coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1)))
          + coboundary M (n + 1) (k' : SingularCochainInt M (n + 1))
    rw [hzc]; abel
  -- `coboundary(indUf U ω) = coboundary(indUf U ω − ω)` since `ω` is a cocycle
  have hωcocy : coboundary M (n + 1) (ω : SingularCochainInt M (n + 1)) = 0 := by
    have h := ω.2; rw [LinearMap.mem_ker] at h
    have h2 := congrArg (fun x : relCochainsInt (U ∩ V) (n + 2) => (x : SingularCochainInt M (n + 2))) h
    simpa only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] using h2
  have hzV : (z : SingularCochainInt M (n + 2))
      = coboundary M (n + 1) ((indUf U (n + 1) (ω : SingularCochainInt M (n + 1))
          - (ω : SingularCochainInt M (n + 1))) + (k' : SingularCochainInt M (n + 1))) := by
    rw [hzU]
    have hb : coboundaryₗ M (n + 1) (ω : SingularCochainInt M (n + 1)) = 0 := hωcocy
    show coboundaryₗ M (n + 1) _ = coboundaryₗ M (n + 1) _
    rw [map_add, map_add, map_sub, hb, sub_zero]
  rw [relCohomMvDiagInt_apply, Prod.mk_eq_zero]
  refine ⟨?_, ?_⟩
  · -- restr_U: `indUf U ω + k' ∈ relC(U)`
    refine relCohomRestrictInt_mk_eq_zero_of_coboundary Set.subset_union_left (n + 1) z _ ?_ hzU
    exact Submodule.add_mem _ (indUf_mem U (n + 1) _)
      (mvUnionCochainsInt_le_relCochainsInt_left U V (n + 1) k'.2)
  · -- restr_V: `(indUf U ω − ω) + k' ∈ relC(V)`
    refine relCohomRestrictInt_mk_eq_zero_of_coboundary Set.subset_union_right (n + 1) z _ ?_ hzV
    exact Submodule.add_mem _ (indVf_mem U V (n + 1) ω.1)
      (mvUnionCochainsInt_le_relCochainsInt_right U V (n + 1) k'.2)

/-- `Σ` on classes: `Σ([α],[β]) = [restr α − restr β]` (the honest ℤ-difference of the restrictions). -/
theorem relCohomMvSumInt_mk (U V : Set ↑M) (n : ℕ)
    (α : LinearMap.ker (relCoboundaryIntₗ U n)) (β : LinearMap.ker (relCoboundaryIntₗ V n)) :
    relCohomMvSumInt U V n (RelativeCohomologyInt.mk U n α, RelativeCohomologyInt.mk V n β)
      = RelativeCohomologyInt.mk (U ∩ V) n
          (relCocycleRestrictInt Set.inter_subset_left n α
            - relCocycleRestrictInt Set.inter_subset_right n β) := by
  rw [relCohomMvSumInt_apply, relCohomRestrictInt_mk, relCohomRestrictInt_mk]
  exact (Submodule.Quotient.mk_sub _).symm

/-- **Exactness at `Hᵏ(M|U∩V)`**: `Function.Exact Σ δ` (`ker δ = range Σ`). The `ker ⊆ range` half: for
`ω` a cocycle with `midCohom [ω] = 0` (so `coboundary(indUf U ω) = coboundary k`, `k ∈ mvUnion`),
`a := indUf U ω − k` is a `U`-cocycle and `b := a − ω` a `V`-cocycle with `Σ([a],[b]) = [ω]`. -/
theorem relCohomMv_exact_sumInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Function.Exact (relCohomMvSumInt U V (n + 1)) (relCohomMvConnectingInt U V hU hV n) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨ω, rfl⟩ := RelativeCohomologyInt.mk_surjective (U ∩ V) (n + 1) x
    rw [relCohomMvConnectingInt_eq_zero_iff, midCohomInt_mk, QCohomologyInt.mk_eq_zero_iff] at hx
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype, qCoboundaryRangeInt,
      LinearMap.mem_range] at hx
    obtain ⟨k, hk⟩ := hx
    have hkc : coboundary M (n + 1) (k : SingularCochainInt M (n + 1))
        = coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1))) := by
      have h := congrArg (fun y : mvUnionCochainsInt U V (n + 2) => (y : SingularCochainInt M (n + 2))) hk
      simpa only [qCoboundaryIntₗ_coe, midCocycleInt_coe] using h
    have hωcocy : coboundary M (n + 1) (ω : SingularCochainInt M (n + 1)) = 0 := by
      have h := ω.2; rw [LinearMap.mem_ker] at h
      have h2 := congrArg (fun y : relCochainsInt (U ∩ V) (n + 2) => (y : SingularCochainInt M (n + 2))) h
      simpa only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] using h2
    -- `a := indUf U ω − k`, a `U`-cocycle
    have hac_mem : indUf U (n + 1) (ω : SingularCochainInt M (n + 1))
        - (k : SingularCochainInt M (n + 1)) ∈ relCochainsInt U (n + 1) :=
      Submodule.sub_mem _ (indUf_mem U (n + 1) _)
        (mvUnionCochainsInt_le_relCochainsInt_left U V (n + 1) k.2)
    have hac_cocy : coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1))
        - (k : SingularCochainInt M (n + 1))) = 0 := by
      show coboundaryₗ M (n + 1) _ = 0
      rw [map_sub]
      show coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1)))
          - coboundary M (n + 1) (k : SingularCochainInt M (n + 1)) = 0
      rw [hkc, sub_self]
    set aKer : LinearMap.ker (relCoboundaryIntₗ U (n + 1)) :=
      ⟨⟨indUf U (n + 1) (ω : SingularCochainInt M (n + 1)) - (k : SingularCochainInt M (n + 1)), hac_mem⟩,
        by rw [LinearMap.mem_ker]; apply Subtype.ext; rw [relCoboundaryIntₗ_coe]; exact hac_cocy⟩
      with haKer
    -- `b := a − ω`, a `V`-cocycle
    have hbc_mem : (indUf U (n + 1) (ω : SingularCochainInt M (n + 1)) - (k : SingularCochainInt M (n + 1)))
        - (ω : SingularCochainInt M (n + 1)) ∈ relCochainsInt V (n + 1) := by
      have hrw : (indUf U (n + 1) (ω : SingularCochainInt M (n + 1)) - (k : SingularCochainInt M (n + 1)))
          - (ω : SingularCochainInt M (n + 1))
          = (indUf U (n + 1) (ω : SingularCochainInt M (n + 1)) - (ω : SingularCochainInt M (n + 1)))
            - (k : SingularCochainInt M (n + 1)) := by abel
      rw [hrw]
      exact Submodule.sub_mem _ (indVf_mem U V (n + 1) ω.1)
        (mvUnionCochainsInt_le_relCochainsInt_right U V (n + 1) k.2)
    have hbc_cocy : coboundary M (n + 1) ((indUf U (n + 1) (ω : SingularCochainInt M (n + 1))
        - (k : SingularCochainInt M (n + 1))) - (ω : SingularCochainInt M (n + 1))) = 0 := by
      show coboundaryₗ M (n + 1) _ = 0
      rw [map_sub]
      show coboundary M (n + 1) (indUf U (n + 1) (ω : SingularCochainInt M (n + 1))
          - (k : SingularCochainInt M (n + 1))) - coboundary M (n + 1) (ω : SingularCochainInt M (n + 1)) = 0
      rw [hac_cocy, hωcocy, sub_zero]
    set bKer : LinearMap.ker (relCoboundaryIntₗ V (n + 1)) :=
      ⟨⟨(indUf U (n + 1) (ω : SingularCochainInt M (n + 1)) - (k : SingularCochainInt M (n + 1)))
          - (ω : SingularCochainInt M (n + 1)), hbc_mem⟩,
        by rw [LinearMap.mem_ker]; apply Subtype.ext; rw [relCoboundaryIntₗ_coe]; exact hbc_cocy⟩
      with hbKer
    refine ⟨(RelativeCohomologyInt.mk U (n + 1) aKer, RelativeCohomologyInt.mk V (n + 1) bKer), ?_⟩
    rw [relCohomMvSumInt_mk]
    refine mk_eq_of_coboundary_diff n _ ω 0 ?_
    have hrhs : coboundary M n ((0 : relCochainsInt (U ∩ V) n) : SingularCochainInt M n) = 0 := by
      rw [ZeroMemClass.coe_zero]; exact map_zero (coboundaryₗ M n)
    have haKer_coe : ((aKer : relCochainsInt U (n + 1)) : SingularCochainInt M (n + 1))
        = indUf U (n + 1) (ω : SingularCochainInt M (n + 1)) - (k : SingularCochainInt M (n + 1)) := rfl
    have hbKer_coe : ((bKer : relCochainsInt V (n + 1)) : SingularCochainInt M (n + 1))
        = (indUf U (n + 1) (ω : SingularCochainInt M (n + 1)) - (k : SingularCochainInt M (n + 1)))
          - (ω : SingularCochainInt M (n + 1)) := rfl
    rw [hrhs]
    simp only [AddSubgroupClass.coe_sub, relCocycleRestrictInt_coe, relCochainRestrictInt_coe,
      haKer_coe, hbKer_coe]
    abel
  · rintro _ ⟨p, rfl⟩
    rw [LinearMap.mem_ker]
    exact relCohomMvConnectingInt_relCohomMvSumInt U V hU hV n p

/-- **Exactness at `Hᵏ⁺¹(M|U∪V)`**: `Function.Exact δ Δ` (`ker Δ = range δ`). The `ker ⊆ range` half: a
cocycle `z` restricting to coboundaries `coboundary pU` (on `U`) and `coboundary pV` (on `V`) is `δ[ω]` for
`ω := pU − pV` — `midCocycle ω = coboundary(indUf U ω) = z − coboundary(indUf U pV)`, cohomologous to `z`. -/
theorem relCohomMv_exact_connectingInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Function.Exact (relCohomMvConnectingInt U V hU hV n) (relCohomMvDiagInt U V (n + 2)) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    obtain ⟨z, rfl⟩ := RelativeCohomologyInt.mk_surjective (U ∪ V) (n + 2) y
    rw [relCohomMvDiagInt_apply, Prod.mk_eq_zero] at hy
    obtain ⟨hyU, hyV⟩ := hy
    rw [relCohomRestrictInt_mk, RelativeCohomologyInt.mk_eq_zero_iff] at hyU hyV
    simp only [relCoboundaryRangeInt, LinearMap.mem_range] at hyU hyV
    obtain ⟨pU, hpU⟩ := hyU
    obtain ⟨pV, hpV⟩ := hyV
    have hpUc : coboundary M (n + 1) (pU : SingularCochainInt M (n + 1))
        = (z : SingularCochainInt M (n + 2)) := by
      have h := congrArg (fun x : relCochainsInt U (n + 2) => (x : SingularCochainInt M (n + 2))) hpU
      simpa only [relCoboundaryIntₗ_coe, relCocycleRestrictInt_coe, relCochainRestrictInt_coe] using h
    have hpVc : coboundary M (n + 1) (pV : SingularCochainInt M (n + 1))
        = (z : SingularCochainInt M (n + 2)) := by
      have h := congrArg (fun x : relCochainsInt V (n + 2) => (x : SingularCochainInt M (n + 2))) hpV
      simpa only [relCoboundaryIntₗ_coe, relCocycleRestrictInt_coe, relCochainRestrictInt_coe] using h
    have hω_mem : (pU : SingularCochainInt M (n + 1)) - (pV : SingularCochainInt M (n + 1))
        ∈ relCochainsInt (U ∩ V) (n + 1) :=
      Submodule.sub_mem _ (relCochainsInt_antitone Set.inter_subset_left (n + 1) pU.2)
        (relCochainsInt_antitone Set.inter_subset_right (n + 1) pV.2)
    have hω_cocy : coboundary M (n + 1) ((pU : SingularCochainInt M (n + 1))
        - (pV : SingularCochainInt M (n + 1))) = 0 := by
      show coboundaryₗ M (n + 1) _ = 0
      rw [map_sub]
      show coboundary M (n + 1) (pU : SingularCochainInt M (n + 1))
          - coboundary M (n + 1) (pV : SingularCochainInt M (n + 1)) = 0
      rw [hpUc, hpVc, sub_self]
    set ωKer : LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (n + 1)) :=
      ⟨⟨(pU : SingularCochainInt M (n + 1)) - (pV : SingularCochainInt M (n + 1)), hω_mem⟩,
        by rw [LinearMap.mem_ker]; apply Subtype.ext; rw [relCoboundaryIntₗ_coe]; exact hω_cocy⟩
      with hωKer
    refine ⟨RelativeCohomologyInt.mk (U ∩ V) (n + 1) ωKer, ?_⟩
    rw [relCohomMvConnectingInt_apply, LinearEquiv.symm_apply_eq, midCohomInt_mk,
      dualExcisionEquivInt_apply, dualExcisionInt_mk]
    refine (Submodule.Quotient.eq _).2 ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype, qCoboundaryRangeInt,
      LinearMap.mem_range]
    refine ⟨⟨-(indUf U (n + 1) (pV : SingularCochainInt M (n + 1))),
      Submodule.neg_mem _ (indUf_mem_mvUnion U V (n + 1) _ pV.2)⟩, ?_⟩
    apply Subtype.ext
    have hωKer_coe : ((ωKer : relCochainsInt (U ∩ V) (n + 1)) : SingularCochainInt M (n + 1))
        = (pU : SingularCochainInt M (n + 1)) - (pV : SingularCochainInt M (n + 1)) := rfl
    simp only [qCoboundaryIntₗ_coe, AddSubgroupClass.coe_sub, midCocycleInt_coe, relToQCocycleInt_coe,
      relToQCochainInt_coe, hωKer_coe, indUf_sub,
      indUf_eq_self_of_mem U (n + 1) (pU : SingularCochainInt M (n + 1)) pU.2]
    have hpUc' : coboundaryₗ M (n + 1) (pU : SingularCochainInt M (n + 1))
        = (z : SingularCochainInt M (n + 2)) := hpUc
    show coboundaryₗ M (n + 1) (-(indUf U (n + 1) (pV : SingularCochainInt M (n + 1))))
        = coboundaryₗ M (n + 1) ((pU : SingularCochainInt M (n + 1))
            - indUf U (n + 1) (pV : SingularCochainInt M (n + 1))) - (z : SingularCochainInt M (n + 2))
    rw [map_neg, map_sub, hpUc']
    abel
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    exact relCohomMvDiagInt_relCohomMvConnectingInt U V hU hV n y

end SKEFTHawking.SingularRelativeCohomologyMVConnectingInt
