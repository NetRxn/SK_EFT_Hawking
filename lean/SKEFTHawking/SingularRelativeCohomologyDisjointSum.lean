/-
# Phase 5q.H (W-A addClosure, layer 1) — disjoint-union additivity of RELATIVE singular `ℤ/2`
cohomology

The relative companion to `SingularCohomologyDisjointSum` (which builds `Hⁿ(A ⊔ B) ≅ Hⁿ(A) × Hⁿ(B)`
absolutely). Here we build, for pairs `(A, S₁)` and `(B, S₂)`,
`Hⁿ(A ⊔ B, S₁ ⊔ S₂) ≅ Hⁿ(A, S₁) × Hⁿ(B, S₂)` in every degree `n`, where the union subspace is
`S₁ ⊔ S₂ = Sum.inl '' S₁ ∪ Sum.inr '' S₂` — exactly the `boundary_disjointUnion` shape of the boundary
set of `b₁.add b₂` (`W = W₁ ⊕ W₂`, `∂W = ∂W₁ ⊔ ∂W₂`).

**Route (chain-level splitting, the honest cheaper one).** We reuse the absolute glue/restrict cochain
machinery of `SingularCohomologyDisjointSum` verbatim: the absolute restriction pair `(inl*, inr*)`
and the glue `glueCochain` are mutually inverse, commute with `δ`, and — the new content — both
**preserve the relative-cochain annihilators**: `inl*` / `inr*` send `Cⁿ(A ⊔ B, S₁ ⊔ S₂)` into
`Cⁿ(A, S₁)` / `Cⁿ(B, S₂)` (Kronecker-adjoint of `mapChain_mem_subspaceChains`), and `glue` sends the
pair back (a subspace simplex of the union factors through one inclusion into the corresponding
`Sᵢ`). Hence the pullback pair descends to the relative-cohomology isomorphism
`relCohomologyDisjointSumEquiv`, plus the two block sections. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyDisjointSum
import SKEFTHawking.SingularRelativeCohomologyMod2
import SKEFTHawking.SingularRelativeFunctoriality

namespace SKEFTHawking.SingularRelativeCohomologyDisjointSum

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.SingularExcision SKEFTHawking.SingularDisjointUnion

/-! ## §0. The general relative cochain / cohomology pullback along a pair map

Contravariant companion to `SingularRelativeFunctoriality.RelativeHomology.map`: a map of pairs
`φ : (X, SX) → (Y, SY)` (`Set.MapsTo φ SX SY`) induces `Hⁿ(Y, SY) → Hⁿ(X, SX)`. -/

section GeneralPullback

variable {X Y : TopCat} (φ : C(↑X, ↑Y)) {SX : Set ↑X} {SY : Set ↑Y} (hφ : Set.MapsTo φ SX SY)

include hφ

/-- **The cochain pullback preserves relative cochains**: `inl*` of a relative cochain is relative.
Kronecker-adjoint of `mapChain_mem_subspaceChains`. -/
theorem cochainPullback_mem_relCochains (n : ℕ) (f : SingularCochain Y n)
    (hf : f ∈ relCochains SY n) : cochainPullback φ n f ∈ relCochains SX n := by
  intro c hc
  rw [kronecker_cochainPullback]
  exact hf _ (mapChain_mem_subspaceChains φ hφ n c hc)

/-- The relative cochain pullback `Cⁿ(Y, SY) →ₗ Cⁿ(X, SX)`. -/
noncomputable def relCochainPullback (n : ℕ) :
    relCochains SY n →ₗ[ZMod 2] relCochains SX n :=
  ((cochainPullback φ n).domRestrict (relCochains SY n)).codRestrict (relCochains SX n)
    (fun f => cochainPullback_mem_relCochains φ hφ n f.1 f.2)

@[simp] theorem relCochainPullback_coe (n : ℕ) (f : relCochains SY n) :
    (relCochainPullback φ hφ n f : SingularCochain X n)
      = cochainPullback φ n (f : SingularCochain Y n) := rfl

/-- The relative cochain pullback commutes with the relative coboundary. -/
theorem relCoboundary_relCochainPullback (n : ℕ) (f : relCochains SY n) :
    relCoboundaryₗ SX n (relCochainPullback φ hφ n f)
      = relCochainPullback φ hφ (n + 1) (relCoboundaryₗ SY n f) := by
  apply Subtype.ext
  rw [relCoboundaryₗ_coe, relCochainPullback_coe, relCochainPullback_coe, relCoboundaryₗ_coe]
  exact coboundary_cochainPullback φ n (f : SingularCochain Y n)

/-- The relative cochain pullback sends relative cocycles to relative cocycles. -/
theorem relCochainPullback_mem_ker (n : ℕ) (f : LinearMap.ker (relCoboundaryₗ SY n)) :
    relCochainPullback φ hφ n f.1 ∈ LinearMap.ker (relCoboundaryₗ SX n) := by
  rw [LinearMap.mem_ker, relCoboundary_relCochainPullback, LinearMap.mem_ker.mp f.2, map_zero]

/-- **The relative cohomology pullback** `Hⁿ(Y, SY) →ₗ Hⁿ(X, SX)` — the descended relative cochain
pullback. Contravariant companion to `RelativeHomology.map`. -/
noncomputable def relCohomPullback (n : ℕ) :
    RelativeCohomology SY n →ₗ[ZMod 2] RelativeCohomology SX n :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      (((relCochainPullback φ hφ n).domRestrict (LinearMap.ker (relCoboundaryₗ SY n))).codRestrict
        (LinearMap.ker (relCoboundaryₗ SX n)) fun f => relCochainPullback_mem_ker φ hφ n f))
    (by
      intro a ha
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
      cases n with
      | zero =>
          rw [show relCoboundaryRange SY 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
            Submodule.mem_bot] at ha
          rw [show relCoboundaryRange SX 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
            Submodule.mem_bot]
          have ha' : a.1 = (0 : relCochains SY 0) := ha
          rw [ha', map_zero]
      | succ m =>
          rw [show relCoboundaryRange SY (m + 1) = LinearMap.range (relCoboundaryₗ SY m) from rfl]
            at ha
          obtain ⟨b, hb⟩ := ha
          rw [show relCoboundaryRange SX (m + 1) = LinearMap.range (relCoboundaryₗ SX m) from rfl]
          refine ⟨relCochainPullback φ hφ m b, ?_⟩
          rw [relCoboundary_relCochainPullback, hb])

/-- Computation rule for `relCohomPullback` on a representative relative cocycle. -/
@[simp] theorem relCohomPullback_mk (n : ℕ) (f : LinearMap.ker (relCoboundaryₗ SY n)) :
    relCohomPullback φ hφ n (RelativeCohomology.mk SY n f)
      = RelativeCohomology.mk SX n ⟨relCochainPullback φ hφ n f.1,
          relCochainPullback_mem_ker φ hφ n f⟩ :=
  rfl

end GeneralPullback

/-! ## §1. The union subspace and the two inclusion maps of pairs -/

variable (A B : TopCat) (S₁ : Set ↑A) (S₂ : Set ↑B)

/-- The disjoint-union subspace `S₁ ⊔ S₂ = Sum.inl '' S₁ ∪ Sum.inr '' S₂ ⊆ A ⊔ B`. -/
def sumSet : Set ↑(sumSpace A B) := Sum.inl '' S₁ ∪ Sum.inr '' S₂

/-- `inl` maps `S₁` into the union subspace. -/
theorem mapsTo_inl : Set.MapsTo (inlMap A B) S₁ (sumSet A B S₁ S₂) :=
  fun a ha => Or.inl ⟨a, ha, rfl⟩

/-- `inr` maps `S₂` into the union subspace. -/
theorem mapsTo_inr : Set.MapsTo (inrMap A B) S₂ (sumSet A B S₁ S₂) :=
  fun b hb => Or.inr ⟨b, hb, rfl⟩

/-! ## §2. The vanishing lemma and the relative glue membership -/

/-- A relative cochain vanishes on any simplex whose realization has range inside `S`. -/
theorem relCochain_vanish_range {X : TopCat} {S : Set ↑X} {n : ℕ} (f : relCochains S n)
    (ρ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)))
    (hρ : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) ρ) ⊆ S) :
    (f : SingularCochain X n) ρ = 0 := by
  have hmem := single_mem_subspaceChains_of_subordinate hρ
  have h0 := f.2 _ hmem
  rwa [kronecker_single, one_mul] at h0

/-- **The relative glue membership**: the absolute glue of two relative cochains is a relative cochain
of the union. A subspace simplex `simplexIncl (S₁ ⊔ S₂) n τ` of the union has range in `S₁ ⊔ S₂`, so
(`Δⁿ` preconnected ⟹ factors through one inclusion) it lands entirely in `inl '' S₁` or `inr '' S₂`;
the glue reads the corresponding relative cochain on the factored simplex (range in `Sᵢ`), which
vanishes by `relCochain_vanish_range`. -/
theorem glue_mem_relCochains (n : ℕ) (a : relCochains S₁ n) (b : relCochains S₂ n) :
    glueCochain A B n (a.1, b.1) ∈ relCochains (sumSet A B S₁ S₂) n := by
  intro c hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero]; simp only [kronecker_apply, Finsupp.sum_zero_index]
  | add c₁ c₂ h₁ h₂ => rw [map_add, kronecker_add_right, h₁, h₂, add_zero]
  | single τ a' =>
      rw [chainIncl_single, kronecker_single]
      set σ := simplexIncl (sumSet A B S₁ S₂) n τ with hσ
      have hrange : Set.range ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ)
          ⊆ sumSet A B S₁ S₂ := range_realize_simplexIncl (sumSet A B S₁ S₂) τ
      have hval : glueCochain A B n (a.1, b.1) σ = 0 := by
        rw [glueCochain_apply]
        by_cases h : Set.range ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ)
            ⊆ Set.range (Sum.inl : ↑A → ↑A ⊕ ↑B)
        · simp only [glueVal, dif_pos h]
          refine relCochain_vanish_range a _ ?_
          rw [Equiv.apply_symm_apply]
          rintro x ⟨t, rfl⟩
          have hx : (Sum.inl (factorLeft ((sumSpace A B).toSSetObjEquiv
              (op (SimplexCategory.mk n)) σ) h t) : ↑A ⊕ ↑B) ∈ sumSet A B S₁ S₂ := by
            rw [inl_factorLeft]; exact hrange ⟨t, rfl⟩
          rcases hx with ⟨y, hy, hyeq⟩ | ⟨y, hy, hyeq⟩
          · rw [Sum.inl.injEq] at hyeq; exact hyeq ▸ hy
          · exact absurd hyeq (Sum.inr_ne_inl)
        · have hR := (continuous_to_sum_factor
            ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ)).resolve_left h
          simp only [glueVal, dif_neg h]
          refine relCochain_vanish_range b _ ?_
          rw [Equiv.apply_symm_apply]
          rintro x ⟨t, rfl⟩
          have hx : (Sum.inr (factorRight ((sumSpace A B).toSSetObjEquiv
              (op (SimplexCategory.mk n)) σ) hR t) : ↑A ⊕ ↑B) ∈ sumSet A B S₁ S₂ := by
            rw [inr_factorRight]; exact hrange ⟨t, rfl⟩
          rcases hx with ⟨y, hy, hyeq⟩ | ⟨y, hy, hyeq⟩
          · exact absurd hyeq (Sum.inl_ne_inr)
          · rw [Sum.inr.injEq] at hyeq; exact hyeq ▸ hy
      rw [hval, mul_zero]

/-! ## §3. The relative disjoint-union cohomology additivity isomorphism -/

/-- The relative cohomology restriction pair `Hⁿ(A ⊔ B, S₁ ⊔ S₂) → Hⁿ(A, S₁) × Hⁿ(B, S₂)`. -/
noncomputable def relRestrictPairCohomology (n : ℕ) :
    RelativeCohomology (sumSet A B S₁ S₂) n →ₗ[ZMod 2]
      RelativeCohomology S₁ n × RelativeCohomology S₂ n :=
  (relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) n).prod
    (relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) n)

@[simp] theorem relRestrictPairCohomology_apply (n : ℕ)
    (x : RelativeCohomology (sumSet A B S₁ S₂) n) :
    relRestrictPairCohomology A B S₁ S₂ n x
      = (relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) n x,
         relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) n x) := rfl

/-- **The relative restriction pair is injective**: a relative class restricting to `0` on both
summands is `0`. Its representative `f` restricts to a relative coboundary on each summand; glue the
primitives (`coboundary_glueCochain` + `glue_cochainPullback`, wrapped by `glue_mem_relCochains`) to a
global relative primitive of `f`. -/
theorem relRestrictPairCohomology_injective (n : ℕ) :
    Function.Injective (relRestrictPairCohomology A B S₁ S₂ n) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mem_bot]
  rw [LinearMap.mem_ker, relRestrictPairCohomology_apply] at hx
  have hxl : relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) n
      (RelativeCohomology.mk (sumSet A B S₁ S₂) n f) = 0 := congrArg Prod.fst hx
  have hxr : relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) n
      (RelativeCohomology.mk (sumSet A B S₁ S₂) n f) = 0 := congrArg Prod.snd hx
  rw [relCohomPullback_mk, RelativeCohomology.mk_eq_zero_iff] at hxl hxr
  show RelativeCohomology.mk (sumSet A B S₁ S₂) n f = 0
  rw [RelativeCohomology.mk_eq_zero_iff]
  -- goal: (↑f : relCochains (sumSet) n) ∈ relCoboundaryRange (sumSet) n
  cases n with
  | zero =>
      rw [show relCoboundaryRange S₁ 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
        Submodule.mem_bot] at hxl
      rw [show relCoboundaryRange S₂ 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
        Submodule.mem_bot] at hxr
      rw [show relCoboundaryRange (sumSet A B S₁ S₂) 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
        Submodule.mem_bot]
      apply Subtype.ext
      have hl0 : cochainPullback (inlMap A B) 0 (↑↑f) = 0 := by
        have h : (relCochainPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) 0 (↑f)
            : relCochains S₁ 0) = 0 := hxl
        have h2 := congrArg Subtype.val h
        rw [relCochainPullback_coe] at h2
        simpa using h2
      have hr0 : cochainPullback (inrMap A B) 0 (↑↑f) = 0 := by
        have h : (relCochainPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) 0 (↑f)
            : relCochains S₂ 0) = 0 := hxr
        have h2 := congrArg Subtype.val h
        rw [relCochainPullback_coe] at h2
        simpa using h2
      show (↑↑f : SingularCochain (sumSpace A B) 0) = _
      rw [ZeroMemClass.coe_zero, ← glue_cochainPullback A B 0 (↑↑f)]
      show glueCochain A B 0
        (cochainPullback (inlMap A B) 0 (↑↑f), cochainPullback (inrMap A B) 0 (↑↑f)) = 0
      rw [hl0, hr0]
      exact map_zero _
  | succ m =>
      rw [show relCoboundaryRange S₁ (m + 1) = LinearMap.range (relCoboundaryₗ S₁ m) from rfl]
        at hxl
      rw [show relCoboundaryRange S₂ (m + 1) = LinearMap.range (relCoboundaryₗ S₂ m) from rfl]
        at hxr
      rw [show relCoboundaryRange (sumSet A B S₁ S₂) (m + 1)
        = LinearMap.range (relCoboundaryₗ (sumSet A B S₁ S₂) m) from rfl]
      obtain ⟨aA, haA⟩ := hxl
      obtain ⟨bB, hbB⟩ := hxr
      have haA' : coboundary A m aA.1 = cochainPullback (inlMap A B) (m + 1) (↑↑f) := by
        have h := congrArg Subtype.val haA
        rw [relCoboundaryₗ_coe, relCochainPullback_coe] at h
        exact h
      have hbB' : coboundary B m bB.1 = cochainPullback (inrMap A B) (m + 1) (↑↑f) := by
        have h := congrArg Subtype.val hbB
        rw [relCoboundaryₗ_coe, relCochainPullback_coe] at h
        exact h
      refine ⟨⟨glueCochain A B m (aA.1, bB.1),
        glue_mem_relCochains A B S₁ S₂ m aA bB⟩, ?_⟩
      apply Subtype.ext
      rw [relCoboundaryₗ_coe]
      show coboundary (sumSpace A B) m (glueCochain A B m (aA.1, bB.1)) = ↑↑f
      rw [coboundary_glueCochain, haA', hbB', glue_cochainPullback]

/-- **The relative restriction pair is surjective**: any pair of relative classes is realized by the
glued relative cocycle. -/
theorem relRestrictPairCohomology_surjective (n : ℕ) :
    Function.Surjective (relRestrictPairCohomology A B S₁ S₂ n) := by
  rintro ⟨x, y⟩
  obtain ⟨aA, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨bB, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hglue_ker : glueCochain A B n (aA.1.1, bB.1.1)
      ∈ relCochains (sumSet A B S₁ S₂) n :=
    glue_mem_relCochains A B S₁ S₂ n aA.1 bB.1
  have hw : relCoboundaryₗ (sumSet A B S₁ S₂) n ⟨glueCochain A B n (aA.1.1, bB.1.1), hglue_ker⟩ = 0 := by
    apply Subtype.ext
    rw [relCoboundaryₗ_coe]
    show coboundary (sumSpace A B) n (glueCochain A B n (aA.1.1, bB.1.1)) = 0
    rw [coboundary_glueCochain]
    have haz : coboundary A n aA.1.1 = 0 := by
      have h := congrArg Subtype.val (LinearMap.mem_ker.mp aA.2)
      rw [relCoboundaryₗ_coe] at h
      simpa using h
    have hbz : coboundary B n bB.1.1 = 0 := by
      have h := congrArg Subtype.val (LinearMap.mem_ker.mp bB.2)
      rw [relCoboundaryₗ_coe] at h
      simpa using h
    rw [haz, hbz]
    exact map_zero _
  refine ⟨RelativeCohomology.mk (sumSet A B S₁ S₂) n
    ⟨⟨glueCochain A B n (aA.1.1, bB.1.1), hglue_ker⟩, hw⟩, ?_⟩
  rw [relRestrictPairCohomology_apply, relCohomPullback_mk, relCohomPullback_mk]
  refine Prod.ext ?_ ?_
  · apply congrArg (RelativeCohomology.mk S₁ n)
    apply Subtype.ext
    apply Subtype.ext
    show cochainPullback (inlMap A B) n (glueCochain A B n (aA.1.1, bB.1.1)) = aA.1.1
    exact cochainPullback_inl_glue A B n aA.1.1 bB.1.1
  · apply congrArg (RelativeCohomology.mk S₂ n)
    apply Subtype.ext
    apply Subtype.ext
    show cochainPullback (inrMap A B) n (glueCochain A B n (aA.1.1, bB.1.1)) = bB.1.1
    exact cochainPullback_inr_glue A B n aA.1.1 bB.1.1

/-- **Relative disjoint-union cohomology additivity** (all degrees):
`Hⁿ(A ⊔ B, S₁ ⊔ S₂) ≃ₗ Hⁿ(A, S₁) × Hⁿ(B, S₂)` via the two inclusion pullbacks. The relative companion
to `SingularCohomologyDisjointSum.cohomologyDisjointSumEquiv`, and the relative-cohomology input for the
boundary set of `b₁.add b₂` (`∂(W₁ ⊔ W₂) = ∂W₁ ⊔ ∂W₂`). -/
noncomputable def relCohomologyDisjointSumEquiv (n : ℕ) :
    RelativeCohomology (sumSet A B S₁ S₂) n ≃ₗ[ZMod 2]
      RelativeCohomology S₁ n × RelativeCohomology S₂ n :=
  LinearEquiv.ofBijective (relRestrictPairCohomology A B S₁ S₂ n)
    ⟨relRestrictPairCohomology_injective A B S₁ S₂ n,
     relRestrictPairCohomology_surjective A B S₁ S₂ n⟩

/-! ## §4. The block sections and finite-dimensionality/rank additivity -/

/-- The **left block section** `Hⁿ(A, S₁) → Hⁿ(A ⊔ B, S₁ ⊔ S₂)`, `y ↦ equiv⁻¹ (y, 0)`. -/
noncomputable def relSectionInl (n : ℕ) :
    RelativeCohomology S₁ n →ₗ[ZMod 2] RelativeCohomology (sumSet A B S₁ S₂) n :=
  (relCohomologyDisjointSumEquiv A B S₁ S₂ n).symm.toLinearMap.comp
    (LinearMap.inl (ZMod 2) (RelativeCohomology S₁ n) (RelativeCohomology S₂ n))

/-- The **right block section** `Hⁿ(B, S₂) → Hⁿ(A ⊔ B, S₁ ⊔ S₂)`, `y ↦ equiv⁻¹ (0, y)`. -/
noncomputable def relSectionInr (n : ℕ) :
    RelativeCohomology S₂ n →ₗ[ZMod 2] RelativeCohomology (sumSet A B S₁ S₂) n :=
  (relCohomologyDisjointSumEquiv A B S₁ S₂ n).symm.toLinearMap.comp
    (LinearMap.inr (ZMod 2) (RelativeCohomology S₁ n) (RelativeCohomology S₂ n))

/-- The restriction pair of the left section is `(y, 0)`. -/
theorem relRestrictPair_relSectionInl (n : ℕ) (y : RelativeCohomology S₁ n) :
    relRestrictPairCohomology A B S₁ S₂ n (relSectionInl A B S₁ S₂ n y) = (y, 0) := by
  show relCohomologyDisjointSumEquiv A B S₁ S₂ n
      ((relCohomologyDisjointSumEquiv A B S₁ S₂ n).symm (y, 0)) = (y, 0)
  rw [LinearEquiv.apply_symm_apply]

/-- The restriction pair of the right section is `(0, y)`. -/
theorem relRestrictPair_relSectionInr (n : ℕ) (y : RelativeCohomology S₂ n) :
    relRestrictPairCohomology A B S₁ S₂ n (relSectionInr A B S₁ S₂ n y) = (0, y) := by
  show relCohomologyDisjointSumEquiv A B S₁ S₂ n
      ((relCohomologyDisjointSumEquiv A B S₁ S₂ n).symm (0, y)) = (0, y)
  rw [LinearEquiv.apply_symm_apply]

/-- Left-restriction of the left section is the identity. -/
theorem relCohomPullback_inl_relSectionInl (n : ℕ) (y : RelativeCohomology S₁ n) :
    relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) n (relSectionInl A B S₁ S₂ n y) = y :=
  congrArg Prod.fst (relRestrictPair_relSectionInl A B S₁ S₂ n y)

/-- Right-restriction of the left section vanishes. -/
theorem relCohomPullback_inr_relSectionInl (n : ℕ) (y : RelativeCohomology S₁ n) :
    relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) n (relSectionInl A B S₁ S₂ n y) = 0 :=
  congrArg Prod.snd (relRestrictPair_relSectionInl A B S₁ S₂ n y)

/-- Right-restriction of the right section is the identity. -/
theorem relCohomPullback_inr_relSectionInr (n : ℕ) (y : RelativeCohomology S₂ n) :
    relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) n (relSectionInr A B S₁ S₂ n y) = y :=
  congrArg Prod.snd (relRestrictPair_relSectionInr A B S₁ S₂ n y)

/-- Left-restriction of the right section vanishes. -/
theorem relCohomPullback_inl_relSectionInr (n : ℕ) (y : RelativeCohomology S₂ n) :
    relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) n (relSectionInr A B S₁ S₂ n y) = 0 :=
  congrArg Prod.fst (relRestrictPair_relSectionInr A B S₁ S₂ n y)

/-- **Finite-dimensionality of `Hⁿ(A ⊔ B, S₁ ⊔ S₂)`** from the two summands. -/
theorem finiteDimensional_relCohomology_disjointSum (n : ℕ)
    (hA : FiniteDimensional (ZMod 2) (RelativeCohomology S₁ n))
    (hB : FiniteDimensional (ZMod 2) (RelativeCohomology S₂ n)) :
    FiniteDimensional (ZMod 2) (RelativeCohomology (sumSet A B S₁ S₂) n) :=
  haveI := hA
  haveI := hB
  (relCohomologyDisjointSumEquiv A B S₁ S₂ n).symm.finiteDimensional

/-- **Rank additivity**: `dim Hⁿ(A ⊔ B, S₁ ⊔ S₂) = dim Hⁿ(A, S₁) + dim Hⁿ(B, S₂)`. -/
theorem finrank_relCohomology_disjointSum (n : ℕ)
    [FiniteDimensional (ZMod 2) (RelativeCohomology S₁ n)]
    [FiniteDimensional (ZMod 2) (RelativeCohomology S₂ n)] :
    Module.finrank (ZMod 2) (RelativeCohomology (sumSet A B S₁ S₂) n)
      = Module.finrank (ZMod 2) (RelativeCohomology S₁ n)
        + Module.finrank (ZMod 2) (RelativeCohomology S₂ n) := by
  rw [(relCohomologyDisjointSumEquiv A B S₁ S₂ n).finrank_eq, Module.finrank_prod]

end SKEFTHawking.SingularRelativeCohomologyDisjointSum
