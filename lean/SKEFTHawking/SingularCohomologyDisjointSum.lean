/-
# Phase 5q.H (W-A.1e cyl) — disjoint-union additivity of singular `ℤ/2` COHOMOLOGY (all degrees)

The cohomology-side companion to `SingularDisjointUnion` (which builds the *homology* additivity, but
only at degree `0`). Here we build `Hⁿ(A ⊔ B) ≅ Hⁿ(A) × Hⁿ(B)` in **every** degree `n`, the
absolute-cohomology input for the cylinder boundary `∂W = M ⊔ M` (`W = M × [0,1]`).

**Route (chain-level splitting, not a Kronecker bootstrap).** A singular `n`-simplex of `A ⊕ B` is a
continuous map from the (preconnected) standard simplex, so it factors through `Sum.inl` or `Sum.inr`
(`continuous_to_sum_factor`, with the factors `factorLeft` / `factorRight`). Dually, a singular
`n`-cochain of `A ⊕ B` is exactly a pair of cochains on `A` and `B`: the restriction pair
`(inl*, inr*)` and the **glue** `glueCochain` are mutually inverse (`glue_restrict`, `restrict_glue`),
and — being the inverse of two cochain maps — glue commutes with the coboundary
(`coboundary_glueCochain`). Hence the pullback pair descends to a cohomology isomorphism
`cohomologyDisjointSumEquiv`. No new geometry, no dualization — the honest cheaper route flagged by
the audit.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyDisjoint
import SKEFTHawking.SingularCohomologyFunctoriality

namespace SKEFTHawking.SingularCohomologyDisjointSum

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality

variable (A B : TopCat)

/-- The two-summand space `A ⊔ B` as a `TopCat`. -/
abbrev sumSpace (A B : TopCat) : TopCat := TopCat.of (↑A ⊕ ↑B)

/-- Left inclusion `A ↪ A ⊔ B` as a bundled continuous map. -/
def inlMap : C(↑A, ↑(sumSpace A B)) := ⟨Sum.inl, continuous_inl⟩

/-- Right inclusion `B ↪ A ⊔ B` as a bundled continuous map. -/
def inrMap : C(↑B, ↑(sumSpace A B)) := ⟨Sum.inr, continuous_inr⟩

@[simp] theorem inlMap_apply (a : ↑A) : inlMap A B a = Sum.inl a := rfl
@[simp] theorem inrMap_apply (b : ↑B) : inrMap A B b = Sum.inr b := rfl

/-! ## §1. The glue cochain -/

open Classical in
/-- The value of the glued cochain on a single simplex `σ` of `A ⊔ B`: `σ` factors through one
inclusion (`continuous_to_sum_factor`); evaluate `a` on its `A`-factor, or `b` on its `B`-factor. -/
noncomputable def glueVal {n : ℕ} (a : SingularCochain A n) (b : SingularCochain B n)
    (σ : (TopCat.toSSet.obj (sumSpace A B)).obj (op (SimplexCategory.mk n))) : ZMod 2 :=
  if h : Set.range ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ)
      ⊆ Set.range (Sum.inl : ↑A → ↑A ⊕ ↑B) then
    a ((A.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
      (factorLeft ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ) h))
  else
    b ((B.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
      (factorRight ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ)
        ((continuous_to_sum_factor _).resolve_left h)))

/-- **The glue cochain** `Cⁿ(A) × Cⁿ(B) → Cⁿ(A ⊔ B)`, `(a, b) ↦ glue`, `ℤ/2`-linear. -/
noncomputable def glueCochain (n : ℕ) :
    (SingularCochain A n × SingularCochain B n) →ₗ[ZMod 2] SingularCochain (sumSpace A B) n where
  toFun p := fun σ => glueVal A B p.1 p.2 σ
  map_add' p q := by
    funext σ
    show glueVal A B (p.1 + q.1) (p.2 + q.2) σ = glueVal A B p.1 p.2 σ + glueVal A B q.1 q.2 σ
    unfold glueVal
    split <;> rfl
  map_smul' c p := by
    funext σ
    show glueVal A B (c • p.1) (c • p.2) σ = c • glueVal A B p.1 p.2 σ
    unfold glueVal
    split <;> rfl

@[simp] theorem glueCochain_apply (n : ℕ) (a : SingularCochain A n) (b : SingularCochain B n)
    (σ : (TopCat.toSSet.obj (sumSpace A B)).obj (op (SimplexCategory.mk n))) :
    glueCochain A B n (a, b) σ = glueVal A B a b σ := rfl

/-! ## §2. Realization of a pushed-forward simplex -/

/-- The realization of `mapSimplex inl τ` is `inl ∘ τ`. -/
theorem realize_mapSimplex_inlMap {n : ℕ}
    (τ : (TopCat.toSSet.obj A).obj (op (SimplexCategory.mk n))) :
    (sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) (mapSimplex (inlMap A B) τ)
      = (inlMap A B).comp (A.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) := by
  simp only [mapSimplex, Equiv.apply_symm_apply]

/-- The realization of `mapSimplex inr τ` is `inr ∘ τ`. -/
theorem realize_mapSimplex_inrMap {n : ℕ}
    (τ : (TopCat.toSSet.obj B).obj (op (SimplexCategory.mk n))) :
    (sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) (mapSimplex (inrMap A B) τ)
      = (inrMap A B).comp (B.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) := by
  simp only [mapSimplex, Equiv.apply_symm_apply]

/-! ## §3. The round-trip identities -/

/-- **Left restriction of glue is the first component**: `inl*(glue a b) = a`. -/
theorem cochainPullback_inl_glue (n : ℕ) (a : SingularCochain A n) (b : SingularCochain B n) :
    cochainPullback (inlMap A B) n (glueCochain A B n (a, b)) = a := by
  funext τ
  rw [cochainPullback_apply, glueCochain_apply]
  have hsub : Set.range ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n))
      (mapSimplex (inlMap A B) τ)) ⊆ Set.range (Sum.inl : ↑A → ↑A ⊕ ↑B) := by
    rw [realize_mapSimplex_inlMap]
    rintro x ⟨d, rfl⟩
    exact ⟨A.toSSetObjEquiv (op (SimplexCategory.mk n)) τ d, rfl⟩
  simp only [glueVal, dif_pos hsub]
  have hfac : factorLeft ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n))
        (mapSimplex (inlMap A B) τ)) hsub = A.toSSetObjEquiv (op (SimplexCategory.mk n)) τ := by
    apply ContinuousMap.ext
    intro d
    apply Sum.inl_injective
    rw [inl_factorLeft, realize_mapSimplex_inlMap]
    rfl
  rw [hfac, Equiv.symm_apply_apply]

/-- **Right restriction of glue is the second component**: `inr*(glue a b) = b`. -/
theorem cochainPullback_inr_glue (n : ℕ) (a : SingularCochain A n) (b : SingularCochain B n) :
    cochainPullback (inrMap A B) n (glueCochain A B n (a, b)) = b := by
  funext τ
  rw [cochainPullback_apply, glueCochain_apply]
  have hnsub : ¬ Set.range ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n))
      (mapSimplex (inrMap A B) τ)) ⊆ Set.range (Sum.inl : ↑A → ↑A ⊕ ↑B) := by
    intro hsub
    obtain ⟨x, hx⟩ := Set.range_nonempty ((sumSpace A B).toSSetObjEquiv
      (op (SimplexCategory.mk n)) (mapSimplex (inrMap A B) τ))
    obtain ⟨a', ha'⟩ := hsub hx
    rw [realize_mapSimplex_inrMap] at hx
    obtain ⟨d, hd⟩ := hx
    rw [ContinuousMap.comp_apply, inrMap_apply] at hd
    exact Sum.inl_ne_inr (ha'.trans hd.symm)
  simp only [glueVal, dif_neg hnsub]
  have hfac : factorRight ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n))
        (mapSimplex (inrMap A B) τ)) ((continuous_to_sum_factor _).resolve_left hnsub)
      = B.toSSetObjEquiv (op (SimplexCategory.mk n)) τ := by
    apply ContinuousMap.ext
    intro d
    apply Sum.inr_injective
    rw [inr_factorRight, realize_mapSimplex_inrMap]
    rfl
  rw [hfac, Equiv.symm_apply_apply]

/-- **Glue of the restriction pair is the identity**: `glue (inl* f) (inr* f) = f`. -/
theorem glue_cochainPullback (n : ℕ) (f : SingularCochain (sumSpace A B) n) :
    glueCochain A B n (cochainPullback (inlMap A B) n f, cochainPullback (inrMap A B) n f) = f := by
  funext σ
  rw [glueCochain_apply]
  by_cases h : Set.range ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ)
      ⊆ Set.range (Sum.inl : ↑A → ↑A ⊕ ↑B)
  · simp only [glueVal, dif_pos h, cochainPullback_apply]
    have hkey : mapSimplex (inlMap A B) ((A.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
        (factorLeft ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ) h)) = σ := by
      apply (sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) |>.injective
      rw [realize_mapSimplex_inlMap, Equiv.apply_symm_apply]
      apply ContinuousMap.ext
      intro d
      rw [ContinuousMap.comp_apply, inlMap_apply, inl_factorLeft]
    rw [hkey]
  · simp only [glueVal, dif_neg h, cochainPullback_apply]
    have hR := (continuous_to_sum_factor
      ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ)).resolve_left h
    have hkey : mapSimplex (inrMap A B) ((B.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
        (factorRight ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ) hR)) = σ := by
      apply (sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) |>.injective
      rw [realize_mapSimplex_inrMap, Equiv.apply_symm_apply]
      apply ContinuousMap.ext
      intro d
      rw [ContinuousMap.comp_apply, inrMap_apply, inr_factorRight]
    rw [hkey]

/-! ## §3. Glue commutes with the coboundary -/

/-- The cochain restriction pair `Cⁿ(A ⊔ B) → Cⁿ(A) × Cⁿ(B)`. -/
noncomputable def restrictPairCochain (n : ℕ) :
    SingularCochain (sumSpace A B) n →ₗ[ZMod 2] SingularCochain A n × SingularCochain B n :=
  (cochainPullback (inlMap A B) n).prod (cochainPullback (inrMap A B) n)

theorem restrictPairCochain_injective (n : ℕ) :
    Function.Injective (restrictPairCochain A B n) := by
  intro f g hfg
  have h1 : cochainPullback (inlMap A B) n f = cochainPullback (inlMap A B) n g :=
    congrArg Prod.fst hfg
  have h2 : cochainPullback (inrMap A B) n f = cochainPullback (inrMap A B) n g :=
    congrArg Prod.snd hfg
  rw [← glue_cochainPullback A B n f, ← glue_cochainPullback A B n g, h1, h2]

/-- **Glue commutes with `δ`**: `δ (glue a b) = glue (δa) (δb)`. Derived from the two restrictions
commuting with `δ` (`coboundary_cochainPullback`) and the injectivity of the restriction pair. -/
theorem coboundary_glueCochain (n : ℕ) (a : SingularCochain A n) (b : SingularCochain B n) :
    coboundary (sumSpace A B) n (glueCochain A B n (a, b))
      = glueCochain A B (n + 1) (coboundary A n a, coboundary B n b) := by
  apply restrictPairCochain_injective A B (n + 1)
  apply Prod.ext
  · show cochainPullback (inlMap A B) (n + 1) (coboundary (sumSpace A B) n (glueCochain A B n (a, b)))
        = cochainPullback (inlMap A B) (n + 1) (glueCochain A B (n + 1) (coboundary A n a, coboundary B n b))
    rw [cochainPullback_inl_glue,
      show coboundary (sumSpace A B) n (glueCochain A B n (a, b))
        = coboundary (sumSpace A B) n (glueCochain A B n (a, b)) from rfl,
      ← coboundary_cochainPullback, cochainPullback_inl_glue]
  · show cochainPullback (inrMap A B) (n + 1) (coboundary (sumSpace A B) n (glueCochain A B n (a, b)))
        = cochainPullback (inrMap A B) (n + 1) (glueCochain A B (n + 1) (coboundary A n a, coboundary B n b))
    rw [cochainPullback_inr_glue, ← coboundary_cochainPullback, cochainPullback_inr_glue]

/-! ## §4. The disjoint-union cohomology additivity isomorphism -/

/-- The cohomology restriction pair `Hⁿ(A ⊔ B) → Hⁿ(A) × Hⁿ(B)` via the two inclusion pullbacks. -/
noncomputable def restrictPairCohomology (n : ℕ) :
    Cohomology (sumSpace A B) n →ₗ[ZMod 2] Cohomology A n × Cohomology B n :=
  (cohomologyPullback (inlMap A B) n).prod (cohomologyPullback (inrMap A B) n)

@[simp] theorem restrictPairCohomology_apply (n : ℕ) (x : Cohomology (sumSpace A B) n) :
    restrictPairCohomology A B n x
      = (cohomologyPullback (inlMap A B) n x, cohomologyPullback (inrMap A B) n x) := rfl

/-- `Cohomology.mk` is zero iff its representative is a coboundary. -/
private theorem mk_eq_zero_iff' {X : TopCat} {n : ℕ} (a : LinearMap.ker (coboundaryₗ X n)) :
    Cohomology.mk X n a = 0 ↔ (a : SingularCochain X n) ∈ coboundaryRange X n := by
  show Submodule.Quotient.mk a = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]

/-- **The restriction pair is injective**: a class restricting to `0` on both summands is `0`. Its
representative `f` restricts to a coboundary on each summand; glue those primitives (`coboundary_
glueCochain` + `glue_cochainPullback`) to a global primitive of `f`. -/
theorem restrictPairCohomology_injective (n : ℕ) :
    Function.Injective (restrictPairCohomology A B n) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mem_bot]
  rw [LinearMap.mem_ker] at hx
  have hxl : cohomologyPullback (inlMap A B) n (Cohomology.mk (sumSpace A B) n f) = 0 :=
    congrArg Prod.fst hx
  have hxr : cohomologyPullback (inrMap A B) n (Cohomology.mk (sumSpace A B) n f) = 0 :=
    congrArg Prod.snd hx
  rw [cohomologyPullback_mk, mk_eq_zero_iff'] at hxl hxr
  show Cohomology.mk (sumSpace A B) n f = 0
  rw [mk_eq_zero_iff']
  show (f : SingularCochain (sumSpace A B) n) ∈ coboundaryRange (sumSpace A B) n
  rw [← glue_cochainPullback A B n f.1]
  cases n with
  | zero =>
      rw [show coboundaryRange A 0 = (⊥ : Submodule (ZMod 2) _) from rfl, Submodule.mem_bot] at hxl
      rw [show coboundaryRange B 0 = (⊥ : Submodule (ZMod 2) _) from rfl, Submodule.mem_bot] at hxr
      have hxl' : cochainPullback (inlMap A B) 0 f.1 = 0 := hxl
      have hxr' : cochainPullback (inrMap A B) 0 f.1 = 0 := hxr
      rw [hxl', hxr', show coboundaryRange (sumSpace A B) 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
        Submodule.mem_bot]
      exact map_zero _
  | succ m =>
      obtain ⟨aA, haA⟩ := hxl
      obtain ⟨bB, hbB⟩ := hxr
      refine ⟨glueCochain A B m (aA, bB), ?_⟩
      show coboundary (sumSpace A B) m (glueCochain A B m (aA, bB)) = _
      rw [coboundary_glueCochain]
      exact congrArg (glueCochain A B (m + 1)) (Prod.ext haA hbB)

/-- **The restriction pair is surjective**: any pair of classes is realized by the glued cocycle. -/
theorem restrictPairCohomology_surjective (n : ℕ) :
    Function.Surjective (restrictPairCohomology A B n) := by
  rintro ⟨x, y⟩
  obtain ⟨aA, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨bB, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hw : coboundaryₗ (sumSpace A B) n (glueCochain A B n (aA.1, bB.1)) = 0 := by
    show coboundary (sumSpace A B) n (glueCochain A B n (aA.1, bB.1)) = 0
    rw [coboundary_glueCochain, show coboundary A n aA.1 = coboundaryₗ A n aA.1 from rfl,
      LinearMap.mem_ker.mp aA.2, show coboundary B n bB.1 = coboundaryₗ B n bB.1 from rfl,
      LinearMap.mem_ker.mp bB.2]
    exact map_zero _
  refine ⟨Cohomology.mk (sumSpace A B) n ⟨glueCochain A B n (aA.1, bB.1), hw⟩, ?_⟩
  rw [restrictPairCohomology_apply, cohomologyPullback_mk, cohomologyPullback_mk]
  refine Prod.ext ?_ ?_
  · exact congrArg (Cohomology.mk A n) (Subtype.ext (cochainPullback_inl_glue A B n aA.1 bB.1))
  · exact congrArg (Cohomology.mk B n) (Subtype.ext (cochainPullback_inr_glue A B n aA.1 bB.1))

/-- **Disjoint-union cohomology additivity** (all degrees): `Hⁿ(A ⊔ B) ≃ₗ Hⁿ(A) × Hⁿ(B)` via the two
inclusion pullbacks. The cohomology-side companion to `SingularDisjointUnion.splitH0Equiv` (which is
degree-`0` only), and the absolute-cohomology input for the cylinder boundary `∂W = M ⊔ M`. -/
noncomputable def cohomologyDisjointSumEquiv (n : ℕ) :
    Cohomology (sumSpace A B) n ≃ₗ[ZMod 2] Cohomology A n × Cohomology B n :=
  LinearEquiv.ofBijective (restrictPairCohomology A B n)
    ⟨restrictPairCohomology_injective A B n, restrictPairCohomology_surjective A B n⟩

/-- **Finite-dimensionality of `Hⁿ(A ⊔ B)`** from the two summands — the `findim` input for the
cylinder boundary. -/
theorem finiteDimensional_cohomology_disjointSum (n : ℕ)
    (hA : FiniteDimensional (ZMod 2) (Cohomology A n))
    (hB : FiniteDimensional (ZMod 2) (Cohomology B n)) :
    FiniteDimensional (ZMod 2) (Cohomology (sumSpace A B) n) :=
  haveI := hA
  haveI := hB
  (cohomologyDisjointSumEquiv A B n).symm.finiteDimensional

/-- **The rank of `Hⁿ(A ⊔ B)` is the sum of the summand ranks** (finite-dimensional). For the cylinder
boundary `∂W = M ⊔ M` this gives `dim Hⁿ(∂W) = 2 · dim Hⁿ(M)`. -/
theorem finrank_cohomology_disjointSum (n : ℕ)
    [FiniteDimensional (ZMod 2) (Cohomology A n)]
    [FiniteDimensional (ZMod 2) (Cohomology B n)] :
    Module.finrank (ZMod 2) (Cohomology (sumSpace A B) n)
      = Module.finrank (ZMod 2) (Cohomology A n) + Module.finrank (ZMod 2) (Cohomology B n) := by
  rw [(cohomologyDisjointSumEquiv A B n).finrank_eq, Module.finrank_prod]

end SKEFTHawking.SingularCohomologyDisjointSum
