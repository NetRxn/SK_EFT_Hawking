/-
# Phase 5q.H close-out — disjoint-union additivity of singular **ℤ** COHOMOLOGY (all degrees)

The **integral** port of `SingularCohomologyDisjointSum` (which builds `Hⁿ(A ⊔ B; ℤ/2) ≅ Hⁿ(A;ℤ/2) ×
Hⁿ(B;ℤ/2)`). Here we build `Hⁿ(A ⊔ B; ℤ) ≃ₗ[ℤ] Hⁿ(A;ℤ) × Hⁿ(B;ℤ)` in **every** degree `n` — the
absolute integral-cohomology input the canonical disjoint-union intersection form consumes (`M ⊔ N` a
disjoint union of closed spin 4-manifolds, the σ-additivity substrate).

**Route (coefficient-agnostic chain-level splitting).** The topological/simplicial substrate is REUSED
verbatim from the mod-2 module: the two-summand space `sumSpace A B = TopCat.of (↑A ⊕ ↑B)`, the
inclusions `inlMap`/`inrMap`, and the simplex-factoring lemmas (`continuous_to_sum_factor`,
`factorLeft`/`factorRight`, `inl_factorLeft`/`inr_factorRight`, `realize_mapSimplex_inlMap/inrMap`) are
all purely topological (independent of the coefficient ring). Only the coefficient-dependent glue —
`glueValInt`/`glueCochainInt` (now `ℤ`-valued), the round-trips, glue-commutes-with-`δ`, and the
descent to the cohomology isomorphism — is redone over `ℤ`. The mod-2 proof transfers nearly verbatim
(the alternating signs `(-1)ⁱ` in the integral `δ` never enter these arguments — glue is a value-level
selection, so it commutes with any linear `δ`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyDisjointSum
import SKEFTHawking.SingularCohomologyFunctorialityInt

namespace SKEFTHawking.SingularCohomologyDisjointSumInt

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularCohomologyFunctorialityInt
open SKEFTHawking.SingularCohomologyDisjointSum (sumSpace inlMap inrMap inlMap_apply inrMap_apply
  realize_mapSimplex_inlMap realize_mapSimplex_inrMap)
open SKEFTHawking.SingularFunctoriality (mapSimplex)

variable (A B : TopCat)

/-! ## §1. The integral glue cochain -/

open Classical in
/-- The value of the integral glued cochain on a single simplex `σ` of `A ⊔ B`: `σ` factors through
one inclusion (`continuous_to_sum_factor`); evaluate `a` on its `A`-factor, or `b` on its `B`-factor.
The `ℤ`-analogue of `SingularCohomologyDisjointSum.glueVal`. -/
noncomputable def glueValInt {n : ℕ} (a : SingularCochainInt A n) (b : SingularCochainInt B n)
    (σ : (TopCat.toSSet.obj (sumSpace A B)).obj (op (SimplexCategory.mk n))) : ℤ :=
  if h : Set.range ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ)
      ⊆ Set.range (Sum.inl : ↑A → ↑A ⊕ ↑B) then
    a ((A.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
      (SingularCohomologyMod2.factorLeft
        ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ) h))
  else
    b ((B.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
      (SingularCohomologyMod2.factorRight
        ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ)
        ((SingularCohomologyMod2.continuous_to_sum_factor _).resolve_left h)))

/-- **The integral glue cochain** `Cⁿ(A;ℤ) × Cⁿ(B;ℤ) → Cⁿ(A ⊔ B;ℤ)`, `(a, b) ↦ glue`, `ℤ`-linear. -/
noncomputable def glueCochainInt (n : ℕ) :
    (SingularCochainInt A n × SingularCochainInt B n) →ₗ[ℤ] SingularCochainInt (sumSpace A B) n where
  toFun p := fun σ => glueValInt A B p.1 p.2 σ
  map_add' p q := by
    funext σ
    show glueValInt A B (p.1 + q.1) (p.2 + q.2) σ = glueValInt A B p.1 p.2 σ + glueValInt A B q.1 q.2 σ
    unfold glueValInt
    split <;> rfl
  map_smul' c p := by
    funext σ
    show glueValInt A B (c • p.1) (c • p.2) σ = c • glueValInt A B p.1 p.2 σ
    unfold glueValInt
    split <;> rfl

@[simp] theorem glueCochainInt_apply (n : ℕ) (a : SingularCochainInt A n) (b : SingularCochainInt B n)
    (σ : (TopCat.toSSet.obj (sumSpace A B)).obj (op (SimplexCategory.mk n))) :
    glueCochainInt A B n (a, b) σ = glueValInt A B a b σ := rfl

/-! ## §2. The round-trip identities -/

/-- **Left restriction of glue is the first component**: `inl*(glue a b) = a`. -/
theorem cochainPullbackInt_inl_glue (n : ℕ) (a : SingularCochainInt A n) (b : SingularCochainInt B n) :
    cochainPullbackInt (inlMap A B) n (glueCochainInt A B n (a, b)) = a := by
  funext τ
  rw [cochainPullbackInt_apply, glueCochainInt_apply]
  have hsub : Set.range ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n))
      (mapSimplex (inlMap A B) τ)) ⊆ Set.range (Sum.inl : ↑A → ↑A ⊕ ↑B) := by
    rw [realize_mapSimplex_inlMap]
    rintro x ⟨d, rfl⟩
    exact ⟨A.toSSetObjEquiv (op (SimplexCategory.mk n)) τ d, rfl⟩
  simp only [glueValInt, dif_pos hsub]
  have hfac : SingularCohomologyMod2.factorLeft
        ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n))
          (mapSimplex (inlMap A B) τ)) hsub = A.toSSetObjEquiv (op (SimplexCategory.mk n)) τ := by
    apply ContinuousMap.ext
    intro d
    apply Sum.inl_injective
    rw [SingularCohomologyMod2.inl_factorLeft, realize_mapSimplex_inlMap]
    rfl
  rw [hfac, Equiv.symm_apply_apply]

/-- **Right restriction of glue is the second component**: `inr*(glue a b) = b`. -/
theorem cochainPullbackInt_inr_glue (n : ℕ) (a : SingularCochainInt A n) (b : SingularCochainInt B n) :
    cochainPullbackInt (inrMap A B) n (glueCochainInt A B n (a, b)) = b := by
  funext τ
  rw [cochainPullbackInt_apply, glueCochainInt_apply]
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
  simp only [glueValInt, dif_neg hnsub]
  have hfac : SingularCohomologyMod2.factorRight
        ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n))
          (mapSimplex (inrMap A B) τ))
        ((SingularCohomologyMod2.continuous_to_sum_factor _).resolve_left hnsub)
      = B.toSSetObjEquiv (op (SimplexCategory.mk n)) τ := by
    apply ContinuousMap.ext
    intro d
    apply Sum.inr_injective
    rw [SingularCohomologyMod2.inr_factorRight, realize_mapSimplex_inrMap]
    rfl
  rw [hfac, Equiv.symm_apply_apply]

/-- **Glue of the restriction pair is the identity**: `glue (inl* f) (inr* f) = f`. -/
theorem glueInt_cochainPullback (n : ℕ) (f : SingularCochainInt (sumSpace A B) n) :
    glueCochainInt A B n
        (cochainPullbackInt (inlMap A B) n f, cochainPullbackInt (inrMap A B) n f) = f := by
  funext σ
  rw [glueCochainInt_apply]
  by_cases h : Set.range ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ)
      ⊆ Set.range (Sum.inl : ↑A → ↑A ⊕ ↑B)
  · simp only [glueValInt, dif_pos h, cochainPullbackInt_apply]
    have hkey : mapSimplex (inlMap A B) ((A.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
        (SingularCohomologyMod2.factorLeft
          ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ) h)) = σ := by
      apply (sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) |>.injective
      rw [realize_mapSimplex_inlMap, Equiv.apply_symm_apply]
      apply ContinuousMap.ext
      intro d
      rw [ContinuousMap.comp_apply, inlMap_apply, SingularCohomologyMod2.inl_factorLeft]
    rw [hkey]
  · simp only [glueValInt, dif_neg h, cochainPullbackInt_apply]
    have hR := (SingularCohomologyMod2.continuous_to_sum_factor
      ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ)).resolve_left h
    have hkey : mapSimplex (inrMap A B) ((B.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
        (SingularCohomologyMod2.factorRight
          ((sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) σ) hR)) = σ := by
      apply (sumSpace A B).toSSetObjEquiv (op (SimplexCategory.mk n)) |>.injective
      rw [realize_mapSimplex_inrMap, Equiv.apply_symm_apply]
      apply ContinuousMap.ext
      intro d
      rw [ContinuousMap.comp_apply, inrMap_apply, SingularCohomologyMod2.inr_factorRight]
    rw [hkey]

/-! ## §3. The cochain restriction pair and glue-commutes-with-`δ` -/

/-- The integral cochain restriction pair `Cⁿ(A ⊔ B;ℤ) → Cⁿ(A;ℤ) × Cⁿ(B;ℤ)`. -/
noncomputable def restrictPairCochainInt (n : ℕ) :
    SingularCochainInt (sumSpace A B) n →ₗ[ℤ] SingularCochainInt A n × SingularCochainInt B n :=
  (cochainPullbackInt (inlMap A B) n).prod (cochainPullbackInt (inrMap A B) n)

theorem restrictPairCochainInt_injective (n : ℕ) :
    Function.Injective (restrictPairCochainInt A B n) := by
  intro f g hfg
  have h1 : cochainPullbackInt (inlMap A B) n f = cochainPullbackInt (inlMap A B) n g :=
    congrArg Prod.fst hfg
  have h2 : cochainPullbackInt (inrMap A B) n f = cochainPullbackInt (inrMap A B) n g :=
    congrArg Prod.snd hfg
  rw [← glueInt_cochainPullback A B n f, ← glueInt_cochainPullback A B n g, h1, h2]

/-- **Glue commutes with `δ`**: `δ (glue a b) = glue (δa) (δb)`. From the two restrictions commuting
with `δ` (`coboundary_cochainPullbackInt`) and injectivity of the restriction pair. -/
theorem coboundary_glueCochainInt (n : ℕ) (a : SingularCochainInt A n) (b : SingularCochainInt B n) :
    coboundary (sumSpace A B) n (glueCochainInt A B n (a, b))
      = glueCochainInt A B (n + 1) (coboundary A n a, coboundary B n b) := by
  apply restrictPairCochainInt_injective A B (n + 1)
  apply Prod.ext
  · show cochainPullbackInt (inlMap A B) (n + 1)
        (coboundary (sumSpace A B) n (glueCochainInt A B n (a, b)))
      = cochainPullbackInt (inlMap A B) (n + 1)
        (glueCochainInt A B (n + 1) (coboundary A n a, coboundary B n b))
    rw [cochainPullbackInt_inl_glue, ← coboundary_cochainPullbackInt, cochainPullbackInt_inl_glue]
  · show cochainPullbackInt (inrMap A B) (n + 1)
        (coboundary (sumSpace A B) n (glueCochainInt A B n (a, b)))
      = cochainPullbackInt (inrMap A B) (n + 1)
        (glueCochainInt A B (n + 1) (coboundary A n a, coboundary B n b))
    rw [cochainPullbackInt_inr_glue, ← coboundary_cochainPullbackInt, cochainPullbackInt_inr_glue]

/-! ## §4. The disjoint-union integral cohomology additivity isomorphism -/

/-- The integral cohomology restriction pair `Hⁿ(A ⊔ B;ℤ) → Hⁿ(A;ℤ) × Hⁿ(B;ℤ)` via the two inclusion
pullbacks. -/
noncomputable def restrictPairCohomologyInt (n : ℕ) :
    Cohomology (sumSpace A B) n →ₗ[ℤ] Cohomology A n × Cohomology B n :=
  (cohomologyPullbackInt (inlMap A B) n).prod (cohomologyPullbackInt (inrMap A B) n)

@[simp] theorem restrictPairCohomologyInt_apply (n : ℕ) (x : Cohomology (sumSpace A B) n) :
    restrictPairCohomologyInt A B n x
      = (cohomologyPullbackInt (inlMap A B) n x, cohomologyPullbackInt (inrMap A B) n x) := rfl

/-- `Cohomology.mk` is zero iff its representative is a coboundary. -/
private theorem mk_eq_zero_iff' {X : TopCat} {n : ℕ} (a : LinearMap.ker (coboundaryₗ X n)) :
    Cohomology.mk X n a = 0 ↔ (a : SingularCochainInt X n) ∈ coboundaryRange X n := by
  show Submodule.Quotient.mk a = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]

/-- **The restriction pair is injective**: a class restricting to `0` on both summands is `0`. Its
representative `f` restricts to a coboundary on each summand; glue those primitives
(`coboundary_glueCochainInt` + `glueInt_cochainPullback`) to a global primitive of `f`. -/
theorem restrictPairCohomologyInt_injective (n : ℕ) :
    Function.Injective (restrictPairCohomologyInt A B n) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mem_bot]
  rw [LinearMap.mem_ker] at hx
  have hxl : cohomologyPullbackInt (inlMap A B) n (Cohomology.mk (sumSpace A B) n f) = 0 :=
    congrArg Prod.fst hx
  have hxr : cohomologyPullbackInt (inrMap A B) n (Cohomology.mk (sumSpace A B) n f) = 0 :=
    congrArg Prod.snd hx
  rw [cohomologyPullbackInt_mk, mk_eq_zero_iff'] at hxl hxr
  show Cohomology.mk (sumSpace A B) n f = 0
  rw [mk_eq_zero_iff']
  show (f : SingularCochainInt (sumSpace A B) n) ∈ coboundaryRange (sumSpace A B) n
  rw [← glueInt_cochainPullback A B n f.1]
  cases n with
  | zero =>
      rw [show coboundaryRange A 0 = (⊥ : Submodule ℤ _) from rfl, Submodule.mem_bot] at hxl
      rw [show coboundaryRange B 0 = (⊥ : Submodule ℤ _) from rfl, Submodule.mem_bot] at hxr
      have hxl' : cochainPullbackInt (inlMap A B) 0 f.1 = 0 := hxl
      have hxr' : cochainPullbackInt (inrMap A B) 0 f.1 = 0 := hxr
      rw [hxl', hxr', show coboundaryRange (sumSpace A B) 0 = (⊥ : Submodule ℤ _) from rfl,
        Submodule.mem_bot]
      exact map_zero _
  | succ m =>
      obtain ⟨aA, haA⟩ := hxl
      obtain ⟨bB, hbB⟩ := hxr
      refine ⟨glueCochainInt A B m (aA, bB), ?_⟩
      show coboundary (sumSpace A B) m (glueCochainInt A B m (aA, bB)) = _
      rw [coboundary_glueCochainInt]
      exact congrArg (glueCochainInt A B (m + 1)) (Prod.ext haA hbB)

/-- **The restriction pair is surjective**: any pair of classes is realized by the glued cocycle. -/
theorem restrictPairCohomologyInt_surjective (n : ℕ) :
    Function.Surjective (restrictPairCohomologyInt A B n) := by
  rintro ⟨x, y⟩
  obtain ⟨aA, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨bB, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hw : coboundaryₗ (sumSpace A B) n (glueCochainInt A B n (aA.1, bB.1)) = 0 := by
    show coboundary (sumSpace A B) n (glueCochainInt A B n (aA.1, bB.1)) = 0
    rw [coboundary_glueCochainInt, show coboundary A n aA.1 = coboundaryₗ A n aA.1 from rfl,
      LinearMap.mem_ker.mp aA.2, show coboundary B n bB.1 = coboundaryₗ B n bB.1 from rfl,
      LinearMap.mem_ker.mp bB.2]
    exact map_zero _
  refine ⟨Cohomology.mk (sumSpace A B) n ⟨glueCochainInt A B n (aA.1, bB.1), hw⟩, ?_⟩
  rw [restrictPairCohomologyInt_apply, cohomologyPullbackInt_mk, cohomologyPullbackInt_mk]
  refine Prod.ext ?_ ?_
  · exact congrArg (Cohomology.mk A n) (Subtype.ext (cochainPullbackInt_inl_glue A B n aA.1 bB.1))
  · exact congrArg (Cohomology.mk B n) (Subtype.ext (cochainPullbackInt_inr_glue A B n aA.1 bB.1))

/-- **Disjoint-union integral cohomology additivity** (all degrees): `Hⁿ(A ⊔ B;ℤ) ≃ₗ[ℤ] Hⁿ(A;ℤ) ×
Hⁿ(B;ℤ)` via the two inclusion pullbacks. The `ℤ`-analogue of
`SingularCohomologyDisjointSum.cohomologyDisjointSumEquiv`, and the absolute-cohomology input for the
canonical disjoint-union intersection form of `M ⊔ N`. -/
noncomputable def cohomologyDisjointSumEquivInt (n : ℕ) :
    Cohomology (sumSpace A B) n ≃ₗ[ℤ] Cohomology A n × Cohomology B n :=
  LinearEquiv.ofBijective (restrictPairCohomologyInt A B n)
    ⟨restrictPairCohomologyInt_injective A B n, restrictPairCohomologyInt_surjective A B n⟩

@[simp] theorem cohomologyDisjointSumEquivInt_apply (n : ℕ) (x : Cohomology (sumSpace A B) n) :
    cohomologyDisjointSumEquivInt A B n x
      = (cohomologyPullbackInt (inlMap A B) n x, cohomologyPullbackInt (inrMap A B) n x) := rfl

end SKEFTHawking.SingularCohomologyDisjointSumInt
