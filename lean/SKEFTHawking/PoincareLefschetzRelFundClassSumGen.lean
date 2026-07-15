/-
# Phase 5q.H (W-A addClosure, layer 3) — the interior local-generation of the block-sum class

Supplies the `gen`/`restricts` fields of the disjoint-union relative fundamental-class datum
(`PoincareLefschetzRelFundClassSum.blockSumCls`) and assembles the concrete
`PoincareLefschetzWuBlockAssembly.SumRelFundClass` term.

At an interior point `inl a` (`a ∉ S₁`) the local homology of the union pair excises to that of the
summand: `Hₙ(A ⊔ B, {inl a}ᶜ) ≅ Hₙ(A, {a}ᶜ)` — the pushforward `RelativeHomology.map inl` is a
**bijection** (the open-embedding excision triangle of `SingularFundamentalClassSum`, upgraded from the
injective statement to bijective). The interior local-iso `gen (inl a)` is `D₁.gen a` pulled through
this excision; symmetrically at `inr b`. The block class restricts to that generator because the
"other" summand's pushforward restricted to `{inl a}ᶜ` factors through `H(B, B) = 0`.

Carries `[T1Space]` on each carrier (points closed ⟹ the excision cover condition), discharged from the
manifold instances at the bordism level.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassSum
import SKEFTHawking.SingularFundamentalClassSum

namespace SKEFTHawking.PoincareLefschetzRelFundClassSumGen

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.SingularRelativeCohomologyDisjointSum
open SKEFTHawking.SingularFundamentalClassSum
open SKEFTHawking.SingularGoodCompactEuclidean
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzWuBlockAssembly
open SKEFTHawking.PoincareLefschetzRelFundClassSum

/-! ## §1. The open-embedding point pair-map is a BIJECTION (excision, bijective form). -/

/-- **The point pair-map along an open embedding is bijective** — the bijective upgrade of
`SingularFundamentalClassSum.relPointMap_injective_of_isOpenEmbedding`: the excision triangle
`φ = ambIncl (range φ) ∘ (embedding-to-range homeo)` composes a homeomorphism-induced iso with the
excision iso, both bijective. Takes the excision cover `int {φ x}ᶜ ∪ int (range φ) = univ` as a
hypothesis (rather than deriving it from `T1Space`), so it applies to non-`T1` ambient spaces (e.g.
bordism carriers) when the cover holds structurally — as it does for a disjoint-union inclusion. -/
theorem relPointMap_bijective_of_isOpenEmbedding {X Y : TopCat} (φ : C(↑X, ↑Y))
    (hφ : Topology.IsOpenEmbedding (⇑φ)) (x : ↑X) (m : ℕ)
    (hmt : Set.MapsTo (⇑φ) ({x}ᶜ : Set ↑X) ({φ x}ᶜ : Set ↑Y))
    (hcov : (⋃ U ∈ ({({φ x}ᶜ : Set ↑Y), Set.range (⇑φ)} : Set (Set ↑Y)), interior U) = Set.univ) :
    Function.Bijective (RelativeHomology.map φ hmt (m + 2)) := by
  set V : Set ↑Y := Set.range (⇑φ) with hV
  set e := hφ.isEmbedding.toHomeomorph with he
  set eC : C(↑X, ↑(sub V)) := ⟨e, e.continuous⟩ with heC
  set eC' : C(↑(sub V), ↑X) := ⟨e.symm, e.symm.continuous⟩ with heC'
  have h1 : Set.MapsTo (⇑eC) ({x}ᶜ : Set ↑X) (restr ({φ x}ᶜ : Set ↑Y) V) := by
    intro z hz hcon
    exact hz (Set.mem_singleton_iff.mpr (hφ.injective (Set.mem_singleton_iff.mp hcon)))
  have h1' : Set.MapsTo (⇑eC') (restr ({φ x}ᶜ : Set ↑Y) V) ({x}ᶜ : Set ↑X) := by
    intro w hw hcon
    refine hw (Set.mem_singleton_iff.mpr ?_)
    have : (w : ↑Y) = φ x := by
      rw [show (w : ↑Y) = ((e (e.symm w) : Set.range (⇑φ)) : ↑Y) from by
        rw [Homeomorph.apply_symm_apply],
        show e.symm w = x from Set.mem_singleton_iff.mp hcon]
      exact Topology.IsEmbedding.toHomeomorph_apply_coe hφ.isEmbedding x
    exact this
  have hbijA : Function.Bijective (RelativeHomology.map eC h1 (m + 2)) :=
    RelativeHomology.map_bijective_of_comp_id eC eC' h1 h1'
      (by ext z; exact e.symm_apply_apply z)
      (by ext w; exact congrArg Subtype.val (e.apply_symm_apply w)) (m + 2)
  have hbijB : Function.Bijective
      (RelativeHomology.map (ambIncl V) (A := restr ({φ x}ᶜ : Set ↑Y) V)
        (B := ({φ x}ᶜ : Set ↑Y)) (fun _ hp => hp) (m + 1 + 1)) := by
    have hbij0 : Function.Bijective (excisionMap ({φ x}ᶜ : Set ↑Y) V (m + 1 + 1)) :=
      ⟨excisionMap_injective _ _ (m + 1) hcov, excisionMap_surjective _ _ (m + 1) hcov⟩
    rwa [excisionMap_eq_map] at hbij0
  have hfun : φ = (ambIncl V).comp eC := by
    refine ContinuousMap.ext (fun z => ?_)
    exact (Topology.IsEmbedding.toHomeomorph_apply_coe hφ.isEmbedding z).symm
  have htri2 : RelativeHomology.map φ hmt (m + 2)
      = (RelativeHomology.map (ambIncl V) (A := restr ({φ x}ᶜ : Set ↑Y) V)
          (B := ({φ x}ᶜ : Set ↑Y)) (fun _ hp => hp) (m + 2)).comp
        (RelativeHomology.map eC h1 (m + 2)) := by
    rw [← RelativeHomology.map_comp]
    exact relHomologyMap_fun_congr hfun hmt (m + 2)
  rw [htri2, LinearMap.coe_comp]
  exact Function.Bijective.comp hbijB hbijA

/-! ## §2. `Hₙ(X, X) = 0` (the whole-space relative homology vanishes) — the away-kill for the
"other" summand. -/

/-- **`subspaceChains univ = ⊤`**: every chain lands in `univ` (`univ = ∅ᶜ`). -/
theorem subspaceChains_univ_eq_top {X : TopCat} (n : ℕ) :
    subspaceChains (Set.univ : Set ↑X) n = ⊤ := by
  rw [← Set.compl_empty]; exact subspaceChains_compl_empty_eq_top n

/-- The relative chain module of the pair `(X, univ) = (X, X)` is the zero module. -/
instance relativeChain_univ_subsingleton {X : TopCat} (n : ℕ) :
    Subsingleton (RelativeChain (Set.univ : Set ↑X) n) := by
  rw [RelativeChain, subspaceChains_univ_eq_top]
  infer_instance

/-- **`Hₙ(X, X) = 0`**: every relative-homology class of the pair `(X, univ) = (X, X)` is zero. -/
theorem relHomology_univ_eq_zero {X : TopCat} (n : ℕ)
    (x : RelativeHomology (Set.univ : Set ↑X) n) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show z = 0 from Subsingleton.elim z 0]
  exact Submodule.Quotient.mk_zero _

/-! ## §3. Restriction naturality: `restrictBd ∘ map φ = map φ ∘ relIncl` (both are `map φ`). -/

/-- **Restricting a pushforward is the pushforward-to-the-punctured-target**:
`restrictBd SY hy (φ_* α) = φ_* α` re-typed to the pair `(X, {φ⁻¹ y}ᶜ)`. Both are
`RelativeHomology.map φ` (differing only in the — proof-irrelevant — `MapsTo` hypothesis), so the
identity is functoriality of `map` through `relIncl = map id`. -/
theorem restrictBd_map {X Y : TopCat} (φ : C(↑X, ↑Y)) {SX : Set ↑X} {SY : Set ↑Y}
    (hφ : Set.MapsTo φ SX SY) {y : ↑Y} (hy : y ∉ SY) (n : ℕ)
    (hmt : Set.MapsTo φ SX ({y}ᶜ : Set ↑Y)) (α : RelativeHomology SX n) :
    restrictBd SY hy n (RelativeHomology.map φ hφ n α) = RelativeHomology.map φ hmt n α := by
  rw [restrictBd, relIncl, ← LinearMap.comp_apply, ← RelativeHomology.map_comp]
  rfl

/-- **Pushing a restriction forward is the pushforward-to-the-punctured-target**:
`φ_* (restrictBd SX hx β) = φ_* β` re-typed to the target `{φ x}ᶜ`. -/
theorem map_restrictBd {X Y : TopCat} (φ : C(↑X, ↑Y)) {SX : Set ↑X} {SY : Set ↑Y}
    (hφ : Set.MapsTo φ SX SY) {x : ↑X} (hx : x ∉ SX) (n : ℕ)
    (hmt : Set.MapsTo φ ({x}ᶜ : Set ↑X) SY) (β : RelativeHomology SX n) :
    RelativeHomology.map φ hmt n (restrictBd SX hx n β) = RelativeHomology.map φ hφ n β := by
  rw [restrictBd, relIncl, ← LinearMap.comp_apply, ← RelativeHomology.map_comp]
  rfl

/-- **Pushing an inclusion forward is the pushforward of the sub-pair**: `φ_* (relIncl β) = φ_* β`
re-typed. Both are `RelativeHomology.map φ`; the identity is `map_comp` through `relIncl = map id`. -/
theorem map_relIncl {X Y : TopCat} (φ : C(↑X, ↑Y)) {S T : Set ↑X} {SY : Set ↑Y}
    (hST : S ⊆ T) (hφ : Set.MapsTo φ S SY) (hφT : Set.MapsTo φ T SY) (n : ℕ)
    (β : RelativeHomology S n) :
    RelativeHomology.map φ hφ n β = RelativeHomology.map φ hφT n (relIncl hST n β) := by
  rw [relIncl, ← LinearMap.comp_apply, ← RelativeHomology.map_comp]
  rfl

/-! ## §4. The interior excision equivalences and the block-class datum on the disjoint sum. -/

section Sum

variable {A B : TopCat} {S₁ : Set ↑A} {S₂ : Set ↑B}

/-- `inl a ∉ S₁ ⊔ S₂ ↔ a ∉ S₁`. -/
theorem inl_notMem_sumSet {a : ↑A} :
    (Sum.inl a : ↑(sumSpace A B)) ∉ sumSet A B S₁ S₂ ↔ a ∉ S₁ := by
  simp only [sumSet, Set.mem_union, Set.mem_image, not_or, not_exists, not_and]
  constructor
  · intro h ha; exact (h.1 a ha rfl)
  · refine fun ha => ⟨fun c hc hce => ha (Sum.inl_injective hce ▸ hc), fun c _ hce => ?_⟩
    exact Sum.inl_ne_inr hce.symm

/-- `inr b ∉ S₁ ⊔ S₂ ↔ b ∉ S₂`. -/
theorem inr_notMem_sumSet {b : ↑B} :
    (Sum.inr b : ↑(sumSpace A B)) ∉ sumSet A B S₁ S₂ ↔ b ∉ S₂ := by
  simp only [sumSet, Set.mem_union, Set.mem_image, not_or, not_exists, not_and]
  constructor
  · intro h hb; exact (h.2 b hb rfl)
  · exact fun hb => ⟨fun c _ hce => Sum.inr_ne_inl hce.symm,
      fun c hc hce => hb (Sum.inr_injective hce ▸ hc)⟩

/-- The complement-of-point pair map hypothesis for `inl` at `a`. -/
theorem mapsTo_inl_compl (a : ↑A) :
    Set.MapsTo (inlMap A B) ({a}ᶜ : Set ↑A)
      ({(Sum.inl a : ↑(sumSpace A B))}ᶜ : Set ↑(sumSpace A B)) :=
  fun _ hz hcon => hz (Set.mem_singleton_iff.mpr (Sum.inl_injective (Set.mem_singleton_iff.mp hcon)))

/-- The complement-of-point pair map hypothesis for `inr` at `b`. -/
theorem mapsTo_inr_compl (b : ↑B) :
    Set.MapsTo (inrMap A B) ({b}ᶜ : Set ↑B)
      ({(Sum.inr b : ↑(sumSpace A B))}ᶜ : Set ↑(sumSpace A B)) :=
  fun _ hz hcon => hz (Set.mem_singleton_iff.mpr (Sum.inr_injective (Set.mem_singleton_iff.mp hcon)))

/-- **The excision cover at `inl a`** — `int {inl a}ᶜ ∪ int (range inl) = univ`, holding structurally
(no `T1` needed): every `inl _` lands in the open `range inl`, every `inr _` in the open
`range inr ⊆ {inl a}ᶜ`. -/
theorem sumCover_inl (a : ↑A) :
    (⋃ U ∈ ({({(Sum.inl a : ↑(sumSpace A B))}ᶜ : Set ↑(sumSpace A B)),
        Set.range (⇑(inlMap A B))} : Set (Set ↑(sumSpace A B))), interior U) = Set.univ := by
  rw [Set.biUnion_pair, Set.eq_univ_iff_forall]
  have hoInl : IsOpen (Set.range (⇑(inlMap A B))) :=
    (Topology.IsOpenEmbedding.inl (X := ↑A) (Y := ↑B)).isOpen_range
  have hoInr : IsOpen (Set.range (⇑(inrMap A B))) :=
    (Topology.IsOpenEmbedding.inr (X := ↑A) (Y := ↑B)).isOpen_range
  rintro (a' | b')
  · exact Or.inr (by rw [hoInl.interior_eq]; exact ⟨a', rfl⟩)
  · refine Or.inl (interior_maximal (fun _ ⟨w, hw⟩ hcon => ?_) hoInr ⟨b', rfl⟩)
    exact Sum.inr_ne_inl (hw.trans (Set.mem_singleton_iff.mp hcon))

/-- **The excision cover at `inr b`**. -/
theorem sumCover_inr (b : ↑B) :
    (⋃ U ∈ ({({(Sum.inr b : ↑(sumSpace A B))}ᶜ : Set ↑(sumSpace A B)),
        Set.range (⇑(inrMap A B))} : Set (Set ↑(sumSpace A B))), interior U) = Set.univ := by
  rw [Set.biUnion_pair, Set.eq_univ_iff_forall]
  have hoInl : IsOpen (Set.range (⇑(inlMap A B))) :=
    (Topology.IsOpenEmbedding.inl (X := ↑A) (Y := ↑B)).isOpen_range
  have hoInr : IsOpen (Set.range (⇑(inrMap A B))) :=
    (Topology.IsOpenEmbedding.inr (X := ↑A) (Y := ↑B)).isOpen_range
  rintro (a' | b')
  · refine Or.inl (interior_maximal (fun _ ⟨w, hw⟩ hcon => ?_) hoInl ⟨a', rfl⟩)
    exact Sum.inl_ne_inr (hw.trans (Set.mem_singleton_iff.mp hcon))
  · exact Or.inr (by rw [hoInr.interior_eq]; exact ⟨b', rfl⟩)

/-- **Interior excision at `inl a`**: `Hₙ(A, {a}ᶜ) ≅ Hₙ(A ⊔ B, {inl a}ᶜ)` via the (bijective)
pushforward along the open embedding `inl`. -/
noncomputable def sumExcInl (a : ↑A) :
    RelativeHomology ({a}ᶜ : Set ↑A) 5 ≃ₗ[ZMod 2]
      RelativeHomology ({(Sum.inl a : ↑(sumSpace A B))}ᶜ : Set ↑(sumSpace A B)) 5 :=
  LinearEquiv.ofBijective (RelativeHomology.map (inlMap A B) (mapsTo_inl_compl a) 5)
    (relPointMap_bijective_of_isOpenEmbedding (inlMap A B) Topology.IsOpenEmbedding.inl a 3
      (mapsTo_inl_compl a) (sumCover_inl a))

/-- **Interior excision at `inr b`**: `Hₙ(B, {b}ᶜ) ≅ Hₙ(A ⊔ B, {inr b}ᶜ)`. -/
noncomputable def sumExcInr (b : ↑B) :
    RelativeHomology ({b}ᶜ : Set ↑B) 5 ≃ₗ[ZMod 2]
      RelativeHomology ({(Sum.inr b : ↑(sumSpace A B))}ᶜ : Set ↑(sumSpace A B)) 5 :=
  LinearEquiv.ofBijective (RelativeHomology.map (inrMap A B) (mapsTo_inr_compl b) 5)
    (relPointMap_bijective_of_isOpenEmbedding (inrMap A B) Topology.IsOpenEmbedding.inr b 3
      (mapsTo_inr_compl b) (sumCover_inr b))

@[simp] theorem sumExcInl_apply (a : ↑A) (α : RelativeHomology ({a}ᶜ : Set ↑A) 5) :
    sumExcInl (A := A) (B := B) a α = RelativeHomology.map (inlMap A B) (mapsTo_inl_compl a) 5 α :=
  rfl

@[simp] theorem sumExcInr_apply (b : ↑B) (α : RelativeHomology ({b}ᶜ : Set ↑B) 5) :
    sumExcInr (A := A) (B := B) b α = RelativeHomology.map (inrMap A B) (mapsTo_inr_compl b) 5 α :=
  rfl

/-- **The block-sum class restricts, at an interior point `inl a`, to the excised `A`-generator**:
`restrictBd (blockSumCls) = sumExcInl (restrictBd D₁.cls)`. The `B`-summand's contribution restricts
to `H(B, B) = 0` (the away-kill); the `A`-summand's is the excision-transported restriction. -/
theorem restrictBd_blockSumCls_inl (D₁ : RelFundClassDatum (m := 3) S₁)
    (D₂ : RelFundClassDatum (m := 3) S₂) {a : ↑A} (ha : a ∉ S₁)
    (hx : (Sum.inl a : ↑(sumSpace A B)) ∉ sumSet A B S₁ S₂) :
    restrictBd (sumSet A B S₁ S₂) hx 5 (blockSumCls D₁ D₂)
      = sumExcInl a (restrictBd S₁ ha 5 D₁.cls) := by
  have hmt1 : Set.MapsTo (inlMap A B) S₁ ({(Sum.inl a : ↑(sumSpace A B))}ᶜ) :=
    fun s hs hcon => ha (Sum.inl_injective (Set.mem_singleton_iff.mp hcon) ▸ hs)
  have hmt2 : Set.MapsTo (inrMap A B) S₂ ({(Sum.inl a : ↑(sumSpace A B))}ᶜ) :=
    fun s _ hcon => Sum.inr_ne_inl (Set.mem_singleton_iff.mp hcon)
  have huniv : Set.MapsTo (inrMap A B) (Set.univ : Set ↑B) ({(Sum.inl a : ↑(sumSpace A B))}ᶜ) :=
    fun s _ hcon => Sum.inr_ne_inl (Set.mem_singleton_iff.mp hcon)
  rw [blockSumCls, map_add, restrictBd_map (inlMap A B) (mapsTo_inl A B S₁ S₂) hx 5 hmt1,
    restrictBd_map (inrMap A B) (mapsTo_inr A B S₁ S₂) hx 5 hmt2,
    map_relIncl (inrMap A B) (Set.subset_univ S₂) hmt2 huniv 5 D₂.cls,
    relHomology_univ_eq_zero 5 (relIncl (Set.subset_univ S₂) 5 D₂.cls), map_zero, add_zero,
    sumExcInl_apply, map_restrictBd (inlMap A B) hmt1 ha 5 (mapsTo_inl_compl a) D₁.cls]

/-- **The block-sum class restricts, at an interior point `inr b`, to the excised `B`-generator**. -/
theorem restrictBd_blockSumCls_inr (D₁ : RelFundClassDatum (m := 3) S₁)
    (D₂ : RelFundClassDatum (m := 3) S₂) {b : ↑B} (hb : b ∉ S₂)
    (hx : (Sum.inr b : ↑(sumSpace A B)) ∉ sumSet A B S₁ S₂) :
    restrictBd (sumSet A B S₁ S₂) hx 5 (blockSumCls D₁ D₂)
      = sumExcInr b (restrictBd S₂ hb 5 D₂.cls) := by
  have hmt1 : Set.MapsTo (inlMap A B) S₁ ({(Sum.inr b : ↑(sumSpace A B))}ᶜ) :=
    fun s _ hcon => Sum.inl_ne_inr (Set.mem_singleton_iff.mp hcon)
  have huniv : Set.MapsTo (inlMap A B) (Set.univ : Set ↑A) ({(Sum.inr b : ↑(sumSpace A B))}ᶜ) :=
    fun s _ hcon => Sum.inl_ne_inr (Set.mem_singleton_iff.mp hcon)
  have hmt2 : Set.MapsTo (inrMap A B) S₂ ({(Sum.inr b : ↑(sumSpace A B))}ᶜ) :=
    fun s hs hcon => hb (Sum.inr_injective (Set.mem_singleton_iff.mp hcon) ▸ hs)
  rw [blockSumCls, map_add, restrictBd_map (inlMap A B) (mapsTo_inl A B S₁ S₂) hx 5 hmt1,
    restrictBd_map (inrMap A B) (mapsTo_inr A B S₁ S₂) hx 5 hmt2,
    map_relIncl (inlMap A B) (Set.subset_univ S₁) hmt1 huniv 5 D₁.cls,
    relHomology_univ_eq_zero 5 (relIncl (Set.subset_univ S₁) 5 D₁.cls), map_zero, zero_add,
    sumExcInr_apply, map_restrictBd (inrMap A B) hmt2 hb 5 (mapsTo_inr_compl b) D₂.cls]

/-! ## §5. The disjoint-sum relative fundamental-class datum and the `SumRelFundClass`. -/

/-- **The interior local-iso family of the block-sum class**: at `inl a` (resp. `inr b`) it is
`D₁.gen a` (resp. `D₂.gen b`) pulled through the interior excision `sumExcInl` (resp. `sumExcInr`). -/
noncomputable def sumGen (D₁ : RelFundClassDatum (m := 3) S₁) (D₂ : RelFundClassDatum (m := 3) S₂) :
    ∀ x : ↑(sumSpace A B), x ∉ sumSet A B S₁ S₂ →
      (RelativeHomology ({x}ᶜ : Set ↑(sumSpace A B)) 5 ≃ₗ[ZMod 2] ZMod 2)
  | Sum.inl a, hx => (sumExcInl a).symm.trans (D₁.gen a (inl_notMem_sumSet.mp hx))
  | Sum.inr b, hx => (sumExcInr b).symm.trans (D₂.gen b (inr_notMem_sumSet.mp hx))

/-- **The disjoint-sum relative fundamental-class datum**: the block-sum class with its
excision-transported interior local generators, restricting to them by
`restrictBd_blockSumCls_inl/inr`. -/
noncomputable def sumRelFundClassDatum (D₁ : RelFundClassDatum (m := 3) S₁)
    (D₂ : RelFundClassDatum (m := 3) S₂) : RelFundClassDatum (m := 3) (sumSet A B S₁ S₂) where
  cls := blockSumCls D₁ D₂
  gen := sumGen D₁ D₂
  restricts := by
    rintro (a | b) hx
    · have ha := inl_notMem_sumSet.mp hx
      rw [restrictBd_blockSumCls_inl D₁ D₂ ha hx, D₁.restricts a ha]
      show sumExcInl a ((D₁.gen a ha).symm 1) = (sumGen D₁ D₂ (Sum.inl a) hx).symm 1
      rw [sumGen, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
    · have hb := inr_notMem_sumSet.mp hx
      rw [restrictBd_blockSumCls_inr D₁ D₂ hb hx, D₂.restricts b hb]
      show sumExcInr b ((D₂.gen b hb).symm 1) = (sumGen D₁ D₂ (Sum.inr b) hx).symm 1
      rw [sumGen, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]

/-- **THE BLOCK-SUM RELATIVE FUNDAMENTAL CLASS** — the concrete `SumRelFundClass A B S₁ S₂`: the
`sumD` block-diagonal datum (`sumRelFundClassDatum`) with the μ-block-sum identity (`blockSumCls_mu`).
This is the sole interface `PoincareLefschetzWuBlockAssembly.exists_wuAdmPinned_sum` consumes, so it
closes the disjoint-union `addClosure` residual. Requires `[T1Space]` on each carrier (discharged from
the manifold instances at the bordism level). -/
noncomputable def sumRelFundClass : SumRelFundClass A B S₁ S₂ where
  sumD := sumRelFundClassDatum
  sumD_mu := fun D₁ D₂ z => by
    rw [RelFundClassDatum.mu_apply]
    exact blockSumCls_mu D₁ D₂ z

end Sum

end SKEFTHawking.PoincareLefschetzRelFundClassSumGen
