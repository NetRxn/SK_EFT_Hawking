import Mathlib
import SKEFTHawking.SingularFundamentalClassPushforward
import SKEFTHawking.SingularCochainGlue
import SKEFTHawking.SingularGoodCompactEuclidean

/-!
# Phase 5q.G (G3 F-ladder, F7c) — the fundamental class of a disjoint union is the sum

`[M ⊕ N] = inl₊[M] + inr₊[N]` via the F4 uniqueness machinery
(`eq_fundamentalClass_of_restricts_generator`): at a point `inl x`,

* the `inr`-summand restricts to `0` — the *away-kill*: a class pushed forward along a map
  missing `y` factors through `H(X, X) = 0` (`relativeHomology_compl_empty_eq_zero`), purely
  structurally;
* the `inl`-summand restricts to the pair-map image of the `M`-local generator (F4 naturality),
  which is **nonzero** — the pair map along an *open embedding* is injective by excision
  (`excisionMap` at the cover `{{φ x}ᶜ, range φ}`, transported to `RelativeHomology.map` via
  `excisionMap_eq_map` and the embedding-to-range homeomorphism) — hence *the* generator of
  `H(M ⊕ N | inl x) ≅ ℤ/2` (`linearEquiv_zmod2_apply_eq_one`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularRelativeEmpty
open SKEFTHawking.SingularRelativeFunctoriality SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularManifoldFundamentalClass SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.SingularFundamentalClassPushforward SKEFTHawking.SingularCochainGlue
open SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularMayerVietorisLES

namespace SKEFTHawking.SingularFundamentalClassSum

/-- `RelativeHomology.map` respects equality of the underlying continuous maps (the `MapsTo`
side conditions are proof-irrelevant). -/
theorem relHomologyMap_fun_congr {X Y : TopCat} {φ ψ : C(↑X, ↑Y)} (h : φ = ψ)
    {A : Set ↑X} {B : Set ↑Y} (hA : Set.MapsTo φ A B) (n : ℕ) :
    RelativeHomology.map φ hA n = RelativeHomology.map ψ (h ▸ hA) n := by
  subst h; rfl

/-- **The away-kill**: a class pushed forward along a map whose range misses `y` restricts to
`0` at `y` — the restriction factors through `H(X | ∅ᶜ) = H(X, X) = 0`. -/
theorem restrictHomologyToPoint_map_of_notMem {X Y : TopCat} (φ : C(↑X, ↑Y)) {y : ↑Y}
    (hy : y ∉ Set.range φ) (n : ℕ) (α : Homology X n) :
    restrictHomologyToPoint (X := Y) y n (Homology.map φ n α) = 0 := by
  have hinner : (relHomologyEmptyEquiv (X := Y) n).symm (Homology.map φ n α)
      = RelativeHomology.map φ (Set.mapsTo_empty ⇑φ ∅) n
        ((relHomologyEmptyEquiv (X := X) n).symm α) := by
    rw [LinearEquiv.symm_apply_eq, ← emptyEquiv_naturality, LinearEquiv.apply_symm_apply]
  have hmt2 : Set.MapsTo (⇑φ) ((∅ : Set ↑X)ᶜ) ({y}ᶜ : Set ↑Y) :=
    fun z _ hz => hy ⟨z, (Set.mem_singleton_iff.mp hz).symm ▸ rfl⟩
  have hz := SKEFTHawking.SingularGoodCompactEuclidean.relativeHomology_compl_empty_eq_zero
    (X := X) n
    (relIncl (Set.empty_subset ((∅ : Set ↑X)ᶜ)) n ((relHomologyEmptyEquiv (X := X) n).symm α))
  show relIncl (Set.empty_subset ({y}ᶜ : Set ↑Y)) n
      ((relHomologyEmptyEquiv (X := Y) n).symm (Homology.map φ n α)) = 0
  rw [hinner, ← relIncl_map φ (Set.empty_subset ((∅ : Set ↑X)ᶜ)) (Set.mapsTo_empty ⇑φ ∅) hmt2
      (Set.empty_subset ({y}ᶜ : Set ↑Y)) n,
    hz, map_zero]

section OpenEmbedding

variable {X Y : TopCat} [T1Space ↑Y]

/-- **The point pair-map along an open embedding is injective** — excision at the cover
`{{φ x}ᶜ, range φ}` identifies `H(sub (range φ) | ·)` with `H(Y | φ x)`, and the
embedding-to-range homeomorphism identifies the source with `H(X | x)`. -/
theorem relPointMap_injective_of_isOpenEmbedding (φ : C(↑X, ↑Y))
    (hφ : Topology.IsOpenEmbedding (⇑φ)) (x : ↑X) (m : ℕ)
    (hmt : Set.MapsTo (⇑φ) ({x}ᶜ : Set ↑X) ({φ x}ᶜ : Set ↑Y)) :
    Function.Injective (RelativeHomology.map φ hmt (m + 2)) := by
  set V : Set ↑Y := Set.range (⇑φ) with hV
  -- the embedding-to-range homeomorphism, as continuous maps both ways
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
  -- the excision half: `map (ambIncl V)` is bijective in degree `m+2 = (m+1)+1`
  have hcov : (⋃ U ∈ ({({φ x}ᶜ : Set ↑Y), V} : Set (Set ↑Y)), interior U) = Set.univ := by
    rw [Set.biUnion_pair, (isClosed_singleton (x := φ x)).isOpen_compl.interior_eq,
      hφ.isOpen_range.interior_eq, Set.eq_univ_iff_forall]
    intro z
    by_cases h : z = φ x
    · exact Or.inr (h ▸ ⟨x, rfl⟩)
    · exact Or.inl h
  have hbijB : Function.Bijective
      (RelativeHomology.map (ambIncl V) (A := restr ({φ x}ᶜ : Set ↑Y) V)
        (B := ({φ x}ᶜ : Set ↑Y)) (fun _ hp => hp) (m + 1 + 1)) := by
    have hbij0 : Function.Bijective (excisionMap ({φ x}ᶜ : Set ↑Y) V (m + 1 + 1)) :=
      ⟨excisionMap_injective _ _ (m + 1) hcov, excisionMap_surjective _ _ (m + 1) hcov⟩
    rwa [excisionMap_eq_map] at hbij0
  -- the triangle: `φ = ambIncl V ∘ e`
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
  exact Function.Injective.comp hbijB.1 hbijA.1

end OpenEmbedding

section GeneratorTransport

variable {m : ℕ} {P Q : Type} [TopologicalSpace P] [T2Space P] [CompactSpace P] [Nonempty P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) P] [TopologicalSpace Q] [T2Space Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) Q]

/-- **The pushforward of `[P]` along an open embedding restricts to the local generator at image
points** — F4 naturality + excision injectivity + the unique-nonzero of `H(Q | φ x) ≅ ℤ/2`. -/
theorem restrict_map_fundClass_openEmbedding
    (φ : C(↑(TopCat.of P), ↑(TopCat.of Q))) (hφ : Topology.IsOpenEmbedding (⇑φ)) (x : P) :
    restrictHomologyToPoint (X := TopCat.of Q) (φ x) (m + 2)
        (Homology.map φ (m + 2) (fundamentalClass (m := m) (M := P)))
      = (SKEFTHawking.SingularChartBridge.manifoldLocalIso (φ x)).symm 1 := by
  haveI : T1Space ↑(TopCat.of Q) := inferInstanceAs (T1Space Q)
  have hmt : Set.MapsTo (⇑φ) ({x}ᶜ : Set ↑(TopCat.of P)) ({φ x}ᶜ : Set ↑(TopCat.of Q)) :=
    fun z hz hez => hz (Set.mem_singleton_iff.mpr
      (hφ.injective (Set.mem_singleton_iff.mp hez)))
  rw [restrictHomologyToPoint_naturality φ x hmt (m + 2), fundamentalClass_restricts (m := m) x]
  have hinj := relPointMap_injective_of_isOpenEmbedding φ hφ x m hmt
  have hgen_ne : ((SKEFTHawking.SingularChartBridge.manifoldLocalIso x).symm 1 :
      RelativeHomology ({x}ᶜ : Set ↑(TopCat.of P)) (m + 2)) ≠ 0 := by
    intro h
    have h1 := congrArg (SKEFTHawking.SingularChartBridge.manifoldLocalIso x) h
    rw [LinearEquiv.apply_symm_apply, map_zero] at h1
    exact one_ne_zero h1
  have hv_ne : RelativeHomology.map φ hmt (m + 2)
      ((SKEFTHawking.SingularChartBridge.manifoldLocalIso x).symm 1) ≠ 0 :=
    fun h => hgen_ne (hinj (by rw [h]; exact (map_zero _).symm))
  have h1 := SKEFTHawking.SingularConvexStageIso.linearEquiv_zmod2_apply_eq_one
    (SKEFTHawking.SingularChartBridge.manifoldLocalIso (φ x)) hv_ne
  exact (LinearEquiv.eq_symm_apply _).mpr h1

end GeneratorTransport

section Sum

variable {m : ℕ} {M N : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
  [TopologicalSpace N] [T2Space N] [CompactSpace N] [Nonempty N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) N]

/-- **F7c — the fundamental class of a disjoint union is the sum of the pieces'**:
`[M ⊕ N] = inl₊[M] + inr₊[N]` (each summand restricts to the generator on its own component —
open-embedding transport — and to `0` on the other — the away-kill; F4 uniqueness closes). -/
theorem fundamentalClass_sum :
    fundamentalClass (m := m) (M := M ⊕ N)
      = Homology.map (inlC M N) (m + 2) (fundamentalClass (m := m) (M := M))
        + Homology.map (inrC M N) (m + 2) (fundamentalClass (m := m) (M := N)) := by
  refine (eq_fundamentalClass_of_restricts_generator (fun z => ?_)).symm
  rw [map_add]
  cases z with
  | inl x =>
      rw [show (Sum.inl x : M ⊕ N) = (inlC M N) x from rfl,
        restrict_map_fundClass_openEmbedding (inlC M N) Topology.IsOpenEmbedding.inl x,
        restrictHomologyToPoint_map_of_notMem (inrC M N)
          (by rintro ⟨w, hw⟩; exact Sum.inr_ne_inl hw) (m + 2), add_zero]
  | inr y =>
      rw [show (Sum.inr y : M ⊕ N) = (inrC M N) y from rfl,
        restrict_map_fundClass_openEmbedding (inrC M N) Topology.IsOpenEmbedding.inr y,
        restrictHomologyToPoint_map_of_notMem (inlC M N)
          (by rintro ⟨w, hw⟩; exact Sum.inl_ne_inr hw) (m + 2), zero_add]

end Sum

end SKEFTHawking.SingularFundamentalClassSum
