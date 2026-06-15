/-
# Phase 5q.F (w₂-foundation, brick 6c-c7c.5): the singular barycentric subdivision

Assembles the singular subdivision operator `Sd : Cₙ(X) → Cₙ(X)` from the verified affine engine:
`Sd(σ) := σ_# (Sd ι_n)`, where `ι_n` is the identity affine `n`-simplex of `Δⁿ` (vertices the standard
basis), `Sd ι_n = linSubdiv n ι_n` its barycentric subdivision (kept in `Δⁿ` by the convexity invariant
`SingularSubdivisionConvex`), and `σ_# = pushChainM σ` the module-valued pushforward
(`SingularExcisionPushforward`).

This file currently establishes the **chain-level boundary naturality of the module pushforward** on
in-`Δᴺ` chains — `∂ ∘ σ_# = σ_# ∘ ∂` for `c ∈ chainsIn (Δᴺ)` — the transport lemma that (with the
linear-map naturality `SingularSubdivisionNatural` and the facet-inclusion identity) yields the singular
chain map `∂Sd = Sd∂`. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularExcisionPushforward
import SKEFTHawking.SingularSubdivisionConvex
import SKEFTHawking.SingularSubdivisionNatural

namespace SKEFTHawking.SingularSubdivision

open CategoryTheory Opposite
open SKEFTHawking.SingularExcisionMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularSubdivisionNatural
open SKEFTHawking.SingularExcisionPushforward SKEFTHawking.SingularSubdivisionConvex

/-- **The module pushforward is a chain map on in-`Δᴺ` chains**: `∂ (σ_# c) = σ_# (∂ c)` for any affine
`(n+1)`-chain `c` whose simplices have all vertices in `Δᴺ` (`c ∈ chainsIn (stdSimplex …)`). By
`ℤ/2`-linearity over the spanning simplices + the per-basis `pushSimplexM_face` (whose `Δᴺ`-membership
hypothesis is exactly what `chainsIn` provides). -/
theorem pushChainM_chainBoundary {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    {c : LinChain (Fin (N + 1) → ℝ) (n + 1)}
    (hc : c ∈ chainsIn (stdSimplex ℝ (Fin (N + 1))) (n + 1)) :
    chainBoundary X n (pushChainM σ c) = pushChainM σ (linBoundary n c) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨u, hu, rfl⟩
    rw [pushChainM_single, chainBoundary_single, boundaryBasis, linBoundary_single,
      linBoundaryBasis, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pushSimplexM_face σ hu, pushChainM_single]
  · simp only [map_zero]
  · intro x y _ _ hx hy; simp only [map_add]; rw [hx, hy]
  · intro a x _ hx; simp only [map_smul]; rw [hx]

open SKEFTHawking.SingularSubdivisionNatural in
/-- **Per-simplex facet functoriality**: pushing an in-`Δᴺ` affine simplex `w` of `Δᴺ`, first included
into `Δᴺ⁺¹` via the linear coface `Lᵢ = FunOnFinite.linearMap (δ i)` and then along `σ`, equals pushing
`w` directly along the `i`-th face `face i σ`. The geometric heart of `∂Sd = Sd∂`: it identifies the
subdivision of the `i`-th facet of `Δᴺ⁺¹` (pushed by `σ`) with the subdivision of `Δᴺ` pushed by `∂ᵢσ`.
Combines `toSSetObjEquiv_face` + `stdSimplexMap_comp_affineSimplexStd`. -/
theorem pushSimplexM_facetIncl {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (N + 1)))) (i : Fin (N + 2))
    {w : Fin (n + 1) → (Fin (N + 1) → ℝ)} (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin (N + 1))) :
    pushSimplexM σ
        (fun j => FunOnFinite.linearMap ℝ ℝ (ConcreteCategory.hom (SimplexCategory.δ i)) (w j))
      = pushSimplexM (face i σ) w := by
  have hLw : ∀ j, FunOnFinite.linearMap ℝ ℝ (ConcreteCategory.hom (SimplexCategory.δ i)) (w j)
      ∈ stdSimplex ℝ (Fin (N + 1 + 1)) :=
    fun j => (_root_.stdSimplex.map (ConcreteCategory.hom (SimplexCategory.δ i)) ⟨w j, hw j⟩).2
  have hvert : (fun j => (⟨FunOnFinite.linearMap ℝ ℝ (ConcreteCategory.hom (SimplexCategory.δ i)) (w j),
        hLw j⟩ : stdSimplex ℝ (Fin (N + 1 + 1))))
      = fun j => _root_.stdSimplex.map (SimplexCategory.δ i) (⟨w j, hw j⟩) := by
    funext j; exact Subtype.ext (stdSimplex.map_coe _ ⟨w j, hw j⟩).symm
  rw [pushSimplexM_of_mem σ hLw, pushSimplexM_of_mem (face i σ) hw, hvert]
  simp only [pushSimplex]
  refine congrArg (X.toSSetObjEquiv (op (SimplexCategory.mk n))).symm ?_
  rw [toSSetObjEquiv_face, ContinuousMap.comp_assoc]
  exact congrArg (((X.toSSetObjEquiv (op (SimplexCategory.mk (N + 1)))) σ).comp ·)
    (stdSimplexMap_comp_affineSimplexStd i (fun j => (⟨w j, hw j⟩ : stdSimplex ℝ (Fin (N + 1))))).symm

/-- **Chain-level facet functoriality**: `σ_# ∘ (Lᵢ)_* = (∂ᵢσ)_#` on in-`Δᴺ` chains. The `ℤ/2`-linear
lift of `pushSimplexM_facetIncl` over `chainsIn`: pushing an in-`Δᴺ` chain through the linear coface
`Lᵢ` and then along `σ` equals pushing along the face `∂ᵢσ`. -/
theorem pushChainM_mapVerts {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (N + 1)))) (i : Fin (N + 2))
    {c : LinChain (Fin (N + 1) → ℝ) n}
    (hc : c ∈ chainsIn (stdSimplex ℝ (Fin (N + 1))) n) :
    pushChainM σ (mapVerts (FunOnFinite.linearMap ℝ ℝ i.succAbove) n c)
      = pushChainM (face i σ) c := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨w, hw, rfl⟩
    rw [mapVerts_single, pushChainM_single, pushChainM_single]
    exact congrArg (Finsupp.single · 1) (pushSimplexM_facetIncl σ i hw)
  · simp only [map_zero]
  · intro x y _ _ hx hy; simp only [map_add]; rw [hx, hy]
  · intro a x _ hx; simp only [map_smul]; rw [hx]

/-- The **identity affine `n`-simplex** of `Δⁿ`: the single simplex on the `n+1` standard basis vertices
`eⱼ = Pi.single j 1` of `Δⁿ ⊆ (Fin (n+1) → ℝ)`. Its barycentric subdivision, pushed along `σ`, is `Sd σ`. -/
noncomputable def idChain (n : ℕ) : LinChain (Fin (n + 1) → ℝ) n :=
  Finsupp.single (fun j => Pi.single j 1) 1

theorem idChain_mem (n : ℕ) : idChain n ∈ chainsIn (stdSimplex ℝ (Fin (n + 1))) n :=
  single_mem_chainsIn (fun j => single_mem_stdSimplex ℝ j)

/-- **The singular barycentric subdivision** `Sd : Cₙ(X) → Cₙ(X)`: `Sd σ := σ_# (Sd ι_n)`, the
`ℤ/2`-linear extension of pushing the affine subdivision of the identity simplex along `σ`. -/
noncomputable def singularSd (X : TopCat) (n : ℕ) :
    SingularChain X n →ₗ[ZMod 2] SingularChain X n :=
  Finsupp.linearCombination (ZMod 2) (fun σ => pushChainM σ (linSubdiv n (idChain n)))

theorem singularSd_single (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    singularSd X n (Finsupp.single σ 1) = pushChainM σ (linSubdiv n (idChain n)) := by
  rw [singularSd, Finsupp.linearCombination_single, one_smul]

/-- The `i`-th facet of the identity `(n+1)`-simplex is the linear image of the identity `n`-simplex:
`∂ᵢ ι_{n+1} = (Lᵢ)_* ι_n`, with `Lᵢ = FunOnFinite.linearMap (Fin.succAbove i)` (it sends the basis
vertex `eⱼ` to `e_{δᵢj}`). -/
theorem facet_idChain (n : ℕ) (i : Fin (n + 2)) :
    Finsupp.single ((fun j => (Pi.single j 1 : Fin (n + 1 + 1) → ℝ)) ∘ i.succAbove) (1 : ZMod 2)
      = mapVerts (FunOnFinite.linearMap ℝ ℝ i.succAbove) n (idChain n) := by
  rw [idChain, mapVerts_single]
  congr 1
  funext j
  rw [Function.comp_apply, Function.comp_apply, FunOnFinite.linearMap_piSingle]

/-- **The singular subdivision is a chain map**: `∂ ∘ Sd = Sd ∘ ∂` on a basis simplex. Transports the
affine `∂Sd=Sd∂` (`linBoundary_linSubdiv`) through the pushforward chain map (`pushChainM_chainBoundary`)
and the facet functoriality (`pushChainM_mapVerts` + `mapVerts_linSubdiv` + `facet_idChain`). -/
theorem chainBoundary_singularSd (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    chainBoundary X n (singularSd X (n + 1) (Finsupp.single σ 1))
      = singularSd X n (chainBoundary X n (Finsupp.single σ 1)) := by
  rw [singularSd_single,
    pushChainM_chainBoundary σ
      (linSubdiv_mem_chainsIn (convex_stdSimplex ℝ _) (n + 1) (idChain_mem (n + 1))),
    linBoundary_linSubdiv, idChain, linBoundary_single, linBoundaryBasis, map_sum, map_sum,
    chainBoundary_single, boundaryBasis, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [singularSd_single, facet_idChain, ← mapVerts_linSubdiv,
    pushChainM_mapVerts σ i (linSubdiv_mem_chainsIn (convex_stdSimplex ℝ _) n (idChain_mem n))]

end SKEFTHawking.SingularSubdivision
