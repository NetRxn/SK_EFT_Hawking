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

end SKEFTHawking.SingularSubdivision
