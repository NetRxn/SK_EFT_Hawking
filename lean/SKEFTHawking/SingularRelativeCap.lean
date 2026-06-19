import Mathlib
import SKEFTHawking.SingularHomologyMod2
import SKEFTHawking.SingularRelativeHomologyMod2

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD2) — the relative cap product (chain heart)

Toward Poincaré duality: the cap product `a ⌢ ·` of a cochain `a` that **vanishes on the subspace `S`**
(a relative cochain) kills the subspace chains, so `a ⌢ z` is an **absolute cycle** when `z` is a
relative cycle. The geometric content is that the Alexander–Whitney front/back faces commute with the
subspace inclusion (`frontFace_simplexIncl`/`backFace_simplexIncl`, naturality of `simplexIncl`), so a
cochain vanishing on `S`-simplices evaluates to `0` on the front face of any `S`-simplex.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2

namespace SKEFTHawking.SingularRelativeCap

variable {X : TopCat} (S : Set X)

/-- **`frontFace` commutes with the subspace inclusion** — naturality of `simplexIncl` against the
front-face inclusion `frontIncl`. -/
theorem frontFace_simplexIncl {p q : ℕ}
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk (p + q)))) :
    frontFace (simplexIncl S (p + q) τ) = simplexIncl S p (frontFace τ) := by
  simpa only [simplexIncl, frontFace] using
    (FunctorToTypes.naturality _ _ (TopCat.toSSet.map (inclMap S)) (frontIncl p q).op τ).symm

/-- **`backFace` commutes with the subspace inclusion** — naturality of `simplexIncl` against the
back-face inclusion `backIncl`. -/
theorem backFace_simplexIncl {p q : ℕ}
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk (p + q)))) :
    backFace (simplexIncl S (p + q) τ) = simplexIncl S q (backFace τ) := by
  simpa only [simplexIncl, backFace] using
    (FunctorToTypes.naturality _ _ (TopCat.toSSet.map (inclMap S)) (backIncl p q).op τ).symm

/-- **A cochain vanishing on `S` caps a subspace chain to `0`**: if `a σ = 0` for every `S`-simplex `σ`
(i.e. `a` is a relative cochain), then `a ⌢ c = 0` for every `c ∈ subspaceChains S`. On a basis
`S`-simplex `τ`, `a ⌢ [σ] = a(frontₖ σ)·[backₘ σ]` and `frontₖ (simplexIncl τ) = simplexIncl (frontₖ τ)`
is again an `S`-simplex, so `a` kills it. The vanishing that makes `a ⌢ (relative cycle)` an absolute
cycle. -/
theorem cap_subspaceChain_eq_zero {k m : ℕ} (a : SingularCochain X k)
    (ha : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      a (simplexIncl S k τ) = 0)
    {c : SingularChain X (k + m)} (hc : c ∈ subspaceChains S (k + m)) :
    cap a c = 0 := by
  rw [subspaceChains, LinearMap.mem_range] at hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add d e hd he => rw [map_add, map_add, hd, he, add_zero]
  | single τ s =>
      rw [chainIncl_single, cap_single_smul, capBasis, frontFace_simplexIncl S τ,
        ha (frontFace τ), zero_smul, smul_zero]

/-- **The relative cap lands cycles** (the relative-cap-product cycle property): for a **relative
cocycle** `a` (vanishing on `S`, `δa = 0`) and a **relative cycle** `z` (its boundary `∂z` is a subspace
chain), the cap `a ⌢ z` is an **absolute** cycle. By `cap_cocycle_chainMap` (cocycle ⟹ `cap a` commutes
with `∂`), `∂(a ⌢ z) = a ⌢ (∂z)`, and `a ⌢ (∂z) = 0` since `a` kills subspace chains
(`cap_subspaceChain_eq_zero`). The chain-level heart of the duality map `Hᵏ(M, S) → Hₙ₋ₖ(M)`. -/
theorem cap_relCycle_isCycle {k m : ℕ} (a : SingularCochain X k)
    (ha : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      a (simplexIncl S k τ) = 0)
    (hδa : coboundaryₗ X k a = 0) {z : SingularChain X (k + m + 1)}
    (hz : chainBoundary X (k + m) z ∈ subspaceChains S (k + m)) :
    chainBoundary X m (cap a z) = 0 := by
  rw [cap_cocycle_chainMap a hδa z]
  exact cap_subspaceChain_eq_zero S a ha hz

end SKEFTHawking.SingularRelativeCap
