import Mathlib
import SKEFTHawking.IntCapProductInt
import SKEFTHawking.SingularRelHomologyInt
import SKEFTHawking.SingularRelativeCap
import SKEFTHawking.SingularLocalHomologyIsoInt

/-!
# Phase 5q.H (E1 integral topology) — the Euclidean local Poincaré-duality cap-iso (PD base case)

The **base case** of the Mayer–Vietoris five-lemma proof of integral Poincaré duality on an open
4-manifold (Hatcher 3.35): for the open Euclidean model `ℝ⁴` (a chart ball), the cap-duality map from
compactly-supported cohomology to homology is an **isomorphism**. Concretely the load-bearing case is
`H⁴_c(ℝ⁴; ℤ) ⌢ [ℝ⁴]_loc ≅ H₀(ℝ⁴; ℤ)`, both `≅ ℤ`.

This is the self-contained leaf consumed by the lead's MV five-lemma. It does **not** depend on the
general MV/CSC colimit — the `ℝ⁴` case is built standalone, computing the compactly-supported cohomology
directly (it is `ℤ` at `k = 4` and `0` else).

## Structure

* §A — the **integral relative cap chain-heart**: a cochain vanishing on the subspace `S` caps a
  subspace chain to `0` (`capInt_subspaceChainInt_eq_zero`), so `a ⌢ (relative cycle)` is an absolute
  cycle (`capInt_relCycle_isCycleInt`). Integral mirror of `SingularRelativeCap`, reusing the built
  `capInt` primitives.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)

namespace SKEFTHawking.SingularEuclideanCapIsoInt

variable {X : TopCat} (S : Set X)

/-! ## §A. The integral relative cap chain-heart -/

/-- **`frontFace` commutes with the subspace inclusion** (integral cup faces) — naturality of
`simplexIncl` against the front-face inclusion `frontIncl`. Integral analogue of
`SingularRelativeCap.frontFace_simplexIncl`, for the `SingularCupInt.frontFace` used by `capBasisInt`. -/
theorem frontFace_simplexIncl {p q : ℕ}
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk (p + q)))) :
    frontFace (simplexIncl S (p + q) τ) = simplexIncl S p (frontFace τ) := by
  simpa only [simplexIncl, frontFace] using
    (FunctorToTypes.naturality _ _ (TopCat.toSSet.map (SingularRelativeHomologyMod2.inclMap S))
      (frontIncl p q).op τ).symm

/-- **A cochain vanishing on `S` caps a subspace chain to `0`** (integral): if `a σ = 0` for every
`S`-simplex `σ` (i.e. `a` is a relative cochain), then `a ⌢ c = 0` for every `c ∈ subspaceChainsInt S`.
Integral mirror of `SingularRelativeCap.cap_subspaceChain_eq_zero`, reusing the topological
front-face naturality lemma (`ZMod 2`-independent). -/
theorem capInt_subspaceChainInt_eq_zero {k m : ℕ} (a : SingularCochainInt X k)
    (ha : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      a (simplexIncl S k τ) = 0)
    {c : SingularChainInt X (k + m)} (hc : c ∈ subspaceChainsInt S (k + m)) :
    capInt (m := m) a c = 0 := by
  rw [subspaceChainsInt, LinearMap.mem_range] at hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add d e hd he => rw [map_add, map_add, hd, he, add_zero]
  | single τ s =>
      rw [chainIncl_single, capInt_single_smul, capBasisInt,
        frontFace_simplexIncl S τ, ha (frontFace τ), zero_smul, smul_zero]

/-- **The integral relative cap lands cycles**: for a **relative cocycle** `a` (vanishing on `S`,
`δa = 0`) and a **relative cycle** `z` (its boundary `∂z` is a subspace chain), the cap `a ⌢ z` is an
**absolute** cycle. Integral mirror of `SingularRelativeCap.cap_relCycle_isCycle`; the chain-level heart
of the integral relative duality map `Hᵏ(M, S; ℤ) → Hₙ₋ₖ(M; ℤ)`. -/
theorem capInt_relCycle_isCycleInt {k m : ℕ} (a : SingularCochainInt X k)
    (ha : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      a (simplexIncl S k τ) = 0)
    (hδa : coboundaryₗ X k a = 0) {z : SingularChainInt X (k + m + 1)}
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m)) :
    chainBoundary X m (capInt (m := m + 1) a z) = 0 := by
  rw [capInt_cocycle_chainMap a hδa z]
  rw [capInt_subspaceChainInt_eq_zero S a ha hz, smul_zero]

end SKEFTHawking.SingularEuclideanCapIsoInt
