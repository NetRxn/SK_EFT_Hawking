/-
# Phase 5q.H (E1 integral topology) — integral cap-product locality: the cap preserves the support

Integral (`ZMod 2 → ℤ`) mirror of `SingularCapSupport`. The integral cap product `a ⌢ c` of any cochain
`a` with a chain `c` **supported in `S`** (a subspace chain) is again **supported in `S`**:
`c ∈ subspaceChainsInt S (k+m) ⟹ a ⌢ c ∈ subspaceChainsInt S m`. The geometric reason is that the
Alexander–Whitney back face of an `S`-simplex is an `S`-simplex (`backFace_simplexIncl`), so
`a ⌢ [σ] = a(frontₖσ)•[backₘσ]` lands on `S`-simplices (the same `capBasisInt` unfolding wt1's
`capInt_subspaceChainInt_eq_zero` uses).

This is the locality that lets the integral Poincaré-duality map land in `H_{n-k}(sub K; ℤ)` (the
homology of the compact `K` itself), not just `H_{n-k}(M; ℤ)`: with a fundamental cycle represented in
`C(K;ℤ)`, `a ⌢ z_K ∈ C(K;ℤ)`. The varying target `H_{n-k}(sub K;ℤ)` is what makes the duality fit the
Mayer–Vietoris 5-lemma ladder (the fixed `H_{n-k}(M;ℤ)` of `relativeDualityInt` does not). Consumed by
the integral local-duality map `D_K` (next brick, `SingularLocalDualityKInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularEuclideanCapIsoInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularEuclideanCapIsoInt (capInt_relCycle_isCycleInt)

namespace SKEFTHawking.SingularCapSupportInt

variable {X : TopCat} (S : Set X)

/-- **`backFace` commutes with the subspace inclusion** (integral cup faces) — naturality of
`simplexIncl` against the back-face inclusion `backIncl`. Integral analogue of
`SingularRelativeCap.backFace_simplexIncl`, for the `SingularCupInt.backFace` used by `capBasisInt`
(the back-face companion to wt1's `SingularEuclideanCapIsoInt.frontFace_simplexIncl`). -/
theorem backFace_simplexInclInt {p q : ℕ}
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk (p + q)))) :
    backFace (simplexIncl S (p + q) τ) = simplexIncl S q (backFace τ) := by
  simpa only [simplexIncl, backFace] using
    (NatTrans.naturality_apply (TopCat.toSSet.map (SingularRelativeHomologyMod2.inclMap S))
      (backIncl p q).op τ).symm

/-- **Integral cap-product locality**: `a ⌢ c` is supported in `S` whenever `c` is. On a basis
`S`-simplex `σ`, `a ⌢ [σ] = a(frontₖσ)•[backₘσ]` and the back face of an `S`-simplex is an `S`-simplex
(`backFace_simplexIncl`), so the result lies in `subspaceChainsInt S m`. Integral mirror of
`SingularCapSupport.cap_mem_subspaceChains`; the `single`-case rewrite chain is exactly the one wt1's
`capInt_subspaceChainInt_eq_zero` uses (with `backFace` in place of `frontFace`). -/
theorem capInt_mem_subspaceChainsInt {k m : ℕ} (a : SingularCochainInt X k)
    {c : SingularChainInt X (k + m)} (hc : c ∈ subspaceChainsInt S (k + m)) :
    capInt a c ∈ subspaceChainsInt S m := by
  rw [subspaceChainsInt, LinearMap.mem_range] at hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add d e hd he => rw [map_add, map_add]; exact Submodule.add_mem _ hd he
  | single τ s =>
      rw [chainIncl_single, capInt_single_smul, capBasisInt, backFace_simplexInclInt S τ]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        ⟨Finsupp.single (backFace τ) 1, chainIncl_single S m (backFace τ) 1⟩)

/-- **The integral relative cap of a `K`-supported fundamental cycle is a cycle supported in `K`.** For
a relative cocycle `a` (vanishing on `S = M∖K`, `δa = 0`) and an absolute chain `z` **supported in `K`**
whose boundary `∂z` is a subspace chain of `S` (the rel-cycle condition for the fundamental class of
`M|K`), the cap `a ⌢ z` is both an **absolute cycle** (`capInt_relCycle_isCycleInt`) and **supported in
`K`** (`capInt_mem_subspaceChainsInt`). This `cycles ⊓ subspaceChainsInt K` element is exactly a cycle of
`C(K;ℤ)`, giving the duality class in `H_{n-k}(sub K;ℤ)`. -/
theorem capInt_relCycle_mem_cyclesInt_inf_K {k m : ℕ} (a : SingularCochainInt X k)
    (ha : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      a (simplexIncl S k τ) = 0)
    (hδa : coboundaryₗ X k a = 0) {K : Set X} {z : SingularChainInt X (k + m + 1)}
    (hzK : z ∈ subspaceChainsInt K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m)) :
    capInt a z ∈ cycles X (m + 1) ⊓ subspaceChainsInt K (m + 1) :=
  Submodule.mem_inf.mpr
    ⟨capInt_relCycle_isCycleInt S a ha hδa hzS, capInt_mem_subspaceChainsInt K a hzK⟩

/-- **A `K`-supported absolute integral cycle is the image of a genuine cycle of `sub K`.** If `c` is an
absolute `(m+1)`-cycle supported in `K` (`c ∈ cycles X (m+1) ⊓ subspaceChainsInt K (m+1)`), then
`c = chainIncl K w` for a **cycle** `w ∈ cycles (sub K) (m+1)` of the subspace `K` itself —
`w = (chainIncl K)⁻¹ c` is a cycle because `chainIncl K` is an injective chain map
(`chainIncl_chainBoundary` + `chainIncl_injective`). This is the pullback that turns the `K`-supported
duality cycle into a class in `H_{n-k}(sub K;ℤ)`. -/
theorem exists_subK_cycleInt_of_mem_cyclesInt_inf {K : Set X} {m : ℕ}
    {c : SingularChainInt X (m + 1)}
    (hc : c ∈ cycles X (m + 1) ⊓ subspaceChainsInt K (m + 1)) :
    ∃ w : SingularChainInt (sub K) (m + 1),
      chainBoundary (sub K) m w = 0 ∧ chainIncl K (m + 1) w = c := by
  obtain ⟨hcyc, hsub⟩ := Submodule.mem_inf.mp hc
  rw [subspaceChainsInt, LinearMap.mem_range] at hsub
  obtain ⟨w, rfl⟩ := hsub
  have hcyc' : chainBoundary X m (chainIncl K (m + 1) w) = 0 := hcyc
  refine ⟨w, ?_, rfl⟩
  refine chainIncl_injective K m ?_
  rw [chainIncl_chainBoundary K m w, hcyc', map_zero]

end SKEFTHawking.SingularCapSupportInt
