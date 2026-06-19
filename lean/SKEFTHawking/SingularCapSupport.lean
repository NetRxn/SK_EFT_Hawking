import Mathlib
import SKEFTHawking.SingularRelativeCap

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-capK) — cap-product locality: the cap preserves the support

The cap product `a ⌢ c` of any cochain `a` with a chain `c` **supported in `S`** (a subspace chain) is
again **supported in `S`**: `c ∈ subspaceChains S (k+m) ⟹ a ⌢ c ∈ subspaceChains S m`. The geometric
reason is that the Alexander–Whitney back face of an `S`-simplex is an `S`-simplex
(`backFace_simplexIncl`), so `a ⌢ [σ] = a(frontₖσ)•[backₘσ]` lands on `S`-simplices.

This is the locality that lets the Poincaré-duality map land in `H_{n-k}(K)` (the homology of the compact
`K` itself), not just `H_{n-k}(M)`: with a fundamental cycle represented in `C(K)`, `a ⌢ z_K ∈ C(K)`. The
varying target `H_{n-k}(K)` is what makes the duality fit the Mayer–Vietoris 5-lemma ladder (the fixed
`H_{n-k}(M)` of `SingularRelativeDuality` does not — see the 2026-06-19 framework note).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCap

namespace SKEFTHawking.SingularCapSupport

variable {X : TopCat} (S : Set X)

/-- **Cap-product locality**: `a ⌢ c` is supported in `S` whenever `c` is. On a basis `S`-simplex `σ`,
`a ⌢ [σ] = a(frontₖσ)•[backₘσ]` and the back face of an `S`-simplex is an `S`-simplex
(`backFace_simplexIncl`), so the result lies in `subspaceChains S m`. -/
theorem cap_mem_subspaceChains {k m : ℕ} (a : SingularCochain X k)
    {c : SingularChain X (k + m)} (hc : c ∈ subspaceChains S (k + m)) :
    cap a c ∈ subspaceChains S m := by
  rw [subspaceChains, LinearMap.mem_range] at hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add d e hd he => rw [map_add, map_add]; exact Submodule.add_mem _ hd he
  | single τ s =>
      rw [chainIncl_single, cap_single_smul, capBasis, backFace_simplexIncl S τ]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        ⟨Finsupp.single (backFace τ) 1, chainIncl_single S m (backFace τ) 1⟩)

end SKEFTHawking.SingularCapSupport
