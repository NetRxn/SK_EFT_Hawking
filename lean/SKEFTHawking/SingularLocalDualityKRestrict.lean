import Mathlib
import SKEFTHawking.SingularLocalDualityK
import SKEFTHawking.SingularRelativeCohomologyRestrict

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6e-i) — cohomology-restriction compatibility of `D_K`

The `H(sub K)`-valued duality `relativeDualityK (S) (K) (z)` commutes with the relative-cohomology
restriction `relCohomRestrict` on the **cohomology subspace** `S`, for a *fixed* `K`-supported cycle
`z`: capping the same `z` against a relative cocycle is independent of how large the cohomology
subspace is, because the resulting chain `a ⌢ z` depends only on the underlying absolute cochain
`a.1.1` (which `relCohomRestrict` preserves) and on `z`. This is the varying-target analogue of
`SingularFundamentalDuality.relativeDuality_restrict_compat`, and the `DirectLimit.lift` compatibility
that makes the open duality `D_W : Hᵏ_c(W) → H_{n-k}(sub W)` well-defined when the cycle is fixed.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyRestrict
  SKEFTHawking.SingularLocalDualityK

namespace SKEFTHawking.SingularLocalDualityKRestrict

variable {X : TopCat}

/-- **Cohomology-restriction compatibility of the `H(sub K)`-valued duality**: for `S ⊆ T` and a fixed
`K`-supported cycle `z`, `D_K^S ∘ relCohomRestrict = D_K^T`. Both classes are `[a ⌢ z]_{sub K}` for the
*same* underlying absolute cochain `a.1.1` (`relCohomRestrict` preserves it), so the pulled-back
`sub K`-cycles agree (`chainIncl` is injective and recovers `a ⌢ z`). -/
theorem relativeDualityK_restrict_compat {k m : ℕ} {K : Set ↑X}
    (z : SingularChain X (k + m + 1)) {S T : Set ↑X} (h : S ⊆ T)
    (hzK : z ∈ subspaceChains K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (hzT : chainBoundary X (k + m) z ∈ subspaceChains T (k + m))
    (x : RelativeCohomology T k) :
    relativeDualityK S K k m z hzK hzS (relCohomRestrict h k x)
      = relativeDualityK T K k m z hzK hzT x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx : (Submodule.Quotient.mk a : RelativeCohomology T k) = RelativeCohomology.mk T k a := rfl
  rw [hx, relCohomRestrict_mk, relativeDualityK_mk, relativeDualityK_mk]
  apply congrArg (Homology.mk (sub K) (m + 1))
  apply Subtype.ext
  apply chainIncl_injective K (m + 1)
  rw [chainIncl_pullbackDualityₗ, chainIncl_pullbackDualityₗ]
  have hcoe : (↑↑(relCocycleRestrict h k a) : SingularCochain X k) = ↑↑a := by
    rw [relCocycleRestrict_coe, relCochainRestrict_coe]
  rw [hcoe]

end SKEFTHawking.SingularLocalDualityKRestrict
