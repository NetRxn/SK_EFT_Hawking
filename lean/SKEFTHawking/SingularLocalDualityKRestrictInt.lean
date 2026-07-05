/-
# Phase 5q.H (E1 integral topology) — cohomology-restriction compatibility of `D_K` (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularLocalDualityKRestrict`. The `H(sub K)`-valued duality
`relativeDualityKInt S K z` commutes with the relative-cohomology restriction `relCohomRestrictInt` on
the **cohomology subspace** `S`, for a *fixed* `K`-supported cycle `z`: capping the same `z` against a
relative cocycle is independent of how large the cohomology subspace is, because the resulting chain
`a ⌢ z` depends only on the underlying absolute cochain `a.1.1` (which `relCohomRestrictInt` preserves)
and on `z`. This is the `DirectLimit.lift` compatibility that makes the open duality
`D_W : Hᵏ_c(W;ℤ) → H_{n-k}(sub W;ℤ)` well-defined when the cycle is fixed.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularLocalDualityKInt
import SKEFTHawking.SingularRelativeCohomologyRestrictInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeCohomologyRestrictInt
open SKEFTHawking.SingularLocalDualityKInt

namespace SKEFTHawking.SingularLocalDualityKRestrictInt

variable {X : TopCat}

/-- **Cohomology-restriction compatibility of the integral `H(sub K)`-valued duality**: for `S ⊆ T` and
a fixed `K`-supported cycle `z`, `D_K^S ∘ relCohomRestrictInt = D_K^T`. Both classes are `[a ⌢ z]_{sub
K}` for the *same* underlying absolute cochain `a.1.1` (`relCohomRestrictInt` preserves it), so the
pulled-back `sub K`-cycles agree (`chainIncl` is injective and recovers `a ⌢ z`). -/
theorem relativeDualityKInt_restrict_compat {k m : ℕ} {K : Set ↑X}
    (z : SingularChainInt X (k + m + 1)) {S T : Set ↑X} (h : S ⊆ T)
    (hzK : z ∈ subspaceChainsInt K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (hzT : chainBoundary X (k + m) z ∈ subspaceChainsInt T (k + m))
    (x : RelativeCohomologyInt T k) :
    relativeDualityKInt S K k m z hzK hzS (relCohomRestrictInt h k x)
      = relativeDualityKInt T K k m z hzK hzT x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx : (Submodule.Quotient.mk a : RelativeCohomologyInt T k)
      = RelativeCohomologyInt.mk T k a := rfl
  rw [hx, relCohomRestrictInt_mk, relativeDualityKInt_mk, relativeDualityKInt_mk]
  apply congrArg (Homology.mk (sub K) (m + 1))
  apply Subtype.ext
  apply chainIncl_injective K (m + 1)
  rw [chainIncl_pullbackDualityIntₗ, chainIncl_pullbackDualityIntₗ]
  have hcoe : (↑↑(relCocycleRestrictInt h k a) : SingularCochainInt X k) = ↑↑a := by
    rw [relCocycleRestrictInt_coe, relCochainRestrictInt_coe]
  rw [hcoe]

end SKEFTHawking.SingularLocalDualityKRestrictInt
