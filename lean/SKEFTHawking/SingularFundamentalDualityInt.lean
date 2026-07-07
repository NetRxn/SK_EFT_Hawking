/-
# Phase 5q.H (E1 CSC-PD tower) — the integral fixed-target duality `D_M : Hᵏ_c(M;ℤ) → H_{m+1}(M;ℤ)`

Integral (`ZMod 2 → ℤ`) mirror of `SingularFundamentalDuality.fundamentalDuality`: the compactly-supported
Poincaré-duality map, the colimit of the fixed-target relative dualities `relativeDualityInt (Kᶜ)` over the
compacts of `M`. This is the map the σ÷16 bridge identifies with the cap-with-`[M]` (`capHInt 2 1 · zM`);
`pdWindowPInt_univ`'s bijectivity of `openDuality univ` will transfer to it via the `⊤`-collapse.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularCohomologyColimitInt
import SKEFTHawking.SingularRelativeCohomologyRestrictInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCohomologyColimitInt
open SKEFTHawking.SingularRelativeCohomologyRestrictInt

namespace SKEFTHawking.SingularFundamentalDualityInt

variable {X : TopCat}

/-- **Compatibility of the fixed-target integral duality with restriction**: capping the same global cycle
`z` commutes with `relCohomRestrictInt` — both sides are `[a ⌢ z]` for the same underlying absolute cochain
`a`. The `DirectLimit.lift` compatibility making `D_M` well-defined. Mirror of
`SingularFundamentalDuality.relativeDuality_restrict_compat`. -/
theorem relativeDualityInt_restrict_compat {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    {S T : Set ↑X} (h : S ⊆ T)
    (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (hzT : chainBoundary X (k + m) z ∈ subspaceChainsInt T (k + m))
    (x : RelativeCohomologyInt T k) :
    relativeDualityInt (S := S) k m z hzS (relCohomRestrictInt h k x)
      = relativeDualityInt (S := T) k m z hzT x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx : (Submodule.Quotient.mk a : RelativeCohomologyInt T k) = RelativeCohomologyInt.mk T k a := rfl
  rw [hx, relCohomRestrictInt_mk, relativeDualityInt_mk, relativeDualityInt_mk,
    relDualityIntₗ_apply, relDualityIntₗ_apply]
  refine congrArg (Homology.mk X (m + 1)) (Subtype.ext ?_)
  rw [capRelCocycleIntₗ_coe, capRelCocycleIntₗ_coe, relCocycleRestrictInt_coe,
    relCochainRestrictInt_coe]

/-- **The integral compactly-supported duality map** `D_M : Hᵏ_c(M;ℤ) → H_{m+1}(M;ℤ)`, the colimit of the
fixed-target `relativeDualityInt (Kᶜ) z` over the compacts, for an absolute fundamental cycle `z`
(`∂z = 0`). Integral mirror of `SingularFundamentalDuality.fundamentalDuality`. -/
noncomputable def fundamentalDualityInt {M : TopCat} (k m : ℕ)
    (z : SingularChainInt M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0) :
    CompactlySupportedCohomologyInt (M := M) k →ₗ[ℤ] Homology M (m + 1) :=
  Module.DirectLimit.lift ℤ (TopologicalSpace.Compacts ↑M) (cohomGInt k) (cohomFInt k)
    (fun K => relativeDualityInt (S := (↑K : Set ↑M)ᶜ) k m z (by rw [hz]; exact Submodule.zero_mem _))
    (fun K K' h x => relativeDualityInt_restrict_compat z
      (Set.compl_subset_compl.mpr h) (by rw [hz]; exact Submodule.zero_mem _)
      (by rw [hz]; exact Submodule.zero_mem _) x)

end SKEFTHawking.SingularFundamentalDualityInt
