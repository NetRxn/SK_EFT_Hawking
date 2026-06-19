import Mathlib
import SKEFTHawking.SingularFundamentalDuality
import SKEFTHawking.SingularDirectLimitTop
import SKEFTHawking.SingularRelativeDualityCongr
import SKEFTHawking.SingularDualityEmptyInjective

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-DMend) — `nondeg ⟸ D_M injective`

The full reduction of the `PoincareDual4Mid.nondeg` obligation to injectivity of the compactly-supported
duality map `D_M` (`fundamentalDuality`). Chaining:

* `D_M (of ⊤ x) = relativeDuality (univ)ᶜ z x` (`Module.DirectLimit.lift_of`), and `of ⊤` is injective
  (`of_top_bijective`), so `D_M` injective ⟹ `relativeDuality (univ)ᶜ z` injective;
* `(univ)ᶜ = ∅`, so `relativeDuality (univ)ᶜ z` injective ⟹ `relativeDuality ∅ z` injective
  (`relativeDuality_injective_of_set_eq`);
* `relativeDuality ∅ z` injective ⟹ `capH · [z]` injective
  (`capH_injective_of_relativeDuality_empty_injective`).

So once the open-cover induction proves `D_M` an isomorphism (hence injective), `PoincareDual4Mid.nondeg`
follows for the fundamental cycle `z = [M]`. This isolates the **only** remaining L2 obligation to the
Poincaré-duality isomorphism `fundamentalDuality` (the 5-lemma induction).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeDuality SKEFTHawking.SingularCohomologyColimit
  SKEFTHawking.SingularDirectLimitTop SKEFTHawking.SingularRelativeDualityCongr
  SKEFTHawking.SingularDualityEmptyInjective SKEFTHawking.SingularFundamentalDuality
  SKEFTHawking.SingularCapHomology SKEFTHawking.SingularDualityEmpty

namespace SKEFTHawking.SingularFundamentalDualityEndpoint

variable {M : TopCat} [CompactSpace ↑M]

/-- **`relativeDuality (univ)ᶜ z` is injective when `D_M` is**: `D_M (of ⊤ x) = relativeDuality (univ)ᶜ z x`
(`Module.DirectLimit.lift_of`) and `of ⊤` is injective (`of_top_bijective`). -/
theorem relativeDuality_complTop_injective {k m : ℕ} (z : SingularChain M (k + m + 1))
    (hz : chainBoundary M (k + m) z = 0)
    (hD : Function.Injective ⇑(fundamentalDuality k m z hz)) :
    Function.Injective ⇑(relativeDuality ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) k m z
      (by rw [hz]; exact Submodule.zero_mem _)) := by
  have hfac : ∀ x, relativeDuality ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) k m z
        (by rw [hz]; exact Submodule.zero_mem _) x
      = fundamentalDuality k m z hz
          (Module.DirectLimit.of (ZMod 2) (TopologicalSpace.Compacts ↑M) (cohomG k) (cohomF k) ⊤ x) := by
    intro x
    exact (Module.DirectLimit.lift_of
      (fun K : TopologicalSpace.Compacts ↑M =>
        relativeDuality ((↑K : Set ↑M)ᶜ) k m z (by rw [hz]; exact Submodule.zero_mem _)) _ x).symm
  intro a b hab
  rw [hfac, hfac] at hab
  exact (of_top_bijective (cohomG k) (cohomF k)).injective (hD hab)

/-- **The full `nondeg` reduction**: `capH · [z]` is injective whenever the compactly-supported duality
map `fundamentalDuality` (`D_M`) is injective. Chains the colimit endpoint
(`relativeDuality_complTop_injective`), the `(univ)ᶜ = ∅` set-congruence
(`relativeDuality_injective_of_set_eq`), and the empty-subspace bridge
(`capH_injective_of_relativeDuality_empty_injective`). The remaining L2 obligation is exactly the
Poincaré-duality isomorphism (the 5-lemma induction proving `fundamentalDuality` injective). -/
theorem capH_injective_of_fundamentalDuality_injective {k m : ℕ} (z : SingularChain M (k + m + 1))
    (hz : chainBoundary M (k + m) z = 0)
    (hD : Function.Injective ⇑(fundamentalDuality k m z hz)) :
    Function.Injective (fun a : Cohomology M k =>
      capH k m a (Homology.mk M (k + m + 1)
        ⟨z, cycle_of_subspaceChains_empty z (by rw [hz]; exact Submodule.zero_mem _)⟩)) := by
  apply capH_injective_of_relativeDuality_empty_injective z (by rw [hz]; exact Submodule.zero_mem _)
  apply relativeDuality_injective_of_set_eq
    (show (∅ : Set ↑M) = ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) by
      rw [TopologicalSpace.Compacts.coe_top, Set.compl_univ]) z
  exact relativeDuality_complTop_injective z hz hD

end SKEFTHawking.SingularFundamentalDualityEndpoint
