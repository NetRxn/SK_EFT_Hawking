import Mathlib
import SKEFTHawking.SingularDualityEmpty

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-D∅inj) — `capH · [z]` injective from `relativeDuality ∅` injective

The `PoincareDual4Mid.nondeg` obligation (`nondeg_of_duality_injective`) is the injectivity of
`a ↦ capH k m a [z]` for the fundamental cycle `z`. Via the empty-subspace bridge
`SingularDualityEmpty.relativeDuality_empty_eq_capH` (`relativeDuality ∅ z ω = capH k m (eq ω) [z]`,
`eq = relCohomologyEmptyEquiv`), the cap map is `relativeDuality ∅ z` precomposed with the **bijection**
`eq.symm`, so injectivity of the duality map over `∅` transfers directly:
  `Injective (relativeDuality ∅ z) ⟹ Injective (a ↦ capH k m a [z])`.

This reduces the `nondeg` target to injectivity of the Poincaré-duality map at the colimit endpoint `K =
univ` (`M ∖ univ = ∅`), which the open-cover induction (`fundamentalDuality` iso) discharges. No
`(univ)ᶜ = ∅` cast is needed — the statement is purely over `∅`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeDuality SKEFTHawking.SingularRelativeCohomologyEmpty
  SKEFTHawking.SingularCapHomology SKEFTHawking.SingularDualityEmpty

namespace SKEFTHawking.SingularDualityEmptyInjective

variable {X : TopCat}

/-- **`capH · [z]` is injective when the duality map over `∅` is**: the cap-with-`[z]` map is
`relativeDuality ∅ z` precomposed with the bijection `relCohomologyEmptyEquiv.symm`
(`relativeDuality_empty_eq_capH`), so it inherits injectivity. The reduction of the `nondeg` target to the
Poincaré-duality endpoint injectivity. -/
theorem capH_injective_of_relativeDuality_empty_injective {k m : ℕ}
    (z : SingularChain X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChains (∅ : Set X) (k + m))
    (hD : Function.Injective ⇑(relativeDuality (∅ : Set X) k m z hz)) :
    Function.Injective (fun a : Cohomology X k =>
      capH k m a (Homology.mk X (k + m + 1) ⟨z, cycle_of_subspaceChains_empty z hz⟩)) := by
  have key : ∀ c : Cohomology X k,
      capH k m c (Homology.mk X (k + m + 1) ⟨z, cycle_of_subspaceChains_empty z hz⟩)
        = relativeDuality (∅ : Set X) k m z hz ((relCohomologyEmptyEquiv k).symm c) := by
    intro c
    rw [relativeDuality_empty_eq_capH, LinearEquiv.apply_symm_apply]
  intro a b hab
  simp only [key] at hab
  exact (relCohomologyEmptyEquiv k).symm.injective (hD hab)

end SKEFTHawking.SingularDualityEmptyInjective
