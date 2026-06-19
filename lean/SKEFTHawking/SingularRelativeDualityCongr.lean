import Mathlib
import SKEFTHawking.SingularRelativeDuality
import SKEFTHawking.SingularCompactlySupportedTop

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-Dcongr) — set-congruence of the relative duality map

The relative Poincaré-duality map `relativeDuality S z` transports along a **set equality** `S = T`:
  `relativeDuality S z hzS = (relativeDuality T z hzT) ∘ relCohomSetCongr (S = T)`.
A `subst` of the underlying set. This is the bridge from the Poincaré-duality colimit endpoint
`relativeDuality (univ)ᶜ z` (the value of `fundamentalDuality` at `K = ⊤`) to `relativeDuality ∅ z`
(which `SingularDualityEmptyInjective` identifies with `capH · [z]`), since `(univ)ᶜ = ∅`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeDuality
  SKEFTHawking.SingularCompactlySupportedTop

namespace SKEFTHawking.SingularRelativeDualityCongr

variable {X : TopCat}

/-- **Set-congruence of `relativeDuality`**: for `S = T`, the duality map over `S` is the duality map
over `T` precomposed with the relative-cohomology set-congruence `relCohomSetCongr`. A `subst` of the
set. -/
theorem relativeDuality_set_congr {S T : Set ↑X} (hST : S = T) (k m : ℕ)
    (z : SingularChain X (k + m + 1)) (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (ω : RelativeCohomology S k) :
    relativeDuality S k m z hzS ω
      = relativeDuality T k m z (hST ▸ hzS) (relCohomSetCongr hST k ω) := by
  subst hST
  rfl

/-- **Injectivity transfers along a set equality**: if `relativeDuality T z` is injective and `S = T`,
then `relativeDuality S z` is injective (`relCohomSetCongr` is a bijection). The form used to pass the
endpoint injectivity `relativeDuality (univ)ᶜ z` (from `fundamentalDuality` iso) to `relativeDuality ∅ z`
(the `nondeg` reduction). -/
theorem relativeDuality_injective_of_set_eq {S T : Set ↑X} (hST : S = T) {k m : ℕ}
    (z : SingularChain X (k + m + 1)) (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (hD : Function.Injective ⇑(relativeDuality T k m z (hST ▸ hzS))) :
    Function.Injective ⇑(relativeDuality S k m z hzS) := by
  intro a b hab
  rw [relativeDuality_set_congr hST, relativeDuality_set_congr hST] at hab
  exact (relCohomSetCongr hST k).injective (hD hab)

end SKEFTHawking.SingularRelativeDualityCongr
