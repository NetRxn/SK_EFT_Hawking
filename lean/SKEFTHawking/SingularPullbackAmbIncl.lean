import Mathlib
import SKEFTHawking.SingularKroneckerFunctoriality
import SKEFTHawking.SingularCapChainIncl
import SKEFTHawking.SingularMayerVietorisLES

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-R1d) — the cochain-pullback flavor bridge

The two cochain-pullback flavors coincide along the subspace inclusion: the cap-side `pullbackCochain S`
(precompose with `simplexIncl`, the `toSSet.map` of the inclusion) equals the functoriality-side
`pullbackCochainMap (ambIncl S)` (precompose with `mapSimplex`, the `toSSetObjEquiv`-based pushforward),
because `mapSimplex (ambIncl S) = simplexIncl S` (`mapSimplex_ambIncl`). This reconciles the
`pullbackCochain`-form cochains the LHS-half reduction (R3a) consumes with the `pullbackCochainMap`-form
cochains the seam-dual transport (R1b) produces, in the connecting-square match assembly.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularFunctoriality
  SKEFTHawking.SingularKroneckerFunctoriality SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularMayerVietorisLES

namespace SKEFTHawking.SingularPullbackAmbIncl

variable {X : TopCat}

/-- **Flavor bridge**: `pullbackCochain S = pullbackCochainMap (ambIncl S)` — the cap-side and
functoriality-side cochain pullbacks agree along the subspace inclusion `sub S ↪ X`. -/
theorem pullbackCochain_eq_pullbackCochainMap_ambIncl (S : Set ↑X) (k : ℕ) (a : SingularCochain X k) :
    pullbackCochain S k a = pullbackCochainMap (ambIncl S) k a := by
  funext τ
  rw [pullbackCochain_apply, pullbackCochainMap_apply, mapSimplex_ambIncl]

end SKEFTHawking.SingularPullbackAmbIncl
