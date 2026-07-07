/-
# Phase 5q.H (E1 CSC-PD tower) — relative cohomology vanishing from relative homology vanishing (ℤ)

The torsion-safe integral replacement for the mod-2 field bridge
`SingularRelativeUC.relCohomology_eq_zero_of_relHomology_eq_zero`. Over ℤ the relative UCT

  `0 → Ext(Hₙ₋₁;ℤ) → Hⁿ(X,S;ℤ) --κ--> Hom(Hₙ;ℤ) → 0`

has a genuine `Ext` term, so cohomology vanishing needs BOTH `Hₙ = 0` (kills `Hom(Hₙ)`) AND `Hₙ₋₁` FREE
(kills `Ext(Hₙ₋₁)`). Here `Hₙ₋₁ = 0` (⟹ free), giving `Hⁿ = 0` via the free-case injectivity
`relKroneckerHInt_injective_of_free`. This is the crux the base-case B3 CSC-vanishing consumes at every
convex cover-piece (where the convex-compact complement has both middle homology degrees vanishing).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeUCInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt

namespace SKEFTHawking.SingularRelativeUCVanishInt

variable {X : TopCat}

/-- **Relative cohomology vanishes from two-degree relative homology vanishing** (ℤ, torsion-safe): if
`Hₙ(X,S;ℤ) = 0` AND `Hₙ₋₁(X,S;ℤ) = 0` (the latter ⟹ free, killing the `Ext` obstruction), then
`Hⁿ(X,S;ℤ) = 0`. Via `relKroneckerHInt_injective_of_free`. -/
theorem relCohomology_eq_zero_of_relHomology_two_vanishInt {M : ℕ} (S : Set ↑X)
    [Module.Projective ℤ (relBoundariesInt S M)]
    (hH1 : ∀ β : RelHomologyInt S (M + 1), β = 0)
    (hH2 : ∀ β : RelHomologyInt S (M + 2), β = 0)
    (ω : RelativeCohomologyInt S (M + 2)) : ω = 0 := by
  haveI : Subsingleton (RelHomologyInt S (M + 1)) := ⟨fun a b => (hH1 a).trans (hH1 b).symm⟩
  haveI : Module.Free ℤ (RelHomologyInt S (M + 1)) := Module.Free.of_subsingleton ℤ _
  exact SingularRelativeUCInt.relKroneckerHInt_injective_of_free S ω
    (fun β => by rw [hH2 β, map_zero])

end SKEFTHawking.SingularRelativeUCVanishInt
