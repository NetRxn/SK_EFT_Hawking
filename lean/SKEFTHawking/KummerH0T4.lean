/-
# Phase 5q.H — `H₀(T⁴;ℤ) ≅ ℤ`: the one non-Künneth `TorusFour` homology group (integral)

The single degree-0 `TorusFour` homology group, orthogonal to the 4-fold-Künneth `H₂` arc
(`KummerHomologyT4`). `TorusFour = Circle × Circle × Circle × Circle` is path-connected (a product of
four path-connected circles), so the integral augmentation `ε̄ : H₀(T⁴;ℤ) → ℤ` is a `ℤ`-linear
isomorphism: it is surjective on any nonempty space (a single `0`-simplex maps to `1`) and injective on
a path-connected space (reduced `H̃₀(T⁴;ℤ) = 0`).

* §0 — the **path-connectedness inputs**. Pinned Mathlib (v4.29.1) has neither `PathConnectedSpace
  Circle` nor `PathConnectedSpace (X × Y)` (a later Mathlib provides both), so we build them:
  `pathConnectedSpace_circle` (the continuous surjective image of `ℝ` under `Circle.exp`, `z = exp
  (arg z)`), `joinedProdMk` / `pathConnectedSpace_prod` (paths in each coordinate, glued by
  `Path.trans`), and `torusFour_pathConnected` (three products of four circles).
* §1 — the **general integral base case** `homologyZeroPathConnectedEquivInt`: `H₀(X;ℤ) ≅ ℤ` for any
  path-connected `X`, the ℤ mirror of the mod-2 `SingularH0PathConnected.homologyZeroPathConnectedEquiv`,
  assembled from the two banked halves — injectivity
  (`SingularH0PathConnectedInt.augHInt_injective_pathConnected`, reduced `H̃₀ = 0`) and surjectivity
  (`SingularLineMinusPointInt.augHInt_surjective`, one `0`-simplex hits `1`).
* §2 — its instantiation at the *actual* `TopCat.of TorusFour` (`torusFourH0EquivInt`). The iso IS the
  augmentation, so the codomain-`ℤ` identification is genuine (`T⁴` has one path component), not a
  defined-to-be-`ℤ` shell.

**Honest boundary.** This is the degree-0 group only. The degree-2 group `H₂(T⁴;ℤ) ≅ ℤ⁶` and the
cup-form Gram `II(T⁴) ≅ 3H` need the 4-fold Künneth / Eilenberg–Zilber cross product (a separate
multi-file arc; see `KummerHomologyT4` §§K1-a/K1-b), and are NOT in scope here.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularH0PathConnectedInt
import SKEFTHawking.SingularLineMinusPointInt
import SKEFTHawking.KummerK3Base

namespace SKEFTHawking.KummerH0T4

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularLineMinusPointInt (augHInt augHInt_surjective)
open SKEFTHawking.SingularH0PathConnectedInt (augHInt_injective_pathConnected)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)
open SKEFTHawking.KummerK3Base (TorusFour)

/-! ## §0. Path-connectedness of `TorusFour = Circle⁴` -/

/-- **`Circle` is path-connected.** The unit circle in `ℂ` is the continuous surjective image of the
path-connected `ℝ` under `Circle.exp : C(ℝ, Circle)` — every `z : Circle` is `Circle.exp (arg z)`
(`Circle.exp_arg`). Pinned Mathlib (v4.29.1) has no direct `PathConnectedSpace Circle` instance (a later
Mathlib provides one), so this supplies it for `TorusFour = Circle⁴`. -/
theorem pathConnectedSpace_circle : PathConnectedSpace Circle :=
  Function.Surjective.pathConnectedSpace (f := (Circle.exp : ℝ → Circle))
    (fun z => ⟨Complex.arg (z : ℂ), Circle.exp_arg z⟩) Circle.exp.continuous

/-- **Product of two `Joined` witnesses.** A path `(a,b) ⤳ (c,d)` in `X × Y`: move the first
coordinate `a ⤳ c` (holding `b`), then the second `b ⤳ d` (holding `c`), glued by `Path.trans`. -/
theorem joinedProdMk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {a c : X} {b d : Y}
    (h₁ : Joined a c) (h₂ : Joined b d) : Joined (X := X × Y) (a, b) (c, d) :=
  ⟨(h₁.somePath.map (f := fun x : X => (x, b)) (by fun_prop)).trans
    (h₂.somePath.map (f := fun y : Y => (c, y)) (by fun_prop))⟩

/-- **The product of two path-connected spaces is path-connected.** The ℤ-homology base case needs
`TorusFour = Circle⁴` path-connected; pinned Mathlib (v4.29.1) has no `PathConnectedSpace (X × Y)`
instance (a later Mathlib provides one), so this supplies it via `joinedProdMk`. -/
theorem pathConnectedSpace_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] : PathConnectedSpace (X × Y) where
  nonempty := Nonempty.map2 Prod.mk PathConnectedSpace.nonempty PathConnectedSpace.nonempty
  joined p q := joinedProdMk (PathConnectedSpace.joined p.1 q.1) (PathConnectedSpace.joined p.2 q.2)

/-- **`TorusFour = Circle × Circle × Circle × Circle` is path-connected** — three products of the four
path-connected circles (`pathConnectedSpace_circle`, `pathConnectedSpace_prod`). -/
theorem torusFour_pathConnected : PathConnectedSpace TorusFour :=
  haveI : PathConnectedSpace Circle := pathConnectedSpace_circle
  haveI : PathConnectedSpace (Circle × Circle) := pathConnectedSpace_prod
  haveI : PathConnectedSpace (Circle × Circle × Circle) := pathConnectedSpace_prod
  pathConnectedSpace_prod

/-! ## §1. The general integral degree-0 base case `H₀(pathConnected;ℤ) ≅ ℤ` -/

/-- **`H₀(X;ℤ) ≅ ℤ` for a path-connected space** — the integral mirror of the mod-2
`SingularH0PathConnected.homologyZeroPathConnectedEquiv`. The augmentation `ε̄ : H₀(X;ℤ) → ℤ` is
surjective on any nonempty space (a single `0`-simplex maps to `1`, `augHInt_surjective`) and injective
on a path-connected space (reduced `H̃₀(X;ℤ) = 0`, `augHInt_injective_pathConnected`), hence a
`ℤ`-linear isomorphism. The degree-`0` integral base case. -/
noncomputable def homologyZeroPathConnectedEquivInt (X : TopCat) [PathConnectedSpace ↑X] :
    Homology X 0 ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective (augHInt X)
    ⟨augHInt_injective_pathConnected, augHInt_surjective X (constSimplex (Classical.arbitrary ↑X) 0)⟩

/-! ## §2. Instantiation at the actual `TorusFour = Circle⁴` -/

/-- **`H₀(T⁴;ℤ) ≅ ℤ`** — the one non-Künneth `TorusFour` homology group, for the *actual*
`TorusFour = Circle × Circle × Circle × Circle`. `T⁴` is path-connected (`torusFour_pathConnected`);
the iso is the augmentation `ε̄`, so the codomain-`ℤ` identification is genuine (`T⁴` has one path
component), not a defined-to-be-`ℤ` shell. Orthogonal to the deferred 4-fold-Künneth `H₂(T⁴)`
headline. -/
noncomputable def torusFourH0EquivInt : Homology (TopCat.of TorusFour) 0 ≃ₗ[ℤ] ℤ :=
  haveI : PathConnectedSpace ↑(TopCat.of TorusFour) := torusFour_pathConnected
  homologyZeroPathConnectedEquivInt (TopCat.of TorusFour)

end SKEFTHawking.KummerH0T4
