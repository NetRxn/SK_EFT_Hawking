/-
# Phase 5q.H — `H₀(T⁴;ℤ) ≅ ℤ`: the one non-Künneth `TorusFour` homology group (integral)

The single degree-0 `TorusFour` homology group, orthogonal to the 4-fold-Künneth `H₂` arc
(`KummerHomologyT4`). `TorusFour = Circle × Circle × Circle × Circle` is path-connected (a product of
four path-connected circles), so the integral augmentation `ε̄ : H₀(T⁴;ℤ) → ℤ` is a `ℤ`-linear
isomorphism: it is surjective on any nonempty space (a single `0`-simplex maps to `1`) and injective on
a path-connected space (reduced `H̃₀(T⁴;ℤ) = 0`).

* §0 — the **path-connectedness inputs**, now **retired to upstream** (2026-07-29, Mathlib v4.32.0).
  The v4.29.1 pin supplied neither `PathConnectedSpace Circle` nor `PathConnectedSpace (X × Y)`, so
  this file built both; v4.32.0 ships the `Circle` instance and synthesises the product, and
  `torusFour_pathConnected` now follows by `inferInstance`. `pathConnectedSpace_circle` /
  `pathConnectedSpace_prod` / `torusFour_pathConnected` survive as named forwarders (21 downstream
  `haveI := …` sites unchanged); `joinedProdMk` is deleted.
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

/-! **Retired to upstream 2026-07-29 (Mathlib v4.32.0 bump).** These three were hand-built because
the v4.29.1 pin supplied neither instance — the original docstrings said "a later Mathlib provides
one", and it now does: `Analysis/SpecialFunctions/Complex/Circle.lean` gained
`instance : PathConnectedSpace Circle` (0 occurrences at `5e932f97`, 1 at `81a5d257`), and the
product instance is reachable by synthesis. The *statements* are kept as named forwarders so the
21 downstream `haveI := …` sites need no churn; only the proofs are retired. `joinedProdMk` had no
consumers outside this file and is deleted outright. -/

/-- **`Circle` is path-connected.** Now supplied by Mathlib (`PathConnectedSpace Circle`); retained
as a named forwarder for existing consumers. -/
theorem pathConnectedSpace_circle : PathConnectedSpace Circle := inferInstance

/-- **The product of two path-connected spaces is path-connected.** Now reachable by typeclass
synthesis at the v4.32.0 pin; retained as a named forwarder for existing consumers. -/
theorem pathConnectedSpace_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] : PathConnectedSpace (X × Y) := inferInstance

/-- **`TorusFour = Circle × Circle × Circle × Circle` is path-connected** — now synthesised outright
from the Mathlib `Circle` instance and the product instance. -/
theorem torusFour_pathConnected : PathConnectedSpace TorusFour := inferInstance

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
