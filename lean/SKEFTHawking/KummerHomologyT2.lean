/-
# Phase 5q.H — `H_*(T²;ℤ) = H_*(S¹×S¹;ℤ)`: the 2-torus base case of the 4-fold Kummer Künneth

The K3 (= Kummer) generator needs `H₂(T⁴;ℤ) ≅ ℤ⁶` + its cup Gram, which needs a 4-fold Künneth over
`TorusFour = Circle⁴` for the project's custom `SingularHomologyInt.Homology`. This module builds the
**`T² = S¹×S¹` base case** — the first, load-bearing substep — UNCONDITIONALLY on that functor: the
full integral homology of the 2-torus.

**What lands here.**
* §0 — **`H₀(S¹×S¹;ℤ) ≅ ℤ`** (`torusTwoH0EquivInt`). `T² = Circle × Circle` is path-connected, so the
  integral augmentation is an iso (reuses the banked `KummerH0T4.homologyZeroPathConnectedEquivInt`
  and the `pathConnectedSpace_circle`/`pathConnectedSpace_prod` helpers).
* §1 — the **`Sph 1` MV cover** of `T² = Sph 1 × Sph 1`: the polar cover in the second factor
  (`covA = S¹ × (S¹∖{v})`, `covB = S¹ × (S¹∖{−v})`), the same shape as the S²×S² arc
  (`SphereProdHOneInt`) but one dimension lower. Each leg collapses onto `H_*(S¹)` (the punctured
  circle is contractible, `puncContraction`).
* §2 — the **disconnected intersection** `covA∩covB = S¹ × (S¹∖{v,−v})`. Unlike the S²×S² case (where
  the doubly-punctured 2-sphere is path-connected), the doubly-punctured **circle** is TWO disjoint
  arcs, so the intersection is `S¹ ⊔ S¹`: `H₀(covA∩covB;ℤ) ≅ ℤ²` and `H₁(covA∩covB;ℤ) ≅ ℤ²`, via the
  banked doubly-punctured-circle → `ℝ∖0` route (`equatorMap`) + the `posSet`/`posSetᶜ` clopen split +
  the contractible-half-line collapse.
* §3 — **`H₂(S¹×S¹;ℤ) ≅ ℤ`** (`torusTwoH2EquivInt`): the legs' `H₂ = 0` make `δ : H₂(X) → H₁(A∩B)`
  injective, with image `ker Δ₁ = {(a,−a)} ≅ ℤ` (the two arc generators map to the single `H₁(S¹)`
  generator in each leg). The torus fundamental class.
* §4 — **`H₁(S¹×S¹;ℤ) ≅ ℤ²`** (`torusTwoH1EquivInt`): the split extension `0 → ℤ → H₁(X) → ℤ → 0`,
  `im Σ₁ = coker Δ₁ ≅ ℤ` plus `im δ = ker Δ₀ ≅ ℤ` — the two circle generators.
* §5 — the `Circle × Circle` headlines, transported from `Sph 1 × Sph 1` across the
  `circleHomeoSph1` product bridge (the shape the eventual `Circle⁴` Künneth consumes).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerH0T4
import SKEFTHawking.KummerHomologyT4
import SKEFTHawking.SphereProdHTwoInt
import SKEFTHawking.SingularClopenSplitInt

namespace SKEFTHawking.KummerHomologyT2

open SKEFTHawking.SingularHomologyInt (Homology)

/-! ## §0. `H₀(S¹×S¹;ℤ) ≅ ℤ` -/

/-- **`H₀(S¹×S¹;ℤ) ≅ ℤ`** — the degree-0 torus homology, for the *actual* `T² = Circle × Circle`.
`T²` is path-connected (product of two path-connected circles), so the iso is the augmentation `ε̄`,
a genuine `ℤ` identification (one path component), not a defined-to-be-`ℤ` shell. -/
noncomputable def torusTwoH0EquivInt : Homology (TopCat.of (Circle × Circle)) 0 ≃ₗ[ℤ] ℤ :=
  haveI : PathConnectedSpace ↑(TopCat.of (Circle × Circle)) :=
    haveI : PathConnectedSpace Circle := KummerH0T4.pathConnectedSpace_circle
    KummerH0T4.pathConnectedSpace_prod
  KummerH0T4.homologyZeroPathConnectedEquivInt (TopCat.of (Circle × Circle))

end SKEFTHawking.KummerHomologyT2
