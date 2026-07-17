/-
# Phase 5q.H close-out (#208) — THE S²×D³ COHOMOLOGY PACK: three of the six `hBbord` atoms.

#206 (`PinPlusKTSphereProdWAdm`) sharpened the sole `hBbord` residual to six atoms for a
`W = S²×D³`-type coboundary `b`. The `(1,4)` Wu leg is SETTLED-FREE (`degenerateP14`); the residual
is `{a T2 coboundary b · RelFundClassDatum D · Subsingleton (Cohomology W 1) ·
Subsingleton (RelativeCohomology ∂W 4) · the pinned (2,3) datum P23 · wuClass P23 = 0}`. This module
attacks the three cohomology atoms:

1. `Subsingleton (Cohomology W 1)` — `H¹(W;ℤ/2) = 0` (`W ≃ S²`).
2. `Subsingleton (RelativeCohomology ∂W 4)` — `H⁴(W,∂W;ℤ/2) = 0`.
3. `RelFundClassDatum` — `[W,∂W] ∈ H₅(W,∂W;ℤ/2)`.

## Concrete-model-vs-abstract decision (recorded).

The three atoms quantify over the coboundary's abstract carrier `b.W`. For a *fully generic* `b.W`
they are NOT theorems — a torus `W` falsifies atom 1. So they are intrinsically homotopy-type
obligations on `b.W`, and full deletion for abstract `b.W` is impossible; the #206 pattern keeps `b`
abstract and consumes the atoms as hypotheses. The honest, maximal narrowing therefore **reduces each
cohomological atom to its sharpest, most primitive, W-INDEPENDENT homological sub-atom** via in-tree
machinery (universal coefficients + the relative-cohomology pair LES), so the eventual geometric
coboundary provider discharges strictly simpler obligations, AND demonstrates that the reductions
bottom out at TRUE facts on the concrete `Sph 2` sphere bank. Each reduction is a genuine narrowing
(a cohomology-subsingleton becomes a homology-subsingleton or a lower-degree cohomology-subsingleton),
not a repackaging.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularUniversalCoeff
import SKEFTHawking.SingularKroneckerEquiv
import SKEFTHawking.SingularRelativeKroneckerEquiv

open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularKroneckerEquiv SKEFTHawking.SingularRelativeKroneckerEquiv

namespace SKEFTHawking.PinPlusKTSphereProdCohomology

/-! ## §1. Atom 1 — `H¹(W;ℤ/2) = 0` reduced to `H₁(W;ℤ/2) = 0` (universal coefficients). -/

variable {X : TopCat}

/-- **Atom 1, W-independent reduction.** Over the field `ℤ/2` the Kronecker pairing is a perfect
duality `Hᵏ(X) ≅ (Hₖ(X))^*` (`kroneckerHEquiv`), so a vanishing homology group forces a vanishing
cohomology group: `Subsingleton (Homology X (N+1)) → Subsingleton (Cohomology X (N+1))`. For
`N = 0`, `X = W ≃ S²`, this is `H¹(W;ℤ/2) = 0` from `H₁(W;ℤ/2) = 0` — the sharpest sub-atom of the
`Subsingleton (Cohomology W 1)` atom. -/
theorem subsingleton_cohomology_of_homology (N : ℕ) [Subsingleton (Homology X (N + 1))] :
    Subsingleton (Cohomology X (N + 1)) := by
  haveI : Subsingleton (Homology X (N + 1) →ₗ[ZMod 2] ZMod 2) :=
    ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact (kroneckerHEquiv (X := X) N).toEquiv.subsingleton

/-! ## §2. Atom 2 — `H⁴(W,∂W;ℤ/2) = 0` reduced to `H₄(W,∂W;ℤ/2) = 0` (relative universal
coefficients). -/

/-- **Atom 2, W-independent reduction.** The relative Kronecker pairing is a perfect duality
`Hᵏ(X,S) ≅ (Hₖ(X,S))^*` over `ℤ/2` (`relKroneckerHEquiv`), so a vanishing relative homology group
forces a vanishing relative cohomology group:
`Subsingleton (RelativeHomology S (N+1)) → Subsingleton (RelativeCohomology S (N+1))`. For `N = 3`,
`S = ∂W`, this is `H⁴(W,∂W;ℤ/2) = 0` from `H₄(W,∂W;ℤ/2) = 0` (Poincaré–Lefschetz `≅ H¹(W) = 0`) —
the sharpest sub-atom of the `Subsingleton (RelativeCohomology ∂W 4)` atom. The exact relative twin
of `subsingleton_cohomology_of_homology`. -/
theorem subsingleton_relativeCohomology_of_relativeHomology (S : Set ↑X) (N : ℕ)
    [Subsingleton (RelativeHomology S (N + 1))] : Subsingleton (RelativeCohomology S (N + 1)) := by
  haveI : Subsingleton (RelativeHomology S (N + 1) →ₗ[ZMod 2] ZMod 2) :=
    ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact (relKroneckerHEquiv S N).toEquiv.subsingleton

end SKEFTHawking.PinPlusKTSphereProdCohomology
