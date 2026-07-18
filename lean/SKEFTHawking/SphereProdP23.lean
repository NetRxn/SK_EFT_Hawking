/-
# Phase 5q.H — the `(2,3)` Lefschetz–Wu FINITE-DIMENSIONALITY half for `S²×D³` (P23 numerics)

The `hBbord` `(2,3)` residual (`PinPlusKTSphereProdCohomology.sphereProdCoboundaryWAdm_of_reducedAtoms`)
needs a concrete `LefschetzWuDatum (TopCat.of SphereDisk) sphereDiskBoundarySet 2 3 5`, i.e. the four
`ofRelFund23` numerics `{findimAbs, findimRel, nondeg, dimeq}` on the FIXED carrier
`W = SphereDisk = S²×D³`, `∂W = sphereDiskBoundarySet ≃ S²×S²`.

This module discharges the TWO **finite-dimensionality** numerics — `findimAbs`, `findimRel` — on the
fixed carrier, kernel-pure and unconditionally, AND (in §3) banks the FIRST of the two EXACT rank-1
identities `dimeq` needs plus the reduction of the second, leaving `dimeq` conditional on ONE crisp
un-banked relative-rank residual and `nondeg` fully residual (lead-owned). The finiteness numerics
bottom out at ALREADY-BANKED sphere / sphere-product facts via the carrier-agnostic exact-sequence
bricks of `SingularMVCohomologyFinite`:

* **`sphereDisk_findimAbs23`** — `H²(S²×D³;ℤ/2)` finite. Route: mod-2 universal coefficients
  (`finiteDimensional_cohomology_of_homology`) ∘ the contractible-`D³`-factor collapse
  (`PinPlusKTSphereProdRelFundWuRoots.sphereDiskCollapse`) ∘ the top mod-2 sphere homology
  `H₂(S²;ℤ/2) ≅ ℤ/2` (`SingularLineMinusPoint.topSphereIso`).
* **`sphereDisk_findimRel23`** — `H³(S²×D³, S²×S²;ℤ/2)` finite. Route: relative mod-2 universal
  coefficients (`finiteDimensional_relativeCohomology_of_relativeHomology`) ∘ the pair-LES sandwich
  (`finiteDimensional_relativeHomology_of_pair`) fed by `H₃(S²×D³;ℤ/2) = 0` (collapse + high-degree
  sphere vanishing) and `H₂(S²×S²;ℤ/2)` finite (the closed-4-manifold homology finiteness
  `SingularClosedHomologyFinite.finiteDimensional_homology_of_closed` on `SphereProd`, transported
  along the boundary homeomorphism `PinPlusKTSphereProdRelFundWuRoots.sphereDiskInclHomeo`).

## §3 — the `dimeq` numeric: one EXACT rank-1 identity banked, the other reduced

`dimeq` is the Betti equality `dim H²(W;ℤ/2) = dim H³(W,∂W;ℤ/2)`, and its content is the two EXACT
rank-1 identities `dim H²(W) = 1` and `dim H³(W,∂W) = 1`. §3 banks:

* **`finrank_sphereDisk_cohomology_two`** — the EXACT `dim H²(S²×D³;ℤ/2) = 1` (not merely finite): the
  perfect Kronecker pairing `kroneckerHEquiv 1 : H²(W) ≃ (H₂(W))^*`, then `Subspace.dual_finrank_eq`, the
  collapse `sphereDiskCollapse 1 : H₂(S²×D³) ≃ H₂(S²)`, and `topSphereIso 1 : H₂(S²) ≃ ℤ/2`. GENUINE.
* **`finrank_relativeCohomology_eq_relativeHomology`** — the UNCONDITIONAL reduction (generic in `(X,S,N)`)
  `dim Hᴺ⁺¹(X,S) = dim H_{N+1}(X,S)` via the relative Kronecker pairing, so the second identity's residual
  is the pure-homology rank `dim H₃(W,∂W;ℤ/2)`.
* **`sphereDiskDimeq23_of_relativeCohomology_rank_one`** — assembles the full `dimeq` (the exact field
  `LefschetzWuDatum.ofRelFund23` expects) CONDITIONAL on the ONE residual `dim H³(W,∂W;ℤ/2) = 1`.

## §4 — `dimeq` reduced to a SINGLE crisp geometric residual (`homIncl ≠ 0`)

§4 discharges the pair-LES rank computation, so `dimeq` now hinges on ONE geometric fact, NOT on the
former "no in-tree UCT bridge" wall (that wall is GONE — the mod-2 rank UCT is banked in
`SphereProdHTwoMod2`):

* **`finrank_sphereDiskBoundary_homology_two`** — `dim H₂(∂W;ℤ/2) = 2`, transported from
  `SphereProdHTwoMod2.finrank_sphereProd_homologyMod2_two` (the genuine mod-2 rank UCT on the banked
  `redHomology` bridge) along `sphereDiskInclHomeo`.
* **`finrank_sphereDisk_homology_two`** — `dim H₂(W;ℤ/2) = 1` (collapse + `topSphereIso`).
* **`finrank_relativeHomology_three_of_homIncl_ne_zero`** — the pair-LES
  `H₃(W)=0 → H₃(W,∂W) →δ H₂(∂W) →i H₂(W)`: `δ` injective (`H₃(W)=0`), rank–nullity on `i = homIncl`
  gives `dim H₃(W,∂W;ℤ/2) = 2 − rank i = 1` GIVEN `i ≠ 0`.
* **`sphereDiskDimeq23_of_homIncl_ne_zero`** — the full `(2,3)` `dimeq`, CONDITIONAL only on
  `homIncl sphereDiskBoundarySet 2 ≠ 0`.

### The precise remaining residual (reported, NOT faked)

* **`dimeq` residual** — `homIncl sphereDiskBoundarySet 2 ≠ 0`: the boundary inclusion `S²×S² ↪ S²×D³`
  induces a NONZERO map on `H₂(·;ℤ/2)` (the surviving `S²` area class). The clean route is the banked
  integral→mod-2 naturality `SingularLocalHomologyRedCompatInt.redHomology_homIncl`
  (`redHomology X 2 (homIncl_int S 2 h) = homIncl S 2 (redHomology (sub S) 2 h)`) plus the integral
  first-projection `SphereProdHTwoInt.sumInto_prodFst` and `redHomology`-of-generator nonvanishing
  (`SingularSphereGenReducesInt`), but it needs the map-identification lemmas `homIncl_int = mapInt`
  of the subtype inclusion and `sphereDiskCollapse = Homology.map prodFst`, which are NOT in-tree —
  a separate `homIncl`-realization sub-brick.
* **`nondeg` residual** (lead-owned) — Lefschetz non-degeneracy of the GENUINE Alexander–Whitney cup
  `SingularRelativeCup.relCupH23` against the fundamental functional. Requires the relative cross-product /
  cohomology cup-Fubini for the `(D³, ∂D³)` factor. The ONLY in-tree relative cross-product
  (`SingularRelativeCrossProduct`) is the interval `[I, ∂I]` engine (`prismOp` over `Δᵖ × I`); there is NO
  `[D³, ∂D³]` analogue. The cylinder discharged its own `nondeg` only through an entire interval-specific
  tower (`…CylinderSuspDual.CylinderSuspIntertwineData.ofCapCross`, `SingularCapCrossProjection`,
  `…CrossLocalBridge`), none of which transfers to a 3-disk factor — the same wall the sibling
  `PinPlusKTSphereProdRelFundWuRoots` docstring names.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
import SKEFTHawking.SingularMVCohomologyFinite
import SKEFTHawking.SingularLineMinusPoint
import SKEFTHawking.SingularClosedHomologyFinite
import SKEFTHawking.SingularSphereHighDegree
import SKEFTHawking.SphereProdHTwoMod2
import SKEFTHawking.SingularPairLES

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularMVCohomologyFinite
open SKEFTHawking.SingularLineMinusPoint (topSphereIso)
open SKEFTHawking.SingularSphereHighDegree (sphere_homology_high)
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
open SKEFTHawking.PinPlusCharPairRealizationTied (homeoHomologyEquiv)
open SKEFTHawking.SingularKroneckerEquiv (kroneckerHEquiv)
open SKEFTHawking.SingularRelativeKroneckerEquiv (relKroneckerHEquiv)
open SKEFTHawking.SingularPairLES (homIncl homProj connecting exact_homProj_connecting
  exact_connecting_homIncl)

namespace SKEFTHawking.SphereProdP23

noncomputable section

/-! ## §1. `findimAbs` — `H²(S²×D³;ℤ/2)` finite-dimensional. -/

/-- `H₂(S²;ℤ/2)` is finite-dimensional — the top mod-2 homology of the 2-sphere is `≅ ℤ/2`
(`topSphereIso`), `TopCat.of TwoSphere = Sph 2` definitionally. -/
theorem finiteDimensional_twoSphere_homology_two :
    FiniteDimensional (ZMod 2) (Homology (TopCat.of TwoSphere) 2) :=
  (topSphereIso 1).symm.finiteDimensional

/-- `H₂(S²×D³;ℤ/2)` is finite-dimensional — transported across the contractible-`D³`-factor collapse
`sphereDiskCollapse 1 : H₂(S²×D³) ≃ H₂(S²)`. -/
theorem finiteDimensional_sphereDisk_homology_two :
    FiniteDimensional (ZMod 2) (Homology (TopCat.of SphereDisk) 2) := by
  haveI := finiteDimensional_twoSphere_homology_two
  exact (sphereDiskCollapse 1).symm.finiteDimensional

/-- **`findimAbs` for the `(2,3)` leg** — `H²(S²×D³;ℤ/2)` finite-dimensional, via mod-2 universal
coefficients (`finiteDimensional_cohomology_of_homology`) from `H₂(S²×D³;ℤ/2)` finite. -/
theorem sphereDisk_findimAbs23 :
    FiniteDimensional (ZMod 2) (Cohomology (TopCat.of SphereDisk) 2) :=
  finiteDimensional_cohomology_of_homology (X := TopCat.of SphereDisk) 1
    finiteDimensional_sphereDisk_homology_two

/-! ## §2. `findimRel` — `H³(S²×D³, S²×S²;ℤ/2)` finite-dimensional. -/

/-- `H₃(S²×D³;ℤ/2) = 0` — the ambient acyclicity in degree 3, via the collapse to `H₃(S²;ℤ/2)`, which
vanishes since `3 > 2` (`sphere_homology_high`). -/
theorem sphereDisk_homology_three_eq_zero (x : Homology (TopCat.of SphereDisk) 3) : x = 0 := by
  apply (sphereDiskCollapse 2).injective
  rw [map_zero]
  exact sphere_homology_high 2 3 (by norm_num) (sphereDiskCollapse 2 x)

/-- `H₃(S²×D³;ℤ/2)` is finite-dimensional (it vanishes). -/
theorem finiteDimensional_sphereDisk_homology_three :
    FiniteDimensional (ZMod 2) (Homology (TopCat.of SphereDisk) 3) := by
  haveI : Subsingleton (Homology (TopCat.of SphereDisk) 3) :=
    ⟨fun a b => (sphereDisk_homology_three_eq_zero a).trans
      (sphereDisk_homology_three_eq_zero b).symm⟩
  exact Module.Finite.of_finite

/-- `H₂(S²×S²;ℤ/2)` is finite-dimensional — the closed-4-manifold homology finiteness
(`finiteDimensional_homology_of_closed`, degree 2) on `SphereProd`, using its `E⁴` chart
(`chartedSpaceE4_SphereProd`). -/
theorem finiteDimensional_sphereProd_homology_two :
    FiniteDimensional (ZMod 2) (Homology (TopCat.of SphereProd) 2) :=
  (@SingularClosedHomologyFinite.finiteDimensional_homology_of_closed
    SphereProd _ _ _ _ chartedSpaceE4_SphereProd).2.1

/-- `H₂(sphereDiskBoundarySet;ℤ/2)` is finite-dimensional — transported from `H₂(S²×S²;ℤ/2)` along the
boundary homeomorphism `sphereDiskInclHomeo : SphereProd ≃ₜ sub sphereDiskBoundarySet`. -/
theorem finiteDimensional_sphereDiskBoundary_homology_two :
    FiniteDimensional (ZMod 2)
      (Homology (sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet) 2) :=
  haveI := finiteDimensional_sphereProd_homology_two
  FiniteDimensional.of_injective
    (homeoHomologyEquiv sphereDiskInclHomeo 2).symm.toLinearMap
    (homeoHomologyEquiv sphereDiskInclHomeo 2).symm.injective

/-- **`findimRel` for the `(2,3)` leg** — `H³(S²×D³, S²×S²;ℤ/2)` finite-dimensional, via relative mod-2
universal coefficients (`finiteDimensional_relativeCohomology_of_relativeHomology`) ∘ the pair-LES
sandwich (`finiteDimensional_relativeHomology_of_pair`) fed by `H₃(W;ℤ/2) = 0` and `H₂(∂W;ℤ/2)`
finite. -/
theorem sphereDisk_findimRel23 :
    FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3) := by
  have hrel : FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3) :=
    finiteDimensional_relativeHomology_of_pair (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2
      finiteDimensional_sphereDisk_homology_three
      finiteDimensional_sphereDiskBoundary_homology_two
  exact finiteDimensional_relativeCohomology_of_relativeHomology
    (X := TopCat.of SphereDisk) (S := sphereDiskBoundarySet) 2 hrel

/-! ## §3. `dimeq` for the `(2,3)` leg — the two EXACT rank-1 identities and their equality. -/

/-- **The EXACT `ℤ/2`-dimension of `H²(S²×D³;ℤ/2)` is `1`.** Not merely finite: the `S²` area class
survives the contractible-`D³`-factor collapse. Chain: the perfect Kronecker pairing
`kroneckerHEquiv 1 : H²(W) ≃ (H₂(W))^*`, then `Subspace.dual_finrank_eq` (`dim V^* = dim V`), the
collapse `sphereDiskCollapse 1 : H₂(S²×D³) ≃ H₂(S²)`, and the top sphere homology
`topSphereIso 1 : H₂(S²) ≃ ℤ/2`. -/
theorem finrank_sphereDisk_cohomology_two :
    Module.finrank (ZMod 2) (Cohomology (TopCat.of SphereDisk) 2) = 1 := by
  rw [(kroneckerHEquiv (X := TopCat.of SphereDisk) 1).finrank_eq, Subspace.dual_finrank_eq,
    (sphereDiskCollapse 1).finrank_eq, (topSphereIso 1).finrank_eq, Module.finrank_self]

/-- **Relative Kronecker duality of ranks (any subspace, any successor degree).** By the perfect
relative Kronecker pairing `relKroneckerHEquiv N : Hᴺ⁺¹(X,S) ≃ (H_{N+1}(X,S))^*` and
`Subspace.dual_finrank_eq` (`dim V^* = dim V`), `dim Hᴺ⁺¹(X,S;ℤ/2) = dim H_{N+1}(X,S;ℤ/2)`. UNCONDITIONAL
(no finite-dimensionality needed — both sides `0` when infinite-dimensional). Stated at the equiv's
native `N+1` index so the rewrite matches syntactically. Applied at `S = sphereDiskBoundarySet`, `N = 2`
this reduces the `(2,3)` `dimeq` residual `dim H³(W,∂W)` to the pure-homology rank `dim H₃(W,∂W)`. -/
theorem finrank_relativeCohomology_eq_relativeHomology {X : TopCat} (S : Set X) (N : ℕ) :
    Module.finrank (ZMod 2) (RelativeCohomology S (N + 1))
      = Module.finrank (ZMod 2) (RelativeHomology S (N + 1)) := by
  rw [(relKroneckerHEquiv S N).finrank_eq, Subspace.dual_finrank_eq]

/-- **`dimeq` for the `(2,3)` leg, CONDITIONAL on the ONE un-banked relative-cohomology-rank residual.**
Given `dim H³(S²×D³,S²×S²;ℤ/2) = 1` — the genuinely-nonzero relative-cohomology rank (Lefschetz-dual to
the surviving `S²` area class; `= dim H³(D³,∂D³)⊗H⁰(S²) = 1` by the relative Künneth `S²×(D³,∂D³)`) — the
Lefschetz Betti equality `dim H²(W) = dim H³(W,∂W)` holds, both sides `= 1`. The absolute side
(`finrank_sphereDisk_cohomology_two`) is banked UNCONDITIONALLY; the relative rank is the sole residual
(see the module docstring's residual section). This is exactly the `dimeq` field
`PoincareLefschetzWuAssembly.LefschetzWuDatum.ofRelFund23` expects, once the residual is discharged.
The residual is equivalently the relative-homology rank `dim H₃(W,∂W;ℤ/2) = 1` via
`finrank_relativeCohomology_eq_relativeHomology sphereDiskBoundarySet 2`. -/
theorem sphereDiskDimeq23_of_relativeCohomology_rank_one
    (hrel : Module.finrank (ZMod 2)
      (RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3) = 1) :
    Module.finrank (ZMod 2) (Cohomology (TopCat.of SphereDisk) 2)
      = Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3) := by
  rw [finrank_sphereDisk_cohomology_two, hrel]

/-! ## §4. The residual `dim H₃(W,∂W;ℤ/2) = 1` via the mod-2 pair-LES.

The `dimeq` residual `dim H³(W,∂W;ℤ/2) = 1` reduces (via
`finrank_relativeCohomology_eq_relativeHomology`) to `dim H₃(W,∂W;ℤ/2) = 1`, which the mod-2 pair-LES
`H₃(W) →ᵖ H₃(W,∂W) →ᵟ H₂(∂W) →ⁱ H₂(W)` supplies once the two Betti inputs
`dim H₂(∂W;ℤ/2) = 2` (transported from `SphereProdHTwoMod2.finrank_sphereProd_homologyMod2_two`) and
`dim H₂(W;ℤ/2) = 1` are banked and the boundary inclusion `i = homIncl` is nonzero (the surviving
`S²` class). With `H₃(W;ℤ/2) = 0` the connecting `δ` is injective, so
`dim H₃(W,∂W) = dim ker i = 2 − rank i = 2 − 1 = 1`. -/

/-- `dim_{ℤ/2} H₂(∂W;ℤ/2) = 2` on the boundary set — transported from
`SphereProdHTwoMod2.finrank_sphereProd_homologyMod2_two` along the boundary homeomorphism
`sphereDiskInclHomeo`. -/
theorem finrank_sphereDiskBoundary_homology_two :
    Module.finrank (ZMod 2)
      (Homology (sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet) 2) = 2 := by
  rw [← (homeoHomologyEquiv sphereDiskInclHomeo 2).finrank_eq]
  exact SphereProdHTwoMod2.finrank_sphereProd_homologyMod2_two

/-- **The EXACT `ℤ/2`-dimension of `H₂(S²×D³;ℤ/2)` is `1`** — the surviving `S²` area class, via the
contractible-`D³`-factor collapse `sphereDiskCollapse 1` and the top sphere homology
`topSphereIso 1 : H₂(S²) ≃ ℤ/2`. The homology analogue of `finrank_sphereDisk_cohomology_two`. -/
theorem finrank_sphereDisk_homology_two :
    Module.finrank (ZMod 2) (Homology (TopCat.of SphereDisk) 2) = 1 := by
  rw [(sphereDiskCollapse 1).finrank_eq, (topSphereIso 1).finrank_eq, Module.finrank_self]

/-- **`dim H₃(S²×D³, S²×S²;ℤ/2) = 1`, CONDITIONAL on the boundary inclusion being nonzero.** The
mod-2 pair-LES `H₃(W) →ᵖ H₃(W,∂W) →ᵟ H₂(∂W) →ⁱ H₂(W)`: `H₃(W;ℤ/2) = 0` makes `ᵖ` the zero map, so
exactness makes `δ` injective (`H₃(W,∂W) ≃ range δ = ker i`); rank–nullity on
`i = homIncl` (`dim H₂(∂W) = 2`) with `rank i = 1` (nonzero `i`, `range i ⊆ H₂(W)` of dim 1) gives
`dim ker i = 2 − 1 = 1`. The `i ≠ 0` hypothesis is the surviving-`S²`-class geometric residual. -/
theorem finrank_relativeHomology_three_of_homIncl_ne_zero
    (hincl : homIncl (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2 ≠ 0) :
    Module.finrank (ZMod 2)
      (RelativeHomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3) = 1 := by
  haveI := finiteDimensional_sphereDiskBoundary_homology_two
  haveI := finiteDimensional_sphereDisk_homology_two
  haveI : Subsingleton (Homology (TopCat.of SphereDisk) (2 + 1)) :=
    ⟨fun a b => (sphereDisk_homology_three_eq_zero a).trans
      (sphereDisk_homology_three_eq_zero b).symm⟩
  -- `homProj` on the subsingleton `H₃(W)` is the zero map, so `δ = connecting` is injective.
  have hker : LinearMap.ker (connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2) = ⊥ := by
    rw [(exact_homProj_connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2).linearMap_ker_eq,
      LinearMap.range_eq_bot]
    ext x
    simp [Subsingleton.elim x 0]
  have hconn_inj :
      Function.Injective (connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2) :=
    LinearMap.ker_eq_bot.mp hker
  -- `H₃(W,∂W) ≃ range δ = ker i`.
  have heq1 : Module.finrank (ZMod 2)
      (RelativeHomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3)
      = Module.finrank (ZMod 2)
        (LinearMap.range (connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2)) :=
    (LinearEquiv.ofInjective _ hconn_inj).finrank_eq
  have heq2 : LinearMap.range (connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2)
      = LinearMap.ker (homIncl (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2) :=
    ((exact_connecting_homIncl (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2).linearMap_ker_eq).symm
  rw [heq1, heq2]
  -- rank–nullity for `i = homIncl S 2` with `rank i = 1`.
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (homIncl (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2)
  rw [finrank_sphereDiskBoundary_homology_two] at hrn
  have hne : LinearMap.range (homIncl (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2) ≠ ⊥ :=
    fun h => hincl (LinearMap.range_eq_bot.mp h)
  have hrange1 : Module.finrank (ZMod 2)
      (LinearMap.range (homIncl (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2)) = 1 := by
    have hle : Module.finrank (ZMod 2)
        (LinearMap.range (homIncl (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2))
        ≤ Module.finrank (ZMod 2) (Homology (TopCat.of SphereDisk) 2) := Submodule.finrank_le _
    rw [finrank_sphereDisk_homology_two] at hle
    have hpos : 0 < Module.finrank (ZMod 2)
        (LinearMap.range (homIncl (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2)) :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne)
    omega
  omega

/-- The relative-cohomology↔homology rank bridge at the LITERAL index `3` (the reduction
`finrank_relativeCohomology_eq_relativeHomology` re-stated at `3` rather than `2+1`). The `3 → 2+1`
conversion is pushed through `congrArg` at the `finrank` (`ℕ`-valued) level, so the heavy
`RelativeCohomology` `2+1↔3` *type*-defeq (which blows the heartbeat wall) never fires. -/
theorem finrank_relativeCohomology_three_eq_relativeHomology :
    Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3)
      = Module.finrank (ZMod 2)
        (RelativeHomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3) := by
  have h32 : (3 : ℕ) = 2 + 1 := rfl
  rw [congrArg (fun n => Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet n)) h32,
    congrArg (fun n => Module.finrank (ZMod 2)
        (RelativeHomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet n)) h32]
  exact finrank_relativeCohomology_eq_relativeHomology
    (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2

/-- **`dimeq` for the `(2,3)` leg, CONDITIONAL only on the boundary inclusion `homIncl S 2 ≠ 0`.**
Combines the pair-LES residual `finrank_relativeHomology_three_of_homIncl_ne_zero` with the banked
relative-Kronecker reduction and the unconditional absolute rank. The sole remaining input to the
full `(2,3)` `dimeq` is now the crisp geometric fact that the boundary `S²×S² ↪ S²×D³` induces a
nonzero map on `H₂(·;ℤ/2)` (the surviving `S²` area class). -/
theorem sphereDiskDimeq23_of_homIncl_ne_zero
    (hincl : homIncl (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2 ≠ 0) :
    Module.finrank (ZMod 2) (Cohomology (TopCat.of SphereDisk) 2)
      = Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3) :=
  sphereDiskDimeq23_of_relativeCohomology_rank_one
    (finrank_relativeCohomology_three_eq_relativeHomology.trans
      (finrank_relativeHomology_three_of_homIncl_ne_zero hincl))

end

end SKEFTHawking.SphereProdP23
