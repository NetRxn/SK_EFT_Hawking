/-
# Phase 5q.H — the `(2,3)` Lefschetz–Wu FINITE-DIMENSIONALITY half for `S²×D³` (P23 numerics)

The `hBbord` `(2,3)` residual (`PinPlusKTSphereProdCohomology.sphereProdCoboundaryWAdm_of_reducedAtoms`)
needs a concrete `LefschetzWuDatum (TopCat.of SphereDisk) sphereDiskBoundarySet 2 3 5`, i.e. the four
`ofRelFund23` numerics `{findimAbs, findimRel, nondeg, dimeq}` on the FIXED carrier
`W = SphereDisk = S²×D³`, `∂W = sphereDiskBoundarySet ≃ S²×S²`.

This module discharges the TWO **finite-dimensionality** numerics — `findimAbs`, `findimRel` — on the
fixed carrier, kernel-pure and unconditionally, precisely isolating the residual of the `(2,3)` leg to
`{nondeg, dimeq}` (the perfect-cup-pairing content). Both bottom out at ALREADY-BANKED sphere /
sphere-product facts via the carrier-agnostic exact-sequence bricks of `SingularMVCohomologyFinite`:

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

## The precise remaining residual of the `(2,3)` leg (reported, NOT faked)

The other two numerics — `nondeg` (Lefschetz non-degeneracy of the GENUINE Alexander–Whitney cup
`SingularRelativeCup.relCupH23` against the fundamental functional) and `dimeq` (the Betti equality
`dim H²(W) = dim H³(W,∂W) = 1`) — are the perfect-pairing content, and both require the relative
cross-product / cohomology cup-Fubini for the `(D³, ∂D³)` factor. The ONLY in-tree relative
cross-product (`SingularRelativeCrossProduct`) is the interval `[I, ∂I]` engine (`prismOp` over
`Δᵖ × I`); there is NO `[D³, ∂D³]` analogue. The cylinder discharged its own `nondeg` only through an
entire interval-specific tower (`…CylinderSuspDual.CylinderSuspIntertwineData.ofCapCross`,
`SingularCapCrossProjection`, `…CrossLocalBridge`), none of which transfers to a 3-disk factor —
this is the same class of wall the sibling `PinPlusKTSphereProdRelFundWuRoots` docstring names ("the
`(2,3)` Wu datum needs an ADDITIONAL, separate Lefschetz-nondegeneracy computation … not attempted
here"). So this module banks the two provable numerics and leaves `{nondeg, dimeq}` as the honest,
precisely-scoped residual.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
import SKEFTHawking.SingularMVCohomologyFinite
import SKEFTHawking.SingularLineMinusPoint
import SKEFTHawking.SingularClosedHomologyFinite
import SKEFTHawking.SingularSphereHighDegree

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularMVCohomologyFinite
open SKEFTHawking.SingularLineMinusPoint (topSphereIso)
open SKEFTHawking.SingularSphereHighDegree (sphere_homology_high)
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
open SKEFTHawking.PinPlusCharPairRealizationTied (homeoHomologyEquiv)

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

end

end SKEFTHawking.SphereProdP23
