import Mathlib
import SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
import SKEFTHawking.PinPlusKTSphereProdReassoc
import SKEFTHawking.PinPlusKTSphereProdHincl

/-!
# The `S²×D³` relative fundamental class — hBbord's `HasRelFundClass` root

Assembles `HasRelFundClass (∂SphereDisk) (interiorGenFamily …)` — the open homological root of
`sphereProdCoboundaryWAdm_of_reducedAtoms` — via the GENERIC acyclic-boundary reduction
`PinPlusTraceDiskRelFundReduce.hasRelFundClass_of_acyclic_boundaryIncl`. Since `S²×D³ ≃ S²` is
acyclic in degrees 4 and 5 (`sphereDisk_homology_four/five_eq_zero`) and its boundary carries the
nonzero `betaClass`, the whole class reduces to `hincl_sphereDisk` (the Mayer–Vietoris completion,
`PinPlusKTSphereProdHincl`): at every interior point, the boundary injects into the punctured
manifold on `H₄`.

`SphereDisk`'s manifold structure over `J6 = (𝓡 4).prod (𝓡∂ 1)`'s model space is `chartW6`, exactly
the instance `isManifold_J6` / the consumer's bordism carry — so `ModelWithCorners.boundary` lines up
with the banked `sphereDisk_boundary_eq`.
-/

open scoped Manifold
open SKEFTHawking.SingularMayerVietorisLES (subIncl)
open SKEFTHawking.SingularFunctoriality (Homology.map)
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce (εtrace)
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
open SKEFTHawking.PinPlusKTSphereProdHincl (hincl_sphereDisk)

attribute [local instance] SKEFTHawking.SpinSigmaRoute.chartW6
  SKEFTHawking.SpinSigmaRoute.sphereDisk_t2Space

namespace SKEFTHawking.PinPlusKTSphereProdRelFund

/-- **hBbord's `HasRelFundClass` root** for `S²×D³ = SphereDisk`, unconditionally. Fires the generic
acyclic-boundary reduction on the banked acyclicity (`sphereDisk_homology_four/five_eq_zero`), the
banked nonzero boundary class (`betaClass_ne_zero`), and `hincl_sphereDisk` (the MV completion). This
is the `HasRelFundClass` root consumed by `sphereProdCoboundaryWAdm_of_reducedAtoms`. -/
theorem hasRelFundClass_sphereDisk :
    HasRelFundClass (X := TopCat.of SphereDisk) (((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk)
      (interiorGenFamily (W := SphereDisk) ((𝓡 4).prod (𝓡∂ 1)) εtrace) := by
  have hbd : ((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk = sphereDiskBoundarySet :=
    sphereDisk_boundary_eq
  refine PinPlusTraceDiskRelFundReduce.hasRelFundClass_of_acyclic_boundaryIncl
    (m := 3) _ _ sphereDisk_homology_five_eq_zero sphereDisk_homology_four_eq_zero
    (hbd ▸ betaClass) ?_ hincl_sphereDisk
  convert betaClass_ne_zero using 2 <;> first | rw [hbd] | (exact eqRec_heq _ _) | simp

end SKEFTHawking.PinPlusKTSphereProdRelFund
