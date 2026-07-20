/-
# Phase 5q.H — the `(2,3)` `nondeg` cohomology feeder for `S²×D³` (`hfeeder`)

The one un-banked cohomology atom of `SphereProdP23NondegClose.sphereDiskNondeg23_direct`:

  `hfeeder : ∀ a : H²(S²×D³;ℤ/2), a ≠ 0 → (a|_{∂W}) ≠ 0`

— i.e. the boundary restriction `H²(S²×D³) → H²(∂(S²×D³))` (`cohomologyPullback (inclC ∂W)`) is
INJECTIVE. Since `H²(S²×D³;ℤ/2)` is `1`-dimensional (`finrank_sphereDisk_cohomology_two`), injectivity
follows from nonvanishing on a generator.

## The slice-section route

The restriction `r` equals `sphereDiskIncl*` up to the boundary homeomorphism (`inclC ∘ e =
sphereDiskIncl`, `e = sphereDiskInclHomeo`, defeq), so `r` is injective iff `sphereDiskIncl* :
H²(S²×D³) → H²(S²×S²)` is. The slice `j := sphereDiskIncl ∘ σ₁` (`σ₁(x)=(x,y₀)`, i.e. `j(x)=(x,q₀)`)
has the first projection `prS : S²×D³ → S²` as a LEFT inverse (`prS ∘ j = id`), so `j* = σ₁* ∘
sphereDiskIncl*` is SURJECTIVE, hence (equal `finrank 1 = 1`) bijective, hence injective. Then
`sphereDiskIncl* a = 0 ⟹ j* a = σ₁*(sphereDiskIncl* a) = 0 ⟹ a = 0`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SphereProdP23NondegClose
import SKEFTHawking.SphereProdBoundaryCupSquare

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SphereProdBoundaryCupSquare (sec1)

namespace SKEFTHawking.SphereProdP23NondegFeeder

noncomputable section

/-- First projection `prS : S²×D³ → S²`. -/
def prS : C(↑(TopCat.of SphereDisk), ↑(TopCat.of TwoSphere)) := ⟨Prod.fst, continuous_fst⟩

/-- The boundary inclusion `S²×S² → S²×D³` as a `ContinuousMap`. -/
def sphereDiskInclCM : C(↑(TopCat.of SphereProd), ↑(TopCat.of SphereDisk)) :=
  ⟨sphereDiskIncl, sphereDiskIncl_continuous⟩

/-- The boundary-inclusion homeo composed with the subtype inclusion is `sphereDiskIncl` (defeq). -/
theorem inclC_comp_homeo_eq_sphereDiskIncl :
    (SingularCapConnecting.inclC (X := TopCat.of SphereDisk) sphereDiskBoundarySet).comp
        (⟨sphereDiskInclHomeo, sphereDiskInclHomeo.continuous⟩ :
          C(↑(TopCat.of SphereProd), ↑(sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet)))
      = sphereDiskInclCM := by
  apply ContinuousMap.ext; intro x; rfl

/-- The slice section `prS ∘ (sphereDiskIncl ∘ σ₁) = id` on `S²`. -/
theorem prS_comp_slice_eq_id (y₀ : TwoSphere) :
    prS.comp (sphereDiskInclCM.comp (sec1 y₀)) = ContinuousMap.id (↑(TopCat.of TwoSphere)) := by
  apply ContinuousMap.ext; intro x; rfl

/-- **`sphereDiskIncl* : H²(S²×D³) → H²(S²×S²)` is injective.** The slice `j = sphereDiskIncl ∘ σ₁`
has `prS` as a left inverse, so `j* = σ₁* ∘ sphereDiskIncl*` is surjective; equal `finrank 1 = 1`
makes it bijective, hence injective, which forces `sphereDiskIncl*` injective. -/
theorem sphereDiskIncl_cohomology_injective :
    Function.Injective (cohomologyPullback sphereDiskInclCM 2) := by
  let y₀ : TwoSphere := Classical.arbitrary TwoSphere
  haveI : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of TwoSphere) 2) :=
    SKEFTHawking.SingularMVCohomologyFinite.finiteDimensional_cohomology_of_homology
      (X := TopCat.of TwoSphere) 1
      SKEFTHawking.SphereProdP23.finiteDimensional_twoSphere_homology_two
  haveI : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of SphereDisk) 2) :=
    SKEFTHawking.SphereProdP23.sphereDisk_findimAbs23
  -- `j* ∘ prS* = id`, so `j* = σ₁* ∘ sphereDiskIncl*` is surjective.
  have hjsurj : Function.Surjective
      (cohomologyPullback (sphereDiskInclCM.comp (sec1 y₀)) 2) := by
    have hcomp : (cohomologyPullback (sphereDiskInclCM.comp (sec1 y₀)) 2).comp
        (cohomologyPullback prS 2) = LinearMap.id := by
      rw [← cohomologyPullback_comp, prS_comp_slice_eq_id, cohomologyPullback_id]
    exact Function.RightInverse.surjective (g := cohomologyPullback prS 2)
      (fun x => LinearMap.congr_fun hcomp x)
  -- surjective between equal-`finrank` spaces ⟹ injective (rank–nullity).
  have hjinj : Function.Injective (cohomologyPullback (sphereDiskInclCM.comp (sec1 y₀)) 2) := by
    rw [← LinearMap.ker_eq_bot]
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (cohomologyPullback (sphereDiskInclCM.comp (sec1 y₀)) 2)
    rw [LinearMap.range_eq_top.mpr hjsurj] at hrn
    have hdisk : Module.finrank (ZMod 2) (Cohomology (TopCat.of SphereDisk) 2) = 1 :=
      SKEFTHawking.SphereProdP23.finrank_sphereDisk_cohomology_two
    have hsph : Module.finrank (ZMod 2) (Cohomology (TopCat.of TwoSphere) 2) = 1 :=
      SKEFTHawking.SphereProdP23Nondeg.finrank_twoSphere_cohomology_two
    rw [finrank_top, hdisk, hsph] at hrn
    have hker0 : Module.finrank (ZMod 2)
        (LinearMap.ker (cohomologyPullback (sphereDiskInclCM.comp (sec1 y₀)) 2)) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp hker0
  -- factor `j* = σ₁* ∘ sphereDiskIncl*` and peel the injective `j*`.
  intro a b hab
  apply hjinj
  show cohomologyPullback (sphereDiskInclCM.comp (sec1 y₀)) 2 a
      = cohomologyPullback (sphereDiskInclCM.comp (sec1 y₀)) 2 b
  rw [cohomologyPullback_comp, LinearMap.comp_apply, LinearMap.comp_apply, hab]

/-- **`hfeeder` — the `(2,3)` `nondeg` cohomology feeder for `S²×D³`.** The boundary restriction
`H²(S²×D³;ℤ/2) → H²(∂W;ℤ/2)` is injective, so it carries nonzero classes to nonzero classes. Feeds
`SphereProdP23NondegClose.sphereDiskNondeg23_direct`. -/
theorem sphereDisk_boundaryRestrict_ne_zero
    (a : Cohomology (TopCat.of SphereDisk) 2) (ha : a ≠ 0) :
    cohomologyPullback (SingularCapConnecting.inclC (X := TopCat.of SphereDisk)
      sphereDiskBoundarySet) 2 a ≠ 0 := by
  intro hcontra
  apply ha
  apply sphereDiskIncl_cohomology_injective
  rw [map_zero, ← inclC_comp_homeo_eq_sphereDiskIncl, cohomologyPullback_comp, LinearMap.comp_apply,
    hcontra, map_zero]

end

end SKEFTHawking.SphereProdP23NondegFeeder
