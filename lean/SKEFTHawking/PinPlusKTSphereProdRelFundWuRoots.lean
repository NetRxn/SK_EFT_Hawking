/-
# Phase 5q.H close-out (#211) — THE S²×D³ RELATIVE-FUNDAMENTAL-CLASS + LEFSCHETZ-WU ROOTS

Attacks the deepest remaining atoms of `PinPlusKTSphereProdCohomology.sphereProdCoboundaryWAdm_of_reducedAtoms`
specialized to the FIXED space `SphereDisk = S²×D³` and boundary `sphereDiskBoundarySet = S²×S²`:

1. The `(2,3)` Lefschetz–Wu datum `sphereDiskP23`, its pin, and `wuClass sphereDiskP23 = 0`.
2. The relative fundamental class existence witness
   `HasRelFundClass (TopCat.of SphereDisk) sphereDiskBoundarySet (interiorGenFamily … εtrace)`.

## What lands GREEN here (kernel-pure, no `sorry`/axiom/`native_decide`/`maxHeartbeats`)

Both deliverables bottom out at the SAME deep atom — a `RelFundClassDatum`/`HasRelFundClass` for the
pair `(S²×D³, S²×S²)` — which in turn needs `HasRelFundClass` for a genuine PRODUCT manifold with a
nontrivial base factor (`S²`), a strictly harder shape than anything closed in-tree so far (the
30+-file `PoincareLefschetzRelFundClassCylinder*` tower discharges `M × [0,1]`, and even THAT module's
own docstring names its product existence witness as an open, named residual — "the exact missing
tool is a relative cross-product"). The plain-disk case (`D⁵`, no base factor) IS closed
(`PinPlusTraceDiskCorePair.hasRelFundClass_D5`), but its ray-exit retraction argument does not
transfer verbatim to a product `S²×D³∖{x}` (removing one point from a product does not deformation-
retract onto the boundary the way removing a point from a plain disk does — the retraction is only
literal on the `y ≠ y₀` piece of the fiber).

This module builds the two REUSABLE, fully-closed pieces that any future closing of the wall will
need, reducing the remaining obligation as far as it goes without inventing the missing
cross-product/relative-MV tool:

* §1 — **ambient acyclicity of `SphereDisk` in the two top degrees** (`H₄(S²×D³)=0`, `H₅(S²×D³)=0`),
  via the ALREADY-BANKED mod-2 contractible-factor collapse
  (`PoincareLefschetzRelFundClassCylinderNumerics.prodContractibleHomologyEquiv`, reused verbatim —
  `D³` is `SingularDiskAcyclic.Disk 3`, contractible) composed with the high-degree sphere-vanishing
  tower (`SingularSphereHighDegree.sphere_homology_high`, `4, 5 > 2`).
* §2 — **a nonzero class `β ∈ H₄(sphereDiskBoundarySet)`**: the closed-manifold mod-2 fundamental
  class of `S²×S²` (`SingularFundamentalClassExist.fundamentalClass`/`fundamentalClass_ne_zero`,
  ALREADY proven for ANY compact connected chartable manifold), transported (a) along a new
  model-vector-space chart transport `ChartedSpace (E²×E²) SphereProd → ChartedSpace E⁴ SphereProd`
  (the `fundamentalClass` API is hardwired to literal `EuclideanSpace ℝ (Fin (m+2))`, so the
  `ModelProd E² E²`-charted `SphereProd` needs one linear-equiv transport, mirroring the
  `SphereDiskJ5` associator pattern) and (b) along the compact→T2 homeomorphism
  `sphereDiskIncl : SphereProd ≃ₜ sub sphereDiskBoundarySet`.

## The precise remaining wall (reported, not faked)

`hasRelFundClass_of_acyclic_boundaryIncl` (`PinPlusTraceDiskRelFundReduce`) reduces `HasRelFundClass`
to exactly `{ambient acyclicity (§1, DONE), β ≠ 0 (§2, DONE), hincl}`, where `hincl` is injectivity of
`H₄(∂W) → H₄(W∖x)` at every interior `x`. A full Mayer–Vietoris proof sketch for `hincl` is recorded in
the module docstring below (`§3`) — it is NOT vacuous or hand-waved, but it needs a second contractible-
factor collapse in the OTHER factor slot (`S²∖{p}` contractible, keeping the `D³∖{y}` factor) plus the
already-available `SingularMayerVietorisLES.mv_exact_middle` wiring for the open cover
`A = S²×(D³∖y₀)`, `B = (S²∖p₀)×D³` of `SphereDisk∖{x}` — genuine new work beyond one turn's safe
budget, so it is reported precisely rather than forced. Even after `hincl` closes, deliverable 1 (the
`(2,3)` Wu datum) needs an ADDITIONAL, separate Lefschetz-nondegeneracy computation
(`findimAbs`/`findimRel`/`nondeg`/`dimeq` at bidegree `(2,3)`) not attempted here.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SphereProductBounding
import SKEFTHawking.SphereDiskJ5
import SKEFTHawking.SphereDiskFreezeB
import SKEFTHawking.PoincareLefschetzWu5
import SKEFTHawking.PoincareLefschetzWuAssembly
import SKEFTHawking.PoincareLefschetzRelFundClass
import SKEFTHawking.PoincareLefschetzRelFundClassGeom
import SKEFTHawking.PinPlusTraceRelFundReduce
import SKEFTHawking.PinPlusTraceDiskRelFundReduce
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
import SKEFTHawking.SingularDiskAcyclic
import SKEFTHawking.SingularSphereAcyclic
import SKEFTHawking.SingularSphereHighDegree
import SKEFTHawking.SingularFundamentalClassExist
import SKEFTHawking.PinPlusCharPairRealizationTied

open scoped Manifold
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularProdContractibleInt (ProdSp)
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics (prodContractibleHomologyEquiv)
open SKEFTHawking.SingularDiskAcyclic (Disk contraction slice_contraction_zero slice_contraction_one)
open SKEFTHawking.SingularSphereHighDegree (sphere_homology_high)
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce (εtrace)
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PinPlusCharPairRealizationTied (homeoHomologyEquiv)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots

noncomputable section

/-! ## §1. Ambient acyclicity of `SphereDisk` in degrees 4, 5. -/

/-- `SphereDisk` IS `ProdSp (TopCat.of TwoSphere) (Disk 3)` — the product topology definitionally
matches the project's contractible-factor-collapse `ProdSp`, since `Disk 3 = TopCat.of ThreeDisk`. -/
theorem sphereDisk_eq_prodSp :
    TopCat.of SphereDisk = ProdSp (TopCat.of TwoSphere) (Disk 3) := rfl

/-- **The contractible-factor collapse specialised to `SphereDisk`**: `Hₙ₊₁(S²×D³) ≅ Hₙ₊₁(S²)`, since
`D³ = Disk 3` carries the straight-line contraction to its center. -/
noncomputable def sphereDiskCollapse (n : ℕ) :
    Homology (TopCat.of SphereDisk) (n + 1) ≃ₗ[ZMod 2] Homology (TopCat.of TwoSphere) (n + 1) :=
  sphereDisk_eq_prodSp ▸
    prodContractibleHomologyEquiv (TopCat.of TwoSphere) (Disk 3) ⟨0, by simp⟩ (contraction (n := 3))
      slice_contraction_zero slice_contraction_one n

/-- `TopCat.of TwoSphere` is `SingularSphereAcyclic.Sph 2` definitionally (`Fin (2+1) = Fin 3`). -/
theorem twoSphere_eq_sph2 : TopCat.of TwoSphere = SingularSphereAcyclic.Sph 2 := rfl

/-- **`H₄(S²×D³;ℤ/2) = 0`** — ambient acyclicity in the first of the two top degrees the relative
fundamental class needs (`m = 3`, `m + 1 = 4`). Via the contractible-factor collapse to `H₄(S²)`,
which vanishes since `4 > 2` (`sphere_homology_high`). -/
theorem sphereDisk_homology_four_eq_zero (x : Homology (TopCat.of SphereDisk) 4) : x = 0 := by
  apply (sphereDiskCollapse 3).injective
  rw [map_zero]
  exact sphere_homology_high 2 4 (by norm_num) (sphereDiskCollapse 3 x)

/-- **`H₅(S²×D³;ℤ/2) = 0`** — ambient acyclicity in the second of the two top degrees
(`m = 3`, `m + 2 = 5`). Via the contractible-factor collapse to `H₅(S²)`, which vanishes since
`5 > 2`. -/
theorem sphereDisk_homology_five_eq_zero (x : Homology (TopCat.of SphereDisk) 5) : x = 0 := by
  apply (sphereDiskCollapse 4).injective
  rw [map_zero]
  exact sphere_homology_high 2 5 (by norm_num) (sphereDiskCollapse 4 x)

/-! ## §2. A nonzero class `β ∈ H₄(sphereDiskBoundarySet)`.

`fundamentalClass` is hardwired to a literal `ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M`
instance, but `SphereProd`'s Mathlib-native chart is over `ModelProd E² E² = E²×E²` (the product of
the two sphere charts). One linear-equiv model transport (mirroring `SphereDiskJ5`'s associator
pattern, but for a plain boundaryless product — no half-space factor) bridges the two. -/

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- The canonical linear equiv `E²×E² ≃L E⁴` (`EuclideanSpace.finAddEquivProd`, inverted). -/
def ε4 : (E2 × E2) ≃L[ℝ] E4 :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 2)).symm

/-- The model-space homeomorphism `ModelProd E² E² ≃ₜ E⁴` underlying `ε4`. -/
def ε4Homeo : ModelProd E2 E2 ≃ₜ E4 := ε4.toHomeomorph

/-- `ε4Homeo` as a single global chart (`OpenPartialHomeomorph`, source = univ). -/
def ε4OPH : OpenPartialHomeomorph (ModelProd E2 E2) E4 := ε4Homeo.toOpenPartialHomeomorph

/-- **`ModelProd E² E²` charted on `E⁴`** — the single global chart `ε4OPH`. -/
@[reducible] def chartedSpaceE4_ModelProd : ChartedSpace E4 (ModelProd E2 E2) where
  atlas := {ε4OPH}
  chartAt _ := ε4OPH
  mem_chart_source _ := by
    show _ ∈ ε4OPH.source
    simp [ε4OPH, Homeomorph.toOpenPartialHomeomorph]
  chart_mem_atlas _ := rfl

attribute [local instance] chartedSpaceE4_ModelProd

/-- **`SphereProd` charted on `E⁴`** — `ChartedSpace.comp` through the Mathlib-native
`ModelProd E² E²` chart (product of the two `TwoSphere` charts) and the model transport above. -/
@[reducible] noncomputable def chartedSpaceE4_SphereProd : ChartedSpace E4 SphereProd :=
  ChartedSpace.comp E4 (ModelProd E2 E2) SphereProd

attribute [local instance] chartedSpaceE4_SphereProd

/-- A basepoint of `SphereProd` (needed for `PreconnectedSpace`-free instances / `Nonempty`). -/
noncomputable def sphereProdPt : SphereProd :=
  (Classical.arbitrary TwoSphere, Classical.arbitrary TwoSphere)

/-- **The mod-2 fundamental class of `S²×S²`**, nonzero, via the closed-manifold machinery
(`SingularFundamentalClass.fundamentalClass`/`fundamentalClass_ne_zero`) at `m := 2`
(`m + 2 = 4 = dim SphereProd`), now that `SphereProd` carries a genuine `ChartedSpace E⁴` instance. -/
@[reducible] noncomputable def sphereProdFundClass : Homology (TopCat.of SphereProd) 4 :=
  @fundamentalClass 2 SphereProd _ _ _ _ chartedSpaceE4_SphereProd

theorem sphereProdFundClass_ne_zero : sphereProdFundClass ≠ 0 :=
  @fundamentalClass_ne_zero 2 SphereProd _ _ _ _ chartedSpaceE4_SphereProd sphereProdPt

/-- **`sphereDiskIncl` is a homeomorphism onto `sphereDiskBoundarySet`**: a continuous injection from
the compact `SphereProd` to the Hausdorff `SphereDisk`, corestricted to its range. -/
noncomputable def sphereDiskInclHomeo :
    (TopCat.of SphereProd : Type) ≃ₜ (sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet : Type) :=
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective sphereDiskIncl sphereDiskIncl_injective)
    (sphereDiskIncl_continuous.subtype_mk _)).trans
    (Homeomorph.setCongr range_sphereDiskIncl)

/-- **`β ∈ H₄(sphereDiskBoundarySet)`** — the `S²×S²` fundamental class transported along the
boundary-inclusion homeomorphism. -/
noncomputable def betaClass : Homology (sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet) 4 :=
  (homeoHomologyEquiv sphereDiskInclHomeo 4) sphereProdFundClass

theorem betaClass_ne_zero : betaClass ≠ 0 := by
  show (homeoHomologyEquiv sphereDiskInclHomeo 4) sphereProdFundClass ≠ 0
  rw [LinearEquiv.map_ne_zero_iff]
  exact sphereProdFundClass_ne_zero

end

end SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
