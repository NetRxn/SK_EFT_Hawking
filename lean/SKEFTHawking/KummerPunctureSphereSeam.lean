/-
# Phase 5q.H — the seam relation in the SPHERE coordinates of `T⁴°` (the covering's coordinates)

`KummerPunctureSeamRelation.exists_nonzero_seam_relation` proved, unconditionally, that the sixteen
seam classes of the puncture Mayer–Vietoris cover satisfy a nontrivial ℤ-linear relation — but in
the coordinates of the sixteen closed chart **annuli** `annPiece c ⊆ thickA ∩ ballsV`. The annuli do
NOT lie in the punctured torus `T⁴° = (⋃ chartBall)ᶜ` (only their outer faces do), so the free `ℤ/2`
covering `T⁴° ↠ Q` cannot see them, and the relation is unusable for the `Q`-side transport.

This module moves the relation onto the sixteen **boundary spheres**

    σ_c : S³ → T⁴°,   a ↦ centeredChartParam c (scaleToChart a)

— the round `S³` at chart radius `ρ = 1/2` — which is exactly the map the weld's `Q`-side seam
identification `KummerWeld.s3ToQ` is built from (`s3ToQ c = qmk ∘ σ_c`, definitionally). So the
relation produced here lives in the coordinates in which the covering acts.

## The geometric identification (a): `chartSphere c` IS the outer face of `annPiece c`

`excisionRadius = 1/2`, `chartSphere c = centeredChartParam c '' {sqNorm = 1/4}` and
`ann4 = {1/16 ≤ sqNorm ≤ 1/4}`, so `sqNorm (scaleToChart a) = 1/4` puts `σ_c a` on the outer face of
the `c`-th annulus. §1 records this as the two continuous maps `sphToInter c` / `sphToPT c` and §2
the square that identifies them through `KummerPuncturedMV.puncInclC`.

## The coordinate computation (§3)

Pushing an `H₃(S³;ℤ)` class into the `c`-th annulus and reading the banked coordinatisation
`KummerPunctureH3.interH3EquivEIndex` gives `Pi.single c (sphCoef g)` for a **single** integer
functional `sphCoef` that does not depend on `c` (the chart is the same in every copy). That the
common factor `sphCoef g` may a priori be any integer costs nothing: it rides along as an overall
scalar and is absorbed by the relation.

## Headline (§4)

    exists_nonzero_sphere_seam_relation :
      ∃ v ≠ 0, ∑ c, v c • Homology.mapInt (sphToPT c) 3 s3Gen = 0   in `H₃(T⁴°;ℤ)`

— the sixteen boundary `S³` classes of the punctured torus are ℤ-linearly dependent, stated on the
covering space itself. `KummerPuncturedMV.puncIncl_mapInt_bijective` (the banked
`T⁴° ↪ thickA` homotopy equivalence) is what carries the `thickA`-side relation across.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerPunctureSeamRelation
import SKEFTHawking.KummerK7H1Window
import SKEFTHawking.KummerRP3SphereHomeo
import SKEFTHawking.KummerQuotientCovering

namespace SKEFTHawking.KummerPunctureSphereSeam

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt Homology.mapInt_comp)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (subIncl)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (homologyCongrInt)
open SKEFTHawking.SingularFiniteProdSingleInt (homologyCongrInt_apply)
open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerPuncturedTorus (centeredChartParam continuous_centeredChartParam sqNorm
  chartSphere sphere_subset_puncturedTorus excisionRadius)
open SKEFTHawking.KummerPunctureBalls (ann4 thickA ballsV annPiece annPiece_subset_inter
  interSplitHomeo interEquiv excisionRadius_sq)
open SKEFTHawking.KummerPuncturedMV (puncInclC puncIncl_mapInt_bijective)
open SKEFTHawking.KummerPunctureH3 (ann4H3Equiv interH3EquivEIndex)
open SKEFTHawking.KummerPunctureSeamRelation (seamToThick3 thickSeamCoord3
  exists_nonzero_seam_relation)
open SKEFTHawking.KummerResolutionPiece (S3)
open SKEFTHawking.KummerRP3Covering (S3top)
open SKEFTHawking.KummerRP3SphereHomeo (s3H3EquivInt)
open SKEFTHawking.KummerWeld (EIndex eIndex_fixedSet scaleToChart sqNorm_scaleToChart
  continuous_scaleToChart)
open SKEFTHawking.KummerK7MVAssembly (eIndexProdHnEquivIntGen)
open SKEFTHawking.KummerK7H1Window (genInclC eIndexProdHnEquivIntGen_mapInt_single)
open scoped SKEFTHawking.KummerK7H1Window
open SKEFTHawking.KummerQuotientCovering (PTtop)

noncomputable section

/-! ## §1. The boundary sphere as the outer face of the chart annulus -/

/-- **The scaled `S³` lands on the outer face of the chart annulus**: `sqNorm = ρ² = 1/4`, which is
the upper endpoint of `ann4 = {1/16 ≤ sqNorm ≤ 1/4}`. This is the geometric identification the
transport needs — `chartSphere c` IS the outer face of `annPiece c`. -/
theorem scaleToChart_mem_ann4 (a : S3) : scaleToChart a ∈ ann4 := by
  have h : sqNorm (scaleToChart a) = 1 / 4 := by
    rw [sqNorm_scaleToChart, excisionRadius_sq]
  refine ⟨?_, h.le⟩
  rw [h]
  norm_num

/-- The parametrised chart annulus point of `a : S³` (its outer face). -/
def sphC : C(↑S3top, ↑(TopCat.of ↥ann4)) :=
  ⟨fun a => ⟨scaleToChart a, scaleToChart_mem_ann4 a⟩,
    continuous_scaleToChart.subtype_mk _⟩

/-- **The `c`-th boundary sphere, into the MV seam** `thickA ∩ ballsV`. -/
def sphToInter (c : EIndex) :
    C(↑S3top, ↑(sub (X := TopCat.of TorusFour) (thickA ∩ ballsV))) :=
  ⟨fun a => ⟨centeredChartParam c.1 (scaleToChart a),
      annPiece_subset_inter (eIndex_fixedSet c) ⟨scaleToChart a, scaleToChart_mem_ann4 a, rfl⟩⟩,
    (((continuous_centeredChartParam c.1).comp continuous_scaleToChart)).subtype_mk _⟩

/-- **The `c`-th boundary sphere, into the punctured torus** — the map the covering `T⁴° ↠ Q` acts
on, and (definitionally) the one `KummerWeld.s3ToQ` composes with `qmk`. -/
def sphToPT (c : EIndex) : C(↑S3top, ↑PTtop) :=
  ⟨fun a => ⟨centeredChartParam c.1 (scaleToChart a),
      sphere_subset_puncturedTorus (eIndex_fixedSet c)
        ⟨scaleToChart a, sqNorm_scaleToChart a, rfl⟩⟩,
    (((continuous_centeredChartParam c.1).comp continuous_scaleToChart)).subtype_mk _⟩

/-! ## §2. The two squares -/

/-- **The seam splitter square**: reading the `c`-th boundary sphere through the 16-fold splitter
`interSplitHomeo` gives the `c`-th copy of the annulus parametrisation. -/
theorem interSplit_comp_sphToInter (c : EIndex) :
    (⟨interSplitHomeo.symm, interSplitHomeo.symm.continuous⟩ :
        C(↑(sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)), EIndex × ↥ann4)).comp
      (sphToInter c)
      = (genInclC (TopCat.of ↥ann4) c).comp sphC := by
  refine ContinuousMap.ext fun a => ?_
  show interSplitHomeo.symm _ = (c, (⟨scaleToChart a, scaleToChart_mem_ann4 a⟩ : ↥ann4))
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext rfl

/-- **The thickening square**: the `c`-th boundary sphere reaches `thickA` either through the seam
or through the punctured torus, by the same underlying map. -/
theorem seamIncl_comp_sphToInter (c : EIndex) :
    (subIncl (Set.inter_subset_left (s := thickA) (t := ballsV))).comp (sphToInter c)
      = puncInclC.comp (sphToPT c) :=
  ContinuousMap.ext fun _ => Subtype.ext rfl

/-! ## §3. The coordinate computation -/

/-- **The common integer coefficient** of a top `S³`-class in the annulus coordinatisation. It does
not depend on the copy `c` — the chart annulus is the same in every copy. -/
def sphCoef : Homology S3top 3 →ₗ[ℤ] ℤ :=
  ann4H3Equiv.toLinearMap ∘ₗ Homology.mapInt sphC 3

/-- Pushing a `Pi.single` through a family of linear maps. -/
theorem piCongrRight_single {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] (e : M ≃ₗ[ℤ] N) (c : EIndex) (z : M) :
    (fun d : EIndex => e ((Pi.single c z : EIndex → M) d)) = Pi.single c (e z) := by
  funext d
  rcases eq_or_ne d c with rfl | hne
  · rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne, map_zero]

/-- **THE SEAM COORDINATE OF A BOUNDARY SPHERE CLASS.** Pushing `g ∈ H₃(S³;ℤ)` into the `c`-th
annulus and reading the banked sixteen-fold coordinatisation gives `Pi.single c (sphCoef g)`. -/
theorem interH3EquivEIndex_sphToInter (c : EIndex) (g : Homology S3top 3) :
    interH3EquivEIndex (Homology.mapInt (sphToInter c) 3 g) = Pi.single c (sphCoef g) := by
  have hcong : (homologyCongrInt (X := sub (X := TopCat.of TorusFour) (thickA ∩ ballsV))
      (Y := TopCat.of (EIndex × ↥ann4)) interSplitHomeo.symm 3)
        (Homology.mapInt (sphToInter c) 3 g)
      = Homology.mapInt (X := TopCat.of ↥ann4) (Y := TopCat.of (EIndex × ↥ann4))
          (genInclC (TopCat.of ↥ann4) c) 3 (Homology.mapInt sphC 3 g) := by
    rw [homologyCongrInt_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← Homology.mapInt_comp, ← Homology.mapInt_comp, interSplit_comp_sphToInter]
  rw [interH3EquivEIndex, LinearEquiv.trans_apply,
    SKEFTHawking.KummerPuncturedMV.interHnEquiv, LinearEquiv.trans_apply, hcong,
    eIndexProdHnEquivIntGen_mapInt_single]
  exact piCongrRight_single ann4H3Equiv c _

/-- **The seam map on a boundary-sphere coordinate vector** is the punctured-torus class of that
boundary sphere, pushed into `thickA`. -/
theorem thickSeamCoord3_single (c : EIndex) (g : Homology S3top 3) :
    thickSeamCoord3 (Pi.single c (sphCoef g))
      = Homology.mapInt puncInclC 3 (Homology.mapInt (sphToPT c) 3 g) := by
  have h : thickSeamCoord3 (Pi.single c (sphCoef g))
      = seamToThick3 (Homology.mapInt (sphToInter c) 3 g) := by
    show seamToThick3 (interH3EquivEIndex.symm (Pi.single c (sphCoef g))) = _
    rw [← interH3EquivEIndex_sphToInter c g, interH3EquivEIndex.symm_apply_apply]
  rw [h]
  show (Homology.mapInt (subIncl (Set.inter_subset_left (s := thickA) (t := ballsV))) 3)
      (Homology.mapInt (sphToInter c) 3 g) = _
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
    ← Homology.mapInt_comp, seamIncl_comp_sphToInter]

/-! ## §4. The relation, in the sphere coordinates -/

/-- The `ℤ`-generator of `H₃(S³;ℤ)` picked out by the banked coordinatisation. -/
def s3Gen : Homology S3top 3 := s3H3EquivInt.symm 1

/-- **`s3Gen ≠ 0`.** -/
theorem s3Gen_ne_zero : s3Gen ≠ 0 := by
  intro h
  have h2 : s3H3EquivInt s3Gen = 0 := by rw [h, map_zero]
  simp only [s3Gen, LinearEquiv.apply_symm_apply] at h2
  exact one_ne_zero h2

/-- Scaling a coordinate vector is the sum of its `Pi.single` pieces. -/
theorem smul_eq_sum_single (d : ℤ) (v : EIndex → ℤ) :
    d • v = ∑ c : EIndex, v c • (Pi.single c d : EIndex → ℤ) := by
  classical
  funext e
  rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single e]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_comm]
  · intro b _ hb
    rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hb h.symm), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ e) h

/-- **THE SIXTEEN BOUNDARY `S³` CLASSES OF `T⁴°` ARE ℤ-LINEARLY DEPENDENT, IN THE PUNCTURED TORUS
ITSELF — UNCONDITIONALLY.**

There is a nonzero `v ∈ ℤ¹⁶` with `∑ c, v c • [σ_c]₃ = 0` in `H₃(T⁴°;ℤ)`, where `σ_c : S³ → T⁴°` is
the `c`-th round boundary sphere at chart radius `ρ = 1/2`.

This is `KummerPunctureSeamRelation.exists_nonzero_seam_relation` transported off the annuli and
onto the boundary spheres, using the banked homotopy equivalence `T⁴° ↪ thickA`
(`KummerPuncturedMV.puncIncl_mapInt_bijective`) and §3's coordinate computation. Unlike the annulus
form, this statement lives on the covering space of `Q`, so the free `ℤ/2` covering can transport
it. -/
theorem exists_nonzero_sphere_seam_relation :
    ∃ v : EIndex → ℤ, v ≠ 0 ∧
      ∑ c : EIndex, v c • Homology.mapInt (sphToPT c) 3 s3Gen = 0 := by
  classical
  obtain ⟨v, hv, h0⟩ := exists_nonzero_seam_relation
  refine ⟨v, hv, ?_⟩
  -- The `thickA`-side relation, scaled by the common annulus coefficient.
  have hscaled : thickSeamCoord3 (sphCoef s3Gen • v) = 0 := by
    rw [map_smul, h0, smul_zero]
  -- The same vector, expanded over the sixteen boundary spheres.
  have hexp : thickSeamCoord3 (sphCoef s3Gen • v)
      = Homology.mapInt puncInclC 3
        (∑ c : EIndex, v c • Homology.mapInt (sphToPT c) 3 s3Gen) := by
    rw [smul_eq_sum_single, map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, map_smul, thickSeamCoord3_single]
  rw [hexp] at hscaled
  exact (injective_iff_map_eq_zero _).mp (puncIncl_mapInt_bijective 2).1 _ hscaled

end

end SKEFTHawking.KummerPunctureSphereSeam
