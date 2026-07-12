/-
# Phase 5q.H (N5 witness tower) — `H₁(S²×S²; ℤ) = 0` COMPUTED:
# the `SphereProdHData` freeze's first slice discharged

The `SphereProdHData` freeze (`SphereWitnessTowerInt` §4) carried `H₁(S²×S²;ℤ)` free as a FROZEN
datum because no product-homology machinery was in-tree. This module COMPUTES it: `H₁(S²×S²;ℤ) = 0`
from the in-tree integral Mayer–Vietoris LES (`SingularMayerVietorisLESInt` — complete: Δ/Σ/δ +
three exactness statements) + the contractible-factor collapse (`SingularProdContractibleInt`).
No Künneth machinery: the polar product cover does degree 1 outright.

The cover: `A = S² × (S²∖{v})`, `B = S² × (S²∖{−v})` (polar cover in the SECOND factor, full first
factor). Both legs collapse onto S² (`prodSetContractibleEquivInt` + the stereographic transport of
the straight-line contraction of ℝ², §1), so `H₁(A) = H₁(B) = H₁(S²;ℤ) = 0`
(`sphere_homology_middleInt`). The chase for `x : H₁(S²×S²)`:
* the complex condition `Δ ∘ δ = 0` (`mvHomDiagInt_mvDeltaInt`) puts `δx ∈ ker Δ₀`;
* `Δ₀` is INJECTIVE: its `A`-component is augmentation-compatible (`augHInt_naturality`) and the
  augmentation is injective on the path-connected `A∩B = S² × (S²∖{v,−v})` (§2:
  `Prod.instPathConnectedSpace` + the in-tree doubly-punctured path-connectedness through the
  `seamHomeo`/`prodSetHomeo` reassociations) — so `δx = 0`;
* exactness at `H₁(X)` (`mv_exact_ambientInt`) lifts `x = Σ(u, u')` with `u, u'` in the collapsed
  legs `H₁(A) = H₁(B) = 0`, so `x = 0`.

`sphereProd_homology_one_eq_zero` + the `Subsingleton`/`Module.Free`/`Module.Finite` instances at
`TopCat.of SphereProd` are the freeze-slice replacements `SphereWitnessTowerInt` consumes. The H₂
slice (`H₂(S²×S²;ℤ) ≅ ℤ²`) is now ALSO computed — the same polar cover one degree up
(`SphereProdHTwoInt`, consuming the slice-1+2 intersection data of `SphereProdPuncturedPlaneInt`);
the freeze residue is only the geometric factor-dual basis carrying the Gram pin (see the §4
docstring there).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularProdContractibleInt
import SKEFTHawking.SingularMayerVietorisLESInt
import SKEFTHawking.SingularSphereMiddleInt
import SKEFTHawking.SphereProductBounding

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularSphereAcyclic (Sph Apunc puncturedHomeo antipode ne_antipode)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl contraction slice_contraction_zero
  slice_contraction_one)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularSphereMiddle (restr_doubly_punctured_pathConnected)
open SKEFTHawking.SingularSphereMiddleInt (sphere_homology_middleInt)
open SKEFTHawking.SingularH0PathConnectedInt (augHInt_injective_pathConnected)
open SKEFTHawking.SingularLineMinusPointInt (augHInt augHInt_naturality)
open SKEFTHawking.SingularSphereBottom (basePoint)
open SKEFTHawking.SingularMayerVietorisLES (seamHomeo subIncl ambIncl)
open SKEFTHawking.SpinSigmaRoute (SphereProd)

namespace SKEFTHawking.SphereProdHOneInt

/-! ## §1. The punctured-sphere contraction (stereographic transport) -/

/-- **The contraction of the punctured sphere `Sⁿ∖{v}`**: the straight-line contraction of `ℝⁿ`
transported backwards across the stereographic homeomorphism `puncturedHomeo n v`. -/
noncomputable def puncContraction (n : ℕ) (v : ↑(Sph n)) :
    C(↑(Apunc n v) × unitInterval, ↑(Apunc n v)) :=
  homeoContraction (X := Apunc n v) (Z := Eucl n) (puncturedHomeo n v) (contraction n)

theorem slice_puncContraction_zero (n : ℕ) (v : ↑(Sph n)) :
    slice (puncContraction n v) 0 = ContinuousMap.id ↑(Apunc n v) :=
  slice_homeoContraction_zero _ _ (slice_contraction_zero n)

theorem slice_puncContraction_one (n : ℕ) (v : ↑(Sph n)) :
    slice (puncContraction n v) 1
      = ContinuousMap.const ↑(Apunc n v) ((puncturedHomeo n v).symm 0) :=
  slice_homeoContraction_one _ _ _ (slice_contraction_one n)

/-! ## §2. The polar product cover of S²×S² and its path-connected intersection -/

/-- The `A`-leg of the polar product cover: `S² × (S²∖{v})` (full first factor). -/
abbrev coverA (v : ↑(Sph 2)) : Set ↑(ProdSp (Sph 2) (Sph 2)) :=
  (Set.univ : Set ↑(Sph 2)) ×ˢ ({v}ᶜ : Set ↑(Sph 2))

/-- The `B`-leg of the polar product cover: `S² × (S²∖{−v})`. -/
abbrev coverB (v : ↑(Sph 2)) : Set ↑(ProdSp (Sph 2) (Sph 2)) :=
  (Set.univ : Set ↑(Sph 2)) ×ˢ ({antipode v}ᶜ : Set ↑(Sph 2))

/-- The polar product cover is an interior cover of `S²×S²` (both legs open; the second factors'
complements of `v ≠ −v` exhaust the sphere). -/
theorem coverAB_cover (v : ↑(Sph 2)) :
    (⋃ U ∈ ({coverA v, coverB v} : Set (Set ↑(ProdSp (Sph 2) (Sph 2)))), interior U)
      = Set.univ := by
  have hA : IsOpen (coverA v) := isOpen_univ.prod isOpen_compl_singleton
  have hB : IsOpen (coverB v) := isOpen_univ.prod isOpen_compl_singleton
  rw [Set.biUnion_pair, hA.interior_eq, hB.interior_eq, ← Set.prod_union, ← Set.compl_inter,
    Set.eq_univ_iff_forall]
  intro x
  refine Set.mem_prod.mpr ⟨Set.mem_univ _, ?_⟩
  rw [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_singleton_iff]
  rintro ⟨rfl, h2⟩
  exact ne_antipode _ h2

/-- The cover legs intersect in `S² × (S²∖{v,−v})` (product-set intersection reassociation). -/
theorem coverAB_inter (v : ↑(Sph 2)) :
    coverA v ∩ coverB v
      = (Set.univ : Set ↑(Sph 2)) ×ˢ (({v}ᶜ : Set ↑(Sph 2)) ∩ ({antipode v}ᶜ)) := by
  rw [Set.prod_inter_prod, Set.univ_inter]

/-- **Path-connectedness transports across a homeomorphism** (image of the universal path-connected
set under the continuous surjection). -/
theorem pathConnectedSpace_of_homeo {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (φ : α ≃ₜ β) [PathConnectedSpace α] : PathConnectedSpace β := by
  rw [pathConnectedSpace_iff_univ]
  have h := (pathConnectedSpace_iff_univ.mp ‹_›).image φ.continuous
  rwa [Set.image_univ, Set.range_eq_univ.mpr φ.surjective] at h

/-- **A product of path-connected spaces is path-connected** (pointwise `Path.prod`; the pinned
Mathlib has no product `PathConnectedSpace` instance). -/
theorem pathConnectedSpace_prod {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [PathConnectedSpace α] [PathConnectedSpace β] : PathConnectedSpace (α × β) where
  nonempty := ⟨((PathConnectedSpace.nonempty (X := α)).some,
    (PathConnectedSpace.nonempty (X := β)).some)⟩
  joined p q :=
    ⟨(PathConnectedSpace.joined p.1 q.1).somePath.prod (PathConnectedSpace.joined p.2 q.2).somePath⟩

/-- The 2-sphere is path-connected (`rank ℝ ℝ³ = 3 > 1`). -/
theorem pathConnectedSpace_sphere2 : PathConnectedSpace ↑(Sph 2) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
    rw [← Module.finrank_eq_rank, hfr]
    exact_mod_cast (by norm_num : (1 : ℕ) < 3)
  exact isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere hrank 0 zero_le_one)

/-- The doubly-punctured 2-sphere subtype is path-connected (the in-tree `restr`-form result,
reassociated across `seamHomeo`). -/
theorem pathConnectedSpace_doublyPunctured (v : ↑(Sph 2)) :
    PathConnectedSpace ↥(sub (({v}ᶜ : Set ↑(Sph 2)) ∩ ({antipode v}ᶜ))) := by
  haveI : PathConnectedSpace ↥(sub (restr ({v}ᶜ : Set ↑(Sph 2)) ({antipode v}ᶜ))) :=
    isPathConnected_iff_pathConnectedSpace.mp (restr_doubly_punctured_pathConnected 2 le_rfl v)
  exact pathConnectedSpace_of_homeo (seamHomeo ({v}ᶜ : Set ↑(Sph 2)) ({antipode v}ᶜ))

/-- **The cover intersection `S² × (S²∖{v,−v})` is path-connected**: product of the path-connected
sphere with the path-connected doubly-punctured sphere, reassociated across `prodSetHomeo`. -/
theorem pathConnectedSpace_coverAB_inter (v : ↑(Sph 2)) :
    PathConnectedSpace ↥(sub (coverA v ∩ coverB v)) := by
  haveI : PathConnectedSpace (↑(Sph 2) × ↥(({v}ᶜ : Set ↑(Sph 2)) ∩ ({antipode v}ᶜ))) :=
    @pathConnectedSpace_prod _ _ _ _ pathConnectedSpace_sphere2
      (pathConnectedSpace_doublyPunctured v)
  haveI : PathConnectedSpace
      ↥(sub (X := ProdSp (Sph 2) (Sph 2))
        ((Set.univ : Set ↑(Sph 2)) ×ˢ (({v}ᶜ : Set ↑(Sph 2)) ∩ ({antipode v}ᶜ)))) :=
    pathConnectedSpace_of_homeo
      (α := ↑(Sph 2) × ↥(({v}ᶜ : Set ↑(Sph 2)) ∩ ({antipode v}ᶜ)))
      (prodSetHomeo (Sph 2) (Sph 2) (({v}ᶜ : Set ↑(Sph 2)) ∩ ({antipode v}ᶜ))).symm
  rw [coverAB_inter v]
  exact ‹_›

/-! ## §3. The MV legs collapse: `H₁(A) = H₁(B) = 0` -/

/-- `H₁(S² × (S²∖{v}); ℤ) = 0`: the leg collapses onto `H₁(S²;ℤ) = 0` through the
contractible-factor equivalence (stereographic contraction of the punctured second factor). -/
theorem coverA_homology_one_eq_zero (v : ↑(Sph 2)) (u : Homology (sub (coverA v)) 1) :
    u = 0 := by
  have e := prodSetContractibleEquivInt (Sph 2) (Sph 2) ({v}ᶜ : Set ↑(Sph 2))
    ((puncturedHomeo 2 v).symm 0) (puncContraction 2 v)
    (slice_puncContraction_zero 2 v) (slice_puncContraction_one 2 v) 0
  exact e.map_eq_zero_iff.mp (sphere_homology_middleInt 1 2 one_pos one_lt_two (e u))

/-- `H₁(S² × (S²∖{−v}); ℤ) = 0` — the `B`-leg, same collapse at the antipode. -/
theorem coverB_homology_one_eq_zero (v : ↑(Sph 2)) (u : Homology (sub (coverB v)) 1) :
    u = 0 := by
  have e := prodSetContractibleEquivInt (Sph 2) (Sph 2) ({antipode v}ᶜ : Set ↑(Sph 2))
    ((puncturedHomeo 2 (antipode v)).symm 0) (puncContraction 2 (antipode v))
    (slice_puncContraction_zero 2 (antipode v)) (slice_puncContraction_one 2 (antipode v)) 0
  exact e.map_eq_zero_iff.mp (sphere_homology_middleInt 1 2 one_pos one_lt_two (e u))

/-! ## §4. `H₁(S²×S²;ℤ) = 0` — the Mayer–Vietoris chase -/

/-- **`H₁(S²×S²;ℤ) = 0`.** The polar product cover's MV chase: `δx` dies against the injective
`Δ₀` (augmentation naturality + path-connected intersection), so exactness at `H₁(X)` lifts `x`
to the collapsed legs `H₁(A) = H₁(B) = 0`. The `SphereProdHData` freeze's first slice, COMPUTED. -/
theorem sphereProd_homology_one_eq_zero (x : Homology (ProdSp (Sph 2) (Sph 2)) 1) : x = 0 := by
  set v : ↑(Sph 2) := basePoint 2 with hv
  have hcov := coverAB_cover v
  -- Step 1: δx = 0 (Δ₀ ∘ δ = 0 and Δ₀'s A-component is injective via augmentation).
  have hδ : mvDeltaInt (coverA v) (coverB v) 0 hcov x = 0 := by
    have hdiag := mvHomDiagInt_mvDeltaInt (coverA v) (coverB v) 0 hcov x
    have hfst : Homology.mapInt
        (subIncl (Set.inter_subset_left (s := coverA v) (t := coverB v))) 0
        (mvDeltaInt (coverA v) (coverB v) 0 hcov x) = 0 := congrArg Prod.fst hdiag
    haveI := pathConnectedSpace_coverAB_inter v
    apply augHInt_injective_pathConnected (X := sub (coverA v ∩ coverB v))
    rw [map_zero,
      ← augHInt_naturality (subIncl (Set.inter_subset_left (s := coverA v) (t := coverB v)))
        (mvDeltaInt (coverA v) (coverB v) 0 hcov x),
      hfst, map_zero]
  -- Step 2: exactness at H₁(X) lifts x to the legs, both of which vanish.
  obtain ⟨⟨u, u'⟩, hx⟩ := (mv_exact_ambientInt (coverA v) (coverB v) 0 hcov x).mp hδ
  rw [← hx, mvHomSumInt_apply, coverA_homology_one_eq_zero v u,
    coverB_homology_one_eq_zero v u', map_zero, map_zero, sub_zero]

/-! ## §5. The freeze-slice replacement instances at `SphereProd` -/

/-- The witness tower's carrier `TopCat.of SphereProd` IS the product-space object the MV chase
ran on (definitional; `SphereProd = TwoSphere × TwoSphere` with `TwoSphere = ↑(Sph 2)`). -/
example : TopCat.of SphereProd = ProdSp (Sph 2) (Sph 2) := rfl

/-- **`H₁(S²×S²;ℤ) = 0` — as an instance at the witness tower's carrier.** Replaces the
`SphereProdHData.free1` frozen field. -/
instance : Subsingleton (Homology (TopCat.of SphereProd) 1) :=
  subsingleton_of_forall_eq 0 fun x => sphereProd_homology_one_eq_zero x

/-- The σ÷16 leg's `[Module.Free ℤ H₁]` obligation at S²×S² (the `Ext = 0` input): `H₁ = 0` is
free — now COMPUTED, no longer frozen. -/
instance : Module.Free ℤ (Homology (TopCat.of SphereProd) 1) :=
  Module.Free.of_subsingleton ℤ _

end SKEFTHawking.SphereProdHOneInt
