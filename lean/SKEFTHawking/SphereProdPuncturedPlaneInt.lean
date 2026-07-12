/-
# Phase 5q.H (N5 witness tower) — `H_{≤2}(S² × (ℝ²∖{0}); ℤ)` via the slit-plane Mayer–Vietoris

Arc-map slice 1 of the `SphereProdHData` H₂ residue: the S²×S² polar-cover intersection carries the
factor `S²∖{v,−v} ≃ₜ ℝ²∖{0}` (`SphereDoublyPuncturedPlane`), so the H₂ slice's `H_{≤2}(S²×S¹)`-grade
input is the homology of `S² × (ℝ²∖{0})`. This module COMPUTES it, running the integral MV LES
(`SingularMayerVietorisLESInt`) over `SlitProd := S² × (ℝ²∖{0})` under the slit-plane polar cover
(`SingularStarConvexSlit`) lifted to the product:

* legs `legUp/legDown = S² × (slit plane)`: each slit plane is star-convex, so the legs collapse
  onto `H(S²)` (`starConvexContraction` transported through the subtype seam + the
  contractible-factor collapse `prodSetContractibleEquivInt`);
* intersection `legUp ∩ legDown = S² × {x₀ ≠ 0}`: the two convex half-plane components split by the
  every-degree clopen splitting (`splitHIntEquiv`) and each half collapses onto `H(S²)` — the
  S⁰-shape `H(A∩B) ≅ H(S²)²`;
* **`H₁(S²×(ℝ²∖{0});ℤ) ≅ ℤ`** (`slitProdHOneEquivInt`): exactness at `H₀(A∩B)` — the δ-image is
  `ker Δ₀ = the anti-diagonal` of `H₀ ≅ ℤ²` through the augmentation isos (`augHInt` injective on
  each path-connected piece, surjective at a point, additive across the split);
* **`H₂(S²×(ℝ²∖{0});ℤ) ≅ ℤ`** (`slitProdHTwoEquivInt`): `H₁(A∩B) = 0` makes `Σ₂` surjective, and
  middle exactness computes `ker Σ₂ = im Δ₂ = the diagonal` of `H₂(A∩B) ≅ H₂(S²)²` — the ℤ²/diagonal
  bookkeeping (`interDiag_fst_coords`/`interDiag_snd_coords`). The generator bookkeeping export for
  slice 3: the quotient is realized by the FIRST-FACTOR projection —
  `prodFst_homology_two_bijective : H₂(S²×(ℝ²∖{0})) ≅ H₂(S²)` via `Homology.mapInt (prodFst …) 2`,
  so the surviving H₂ class IS the S² top class, canonically (`slitProdHTwoViaFst` + `topSphereIsoInt 1`).
* Slice 2 (the transport): `interProdHomeo v : sub (coverA v ∩ coverB v) ≃ₜ SlitProd` carries both
  computations to the S²×S² polar-cover intersection (`coverInterHOneEquivInt`/`coverInterHTwoEquivInt`);
  it is first-coordinate-preserving (`interProdHomeo_fst`), so slice 3's Δ-bookkeeping reduces to
  first-factor projections.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularProdContractibleInt
import SKEFTHawking.SingularMayerVietorisLESInt
import SKEFTHawking.SingularClopenSplitInt
import SKEFTHawking.SingularStarConvexSlit
import SKEFTHawking.SingularSphereMiddleInt
import SKEFTHawking.SphereProdHOneInt
import SKEFTHawking.SphereDoublyPuncturedPlane

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.SingularClopenSplitInt
open SKEFTHawking.SingularStarConvexSlit
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularHomotopyInvariance (slice constSimplex)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularSphereMiddleInt (sphere_homology_middleInt)
open SKEFTHawking.SingularH0PathConnectedInt (augHInt_injective_pathConnected)
open SKEFTHawking.SingularLineMinusPointInt (augHInt augHInt_naturality augHInt_surjective
  augHInt_homIncl augHInt_splitH0Int splitH0Int splitH0IntEquiv topSphereIsoInt)
open SKEFTHawking.SingularSphereBottom (basePoint)
open SKEFTHawking.SingularMayerVietorisLES (seamHomeo subIncl ambIncl)
open SKEFTHawking.SphereProdHOneInt (pathConnectedSpace_of_homeo pathConnectedSpace_prod
  pathConnectedSpace_sphere2 coverA coverB coverAB_inter)
open SKEFTHawking.SphereDoublyPuncturedPlane (doublyPuncturedSphereHomeo)
open SKEFTHawking.SingularSphereAcyclic (antipode)

namespace SKEFTHawking.SphereProdPuncturedPlaneInt

/-! ## §0. The spaces: the punctured plane and `S² × (ℝ²∖{0})` -/

/-- The puncture-complement `ℝ²∖{0}` as a set (local shorthand fixing every elaboration pin). -/
abbrev punc : Set (EuclideanSpace ℝ (Fin 2)) := ({0} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ

/-- The punctured plane `ℝ²∖{0}` as a subspace object of `ℝ²`. -/
abbrev PuncPlane : TopCat := sub (X := Eucl 2) punc

/-- `S² × (ℝ²∖{0})` — the slice-1 carrier (the S²×S² polar-cover intersection, up to the
`doublyPuncturedSphereHomeo` transport of slice 2). -/
abbrev SlitProd : TopCat := ProdSp (Sph 2) PuncPlane

/-! ## §1. The slit sets sit inside the punctured plane -/

theorem slitUp_subset_punc : slitUp ⊆ punc := by
  intro x hx
  rintro rfl
  exact hx ⟨rfl, le_of_eq rfl⟩

theorem slitDown_subset_punc : slitDown ⊆ punc := by
  intro x hx
  rintro rfl
  exact hx ⟨rfl, le_of_eq rfl⟩

theorem posHalf_subset_punc : posHalf ⊆ punc := by
  intro x hx
  rintro rfl
  have h : (0 : ℝ) < (0 : EuclideanSpace ℝ (Fin 2)) 0 := hx
  simp at h

theorem negHalf_subset_punc : negHalf ⊆ punc := by
  intro x hx
  rintro rfl
  have h : (0 : EuclideanSpace ℝ (Fin 2)) 0 < 0 := hx
  simp at h

theorem posHalf_subset_slitUp : posHalf ⊆ slitUp := fun _ hx hray => ne_of_gt hx hray.1
theorem posHalf_subset_slitDown : posHalf ⊆ slitDown := fun _ hx hray => ne_of_gt hx hray.1
theorem negHalf_subset_slitUp : negHalf ⊆ slitUp := fun _ hx hray => ne_of_lt hx hray.1
theorem negHalf_subset_slitDown : negHalf ⊆ slitDown := fun _ hx hray => ne_of_lt hx hray.1

/-! ## §2. The generic leg package: star-convex `S ⊆ ℝ²∖{0}` lifts to a collapsing product leg

For every star-convex `S ⊆ ℝ²∖{0}` (the two slit planes and the two half planes), the product set
`univ ×ˢ (restr S punc) ⊆ S²×(ℝ²∖{0})` carries: a transported contraction of its second factor, the
homology collapse onto `H(S²)` in positive degrees, and path-connectedness. -/

section GenericLeg

variable {S : Set (EuclideanSpace ℝ (Fin 2))} {p₀ : EuclideanSpace ℝ (Fin 2)}

/-- The subtype-of-subtype flattener: `S` viewed inside the punctured plane IS `S`
(`seamHomeo` + the set identity `S ∩ punc = S`). -/
noncomputable def flatHomeo (hS : S ⊆ punc) :
    ↥(sub (restr (X := Eucl 2) S punc)) ≃ₜ ↥(sub (X := Eucl 2) S) :=
  (seamHomeo (X := Eucl 2) S punc).trans
    (Homeomorph.setCongr (Set.inter_eq_self_of_subset_left hS))

/-- The star-convex straight-line contraction transported to the punctured-plane subtype
representation `sub (restr S punc)`. -/
noncomputable def restrContraction (hS : S ⊆ punc) (hstar : StarConvex ℝ p₀ S) :
    C(↥(sub (restr (X := Eucl 2) S punc)) × unitInterval,
      ↥(sub (restr (X := Eucl 2) S punc))) :=
  homeoContraction (X := sub (restr (X := Eucl 2) S punc))
    (Z := sub (X := Eucl 2) S) (flatHomeo hS) (starConvexContraction hstar)

theorem slice_restrContraction_zero (hS : S ⊆ punc) (hstar : StarConvex ℝ p₀ S) :
    slice (restrContraction hS hstar) 0
      = ContinuousMap.id ↥(sub (restr (X := Eucl 2) S punc)) :=
  slice_homeoContraction_zero _ _ (slice_starConvexContraction_zero hstar)

theorem slice_restrContraction_one (hS : S ⊆ punc) (hstar : StarConvex ℝ p₀ S) (hp₀ : p₀ ∈ S) :
    slice (restrContraction hS hstar) 1
      = ContinuousMap.const ↥(sub (restr (X := Eucl 2) S punc))
          ((flatHomeo hS).symm ⟨p₀, hp₀⟩) :=
  slice_homeoContraction_one _ _ _ (slice_starConvexContraction_one hstar hp₀)

/-- **The generic leg collapse** `Hₙ₊₁(S² × S; ℤ) ≅ Hₙ₊₁(S²; ℤ)` for star-convex `S ⊆ ℝ²∖{0}`,
in the product-subset representation the MV cover consumes. -/
noncomputable def legEquivInt (hS : S ⊆ punc) (hstar : StarConvex ℝ p₀ S) (hp₀ : p₀ ∈ S) (n : ℕ) :
    Homology (sub (X := SlitProd)
        ((Set.univ : Set ↑(Sph 2)) ×ˢ (restr (X := Eucl 2) S punc))) (n + 1)
      ≃ₗ[ℤ] Homology (Sph 2) (n + 1) :=
  prodSetContractibleEquivInt (Sph 2) PuncPlane (restr (X := Eucl 2) S punc)
    ((flatHomeo hS).symm ⟨p₀, hp₀⟩) (restrContraction hS hstar)
    (slice_restrContraction_zero hS hstar) (slice_restrContraction_one hS hstar hp₀) n

/-- **The generic leg is path-connected**: `S² × S` for star-convex `S`, in the product-subset
representation (`prodSetHomeo` + the flattener + `pathConnectedSpace_prod`). -/
theorem legPathConnected (hS : S ⊆ punc) (hstar : StarConvex ℝ p₀ S) (hp₀ : p₀ ∈ S) :
    PathConnectedSpace ↥(sub (X := SlitProd)
      ((Set.univ : Set ↑(Sph 2)) ×ˢ (restr (X := Eucl 2) S punc))) := by
  haveI hPS : PathConnectedSpace ↥(sub (X := Eucl 2) S) :=
    isPathConnected_iff_pathConnectedSpace.mp (hstar.isPathConnected hp₀)
  haveI : PathConnectedSpace ↥(sub (restr (X := Eucl 2) S punc)) :=
    pathConnectedSpace_of_homeo (flatHomeo hS).symm
  haveI : PathConnectedSpace (↑(Sph 2) × ↥(sub (restr (X := Eucl 2) S punc))) :=
    @pathConnectedSpace_prod _ _ _ _ pathConnectedSpace_sphere2 ‹_›
  exact pathConnectedSpace_of_homeo
    (prodSetHomeo (Sph 2) PuncPlane (restr (X := Eucl 2) S punc)).symm

end GenericLeg

/-! ## §3. The lifted slit-plane cover of `S²×(ℝ²∖{0})` and its four collapsing pieces -/

/-- The `A`-leg: `S² × slitUp`. -/
abbrev legUp : Set ↑SlitProd :=
  (Set.univ : Set ↑(Sph 2)) ×ˢ (restr (X := Eucl 2) slitUp punc)

/-- The `B`-leg: `S² × slitDown`. -/
abbrev legDown : Set ↑SlitProd :=
  (Set.univ : Set ↑(Sph 2)) ×ˢ (restr (X := Eucl 2) slitDown punc)

/-- The positive intersection component: `S² × {x₀ > 0}`. -/
abbrev compPos : Set ↑SlitProd :=
  (Set.univ : Set ↑(Sph 2)) ×ˢ (restr (X := Eucl 2) posHalf punc)

/-- The negative intersection component: `S² × {x₀ < 0}`. -/
abbrev compNeg : Set ↑SlitProd :=
  (Set.univ : Set ↑(Sph 2)) ×ˢ (restr (X := Eucl 2) negHalf punc)

theorem legUp_isOpen : IsOpen legUp :=
  isOpen_univ.prod (slitUp_isOpen.preimage continuous_subtype_val)

theorem legDown_isOpen : IsOpen legDown :=
  isOpen_univ.prod (slitDown_isOpen.preimage continuous_subtype_val)

theorem compPos_isOpen : IsOpen compPos :=
  isOpen_univ.prod (posHalf_isOpen.preimage continuous_subtype_val)

theorem compNeg_isOpen : IsOpen compNeg :=
  isOpen_univ.prod (negHalf_isOpen.preimage continuous_subtype_val)

/-- The lifted slit-plane cover is an interior cover of `S²×(ℝ²∖{0})`. -/
theorem legs_cover :
    (⋃ U ∈ ({legUp, legDown} : Set (Set ↑SlitProd)), interior U) = Set.univ := by
  rw [Set.biUnion_pair, legUp_isOpen.interior_eq, legDown_isOpen.interior_eq, ← Set.prod_union,
    ← Set.preimage_union, slitUp_union_slitDown, Set.eq_univ_iff_forall]
  intro p
  exact Set.mem_prod.mpr ⟨Set.mem_univ _, p.2.2⟩

/-! ### The four instantiated collapses, path-connectedness, and `H₁ = 0` -/

/-- `Hₙ₊₁(S² × slitUp; ℤ) ≅ Hₙ₊₁(S²; ℤ)`. -/
noncomputable def legUpEquivInt (n : ℕ) :
    Homology (sub (X := SlitProd) legUp) (n + 1) ≃ₗ[ℤ] Homology (Sph 2) (n + 1) :=
  legEquivInt slitUp_subset_punc starConvex_slitUp poleUp_mem_slitUp n

/-- `Hₙ₊₁(S² × slitDown; ℤ) ≅ Hₙ₊₁(S²; ℤ)`. -/
noncomputable def legDownEquivInt (n : ℕ) :
    Homology (sub (X := SlitProd) legDown) (n + 1) ≃ₗ[ℤ] Homology (Sph 2) (n + 1) :=
  legEquivInt slitDown_subset_punc starConvex_slitDown poleDown_mem_slitDown n

/-- `Hₙ₊₁(S² × posHalf; ℤ) ≅ Hₙ₊₁(S²; ℤ)`. -/
noncomputable def compPosEquivInt (n : ℕ) :
    Homology (sub (X := SlitProd) compPos) (n + 1) ≃ₗ[ℤ] Homology (Sph 2) (n + 1) :=
  legEquivInt posHalf_subset_punc (posHalf_convex.starConvex posHalf_nonempty)
    posHalf_nonempty n

/-- `Hₙ₊₁(S² × negHalf; ℤ) ≅ Hₙ₊₁(S²; ℤ)`. -/
noncomputable def compNegEquivInt (n : ℕ) :
    Homology (sub (X := SlitProd) compNeg) (n + 1) ≃ₗ[ℤ] Homology (Sph 2) (n + 1) :=
  legEquivInt negHalf_subset_punc (negHalf_convex.starConvex negHalf_nonempty)
    negHalf_nonempty n

theorem legUp_pathConnected : PathConnectedSpace ↥(sub (X := SlitProd) legUp) :=
  legPathConnected slitUp_subset_punc starConvex_slitUp poleUp_mem_slitUp

theorem legDown_pathConnected : PathConnectedSpace ↥(sub (X := SlitProd) legDown) :=
  legPathConnected slitDown_subset_punc starConvex_slitDown poleDown_mem_slitDown

theorem compPos_pathConnected : PathConnectedSpace ↥(sub (X := SlitProd) compPos) :=
  legPathConnected posHalf_subset_punc (posHalf_convex.starConvex posHalf_nonempty)
    posHalf_nonempty

theorem compNeg_pathConnected : PathConnectedSpace ↥(sub (X := SlitProd) compNeg) :=
  legPathConnected negHalf_subset_punc (negHalf_convex.starConvex negHalf_nonempty)
    negHalf_nonempty

theorem legUp_homology_one_eq_zero (u : Homology (sub (X := SlitProd) legUp) 1) : u = 0 :=
  (legUpEquivInt 0).map_eq_zero_iff.mp
    (sphere_homology_middleInt 1 2 one_pos one_lt_two (legUpEquivInt 0 u))

theorem legDown_homology_one_eq_zero (u : Homology (sub (X := SlitProd) legDown) 1) : u = 0 :=
  (legDownEquivInt 0).map_eq_zero_iff.mp
    (sphere_homology_middleInt 1 2 one_pos one_lt_two (legDownEquivInt 0 u))

theorem compPos_homology_one_eq_zero (u : Homology (sub (X := SlitProd) compPos) 1) : u = 0 :=
  (compPosEquivInt 0).map_eq_zero_iff.mp
    (sphere_homology_middleInt 1 2 one_pos one_lt_two (compPosEquivInt 0 u))

theorem compNeg_homology_one_eq_zero (u : Homology (sub (X := SlitProd) compNeg) 1) : u = 0 :=
  (compNegEquivInt 0).map_eq_zero_iff.mp
    (sphere_homology_middleInt 1 2 one_pos one_lt_two (compNegEquivInt 0 u))

/-! ## §4. The clopen split of the intersection: `H(legUp ∩ legDown) ≅ H(compPos) × H(compNeg)` -/

theorem compPos_subset_inter : compPos ⊆ legUp ∩ legDown := by
  intro p hp
  obtain ⟨h1, h2⟩ := Set.mem_prod.mp hp
  exact ⟨Set.mem_prod.mpr ⟨h1, posHalf_subset_slitUp h2⟩,
    Set.mem_prod.mpr ⟨h1, posHalf_subset_slitDown h2⟩⟩

theorem compNeg_subset_inter : compNeg ⊆ legUp ∩ legDown := by
  intro p hp
  obtain ⟨h1, h2⟩ := Set.mem_prod.mp hp
  exact ⟨Set.mem_prod.mpr ⟨h1, negHalf_subset_slitUp h2⟩,
    Set.mem_prod.mpr ⟨h1, negHalf_subset_slitDown h2⟩⟩

/-- Membership in the intersection forces `x₀ ≠ 0` in the plane factor. -/
theorem inter_x0_ne_zero {p : ↑SlitProd} (hp : p ∈ legUp ∩ legDown) :
    (p.2 : EuclideanSpace ℝ (Fin 2)) 0 ≠ 0 := by
  have h : (p.2 : EuclideanSpace ℝ (Fin 2)) ∈ slitUp ∩ slitDown :=
    ⟨(Set.mem_prod.mp hp.1).2, (Set.mem_prod.mp hp.2).2⟩
  rw [slitUp_inter_slitDown] at h
  exact h

/-- The positive component viewed inside the intersection subtype (the clopen `U`). -/
abbrev interU : Set ↥(sub (X := SlitProd) (legUp ∩ legDown)) :=
  restr (X := SlitProd) compPos (legUp ∩ legDown)

/-- The complement of the positive component inside the intersection is the negative component
(`x₀ ≠ 0` trichotomy). -/
theorem interU_compl : interUᶜ = restr (X := SlitProd) compNeg (legUp ∩ legDown) := by
  ext q
  simp only [Set.mem_compl_iff, Set.mem_preimage]
  constructor
  · intro hq
    refine Set.mem_prod.mpr ⟨Set.mem_univ _, ?_⟩
    have hne := inter_x0_ne_zero q.2
    have hpos : ¬(0 < ((q : ↑SlitProd).2 : EuclideanSpace ℝ (Fin 2)) 0) := fun h =>
      hq (Set.mem_prod.mpr ⟨Set.mem_univ _, h⟩)
    exact lt_of_le_of_ne (le_of_not_gt hpos) hne
  · intro hq hpos
    have h1 : (0 : ℝ) < ((q : ↑SlitProd).2 : EuclideanSpace ℝ (Fin 2)) 0 :=
      (Set.mem_prod.mp hpos).2
    have h2 : ((q : ↑SlitProd).2 : EuclideanSpace ℝ (Fin 2)) 0 < 0 :=
      (Set.mem_prod.mp hq).2
    linarith

theorem interU_isClopen : IsClopen interU := by
  constructor
  · rw [← isOpen_compl_iff, interU_compl]
    exact compNeg_isOpen.preimage continuous_subtype_val
  · exact compPos_isOpen.preimage continuous_subtype_val

/-- The positive intersection component IS `compPos` (seam + set congruence). -/
noncomputable def interPosHomeo :
    ↥(sub (X := sub (X := SlitProd) (legUp ∩ legDown)) interU)
      ≃ₜ ↥(sub (X := SlitProd) compPos) :=
  (seamHomeo (X := SlitProd) compPos (legUp ∩ legDown)).trans
    (Homeomorph.setCongr (Set.inter_eq_self_of_subset_left compPos_subset_inter))

/-- The negative intersection component IS `compNeg`. -/
noncomputable def interNegHomeo :
    ↥(sub (X := sub (X := SlitProd) (legUp ∩ legDown)) interUᶜ)
      ≃ₜ ↥(sub (X := SlitProd) compNeg) :=
  (Homeomorph.setCongr interU_compl).trans
    ((seamHomeo (X := SlitProd) compNeg (legUp ∩ legDown)).trans
      (Homeomorph.setCongr (Set.inter_eq_self_of_subset_left compNeg_subset_inter)))

/-- **The every-degree component decomposition of the intersection homology**
`Hₙ(S²×{x₀≠0}; ℤ) ≅ Hₙ(S²×posHalf; ℤ) × Hₙ(S²×negHalf; ℤ)` (clopen split + flatteners). -/
noncomputable def interSplitEquiv (n : ℕ) :
    Homology (sub (X := SlitProd) (legUp ∩ legDown)) n
      ≃ₗ[ℤ] Homology (sub (X := SlitProd) compPos) n × Homology (sub (X := SlitProd) compNeg) n :=
  (splitHIntEquiv interU_isClopen n).symm.trans
    (LinearEquiv.prodCongr (homeoHomologyEquivInt interPosHomeo n)
      (homeoHomologyEquivInt interNegHomeo n))

/-- `H₁(legUp ∩ legDown; ℤ) = 0` — both components collapse to `H₁(S²;ℤ) = 0`. -/
theorem inter_homology_one_eq_zero
    (w : Homology (sub (X := SlitProd) (legUp ∩ legDown)) 1) : w = 0 := by
  have h : interSplitEquiv 1 w = 0 :=
    Prod.ext (compPos_homology_one_eq_zero _) (compNeg_homology_one_eq_zero _)
  exact (interSplitEquiv 1).map_eq_zero_iff.mp h

/-! ## §5. `H₁(S²×(ℝ²∖{0}); ℤ) ≅ ℤ` — exactness at `H₀(A∩B)` through the augmentations -/

/-- **Augmentation additivity across the component split**: `ε̄(w) = ε̄(w₊) + ε̄(w₋)`. -/
theorem augHInt_interSplit (w : Homology (sub (X := SlitProd) (legUp ∩ legDown)) 0) :
    augHInt (sub (X := SlitProd) (legUp ∩ legDown)) w
      = augHInt (sub (X := SlitProd) compPos) (interSplitEquiv 0 w).1
        + augHInt (sub (X := SlitProd) compNeg) (interSplitEquiv 0 w).2 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (splitHIntEquiv interU_isClopen 0).surjective w
  have hcoords : interSplitEquiv 0 (splitHIntEquiv interU_isClopen 0 (a, b))
      = (homeoHomologyEquivInt interPosHomeo 0 a, homeoHomologyEquivInt interNegHomeo 0 b) := by
    rw [interSplitEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  have hsplit : splitHIntEquiv interU_isClopen 0 (a, b) = splitH0Int interU (a, b) := rfl
  rw [hcoords, hsplit, augHInt_splitH0Int]
  rw [homeoHomologyEquivInt_apply, homeoHomologyEquivInt_apply, augHInt_naturality,
    augHInt_naturality]

/-- **The H₁ comparison map** `x ↦ ε̄((split δx)₊)`: the positive-component augmentation of the MV
connecting image. The anti-diagonal `ker Δ₀` in coordinates. -/
noncomputable def hOneToInt : Homology SlitProd 1 →ₗ[ℤ] ℤ :=
  (augHInt (sub (X := SlitProd) compPos)).comp
    ((LinearMap.fst ℤ _ _).comp
      (((interSplitEquiv 0).toLinearMap).comp (mvDeltaInt legUp legDown 0 legs_cover)))

theorem hOneToInt_apply (x : Homology SlitProd 1) :
    hOneToInt x = augHInt (sub (X := SlitProd) compPos)
      (interSplitEquiv 0 (mvDeltaInt legUp legDown 0 legs_cover x)).1 := rfl

/-- `hOneToInt` is injective: `ε̄₊(δx) = 0` forces `δx = 0` (the anti-diagonal constraint from
`Δ₀ ∘ δ = 0` kills the other component; path-connected components make `ε̄` injective), and
exactness at `H₁(X)` lifts `x` to the legs, whose `H₁` vanish. -/
theorem hOneToInt_injective : Function.Injective hOneToInt := by
  refine (injective_iff_map_eq_zero hOneToInt).mpr fun x hx => ?_
  -- Δ₀(δx) = 0 (complex condition), so the A-pushforward of δx vanishes
  have hdiag := mvHomDiagInt_mvDeltaInt legUp legDown 0 legs_cover x
  have hfst : Homology.mapInt (subIncl (Set.inter_subset_left (s := legUp) (t := legDown))) 0
      (mvDeltaInt legUp legDown 0 legs_cover x) = 0 := congrArg Prod.fst hdiag
  -- the total augmentation of δx vanishes
  have haug : augHInt (sub (X := SlitProd) (legUp ∩ legDown))
      (mvDeltaInt legUp legDown 0 legs_cover x) = 0 := by
    rw [← augHInt_naturality (subIncl (Set.inter_subset_left (s := legUp) (t := legDown)))
        (mvDeltaInt legUp legDown 0 legs_cover x), hfst, map_zero]
  -- both component augmentations vanish
  have ha0 : augHInt (sub (X := SlitProd) compPos)
      (interSplitEquiv 0 (mvDeltaInt legUp legDown 0 legs_cover x)).1 = 0 := hx
  have hb0 : augHInt (sub (X := SlitProd) compNeg)
      (interSplitEquiv 0 (mvDeltaInt legUp legDown 0 legs_cover x)).2 = 0 := by
    have h := augHInt_interSplit (mvDeltaInt legUp legDown 0 legs_cover x)
    rw [haug, ha0, zero_add] at h
    exact h.symm
  -- injective augmentations on the path-connected components: δx = 0
  haveI := compPos_pathConnected
  haveI := compNeg_pathConnected
  have ha : (interSplitEquiv 0 (mvDeltaInt legUp legDown 0 legs_cover x)).1 = 0 :=
    augHInt_injective_pathConnected (X := sub (X := SlitProd) compPos)
      (by rw [map_zero]; exact ha0)
  have hb : (interSplitEquiv 0 (mvDeltaInt legUp legDown 0 legs_cover x)).2 = 0 :=
    augHInt_injective_pathConnected (X := sub (X := SlitProd) compNeg)
      (by rw [map_zero]; exact hb0)
  have hδ : mvDeltaInt legUp legDown 0 legs_cover x = 0 :=
    (interSplitEquiv 0).map_eq_zero_iff.mp (Prod.ext ha hb)
  -- exactness at H₁(X) lifts x to the legs, both of which vanish
  obtain ⟨⟨u, v⟩, hx'⟩ := (mv_exact_ambientInt legUp legDown 0 legs_cover x).mp hδ
  rw [← hx', mvHomSumInt_apply, legUp_homology_one_eq_zero u, legDown_homology_one_eq_zero v,
    map_zero, map_zero, sub_zero]

/-- A point of the positive component (for augmentation surjectivity). -/
noncomputable def posPoint : ↥(sub (X := SlitProd) compPos) :=
  ⟨(basePoint 2, ⟨EuclideanSpace.single (0 : Fin 2) (1 : ℝ),
      posHalf_subset_punc posHalf_nonempty⟩),
    Set.mem_prod.mpr ⟨Set.mem_univ _, posHalf_nonempty⟩⟩

/-- A point of the negative component. -/
noncomputable def negPoint : ↥(sub (X := SlitProd) compNeg) :=
  ⟨(basePoint 2, ⟨EuclideanSpace.single (0 : Fin 2) (-1 : ℝ),
      negHalf_subset_punc negHalf_nonempty⟩),
    Set.mem_prod.mpr ⟨Set.mem_univ _, negHalf_nonempty⟩⟩

/-- `hOneToInt` is surjective: hit `m` with the anti-diagonal class `(m, −m)` — its `Δ₀`-image dies
against the injective leg augmentations, so exactness at `H₀(A∩B)` realizes it as a `δ`-image. -/
theorem hOneToInt_surjective : Function.Surjective hOneToInt := by
  intro m
  obtain ⟨a, ha⟩ := augHInt_surjective (sub (X := SlitProd) compPos) (constSimplex posPoint 0) m
  obtain ⟨b, hb⟩ :=
    augHInt_surjective (sub (X := SlitProd) compNeg) (constSimplex negPoint 0) (-m)
  have hcoords : interSplitEquiv 0 ((interSplitEquiv 0).symm (a, b)) = (a, b) :=
    (interSplitEquiv 0).apply_symm_apply (a, b)
  -- the total augmentation of the anti-diagonal class vanishes
  have haugw : augHInt (sub (X := SlitProd) (legUp ∩ legDown))
      ((interSplitEquiv 0).symm (a, b)) = 0 := by
    rw [augHInt_interSplit, hcoords]
    show augHInt (sub (X := SlitProd) compPos) a + augHInt (sub (X := SlitProd) compNeg) b = 0
    rw [ha, hb, add_neg_cancel]
  -- Δ₀ kills it (augmentation-injective path-connected legs)
  haveI := legUp_pathConnected
  haveI := legDown_pathConnected
  have hdiag : mvHomDiagInt legUp legDown 0 ((interSplitEquiv 0).symm (a, b)) = 0 := by
    refine Prod.ext ?_ ?_
    · show Homology.mapInt (subIncl (Set.inter_subset_left (s := legUp) (t := legDown))) 0
        ((interSplitEquiv 0).symm (a, b)) = 0
      apply augHInt_injective_pathConnected (X := sub (X := SlitProd) legUp)
      rw [map_zero, augHInt_naturality, haugw]
    · show Homology.mapInt (subIncl (Set.inter_subset_right (s := legUp) (t := legDown))) 0
        ((interSplitEquiv 0).symm (a, b)) = 0
      apply augHInt_injective_pathConnected (X := sub (X := SlitProd) legDown)
      rw [map_zero, augHInt_naturality, haugw]
  -- exactness at H₀(A∩B) realizes the class as δx
  obtain ⟨x, hx⟩ := (mv_exact_interInt legUp legDown 0 legs_cover
    ((interSplitEquiv 0).symm (a, b))).mp hdiag
  refine ⟨x, ?_⟩
  rw [hOneToInt_apply, hx, hcoords]
  exact ha

/-- **`H₁(S²×(ℝ²∖{0}); ℤ) ≅ ℤ`** — slice 1's first deliverable. The generator is the puncture
circle class: its δ-image is the anti-diagonal `(1, −1)` across the two intersection components. -/
noncomputable def slitProdHOneEquivInt : Homology SlitProd 1 ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective hOneToInt ⟨hOneToInt_injective, hOneToInt_surjective⟩

/-! ## §6. The generator bookkeeping: every collapse is the first-coordinate projection

`legEquivInt` (hence all four instantiated collapses) is induced by the literal continuous map
`p ↦ p.1.1`; pushing a component class into a leg and collapsing therefore equals collapsing the
component directly — every naturality square is `rfl` at the continuous-map level. This is what
makes the `Δ₂`-image the DIAGONAL in `(H₂(S²))²` coordinates. -/

/-- The first-coordinate collapse of a subset of `S²×(ℝ²∖{0})`. -/
def fstCM (T : Set ↑SlitProd) : C(↥(sub (X := SlitProd) T), ↑(Sph 2)) :=
  ⟨fun p => (p : ↑SlitProd).1, continuous_fst.comp continuous_subtype_val⟩

/-- The first-coordinate collapse of a subset of the intersection subtype (double subtype). -/
def interFstCM (T : Set ↥(sub (X := SlitProd) (legUp ∩ legDown))) :
    C(↥(sub (X := sub (X := SlitProd) (legUp ∩ legDown)) T), ↑(Sph 2)) :=
  ⟨fun p => ((p : ↥(sub (X := SlitProd) (legUp ∩ legDown))) : ↑SlitProd).1,
    continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

/-- **The generic leg collapse is the first-coordinate pushforward** — the canonical form of
`legEquivInt` (its homeo seam + projection compose to the literal `p ↦ p.1.1`). -/
theorem legEquivInt_eq_mapInt {S : Set (EuclideanSpace ℝ (Fin 2))} {p₀ : EuclideanSpace ℝ (Fin 2)}
    (hS : S ⊆ punc) (hstar : StarConvex ℝ p₀ S) (hp₀ : p₀ ∈ S) (n : ℕ)
    (y : Homology (sub (X := SlitProd)
      ((Set.univ : Set ↑(Sph 2)) ×ˢ (restr (X := Eucl 2) S punc))) (n + 1)) :
    legEquivInt hS hstar hp₀ n y
      = Homology.mapInt (fstCM ((Set.univ : Set ↑(Sph 2)) ×ˢ (restr (X := Eucl 2) S punc)))
          (n + 1) y := by
  show Homology.mapInt (prodFst (Sph 2) (sub (restr (X := Eucl 2) S punc))) (n + 1)
      (Homology.mapInt
        ⟨prodSetHomeo (Sph 2) PuncPlane (restr (X := Eucl 2) S punc),
         (prodSetHomeo (Sph 2) PuncPlane (restr (X := Eucl 2) S punc)).continuous⟩ (n + 1) y)
      = _
  rw [← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- Pushing the positive intersection component into the `legUp` leg and collapsing = collapsing
the component (both are `p ↦ p.1.1.1`). -/
theorem legUp_collapse_pos (p : Homology (sub (X := sub (X := SlitProd) (legUp ∩ legDown))
    interU) 2) :
    legUpEquivInt 1 (Homology.mapInt
        (subIncl (Set.inter_subset_left (s := legUp) (t := legDown))) 2
        (homIncl interU 2 p))
      = Homology.mapInt (interFstCM interU) 2 p := by
  rw [← Homology.mapInt_ambIncl, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
    legUpEquivInt, legEquivInt_eq_mapInt, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- Same for the negative component into `legUp`. -/
theorem legUp_collapse_neg (q : Homology (sub (X := sub (X := SlitProd) (legUp ∩ legDown))
    interUᶜ) 2) :
    legUpEquivInt 1 (Homology.mapInt
        (subIncl (Set.inter_subset_left (s := legUp) (t := legDown))) 2
        (homIncl interUᶜ 2 q))
      = Homology.mapInt (interFstCM interUᶜ) 2 q := by
  rw [← Homology.mapInt_ambIncl, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
    legUpEquivInt, legEquivInt_eq_mapInt, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- The positive component into `legDown` — the SAME first-coordinate map. -/
theorem legDown_collapse_pos (p : Homology (sub (X := sub (X := SlitProd) (legUp ∩ legDown))
    interU) 2) :
    legDownEquivInt 1 (Homology.mapInt
        (subIncl (Set.inter_subset_right (s := legUp) (t := legDown))) 2
        (homIncl interU 2 p))
      = Homology.mapInt (interFstCM interU) 2 p := by
  rw [← Homology.mapInt_ambIncl, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
    legDownEquivInt, legEquivInt_eq_mapInt, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- The negative component into `legDown`. -/
theorem legDown_collapse_neg (q : Homology (sub (X := sub (X := SlitProd) (legUp ∩ legDown))
    interUᶜ) 2) :
    legDownEquivInt 1 (Homology.mapInt
        (subIncl (Set.inter_subset_right (s := legUp) (t := legDown))) 2
        (homIncl interUᶜ 2 q))
      = Homology.mapInt (interFstCM interUᶜ) 2 q := by
  rw [← Homology.mapInt_ambIncl, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
    legDownEquivInt, legEquivInt_eq_mapInt, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- The `interSplitEquiv`-coordinate collapse of the positive component is the same
first-coordinate map (the flattener is val-preserving). -/
theorem compPos_collapse_flat (p : Homology (sub (X := sub (X := SlitProd) (legUp ∩ legDown))
    interU) 2) :
    compPosEquivInt 1 (homeoHomologyEquivInt interPosHomeo 2 p)
      = Homology.mapInt (interFstCM interU) 2 p := by
  rw [homeoHomologyEquivInt_apply, compPosEquivInt, legEquivInt_eq_mapInt,
    ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- Same for the negative component. -/
theorem compNeg_collapse_flat (q : Homology (sub (X := sub (X := SlitProd) (legUp ∩ legDown))
    interUᶜ) 2) :
    compNegEquivInt 1 (homeoHomologyEquivInt interNegHomeo 2 q)
      = Homology.mapInt (interFstCM interUᶜ) 2 q := by
  rw [homeoHomologyEquivInt_apply, compNegEquivInt, legEquivInt_eq_mapInt,
    ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- **The `Δ₂`-image is the DIAGONAL, first coordinate**: in the `(H₂(S²))²` coordinates of the
intersection, the `legUp`-pushforward of any class is the SUM of its two component collapses. -/
theorem diag_fst_via_split (w : Homology (sub (X := SlitProd) (legUp ∩ legDown)) 2) :
    legUpEquivInt 1 ((mvHomDiagInt legUp legDown 2 w).1)
      = compPosEquivInt 1 (interSplitEquiv 2 w).1 + compNegEquivInt 1 (interSplitEquiv 2 w).2 := by
  obtain ⟨⟨p, q⟩, rfl⟩ := (splitHIntEquiv interU_isClopen 2).surjective w
  have hcoords : interSplitEquiv 2 (splitHIntEquiv interU_isClopen 2 (p, q))
      = (homeoHomologyEquivInt interPosHomeo 2 p, homeoHomologyEquivInt interNegHomeo 2 q) := by
    rw [interSplitEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  have hsplit : splitHIntEquiv interU_isClopen 2 (p, q)
      = homIncl interU 2 p + homIncl interUᶜ 2 q := rfl
  rw [hcoords, hsplit]
  show legUpEquivInt 1 (Homology.mapInt
      (subIncl (Set.inter_subset_left (s := legUp) (t := legDown))) 2
      (homIncl interU 2 p + homIncl interUᶜ 2 q)) = _
  rw [map_add, map_add, legUp_collapse_pos, legUp_collapse_neg, compPos_collapse_flat,
    compNeg_collapse_flat]

/-- **The `Δ₂`-image is the DIAGONAL, second coordinate** — the `legDown`-pushforward is the SAME
component sum. -/
theorem diag_snd_via_split (w : Homology (sub (X := SlitProd) (legUp ∩ legDown)) 2) :
    legDownEquivInt 1 ((mvHomDiagInt legUp legDown 2 w).2)
      = compPosEquivInt 1 (interSplitEquiv 2 w).1 + compNegEquivInt 1 (interSplitEquiv 2 w).2 := by
  obtain ⟨⟨p, q⟩, rfl⟩ := (splitHIntEquiv interU_isClopen 2).surjective w
  have hcoords : interSplitEquiv 2 (splitHIntEquiv interU_isClopen 2 (p, q))
      = (homeoHomologyEquivInt interPosHomeo 2 p, homeoHomologyEquivInt interNegHomeo 2 q) := by
    rw [interSplitEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  have hsplit : splitHIntEquiv interU_isClopen 2 (p, q)
      = homIncl interU 2 p + homIncl interUᶜ 2 q := rfl
  rw [hcoords, hsplit]
  show legDownEquivInt 1 (Homology.mapInt
      (subIncl (Set.inter_subset_right (s := legUp) (t := legDown))) 2
      (homIncl interU 2 p + homIncl interUᶜ 2 q)) = _
  rw [map_add, map_add, legDown_collapse_pos, legDown_collapse_neg, compPos_collapse_flat,
    compNeg_collapse_flat]

/-! ## §7. `H₂(S²×(ℝ²∖{0}); ℤ) ≅ ℤ` — surjective `Σ₂` and the diagonal kernel -/

/-- **The H₂ comparison map** `t ↦ Σ₂((legUp collapse)⁻¹(t·[S²]), 0)`: the S² top class pushed
through the `legUp` leg. -/
noncomputable def intToHTwo : ℤ →ₗ[ℤ] Homology SlitProd 2 :=
  (mvHomSumInt legUp legDown 2).comp
    ((LinearMap.inl ℤ _ _).comp
      (((legUpEquivInt 1).symm.toLinearMap).comp ((topSphereIsoInt 1).symm.toLinearMap)))

theorem intToHTwo_apply (t : ℤ) :
    intToHTwo t = mvHomSumInt legUp legDown 2
      ((legUpEquivInt 1).symm ((topSphereIsoInt 1).symm t), 0) := rfl

/-- `intToHTwo` is injective: a vanishing image lies in `im Δ₂` (middle exactness), whose
coordinates are diagonal — but the second coordinate of `(s, 0)` collapses to `0`, so the diagonal
value, hence `t`, is `0`. -/
theorem intToHTwo_injective : Function.Injective intToHTwo := by
  refine (injective_iff_map_eq_zero intToHTwo).mpr fun t ht => ?_
  rw [intToHTwo_apply] at ht
  obtain ⟨w, hw⟩ := (mv_exact_middleInt legUp legDown 1 legs_cover _).mp ht
  have h1 := diag_fst_via_split w
  have h2 := diag_snd_via_split w
  have hw1 : (mvHomDiagInt legUp legDown 2 w).1
      = (legUpEquivInt 1).symm ((topSphereIsoInt 1).symm t) := by rw [hw]
  have hw2 : (mvHomDiagInt legUp legDown 2 w).2 = 0 := by rw [hw]
  rw [hw1, LinearEquiv.apply_symm_apply] at h1
  rw [hw2, map_zero] at h2
  have : (topSphereIsoInt 1).symm t = 0 := h1.trans h2.symm
  exact (LinearEquiv.map_eq_zero_iff _).mp this

/-- `intToHTwo` is surjective: `H₁(A∩B) = 0` kills `δ₂`, so `Σ₂` is surjective; correcting a
preimage `(u, v)` by the diagonal class with value `legDown-collapse(v)` moves it into
`(im Δ₂)ᶜ`-normal form `(s, 0)` without changing the image. -/
theorem intToHTwo_surjective : Function.Surjective intToHTwo := by
  intro x
  have hδ : mvDeltaInt legUp legDown 1 legs_cover x = 0 := inter_homology_one_eq_zero _
  obtain ⟨⟨u, v⟩, hx⟩ := (mv_exact_ambientInt legUp legDown 1 legs_cover x).mp hδ
  refine ⟨topSphereIsoInt 1 (legUpEquivInt 1 u - legDownEquivInt 1 v), ?_⟩
  rw [intToHTwo_apply, LinearEquiv.symm_apply_apply]
  -- the diagonal witness with value `legDown-collapse v`
  set d := legDownEquivInt 1 v with hd
  set s := (legUpEquivInt 1).symm (legUpEquivInt 1 u - d) with hs
  set w := (interSplitEquiv 2).symm ((compPosEquivInt 1).symm d, 0) with hwdef
  have hcoords : interSplitEquiv 2 w = ((compPosEquivInt 1).symm d, 0) :=
    (interSplitEquiv 2).apply_symm_apply _
  have hΔ : mvHomDiagInt legUp legDown 2 w = (u - s, v) := by
    refine Prod.ext ?_ ?_
    · apply (legUpEquivInt 1).injective
      rw [diag_fst_via_split w, hcoords]
      show compPosEquivInt 1 ((compPosEquivInt 1).symm d) + compNegEquivInt 1 0 = _
      rw [LinearEquiv.apply_symm_apply, map_zero, add_zero, map_sub, hs,
        LinearEquiv.apply_symm_apply, sub_sub_cancel]
    · apply (legDownEquivInt 1).injective
      rw [diag_snd_via_split w, hcoords]
      show compPosEquivInt 1 ((compPosEquivInt 1).symm d) + compNegEquivInt 1 0 = _
      rw [LinearEquiv.apply_symm_apply, map_zero, add_zero, hd]
  have hker : mvHomSumInt legUp legDown 2 (u - s, v) = 0 := by
    rw [← hΔ]
    exact mvHomSumInt_mvHomDiagInt legUp legDown 2 w
  rw [← hx,
    show (u, v) = ((s, 0) : Homology (sub (X := SlitProd) legUp) 2
        × Homology (sub (X := SlitProd) legDown) 2) + (u - s, v) from by
      rw [Prod.mk_add_mk, add_sub_cancel, zero_add],
    map_add, hker, add_zero]

/-- **The H₂ class of `S²×(ℝ²∖{0}) IS the S² top class**: the first-factor projection induces a
bijection on `H₂` — the generator-bookkeeping export slice 3 consumes. -/
theorem prodFst_homology_two_bijective :
    Function.Bijective (Homology.mapInt (prodFst (Sph 2) PuncPlane) 2) := by
  have hcomp : ∀ t : ℤ, Homology.mapInt (prodFst (Sph 2) PuncPlane) 2 (intToHTwo t)
      = (topSphereIsoInt 1).symm t := by
    intro t
    rw [intToHTwo_apply, mvHomSumInt_apply, map_zero, sub_zero, ← LinearMap.comp_apply,
      ← Homology.mapInt_comp]
    have hcm : Homology.mapInt ((prodFst (Sph 2) PuncPlane).comp (ambIncl legUp)) 2
        ((legUpEquivInt 1).symm ((topSphereIsoInt 1).symm t))
        = legUpEquivInt 1 ((legUpEquivInt 1).symm ((topSphereIsoInt 1).symm t)) := by
      rw [legUpEquivInt, legEquivInt_eq_mapInt]
      rfl
    rw [hcm, LinearEquiv.apply_symm_apply]
  have hbij : Function.Bijective
      (fun t : ℤ => Homology.mapInt (prodFst (Sph 2) PuncPlane) 2 (intToHTwo t)) := by
    rw [funext hcomp]
    exact (topSphereIsoInt 1).symm.bijective
  exact (Function.Bijective.of_comp_iff _
    ⟨intToHTwo_injective, intToHTwo_surjective⟩).mp hbij

/-- `H₂(S²×(ℝ²∖{0});ℤ) ≅ H₂(S²;ℤ)` — realized by the first-factor projection (the canonical
generator identification). -/
noncomputable def slitProdHTwoViaFst : Homology SlitProd 2 ≃ₗ[ℤ] Homology (Sph 2) 2 :=
  LinearEquiv.ofBijective (Homology.mapInt (prodFst (Sph 2) PuncPlane) 2)
    prodFst_homology_two_bijective

/-- **`H₂(S²×(ℝ²∖{0}); ℤ) ≅ ℤ`** — slice 1's second deliverable. -/
noncomputable def slitProdHTwoEquivInt : Homology SlitProd 2 ≃ₗ[ℤ] ℤ :=
  slitProdHTwoViaFst.trans (topSphereIsoInt 1)

instance : Module.Free ℤ (Homology SlitProd 1) := Module.Free.of_equiv slitProdHOneEquivInt.symm
instance : Module.Finite ℤ (Homology SlitProd 1) := Module.Finite.equiv slitProdHOneEquivInt.symm
instance : Module.Free ℤ (Homology SlitProd 2) := Module.Free.of_equiv slitProdHTwoEquivInt.symm
instance : Module.Finite ℤ (Homology SlitProd 2) := Module.Finite.equiv slitProdHTwoEquivInt.symm

/-! ## §8. Slice 2: the transport to the S²×S² polar-cover intersection -/

/-- **The S²×S² polar-cover intersection IS `S²×(ℝ²∖{0})`** — the one-line transport
(cover set congruence → product seam → stereographic recentering in the second factor). -/
noncomputable def interProdHomeo (v : ↑(Sph 2)) :
    ↥(sub (X := ProdSp (Sph 2) (Sph 2)) (coverA v ∩ coverB v)) ≃ₜ ↑SlitProd :=
  ((Homeomorph.setCongr (coverAB_inter v)).trans
    (prodSetHomeo (Sph 2) (Sph 2) (({v}ᶜ : Set ↑(Sph 2)) ∩ ({antipode v}ᶜ)))).trans
    ((Homeomorph.refl ↑(Sph 2)).prodCongr (doublyPuncturedSphereHomeo 2 v))

/-- The transport is first-coordinate-preserving — slice 3's Δ-bookkeeping reduces to first-factor
projections through it. -/
theorem interProdHomeo_fst (v : ↑(Sph 2))
    (p : ↥(sub (X := ProdSp (Sph 2) (Sph 2)) (coverA v ∩ coverB v))) :
    (interProdHomeo v p).1 = (p : ↑(ProdSp (Sph 2) (Sph 2))).1 := rfl

/-- **`H₁(S²×(S²∖{v,−v}); ℤ) ≅ ℤ`** at the polar-cover intersection — slice 3's δ-target datum. -/
noncomputable def coverInterHOneEquivInt (v : ↑(Sph 2)) :
    Homology (sub (X := ProdSp (Sph 2) (Sph 2)) (coverA v ∩ coverB v)) 1 ≃ₗ[ℤ] ℤ :=
  (homeoHomologyEquivInt (interProdHomeo v) 1).trans slitProdHOneEquivInt

/-- **`H₂(S²×(S²∖{v,−v}); ℤ) ≅ ℤ`** at the polar-cover intersection — slice 3's Δ₂-source datum. -/
noncomputable def coverInterHTwoEquivInt (v : ↑(Sph 2)) :
    Homology (sub (X := ProdSp (Sph 2) (Sph 2)) (coverA v ∩ coverB v)) 2 ≃ₗ[ℤ] ℤ :=
  (homeoHomologyEquivInt (interProdHomeo v) 2).trans slitProdHTwoEquivInt

/-- The first-coordinate collapse of the S²×S² polar intersection. -/
def coverInterFstCM (v : ↑(Sph 2)) :
    C(↥(sub (X := ProdSp (Sph 2) (Sph 2)) (coverA v ∩ coverB v)), ↑(Sph 2)) :=
  ⟨fun p => (p : ↑(ProdSp (Sph 2) (Sph 2))).1, continuous_fst.comp continuous_subtype_val⟩

/-- **Slice-3 export**: through the transport, the surviving `H₂` class of the polar intersection
is READ OFF by its own first-coordinate collapse — slice 3's `Δ₂`-coordinates then reduce to
`rfl`-level continuous-map identifications exactly as in this module's §6. -/
theorem coverInter_collapse_two (v : ↑(Sph 2))
    (w : Homology (sub (X := ProdSp (Sph 2) (Sph 2)) (coverA v ∩ coverB v)) 2) :
    slitProdHTwoViaFst (homeoHomologyEquivInt (interProdHomeo v) 2 w)
      = Homology.mapInt (coverInterFstCM v) 2 w := by
  rw [homeoHomologyEquivInt_apply]
  show Homology.mapInt (prodFst (Sph 2) PuncPlane) 2
    (Homology.mapInt ⟨interProdHomeo v, (interProdHomeo v).continuous⟩ 2 w) = _
  rw [← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

end SKEFTHawking.SphereProdPuncturedPlaneInt
