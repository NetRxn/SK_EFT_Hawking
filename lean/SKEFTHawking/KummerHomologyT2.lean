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

/-! ## §1. The `Sph 1` MV cover of `T² = Sph 1 × Sph 1` and the leg collapses -/

open SKEFTHawking.SingularProdContractibleInt (ProdSp prodFst prodSect prodSetHomeo
  prodSetContractibleEquivInt homeoHomologyEquivInt)
open SKEFTHawking.SingularSphereAcyclic (Sph Apunc puncturedHomeo antipode ne_antipode)
open SKEFTHawking.SphereProdHOneInt (puncContraction slice_puncContraction_zero
  slice_puncContraction_one)
open SKEFTHawking.SingularLineMinusPointInt (circleH1EquivInt topSphereIsoInt augHInt)
open SKEFTHawking.SingularSphereBottom (basePoint)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

/-- `T² = S¹ × S¹` as the MV carrier (`Sph 1 × Sph 1`). -/
abbrev TwoTorus : TopCat := ProdSp (Sph 1) (Sph 1)

/-- The `A`-leg of the polar product cover: `S¹ × (S¹∖{v})` (full first factor). -/
abbrev covA (v : ↑(Sph 1)) : Set ↑TwoTorus :=
  (Set.univ : Set ↑(Sph 1)) ×ˢ ({v}ᶜ : Set ↑(Sph 1))

/-- The `B`-leg of the polar product cover: `S¹ × (S¹∖{−v})`. -/
abbrev covB (v : ↑(Sph 1)) : Set ↑TwoTorus :=
  (Set.univ : Set ↑(Sph 1)) ×ˢ ({antipode v}ᶜ : Set ↑(Sph 1))

/-- The polar product cover is an interior cover of `S¹×S¹` (both legs open; the second factors'
complements of `v ≠ −v` exhaust the circle). Same proof as the S²×S² arc, one dimension lower. -/
theorem covAB_cover (v : ↑(Sph 1)) :
    (⋃ U ∈ ({covA v, covB v} : Set (Set ↑TwoTorus)), interior U) = Set.univ := by
  have hA : IsOpen (covA v) := isOpen_univ.prod isOpen_compl_singleton
  have hB : IsOpen (covB v) := isOpen_univ.prod isOpen_compl_singleton
  rw [Set.biUnion_pair, hA.interior_eq, hB.interior_eq, ← Set.prod_union, ← Set.compl_inter,
    Set.eq_univ_iff_forall]
  intro x
  refine Set.mem_prod.mpr ⟨Set.mem_univ _, ?_⟩
  rw [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_singleton_iff]
  rintro ⟨rfl, h2⟩
  exact ne_antipode _ h2

/-- `Hₙ₊₁(S¹×(S¹∖{v}); ℤ) ≅ Hₙ₊₁(S¹;ℤ)` — the `A`-leg collapse at every positive degree (the
punctured circle is contractible, `puncContraction`). -/
noncomputable def legAEquivInt (v : ↑(Sph 1)) (n : ℕ) :
    Homology (sub (covA v)) (n + 1) ≃ₗ[ℤ] Homology (Sph 1) (n + 1) :=
  prodSetContractibleEquivInt (Sph 1) (Sph 1) ({v}ᶜ : Set ↑(Sph 1))
    ((puncturedHomeo 1 v).symm 0) (puncContraction 1 v)
    (slice_puncContraction_zero 1 v) (slice_puncContraction_one 1 v) n

/-- `Hₙ₊₁(S¹×(S¹∖{−v}); ℤ) ≅ Hₙ₊₁(S¹;ℤ)` — the `B`-leg collapse at the antipode. -/
noncomputable def legBEquivInt (v : ↑(Sph 1)) (n : ℕ) :
    Homology (sub (covB v)) (n + 1) ≃ₗ[ℤ] Homology (Sph 1) (n + 1) :=
  prodSetContractibleEquivInt (Sph 1) (Sph 1) ({antipode v}ᶜ : Set ↑(Sph 1))
    ((puncturedHomeo 1 (antipode v)).symm 0) (puncContraction 1 (antipode v))
    (slice_puncContraction_zero 1 (antipode v)) (slice_puncContraction_one 1 (antipode v)) n

/-- `H₂(S¹×(S¹∖{v}); ℤ) = 0`: the leg collapses onto `H₂(S¹;ℤ) = 0`. -/
theorem legA_homology_two_eq_zero (v : ↑(Sph 1)) (u : Homology (sub (covA v)) 2) : u = 0 :=
  (legAEquivInt v 1).map_eq_zero_iff.mp (KummerHomologyT4.circleH_high 0 (legAEquivInt v 1 u))

/-- `H₂(S¹×(S¹∖{−v}); ℤ) = 0` — the `B`-leg. -/
theorem legB_homology_two_eq_zero (v : ↑(Sph 1)) (u : Homology (sub (covB v)) 2) : u = 0 :=
  (legBEquivInt v 1).map_eq_zero_iff.mp (KummerHomologyT4.circleH_high 0 (legBEquivInt v 1 u))

/-! ## §2. The disconnected intersection `covA∩covB = S¹ × (S¹∖{v,−v}) ≅ S¹ ⊔ S¹` -/

open SKEFTHawking.SingularSphereAcyclic (equatorMap equatorMapInv equatorMapInv_comp_equatorMap
  equatorMap_comp_equatorMapInv)
open SKEFTHawking.SingularMayerVietorisLES (seamHomeo)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularPuncturedRetract (Punc)

/-- **The equatorial homeomorphism `S¹∖{v,−v} ≃ₜ ℝ¹∖0`** (packaging the banked `equatorMap`/
`equatorMapInv` continuous-map pair, whose composites are the identity, as a `Homeomorph`). The
doubly-punctured circle IS `ℝ∖0` — two disjoint rays. -/
noncomputable def equatorHomeo (v : ↑(Sph 1)) :
    ↑(sub (restr ({v}ᶜ : Set ↑(Sph 1)) ({antipode v}ᶜ))) ≃ₜ ↑(Punc 1) where
  toFun := equatorMap v
  invFun := equatorMapInv v
  left_inv x := ContinuousMap.congr_fun equatorMapInv_comp_equatorMap x
  right_inv y := ContinuousMap.congr_fun equatorMap_comp_equatorMapInv y
  continuous_toFun := (equatorMap v).continuous
  continuous_invFun := (equatorMapInv v).continuous

/-- **The doubly-punctured circle `S¹∖{v,−v} ≃ₜ ℝ¹∖0`**, in the direct-intersection presentation
`{v}ᶜ ∩ {−v}ᶜ` (bridged from the `restr` presentation across `seamHomeo`, then `equatorHomeo`). -/
noncomputable def dpcHomeo (v : ↑(Sph 1)) :
    ↑(sub (({v}ᶜ : Set ↑(Sph 1)) ∩ ({antipode v}ᶜ : Set ↑(Sph 1)))) ≃ₜ ↑(Punc 1) :=
  (seamHomeo ({v}ᶜ : Set ↑(Sph 1)) ({antipode v}ᶜ)).symm.trans (equatorHomeo v)

/-- The cover legs intersect in `S¹ × (S¹∖{v,−v})` (product-set intersection reassociation). -/
theorem covAB_inter (v : ↑(Sph 1)) :
    covA v ∩ covB v
      = (Set.univ : Set ↑(Sph 1)) ×ˢ (({v}ᶜ : Set ↑(Sph 1)) ∩ ({antipode v}ᶜ)) := by
  rw [Set.prod_inter_prod, Set.univ_inter]

/-- **The intersection `covA∩covB ≃ₜ S¹ × (ℝ∖0)`** — the disconnected doubly-punctured-circle factor
made explicit as `Punc 1`, ready to be clopen-split into the two arcs. -/
noncomputable def intHomeo (v : ↑(Sph 1)) :
    ↑(sub (covA v ∩ covB v)) ≃ₜ ↑(ProdSp (Sph 1) (Punc 1)) :=
  (Homeomorph.setCongr (covAB_inter v)).trans
    ((prodSetHomeo (Sph 1) (Sph 1) (({v}ᶜ : Set ↑(Sph 1)) ∩ ({antipode v}ᶜ))).trans
      ((Homeomorph.refl ↑(Sph 1)).prodCongr (dpcHomeo v)))

/-! ### §2a. The two arcs of `ℝ¹∖0` collapse: `Hₖ₊₁(S¹ × arc) ≅ Hₖ₊₁(S¹)` -/

open SKEFTHawking.SingularProdContractibleInt (homeoContraction slice_homeoContraction_zero
  slice_homeoContraction_one)
open SKEFTHawking.SingularStarConvexSlit (starConvexContraction slice_starConvexContraction_zero
  slice_starConvexContraction_one)
open SKEFTHawking.SingularLineMinusPoint (posSet posRay convex_posRay posFwd posBwd
  posBwd_comp_posFwd posFwd_comp_posBwd negFwd negBwd negBwd_comp_negFwd negFwd_comp_negBwd
  isClopen_posSet)

/-- `ℝ¹` as a `TopCat` (the ambient of the two convex half-line arcs). -/
abbrev R1 : TopCat := TopCat.of (EuclideanSpace ℝ (Fin 1))

/-- The chosen basepoint `1 ∈ posRay` of the positive half-line. -/
theorem posRayPt_mem : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) ∈ posRay := by
  show (0 : ℝ) < EuclideanSpace.single (0 : Fin 1) (1 : ℝ) 0; simp

/-- `posRay` is star-convex about `1` (convex + membership). -/
theorem starConvex_posRay :
    StarConvex ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) posRay :=
  convex_posRay.starConvex posRayPt_mem

/-- The straight-line contraction of the convex half-line `posRay` to `1`. -/
noncomputable def rayContraction :
    C(↑(sub (X := R1) posRay) × ↑unitInterval, ↑(sub (X := R1) posRay)) :=
  starConvexContraction starConvex_posRay

/-- The homeomorphism `↥posSet ≃ₜ ↥posRay` (forget/recover the redundant `≠ 0`). -/
noncomputable def posHomeo : ↑(sub posSet) ≃ₜ ↑(sub (X := R1) posRay) where
  toFun := posFwd
  invFun := posBwd
  left_inv x := ContinuousMap.congr_fun posBwd_comp_posFwd x
  right_inv y := ContinuousMap.congr_fun posFwd_comp_posBwd y
  continuous_toFun := posFwd.continuous
  continuous_invFun := posBwd.continuous

/-- The antipodal homeomorphism `↥posSetᶜ ≃ₜ ↥posSet` (`x ↦ −x` swaps arcs). -/
noncomputable def negHomeo : ↑(sub posSetᶜ) ≃ₜ ↑(sub posSet) where
  toFun := negFwd
  invFun := negBwd
  left_inv x := ContinuousMap.congr_fun negBwd_comp_negFwd x
  right_inv y := ContinuousMap.congr_fun negFwd_comp_negBwd y
  continuous_toFun := negFwd.continuous
  continuous_invFun := negBwd.continuous

/-- The contraction of the positive arc `posSet` (rayContraction transported across `posHomeo`). -/
noncomputable def posSetContraction :
    C(↑(sub posSet) × ↑unitInterval, ↑(sub posSet)) :=
  homeoContraction posHomeo rayContraction

/-- The contraction of the negative arc `posSetᶜ` (rayContraction transported across
`negHomeo.trans posHomeo`). -/
noncomputable def posSetComplContraction :
    C(↑(sub posSetᶜ) × ↑unitInterval, ↑(sub posSetᶜ)) :=
  homeoContraction (negHomeo.trans posHomeo) rayContraction

/-- **The positive-arc leg collapse** `Hₙ₊₁(S¹ × posSet; ℤ) ≅ Hₙ₊₁(S¹;ℤ)`. -/
noncomputable def arcPosEquivInt (n : ℕ) :
    Homology (sub (X := ProdSp (Sph 1) (Punc 1))
      ((Set.univ : Set ↑(Sph 1)) ×ˢ posSet)) (n + 1) ≃ₗ[ℤ] Homology (Sph 1) (n + 1) :=
  prodSetContractibleEquivInt (Sph 1) (Punc 1) posSet
    (posHomeo.symm ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), posRayPt_mem⟩)
    posSetContraction
    (slice_homeoContraction_zero posHomeo rayContraction
      (slice_starConvexContraction_zero starConvex_posRay))
    (slice_homeoContraction_one posHomeo rayContraction
      ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), posRayPt_mem⟩
      (slice_starConvexContraction_one starConvex_posRay posRayPt_mem)) n

/-- **The negative-arc leg collapse** `Hₙ₊₁(S¹ × posSetᶜ; ℤ) ≅ Hₙ₊₁(S¹;ℤ)`. -/
noncomputable def arcNegEquivInt (n : ℕ) :
    Homology (sub (X := ProdSp (Sph 1) (Punc 1))
      ((Set.univ : Set ↑(Sph 1)) ×ˢ posSetᶜ)) (n + 1) ≃ₗ[ℤ] Homology (Sph 1) (n + 1) :=
  prodSetContractibleEquivInt (Sph 1) (Punc 1) posSetᶜ
    ((negHomeo.trans posHomeo).symm ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), posRayPt_mem⟩)
    posSetComplContraction
    (slice_homeoContraction_zero (negHomeo.trans posHomeo) rayContraction
      (slice_starConvexContraction_zero starConvex_posRay))
    (slice_homeoContraction_one (negHomeo.trans posHomeo) rayContraction
      ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), posRayPt_mem⟩
      (slice_starConvexContraction_one starConvex_posRay posRayPt_mem)) n

/-! ### §2b. The clopen split `Hₖ(S¹×(ℝ∖0)) ≅ Hₖ(S¹) × Hₖ(S¹)` -/

open SKEFTHawking.SingularClopenSplitInt (splitHIntEquiv)

/-- The positive-arc clopen slice `S¹ × posSet` of `S¹ × (ℝ∖0)`. -/
abbrev arcU : Set ↑(ProdSp (Sph 1) (Punc 1)) := (Set.univ : Set ↑(Sph 1)) ×ˢ posSet

/-- `S¹ × posSet` is clopen (product of clopens). -/
theorem isClopen_arcU : IsClopen arcU := isClopen_univ.prod isClopen_posSet

/-- Its complement is `S¹ × posSetᶜ` (full first factor, so complementation is in the second). -/
theorem arcUcompl_eq :
    arcUᶜ = (Set.univ : Set ↑(Sph 1)) ×ˢ posSetᶜ := by
  ext p
  simp only [arcU, Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, true_and]

/-- **The intersection two-arc split** `Hₙ₊₁(covA∩covB; ℤ) ≅ Hₙ₊₁(S¹;ℤ) × Hₙ₊₁(S¹;ℤ)`: the
doubly-punctured circle is TWO disjoint arcs, so at every positive degree the intersection homology
is the direct sum of the two arc-legs, each collapsed onto `S¹`. -/
noncomputable def interArcSplitEquivInt (v : ↑(Sph 1)) (n : ℕ) :
    Homology (sub (covA v ∩ covB v)) (n + 1)
      ≃ₗ[ℤ] Homology (Sph 1) (n + 1) × Homology (Sph 1) (n + 1) :=
  (homeoHomologyEquivInt (intHomeo v) (n + 1)).trans
    ((splitHIntEquiv isClopen_arcU (n + 1)).symm.trans
      (LinearEquiv.prodCongr (arcPosEquivInt n)
        ((homeoHomologyEquivInt (Homeomorph.setCongr arcUcompl_eq) (n + 1)).trans
          (arcNegEquivInt n))))

/-- **`H₁(covA∩covB; ℤ) ≅ ℤ²`** — the two circle generators of the two arcs. -/
noncomputable def interHOneEquivInt (v : ↑(Sph 1)) :
    Homology (sub (covA v ∩ covB v)) 1 ≃ₗ[ℤ] ℤ × ℤ :=
  (interArcSplitEquivInt v 0).trans (LinearEquiv.prodCongr circleH1EquivInt circleH1EquivInt)

end SKEFTHawking.KummerHomologyT2
