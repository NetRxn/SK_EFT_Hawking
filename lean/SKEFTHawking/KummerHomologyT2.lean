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

/-- **Abstract kernel lemma.** For a surjective linear map `f : M → N` over a PID `R`, from a free
finite module of rank `2` onto a module of rank `1`, the kernel is `≅ R`: quotient rank-nullity
(`Submodule.finrank_quotient_add_finrank` + `M ⧸ ker f ≅ range f = N`) gives `finrank (ker f) = 1`;
a submodule of a free finite module over a PID is free, and free of rank `1` is `≅ R`. (Stated over a
general PID `R` — not fixed to `ℤ` — so the quotient's `Module R` instance is unique, avoiding the
`ℤ`-module `AddCommGroup.toIntModule` diamond that a `ℤ`-specialised statement triggers.) -/
theorem ker_iso_R_of_surjective {R : Type} [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
    {M : Type} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (hM : Module.finrank R M = 2) {N : Type} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (hN : Module.finrank R N = 1) :
    Nonempty (↥(LinearMap.ker f) ≃ₗ[R] R) := by
  have hquot : Module.finrank R (M ⧸ LinearMap.ker f) = 1 := by
    rw [f.quotKerEquivRange.finrank_eq, LinearMap.range_eq_top.mpr hf, finrank_top]; exact hN
  have hrn := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  have hrank : Module.finrank R (LinearMap.ker f) = 1 := by omega
  have b := Module.finBasis R (LinearMap.ker f)
  rw [hrank] at b
  exact ⟨b.equivFun.trans (LinearEquiv.funUnique (Fin 1) R R)⟩

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

/-! ### §2c. The first-coordinate collapse and the leg "master lemma" -/

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularMayerVietorisLES (subIncl ambIncl)
open SKEFTHawking.SingularMayerVietorisLESInt

/-- The first-coordinate collapse `p ↦ p.1.1` of a subset of `S¹×S¹` onto the first `S¹`. -/
def fstCM (T : Set ↑TwoTorus) : C(↥(sub (X := TwoTorus) T), ↑(Sph 1)) :=
  ⟨fun p => (p : ↑TwoTorus).1, continuous_fst.comp continuous_subtype_val⟩

/-- **The `A`-leg collapse is the first-coordinate pushforward** — the canonical `mapInt` form of
`legAEquivInt` (homeo seam + projection compose to the literal `p ↦ p.1.1`). Mirrors the S²×S² arc's
`coverAEquivInt_eq_mapInt`, one dimension lower. -/
theorem legAEquivInt_eq_mapInt (v : ↑(Sph 1)) (n : ℕ) (y : Homology (sub (covA v)) (n + 1)) :
    legAEquivInt v n y = Homology.mapInt (fstCM (covA v)) (n + 1) y := by
  show Homology.mapInt (prodFst (Sph 1) (sub ({v}ᶜ : Set ↑(Sph 1)))) (n + 1)
      (Homology.mapInt
        ⟨prodSetHomeo (Sph 1) (Sph 1) ({v}ᶜ : Set ↑(Sph 1)),
         (prodSetHomeo (Sph 1) (Sph 1) ({v}ᶜ : Set ↑(Sph 1))).continuous⟩ (n + 1) y)
      = _
  rw [← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- The `B`-leg collapse in canonical `mapInt` form. -/
theorem legBEquivInt_eq_mapInt (v : ↑(Sph 1)) (n : ℕ) (y : Homology (sub (covB v)) (n + 1)) :
    legBEquivInt v n y = Homology.mapInt (fstCM (covB v)) (n + 1) y := by
  show Homology.mapInt (prodFst (Sph 1) (sub ({antipode v}ᶜ : Set ↑(Sph 1)))) (n + 1)
      (Homology.mapInt
        ⟨prodSetHomeo (Sph 1) (Sph 1) ({antipode v}ᶜ : Set ↑(Sph 1)),
         (prodSetHomeo (Sph 1) (Sph 1) ({antipode v}ᶜ : Set ↑(Sph 1))).continuous⟩ (n + 1) y)
      = _
  rw [← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- **`legA ∘ iA∗ = firstCollapse`**: pushing an intersection class into the `A`-leg and collapsing =
collapsing the intersection's first coordinate directly (both are `p ↦ p.1.1`). -/
theorem covA_collapse_inter (v : ↑(Sph 1)) (w : Homology (sub (covA v ∩ covB v)) 1) :
    legAEquivInt v 0 (Homology.mapInt
        (subIncl (Set.inter_subset_left (s := covA v) (t := covB v))) 1 w)
      = Homology.mapInt (fstCM (covA v ∩ covB v)) 1 w := by
  rw [legAEquivInt_eq_mapInt, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- Same for the `B`-leg — the SAME first-coordinate collapse. -/
theorem covB_collapse_inter (v : ↑(Sph 1)) (w : Homology (sub (covA v ∩ covB v)) 1) :
    legBEquivInt v 0 (Homology.mapInt
        (subIncl (Set.inter_subset_right (s := covA v) (t := covB v))) 1 w)
      = Homology.mapInt (fstCM (covA v ∩ covB v)) 1 w := by
  rw [legBEquivInt_eq_mapInt, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-! ### §2d. The first-coordinate collapse is surjective (a `Punc 1` section) -/

open SKEFTHawking.SingularProdContractibleInt (prodFst_comp_prodSect homeoHomologyEquivInt_apply)

/-- A chosen nonzero point of `ℝ¹∖0 = Punc 1` (the section basepoint for the `S¹` projection). -/
noncomputable def puncPt : ↑(Punc 1) :=
  ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), by simp⟩

/-- **`mapInt (prodFst) : H₁(S¹×(ℝ∖0)) → H₁(S¹)` is surjective** — the projection has the section
`x ↦ (x, puncPt)` (`ℝ∖0` is nonempty). -/
theorem prodFst_punc_surjective :
    Function.Surjective (Homology.mapInt (prodFst (Sph 1) (Punc 1)) 1) := by
  intro z
  refine ⟨Homology.mapInt (prodSect (Sph 1) (Punc 1) puncPt) 1 z, ?_⟩
  have h : (Homology.mapInt (prodFst (Sph 1) (Punc 1)) 1).comp
      (Homology.mapInt (prodSect (Sph 1) (Punc 1) puncPt) 1) = LinearMap.id := by
    rw [← Homology.mapInt_comp, prodFst_comp_prodSect, Homology.mapInt_id]
  exact LinearMap.congr_fun h z

/-- **The first-coordinate collapse `H₁(covA∩covB) → H₁(S¹)` is surjective** — it factors as the
`Punc 1` projection after the intersection homeomorphism `intHomeo` (which preserves the first
coordinate), and the projection is surjective. -/
theorem firstCollapse_surjective (v : ↑(Sph 1)) :
    Function.Surjective (Homology.mapInt (fstCM (covA v ∩ covB v)) 1) := by
  have hrw : fstCM (covA v ∩ covB v)
      = (prodFst (Sph 1) (Punc 1)).comp ⟨intHomeo v, (intHomeo v).continuous⟩ := rfl
  rw [hrw, Homology.mapInt_comp]
  refine prodFst_punc_surjective.comp ?_
  intro z
  obtain ⟨y, hy⟩ := (homeoHomologyEquivInt (intHomeo v) 1).surjective z
  exact ⟨y, (homeoHomologyEquivInt_apply (intHomeo v) 1 y).symm.trans hy⟩

/-! ## §3. `H₂(S¹×S¹;ℤ) ≅ ℤ` — the torus fundamental class -/

/-- The first-coordinate collapse `H₁(covA∩covB) →ₗ[ℤ] H₁(S¹)` as a linear map. -/
noncomputable def firstCollapseLM (v : ↑(Sph 1)) :
    Homology (sub (covA v ∩ covB v)) 1 →ₗ[ℤ] Homology (Sph 1) 1 :=
  Homology.mapInt (fstCM (covA v ∩ covB v)) 1

/-- **`ker Δ₁ = ker (firstCollapse)`**: a class dies under the Mayer–Vietoris diagonal `Δ₁` iff it
dies under the first-coordinate collapse — because both legs collapse `iA∗`/`iB∗` to that same
collapse (`covA_collapse_inter`/`covB_collapse_inter`), and the legs are isomorphisms. -/
theorem ker_delta1_eq (v : ↑(Sph 1)) :
    LinearMap.ker (mvHomDiagInt (covA v) (covB v) 1) = LinearMap.ker (firstCollapseLM v) := by
  ext w
  rw [LinearMap.mem_ker, LinearMap.mem_ker, mvHomDiagInt_apply, Prod.mk_eq_zero, firstCollapseLM]
  constructor
  · rintro ⟨hA, _⟩
    rw [← covA_collapse_inter v w, hA, map_zero]
  · intro hF
    exact ⟨(legAEquivInt v 0).map_eq_zero_iff.mp ((covA_collapse_inter v w).trans hF),
      (legBEquivInt v 0).map_eq_zero_iff.mp ((covB_collapse_inter v w).trans hF)⟩

/-- **`δ : H₂(S¹×S¹) → H₁(covA∩covB)` is injective**: exactness at `H₂(X)` puts `ker δ = im Σ₂`,
but both legs have `H₂ = 0`, so `im Σ₂ = 0`. -/
theorem delta_injective (v : ↑(Sph 1)) :
    Function.Injective (mvDeltaInt (covA v) (covB v) 1 (covAB_cover v)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨u, u'⟩, hxeq⟩ := (mv_exact_ambientInt (covA v) (covB v) 1 (covAB_cover v) x).mp hx
  rw [← hxeq, legA_homology_two_eq_zero v u, legB_homology_two_eq_zero v u']
  simp

/-- **`H₂(S¹×S¹;ℤ) ≅ ker (firstCollapse)`**: `δ` embeds `H₂(X)` isomorphically onto `im δ = ker Δ₁`
(exactness at `H₁(covA∩covB)`), which equals `ker (firstCollapse)`. -/
noncomputable def torusTwoH2EquivKer (v : ↑(Sph 1)) :
    Homology TwoTorus 2 ≃ₗ[ℤ] ↥(LinearMap.ker (firstCollapseLM v)) :=
  (LinearEquiv.ofInjective (mvDeltaInt (covA v) (covB v) 1 (covAB_cover v)) (delta_injective v)).trans
    (LinearEquiv.ofEq _ _
      (((LinearMap.exact_iff.mp (mv_exact_interInt (covA v) (covB v) 1 (covAB_cover v))).symm).trans
        (ker_delta1_eq v)))

/-- **`H₂(S¹×S¹;ℤ) ≅ ℤ`** — the torus fundamental class, on `Sph 1 × Sph 1`. `ker (firstCollapse)`
is the kernel of a surjection from `H₁(covA∩covB) ≅ ℤ²` onto `H₁(S¹) ≅ ℤ`, hence `≅ ℤ`. -/
noncomputable def torusTwoH2EquivIntSph : Homology TwoTorus 2 ≃ₗ[ℤ] ℤ :=
  haveI : Module.Free ℤ (Homology (sub (covA (basePoint 1) ∩ covB (basePoint 1))) 1) :=
    Module.Free.of_equiv (interHOneEquivInt (basePoint 1)).symm
  haveI : Module.Finite ℤ (Homology (sub (covA (basePoint 1) ∩ covB (basePoint 1))) 1) :=
    Module.Finite.equiv (interHOneEquivInt (basePoint 1)).symm
  (torusTwoH2EquivKer (basePoint 1)).trans
    (ker_iso_R_of_surjective (R := ℤ)
      ((interHOneEquivInt (basePoint 1)).finrank_eq.trans (by simp))
      (firstCollapseLM (basePoint 1))
      (firstCollapse_surjective (basePoint 1))
      (circleH1EquivInt.finrank_eq.trans (by simp))).some

/-! ## §5. The `Circle × Circle` headlines (transported from `Sph 1 × Sph 1`) -/

open SKEFTHawking.KummerHomologyT4 (circleHomeoSph1)

/-- The product bridge `Circle × Circle ≃ₜ S¹ × S¹` (product of the two `circleHomeoSph1` factors)
identifying the actual `T² = Circle²` with the sphere-homology stack's `Sph 1 × Sph 1`. -/
noncomputable def prodCircleHomeo : (Circle × Circle) ≃ₜ (↑(Sph 1) × ↑(Sph 1)) :=
  circleHomeoSph1.prodCongr circleHomeoSph1

/-- **`H₂(S¹×S¹;ℤ) ≅ ℤ`** — the torus fundamental class, on the actual `T² = Circle × Circle`
(transported across `prodCircleHomeo`). A genuine iso: the codomain-`ℤ` is `ker Δ₁`, the class the
two arc generators of the doubly-punctured circle bound. -/
noncomputable def torusTwoH2EquivInt : Homology (TopCat.of (Circle × Circle)) 2 ≃ₗ[ℤ] ℤ :=
  (homeoHomologyEquivInt (X := TopCat.of (Circle × Circle)) (Y := TwoTorus) prodCircleHomeo 2).trans
    torusTwoH2EquivIntSph

end SKEFTHawking.KummerHomologyT2
