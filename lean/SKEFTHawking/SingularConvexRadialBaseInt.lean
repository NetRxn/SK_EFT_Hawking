import Mathlib
import SKEFTHawking.SingularGoodCompactInt
import SKEFTHawking.SingularConvexRadialRetractInt
import SKEFTHawking.SingularSphereHighDegreeInt
import SKEFTHawking.SingularRelativeFunctorialityInt
import SKEFTHawking.SingularLocalHomologyInt
import SKEFTHawking.SingularConvexRadialBase

/-!
# Phase 5q.H (integral Substrate-G, E1) — the all-dimensional convex base case `goodCompactInt`

The **integer-coefficient** mirror of `SingularConvexRadialBase.goodCompact_convexCompact`. For ANY
convex compact `K ⊆ ℝⁿ` (`n = m+2`) and a point `O ∈ K` — no interior-point assumption, so `K` may be
lower-dimensional — `K` is `SingularGoodCompactInt.goodCompactInt (m+2) K`, i.e. it satisfies both
halves of the ℤ Hatcher 3.27 compactness property:

* **`vanishAboveInt (m+2) K`** (`vanishAboveInt_convexCompact`): `Hᵢ(ℝⁿ | K;ℤ) = 0` for `i > n`. The
  radial-from-`O` retract (brick, `SingularConvexRadialRetractInt.homology_mapInt_inclMapRadial_bijective`)
  + a **translation** `Hₖ₊₁(ℝⁿ∖{O};ℤ) ≅ Hₖ₊₁(ℝⁿ∖0;ℤ)` (`x ↦ x - O`) + the punctured/sphere local model
  land in `Hₖ₊₁(Sⁿ⁻¹;ℤ) = 0` (`SingularSphereHighDegreeInt.sphere_homology_high`).

* **`determinedByPointsInt (m+2) K`** (`determinedByPointsInt_convexCompact`): from the radial
  restriction iso `restrictToPointInt_radial_bijective` (`Hₘ₊₂(ℝⁿ|K;ℤ) → Hₘ₊₂(ℝⁿ|O;ℤ)` bijective), which
  uses the integral connecting-naturality square `connectingInt_relInclInt`.

Combined: `goodCompactInt_convexCompact`. The lower-dimensional convex base case the ℤ Hatcher 3.27
fundamental-class induction stacks on. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularLocalHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.IntOrientationSection (relInclInt restrictToPointInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl subIncl mapSimplex_ambIncl)
open SKEFTHawking.SingularConvexRadialBase (translateMap translateMapInv translateHomeo)

namespace SKEFTHawking.SingularConvexRadialBaseInt

variable {X : TopCat}

/-! ## §0. The chainIncl–mapChainInt bridge and the acyclic connecting iso -/

/-- **chainIncl–mapChainInt bridge** (ℤ): `mapChainInt (ambIncl S) = chainIncl S`. The ℤ mirror of
`SingularMayerVietorisLES.mapChain_ambIncl`. -/
theorem mapChainInt_ambIncl (S : Set ↑X) (n : ℕ) :
    mapChainInt (ambIncl S) n = chainIncl S n := by
  refine LinearMap.ext fun c => ?_
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single σ a => rw [mapChainInt_single, chainIncl_single, mapSimplex_ambIncl]

/-- **The acyclic-ambient connecting isomorphism over `ℝⁿ`** (ℤ): `Hₖ₊₂(ℝⁿ, A;ℤ) ≃ₗ Hₖ₊₁(A;ℤ)`, the
integral mirror of `SingularManifoldFundamentalClass.euclRelHomologyEquiv`. `connectingInt` is bijective
because `ℝⁿ` is acyclic in positive degree (`eucl_homology_trivialInt`). -/
noncomputable def euclRelHomologyEquivInt (m : ℕ)
    (A : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) (k : ℕ) :
    RelHomologyInt A (k + 1 + 1) ≃ₗ[ℤ] Homology (sub A) (k + 1) :=
  LinearEquiv.ofBijective (connectingInt A (k + 1))
    (connectingInt_bijective_of_acyclic A (k + 1)
      (eucl_homology_trivialInt (m + 2) (k + 1)) (eucl_homology_trivialInt (m + 2) k))

/-! ## §1. Brick A — connecting-map naturality under the integral inclusion of pairs -/

/-- **Connecting-map naturality** (ℤ, plain pair inclusion): for `A ⊆ A'`, the connecting map of the
`(X, A')`-pair after the inclusion of pairs `Hₙ₊₁(X, A;ℤ) → Hₙ₊₁(X, A';ℤ)` equals the subspace-inclusion
pushforward `Hₙ(A;ℤ) → Hₙ(A';ℤ)` after the connecting map of `(X, A)`. The ℤ mirror of
`SingularConvexRestrictionIso.connecting_relIncl`. -/
theorem connectingInt_relInclInt {A A' : Set ↑X} (h : A ⊆ A') (n : ℕ)
    (y : RelHomologyInt A (n + 1)) :
    connectingInt A' n (relInclInt h (n + 1) y)
      = Homology.mapInt (subIncl h) n (connectingInt A n y) := by
  have hbridge : ∀ (k : ℕ) (d : SingularChainInt (sub A) k),
      chainIncl A' k (mapChainInt (subIncl h) k d) = chainIncl A k d := by
    intro k d
    rw [← mapChainInt_ambIncl A', ← mapChainInt_comp,
      show (ambIncl A').comp (subIncl h) = ambIncl A from ContinuousMap.ext fun _ => rfl,
      mapChainInt_ambIncl]
  obtain ⟨c, rfl⟩ := relCycleToHom_surjective A n y
  rw [connectingInt_relCycleToHom]
  have hc' : (c : SingularChainInt X (n + 1)) ∈ relCycleLift A' n := by
    show chainBoundary X n (c : SingularChainInt X (n + 1)) ∈ subspaceChainsInt A' n
    obtain ⟨d, hd⟩ := Submodule.mem_comap.mp c.2
    exact ⟨mapChainInt (subIncl h) n d, by rw [hbridge, hd]⟩
  have hrel : relInclInt h (n + 1) (relCycleToHom A n c)
      = relCycleToHom A' n ⟨(c : SingularChainInt X (n + 1)), hc'⟩ := by
    rw [relCycleToHom_apply, relInclInt, RelHomologyInt.mk, RelHomologyInt.map_mk,
      relCycleToHom_apply]
    refine congrArg (RelHomologyInt.mk (S := A') (n + 1)) (Subtype.ext ?_)
    rw [relCyclesMapInt_coe]
    show relMapChainInt (ContinuousMap.id ↑X) _ (n + 1) (RelativeChainInt.mk A (n + 1) c)
      = RelativeChainInt.mk A' (n + 1) c
    rw [relMapChainInt_mk, mapChainInt_id]
  rw [hrel, connectingInt_relCycleToHom, connectingLift_apply, connectingLift_apply,
    Homology.mapInt_mk]
  refine congrArg (Homology.mk (sub A') n) (Subtype.ext ?_)
  rw [cyclesMapInt_coe]
  apply chainIncl_injective A' n
  rw [hbridge, chainIncl_boundaryExtract, chainIncl_boundaryExtract]

/-! ## §2. The translation `ℝⁿ∖{O} ≃ₜ ℝⁿ∖0` on integral homology -/

/-- **The translation induces an integral homology iso in every degree** `Hₖ(ℝⁿ∖{O};ℤ) ≅ Hₖ(ℝⁿ∖0;ℤ)`.
Reuses the mod-2 translation homeomorphism geometry (`translateMap`/`translateMapInv`/`translateHomeo`,
`x ↦ x - O`); the iso follows from integral functoriality (`mapInt_bijective_of_comp_id_all`). -/
theorem homology_mapInt_translateMap_bijective {m : ℕ}
    (O : EuclideanSpace ℝ (Fin (m + 2))) (k : ℕ) :
    Function.Bijective (Homology.mapInt (translateMap O) k) :=
  SingularSphereHomologyInt.Homology.mapInt_bijective_of_comp_id_all (translateMap O)
    (translateMapInv O)
    (ContinuousMap.ext fun x => (translateHomeo O).symm_apply_apply x)
    (ContinuousMap.ext fun x => (translateHomeo O).apply_symm_apply x)
    k

/-! ## §3. (A) High-degree vanishing for a convex compact -/

/-- **`vanishAboveInt (m+2) K` for a convex compact `K`** (any dimension): `Hᵢ(ℝⁿ | K;ℤ) = 0` for
`i > m+2`. The ℤ mirror of `SingularConvexRadialBase.vanishAbove_convexCompact`. -/
theorem vanishAboveInt_convexCompact {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    {O : EuclideanSpace ℝ (Fin (m + 2))} (hOK : O ∈ K) :
    SingularGoodCompactInt.vanishAboveInt
      (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) K := by
  intro i hi x
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 + 1 := ⟨i - 2, by omega⟩
  set a₁ := euclRelHomologyEquivInt m Kᶜ k x with ha₁
  set a₂ := Homology.mapInt (SingularConvexRadialRetract.inclMapRadial hOK) (k + 1) a₁ with ha₂
  set a₃ := Homology.mapInt (translateMap O) (k + 1) a₂ with ha₃
  have h4 : Homology.mapInt (SingularPuncturedRetract.normalize (n := m + 2)) (k + 1) a₃ = 0 :=
    SingularSphereHighDegreeInt.sphere_homology_high (m + 1) (k + 1) (by omega) _
  have h3 : a₃ = 0 :=
    (SingularPuncturedRetractInt.homology_mapInt_normalize_bijective (m + 2) k).injective
      (h4.trans (map_zero _).symm)
  have h2 : a₂ = 0 :=
    (homology_mapInt_translateMap_bijective O (k + 1)).injective
      ((ha₃ ▸ h3).trans (map_zero _).symm)
  have h1 : a₁ = 0 :=
    (SingularConvexRadialRetractInt.homology_mapInt_inclMapRadial_bijective hKconv hKcomp hOK k).injective
      ((ha₂ ▸ h2).trans (map_zero _).symm)
  exact (euclRelHomologyEquivInt m Kᶜ k).injective ((ha₁ ▸ h1).trans (map_zero _).symm)

/-! ## §4. (B) The radial restriction iso -/

/-- **The radial restriction iso** (ℤ): for a convex compact `K ⊆ ℝⁿ` and `O ∈ K`, the restriction map
`restrictToPointInt hOK (m+2) : Hₘ₊₂(ℝⁿ|K;ℤ) → Hₘ₊₂(ℝⁿ|O;ℤ)` is bijective. The ℤ mirror of
`SingularConvexRadialBase.restrictToPoint_radial_bijective`, with the radial retract `inclMapRadial`
supplying the bottom map of the integral connecting-naturality square. -/
theorem restrictToPointInt_radial_bijective {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    {O : EuclideanSpace ℝ (Fin (m + 2))} (hOK : O ∈ K) :
    Function.Bijective
      (restrictToPointInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (show O ∈ K from hOK)
        (m + 2)) := by
  set h : (Kᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ⊆ {O}ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hOK) with hh
  have hrtp : restrictToPointInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (show O ∈ K from hOK)
      (m + 2) = relInclInt h (m + 2) := rfl
  rw [hrtp]
  have hbot : Function.Bijective (Homology.mapInt (subIncl h) (m + 1)) :=
    SingularConvexRadialRetractInt.homology_mapInt_inclMapRadial_bijective hKconv hKcomp hOK m
  have hcA : Function.Bijective (euclRelHomologyEquivInt m Kᶜ m) :=
    (euclRelHomologyEquivInt m Kᶜ m).bijective
  have hc0 : Function.Bijective (euclRelHomologyEquivInt m {O}ᶜ m) :=
    (euclRelHomologyEquivInt m {O}ᶜ m).bijective
  have hdefA : ∀ z, euclRelHomologyEquivInt m Kᶜ m z
      = connectingInt (Kᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) (m + 1) z := fun _ => rfl
  have hdef0 : ∀ z, euclRelHomologyEquivInt m {O}ᶜ m z
      = connectingInt ({O}ᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) (m + 1) z := fun _ => rfl
  have hkey : ∀ y, euclRelHomologyEquivInt m {O}ᶜ m (relInclInt h (m + 2) y)
      = Homology.mapInt (subIncl h) (m + 1) (euclRelHomologyEquivInt m Kᶜ m y) := by
    intro y
    rw [hdef0, hdefA]
    exact connectingInt_relInclInt h (m + 1) y
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : Homology.mapInt (subIncl h) (m + 1) (euclRelHomologyEquivInt m Kᶜ m y) = 0 := by
      rw [← hkey, hy, map_zero]
    have h2 : euclRelHomologyEquivInt m Kᶜ m y = 0 :=
      hbot.injective (by rw [h1, map_zero])
    exact hcA.injective (by rw [h2, map_zero])
  · intro z
    obtain ⟨u, hu⟩ := hbot.surjective (euclRelHomologyEquivInt m {O}ᶜ m z)
    obtain ⟨y, hy⟩ := hcA.surjective u
    refine ⟨y, hc0.injective ?_⟩
    rw [hkey, hy, hu]

/-! ## §5. (C) `determinedByPointsInt` and the assembled `goodCompactInt` -/

/-- **`determinedByPointsInt (m+2) K` for a convex compact `K`** (any dimension, ℤ): a class in
`Hₘ₊₂(ℝⁿ|K;ℤ)` that restricts to `0` at every point of `K` is `0`. Restriction at the single point
`O ∈ K` already detects `0` (the radial restriction iso is injective). Mirror of
`SingularConvexRadialBase.determinedByPoints_convexCompact`. -/
theorem determinedByPointsInt_convexCompact {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    {O : EuclideanSpace ℝ (Fin (m + 2))} (hOK : O ∈ K) :
    SingularGoodCompactInt.determinedByPointsInt
      (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) K := by
  intro α hα
  exact (restrictToPointInt_radial_bijective hKconv hKcomp hOK).injective
    (by rw [hα O hOK, map_zero])

/-- **The all-dimensional convex base case** (ℤ, Hatcher 3.27): any convex compact `K ⊆ ℝⁿ` (`n = m+2`,
possibly lower-dimensional) with a point `O ∈ K` is `goodCompactInt (m+2) K`. The base case the ℤ
fundamental-class compactness induction stacks on. Mirror of
`SingularConvexRadialBase.goodCompact_convexCompact`. -/
theorem goodCompactInt_convexCompact {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    {O : EuclideanSpace ℝ (Fin (m + 2))} (hOK : O ∈ K) :
    SingularGoodCompactInt.goodCompactInt
      (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) K :=
  ⟨vanishAboveInt_convexCompact hKconv hKcomp hOK,
   determinedByPointsInt_convexCompact hKconv hKcomp hOK⟩

end SKEFTHawking.SingularConvexRadialBaseInt
