import Mathlib
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularConvexRestrictionIso
import SKEFTHawking.SingularConvexRadialRetract
import SKEFTHawking.SingularPuncturedRetract
import SKEFTHawking.SingularSphereHighDegree
import SKEFTHawking.SingularLineMinusPoint
import SKEFTHawking.SingularGoodCompact

/-!
# Phase 5q.F (w₂-foundation, brick 72c-4g) — the all-dimensional convex base case `goodCompact`

For ANY convex compact `K ⊆ ℝⁿ` (`n = m+2`) and a point `O ∈ K` — **no interior-point assumption**,
so `K` may be lower-dimensional — `K` is `goodCompact (m+2) K`, i.e. it satisfies both halves of the
Hatcher 3.27 compactness property:

* **`vanishAbove (m+2) K`** (`vanishAbove_convexCompact`): `Hᵢ(ℝⁿ | K) = 0` for `i > n`. Mirrors
  `SingularManifoldFundamentalClass.euclConvexLocalHomology_high`, but swaps the full-dimensional gauge
  retract for the all-dimensional radial-from-`O` retract (brick 4f,
  `SingularConvexRadialRetract.homology_map_inclMapRadial_bijective`) and inserts a **translation**
  `Hₖ₊₁(ℝⁿ∖{O}) ≅ Hₖ₊₁(ℝⁿ∖0)` (the homeo `x ↦ x - O`) before the punctured/sphere local model.

* **`determinedByPoints (m+2) K`** (`determinedByPoints_convexCompact`): from the radial restriction
  iso `restrictToPoint_radial_bijective` (`Hₘ₊₂(ℝⁿ|K) → Hₘ₊₂(ℝⁿ|O)` bijective), which mirrors
  `SingularConvexRestrictionIso.restrictToPoint_bijective` with the radial retract `inclMapRadial`
  replacing the gauge retract in the connecting-naturality square.

Combined: `goodCompact_convexCompact`. This is the lower-dimensional convex base case the Hatcher 3.27
fundamental-class compactness induction (`SingularGoodCompact.goodCompact_biUnion`) stacks on.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularManifoldFundamentalClass

namespace SKEFTHawking.SingularConvexRadialBase

/-! ## The translation `ℝⁿ∖{O} ≃ₜ ℝⁿ∖0` and its homology iso -/

/-- A point `x ≠ O` translates to `x - O ≠ 0`. -/
theorem sub_ne_zero_of_punc {m : ℕ} {O : EuclideanSpace ℝ (Fin (m + 2))}
    (p : ↥({O}ᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2)))) :
    (p : EuclideanSpace ℝ (Fin (m + 2))) - O
      ∈ ({x : EuclideanSpace ℝ (Fin (m + 2)) | x ≠ 0}) := by
  have hp : (p : EuclideanSpace ℝ (Fin (m + 2))) ≠ O := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using p.2
  exact sub_ne_zero.mpr hp

/-- A point `y ≠ 0` translates back to `y + O ≠ O`. -/
theorem add_ne_O_of_punc {m : ℕ} {O : EuclideanSpace ℝ (Fin (m + 2))}
    (q : ↥({x : EuclideanSpace ℝ (Fin (m + 2)) | x ≠ 0}
        : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2)))) :
    (q : EuclideanSpace ℝ (Fin (m + 2))) + O ∈ ({O}ᶜ : Set (EuclideanSpace ℝ (Fin (m + 2)))) := by
  have hq : (q : EuclideanSpace ℝ (Fin (m + 2))) ≠ 0 := q.2
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  exact hq (by rw [add_eq_right] at h; exact h)

/-- The translation homeomorphism `sub ({O}ᶜ) ≃ₜ sub {x | x ≠ 0}` (`= Punc`), `x ↦ x - O`.
Hand-rolled (explicit `toFun`/`invFun`) to keep the homology-functor unification away from the
`Homeomorph.subRight` whnf; codomain is the literal punctured set `{x | x ≠ 0}` that `normalize` uses
(so the chain with `homology_map_normalize_bijective` needs no `{0}ᶜ`-vs-`Punc` defeq blow-up). -/
noncomputable def translateHomeo {m : ℕ} (O : EuclideanSpace ℝ (Fin (m + 2))) :
    ↥({O}ᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ≃ₜ
      ↥({x : EuclideanSpace ℝ (Fin (m + 2)) | x ≠ 0}
        : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) where
  toFun p := ⟨(p : EuclideanSpace ℝ (Fin (m + 2))) - O, sub_ne_zero_of_punc p⟩
  invFun q := ⟨(q : EuclideanSpace ℝ (Fin (m + 2))) + O, add_ne_O_of_punc q⟩
  left_inv p := Subtype.ext (by simp)
  right_inv q := Subtype.ext (by simp)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The translation as a continuous map `sub ({O}ᶜ) → sub {x | x ≠ 0}`. -/
noncomputable def translateMap {m : ℕ} (O : EuclideanSpace ℝ (Fin (m + 2))) :
    C(↑(sub ({O}ᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2)))),
      ↑(sub ({x : EuclideanSpace ℝ (Fin (m + 2)) | x ≠ 0}
        : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))))) :=
  ⟨translateHomeo O, (translateHomeo O).continuous⟩

/-- Its inverse continuous map. -/
noncomputable def translateMapInv {m : ℕ} (O : EuclideanSpace ℝ (Fin (m + 2))) :
    C(↑(sub ({x : EuclideanSpace ℝ (Fin (m + 2)) | x ≠ 0}
        : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2)))),
      ↑(sub ({O}ᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))))) :=
  ⟨(translateHomeo O).symm, (translateHomeo O).symm.continuous⟩

/-- **The translation induces a homology iso in every degree** `Hₖ(ℝⁿ∖{O}) ≅ Hₖ(ℝⁿ∖0)` — a
homeomorphism, so functoriality (`map_bijective_of_comp_id_all`) gives the iso. -/
theorem homology_map_translateMap_bijective {m : ℕ} (O : EuclideanSpace ℝ (Fin (m + 2))) (k : ℕ) :
    Function.Bijective (Homology.map (translateMap O) k) :=
  Homology.map_bijective_of_comp_id_all (translateMap O) (translateMapInv O)
    (ContinuousMap.ext fun x => (translateHomeo O).symm_apply_apply x)
    (ContinuousMap.ext fun x => (translateHomeo O).apply_symm_apply x)
    k

/-! ## (A) High-degree vanishing for a convex compact -/

/-- **`vanishAbove (m+2) K` for a convex compact `K`** (any dimension): `Hᵢ(ℝⁿ | K) = 0` for `i > m+2`.
Mirrors `euclConvexLocalHomology_high`, with the radial retract + translation in place of the gauge
retract; lands in `Hₖ₊₁(Sⁿ⁻¹) = 0` (`sphere_homology_high`). -/
theorem vanishAbove_convexCompact {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    {O : EuclideanSpace ℝ (Fin (m + 2))} (hOK : O ∈ K) :
    vanishAbove (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) K := by
  intro i hi x
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 + 1 := ⟨i - 2, by omega⟩
  -- Push `x` through the four injective maps of the retract chain, one `have` at a time, so the
  -- elaborator never builds the monolithic four-fold `LinearEquiv.trans` (whnf blow-up over ℝⁿ).
  -- Step 1: `Hₖ₊₂(ℝⁿ, ℝⁿ∖K) ≅ Hₖ₊₁(ℝⁿ∖K)` (acyclic connecting iso).
  set a₁ := euclRelHomologyEquiv m Kᶜ k x with ha₁
  -- Step 2: radial retract `Hₖ₊₁(ℝⁿ∖K) ≅ Hₖ₊₁(ℝⁿ∖{O})`.
  set a₂ := Homology.map (SingularConvexRadialRetract.inclMapRadial hOK) (k + 1) a₁ with ha₂
  -- Step 3: translation `Hₖ₊₁(ℝⁿ∖{O}) ≅ Hₖ₊₁(ℝⁿ∖0)`.
  set a₃ := Homology.map (translateMap O) (k + 1) a₂ with ha₃
  -- Step 4: deformation retract `Hₖ₊₁(ℝⁿ∖0) ≅ Hₖ₊₁(Sⁿ⁻¹)`, which vanishes in this degree.
  have h4 : Homology.map (SingularPuncturedRetract.normalize (n := m + 2)) (k + 1) a₃ = 0 :=
    SingularSphereHighDegree.sphere_homology_high (m + 1) (k + 1) (by omega) _
  have h3 : a₃ = 0 :=
    (SingularPuncturedRetract.homology_map_normalize_bijective (n := m + 2) k).injective
      (h4.trans (map_zero _).symm)
  have h2 : a₂ = 0 :=
    (homology_map_translateMap_bijective O (k + 1)).injective
      ((ha₃ ▸ h3).trans (map_zero _).symm)
  have h1 : a₁ = 0 :=
    (SingularConvexRadialRetract.homology_map_inclMapRadial_bijective hKconv hKcomp hOK k).injective
      ((ha₂ ▸ h2).trans (map_zero _).symm)
  exact (euclRelHomologyEquiv m Kᶜ k).injective ((ha₁ ▸ h1).trans (map_zero _).symm)

/-! ## (B) The radial restriction iso -/

/-- **The radial restriction iso**: for a convex compact `K ⊆ ℝⁿ` and `O ∈ K`, the restriction map
`restrictToPoint hOK (m+2) : Hₘ₊₂(ℝⁿ|K) → Hₘ₊₂(ℝⁿ|O)` is bijective. Mirrors
`SingularConvexRestrictionIso.restrictToPoint_bijective`, with the radial retract `inclMapRadial`
(`= subIncl (Kᶜ ⊆ {O}ᶜ)`) supplying the bottom map of the connecting-naturality square. -/
theorem restrictToPoint_radial_bijective {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    {O : EuclideanSpace ℝ (Fin (m + 2))} (hOK : O ∈ K) :
    Function.Bijective
      (SingularManifoldFundamentalClass.restrictToPoint
        (X := SingularEuclideanAcyclic.Eucl (m + 2)) (show O ∈ K from hOK) (m + 2)) := by
  set h : (Kᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ⊆ {O}ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hOK) with hh
  have hrtp : SingularManifoldFundamentalClass.restrictToPoint
      (X := SingularEuclideanAcyclic.Eucl (m + 2)) (show O ∈ K from hOK) (m + 2)
        = relIncl h (m + 2) := rfl
  rw [hrtp]
  have hbot : Function.Bijective (Homology.map (subIncl h) (m + 1)) :=
    SingularConvexRadialRetract.homology_map_inclMapRadial_bijective hKconv hKcomp hOK m
  have hcA : Function.Bijective
      (SingularManifoldFundamentalClass.euclRelHomologyEquiv m Kᶜ m) :=
    (SingularManifoldFundamentalClass.euclRelHomologyEquiv m Kᶜ m).bijective
  have hc0 : Function.Bijective
      (SingularManifoldFundamentalClass.euclRelHomologyEquiv m {O}ᶜ m) :=
    (SingularManifoldFundamentalClass.euclRelHomologyEquiv m {O}ᶜ m).bijective
  have hdefA : ∀ z, SingularManifoldFundamentalClass.euclRelHomologyEquiv m Kᶜ m z
      = connecting (Kᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) (m + 1) z := fun _ => rfl
  have hdef0 : ∀ z, SingularManifoldFundamentalClass.euclRelHomologyEquiv m {O}ᶜ m z
      = connecting ({O}ᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) (m + 1) z := fun _ => rfl
  have hkey : ∀ y, SingularManifoldFundamentalClass.euclRelHomologyEquiv m {O}ᶜ m
      (relIncl h (m + 2) y)
      = Homology.map (subIncl h) (m + 1)
          (SingularManifoldFundamentalClass.euclRelHomologyEquiv m Kᶜ m y) := by
    intro y
    rw [hdef0, hdefA]
    exact SingularConvexRestrictionIso.connecting_relIncl h (m + 1) y
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : Homology.map (subIncl h) (m + 1)
        (SingularManifoldFundamentalClass.euclRelHomologyEquiv m Kᶜ m y) = 0 := by
      rw [← hkey, hy, map_zero]
    have h2 : SingularManifoldFundamentalClass.euclRelHomologyEquiv m Kᶜ m y = 0 :=
      hbot.injective (by rw [h1, map_zero])
    exact hcA.injective (by rw [h2, map_zero])
  · intro z
    obtain ⟨u, hu⟩ := hbot.surjective
      (SingularManifoldFundamentalClass.euclRelHomologyEquiv m {O}ᶜ m z)
    obtain ⟨y, hy⟩ := hcA.surjective u
    refine ⟨y, hc0.injective ?_⟩
    rw [hkey, hy, hu]

/-! ## (C) `determinedByPoints` and the assembled `goodCompact` -/

/-- **`determinedByPoints (m+2) K` for a convex compact `K`** (any dimension): a class in `Hₘ₊₂(ℝⁿ|K)`
that restricts to `0` at every point of `K` is `0`. Restriction at the single point `O ∈ K` already
detects `0` (the radial restriction iso is injective). -/
theorem determinedByPoints_convexCompact {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    {O : EuclideanSpace ℝ (Fin (m + 2))} (hOK : O ∈ K) :
    determinedByPoints (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) K := by
  intro α hα
  exact (restrictToPoint_radial_bijective hKconv hKcomp hOK).injective
    (by rw [hα O hOK, map_zero])

/-- **The all-dimensional convex base case** (Hatcher 3.27): any convex compact `K ⊆ ℝⁿ` (`n = m+2`,
possibly lower-dimensional) with a point `O ∈ K` is `goodCompact (m+2) K`. The base case the
`SingularGoodCompact.goodCompact_biUnion` compactness induction stacks on. -/
theorem goodCompact_convexCompact {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    {O : EuclideanSpace ℝ (Fin (m + 2))} (hOK : O ∈ K) :
    SKEFTHawking.SingularGoodCompact.goodCompact
      (X := SingularEuclideanAcyclic.Eucl (m + 2)) (m + 2) K :=
  ⟨vanishAbove_convexCompact hKconv hKcomp hOK,
   determinedByPoints_convexCompact hKconv hKcomp hOK⟩

end SKEFTHawking.SingularConvexRadialBase
