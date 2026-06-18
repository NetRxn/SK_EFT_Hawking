import Mathlib
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularMayerVietorisLES

/-!
# Phase 5q.F (w₂-foundation, brick 72c-3v) — connecting-naturality + Euclidean convex restriction iso

Two bricks toward the degree-`n` "determined by points" half of Hatcher 3.27.

* **Brick A** (`connecting_relIncl`): the pair-LES connecting map is natural under the inclusion of
  pairs. For `A ⊆ A'` (subspaces of an ambient `X`), the square
  `Hₙ₊₁(X, A) →[δ] Hₙ(A)`, `Hₙ₊₁(X, A) →[relIncl] Hₙ₊₁(X, A')`, `Hₙ(A) →[i_*] Hₙ(A')`,
  `Hₙ₊₁(X, A') →[δ] Hₙ(A')` commutes. The plain-inclusion analogue of the excision Barratt–Whitehead
  square `SingularMayerVietorisLES.inclRA_connecting` (no excision: the absolute lift chain is
  unchanged, and the bottom map is the genuine subspace inclusion `sub A → sub A'`).

* **Brick B** (`restrictToPoint_bijective`): for a compact convex `A ⊆ ℝⁿ` (`n = m+2`) with
  `0 ∈ interior A`, the restriction-to-the-origin map `restrictToPoint : Hₙ(ℝⁿ, ℝⁿ∖A) → Hₙ(ℝⁿ, ℝⁿ∖0)`
  (`= relIncl (Aᶜ ⊆ {0}ᶜ)`) is bijective. Via Brick A and the acyclic connecting iso
  `euclRelHomologyEquiv`, the relative restriction corresponds to the absolute inclusion-induced map
  `Hₙ₋₁(ℝⁿ∖A) → Hₙ₋₁(ℝⁿ∖0)`, bijective by the convex-complement radial retract
  (`SingularConvexComplementRetract.homology_map_inclMap_bijective`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularMayerVietorisLES

namespace SKEFTHawking.SingularConvexRestrictionIso

variable {X : TopCat}

/-! ## Brick A — pair-LES connecting-map naturality under inclusion of pairs -/

/-- **Connecting-map naturality** (plain pair inclusion): for `A ⊆ A'`, the connecting map of the
`(X, A')`-pair after the inclusion of pairs `Hₙ₊₁(X, A) → Hₙ₊₁(X, A')` equals the subspace-inclusion
pushforward `Hₙ(A) → Hₙ(A')` after the connecting map of `(X, A)`. The plain-inclusion analogue of the
excision Barratt–Whitehead square `SingularMayerVietorisLES.inclRA_connecting`. -/
theorem connecting_relIncl {A A' : Set ↑X} (h : A ⊆ A') (n : ℕ)
    (y : RelativeHomology A (n + 1)) :
    connecting A' n (relIncl h (n + 1) y)
      = Homology.map (subIncl h) n (connecting A n y) := by
  -- The chain-level bridge: including a `sub A`-chain into `X` via `sub A'` equals direct inclusion.
  have hbridge : ∀ (k : ℕ) (d : SingularChain (sub A) k),
      chainIncl A' k (mapChain (subIncl h) k d) = chainIncl A k d := by
    intro k d
    rw [← mapChain_ambIncl A', ← mapChain_comp,
      show (ambIncl A').comp (subIncl h) = ambIncl A from ContinuousMap.ext fun _ => rfl,
      mapChain_ambIncl]
  obtain ⟨c, rfl⟩ := relCycleToHom_surjective A n y
  rw [connecting_relCycleToHom]
  -- `c`'s underlying chain is also a lift chain for the larger subspace `A'`.
  have hc' : (c : SingularChain X (n + 1)) ∈ relCycleLift A' n := by
    show chainBoundary X n (c : SingularChain X (n + 1)) ∈ subspaceChains A' n
    obtain ⟨d, hd⟩ := Submodule.mem_comap.mp c.2
    exact ⟨mapChain (subIncl h) n d, by rw [hbridge, hd]⟩
  -- The inclusion-of-pairs map fixes the underlying absolute chain, so it lands in `relCycleToHom A'`.
  have hrel : relIncl h (n + 1) (relCycleToHom A n c)
      = relCycleToHom A' n ⟨(c : SingularChain X (n + 1)), hc'⟩ := by
    rw [relCycleToHom_apply, relIncl_mk, relCycleToHom_apply]
    refine congrArg (RelativeHomology.mk (S := A') (n + 1)) (Subtype.ext ?_)
    rw [relCyclesMap_coe]
    show relMapChain (ContinuousMap.id ↑X) _ (n + 1) (RelativeChain.mk A (n + 1) c)
      = RelativeChain.mk A' (n + 1) c
    rw [relMapChain_mk, mapChain_id]
  rw [hrel, connecting_relCycleToHom, connectingLift_apply, connectingLift_apply, Homology.map_mk]
  refine congrArg (Homology.mk (sub A') n) (Subtype.ext ?_)
  rw [cyclesMap_coe]
  apply chainIncl_injective A' n
  rw [hbridge, chainIncl_boundaryExtract, chainIncl_boundaryExtract]

/-! ## Brick B — Euclidean convex restriction iso -/

/-- **Euclidean convex restriction iso**: for a compact convex `A ⊆ ℝⁿ` (`n = m+2`) with
`0 ∈ interior A`, the restriction map `Hₙ(ℝⁿ, ℝⁿ∖A) → Hₙ(ℝⁿ, ℝⁿ∖0)` is bijective. The "determined by
points" half of Hatcher 3.27 for the convex base case. -/
theorem restrictToPoint_bijective (m : ℕ)
    {A : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + 2)))) :
    Function.Bijective
      (SingularManifoldFundamentalClass.restrictToPoint
        (X := SingularEuclideanAcyclic.Eucl (m + 2)) (mem_of_mem_nhds hA0) (m + 2)) := by
  set h : (Aᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ⊆ {0}ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (mem_of_mem_nhds hA0)) with hh
  -- `restrictToPoint` is the inclusion-of-pairs map `relIncl (Aᶜ ⊆ {0}ᶜ)`.
  have hrtp : SingularManifoldFundamentalClass.restrictToPoint
      (X := SingularEuclideanAcyclic.Eucl (m + 2)) (mem_of_mem_nhds hA0) (m + 2)
        = relIncl h (m + 2) := rfl
  rw [hrtp]
  -- The bottom map of the naturality square is the convex-complement inclusion, bijective by retract.
  have hbot : Function.Bijective (Homology.map (subIncl h) (m + 1)) :=
    SingularConvexComplementRetract.homology_map_inclMap_bijective hAc hAcomp hA0 m
  -- Both vertical connecting maps are isos over the acyclic ambient ℝⁿ (via `euclRelHomologyEquiv`,
  -- whose coercion is definitionally the pair-LES connecting map). Using the prebuilt equiv avoids a
  -- `whnf` blow-up that re-elaborating `connecting_bijective_of_acyclic` here would trigger.
  have hcA : Function.Bijective
      (SingularManifoldFundamentalClass.euclRelHomologyEquiv m Aᶜ m) :=
    (SingularManifoldFundamentalClass.euclRelHomologyEquiv m Aᶜ m).bijective
  have hc0 : Function.Bijective
      (SingularManifoldFundamentalClass.euclRelHomologyEquiv m {0}ᶜ m) :=
    (SingularManifoldFundamentalClass.euclRelHomologyEquiv m {0}ᶜ m).bijective
  -- The connecting map is definitionally the equiv coercion.
  have hdefA : ∀ z, SingularManifoldFundamentalClass.euclRelHomologyEquiv m Aᶜ m z
      = connecting (Aᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) (m + 1) z := fun _ => rfl
  have hdef0 : ∀ z, SingularManifoldFundamentalClass.euclRelHomologyEquiv m {0}ᶜ m z
      = connecting ({0}ᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) (m + 1) z := fun _ => rfl
  -- The naturality square (Brick A) phrased through the equivs.
  have hkey : ∀ y, SingularManifoldFundamentalClass.euclRelHomologyEquiv m {0}ᶜ m
      (relIncl h (m + 2) y)
      = Homology.map (subIncl h) (m + 1)
          (SingularManifoldFundamentalClass.euclRelHomologyEquiv m Aᶜ m y) := by
    intro y
    rw [hdef0, hdefA]
    exact connecting_relIncl h (m + 1) y
  constructor
  · -- Injectivity: chase `relIncl y = 0` through the three injective maps.
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : Homology.map (subIncl h) (m + 1)
        (SingularManifoldFundamentalClass.euclRelHomologyEquiv m Aᶜ m y) = 0 := by
      rw [← hkey, hy, map_zero]
    have h2 : SingularManifoldFundamentalClass.euclRelHomologyEquiv m Aᶜ m y = 0 :=
      hbot.injective (by rw [h1, map_zero])
    exact hcA.injective (by rw [h2, map_zero])
  · -- Surjectivity: pull `z` back through the three surjective maps.
    intro z
    obtain ⟨u, hu⟩ := hbot.surjective
      (SingularManifoldFundamentalClass.euclRelHomologyEquiv m {0}ᶜ m z)
    obtain ⟨y, hy⟩ := hcA.surjective u
    refine ⟨y, hc0.injective ?_⟩
    rw [hkey, hy, hu]

end SKEFTHawking.SingularConvexRestrictionIso
