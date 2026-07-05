import Mathlib
import SKEFTHawking.SingularConvexRadialRetract
import SKEFTHawking.SingularFunctorialityInt

/-!
# Phase 5q.H (integral Substrate-G, E1) — the all-dimensional convex-complement radial retract (ℤ)

The **integer-coefficient** mirror of `SingularConvexRadialRetract.homology_map_inclMapRadial_bijective`.
For ANY convex compact `K ⊆ ℝⁿ` and a point `O ∈ K` (no interior-point assumption — `K` may be
lower-dimensional), the inclusion `f : ℝⁿ ∖ K ↪ ℝⁿ ∖ {O}` (`inclMapRadial`) induces an isomorphism on
`Hₖ₊₁(·; ℤ)`.

**All the geometry is reused verbatim** from the mod-2 module `SingularConvexRadialRetract`: the
continuous maps `inclMapRadial`, `pushMap`, and the homotopies `homotopyComplK`, `homotopyPunc` are
coefficient-independent `ContinuousMap`s. Only the final homology-functor step differs — it applies the
integral homotopy-equivalence bijectivity engine `SingularFunctorialityInt.Homology.mapInt_bijective_of_homotopyEquiv`
in place of the mod-2 `Homology.map_bijective_of_homotopyEquiv`. The slice-boundary witnesses are the
exact same `simp [htScale]` closures.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularEuclideanAcyclic
open SKEFTHawking.SingularConvexRadialRetract
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)

namespace SKEFTHawking.SingularConvexRadialRetractInt

variable {n : ℕ}

/-- **The all-dimensional convex-complement inclusion `f : ℝⁿ∖K ↪ ℝⁿ∖{O}` is an integral homology
isomorphism** (positive degree) for ANY convex compact `K` and `O ∈ K` — no interior-point assumption.
The radial push-out `g` (`pushMap`, with `R` from `K ⊆ closedBall O R`) is a homotopy inverse. The ℤ
mirror of `SingularConvexRadialRetract.homology_map_inclMapRadial_bijective`; reuses the same geometry,
swapping the homology functor for the integral one. -/
theorem homology_mapInt_inclMapRadial_bijective {K : Set (EuclideanSpace ℝ (Fin n))}
    {O : EuclideanSpace ℝ (Fin n)} (hKconv : Convex ℝ K) (hKcomp : IsCompact K) (hOK : O ∈ K)
    (k : ℕ) : Function.Bijective (Homology.mapInt (inclMapRadial hOK) (k + 1)) := by
  obtain ⟨R, hRpos, hKR⟩ := hKcomp.isBounded.subset_closedBall_lt 0 O
  refine SingularFunctorialityInt.Homology.mapInt_bijective_of_homotopyEquiv
    (inclMapRadial hOK) (pushMap R hKR)
    (homotopyComplK hKconv R hOK) ?_ ?_ (homotopyPunc R) ?_ ?_ k
  · refine ContinuousMap.ext fun p => Subtype.ext ?_
    show O + htScale O R ((0 : unitInterval) : ℝ) (p : EuclideanSpace ℝ (Fin n)) • _
      = O + rscale O R (p : EuclideanSpace ℝ (Fin n)) • _
    simp [htScale, inclMapRadial, Set.inclusion]
  · refine ContinuousMap.ext fun p => Subtype.ext ?_
    show O + htScale O R ((1 : unitInterval) : ℝ) (p : EuclideanSpace ℝ (Fin n)) • _
      = (p : EuclideanSpace ℝ (Fin n))
    simp [htScale]
  · refine ContinuousMap.ext fun q => Subtype.ext ?_
    show O + htScale O R ((0 : unitInterval) : ℝ) (q : EuclideanSpace ℝ (Fin n)) • _
      = O + rscale O R (q : EuclideanSpace ℝ (Fin n)) • _
    simp [htScale]
  · refine ContinuousMap.ext fun q => Subtype.ext ?_
    show O + htScale O R ((1 : unitInterval) : ℝ) (q : EuclideanSpace ℝ (Fin n)) • _
      = (q : EuclideanSpace ℝ (Fin n))
    simp [htScale]

end SKEFTHawking.SingularConvexRadialRetractInt
