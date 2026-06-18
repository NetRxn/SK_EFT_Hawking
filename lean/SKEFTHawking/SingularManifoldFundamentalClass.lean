import Mathlib
import SKEFTHawking.SingularPairLES
import SKEFTHawking.SingularRelativeMV
import SKEFTHawking.SingularChartBridge
import SKEFTHawking.SingularEuclideanAcyclic
import SKEFTHawking.SingularConvexComplementRetract

/-!
# Phase 5q.F (w₂-foundation, brick 6e) — toward the fundamental class `[M]`

Building `Hₙ(M; ℤ/2) ≅ ℤ/2` for a closed `n`-manifold (Hatcher Lemma 3.27) on this phase's hand-rolled
singular ℤ/2 homology. The engine is the relative Mayer–Vietoris LES (`SingularRelativeMV`); the local
input is `Hₙ(M | x) ≅ ℤ/2` (`SingularChartBridge.manifoldLocalIso`). This file collects the
pair-LES reductions and the compactness induction.

First brick: the **pair-LES connecting isomorphism for an acyclic ambient**
`Hₙ₊₁(X, A) ≅ Hₙ(A)` when `Hₙ₊₁(X) = Hₙ(X) = 0` — the reduction `Hₙ(ℝⁿ, ℝⁿ∖A) ≅ H̃ₙ₋₁(ℝⁿ∖A)` used in the
convex base case. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES

namespace SKEFTHawking.SingularManifoldFundamentalClass

variable {X : TopCat}

/-- **The pair-LES connecting map is an isomorphism over an acyclic ambient**: if `Hₙ₊₁(X) = 0` and
`Hₙ(X) = 0`, then `δ : Hₙ₊₁(X, A) → Hₙ(A)` is bijective. (Injective: `ker δ = range j_* = 0` since
`Hₙ₊₁(X) = 0`. Surjective: `range δ = ker i_* = ⊤` since `Hₙ(X) = 0`.) The reduction
`Hₙ(ℝⁿ, ℝⁿ∖A) ≅ Hₙ₋₁(ℝⁿ∖A)`. -/
theorem connecting_bijective_of_acyclic (S : Set ↑X) (n : ℕ)
    (h1 : ∀ x : Homology X (n + 1), x = 0) (h0 : ∀ x : Homology X n, x = 0) :
    Function.Bijective (connecting S n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := (exact_homProj_connecting S n x).mp hx
    rw [← hy, h1 y, map_zero]
  · intro y
    exact (exact_connecting_homIncl S n y).mp (h0 _)

/-- The acyclic-ambient connecting isomorphism `Hₙ₊₁(X, A) ≃ₗ Hₙ(A)`. -/
noncomputable def connectingEquiv_of_acyclic (S : Set ↑X) (n : ℕ)
    (h1 : ∀ x : Homology X (n + 1), x = 0) (h0 : ∀ x : Homology X n, x = 0) :
    RelativeHomology S (n + 1) ≃ₗ[ZMod 2] Homology (sub S) n :=
  LinearEquiv.ofBijective (connecting S n) (connecting_bijective_of_acyclic S n h1 h0)

/-- **`ℝⁿ` is acyclic in positive degree**: `Hₖ₊₁(ℝⁿ; ℤ/2) = 0` (every cycle is a boundary, from the
straight-line contraction `SingularEuclideanAcyclic.cycle_mem_boundaries`). -/
theorem eucl_homology_zero (n k : ℕ) (x : Homology (SingularEuclideanAcyclic.Eucl n) (k + 1)) :
    x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
  exact SingularEuclideanAcyclic.cycle_mem_boundaries n k z (LinearMap.mem_ker.mp z.2)

/-- **The local relative homology of `ℝⁿ` rel a subset `A`** reduces to the subspace:
`Hₖ₊₂(ℝⁿ, A) ≅ Hₖ₊₁(A)` (the acyclic-ambient connecting iso, `n = m+2`). -/
noncomputable def euclRelHomologyEquiv (m : ℕ) (A : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
    (k : ℕ) :
    RelativeHomology A (k + 1 + 1) ≃ₗ[ZMod 2] Homology (sub A) (k + 1) :=
  connectingEquiv_of_acyclic A (k + 1) (eucl_homology_zero (m + 2) (k + 1))
    (eucl_homology_zero (m + 2) k)

/-- **The local homology of `ℝⁿ` rel a compact convex `A`** is `ℤ/2`: `Hₘ₊₂(ℝⁿ, ℝⁿ∖A) ≅ ℤ/2`
(`n = m+2`, `0 ∈ interior A`). The convex base case of Hatcher 3.27 — assembled from the acyclic
connecting iso, the convex-complement radial retract (`ℝⁿ∖A ≃ ℝⁿ∖0`), and the punctured/sphere
local model (`normalize` + `topSphereIso`), exactly as `localHomologyIso` does for a point. -/
noncomputable def euclConvexLocalHomologyIso (m : ℕ)
    {A : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + 2)))) :
    RelativeHomology (X := SingularEuclideanAcyclic.Eucl (m + 2)) Aᶜ (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  (euclRelHomologyEquiv m Aᶜ m).trans
    ((LinearEquiv.ofBijective _
        (SingularConvexComplementRetract.homology_map_inclMap_bijective hAc hAcomp hA0 m)).trans
      ((LinearEquiv.ofBijective _
          (SingularPuncturedRetract.homology_map_normalize_bijective (n := m + 2) m)).trans
        (SingularLineMinusPoint.topSphereIso m)))

end SKEFTHawking.SingularManifoldFundamentalClass
