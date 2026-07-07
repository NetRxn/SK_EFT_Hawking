/-
# Phase 5q.H (E1 CSC-PD tower, base-case B5) — chart-convex subspaces are integrally acyclic

Integral (`ZMod 2 → ℤ`) mirror of the homology-vanishing half of `SingularConvexSubAcyclic`:
`H_{k+1}(sub W;ℤ) = 0` for a chart-convex open `W ⊆ M`. The straight-line contraction of the convex
subspace kills its positive integral homology; the chart-restricted homeomorphism `sub W ≃ₜ sub C`
transports the vanishing. The contraction + homeomorphism are COEFFICIENT-AGNOSTIC (continuous maps, no
chains) and reused verbatim from the mod-2 module; only the two `Homology`-level vanishing lemmas are
re-proved over ℤ.

The `H₂ = H₁ = H₀ = 0` inputs of the base-case `(2,1)`/`(3,0)`/`D⁰` conjuncts.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConvexSubAcyclic
import SKEFTHawking.SingularHomotopyInvarianceInt
import SKEFTHawking.SingularEuclideanSphereInt
import SKEFTHawking.IntCapProductInt
import SKEFTHawking.SingularSphereHomologyInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularHomotopyInvarianceInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularConvexSubAcyclic
  (convexContraction chartSubHomeo slice_convexContraction_zero slice_convexContraction_one)

namespace SKEFTHawking.SingularConvexSubAcyclicInt

/-- **A convex subspace is integrally acyclic**: `H_{k+1}(sub C;ℤ) = 0` for `C` convex with `p₀ ∈ C`. -/
theorem homology_convexSub_eq_zeroInt {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : Convex ℝ C) {p₀ : EuclideanSpace ℝ (Fin n)} (hp₀ : p₀ ∈ C) (k : ℕ)
    (x : Homology (sub (X := SingularEuclideanAcyclic.Eucl n) C) (k + 1)) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk z : Homology _ (k + 1)) = Homology.mk _ (k + 1) z from rfl,
    SKEFTHawking.SingularCohomologyInt.Homology.mk_eq_zero]
  exact Submodule.mem_comap.mpr (by
    simpa using cycle_mem_boundaries_of_contractionInt (convexContraction hC hp₀) ⟨p₀, hp₀⟩
      (slice_convexContraction_zero hC hp₀) (slice_convexContraction_one hC hp₀)
      z.1 (LinearMap.mem_ker.mp z.2))

/-- **B5: a chart-convex open subspace of a manifold is integrally acyclic** — `H_{k+1}(sub W;ℤ) = 0`. -/
theorem homology_chartConvexSub_eq_zeroInt {M : TopCat} {m : ℕ}
    {U : Set ↑M} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hCconv : Convex ℝ C)
    {p₀ : EuclideanSpace ℝ (Fin (m + 2))} (hp₀ : p₀ ∈ C) (hCV : C ⊆ V)
    {W : Set ↑M} (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : ↑M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C))
    (k : ℕ) (x : Homology (sub W) (k + 1)) : x = 0 := by
  set φ := chartSubHomeo e hCV hWU hWe with hφ
  have hbij : Function.Bijective
      (Homology.mapInt (⟨φ, φ.continuous⟩ : C(↑(sub W),
        ↑(sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) C))) (k + 1)) :=
    SingularSphereHomologyInt.Homology.mapInt_bijective_of_comp_id_all
      (⟨φ, φ.continuous⟩ : C(↑(sub W), ↑(sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) C)))
      (⟨φ.symm, φ.symm.continuous⟩ :
        C(↑(sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) C), ↑(sub W)))
      (ContinuousMap.ext fun z => show φ.symm (φ z) = z from φ.symm_apply_apply z)
      (ContinuousMap.ext fun z => show φ (φ.symm z) = z from φ.apply_symm_apply z) (k + 1)
  exact hbij.injective (by
    rw [map_zero]
    exact homology_convexSub_eq_zeroInt hCconv hp₀ k _)

end SKEFTHawking.SingularConvexSubAcyclicInt
