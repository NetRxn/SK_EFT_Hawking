import Mathlib
import SKEFTHawking.RP4Covering
import SKEFTHawking.StdSimplexLocPath
import SKEFTHawking.SingularFunctoriality

/-!
# Phase 5q.G (B-arc, M2-b core) — the two-fold lift of `ℝP⁴`-simplices

Every singular simplex of `ℝP⁴` lifts uniquely through the antipodal covering (M2-a) once a
fiber point over its barycenter value is chosen — `Δⁿ` is simply connected and locally
path-connected (the M2-b prelude), so Mathlib's packaged
`IsCoveringMap.existsUnique_continuousMap_lifts` applies on the nose. The fiber over any point
is the antipodal pair, so each simplex has exactly two lifts — the transfer `τσ = lift₊ + lift₋`
of the Smith sequence (M2-c).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.RP4PointSet SKEFTHawking.RP4Covering
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.RP4Transfer

/-- The barycenter of the standard simplex. -/
noncomputable def bary (n : ℕ) : stdSimplex ℝ (Fin (n + 1)) :=
  ⟨fun _ => ((n : ℝ) + 1)⁻¹,
    fun _ => by positivity,
    by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      push_cast
      field_simp⟩

/-- The realization of an `ℝP⁴`-simplex. -/
noncomputable def rlP {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    C(stdSimplex ℝ (Fin (n + 1)), RP4) :=
  (TopCat.of RP4).toSSetObjEquiv (op (SimplexCategory.mk n)) σ

/-- **The fiber is the antipodal pair**: any two points over the same class differ by `±1`. -/
theorem fiber_pair {e y : S4}
    (h : Quotient.mk (MulAction.orbitRel ℤˣ S4) e
      = Quotient.mk (MulAction.orbitRel ℤˣ S4) y) :
    e = y ∨ e = (-1 : ℤˣ) • y := by
  obtain ⟨u, hu⟩ : e ∈ MulAction.orbit ℤˣ y := Quotient.eq''.mp h
  have hu' : u • y = e := hu
  rcases Int.units_eq_one_or u with h1 | h1
  · left; rw [h1, one_smul] at hu'; exact hu'.symm
  · right; rw [h1] at hu'; exact hu'.symm

/-- **The unique lift of an `ℝP⁴`-simplex** at a chosen fiber point over its barycenter value. -/
noncomputable def liftSimplex {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) (e₀ : S4)
    (he : Quotient.mk (MulAction.orbitRel ℤˣ S4) e₀ = rlP σ (bary n)) :
    (TopCat.toSSet.obj (TopCat.of S4)).obj (op (SimplexCategory.mk n)) :=
  ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n))).symm
    (rp4_isCoveringMap.existsUnique_continuousMap_lifts (rlP σ) (bary n) e₀ he).exists.choose

/-- The lift's defining properties, packaged: it sits over `σ` and hits `e₀` at the barycenter. -/
theorem liftSimplex_spec {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) (e₀ : S4)
    (he : Quotient.mk (MulAction.orbitRel ℤˣ S4) e₀ = rlP σ (bary n)) :
    ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n))
        (liftSimplex σ e₀ he)) (bary n) = e₀ ∧
      Quotient.mk (MulAction.orbitRel ℤˣ S4) ∘
        ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) (liftSimplex σ e₀ he))
        = rlP σ := by
  have hspec :=
    (rp4_isCoveringMap.existsUnique_continuousMap_lifts (rlP σ) (bary n) e₀ he).exists.choose_spec
  rw [liftSimplex, Equiv.apply_symm_apply]
  exact hspec

/-- **The lift sits over `σ`**: pushing forward along the covering recovers `σ`. -/
theorem mapSimplex_liftSimplex {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) (e₀ : S4)
    (he : Quotient.mk (MulAction.orbitRel ℤˣ S4) e₀ = rlP σ (bary n)) :
    mapSimplex (⟨Quotient.mk (MulAction.orbitRel ℤˣ S4), continuous_quotient_mk'⟩ :
        C(S4, RP4)) (liftSimplex σ e₀ he) = σ := by
  rw [mapSimplex, Equiv.symm_apply_eq]
  refine ContinuousMap.ext (fun d => ?_)
  have h := (liftSimplex_spec σ e₀ he).2
  exact congrFun h d

/-- **Uniqueness**: any simplex over `σ` hitting `e₀` at the barycenter IS the lift. -/
theorem liftSimplex_unique {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) (e₀ : S4)
    (he : Quotient.mk (MulAction.orbitRel ℤˣ S4) e₀ = rlP σ (bary n))
    (τ : (TopCat.toSSet.obj (TopCat.of S4)).obj (op (SimplexCategory.mk n)))
    (hτ0 : ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n) = e₀)
    (hτ : Quotient.mk (MulAction.orbitRel ℤˣ S4) ∘
      ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ) = rlP σ) :
    τ = liftSimplex σ e₀ he := by
  have huniq :=
    (rp4_isCoveringMap.existsUnique_continuousMap_lifts (rlP σ) (bary n) e₀ he).unique
      (y₁ := (TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ)
      (y₂ := (TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) (liftSimplex σ e₀ he))
      ⟨hτ0, hτ⟩ (liftSimplex_spec σ e₀ he)
  exact ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n))).injective huniq

end SKEFTHawking.RP4Transfer
