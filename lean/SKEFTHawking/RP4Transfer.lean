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

/-- The covering map as a continuous map of `TopCat` carriers. -/
noncomputable def mkC : C(↑(TopCat.of S4), ↑(TopCat.of RP4)) :=
  ⟨Quotient.mk (MulAction.orbitRel ℤˣ S4), continuous_quotient_mk'⟩

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
    mapSimplex mkC (liftSimplex σ e₀ he) = σ := by
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

/-! ## §2. The transfer chain map `τ` — each simplex to the sum of its two lifts -/

/-- The canonical fiber point over a simplex's barycenter value. -/
noncomputable def outFiber {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) : S4 :=
  Quotient.out (rlP σ (bary n))

theorem mk_outFiber {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    Quotient.mk (MulAction.orbitRel ℤˣ S4) (outFiber σ) = rlP σ (bary n) :=
  Quotient.out_eq _

theorem mk_neg_outFiber {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    Quotient.mk (MulAction.orbitRel ℤˣ S4) ((-1 : ℤˣ) • outFiber σ) = rlP σ (bary n) :=
  (Quotient.sound (⟨(-1 : ℤˣ), rfl⟩ :
    (-1 : ℤˣ) • outFiber σ ∈ MulAction.orbit ℤˣ (outFiber σ))).trans (mk_outFiber σ)

/-- The `+`-lift (at the canonical fiber point). -/
noncomputable def liftPlus {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj (TopCat.of S4)).obj (op (SimplexCategory.mk n)) :=
  liftSimplex σ (outFiber σ) (mk_outFiber σ)

/-- The `−`-lift (at the antipodal fiber point). -/
noncomputable def liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj (TopCat.of S4)).obj (op (SimplexCategory.mk n)) :=
  liftSimplex σ ((-1 : ℤˣ) • outFiber σ) (mk_neg_outFiber σ)

/-- The antipodal pair is genuinely two points: `-y ≠ y` on the sphere. -/
theorem neg_ne_outFiber {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    (-1 : ℤˣ) • outFiber σ ≠ outFiber σ := by
  intro h
  have hcoe := congrArg Subtype.val h
  simp only [smul_coe] at hcoe
  rw [show ((((-1 : ℤˣ) : ℤ) : ℝ)) = -1 by norm_num, neg_one_smul] at hcoe
  have h2 : (outFiber σ : EuclideanSpace ℝ (Fin (4 + 1)))
      + (outFiber σ : EuclideanSpace ℝ (Fin (4 + 1))) = 0 := by
    nth_rewrite 1 [← hcoe]
    exact neg_add_cancel _
  have h3 : (2 : ℝ) • (outFiber σ : EuclideanSpace ℝ (Fin (4 + 1))) = 0 := by
    rw [two_smul]; exact h2
  have h0 : (outFiber σ : EuclideanSpace ℝ (Fin (4 + 1))) = 0 :=
    (smul_eq_zero.mp h3).resolve_left (by norm_num)
  have hnorm := mem_sphere_zero_iff_norm.mp (outFiber σ).2
  rw [h0, norm_zero] at hnorm
  exact one_ne_zero hnorm.symm

/-- **The two lifts are distinct** — they differ at the barycenter. -/
theorem liftPlus_ne_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    liftPlus σ ≠ liftMinus σ := by
  intro h
  have h1 := (liftSimplex_spec σ (outFiber σ) (mk_outFiber σ)).1
  have h2 := (liftSimplex_spec σ ((-1 : ℤˣ) • outFiber σ) (mk_neg_outFiber σ)).1
  have hval := congrArg
    (fun τ => ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n)) h
  simp only at hval
  rw [show liftSimplex σ (outFiber σ) (mk_outFiber σ) = liftPlus σ from rfl] at h1
  rw [show liftSimplex σ ((-1 : ℤˣ) • outFiber σ) (mk_neg_outFiber σ) = liftMinus σ from rfl]
    at h2
  rw [h1, h2] at hval
  exact neg_ne_outFiber σ hval.symm

@[simp] theorem mapSimplex_liftPlus {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    mapSimplex mkC (liftPlus σ) = σ :=
  mapSimplex_liftSimplex σ _ _

@[simp] theorem mapSimplex_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    mapSimplex mkC (liftMinus σ) = σ :=
  mapSimplex_liftSimplex σ _ _

/-- **The transfer chain map** `τ : Cₙ(ℝP⁴) → Cₙ(S⁴)`: each simplex to the sum of its two
lifts, at the fixed canonical fiber choice `Quotient.out`. (Choice-independence of the mod-2
sum is true but neither proven nor needed here — everything downstream uses the fixed choice.) -/
noncomputable def transferChain (n : ℕ) :
    SingularChain (TopCat.of RP4) n →ₗ[ZMod 2] SingularChain (TopCat.of S4) n :=
  Finsupp.linearCombination (ZMod 2)
    (fun σ => Finsupp.single (liftPlus σ) 1 + Finsupp.single (liftMinus σ) 1)

@[simp] theorem transferChain_single {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    transferChain n (Finsupp.single σ 1)
      = Finsupp.single (liftPlus σ) 1 + Finsupp.single (liftMinus σ) 1 := by
  rw [transferChain, Finsupp.linearCombination_single, one_smul]

/-- **`π_# ∘ τ = 0` (mod 2)**: both lifts push forward to the same simplex, and `σ + σ = 0`. -/
theorem mapChain_transferChain (n : ℕ) (c : SingularChain (TopCat.of RP4) n) :
    mapChain mkC n (transferChain n c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add c d hc hd => rw [map_add, map_add, hc, hd, add_zero]
  | single σ a =>
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with ha | ha
      · rw [ha, Finsupp.single_zero, map_zero, map_zero]
      · rw [ha, transferChain_single, map_add, mapChain_single, mapChain_single,
          mapSimplex_liftPlus, mapSimplex_liftMinus, ZModModule.add_self]

end SKEFTHawking.RP4Transfer