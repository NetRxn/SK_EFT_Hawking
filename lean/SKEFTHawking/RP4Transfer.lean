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

/-! ## §3. The transfer is a chain map — faces of the lift-pair are the lift-pair of the face -/

/-- **Two lifts of the same simplex agreeing anywhere are equal** — covering uniqueness on the
preconnected simplex (`IsCoveringMap.eq_of_comp_eq`). -/
theorem liftSimplex_eq_of_agree {n : ℕ}
    (τ τ' : (TopCat.toSSet.obj (TopCat.of S4)).obj (op (SimplexCategory.mk n)))
    (hover : mapSimplex mkC τ = mapSimplex mkC τ')
    (d : stdSimplex ℝ (Fin (n + 1)))
    (hd : ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ) d
      = ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ') d) : τ = τ' := by
  have hcomp : Quotient.mk (MulAction.orbitRel ℤˣ S4) ∘
      ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ)
      = Quotient.mk (MulAction.orbitRel ℤˣ S4) ∘
        ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ') := by
    have h1 := congrArg ((TopCat.of RP4).toSSetObjEquiv (op (SimplexCategory.mk n))) hover
    rw [mapSimplex, mapSimplex, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    exact congrArg DFunLike.coe h1
  have := rp4_isCoveringMap.eq_of_comp_eq
    (((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ)).continuous
    (((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ')).continuous
    hcomp d hd
  exact ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n))).injective
    (ContinuousMap.coe_injective this)

/-- A face of a lift sits over the corresponding face. -/
theorem mapSimplex_face_liftPlus {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2)) :
    mapSimplex mkC (SKEFTHawking.SingularCohomologyMod2.face i (liftPlus σ))
      = SKEFTHawking.SingularCohomologyMod2.face i σ := by
  rw [← face_mapSimplex, mapSimplex_liftPlus]

theorem mapSimplex_face_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2)) :
    mapSimplex mkC (SKEFTHawking.SingularCohomologyMod2.face i (liftMinus σ))
      = SKEFTHawking.SingularCohomologyMod2.face i σ := by
  rw [← face_mapSimplex, mapSimplex_liftMinus]

/-- **A face of a lift is one of the two lifts of the face.** -/
theorem face_lift_mem_pair {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2))
    (τ : (TopCat.toSSet.obj (TopCat.of S4)).obj (op (SimplexCategory.mk (n + 1))))
    (hτ : mapSimplex mkC τ = σ) :
    SKEFTHawking.SingularCohomologyMod2.face i τ
        = liftPlus (SKEFTHawking.SingularCohomologyMod2.face i σ) ∨
      SKEFTHawking.SingularCohomologyMod2.face i τ
        = liftMinus (SKEFTHawking.SingularCohomologyMod2.face i σ) := by
  set F := SKEFTHawking.SingularCohomologyMod2.face i σ with hF
  set τF := SKEFTHawking.SingularCohomologyMod2.face i τ with hτF
  have hover : mapSimplex mkC τF = F := by
    rw [hτF, ← face_mapSimplex, hτ]
  -- `rlP F = mk ∘ realize τF` (the over-property at the map level)
  have h1 : rlP F = mkC.comp ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τF) := by
    rw [rlP, ← hover, mapSimplex, Equiv.apply_symm_apply]
  set y := ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τF) (bary n) with hy
  have hmk : Quotient.mk (MulAction.orbitRel ℤˣ S4) y = rlP F (bary n) :=
    (congrFun (congrArg DFunLike.coe h1) (bary n)).symm
  have hcirc : Quotient.mk (MulAction.orbitRel ℤˣ S4) ∘
      ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τF) = rlP F :=
    (congrArg DFunLike.coe h1).symm
  have hpair := fiber_pair (hmk.trans (mk_outFiber F).symm)
  rcases hpair with hcase | hcase
  · left
    exact liftSimplex_unique F (outFiber F) (mk_outFiber F) τF (hy ▸ hcase) hcirc
  · right
    exact liftSimplex_unique F ((-1 : ℤˣ) • outFiber F) (mk_neg_outFiber F) τF
      (hy ▸ hcase) hcirc

/-- **Faces of the two lifts are distinct** — else the lifts agree at a face-embedded point,
forcing them equal by covering uniqueness, contradicting the barycenter separation. -/
theorem face_liftPlus_ne_face_liftMinus {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2)) :
    SKEFTHawking.SingularCohomologyMod2.face i (liftPlus σ)
      ≠ SKEFTHawking.SingularCohomologyMod2.face i (liftMinus σ) := by
  intro h
  refine liftPlus_ne_liftMinus σ ?_
  refine liftSimplex_eq_of_agree (liftPlus σ) (liftMinus σ)
    ((mapSimplex_liftPlus σ).trans (mapSimplex_liftMinus σ).symm)
    ((⟨_root_.stdSimplex.map (SimplexCategory.δ i),
      _root_.stdSimplex.continuous_map (SimplexCategory.δ i)⟩ :
        C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2)))) (bary n)) ?_
  have h1 := congrArg
    (fun τ => ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n)) h
  simp only at h1
  rwa [SKEFTHawking.SingularExcisionPushforward.toSSetObjEquiv_face,
    SKEFTHawking.SingularExcisionPushforward.toSSetObjEquiv_face] at h1

/-- **The face pair-sum identity**: the faces of the two lifts of `σ` are (as a mod-2 sum) the
two lifts of the face. -/
theorem face_pair_sum {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2)) :
    Finsupp.single (SKEFTHawking.SingularCohomologyMod2.face i (liftPlus σ)) (1 : ZMod 2)
        + Finsupp.single (SKEFTHawking.SingularCohomologyMod2.face i (liftMinus σ)) 1
      = Finsupp.single (liftPlus (SKEFTHawking.SingularCohomologyMod2.face i σ)) 1
        + Finsupp.single (liftMinus (SKEFTHawking.SingularCohomologyMod2.face i σ)) 1 := by
  rcases face_lift_mem_pair σ i (liftPlus σ) (mapSimplex_liftPlus σ) with hP | hP <;>
    rcases face_lift_mem_pair σ i (liftMinus σ) (mapSimplex_liftMinus σ) with hM | hM
  · exact absurd (hP.trans hM.symm) (face_liftPlus_ne_face_liftMinus σ i)
  · rw [hP, hM]
  · rw [hP, hM]
    exact add_comm _ _
  · exact absurd (hP.trans hM.symm) (face_liftPlus_ne_face_liftMinus σ i)

/-- **The transfer is a chain map**: `∂ ∘ τ = τ ∘ ∂` — per-face via the pair-sum identity. -/
theorem chainBoundary_transferChain (n : ℕ) (c : SingularChain (TopCat.of RP4) (n + 1)) :
    chainBoundary (TopCat.of S4) n (transferChain (n + 1) c)
      = transferChain n (chainBoundary (TopCat.of RP4) n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with ha | ha
      · rw [ha, Finsupp.single_zero]
        simp only [map_zero]
      · rw [ha, transferChain_single, map_add, chainBoundary_single, chainBoundary_single,
          chainBoundary_single, SKEFTHawking.SingularHomologyMod2.boundaryBasis,
          SKEFTHawking.SingularHomologyMod2.boundaryBasis,
          SKEFTHawking.SingularHomologyMod2.boundaryBasis, map_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [transferChain_single]
        exact face_pair_sum σ i

/-! ## §4. The apply-calculus of the 2-to-1 collapse — toward `ker π_# = im τ` -/

/-- **Every `S⁴`-simplex is one of the two lifts of its pushforward.** -/
theorem mem_pair_of_pushforward {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of S4)).obj (op (SimplexCategory.mk n))) :
    τ = liftPlus (mapSimplex mkC τ) ∨ τ = liftMinus (mapSimplex mkC τ) := by
  set F := mapSimplex mkC τ with hF
  have h1 : rlP F = mkC.comp ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ) := by
    rw [rlP, hF, mapSimplex, Equiv.apply_symm_apply]
  set y := ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ) (bary n) with hy
  have hmk : Quotient.mk (MulAction.orbitRel ℤˣ S4) y = rlP F (bary n) :=
    (congrFun (congrArg DFunLike.coe h1) (bary n)).symm
  have hcirc : Quotient.mk (MulAction.orbitRel ℤˣ S4) ∘
      ((TopCat.of S4).toSSetObjEquiv (op (SimplexCategory.mk n)) τ) = rlP F :=
    (congrArg DFunLike.coe h1).symm
  rcases fiber_pair (hmk.trans (mk_outFiber F).symm) with hcase | hcase
  · left
    exact liftSimplex_unique F (outFiber F) (mk_outFiber F) τ (hy ▸ hcase) hcirc
  · right
    exact liftSimplex_unique F ((-1 : ℤˣ) • outFiber F) (mk_neg_outFiber F) τ
      (hy ▸ hcase) hcirc

/-- **The 2-to-1 coefficient formula**: the pushforward's coefficient at `β` is the sum of the
coefficients at `β`'s two lifts. -/
theorem mapChain_apply_pair {n : ℕ} (c : SingularChain (TopCat.of S4) n)
    (β : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    mapChain mkC n c β = c (liftPlus β) + c (liftMinus β) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply, Finsupp.add_apply]
      abel
  | single σ a =>
      classical
      rw [mapChain_single, Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply]
      by_cases hβ : mapSimplex mkC σ = β
      · rcases mem_pair_of_pushforward σ with hσ | hσ
        · have hσ' : σ = liftPlus β := by rw [hβ] at hσ; exact hσ
          rw [if_pos hβ, if_pos hσ',
            if_neg (fun h => liftPlus_ne_liftMinus β (hσ'.symm.trans h)), add_zero]
        · have hσ' : σ = liftMinus β := by rw [hβ] at hσ; exact hσ
          rw [if_pos hβ, if_neg (fun h => liftPlus_ne_liftMinus β (h.symm.trans hσ')),
            if_pos hσ', zero_add]
      · rw [if_neg hβ, if_neg (fun h => hβ (by rw [h, mapSimplex_liftPlus])),
          if_neg (fun h => hβ (by rw [h, mapSimplex_liftMinus])), add_zero]

/-- **The transfer's coefficient at a `+`-lift is the source coefficient** (each `liftPlus β`
arises from exactly one basis simplex). -/
theorem transferChain_apply_liftPlus {n : ℕ} (c : SingularChain (TopCat.of RP4) n)
    (β : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    transferChain n c (liftPlus β) = c β := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply]
  | single σ a =>
      classical
      have hML : liftMinus σ ≠ liftPlus β := by
        intro h
        have h2 := congrArg (mapSimplex mkC) h
        rw [mapSimplex_liftMinus, mapSimplex_liftPlus] at h2
        subst h2
        exact liftPlus_ne_liftMinus σ h.symm
      rw [transferChain, Finsupp.linearCombination_single, smul_add, Finsupp.smul_single,
        Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.add_apply,
        Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply]
      by_cases hσ : σ = β
      · rw [if_pos (show liftPlus σ = liftPlus β by rw [hσ]), if_neg hML, add_zero, if_pos hσ]
      · rw [if_neg (fun h => hσ (by
            have h2 := congrArg (mapSimplex mkC) h
            rwa [mapSimplex_liftPlus, mapSimplex_liftPlus] at h2)),
          if_neg hML, if_neg hσ, add_zero]

/-- **The transfer is injective** — read off the `+`-lift coefficients. -/
theorem transferChain_injective (n : ℕ) : Function.Injective (transferChain n) := by
  intro c d h
  ext β
  have h1 := congrArg (fun x => x (liftPlus β)) h
  simpa only [transferChain_apply_liftPlus] using h1

/-- **The kernel of the pushforward is the image of the transfer** — the exactness heart of the
Smith sequence at the chain level: a mod-2 chain killed by `π_#` has its coefficients paired
antipodally (`mapChain_apply_pair`), so adding transfer-images strips its support two lifts at a
time; induction on a support-card bound finishes. -/
theorem mem_range_transferChain_of_mapChain_eq_zero {n : ℕ}
    (c : SingularChain (TopCat.of S4) n) (hc : mapChain mkC n c = 0) :
    c ∈ LinearMap.range (transferChain n) := by
  classical
  suffices H : ∀ (N : ℕ) (c : SingularChain (TopCat.of S4) n), c.support.card ≤ N →
      mapChain mkC n c = 0 → c ∈ LinearMap.range (transferChain n) from H _ c le_rfl hc
  intro N
  induction N with
  | zero =>
      intro c hcard _
      have hc0 : c = 0 :=
        Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
      exact ⟨0, by rw [map_zero, hc0]⟩
  | succ N ih =>
      intro c hcard hc
      rcases Finset.eq_empty_or_nonempty c.support with hemp | ⟨σ₀, hσ₀⟩
      · exact ⟨0, by rw [map_zero, Finsupp.support_eq_empty.mp hemp]⟩
      · set β := mapSimplex mkC σ₀ with hβ
        have hsum : c (liftPlus β) + c (liftMinus β) = 0 := by
          rw [← mapChain_apply_pair, hc]
          rfl
        have heq : c (liftPlus β) = c (liftMinus β) := by
          revert hsum
          generalize c (liftPlus β) = x
          generalize c (liftMinus β) = y
          revert x y
          decide
        have hone : c σ₀ = 1 := by
          have hne : c σ₀ ≠ 0 := Finsupp.mem_support_iff.mp hσ₀
          revert hne
          generalize c σ₀ = x
          revert x
          decide
        have hpair := mem_pair_of_pushforward σ₀
        rw [← hβ] at hpair
        have hP : c (liftPlus β) = 1 := by
          rcases hpair with h | h
          · rw [← h]; exact hone
          · rw [heq, ← h]; exact hone
        have hM : c (liftMinus β) = 1 := by rw [← heq]; exact hP
        set t := transferChain n (Finsupp.single β 1) with hts
        have hc' : mapChain mkC n (c + t) = 0 := by
          rw [map_add, hc, zero_add, hts]
          exact mapChain_transferChain n _
        have hsub : (c + t).support ⊆ c.support.erase (liftPlus β) := by
          intro x hx
          have hx0 : (c + t) x ≠ 0 := Finsupp.mem_support_iff.mp hx
          rw [Finsupp.add_apply, hts, transferChain_single, Finsupp.add_apply,
            Finsupp.single_apply, Finsupp.single_apply] at hx0
          rw [Finset.mem_erase, Finsupp.mem_support_iff]
          by_cases h1 : liftPlus β = x
          · exfalso
            apply hx0
            rw [if_pos h1, if_neg (fun h => liftPlus_ne_liftMinus β (h.trans h1.symm).symm),
              ← h1, hP]
            decide
          · by_cases h2 : liftMinus β = x
            · exfalso
              apply hx0
              rw [if_neg h1, if_pos h2, ← h2, hM]
              decide
            · rw [if_neg h1, if_neg h2] at hx0
              refine ⟨fun h => h1 h.symm, ?_⟩
              intro hcx
              apply hx0
              rw [hcx]
              decide
        have hPmem : liftPlus β ∈ c.support :=
          Finsupp.mem_support_iff.mpr (by rw [hP]; exact one_ne_zero)
        have hcard' : (c + t).support.card ≤ N := by
          have h1 := Finset.card_le_card hsub
          have h2 : (c.support.erase (liftPlus β)).card = c.support.card - 1 :=
            Finset.card_erase_of_mem hPmem
          omega
        obtain ⟨d, hd⟩ := ih (c + t) hcard' hc'
        refine ⟨d + Finsupp.single β 1, ?_⟩
        rw [map_add, hd, ← hts, add_assoc]
        have htt : t + t = 0 := by
          rw [← two_smul (ZMod 2) t, show (2 : ZMod 2) = 0 by decide, zero_smul]
        rw [htt, add_zero]

/-- **`ker π_# = range τ`** — the Smith short-exact-sequence identity, packaged. -/
theorem ker_mapChain_eq_range_transferChain (n : ℕ) :
    LinearMap.ker (mapChain mkC n) = LinearMap.range (transferChain n) := by
  ext c
  constructor
  · exact fun hc => mem_range_transferChain_of_mapChain_eq_zero c (LinearMap.mem_ker.mp hc)
  · rintro ⟨d, rfl⟩
    exact LinearMap.mem_ker.mpr (mapChain_transferChain n d)

/-- **The pushforward is surjective** — every base simplex lifts through `liftPlus`. With
`transferChain_injective` and `ker_mapChain_eq_range_transferChain` this completes the Smith
short exact sequence `0 → Cₙ(ℝP⁴) → Cₙ(S⁴) → Cₙ(ℝP⁴) → 0` of mod-2 chain groups. -/
theorem mapChain_surjective (n : ℕ) : Function.Surjective (mapChain mkC n) := by
  intro c
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add c d hc hd =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨b, hb⟩ := hd
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | single σ a =>
      exact ⟨Finsupp.single (liftPlus σ) a, by rw [mapChain_single, mapSimplex_liftPlus]⟩

end SKEFTHawking.RP4Transfer