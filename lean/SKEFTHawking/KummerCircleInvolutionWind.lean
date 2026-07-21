/-
# Phase 5q.H — K7 residual (a): the winding cocycle negates under circle inversion

The ground fact of the `τ_*`-eigenvalue computation for the `Q`-side `H₂` solve: pulling the
integral winding 1-cocycle back along the circle inversion `z ↦ z⁻¹` negates it **up to an
explicit integral coboundary** — the `arg = π` branch correction:

* `argCorr` — the 0-cochain `σ ↦ [arg(σ) = π]` (the branch indicator of `Complex.arg`),
* `windC_inv` — `inv* windC = −windC − δ argCorr` (per-edge: any lift `L` of an edge negates to a
  lift `−L` of the inverted edge, and `arg(z⁻¹) + arg(z) ∈ {0, 2π}` with the `2π` exactly on the
  `arg = π` branch),
* `windS_inv` — the same identity transported to the sphere-stack carrier `Sph 1` along the
  banked `circleHomeoSph1` bridge, against the conjugated inversion `invSphC`.

Downstream (`KummerT4InvolutionAction`): the coordinate 1-cocycles `b₀ … b₃` of
`T⁴ = Tor (Tor TwoTorus)` are iterated pullbacks of `windS`, so the coordinatewise involution
pulls each back to `−bᵢ − δuᵢ` — the class-level `τ_* = −1` on `H¹` and `τ_* = +1` on the cup
squares that drives `ker(1−τ_*) = 0` on `H₁` and `ker(1+τ_*) = 0` on `H₂`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.CircleWindingCocycle
import SKEFTHawking.TorusCrossPeel

namespace SKEFTHawking.KummerCircleInvolutionWind

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularFunctoriality (mapSimplex mapSimplex_comp)
open SKEFTHawking.SingularCohomologyFunctorialityInt (cochainPullbackInt cochainPullbackInt_apply
  coboundary_cochainPullbackInt)
open SKEFTHawking.CircleWindingCocycle (CircleT rl liftMap liftMap_anchor liftMap_lifts
  windMap windMap_spec windMap_char windMap_eq_of_char windC windC_apply v0 v1 faceC rl_face
  faceC_vertex windS windS_apply s2c c2s s2c_c2s windS_cocycle)
open SKEFTHawking.TorusCrossPeel (rl_mapSimplex)
open SKEFTHawking.SingularSphereAcyclic (Sph)

noncomputable section

/-! ## §1. The circle inversion and the branch-indicator 0-cochain -/

/-- The circle inversion `z ↦ z⁻¹` as a bundled continuous map on the `Circle` carrier. -/
def invCircleC : C(↑CircleT, ↑CircleT) := ⟨fun z => z⁻¹, continuous_inv⟩

@[simp] theorem invCircleC_apply (z : Circle) : invCircleC z = z⁻¹ := rfl

/-- `inv² = id` on the circle. -/
theorem invCircleC_comp_self : invCircleC.comp invCircleC = ContinuousMap.id ↑CircleT :=
  ContinuousMap.ext fun z => inv_inv z

/-- The unique vertex of `Δ⁰`. -/
def d0 : stdSimplex ℝ (Fin 1) := stdSimplex.vertex 0

/-- **The branch-indicator 0-cochain**: `1` on 0-simplices sitting at `arg = π` (the point `−1`),
`0` elsewhere. The explicit primitive of the failure of `arg` to be odd. -/
def argCorr : SingularCochainInt CircleT 0 := fun σ =>
  if ((rl (X := CircleT) σ) d0 : ℂ).arg = Real.pi then 1 else 0

/-- The branch value `arg(z⁻¹) + arg(z)` is `2π` on the `arg = π` branch and `0` off it. -/
theorem arg_inv_add_arg (z : Circle) :
    ((z⁻¹ : Circle) : ℂ).arg + ((z : Circle) : ℂ).arg
      = (if ((z : Circle) : ℂ).arg = Real.pi then 1 else 0) * (2 * Real.pi) := by
  rw [Circle.coe_inv, Complex.arg_inv]
  split
  · next h => rw [h]; ring
  · ring

/-! ## §2. `inv* windC = −windC − δ argCorr` -/

/-- The vertex values of an edge's realization at the two face-embedded `Δ⁰`-points. -/
theorem rl_face_d0_zero (e : (TopCat.toSSet.obj CircleT).obj (op (SimplexCategory.mk 1))) :
    (rl (X := CircleT) (face (0 : Fin 2) e)) d0 = (rl (X := CircleT) e) v1 := by
  rw [rl_face]
  show (rl (X := CircleT) e) (faceC (0 : Fin 2) d0) = (rl (X := CircleT) e) v1
  congr 1
  rw [d0, faceC_vertex,
    show ((ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 2))) (0 : Fin 1)) = (1 : Fin 2)
      from by decide]
  rfl

theorem rl_face_d0_one (e : (TopCat.toSSet.obj CircleT).obj (op (SimplexCategory.mk 1))) :
    (rl (X := CircleT) (face (1 : Fin 2) e)) d0 = (rl (X := CircleT) e) v0 := by
  rw [rl_face]
  show (rl (X := CircleT) e) (faceC (1 : Fin 2) d0) = (rl (X := CircleT) e) v0
  congr 1
  rw [d0, faceC_vertex,
    show ((ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 2))) (0 : Fin 1)) = (0 : Fin 2)
      from by decide]
  rfl

/-- The coboundary of the branch indicator on an edge: endpoint minus startpoint values. -/
theorem coboundary_argCorr_apply
    (e : (TopCat.toSSet.obj CircleT).obj (op (SimplexCategory.mk 1))) :
    coboundary CircleT 0 argCorr e
      = (if ((rl (X := CircleT) e) v1 : ℂ).arg = Real.pi then 1 else 0)
        - (if ((rl (X := CircleT) e) v0 : ℂ).arg = Real.pi then 1 else 0) := by
  rw [coboundary_apply, Fin.sum_univ_two]
  show (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) * argCorr (face 0 e)
      + (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) * argCorr (face 1 e) = _
  rw [argCorr, argCorr, rl_face_d0_zero, rl_face_d0_one]
  split_ifs <;> norm_num

/-- **The winding cochain negates under inversion, up to the branch coboundary**:
`windC (inv₊ e) = −windC e − (δ argCorr) e` for every edge `e`. -/
theorem windC_inv (e : (TopCat.toSSet.obj CircleT).obj (op (SimplexCategory.mk 1))) :
    windC (mapSimplex invCircleC e) = -windC e - coboundary CircleT 0 argCorr e := by
  set f : C(stdSimplex ℝ (Fin 2), Circle) := rl (X := CircleT) e with hf
  -- the anchored lift of `f` and its negation
  set L : C(stdSimplex ℝ (Fin 2), ℝ) :=
    liftMap f v0 ((f v0 : ℂ)).arg (Circle.exp_arg (f v0)) with hL
  have hL0 : L v0 = ((f v0 : ℂ)).arg := liftMap_anchor f v0 _ _
  have hL1 : L v1 = ((f v1 : ℂ)).arg + windMap f * (2 * Real.pi) := windMap_spec f
  have hLlift : ⇑Circle.exp ∘ ⇑L = ⇑f := liftMap_lifts f v0 _ _
  set negL : C(stdSimplex ℝ (Fin 2), ℝ) := ⟨fun d => -(L d), by fun_prop⟩ with hnegL
  -- the inverted edge realizes as `inv ∘ f`, and `−L` lifts it
  have hrl : rl (X := CircleT) (mapSimplex invCircleC e) = invCircleC.comp f := by
    rw [hf, rl_mapSimplex]
  have hlift : ⇑Circle.exp ∘ ⇑negL = ⇑(invCircleC.comp f) := by
    funext d
    show Circle.exp (-(L d)) = (f d)⁻¹
    rw [Circle.exp_neg]
    exact congrArg Inv.inv (congrFun hLlift d)
  -- the two branch indicators
  set c1 : ℤ := if ((f v1 : ℂ)).arg = Real.pi then 1 else 0 with hc1
  set c0 : ℤ := if ((f v0 : ℂ)).arg = Real.pi then 1 else 0 with hc0
  -- the characterization computes the inverted winding
  have hwind : windMap (invCircleC.comp f) = -windMap f - (c1 - c0) := by
    refine windMap_eq_of_char (invCircleC.comp f) negL hlift _ ?_
    have hv1 : ((invCircleC.comp f) v1 : ℂ).arg = (((f v1)⁻¹ : Circle) : ℂ).arg := rfl
    have hv0 : ((invCircleC.comp f) v0 : ℂ).arg = (((f v0)⁻¹ : Circle) : ℂ).arg := rfl
    have hA1 := arg_inv_add_arg (f v1)
    have hA0 := arg_inv_add_arg (f v0)
    show (negL v1 - negL v0) - _ = _
    have hnegL1 : negL v1 = -(L v1) := rfl
    have hnegL0 : negL v0 = -(L v0) := rfl
    rw [hnegL1, hnegL0, hv1, hv0, hL0, hL1, hc1, hc0]
    by_cases h1 : ((f v1 : ℂ)).arg = Real.pi <;>
      by_cases h0 : ((f v0 : ℂ)).arg = Real.pi
    · simp only [if_pos h1, if_pos h0] at hA1 hA0 ⊢
      push_cast at hA1 hA0 ⊢
      linarith [hA1, hA0]
    · simp only [if_pos h1, if_neg h0] at hA1 hA0 ⊢
      push_cast at hA1 hA0 ⊢
      linarith [hA1, hA0]
    · simp only [if_neg h1, if_pos h0] at hA1 hA0 ⊢
      push_cast at hA1 hA0 ⊢
      linarith [hA1, hA0]
    · simp only [if_neg h1, if_neg h0] at hA1 hA0 ⊢
      push_cast at hA1 hA0 ⊢
      linarith [hA1, hA0]
  -- assemble
  have hwc : windC (mapSimplex invCircleC e) = windMap (invCircleC.comp f) := by
    rw [windC_apply, hrl]
  rw [hwc, hwind, windC_apply, ← hf, coboundary_argCorr_apply, ← hc1, ← hc0]

/-! ## §3. Transport to `Sph 1` along the bridge -/

/-- The conjugated inversion on the sphere-stack carrier `Sph 1`. -/
def invSphC : C(↑(Sph 1), ↑(Sph 1)) := c2s.comp (invCircleC.comp s2c)

@[simp] theorem invSphC_apply (x : ↑(Sph 1)) : invSphC x = c2s ((s2c x)⁻¹) := rfl

/-- The bridge intertwines the two inversions: `s2c ∘ invSph = inv ∘ s2c`. -/
theorem s2c_comp_invSphC : s2c.comp invSphC = invCircleC.comp s2c :=
  ContinuousMap.ext fun x => s2c_c2s ((s2c x)⁻¹)

/-- `invSph² = id` on `Sph 1`. -/
theorem invSphC_comp_self : invSphC.comp invSphC = ContinuousMap.id ↑(Sph 1) := by
  refine ContinuousMap.ext fun x => ?_
  show c2s ((s2c (c2s ((s2c x)⁻¹)))⁻¹) = x
  rw [s2c_c2s, inv_inv]
  exact SKEFTHawking.KummerHomologyT4.circleHomeoSph1.apply_symm_apply x

/-- The branch indicator on `Sph 1` (pullback along the bridge). -/
def argCorrS : SingularCochainInt (Sph 1) 0 := cochainPullbackInt s2c 0 argCorr

/-- **`invSph* windS = −windS − δ argCorrS`** — the sphere-carrier form of the negation. -/
theorem windS_inv (e : (TopCat.toSSet.obj (Sph 1)).obj (op (SimplexCategory.mk 1))) :
    windS (mapSimplex invSphC e) = -windS e - coboundary (Sph 1) 0 argCorrS e := by
  have h1 : windS (mapSimplex invSphC e) = windC (mapSimplex s2c (mapSimplex invSphC e)) :=
    windS_apply _
  have h2 : mapSimplex s2c (mapSimplex invSphC e)
      = mapSimplex invCircleC (mapSimplex s2c e) := by
    rw [← mapSimplex_comp s2c invSphC, s2c_comp_invSphC, mapSimplex_comp]
  have hδ : coboundary (Sph 1) 0 argCorrS e
      = coboundary CircleT 0 argCorr (mapSimplex s2c e) := by
    have h := congrFun (coboundary_cochainPullbackInt s2c 0 argCorr) e
    exact h
  rw [h1, h2, windC_inv, ← windS_apply, hδ]

end

end SKEFTHawking.KummerCircleInvolutionWind
