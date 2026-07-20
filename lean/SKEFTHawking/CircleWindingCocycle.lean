/-
# Phase 5q.H · K1-b — the integral winding 1-cocycle on the circle

The **explicit degree-1 integral singular cocycle** `windS ∈ C¹(S¹;ℤ)` representing the winding
number, built on `Circle` (the unit circle in `ℂ`) through Mathlib's covering `Circle.exp` and
transported to the sphere-stack's carrier `Sph 1` along the banked `circleHomeoSph1` bridge.

Construction: every singular `1`-simplex `e : Δ¹ → Circle` lifts uniquely through the covering
`Circle.exp : ℝ → Circle` once anchored at `arg (e v₀)` over its first vertex (`Δ¹` is simply
connected and locally path-connected — the same `IsCoveringMap.existsUnique_continuousMap_lifts`
pattern as the `RP2Transfer` simplex lifts). The **winding number** `windMap e ∈ ℤ` is the unique
integer with `lift(v₁) = arg (e v₁) + windMap e · 2π`. The characterization
`windMap_char` (valid against *any* lift) makes everything computable:

* `windC_cocycle` / `windS_cocycle` — `δ wind = 0`: restrict a 2-simplex's global lift to its three
  edges; the alternating sum of the lift-endpoint differences telescopes to `0`.
* `wind*_const` — winding kills every constant edge (the constant lift anchors it).
* `windS_pathEdge_arcA = 0`, `windS_pathEdge_arcB = 1` — the two explicit half-circle arcs
  (`t ↦ exp (πt)` and `t ↦ exp (π + πt)`) carry winding `0` and `1`: the glued loop has total
  winding `1`. These are the arc weights the torus-step cross-evaluation (`TorusCrossPeel`)
  consumes: the `A`-cylinder of every glued cross contributes nothing and the `B`-cylinder
  contributes exactly once.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCupInt
import SKEFTHawking.SingularCohomologyFunctorialityInt
import SKEFTHawking.StdSimplexLocPath
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.KummerHomologyT4

namespace SKEFTHawking.CircleWindingCocycle

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularFunctoriality (mapSimplex)
open SKEFTHawking.SingularCohomologyFunctorialityInt (cochainPullbackInt
  cochainPullbackInt_apply coboundary_cochainPullbackInt)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.KummerHomologyT4 (circleHomeoSph1)

/-! ## §1. Realizations and anchored covering lifts -/

/-- The unit circle in `ℂ` as a `TopCat` carrier. -/
noncomputable abbrev CircleT : TopCat := TopCat.of Circle

/-- The geometric realization of a singular `n`-simplex (the `toSSetObjEquiv` readout). -/
noncomputable def rl {X : TopCat} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    C(stdSimplex ℝ (Fin (n + 1)), ↑X) :=
  X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ

/-- **The anchored lift** of a continuous `f : Δⁿ → Circle` through the covering `Circle.exp`,
pinned to the value `r₀` over the point `d₀` (`Δⁿ` is simply connected and locally path-connected,
so Mathlib's packaged unique-lifting applies on the nose). -/
noncomputable def liftMap {n : ℕ} (f : C(stdSimplex ℝ (Fin (n + 1)), Circle))
    (d₀ : stdSimplex ℝ (Fin (n + 1))) (r₀ : ℝ) (h : Circle.exp r₀ = f d₀) :
    C(stdSimplex ℝ (Fin (n + 1)), ℝ) :=
  (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f d₀ r₀ h).exists.choose

theorem liftMap_anchor {n : ℕ} (f : C(stdSimplex ℝ (Fin (n + 1)), Circle))
    (d₀ : stdSimplex ℝ (Fin (n + 1))) (r₀ : ℝ) (h : Circle.exp r₀ = f d₀) :
    liftMap f d₀ r₀ h d₀ = r₀ :=
  (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f d₀ r₀ h).exists.choose_spec.1

theorem liftMap_lifts {n : ℕ} (f : C(stdSimplex ℝ (Fin (n + 1)), Circle))
    (d₀ : stdSimplex ℝ (Fin (n + 1))) (r₀ : ℝ) (h : Circle.exp r₀ = f d₀) :
    ⇑Circle.exp ∘ ⇑(liftMap f d₀ r₀ h) = ⇑f :=
  (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f d₀ r₀ h).exists.choose_spec.2

/-- **Uniqueness of the anchored lift**: any lift hitting `r₀` at `d₀` is `liftMap`. -/
theorem liftMap_unique {n : ℕ} (f : C(stdSimplex ℝ (Fin (n + 1)), Circle))
    (d₀ : stdSimplex ℝ (Fin (n + 1))) (r₀ : ℝ) (h : Circle.exp r₀ = f d₀)
    (g : C(stdSimplex ℝ (Fin (n + 1)), ℝ)) (hg₀ : g d₀ = r₀)
    (hg : ⇑Circle.exp ∘ ⇑g = ⇑f) : g = liftMap f d₀ r₀ h :=
  (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f d₀ r₀ h).unique
    ⟨hg₀, hg⟩ ⟨liftMap_anchor f d₀ r₀ h, liftMap_lifts f d₀ r₀ h⟩

/-! ## §2. The winding number of an edge -/

/-- The first vertex of `Δ¹`. -/
noncomputable def v0 : stdSimplex ℝ (Fin 2) := stdSimplex.vertex 0

/-- The second vertex of `Δ¹`. -/
noncomputable def v1 : stdSimplex ℝ (Fin 2) := stdSimplex.vertex 1

@[simp] theorem coe_v0_one : (v0 : Fin 2 → ℝ) 1 = 0 := by
  simp [v0, stdSimplex.vertex]

@[simp] theorem coe_v1_one : (v1 : Fin 2 → ℝ) 1 = 1 := by
  simp [v1, stdSimplex.vertex]

theorem exists_windEq (f : C(stdSimplex ℝ (Fin 2), Circle)) :
    ∃ m : ℤ, liftMap f v0 ((f v0 : ℂ)).arg (Circle.exp_arg (f v0)) v1
      = ((f v1 : ℂ)).arg + m * (2 * Real.pi) := by
  have h1 : Circle.exp (liftMap f v0 ((f v0 : ℂ)).arg (Circle.exp_arg (f v0)) v1) = f v1 :=
    congrFun (liftMap_lifts f v0 _ (Circle.exp_arg (f v0))) v1
  have h2 : Circle.exp ((f v1 : ℂ)).arg = f v1 := Circle.exp_arg (f v1)
  exact Circle.exp_eq_exp.mp (h1.trans h2.symm)

/-- **The winding number** of a continuous edge `f : Δ¹ → Circle`: the unique integer `m` with
`lift(v₁) = arg (f v₁) + m · 2π` for the `arg (f v₀)`-anchored lift. -/
noncomputable def windMap (f : C(stdSimplex ℝ (Fin 2), Circle)) : ℤ :=
  (exists_windEq f).choose

theorem windMap_spec (f : C(stdSimplex ℝ (Fin 2), Circle)) :
    liftMap f v0 ((f v0 : ℂ)).arg (Circle.exp_arg (f v0)) v1
      = ((f v1 : ℂ)).arg + windMap f * (2 * Real.pi) :=
  (exists_windEq f).choose_spec

/-- **The winding characterization against an arbitrary lift** `L` (`exp ∘ L = f`):
`windMap f · 2π = (L v₁ − L v₀) − (arg (f v₁) − arg (f v₀))`. The workhorse: it computes `windMap`
from any convenient lift — global 2-simplex restrictions, constants, explicit arc lifts. -/
theorem windMap_char (f : C(stdSimplex ℝ (Fin 2), Circle)) (L : C(stdSimplex ℝ (Fin 2), ℝ))
    (hL : ⇑Circle.exp ∘ ⇑L = ⇑f) :
    (windMap f : ℝ) * (2 * Real.pi)
      = (L v1 - L v0) - (((f v1 : ℂ)).arg - ((f v0 : ℂ)).arg) := by
  set c : ℝ := L v0 - ((f v0 : ℂ)).arg with hc
  have hexpc : Circle.exp c = 1 := by
    have h1 : Circle.exp (L v0) = f v0 := congrFun hL v0
    have h2 : Circle.exp (c + ((f v0 : ℂ)).arg) = Circle.exp c * Circle.exp ((f v0 : ℂ)).arg :=
      Circle.exp_add c _
    rw [show c + ((f v0 : ℂ)).arg = L v0 by rw [hc]; ring, h1, Circle.exp_arg] at h2
    exact mul_right_cancel (h2.symm.trans (one_mul (f v0)).symm)
  set L' : C(stdSimplex ℝ (Fin 2), ℝ) := L - ContinuousMap.const (stdSimplex ℝ (Fin 2)) c
    with hL'def
  have hL'apply : ∀ d, L' d = L d - c := fun d => rfl
  have hlift' : ⇑Circle.exp ∘ ⇑L' = ⇑f := by
    funext d
    have hmul : Circle.exp (L d - c) * Circle.exp c = Circle.exp (L d) := by
      rw [← Circle.exp_add]; congr 1; ring
    rw [hexpc, mul_one] at hmul
    show Circle.exp (L' d) = f d
    rw [hL'apply d, hmul]
    exact congrFun hL d
  have hanchor : L' v0 = ((f v0 : ℂ)).arg := by
    rw [hL'apply v0, hc]; ring
  have huniq := liftMap_unique f v0 ((f v0 : ℂ)).arg (Circle.exp_arg (f v0)) L' hanchor hlift'
  have hval : L' v1 = ((f v1 : ℂ)).arg + windMap f * (2 * Real.pi) := by
    rw [huniq]; exact windMap_spec f
  rw [hL'apply v1, hc] at hval
  linarith [hval]

/-- Determine `windMap` from any lift plus the endpoint arithmetic. -/
theorem windMap_eq_of_char (f : C(stdSimplex ℝ (Fin 2), Circle))
    (L : C(stdSimplex ℝ (Fin 2), ℝ)) (hL : ⇑Circle.exp ∘ ⇑L = ⇑f) (m : ℤ)
    (hm : (L v1 - L v0) - (((f v1 : ℂ)).arg - ((f v0 : ℂ)).arg) = (m : ℝ) * (2 * Real.pi)) :
    windMap f = m := by
  have h := windMap_char f L hL
  rw [hm] at h
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  exact_mod_cast mul_right_cancel₀ h2π h

/-! ## §3. The winding cochain on `Circle` and its cocycle law -/

/-- **The integral winding 1-cochain** on `Circle`: `e ↦ windMap (rl e)`. -/
noncomputable def windC : SingularCochainInt CircleT 1 := fun e => windMap (rl (X := CircleT) e)

theorem windC_apply (e : (TopCat.toSSet.obj CircleT).obj (op (SimplexCategory.mk 1))) :
    windC e = windMap (rl (X := CircleT) e) := rfl

/-- The affine coface realization `Δⁿ⁺¹ ⊃ Δⁿ`, as a bundled continuous map. -/
noncomputable def faceC {n : ℕ} (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (SimplexCategory.δ i), stdSimplex.continuous_map (SimplexCategory.δ i)⟩

/-- The realization of a face is the realization precomposed with the affine coface (definitional
`toSSetObjEquiv`-naturality, as in `SingularExcisionPushforward.toSSetObjEquiv_face`). -/
theorem rl_face {X : TopCat} {n : ℕ} (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    rl (face i σ) = (rl σ).comp (faceC i) :=
  rfl

/-- Vertex transport along the affine coface. -/
theorem faceC_vertex {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 1)) :
    faceC i (stdSimplex.vertex k)
      = stdSimplex.vertex ((ConcreteCategory.hom (SimplexCategory.δ i)) k) :=
  stdSimplex.map_vertex _ _

/-- **`δ windC = 0`** — the winding cochain is a cocycle. Restrict a global lift of the 2-simplex to
its three edges (each restriction is a lift of the corresponding face); the alternating sum of the
per-edge winding formulas telescopes to `0` over ℝ, and `2π ≠ 0` descends it to ℤ. -/
theorem windC_cocycle : coboundaryₗ CircleT 1 windC = 0 := by
  funext σ
  show coboundary CircleT 1 windC σ = 0
  rw [coboundary_apply]
  set g : C(stdSimplex ℝ (Fin 3), Circle) := rl (X := CircleT) σ with hg
  set L : C(stdSimplex ℝ (Fin 3), ℝ) :=
    liftMap g (stdSimplex.vertex 0) ((g (stdSimplex.vertex 0) : ℂ)).arg
      (Circle.exp_arg _) with hL
  have hLlift : ⇑Circle.exp ∘ ⇑L = ⇑g := liftMap_lifts g _ _ _
  have hedge : ∀ i : Fin 3,
      (windC (face i σ) : ℝ) * (2 * Real.pi)
        = (L (stdSimplex.vertex ((ConcreteCategory.hom (SimplexCategory.δ i)) (1 : Fin 2)))
            - L (stdSimplex.vertex ((ConcreteCategory.hom (SimplexCategory.δ i)) (0 : Fin 2))))
          - (((g (stdSimplex.vertex ((ConcreteCategory.hom (SimplexCategory.δ i)) (1 : Fin 2))) : ℂ)).arg
            - ((g (stdSimplex.vertex ((ConcreteCategory.hom (SimplexCategory.δ i)) (0 : Fin 2))) : ℂ)).arg) := by
    intro i
    have hLi : ⇑Circle.exp ∘ ⇑(L.comp (faceC i)) = ⇑(rl (X := CircleT) (face i σ)) := by
      rw [rl_face]
      funext d
      exact congrFun hLlift _
    have h := windMap_char (rl (X := CircleT) (face i σ)) (L.comp (faceC i)) hLi
    have hv0 : (L.comp (faceC i)) v0
        = L (stdSimplex.vertex ((ConcreteCategory.hom (SimplexCategory.δ i)) (0 : Fin 2))) :=
      congrArg L (faceC_vertex i 0)
    have hv1 : (L.comp (faceC i)) v1
        = L (stdSimplex.vertex ((ConcreteCategory.hom (SimplexCategory.δ i)) (1 : Fin 2))) :=
      congrArg L (faceC_vertex i 1)
    have hfv0 : rl (X := CircleT) (face i σ) v0
        = g (stdSimplex.vertex ((ConcreteCategory.hom (SimplexCategory.δ i)) (0 : Fin 2))) := by
      rw [rl_face]
      exact congrArg g (faceC_vertex i 0)
    have hfv1 : rl (X := CircleT) (face i σ) v1
        = g (stdSimplex.vertex ((ConcreteCategory.hom (SimplexCategory.δ i)) (1 : Fin 2))) := by
      rw [rl_face]
      exact congrArg g (faceC_vertex i 1)
    rw [windC_apply, h, hv0, hv1, hfv0, hfv1]
  have hsum : ((∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) * windC (face i σ) : ℤ) : ℝ) * (2 * Real.pi)
      = 0 := by
    push_cast
    rw [Fin.sum_univ_three]
    have h0 := hedge 0
    have h1 := hedge 1
    have h2 := hedge 2
    have e00 : ((ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 3))) (0 : Fin 2))
        = (1 : Fin 3) := rfl
    have e01 : ((ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 3))) (1 : Fin 2))
        = (2 : Fin 3) := rfl
    have e10 : ((ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 3))) (0 : Fin 2))
        = (0 : Fin 3) := rfl
    have e11 : ((ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 3))) (1 : Fin 2))
        = (2 : Fin 3) := rfl
    have e20 : ((ConcreteCategory.hom (SimplexCategory.δ (2 : Fin 3))) (0 : Fin 2))
        = (0 : Fin 3) := rfl
    have e21 : ((ConcreteCategory.hom (SimplexCategory.δ (2 : Fin 3))) (1 : Fin 2))
        = (1 : Fin 3) := rfl
    rw [e00, e01] at h0
    rw [e10, e11] at h1
    rw [e20, e21] at h2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_succ, one_mul,
      neg_mul, neg_neg]
    nlinarith [h0, h1, h2]
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  rcases mul_eq_zero.mp hsum with h | h
  · exact_mod_cast h
  · exact absurd h h2π

/-- **Winding kills constant edges**: `windC (constSimplex z 1) = 0` (the constant lift anchors). -/
theorem windC_const (z : Circle) : windC (constSimplex (X := CircleT) z 1) = 0 := by
  rw [windC_apply]
  have hrl : rl (X := CircleT) (constSimplex (X := CircleT) z 1)
      = ContinuousMap.const (stdSimplex ℝ (Fin 2)) z := by
    rw [rl, constSimplex, Equiv.apply_symm_apply]
    rfl
  refine windMap_eq_of_char _ (ContinuousMap.const _ ((z : ℂ)).arg) ?_ 0 ?_
  · funext d
    rw [hrl]
    exact Circle.exp_arg z
  · rw [hrl]
    simp only [ContinuousMap.const_apply]
    push_cast
    ring

/-! ## §4. The interval coordinate and path edges -/

/-- The affine coordinate `Δ¹ → [0,1]`, `d ↦ d 1` (the second barycentric coordinate). -/
noncomputable def iota : C(stdSimplex ℝ (Fin 2), unitInterval) where
  toFun d := ⟨(d : Fin 2 → ℝ) 1, ⟨d.2.1 1, by
    calc (d : Fin 2 → ℝ) 1
        ≤ (d : Fin 2 → ℝ) 0 + (d : Fin 2 → ℝ) 1 := le_add_of_nonneg_left (d.2.1 0)
      _ = 1 := by rw [← Fin.sum_univ_two]; exact d.2.2⟩⟩
  continuous_toFun := ((continuous_apply (1 : Fin 2)).comp continuous_subtype_val).subtype_mk _

@[simp] theorem coe_iota (d : stdSimplex ℝ (Fin 2)) : ((iota d : unitInterval) : ℝ)
    = (d : Fin 2 → ℝ) 1 := rfl

@[simp] theorem iota_v0 : iota v0 = 0 := by
  apply Subtype.ext
  rw [coe_iota, coe_v0_one]
  rfl

@[simp] theorem iota_v1 : iota v1 = 1 := by
  apply Subtype.ext
  rw [coe_iota, coe_v1_one]
  rfl

/-- **The edge simplex of a path** `γ : [0,1] → X`: the singular 1-simplex `γ ∘ iota`. -/
noncomputable def pathEdge (X : TopCat) (γ : C(unitInterval, ↑X)) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 1)) :=
  (X.toSSetObjEquiv (op (SimplexCategory.mk 1))).symm (γ.comp iota)

theorem rl_pathEdge (X : TopCat) (γ : C(unitInterval, ↑X)) :
    rl (pathEdge X γ) = γ.comp iota :=
  Equiv.apply_symm_apply _ _

/-! ## §5. The two half-circle arcs on `Circle` and their winding -/

/-- The upper half-arc `t ↦ exp (π t)` (from `1` to `−1`). -/
noncomputable def arcCA : C(unitInterval, ↑CircleT) :=
  Circle.exp.comp ⟨fun t => Real.pi * (t : ℝ), by fun_prop⟩

/-- The lower half-arc `t ↦ exp (π + π t)` (from `−1` around to `1`). -/
noncomputable def arcCB : C(unitInterval, ↑CircleT) :=
  Circle.exp.comp ⟨fun t => Real.pi + Real.pi * (t : ℝ), by fun_prop⟩

theorem arcCA_apply (t : unitInterval) : arcCA t = Circle.exp (Real.pi * (t : ℝ)) := rfl

theorem arcCB_apply (t : unitInterval) : arcCB t = Circle.exp (Real.pi + Real.pi * (t : ℝ)) := rfl

theorem argexp_zero : ((Circle.exp 0 : ℂ)).arg = 0 := by
  rw [Circle.exp_zero]
  exact Complex.arg_one

theorem argexp_pi : ((Circle.exp Real.pi : ℂ)).arg = Real.pi := by
  rw [Circle.coe_exp, Complex.exp_pi_mul_I, Complex.arg_neg_one]

theorem exp_two_pi : Circle.exp (2 * Real.pi) = 1 := by
  have h := Circle.exp_int_mul_two_pi 1
  rwa [Int.cast_one, one_mul] at h

theorem argexp_two_pi : ((Circle.exp (2 * Real.pi) : ℂ)).arg = 0 := by
  rw [exp_two_pi]
  exact Complex.arg_one

/-- **The upper arc has winding `0`** (its lift `d ↦ π d₁` stays inside one period). -/
theorem windC_pathEdge_arcCA : windC (pathEdge CircleT arcCA) = 0 := by
  rw [windC_apply]
  refine windMap_eq_of_char _
    ⟨fun d => Real.pi * (d : Fin 2 → ℝ) 1,
      continuous_const.mul ((continuous_apply (1 : Fin 2)).comp continuous_subtype_val)⟩ ?_ 0 ?_
  · rw [rl_pathEdge]
    funext d
    show Circle.exp (Real.pi * (d : Fin 2 → ℝ) 1) = arcCA (iota d)
    rw [arcCA_apply, coe_iota]
  · rw [rl_pathEdge]
    have hb0 : (arcCA.comp iota) v0 = Circle.exp 0 := by
      show arcCA (iota v0) = _
      rw [iota_v0, arcCA_apply]
      norm_num
    have hb1 : (arcCA.comp iota) v1 = Circle.exp Real.pi := by
      show arcCA (iota v1) = _
      rw [iota_v1, arcCA_apply]
      norm_num
    show (Real.pi * (v1 : Fin 2 → ℝ) 1 - Real.pi * (v0 : Fin 2 → ℝ) 1)
        - ((((arcCA.comp iota) v1 : ℂ)).arg - (((arcCA.comp iota) v0 : ℂ)).arg)
      = ((0 : ℤ) : ℝ) * (2 * Real.pi)
    rw [coe_v0_one, coe_v1_one, hb0, hb1, argexp_pi, argexp_zero]
    push_cast
    ring

/-- **The lower arc has winding `1`** (its lift `d ↦ π + π d₁` crosses the `arg` cut once). -/
theorem windC_pathEdge_arcCB : windC (pathEdge CircleT arcCB) = 1 := by
  rw [windC_apply]
  refine windMap_eq_of_char _
    ⟨fun d => Real.pi + Real.pi * (d : Fin 2 → ℝ) 1,
      continuous_const.add (continuous_const.mul
        ((continuous_apply (1 : Fin 2)).comp continuous_subtype_val))⟩ ?_ 1 ?_
  · rw [rl_pathEdge]
    funext d
    show Circle.exp (Real.pi + Real.pi * (d : Fin 2 → ℝ) 1) = arcCB (iota d)
    rw [arcCB_apply, coe_iota]
  · rw [rl_pathEdge]
    have hb0 : (arcCB.comp iota) v0 = Circle.exp Real.pi := by
      show arcCB (iota v0) = _
      rw [iota_v0, arcCB_apply]
      norm_num
    have hb1 : (arcCB.comp iota) v1 = Circle.exp (2 * Real.pi) := by
      show arcCB (iota v1) = _
      rw [iota_v1, arcCB_apply]
      exact congrArg Circle.exp (by norm_num; ring)
    show ((Real.pi + Real.pi * (v1 : Fin 2 → ℝ) 1) - (Real.pi + Real.pi * (v0 : Fin 2 → ℝ) 1))
        - ((((arcCB.comp iota) v1 : ℂ)).arg - (((arcCB.comp iota) v0 : ℂ)).arg)
      = ((1 : ℤ) : ℝ) * (2 * Real.pi)
    rw [coe_v0_one, coe_v1_one, hb0, hb1, argexp_two_pi, argexp_pi]
    push_cast
    ring

/-! ## §6. Transport to the sphere carrier `Sph 1` -/

/-- The bridge `Circle → Sph 1` (the banked `circleHomeoSph1`, as a continuous map). -/
noncomputable def c2s : C(↑CircleT, ↑(Sph 1)) :=
  ⟨circleHomeoSph1, circleHomeoSph1.continuous⟩

/-- The bridge `Sph 1 → Circle` (the inverse direction). -/
noncomputable def s2c : C(↑(Sph 1), ↑CircleT) :=
  ⟨circleHomeoSph1.symm, circleHomeoSph1.symm.continuous⟩

theorem s2c_c2s (z : ↑CircleT) : s2c (c2s z) = z := circleHomeoSph1.symm_apply_apply z

/-- **The winding cochain on `Sph 1`** — the pullback of `windC` along the bridge. -/
noncomputable def windS : SingularCochainInt (Sph 1) 1 :=
  cochainPullbackInt s2c 1 windC

theorem windS_apply (e : (TopCat.toSSet.obj (Sph 1)).obj (op (SimplexCategory.mk 1))) :
    windS e = windC (mapSimplex s2c e) := rfl

/-- `windS` is a cocycle (pullback naturality of the coboundary + `windC_cocycle`). -/
theorem windS_cocycle : coboundaryₗ (Sph 1) 1 windS = 0 := by
  have h := coboundary_cochainPullbackInt s2c 1 windC
  rw [windS]
  rw [show coboundaryₗ (Sph 1) 1 (cochainPullbackInt s2c 1 windC)
      = cochainPullbackInt s2c 2 (coboundaryₗ CircleT 1 windC) from h,
    windC_cocycle, map_zero]

/-- The pushforward of a constant simplex is the constant simplex at the image point. -/
theorem mapSimplex_constSimplex {X Y : TopCat} (φ : C(↑X, ↑Y)) (b : ↑X) (k : ℕ) :
    mapSimplex φ (constSimplex b k) = constSimplex (φ b) k := by
  rw [mapSimplex, constSimplex, constSimplex, Equiv.apply_symm_apply]
  exact congrArg _ (ContinuousMap.ext fun d => rfl)

/-- `windS` kills constant edges. -/
theorem windS_const (b : ↑(Sph 1)) : windS (constSimplex b 1) = 0 := by
  rw [windS_apply, mapSimplex_constSimplex]
  exact windC_const _

/-! ## §7. The two arcs on `Sph 1` and their winding weights -/

/-- The upper half-arc on `Sph 1`. -/
noncomputable def arcA : C(unitInterval, ↑(Sph 1)) := c2s.comp arcCA

/-- The lower half-arc on `Sph 1`. -/
noncomputable def arcB : C(unitInterval, ↑(Sph 1)) := c2s.comp arcCB

/-- The arcs glue: `arcA 1 = arcB 0` (both are the image of `exp π = −1`). -/
theorem arcA_one_eq_arcB_zero : arcA 1 = arcB 0 := by
  show c2s (arcCA 1) = c2s (arcCB 0)
  congr 1
  rw [arcCA_apply, arcCB_apply]
  congr 1
  norm_num

/-- The arcs close up: `arcB 1 = arcA 0` (both are the image of `1 = exp 0 = exp 2π`). -/
theorem arcB_one_eq_arcA_zero : arcB 1 = arcA 0 := by
  show c2s (arcCB 1) = c2s (arcCA 0)
  congr 1
  rw [arcCA_apply, arcCB_apply]
  have h1 : Real.pi + Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by
    norm_num; ring
  have h0 : Real.pi * ((0 : unitInterval) : ℝ) = 0 := by norm_num
  rw [h1, h0, Circle.exp_zero, exp_two_pi]

theorem windS_pathEdge_comp (γ : C(unitInterval, ↑CircleT)) :
    windS (pathEdge (Sph 1) (c2s.comp γ)) = windC (pathEdge CircleT γ) := by
  rw [windS_apply]
  congr 1
  rw [mapSimplex, pathEdge, pathEdge, Equiv.apply_symm_apply]
  congr 1
  refine ContinuousMap.ext fun d => ?_
  show s2c (c2s (γ (iota d))) = γ (iota d)
  exact s2c_c2s (γ (iota d))

/-- **The `A`-arc weight is `0`.** -/
theorem windS_pathEdge_arcA : windS (pathEdge (Sph 1) arcA) = 0 := by
  rw [show arcA = c2s.comp arcCA from rfl, windS_pathEdge_comp]
  exact windC_pathEdge_arcCA

/-- **The `B`-arc weight is `1`.** -/
theorem windS_pathEdge_arcB : windS (pathEdge (Sph 1) arcB) = 1 := by
  rw [show arcB = c2s.comp arcCB from rfl, windS_pathEdge_comp]
  exact windC_pathEdge_arcCB

end SKEFTHawking.CircleWindingCocycle
