/-
# Phase 5q.H close-out — THE DISK-CORE PAIR: `β` (`H₄(∂D⁵) ≠ 0`) and `hincl` (`H₄`-injectivity)

`PinPlusTraceDiskRelFundReduce.hasRelFundClass_D5_of_boundaryIncl` reduces the `D⁵` relative
fundamental class to two geometric atoms over the boundary sphere `∂D⁵ = S⁴ = {v | ‖v‖ = 1}`:

* **`β`** — a nonzero class in `H₄(∂D⁵; ℤ/2)`. Built here: the double-subtype homeomorphism
  `↥(∂D⁵ : Set D⁵) ≃ₜ Metric.sphere (0 : E⁵) 1 = Sph 4` (`subSubtypeHomeo`, a generic
  subtype-of-subtype-vs-direct-subtype homeo instantiated once), transported to homology by the
  in-tree `homeoHomologyEquiv`, carrying the nonzero generator `(topSphereIso 3).symm 1` of
  `H₄(Sph 4) ≅ ℤ/2` back to `∂D⁵`.
* **`hincl`** — the boundary inclusion `∂D⁵ ↪ D⁵∖{x}` is `H₄`-injective at every interior point
  `x` (`‖x‖ < 1`). Built here by a clean **retraction argument** (no homotopy): the radial
  ray-exit map `r : D⁵∖{x} → ∂D⁵`, `v ↦ the point where the ray from x through v meets ‖·‖ = 1`,
  satisfies `r ∘ incl = id` on `∂D⁵` (boundary points are their own ray-exits), so
  `Homology.map r ∘ Homology.map incl = id` and `Homology.map incl` is split-injective. The
  ray-exit map, its `‖·‖ = 1` landing, its boundary-fixing, and its continuity are all proven
  **ambient-abstract** over a real inner-product space (`rayExit …`), instantiated for `E⁵` once —
  the whnf-hostile concrete `D⁵`/`closedBall`/`WithLp` stack is never forced.

Firing `hasRelFundClass_D5_of_boundaryIncl β hβ hincl` lands the disk relative fundamental class
`HasRelFundClass (TopCat.of D⁵) (∂D⁵) (interiorGenFamily …)` UNCONDITIONALLY.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
import SKEFTHawking.PinPlusTraceDiskRelFundReduce
import SKEFTHawking.SingularSphereAcyclic
import SKEFTHawking.SingularLineMinusPoint
import SKEFTHawking.PinPlusCharPairRealizationTied

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.DiskChartGeneric (D5)

namespace SKEFTHawking.PinPlusTraceDiskCorePair

noncomputable section

/-! ## §0. Two abstract lemmas — the retraction-injectivity engine and the double-subtype homeo. -/

/-- **Retraction ⇒ homology-injectivity** (abstract, ambient `TopCat`). If a subspace inclusion
`subIncl h : sub s ↪ sub t` admits a continuous retraction `r : sub t → sub s` with
`r ∘ subIncl h = id`, then `Homology.map (subIncl h) n` is injective. Proof: `Homology.map r n`
is a left inverse (`map_comp` + `map_id`). No homotopy needed. -/
theorem injective_homologyMap_of_retract {X : TopCat} {s t : Set ↑X} (h : s ⊆ t) (n : ℕ)
    (r : C(↑(sub t), ↑(sub s)))
    (hr : r.comp (subIncl h) = ContinuousMap.id ↑(sub s)) :
    Function.Injective (Homology.map (subIncl h) n) := by
  have hcomp : (Homology.map r n).comp (Homology.map (subIncl h) n) = LinearMap.id := by
    rw [← Homology.map_comp, hr, Homology.map_id]
  intro a b hab
  have hkey := congrArg (Homology.map r n) hab
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hcomp, LinearMap.id_apply,
    LinearMap.id_apply] at hkey
  exact hkey

/-- **A subtype-of-subtype is homeomorphic to the direct subtype it covers** (abstract). If
`S : Set (Subtype p)` has underlying-`α` values that hit exactly `T : Set α` (`hmem`) and `T` lies
inside `{a | p a}` (`hpT`), then `↥S ≃ₜ ↥T`. Both directions are the identity on the ambient `α`,
so continuity is `continuous_subtype_val` twice. Instantiated once for `∂D⁵ ⊆ D⁵ ⊆ E⁵`. -/
def subSubtypeHomeo {α : Type*} [TopologicalSpace α] {p : α → Prop} (S : Set (Subtype p))
    (T : Set α) (hmem : ∀ v : Subtype p, v ∈ S ↔ (v : α) ∈ T) (hpT : ∀ a, a ∈ T → p a) :
    ↥S ≃ₜ ↥T where
  toFun v := ⟨((v : Subtype p) : α), (hmem _).mp v.2⟩
  invFun w := ⟨⟨(w : α), hpT _ w.2⟩, (hmem ⟨(w : α), hpT _ w.2⟩).mpr w.2⟩
  left_inv v := by ext; rfl
  right_inv w := by ext; rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

/-! ## §1. `β` — a nonzero class in `H₄(∂D⁵; ℤ/2)`. -/

/-- Membership bridge: `v ∈ ∂D⁵ ↔ (v : E⁵) ∈ Metric.sphere 0 1`, from `boundary_D5` (norm 1) and
`mem_sphere_zero_iff_norm`. -/
theorem mem_boundary_iff_mem_sphere (v : D5) :
    v ∈ ((𝓡 4).prod (𝓡∂ 1)).boundary D5
      ↔ (v : EuclideanSpace ℝ (Fin 5)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 := by
  rw [PinPlusTraceCapstoneCoverGlueDisk.boundary_D5]
  exact mem_sphere_zero_iff_norm.symm

/-- **The boundary sphere of `D⁵` is homeomorphic to `Sph 4 = Metric.sphere (0 : E⁵) 1`.** The
`subSubtypeHomeo` instance for `∂D⁵ ⊆ D⁵ ⊆ E⁵`; the underlying map is the identity on `E⁵`. -/
def boundaryHomeoSph :
    (sub (X := TopCat.of D5) (((𝓡 4).prod (𝓡∂ 1)).boundary D5) : Type)
      ≃ₜ (SingularSphereAcyclic.Sph 4 : Type) :=
  subSubtypeHomeo (p := fun a => a ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 5)) 1)
    (((𝓡 4).prod (𝓡∂ 1)).boundary D5) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)
    mem_boundary_iff_mem_sphere (fun _ ha => Metric.sphere_subset_closedBall ha)

/-- **`β` — the transported top sphere generator, a nonzero class in `H₄(∂D⁵; ℤ/2)`.** Pull the
nonzero generator `(topSphereIso 3).symm 1` of `H₄(Sph 4) ≅ ℤ/2` back along the homology iso
`homeoHomologyEquiv boundaryHomeoSph 4`. -/
def betaClass : Homology (sub (X := TopCat.of D5) (((𝓡 4).prod (𝓡∂ 1)).boundary D5)) 4 :=
  (PinPlusCharPairRealizationTied.homeoHomologyEquiv boundaryHomeoSph 4).symm
    ((SingularLineMinusPoint.topSphereIso 3).symm 1)

/-- **`β ≠ 0`.** The generator `(topSphereIso 3).symm 1 ≠ 0` (a `ZMod 2`-linear-equiv image of
`1 ≠ 0`), pulled back by the injective `homeoHomologyEquiv`. -/
theorem betaClass_ne_zero : betaClass ≠ 0 := by
  rw [betaClass, LinearEquiv.map_ne_zero_iff]
  exact (SingularLineMinusPoint.topSphereIso 3).symm.map_ne_zero_iff.mpr one_ne_zero

/-! ## §2. `hincl` — the radial ray-exit retraction (ambient-abstract), giving `H₄`-injectivity. -/

section RayExit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The positive ray-exit scalar** `t(x,v)` — the larger root of `‖x + t·(v−x)‖ = 1`, i.e.
`(−B + √(B²−4AC)) / (2A)` with `A = ‖v−x‖²`, `B = 2⟪x, v−x⟫`, `C = ‖x‖² − 1`. For `‖x‖ < 1` and
`v ≠ x` the ray from `x` through `v` meets the unit sphere at exactly this positive `t`. -/
noncomputable def rayT (x v : E) : ℝ :=
  (-(2 * inner ℝ x (v - x)) +
      Real.sqrt ((2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1)))
    / (2 * ‖v - x‖ ^ 2)

/-- **The ray-exit point** `x + t·(v−x)` — on the unit sphere for `‖x‖ < 1`, `v ≠ x`. -/
noncomputable def rayExit (x v : E) : E := x + rayT x v • (v - x)

/-- The discriminant `B²−4AC` is nonnegative when `‖x‖ < 1`, `v ≠ x` (`A > 0`, `C < 0`). -/
theorem rayDisc_nonneg (x v : E) (hx : ‖x‖ < 1) (hv : v ≠ x) :
    0 ≤ (2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1) := by
  have hApos : 0 < ‖v - x‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv)) 2
  have hCneg : ‖x‖ ^ 2 - 1 < 0 := by nlinarith [norm_nonneg x]
  nlinarith [sq_nonneg (2 * inner ℝ x (v - x)), hApos, hCneg]

/-- **`rayT` solves the ray-sphere quadratic** `A·t² + B·t + C = 0`. -/
theorem rayT_quad (x v : E) (hx : ‖x‖ < 1) (hv : v ≠ x) :
    ‖v - x‖ ^ 2 * rayT x v ^ 2 + 2 * inner ℝ x (v - x) * rayT x v + (‖x‖ ^ 2 - 1) = 0 := by
  have hApos : 0 < ‖v - x‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv)) 2
  have h2A : (2 * ‖v - x‖ ^ 2) ≠ 0 := by positivity
  have hΔ : 0 ≤ (2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1) :=
    rayDisc_nonneg x v hx hv
  -- `t·(2A) = −B + √Δ`
  have hkey : rayT x v * (2 * ‖v - x‖ ^ 2)
      = -(2 * inner ℝ x (v - x))
        + Real.sqrt ((2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1)) := by
    rw [rayT, div_mul_cancel₀ _ h2A]
  -- `2A·t + B = √Δ`
  have hsB : 2 * ‖v - x‖ ^ 2 * rayT x v + 2 * inner ℝ x (v - x)
      = Real.sqrt ((2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1)) := by
    linear_combination hkey
  have hsqrt : Real.sqrt ((2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1)) ^ 2
      = (2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1) := Real.sq_sqrt hΔ
  -- `4A·(A t² + B t + C) = (2At+B)² − Δ = 0`
  have hfin : 4 * ‖v - x‖ ^ 2
      * (‖v - x‖ ^ 2 * rayT x v ^ 2 + 2 * inner ℝ x (v - x) * rayT x v + (‖x‖ ^ 2 - 1)) = 0 := by
    have h1 : (2 * ‖v - x‖ ^ 2 * rayT x v + 2 * inner ℝ x (v - x)) ^ 2
        = (2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1) := by
      rw [hsB, hsqrt]
    linear_combination h1
  have h4A : (4 * ‖v - x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hfin).resolve_left h4A

/-- **The ray-exit point lands on the unit sphere**: `‖rayExit x v‖ = 1`. -/
theorem rayExit_norm (x v : E) (hx : ‖x‖ < 1) (hv : v ≠ x) : ‖rayExit x v‖ = 1 := by
  have hquad := rayT_quad x v hx hv
  have hsq : ‖rayExit x v‖ ^ 2 = 1 := by
    rw [rayExit, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs]
    linear_combination hquad
  nlinarith [hsq, norm_nonneg (rayExit x v)]

/-- **The ray-exit map fixes the boundary sphere**: if `‖v‖ = 1` (and `v ≠ x`, `‖x‖ < 1`) then
`rayExit x v = v` — the ray from `x` through a boundary point `v` exits at `v` itself (`t = 1`). -/
theorem rayExit_of_norm_one (x v : E) (hx : ‖x‖ < 1) (hv : v ≠ x) (h1 : ‖v‖ = 1) :
    rayExit x v = v := by
  have hApos : 0 < ‖v - x‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv)) 2
  have h2A : (2 * ‖v - x‖ ^ 2) ≠ 0 := by positivity
  -- `A + B + C = ‖v‖² − 1 = 0`
  have hABC : ‖v - x‖ ^ 2 + 2 * inner ℝ x (v - x) + (‖x‖ ^ 2 - 1) = 0 := by
    have hexp : ‖x + (v - x)‖ ^ 2
        = ‖x‖ ^ 2 + 2 * inner ℝ x (v - x) + ‖v - x‖ ^ 2 := by
      rw [norm_add_sq_real]
    have hxv : x + (v - x) = v := by abel
    rw [hxv, h1] at hexp
    nlinarith [hexp]
  -- so `√Δ = 2A + B` (with `2A + B > 0`), giving `t = 1`
  have hCneg : ‖x‖ ^ 2 - 1 < 0 := by nlinarith [norm_nonneg x]
  have h2AB : 0 ≤ 2 * ‖v - x‖ ^ 2 + 2 * inner ℝ x (v - x) := by nlinarith [hApos, hABC, hCneg]
  have hΔeq : (2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1)
      = (2 * ‖v - x‖ ^ 2 + 2 * inner ℝ x (v - x)) ^ 2 := by nlinarith [hABC]
  have hsqrt : Real.sqrt ((2 * inner ℝ x (v - x)) ^ 2 - 4 * ‖v - x‖ ^ 2 * (‖x‖ ^ 2 - 1))
      = 2 * ‖v - x‖ ^ 2 + 2 * inner ℝ x (v - x) := by
    rw [hΔeq, Real.sqrt_sq h2AB]
  have hT1 : rayT x v = 1 := by
    rw [rayT, hsqrt, div_eq_one_iff_eq h2A]
    ring
  rw [rayExit, hT1, one_smul, add_sub_cancel]

/-- **`rayExit x ∘ g` is continuous** for any continuous `g : Y → E` whose image avoids `x`
(so the denominator `2‖g y − x‖² ≠ 0`). The reusable continuity engine, instantiated once. -/
theorem continuous_rayExit_comp {Y : Type*} [TopologicalSpace Y] (x : E)
    (g : Y → E) (hg : Continuous g) (hgx : ∀ y, g y ≠ x) :
    Continuous (fun y => rayExit x (g y)) := by
  have hden : ∀ y, (2 * ‖g y - x‖ ^ 2 : ℝ) ≠ 0 := fun y => by
    have : g y - x ≠ 0 := sub_ne_zero.mpr (hgx y)
    positivity
  have hinner : Continuous (fun y => inner ℝ x (g y - x) : Y → ℝ) :=
    continuous_const.inner (hg.sub continuous_const)
  have hnorm : Continuous (fun y => ‖g y - x‖ ^ 2 : Y → ℝ) :=
    (continuous_norm.comp (hg.sub continuous_const)).pow 2
  have hT : Continuous (fun y => rayT x (g y)) := by
    unfold rayT
    exact ((continuous_const.mul hinner).neg.add
      (((continuous_const.mul hinner).pow 2).sub
        ((continuous_const.mul hnorm).mul continuous_const)).sqrt).div
      (continuous_const.mul hnorm) hden
  exact continuous_const.add (hT.smul (hg.sub continuous_const))

end RayExit

/-! ## §2b. The disk radial retraction and `H₄`-injectivity of the boundary inclusion. -/

/-- **The radial ray-exit retraction** `D⁵∖{x} → ∂D⁵` at an interior point `x` (`‖x‖ < 1`): the
`E⁵`-instance of `rayExit`, wrapped into the double subtype `↥(∂D⁵)`. Continuous
(`continuous_rayExit_comp`); lands on `‖·‖ = 1 = ∂D⁵` (`rayExit_norm` + `boundary_D5`). -/
def diskRetract (x : D5) (hxint : ‖(x : EuclideanSpace ℝ (Fin 5))‖ < 1) :
    C(↑(sub (X := TopCat.of D5) ({x}ᶜ)),
      ↑(sub (X := TopCat.of D5) (((𝓡 4).prod (𝓡∂ 1)).boundary D5))) where
  toFun w :=
    have hvne : ((w : D5) : EuclideanSpace ℝ (Fin 5)) ≠ (x : EuclideanSpace ℝ (Fin 5)) :=
      fun h => w.2 (Subtype.ext h)
    ⟨⟨rayExit (x : EuclideanSpace ℝ (Fin 5)) ((w : D5) : EuclideanSpace ℝ (Fin 5)),
        by rw [mem_closedBall_zero_iff, rayExit_norm _ _ hxint hvne]⟩,
      by rw [mem_boundary_iff_mem_sphere, mem_sphere_zero_iff_norm]
         exact rayExit_norm _ _ hxint hvne⟩
  continuous_toFun := by
    have hg : Continuous
        (fun w : ↑(sub (X := TopCat.of D5) ({x}ᶜ)) =>
          ((w : D5) : EuclideanSpace ℝ (Fin 5))) := by fun_prop
    have hgx : ∀ w : ↑(sub (X := TopCat.of D5) ({x}ᶜ)),
        ((w : D5) : EuclideanSpace ℝ (Fin 5)) ≠ (x : EuclideanSpace ℝ (Fin 5)) :=
      fun w h => w.2 (Subtype.ext h)
    exact Continuous.subtype_mk (Continuous.subtype_mk
      (continuous_rayExit_comp (x : EuclideanSpace ℝ (Fin 5)) _ hg hgx) _) _

/-- **`hincl` — the boundary inclusion `∂D⁵ ↪ D⁵∖{x}` is `H₄`-injective at every interior point.**
The retraction argument: `diskRetract x` is a continuous left inverse of the inclusion on `∂D⁵`
(boundary points are their own ray-exits, `rayExit_of_norm_one`), so
`injective_homologyMap_of_retract` gives injectivity of `Homology.map (subIncl …) 4`. -/
theorem boundaryIncl_injective :
    ∀ (x : ↑(TopCat.of D5)) (hx : x ∉ ((𝓡 4).prod (𝓡∂ 1)).boundary D5),
      Function.Injective
        (Homology.map (subIncl (X := TopCat.of D5)
          (Set.subset_compl_singleton_iff.mpr hx)) 4) := by
  intro x hx
  have hxle : ‖(x : EuclideanSpace ℝ (Fin 5))‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
  have hxne1 : ‖(x : EuclideanSpace ℝ (Fin 5))‖ ≠ 1 := fun h =>
    hx ((mem_boundary_iff_mem_sphere x).mpr (mem_sphere_zero_iff_norm.mpr h))
  have hxint : ‖(x : EuclideanSpace ℝ (Fin 5))‖ < 1 := lt_of_le_of_ne hxle hxne1
  refine injective_homologyMap_of_retract (Set.subset_compl_singleton_iff.mpr hx) 4
    (diskRetract x hxint) ?_
  apply ContinuousMap.ext
  intro b
  apply Subtype.ext
  apply Subtype.ext
  show rayExit (x : EuclideanSpace ℝ (Fin 5)) ((b : D5) : EuclideanSpace ℝ (Fin 5))
      = ((b : D5) : EuclideanSpace ℝ (Fin 5))
  have hbnorm : ‖((b : D5) : EuclideanSpace ℝ (Fin 5))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ((mem_boundary_iff_mem_sphere (b : D5)).mp b.2)
  refine rayExit_of_norm_one _ _ hxint (fun h => ?_) hbnorm
  rw [h] at hbnorm
  exact absurd hbnorm (ne_of_lt hxint)

/-! ## §3. Firing the reduction — the disk relative fundamental class, unconditionally. -/

/-- **The `D⁵` relative fundamental class, unconditionally.** `hasRelFundClass_D5_of_boundaryIncl`
fed the two atoms `β` (`betaClass_ne_zero`) and `hincl` (`boundaryIncl_injective`). -/
theorem hasRelFundClass_D5 :
    HasRelFundClass (X := TopCat.of D5) (((𝓡 4).prod (𝓡∂ 1)).boundary D5)
      (interiorGenFamily (W := D5) ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  PinPlusTraceDiskRelFundReduce.hasRelFundClass_D5_of_boundaryIncl betaClass betaClass_ne_zero
    boundaryIncl_injective

end

end SKEFTHawking.PinPlusTraceDiskCorePair
