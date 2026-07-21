/-
# The `k = 0` vs `k ≥ 1` SEPARATING WITNESS — there is no generic C⁰ → C¹ transport

Companion to `PinPlusRegularityFence.lean`, which established that at `k = 0` the
`IsManifold` binder is **free** (`isManifoldZero_free`), and explicitly declined the stronger
claim.  This module supplies that stronger claim.

See the module's §4 for the precise scope of what is and is not established.
-/

import Mathlib
import SKEFTHawking.PinPlusRegularityFence

namespace SKEFTHawking.PinPlusRegularitySeparation

open scoped Manifold

/-! ## §1. The kink — a homeomorphism of `ℝ` whose inverse is not differentiable at `0` -/

/-- `kink t = max t (2t)`: the identity on `t ≤ 0`, doubling on `t ≥ 0`. -/
noncomputable def kink (t : ℝ) : ℝ := max t (2 * t)

/-- The inverse kink `min t (t/2)`: the identity on `t ≤ 0`, halving on `t ≥ 0`. -/
noncomputable def kinkInv (t : ℝ) : ℝ := min t (t / 2)

theorem kinkInv_of_nonpos {t : ℝ} (h : t ≤ 0) : kinkInv t = t := by
  simp only [kinkInv, min_eq_left_iff]; linarith

theorem kinkInv_of_nonneg {t : ℝ} (h : 0 ≤ t) : kinkInv t = t / 2 := by
  simp only [kinkInv, min_eq_right_iff]; linarith

theorem kink_of_nonpos {t : ℝ} (h : t ≤ 0) : kink t = t := by
  simp only [kink, max_eq_left_iff]; linarith

theorem kink_of_nonneg {t : ℝ} (h : 0 ≤ t) : kink t = 2 * t := by
  simp only [kink, max_eq_right_iff]; linarith

theorem continuous_kink : Continuous kink :=
  continuous_id.max (continuous_const.mul continuous_id)

theorem continuous_kinkInv : Continuous kinkInv :=
  continuous_id.min (continuous_id.div_const 2)

theorem kinkInv_kink (t : ℝ) : kinkInv (kink t) = t := by
  rcases le_total t 0 with h | h
  · rw [kink_of_nonpos h, kinkInv_of_nonpos h]
  · rw [kink_of_nonneg h, kinkInv_of_nonneg (by linarith)]; ring

theorem kink_kinkInv (t : ℝ) : kink (kinkInv t) = t := by
  rcases le_total t 0 with h | h
  · rw [kinkInv_of_nonpos h, kink_of_nonpos h]
  · rw [kinkInv_of_nonneg h, kink_of_nonneg (by linarith)]; ring

/-- The kink as a self-homeomorphism of `ℝ`. -/
noncomputable def kinkHomeo : ℝ ≃ₜ ℝ where
  toFun := kink
  invFun := kinkInv
  left_inv := kinkInv_kink
  right_inv := kink_kinkInv
  continuous_toFun := continuous_kink
  continuous_invFun := continuous_kinkInv

/-- **The kink's inverse is not differentiable at `0`** — its one-sided derivatives there are
`1` (from the left) and `1/2` (from the right).  This single analytic fact is the entire
engine of the separation below. -/
theorem not_differentiableAt_kinkInv : ¬ DifferentiableAt ℝ kinkInv 0 := by
  intro h
  have hIci : HasDerivWithinAt kinkInv (1 / 2 : ℝ) (Set.Ici 0) 0 :=
    ((hasDerivAt_id (0 : ℝ)).div_const 2).hasDerivWithinAt.congr
      (fun y hy => (kinkInv_of_nonneg hy)) (by simp [kinkInv_of_nonneg])
  have hIic : HasDerivWithinAt kinkInv (1 : ℝ) (Set.Iic 0) 0 :=
    (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt.congr
      (fun y hy => (kinkInv_of_nonpos hy)) (by simp [kinkInv_of_nonpos])
  have hd := h.hasDerivAt
  have e1 : derivWithin kinkInv (Set.Ici 0) 0 = 1 / 2 :=
    hIci.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))
  have e1' : derivWithin kinkInv (Set.Ici 0) 0 = deriv kinkInv 0 :=
    hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))
  have e2 : derivWithin kinkInv (Set.Iic 0) 0 = 1 :=
    hIic.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
  have e2' : derivWithin kinkInv (Set.Iic 0) 0 = deriv kinkInv 0 :=
    hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
  rw [e1] at e1'
  rw [e2, ← e1'] at e2'
  norm_num at e2'

/-! ## §2. The kink shear — a self-homeomorphism of a normed space that is not `C¹` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Shear a normed space along the line `ℝ ∙ v` by the kink read off the functional `f`. -/
noncomputable def shear (f : E →L[ℝ] ℝ) (v c : E) (x : E) : E :=
  x + (kink (f x - f c) - (f x - f c)) • v

/-- The inverse shear. -/
noncomputable def shearInv (f : E →L[ℝ] ℝ) (v c : E) (x : E) : E :=
  x + (kinkInv (f x - f c) - (f x - f c)) • v

theorem shear_apply_sub (f : E →L[ℝ] ℝ) (v c : E) (hv : f v = 1) (x : E) :
    f (shear f v c x) - f c = kink (f x - f c) := by
  simp only [shear, map_add, ContinuousLinearMap.map_smul, smul_eq_mul, hv, mul_one]
  ring

theorem shearInv_apply_sub (f : E →L[ℝ] ℝ) (v c : E) (hv : f v = 1) (x : E) :
    f (shearInv f v c x) - f c = kinkInv (f x - f c) := by
  simp only [shearInv, map_add, ContinuousLinearMap.map_smul, smul_eq_mul, hv, mul_one]
  ring

theorem shearInv_shear (f : E →L[ℝ] ℝ) (v c : E) (hv : f v = 1) (x : E) :
    shearInv f v c (shear f v c x) = x := by
  rw [shearInv, shear_apply_sub f v c hv, kinkInv_kink, shear]
  module

theorem shear_shearInv (f : E →L[ℝ] ℝ) (v c : E) (hv : f v = 1) (x : E) :
    shear f v c (shearInv f v c x) = x := by
  rw [shear, shearInv_apply_sub f v c hv, kink_kinkInv, shearInv]
  module

/-- The kink shear as a self-homeomorphism of `E`, kinking exactly on the hyperplane `f x = f c`
(in particular at `c` itself). -/
noncomputable def shearHomeo (f : E →L[ℝ] ℝ) (v c : E) (hv : f v = 1) : E ≃ₜ E where
  toFun := shear f v c
  invFun := shearInv f v c
  left_inv := shearInv_shear f v c hv
  right_inv := shear_shearInv f v c hv
  continuous_toFun := by
    exact continuous_id.add (((continuous_kink.comp
      (f.continuous.sub continuous_const)).sub (f.continuous.sub continuous_const)).smul
      continuous_const)
  continuous_invFun := by
    exact continuous_id.add (((continuous_kinkInv.comp
      (f.continuous.sub continuous_const)).sub (f.continuous.sub continuous_const)).smul
      continuous_const)

/-- The shear fixes its kink point. -/
theorem shear_self (f : E →L[ℝ] ℝ) (v c : E) : shear f v c c = c := by
  simp [shear, kink_of_nonneg (le_refl (0 : ℝ))]

/-- **The inverse shear is not differentiable at the kink point `c`.**  Restricting it to the
line `t ↦ c + t • v` and reading off `f` recovers `kinkInv`, which is not differentiable at `0`. -/
theorem not_differentiableAt_shearInv (f : E →L[ℝ] ℝ) (v c : E) (hv : f v = 1) :
    ¬ DifferentiableAt ℝ (shearInv f v c) c := by
  intro h
  have hγ : DifferentiableAt ℝ (fun t : ℝ => c + t • v) 0 :=
    (differentiableAt_const c).add (differentiableAt_id.smul_const v)
  have hc : (fun t : ℝ => c + t • v) 0 = c := by simp
  have hcomp : DifferentiableAt ℝ (fun t : ℝ => shearInv f v c (c + t • v)) 0 := by
    have := DifferentiableAt.comp (𝕜 := ℝ) 0 (hc ▸ h) hγ
    simpa [Function.comp_def] using this
  have hf : DifferentiableAt ℝ (fun t : ℝ => f (shearInv f v c (c + t • v)) - f c) 0 :=
    ((f.differentiableAt).comp 0 hcomp).sub (differentiableAt_const _)
  have heq : (fun t : ℝ => f (shearInv f v c (c + t • v)) - f c) = kinkInv := by
    funext t
    rw [shearInv_apply_sub f v c hv]
    congr 1
    simp [hv]
  rw [heq] at hf
  exact not_differentiableAt_kinkInv hf

/-! ## §3. The separating witness -/

/-- The zeroth coordinate functional on `ℝ⁴`. -/
noncomputable def coord4 : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ := EuclideanSpace.proj 0

/-- The zeroth coordinate vector of `ℝ⁴`. -/
noncomputable def vec4 : EuclideanSpace ℝ (Fin 4) := EuclideanSpace.single 0 1

theorem coord4_vec4 : coord4 vec4 = 1 := by simp [coord4, vec4]

/-- **The twist**: a self-homeomorphism of `ℝ⁴` whose inverse is not differentiable at `c`. -/
noncomputable def twist (c : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) ≃ₜ EuclideanSpace ℝ (Fin 4) :=
  shearHomeo coord4 vec4 c coord4_vec4

/-- `ℝ⁴` carrying the two-element atlas `{id, twist}` instead of its standard one. -/
def TwistedR4 : Type := EuclideanSpace ℝ (Fin 4)

instance : TopologicalSpace TwistedR4 :=
  inferInstanceAs (TopologicalSpace (EuclideanSpace ℝ (Fin 4)))

noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin 4)) TwistedR4 where
  atlas := {OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 4)),
            (twist 0).toOpenPartialHomeomorph}
  chartAt _ := OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 4))
  mem_chart_source _ := Set.mem_univ _
  chart_mem_atlas _ := Set.mem_insert _ _

theorem twistedR4_isManifold_zero : IsManifold (𝓡 4) 0 TwistedR4 :=
  PinPlusRegularityFence.isManifoldZero_free (𝓡 4)

theorem twistedR4_not_isManifold_one : ¬ IsManifold (𝓡 4) 1 TwistedR4 := by
  intro h
  have hrefl : (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 4)) :
      OpenPartialHomeomorph TwistedR4 (EuclideanSpace ℝ (Fin 4)))
      ∈ atlas (EuclideanSpace ℝ (Fin 4)) TwistedR4 := Set.mem_insert _ _
  have htw : ((twist 0).toOpenPartialHomeomorph :
      OpenPartialHomeomorph TwistedR4 (EuclideanSpace ℝ (Fin 4)))
      ∈ atlas (EuclideanSpace ℝ (Fin 4)) TwistedR4 :=
    Set.mem_insert_of_mem _ rfl
  have hcomp := StructureGroupoid.compatible (contDiffGroupoid 1 (𝓡 4)) hrefl htw
  erw [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans,
    mem_groupoid_of_pregroupoid] at hcomp
  have h2 := hcomp.2
  simp only [contDiffPregroupoid, Homeomorph.toOpenPartialHomeomorph_symm_apply,
    Homeomorph.toOpenPartialHomeomorph_target, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Set.preimage_id, Set.range_id, Set.inter_univ,
    Function.comp_def, id_eq] at h2
  have hdiff : DifferentiableAt ℝ (shearInv coord4 vec4 0) 0 :=
    (h2.differentiableOn one_ne_zero).differentiableAt Filter.univ_mem
  exact not_differentiableAt_shearInv coord4 vec4 0 coord4_vec4 hdiff

/-! ## §4. The headline — there is NO generic `k = 0 ⟹ k ≥ 1` transport

This is the direct answer to the question `PinPlusRegularityFence` left open. -/

/-- **NO GENERIC `C⁰ → C¹` TRANSPORT FOR THE `𝓡 4` REGULARITY BINDER.**

Any proposed bridge of the shape "every `k = 0` charted space over `𝓡 4` is also a `k ≥ 1`
manifold" — i.e. any attempt to reinterpret a `k := 0` conclusion as a smooth-category
conclusion by transporting the binder — is **false**, kernel-checked: `TwistedR4` satisfies
`IsManifold (𝓡 4) 0` (freely, by `isManifoldZero_free`) and provably fails
`IsManifold (𝓡 4) 1`, because its atlas `{id, twist 0}` has the transition `twist 0`, whose
inverse is not differentiable at `0` (`not_differentiableAt_shearInv`, ultimately
`not_differentiableAt_kinkInv`).

Together with `PinPlusRegularityFence.isManifoldZero_free`, this settles the fence's open
question in the NEGATIVE: the `k = 0` statements of the KT lane cannot be re-read as smooth
statements by any generic transport. They must either be re-declared at `k ≥ 1`, or quoted
with their regularity level attached. -/
theorem no_generic_zero_to_one_transport :
    ¬ ∀ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 4)) M),
        IsManifold (𝓡 4) 0 M → IsManifold (𝓡 4) 1 M := by
  intro hall
  exact twistedR4_not_isManifold_one
    (hall TwistedR4 inferInstance inferInstance twistedR4_isManifold_zero)

/-! ## §5. SCOPE — what this does and does not establish

* **ESTABLISHED (kernel):** the `𝓡 4` regularity binder genuinely separates `k = 0` from
  `k = 1`.  `TwistedR4` is a charted space over the model of the KT carrier that is a `C⁰`
  manifold and is *not* a `C¹` manifold.  Hence **no generic transport of a `k = 0`
  conclusion to `k ≥ 1` can exist** (`no_generic_zero_to_one_transport`).  Route (B) — "prove
  `k = 0 ⟹ k ≥ 1` for the carrier as actually used" — is therefore closed as a general
  strategy: the only remaining route to a smooth-category reading is to *re-declare* the
  assembly at `k ≥ 1`.

* **NOT established *here* — the carrier-level witness (but see below).** `TwistedR4` is
  **not compact**, so it is not itself an element of `SingularManifold PUnit 0 (𝓡 4)` (which
  requires `[CompactSpace M]` and `[BoundarylessManifold I M]`; see
  `Mathlib/Geometry/Manifold/Bordism.lean:120`).  **`PinPlusRegularitySeparationCarrier`
  supplies the compact version** — `Twisted ℝP⁴`, and
  `exists_carrier_element_not_smooth : ∃ s : SingularManifold PUnit 0 (𝓡 4),
  ¬ IsManifold (𝓡 4) 1 s.M`.

* **NOT established here — a bordism-group inequality.** Even a carrier-level witness would
  show the C⁰ *object class* is strictly larger; it would **not** by itself show the C⁰
  *bordism group* is larger (bordism could identify the extra objects).  The
  Kirby–Siebenmann statement `Ω₄^{TopPin⁺} ≅ ℤ/2 ⊕ ℤ/8` quoted in
  `Phase5qH_LiteratureGradeUnconditional_Roadmap.md` §2 leg 2 is **not** formalized here and
  is not claimed.  Nothing in this module is evidence that the KT lane's ℤ/16 mathematics is
  wrong; what it shows is that the lane's *statements as declared* are C⁰ statements and
  cannot be silently promoted. -/

end SKEFTHawking.PinPlusRegularitySeparation
