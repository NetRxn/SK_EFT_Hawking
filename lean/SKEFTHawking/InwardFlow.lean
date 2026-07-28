/-
Copyright (c) 2026 SK-EFT Hawking project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.MeanValue

/-!
# One-sided flow of an inward-pointing vector field

The third collar prerequisite, in its model-space form. Mathlib records as an open TODO in
`Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean` "the case where the integral curve may
venture to the boundary of the manifold. See Theorem 9.34, Lee"; correspondingly
`exists_isMIntegralCurveAt_of_contMDiffAt` requires `I.IsInteriorPoint x₀`, and every uniform-time
result in `IntegralCurve/UniformTime.lean` carries `[BoundarylessManifold I M]`.

**The ODE half of that gap is not actually missing.** `IsPicardLindelof f t₀ x₀ a r L K` only asks
`t₀ : Icc tmin tmax` — `t₀` may be an **endpoint** — and
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` then yields a solution on
`Icc tmin tmax` whose derivative is a `HasDerivWithinAt` relative to that interval. Taking
`tmin = t₀ = 0` gives a genuine one-sided solution on `[0, ε]`, with no interiority anywhere.

What *is* missing, and is supplied here, is the **barrier**: the reason such a trajectory is
admissible, i.e. does not immediately leave the half space in which the manifold-with-boundary
lives. For a field whose `φ`-component is bounded below by `c > 0`, the affine function
`t ↦ φ x₀ + c t` is a lower fence for `φ ∘ α`, so the trajectory stays in `{0 ≤ φ}` and in fact
enters `{0 < φ}` immediately.

## Main results

* `exists_forward_flow_of_inward`: the fenced one-sided flow, `φ x₀ + c t ≤ φ (α t)`.
* `exists_forward_flow_halfSpace`: the half-space form — stays in `{0 ≤ φ}`, strictly inside
  `{0 < φ}` for `t > 0`.

Both are stated for an arbitrary complete normed space and an arbitrary continuous linear
functional, with no manifold structure and no reference to the bordism stack; the transport to the
bordism model's range is `SKEFTHawking.Collar.exists_forward_flow_prodHalf`.

## Remaining wall (manifold level)

`IsMIntegralCurveAt` is intrinsically two-sided (`HasMFDerivAt`), so lifting the above to a
manifold with boundary needs a *new* one-sided notion — an `IsMIntegralCurveWithinAt` on `Ici t₀`,
together with its uniqueness and uniform-time theory. That is a genuine API addition, not a
consequence of what is here.
-/

open Set Filter Metric
open scoped NNReal Topology

namespace SKEFTHawking.Collar

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Forward flow of a globally Lipschitz, bounded vector field, with an inward barrier.** -/
theorem exists_forward_flow_of_inward {v : F → F} {K L : ℝ≥0} (hlip : LipschitzWith K v)
    (hbdd : ∀ x, ‖v x‖ ≤ L) {φ : F →L[ℝ] ℝ} {c : ℝ} (hφ : ∀ x, c ≤ φ (v x))
    (x₀ : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ → F, α 0 = x₀ ∧
      (∀ t ∈ Icc (0 : ℝ) ε, HasDerivWithinAt α (v (α t)) (Icc (0 : ℝ) ε) t) ∧
      ∀ t ∈ Icc (0 : ℝ) ε, φ x₀ + c * t ≤ φ (α t) := by
  have ht₀ : (0 : ℝ) ∈ Icc (0 : ℝ) ε := ⟨le_rfl, hε.le⟩
  have hPL : IsPicardLindelof (fun _ : ℝ => v) (⟨0, ht₀⟩ : Icc (0 : ℝ) ε) x₀
      (L * ⟨ε, hε.le⟩) 0 L K :=
    { lipschitzOnWith := fun _ _ => hlip.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ x _ => hbdd x
      mul_max_le := by
        simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hε.le] }
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨α, hα0, hα, ?_⟩
  -- the barrier: `φ ∘ α` dominates the affine lower boundary `t ↦ φ x₀ + c t`
  have hcont : ContinuousOn (fun t => φ (α t)) (Icc (0 : ℝ) ε) := fun t ht =>
    (φ.continuous.continuousWithinAt).comp (hα t ht).continuousWithinAt (mapsTo_image _ _ |>.mono
      subset_rfl (subset_refl _)) |>.mono subset_rfl
  refine image_le_of_deriv_right_le_deriv_boundary
    (f := fun t => φ x₀ + c * t) (f' := fun _ => c) (B := fun t => φ (α t))
    (B' := fun t => φ (v (α t))) ?_ ?_ (by simp [hα0]) hcont ?_ ?_
  · exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
  · intro t _
    simpa using ((hasDerivAt_id t).const_mul c).const_add (φ x₀) |>.hasDerivWithinAt
  · intro t ht
    have hsub : Icc t ε ∈ 𝓝[Ici t] t :=
      inter_mem_nhdsWithin (Ici t) (Iic_mem_nhds ht.2)
    have hd : HasDerivWithinAt α (v (α t)) (Icc t ε) t :=
      (hα t ⟨ht.1, ht.2.le⟩).mono (Icc_subset_Icc ht.1 le_rfl)
    exact (φ.hasFDerivAt.comp_hasDerivWithinAt t (hd.mono_of_mem_nhdsWithin hsub))
  · exact fun t _ => hφ (α t)

/-- **Flow out of the boundary of a closed half space.**

If the vector field `v` is globally Lipschitz and bounded, and its `φ`-component is bounded below
by `c > 0` (it points strictly *into* the half space `{x | 0 ≤ φ x}`), then the forward trajectory
from any point of the closed half space

* exists on `[0, ε]` for **every** `ε > 0`, as a genuine one-sided solution — the derivative is a
  `HasDerivWithinAt` relative to `Icc 0 ε`, with `0` an endpoint;
* stays in the closed half space; and
* enters the **open** half space immediately and stays there.

This is the model-space content of Mathlib's own TODO in
`Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean` ("the case where the integral curve may
venture to the boundary of the manifold"). The ODE half is not in fact missing —
`IsPicardLindelof f t₀ x₀ a r L K` only requires `t₀ : Icc tmin tmax`, so `t₀` is allowed to be an
endpoint — what is missing, and is supplied here, is the barrier argument that keeps the
trajectory admissible. -/
theorem exists_forward_flow_halfSpace {v : F → F} {K L : ℝ≥0} (hlip : LipschitzWith K v)
    (hbdd : ∀ x, ‖v x‖ ≤ L) {φ : F →L[ℝ] ℝ} {c : ℝ} (hc : 0 < c) (hφ : ∀ x, c ≤ φ (v x))
    {x₀ : F} (hx₀ : 0 ≤ φ x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ → F, α 0 = x₀ ∧
      (∀ t ∈ Icc (0 : ℝ) ε, HasDerivWithinAt α (v (α t)) (Icc (0 : ℝ) ε) t) ∧
      (∀ t ∈ Icc (0 : ℝ) ε, 0 ≤ φ (α t)) ∧
      ∀ t ∈ Ioc (0 : ℝ) ε, 0 < φ (α t) := by
  obtain ⟨α, hα0, hα, hbar⟩ := exists_forward_flow_of_inward hlip hbdd hφ x₀ hε
  refine ⟨α, hα0, hα, fun t ht => ?_, fun t ht => ?_⟩
  · exact le_trans (add_nonneg hx₀ (mul_nonneg hc.le ht.1)) (hbar t ht)
  · exact lt_of_lt_of_le (mul_pos hc ht.1)
      (le_trans (le_add_of_nonneg_left hx₀) (hbar t ⟨ht.1.le, ht.2⟩))

end SKEFTHawking.Collar
