/-
# Phase 5q.H — K6′b Leg 12: SMOOTHNESS across the interior flattening

`HalfSpaceInteriorFlatten.flatten` converts a half-space chart into a flat `𝓔³ × ℝ` chart on the
strictly-positive-height region. This module upgrades that from *topological* to *smooth*: a
`contDiffGroupoid` coordinate change for the boundary model `(𝓡 3).prod (𝓡∂ 1)` conjugates into a
`contDiffGroupoid` coordinate change for the self-model `𝓘(ℝ, 𝓔³ × ℝ)`.

**Why it is clean.** The model vector space of `(𝓡 3).prod (𝓡∂ 1)` is the *untagged* `𝓔³ × 𝓔¹`
(`ModelWithCorners.prod` tags only the model *space*, never the vector space), and the flattening is
literally the boundary model followed by a **continuous linear equivalence** `𝓔³ × 𝓔¹ ≃L 𝓔³ × ℝ`:

* `flatten q = flatCoord (I q)` — on the nose, for every `q` (`flatten_eq_flatCoord_model`);
* `flatten.symm p = I.symm (flatCoord.symm p)` for `0 < p.2` — the `max · 0` clamps of `𝓡∂ 1` and of
  `ofHeight` agree there (`flatten_symm_eq`).

So the conjugated transition is `flatCoord ∘ (I ∘ g ∘ I.symm) ∘ flatCoord.symm` on a set that
`flatCoord.symm` carries into `I.symm ⁻¹' g.source ∩ range I` — and `ContDiffOn` is monotone, so the
fact that the boundary-model hypothesis lives on the *non-open* set `… ∩ range I` costs nothing.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.HalfSpaceInteriorFlatten
import SKEFTHawking.ManifoldModelTransport

namespace SKEFTHawking.HalfSpaceInteriorSmooth

open Set Topology
open scoped Manifold
open SKEFTHawking.HalfSpaceInteriorFlatten

noncomputable section

/-- The half-space boundary model with corners of the weld, `(𝓡 3).prod (𝓡∂ 1)`. Its model vector
space is the **untagged** `𝓔³ × 𝓔¹`. -/
abbrev IH : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)) HModel :=
  (𝓡 3).prod (𝓡∂ 1)

/-! ## §1. The linear reshape `𝓔³ × 𝓔¹ ≃L 𝓔³ × ℝ` -/

/-- `𝓔¹ ≃L[ℝ] ℝ` — read off the single coordinate. -/
def e1EquivReal : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 1 => ℝ)).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

@[simp] theorem e1EquivReal_apply (x : EuclideanSpace ℝ (Fin 1)) : e1EquivReal x = x.ofLp 0 := rfl

@[simp] theorem e1EquivReal_symm_apply (t : ℝ) :
    e1EquivReal.symm t = WithLp.toLp 2 (fun _ : Fin 1 => t) := rfl

/-- **The flat coordinate reshape** `𝓔³ × 𝓔¹ ≃L[ℝ] 𝓔³ × ℝ` — the linear part of the flattening. -/
def flatCoord : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] FModel :=
  (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3))).prodCongr e1EquivReal

@[simp] theorem flatCoord_apply (v : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)) :
    flatCoord v = (v.1, v.2.ofLp 0) := rfl

@[simp] theorem flatCoord_symm_apply (p : FModel) :
    flatCoord.symm p = (p.1, WithLp.toLp 2 (fun _ : Fin 1 => p.2)) := rfl

/-! ## §2. `flatten` factors through the boundary model -/

/-- **Forward factorisation** — the flattening is the boundary model followed by the linear
reshape, on the nose. -/
theorem flatten_eq_flatCoord_model (q : HModel) : flatten q = flatCoord (IH q) := rfl

/-- **Backward factorisation on the interior** — the `max · 0` clamp of `𝓡∂ 1` and the `max · 0`
clamp of `ofHeight` agree once the height is nonnegative. -/
theorem flatten_symm_eq {p : FModel} (hp : 0 ≤ p.2) :
    flatten.symm p = IH.symm (flatCoord.symm p) := by
  refine Prod.ext rfl ?_
  apply Subtype.ext
  show WithLp.toLp 2 (fun _ : Fin 1 => max p.2 0)
    = WithLp.toLp 2 (Function.update ((WithLp.toLp 2 (fun _ : Fin 1 => p.2)).ofLp) 0 (max p.2 0))
  congr 1
  funext i
  rw [Subsingleton.elim i 0]
  simp

/-- **The reshape lands in the model range** — the image of a nonnegative-height flat point is in
`range IH`. -/
theorem flatCoord_symm_mem_range {p : FModel} (hp : 0 ≤ p.2) : flatCoord.symm p ∈ range IH := by
  refine ⟨flatten.symm p, Prod.ext rfl ?_⟩
  show WithLp.toLp 2 (fun _ : Fin 1 => max p.2 0) = WithLp.toLp 2 (fun _ : Fin 1 => p.2)
  rw [max_eq_left hp]

/-! ## §3. The `ContDiffOn` transfer -/

/-- **THE TRANSFER.** A boundary-model `ContDiffOn` certificate for a coordinate change `g` gives a
flat-model `ContDiffOn` certificate for the flattened conjugate, on any set of strictly positive
height mapped into `g.source`. -/
theorem contDiffOn_flatConj {n : WithTop ℕ∞} {g : OpenPartialHomeomorph HModel HModel}
    (hg : ContDiffOn ℝ n (IH ∘ g ∘ IH.symm) (IH.symm ⁻¹' g.source ∩ range IH))
    {S : Set FModel} (hpos : ∀ p ∈ S, 0 < p.2)
    (hsrc : ∀ p ∈ S, flatten.symm p ∈ g.source) :
    ContDiffOn ℝ n (fun p => flatten (g (flatten.symm p))) S := by
  have hmaps : ∀ p ∈ S, flatCoord.symm p ∈ IH.symm ⁻¹' g.source ∩ range IH := by
    intro p hp
    have hp0 : (0 : ℝ) ≤ p.2 := le_of_lt (hpos p hp)
    exact ⟨by rw [Set.mem_preimage, ← flatten_symm_eq hp0]; exact hsrc p hp,
      flatCoord_symm_mem_range hp0⟩
  have h1 : ContDiffOn ℝ n ((IH ∘ g ∘ IH.symm) ∘ flatCoord.symm) S :=
    hg.comp flatCoord.symm.contDiff.contDiffOn hmaps
  have h2 : ContDiffOn ℝ n (fun p => flatCoord ((IH ∘ g ∘ IH.symm) (flatCoord.symm p))) S :=
    flatCoord.contDiff.comp_contDiffOn h1
  refine h2.congr (fun p hp => ?_)
  have hp0 : (0 : ℝ) ≤ p.2 := le_of_lt (hpos p hp)
  simp only [Function.comp_apply]
  rw [← flatten_symm_eq hp0, ← flatten_eq_flatCoord_model]

/-! ## §4. The conjugated coordinate change is in the flat groupoid -/

variable {M : Type*} [TopologicalSpace M]

/-- Unfolding the boundary-model groupoid membership into its `ContDiffOn` content. -/
theorem contDiffOn_of_mem_contDiffGroupoid {n : WithTop ℕ∞}
    {g : OpenPartialHomeomorph HModel HModel} (hg : g ∈ contDiffGroupoid n IH) :
    ContDiffOn ℝ n (IH ∘ g ∘ IH.symm) (IH.symm ⁻¹' g.source ∩ range IH) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg
  exact hg.1

/-- The flattened transition's source is of strictly positive height and lands in the underlying
transition's source; and there the two functions agree. -/
theorem flatChart_trans_source_aux {c c' : OpenPartialHomeomorph M HModel}
    {p : FModel} (hp : p ∈ ((flatChart c).symm.trans (flatChart c')).source) :
    0 < p.2 ∧ flatten.symm p ∈ (c.symm.trans c').source := by
  rw [flatChart, flatChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source] at hp
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
  rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hp3
  refine ⟨hp1, ?_⟩
  rw [OpenPartialHomeomorph.trans_source]
  exact ⟨hp2, hp3.1⟩

/-- **THE FLAT-GROUPOID CONJUGATION.** A `C^n` coordinate change for the half-space boundary model
flattens to a `C^n` coordinate change for the boundaryless self-model `𝓘(ℝ, 𝓔³ × ℝ)`. This is the
smooth counterpart of `HalfSpaceInteriorFlatten.flatChart`, and the engine behind the interior
diagonal classes of the weld's transition dispatch. -/
theorem mem_contDiffGroupoid_flatChart {n : WithTop ℕ∞}
    {c c' : OpenPartialHomeomorph M HModel}
    (h : (c.symm.trans c') ∈ contDiffGroupoid n IH) :
    ((flatChart c).symm.trans (flatChart c')) ∈ contDiffGroupoid n 𝓘(ℝ, FModel) := by
  have hsymm : ((flatChart c).symm.trans (flatChart c')).symm
      = (flatChart c').symm.trans (flatChart c) :=
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm _ _ |>.trans (by rw [OpenPartialHomeomorph.symm_symm])
  have main : ∀ (a b : OpenPartialHomeomorph M HModel),
      (a.symm.trans b) ∈ contDiffGroupoid n IH →
      ContDiffOn ℝ n ((flatChart a).symm.trans (flatChart b))
        ((flatChart a).symm.trans (flatChart b)).source := by
    intro a b hab
    refine (contDiffOn_flatConj (contDiffOn_of_mem_contDiffGroupoid hab)
      (fun p hp => (flatChart_trans_source_aux hp).1)
      (fun p hp => (flatChart_trans_source_aux hp).2)).congr ?_
    intro p hp
    rfl
  rw [SKEFTHawking.ManifoldModelTransport.mem_contDiffGroupoid_self]
  refine ⟨main c c' h, ?_⟩
  rw [hsymm, ← OpenPartialHomeomorph.symm_source]
  exact (main c' c (StructureGroupoid.symm _ h)).mono (by rw [hsymm])

end

end SKEFTHawking.HalfSpaceInteriorSmooth
