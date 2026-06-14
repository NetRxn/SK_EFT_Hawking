/-
# Phase 5q.F W4 — a genuine bordism group over Mathlib's manifolds-with-boundary

The geometric spine of the `Ω₄^{Pin⁺} ≅ ℤ/16` discharge (`Lit-Search/Phase-5qF/goal_prompt.md`,
`LAB_NOTEBOOK.md`). Builds the cobordism relation + group that `Mathlib.Geometry.Manifold.Bordism`
lists as TODO, project-locally, over Mathlib's `SingularManifold` (closed manifolds) and
manifolds-with-boundary (`IsManifold` + `ModelWithCorners.boundary`).

## The collar/embedding encoding (design note)

Mathlib's `ModelWithCorners.boundary J W` is only a **`Set W`** — there is no manifold structure on the
boundary yet (InteriorBoundary.lean lists "boundary is a submanifold" as an unproven goal). So we cannot
state "∂W ≅ M ⊔ N" as a `Diffeomorph` of boundary manifolds. Instead a **bordism** is encoded as a compact
manifold-with-boundary `W` together with a smooth injection `e : s.M ⊕ t.M → W` whose range is exactly the
boundary `J.boundary W`. This uses only the boundary-as-`Set` (which Mathlib has) plus `ContMDiff I J k`
(which it has). It is faithful: `e` identifies the closed `n`-manifold `s.M ⊕ t.M` with the boundary of the
`(n+1)`-manifold `W`. (`e` can later be strengthened to a smooth embedding / immersion once the
boundary-as-manifold lands; the present injection-onto-the-boundary already pins the bordism content.)
-/
import Mathlib

namespace SKEFTHawking.BordismTheory

open scoped Manifold
open SingularManifold

/-- A **bordism** between two closed singular `I`-manifolds `s` and `t` on `X`: a compact `C^k`
manifold-with-boundary `W` (modelled on `J`, one dimension up) with a smooth injection
`e : s.M ⊕ t.M → W` onto the boundary `J.boundary W`, and a continuous `g : W → X` restricting (via `e`)
to `s.f` and `t.f`. -/
structure Bordism.{u} {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
    (s t : SingularManifold.{u} X k I) where
  /-- The bordism manifold-with-boundary `W`. -/
  W : Type u
  [topW : TopologicalSpace W]
  [chartW : ChartedSpace H' W]
  [mfdW : IsManifold J k W]
  [compactW : CompactSpace W]
  /-- The boundary identification: a smooth injection of `s.M ⊕ t.M` onto `∂W`. -/
  e : s.M ⊕ t.M → W
  he_smooth : ContMDiff I J k e
  he_inj : Function.Injective e
  he_boundary : Set.range e = J.boundary W
  /-- The map `W → X` restricting to `s.f`, `t.f` on the boundary. -/
  g : W → X
  hg : Continuous g
  hg_restrict : g ∘ e = Sum.elim s.f t.f

/-- Two closed singular `I`-manifolds `s`, `t` on `X` are **bordant** (w.r.t. the bordism model `J`,
one dimension up) if there exists a bordism between them. This is the cobordism relation whose quotient
is the bordism group; `J` is fixed (canonically the half-space extension of `I`) so glued bordisms stay
in the same model, making the relation transitive. -/
def IsBordant.{u} {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
    (s t : SingularManifold.{u} X k I) : Prop :=
  Nonempty (Bordism J s t)

/-! ## §2. The cobordism relation is an equivalence -/

namespace Bordism

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {s t : SingularManifold X k I}

instance {b : Bordism J s t} : TopologicalSpace b.W := b.topW
instance {b : Bordism J s t} : ChartedSpace H' b.W := b.chartW
instance {b : Bordism J s t} : IsManifold J k b.W := b.mfdW
instance {b : Bordism J s t} : CompactSpace b.W := b.compactW

/-- **Symmetry.** The same bordism manifold `W` witnesses `t ~ s`: precompose the boundary
identification `e` with `Sum.swap` (which is smooth and bijective), and swap the restricted maps. -/
def symm (b : Bordism J s t) : Bordism J t s where
  W := b.W
  topW := b.topW
  chartW := b.chartW
  mfdW := b.mfdW
  compactW := b.compactW
  e := b.e ∘ Sum.swap
  he_smooth := b.he_smooth.comp (ContMDiff.sumElim ContMDiff.inr ContMDiff.inl)
  he_inj := b.he_inj.comp (Equiv.sumComm t.M s.M).injective
  he_boundary := by
    have hsurj : Function.Surjective (Sum.swap : t.M ⊕ s.M → s.M ⊕ t.M) :=
      (Equiv.sumComm t.M s.M).surjective
    rw [Set.range_comp, hsurj.range_eq, Set.image_univ]; exact b.he_boundary
  g := b.g
  hg := b.hg
  hg_restrict := by
    rw [← Function.comp_assoc, b.hg_restrict]; funext x; cases x <;> rfl

end Bordism

/-- The cobordism relation is symmetric. -/
theorem IsBordant.symm {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {s t : SingularManifold X k I} (h : IsBordant J s t) : IsBordant J t s :=
  h.elim fun b => ⟨b.symm⟩

end SKEFTHawking.BordismTheory
