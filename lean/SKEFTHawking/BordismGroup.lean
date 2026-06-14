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

/-! ## §3. The cylinder bordism — reflexivity and the operations' workhorse -/

open scoped Manifold

/-- The **cylinder bordism** `s.M × [0,1]`: a bordism from `s` to itself. The workhorse for reflexivity,
the disjoint-union congruence, and the additive inverse. Built on Mathlib's `Icc` manifold-with-boundary
and its pre-computed product boundary `∂(M × [0,1]) = M × {⊥,⊤}` (`boundary_product`). -/
noncomputable def reflCylinder {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    (s : SingularManifold X k I) :
    Bordism (I.prod (𝓡∂ 1)) s s where
  W := s.M × Set.Icc (0 : ℝ) 1
  e := Sum.elim (fun m => (m, ⊥)) (fun m => (m, ⊤))
  he_smooth :=
    ContMDiff.sumElim (contMDiff_id.prodMk contMDiff_const)
      (contMDiff_id.prodMk contMDiff_const)
  he_inj := by
    have hbt : (⊥ : Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
      intro h; have := congrArg Subtype.val h; norm_num at this
    rintro (a | a) (b | b) hab <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab
    · rw [hab.1]
    · exact absurd hab.2 hbt
    · exact absurd hab.2.symm hbt
    · rw [hab.1]
  he_boundary := by
    rw [boundary_product, Set.Sum.elim_range]
    ext ⟨m, t⟩
    simp only [Set.mem_union, Set.mem_range, Prod.mk.injEq]
    constructor
    · rintro (⟨x, _, rfl⟩ | ⟨x, _, rfl⟩)
      · exact Set.mk_mem_prod (Set.mem_univ _) (Set.mem_insert _ _)
      · exact Set.mk_mem_prod (Set.mem_univ _) (Set.mem_insert_of_mem _ rfl)
    · intro hmem
      rcases hmem.2 with rfl | rfl
      · exact Or.inl ⟨m, rfl, rfl⟩
      · exact Or.inr ⟨m, rfl, rfl⟩
  g := fun p => s.f p.1
  hg := s.hf.comp continuous_fst
  hg_restrict := by funext x; cases x <;> rfl

/-- **Reflexivity** of the cobordism relation, via the cylinder. -/
theorem IsBordant.refl {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    (s : SingularManifold X k I) : IsBordant (I.prod (𝓡∂ 1)) s s :=
  ⟨reflCylinder s⟩

/-! ## §3.5. Disjoint union of bordisms — the `⊕` operation's congruence -/

namespace Bordism

/-- **Disjoint union of bordisms.** `b₁ ⊔ b₂` is a bordism from `s₁ ⊔ s₂` to `t₁ ⊔ t₂` on `W = W₁ ⊔ W₂`.
The boundary identification routes the four pieces through the inclusions `b₁.e`/`b₂.e` into the two
halves. This is the disjoint-union congruence that makes `⊕` well-defined on bordism classes (no gluing). -/
noncomputable def add {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {s₁ t₁ s₂ t₂ : SingularManifold X k I}
    (b₁ : Bordism J s₁ t₁) (b₂ : Bordism J s₂ t₂) :
    Bordism J (s₁.sum s₂) (t₁.sum t₂) where
  W := b₁.W ⊕ b₂.W
  e := Sum.elim
        (Sum.elim (fun a => Sum.inl (b₁.e (Sum.inl a))) (fun a => Sum.inr (b₂.e (Sum.inl a))))
        (Sum.elim (fun a => Sum.inl (b₁.e (Sum.inr a))) (fun a => Sum.inr (b₂.e (Sum.inr a))))
  he_smooth :=
    ContMDiff.sumElim
      (ContMDiff.sumElim (ContMDiff.inl.comp (b₁.he_smooth.comp ContMDiff.inl))
        (ContMDiff.inr.comp (b₂.he_smooth.comp ContMDiff.inl)))
      (ContMDiff.sumElim (ContMDiff.inl.comp (b₁.he_smooth.comp ContMDiff.inr))
        (ContMDiff.inr.comp (b₂.he_smooth.comp ContMDiff.inr)))
  he_inj := by
    rintro (a | a) (c | c) hac <;>
      rcases a with a | a <;> rcases c with c | c <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hac <;>
      first
        | (have := b₁.he_inj hac; aesop)
        | (have := b₂.he_inj hac; aesop)
  he_boundary := by
    rw [ModelWithCorners.boundary_disjointUnion, ← b₁.he_boundary, ← b₂.he_boundary]
    ext w
    simp only [Set.mem_range, Set.mem_union, Set.mem_image, Sum.exists, Sum.elim_inl, Sum.elim_inr]
    aesop
  g := Sum.elim b₁.g b₂.g
  hg := b₁.hg.sumElim b₂.hg
  hg_restrict := by
    funext x
    rcases x with (a | a) | (a | a)
    · exact congrFun b₁.hg_restrict (Sum.inl a)
    · exact congrFun b₂.hg_restrict (Sum.inl a)
    · exact congrFun b₁.hg_restrict (Sum.inr a)
    · exact congrFun b₂.hg_restrict (Sum.inr a)

end Bordism

/-! ## §4. The bordism group `Quot (IsBordant)` (no transitivity/gluing needed) -/

/-- The **bordism group** of `X` (with `X = PUnit` for the absolute `Ω_•^I(pt)`): bordism classes of
closed singular `I`-manifolds, with the canonical `(n+1)`-bordism model `I.prod (𝓡∂ 1)`. `Quot`
quotients by the cobordism relation directly — it identifies via the relation's equivalence-closure, so
**no transitivity (manifold-gluing) proof is needed**, and the quotient is the genuine bordism group. -/
def BordismGrp (X : Type*) [TopologicalSpace X] (k : WithTop ℕ∞)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) : Type _ :=
  Quot (IsBordant (I.prod (𝓡∂ 1)) : SingularManifold X k I → SingularManifold X k I → Prop)

/-- The bordism class of a closed singular manifold. -/
def BordismGrp.mk {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} (s : SingularManifold X k I) :
    BordismGrp X k I :=
  Quot.mk _ s

/-- Bordant manifolds have the same bordism class. -/
theorem BordismGrp.mk_eq_of_bordant {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {s t : SingularManifold X k I}
    (h : IsBordant (I.prod (𝓡∂ 1)) s t) : BordismGrp.mk s = BordismGrp.mk t :=
  Quot.sound h

/-! ## §5. The disjoint-union operation on the bordism group -/

section Group
variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **Disjoint union `⊕` on bordism classes.** Well-defined via `Bordism.add` + the cylinder: the
congruence `s ~ s' ⟹ s ⊔ t ~ s' ⊔ t` is `Bordism.add (bordism) (reflCylinder t)`, with no gluing. -/
noncomputable def BordismGrp.add (x y : BordismGrp X k I) : BordismGrp X k I :=
  Quot.lift₂ (fun s t => BordismGrp.mk (s.sum t))
    (fun s _t _t' h => h.elim fun b => mk_eq_of_bordant ⟨Bordism.add (reflCylinder s) b⟩)
    (fun _s _s' t h => h.elim fun b => mk_eq_of_bordant ⟨Bordism.add b (reflCylinder t)⟩)
    x y

@[simp] theorem BordismGrp.add_mk (s t : SingularManifold X k I) :
    BordismGrp.add (BordismGrp.mk s) (BordismGrp.mk t) = BordismGrp.mk (s.sum t) :=
  rfl

end Group

end SKEFTHawking.BordismTheory
