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

/-- **Mapping cylinder.** A compatible diffeomorphism `φ : s.M ≃ t.M` (with `t.f ∘ φ = s.f`) of the
underlying manifolds gives a bordism `s → t`: the cylinder `s.M × [0,1]` with the top end reparametrized
by `φ⁻¹`. This is the workhorse for the bordism-group laws — **diffeomorphic singular manifolds are
bordant** — and generalizes `reflCylinder` (the `φ = id` case). -/
noncomputable def mapCylinder {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {s t : SingularManifold X k I} (φ : Diffeomorph I I s.M t.M k) (hf : t.f ∘ φ = s.f) :
    Bordism (I.prod (𝓡∂ 1)) s t where
  W := s.M × Set.Icc (0 : ℝ) 1
  e := Sum.elim (fun m => (m, ⊥)) (fun m' => (φ.symm m', ⊤))
  he_smooth :=
    ContMDiff.sumElim (contMDiff_id.prodMk contMDiff_const)
      (φ.symm.contMDiff.prodMk contMDiff_const)
  he_inj := by
    have hbt : (⊥ : Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
      intro h; have := congrArg Subtype.val h; norm_num at this
    rintro (a | a) (b | b) hab <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab
    · rw [hab.1]
    · exact absurd hab.2 hbt
    · exact absurd hab.2.symm hbt
    · rw [φ.symm.injective hab.1]
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
      · exact Or.inr ⟨φ m, φ.symm_apply_apply m, rfl⟩
  g := fun p => s.f p.1
  hg := s.hf.comp continuous_fst
  hg_restrict := by
    funext x
    cases x with
    | inl m => rfl
    | inr m' =>
      show s.f (φ.symm m') = t.f m'
      rw [← hf]; simp [Function.comp, φ.apply_symm_apply]

/-- **Diffeomorphic singular manifolds are bordant.** The driver of the group laws. -/
theorem IsBordant.of_diffeo {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {s t : SingularManifold X k I} (φ : Diffeomorph I I s.M t.M k) (hf : t.f ∘ φ = s.f) :
    IsBordant (I.prod (𝓡∂ 1)) s t :=
  ⟨mapCylinder φ hf⟩

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

/-- The **empty singular manifold** — the additive identity of the bordism group. The `ChartedSpace`
on the empty type is `ChartedSpace.empty` (a `def`, provided locally). -/
noncomputable def emptySM : SingularManifold X k I :=
  haveI : ChartedSpace H PEmpty := ChartedSpace.empty H PEmpty
  SingularManifold.empty X PEmpty I

/-- The empty singular manifold is empty. -/
instance : IsEmpty (emptySM (X := X) (k := k) (I := I)).M :=
  inferInstanceAs (IsEmpty PEmpty)

/-- `⊕` on bordism classes is **commutative** (disjoint union commutes up to diffeomorphism). -/
theorem BordismGrp.add_comm (x y : BordismGrp X k I) : x.add y = y.add x := by
  induction x using Quot.ind with | _ s =>
  induction y using Quot.ind with | _ t =>
  exact mk_eq_of_bordant (IsBordant.of_diffeo (Diffeomorph.sumComm I s.M k t.M)
    (by funext z; rcases z with z | z <;> rfl))

/-- `⊕` on bordism classes is **associative** (disjoint union associates up to diffeomorphism). -/
theorem BordismGrp.add_assoc (x y z : BordismGrp X k I) :
    (x.add y).add z = x.add (y.add z) := by
  induction x using Quot.ind with | _ s =>
  induction y using Quot.ind with | _ t =>
  induction z using Quot.ind with | _ u =>
  exact mk_eq_of_bordant (IsBordant.of_diffeo (Diffeomorph.sumAssoc I s.M k t.M u.M)
    (by funext w; rcases w with (w | w) | w <;> rfl))

/-- The **zero** bordism class: the empty manifold (null-bordant). -/
noncomputable def BordismGrp.zero : BordismGrp X k I := BordismGrp.mk emptySM

/-- `x ⊕ 0 = x` (the empty manifold is a right unit, `M ⊔ ∅ ≅ M`). -/
theorem BordismGrp.add_zero (x : BordismGrp X k I) : x.add zero = x := by
  induction x using Quot.ind with | _ s =>
  exact mk_eq_of_bordant (IsBordant.of_diffeo
    (Diffeomorph.sumEmpty I s.M k (M' := emptySM.M))
    (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim))

/-- `0 ⊕ x = x` (commute, then use the right unit). -/
theorem BordismGrp.zero_add (x : BordismGrp X k I) : zero.add x = x := by
  rw [add_comm]; exact add_zero x

/-- The **doubling bordism**: `M ⊔ M` bounds the cylinder `M × [0,1]` (boundary `M ⊔ M`, target empty),
witnessing `[M] + [M] = 0`. The unoriented bordism group is 2-torsion. -/
noncomputable def doublingBordism (s : SingularManifold X k I) :
    Bordism (I.prod (𝓡∂ 1)) (s.sum s) emptySM where
  W := s.M × Set.Icc (0 : ℝ) 1
  e := Sum.elim (Sum.elim (fun m => (m, ⊥)) (fun m => (m, ⊤))) (fun z => isEmptyElim z)
  he_smooth :=
    ContMDiff.sumElim
      (ContMDiff.sumElim (contMDiff_id.prodMk contMDiff_const)
        (contMDiff_id.prodMk contMDiff_const))
      (fun z => isEmptyElim z)
  he_inj := by
    have hbt : (⊥ : Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
      intro h; have := congrArg Subtype.val h; norm_num at this
    rintro (a | a) (b | b) hab
    · rcases a with a | a <;> rcases b with b | b <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at hab
      · rw [hab.1]
      · exact absurd hab.2 hbt
      · exact absurd hab.2.symm hbt
      · rw [hab.1]
    · exact isEmptyElim b
    · exact isEmptyElim a
    · exact isEmptyElim a
  he_boundary := by
    rw [boundary_product]
    ext ⟨m, t⟩
    constructor
    · rintro ⟨x, hx⟩
      rcases x with (a | a) | z
      · simp only [Sum.elim_inl] at hx; rw [← hx]
        exact Set.mk_mem_prod (Set.mem_univ _) (Set.mem_insert _ _)
      · simp only [Sum.elim_inl, Sum.elim_inr] at hx; rw [← hx]
        exact Set.mk_mem_prod (Set.mem_univ _) (Set.mem_insert_of_mem _ rfl)
      · exact isEmptyElim z
    · intro hmem
      rcases hmem.2 with rfl | rfl
      · exact ⟨Sum.inl (Sum.inl m), rfl⟩
      · exact ⟨Sum.inl (Sum.inr m), rfl⟩
  g := fun p => s.f p.1
  hg := s.hf.comp continuous_fst
  hg_restrict := by
    funext x
    rcases x with (a | a) | z
    · rfl
    · rfl
    · exact isEmptyElim z

noncomputable instance : Zero (BordismGrp X k I) := ⟨BordismGrp.zero⟩
noncomputable instance : Add (BordismGrp X k I) := ⟨BordismGrp.add⟩
/-- The unoriented bordism group is 2-torsion, so negation is the identity. -/
instance : Neg (BordismGrp X k I) := ⟨id⟩

/-- The bordism group is an **additive commutative group** under disjoint union (the empty manifold is
the identity; the unoriented group is 2-torsion, so negation is the identity and `neg_add_cancel` is the
doubling bordism `[M] + [M] = 0`). -/
noncomputable instance : AddCommGroup (BordismGrp X k I) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  add_assoc := BordismGrp.add_assoc
  zero_add := BordismGrp.zero_add
  add_zero := BordismGrp.add_zero
  add_comm := BordismGrp.add_comm
  neg_add_cancel := fun x => by
    induction x using Quot.ind with | _ s =>
      exact BordismGrp.mk_eq_of_bordant ⟨doublingBordism s⟩
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul := zsmulRec
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

end Group

end SKEFTHawking.BordismTheory
