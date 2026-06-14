/-
# Phase 5q.F W4 (tangential layer) — the tangential-structure interface on the bordism group

Refines the genuine unoriented bordism group of `BordismGroup.lean` to **tangential bordism**
(`Ω^ξ`): bordism classes of closed manifolds carrying a tangential structure `ξ`, via bordisms also
carrying `ξ`. Pin⁺/Spin/Spin-ℤ₄ are instances. Per `Lit-Search/Phase-5qF/goal_prompt.md`: the goal's
`Ω₄^{Pin⁺}` is the `Pin⁺`-tangential bordism group; the Smith-LES route assembles it from the classical
tangential groups.

## The Prop-interface (design note)

A tangential structure is modeled as a **pair of conditions** — `onMfd` on closed manifolds (its
characteristic-class condition, e.g. Pin⁺ ⟺ `w₂ = 0`) and `onBor` on bordism manifolds — closed under
the bordism operations (empty, disjoint union, cylinder, symmetry) so that the `ξ`-refined cobordism
relation on `ξ`-manifolds is reflexive/symmetric and `⊕`-congruent. This is the goal's
"tangential Prop-interface"; the genuine manifold/cobordism content is `BordismGroup.lean`, reused
verbatim. The trivial structure (`onMfd = onBor = True`) recovers the unoriented group `Ω^O`.
-/
import Mathlib
import SKEFTHawking.BordismGroup

namespace SKEFTHawking.TangentialBordism

open SKEFTHawking.BordismTheory
open scoped Manifold

/-- A **tangential structure** for `I`-manifold bordism: a condition `onMfd` on closed singular
manifolds (the characteristic-class condition — Pin⁺ ⟺ `w₂=0`, Spin ⟺ `w₁=w₂=0`, …) and a condition
`onBor` on bordism manifolds, closed under the operations. Pin⁺/Spin/Spin-ℤ₄ are instances. -/
structure TangentialStr.{u} (X : Type*) [TopologicalSpace X] (k : WithTop ℕ∞)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless] where
  /-- The tangential condition on a closed singular manifold. -/
  onMfd : SingularManifold.{u} X k I → Prop
  /-- The tangential condition on a bordism manifold. -/
  onBor : {s t : SingularManifold.{u} X k I} → Bordism.{u} (I.prod (𝓡∂ 1)) s t → Prop
  /-- The empty manifold carries the structure. -/
  onEmpty : onMfd emptySM
  /-- Disjoint unions of `ξ`-manifolds are `ξ`-manifolds. -/
  onSum : {s t : SingularManifold.{u} X k I} → onMfd s → onMfd t → onMfd (s.sum t)
  /-- The cylinder of a `ξ`-manifold is a `ξ`-bordism (so the relation stays reflexive). -/
  cyl_onBor : {s : SingularManifold.{u} X k I} → onMfd s → onBor (reflCylinder s)
  /-- Disjoint unions of `ξ`-bordisms are `ξ`-bordisms (for the `⊕`-congruence). -/
  add_onBor : {s₁ t₁ s₂ t₂ : SingularManifold.{u} X k I} → {b₁ : Bordism.{u} (I.prod (𝓡∂ 1)) s₁ t₁} →
    {b₂ : Bordism.{u} (I.prod (𝓡∂ 1)) s₂ t₂} → onBor b₁ → onBor b₂ → onBor (b₁.add b₂)
  /-- The reverse of a `ξ`-bordism is a `ξ`-bordism (for symmetry). -/
  symm_onBor : {s t : SingularManifold.{u} X k I} → {b : Bordism.{u} (I.prod (𝓡∂ 1)) s t} →
    onBor b → onBor b.symm
  /-- The mapping cylinder of a `ξ`-manifold is a `ξ`-bordism (covers refl + the group laws via the
  sum diffeomorphisms). -/
  mapCyl_onBor : {s t : SingularManifold.{u} X k I} → {φ : Diffeomorph I I s.M t.M k} →
    {hf : t.f ∘ φ = s.f} → onMfd s → onBor (mapCylinder φ hf)
  /-- The doubling bordism `M ⊔ M ~ ∅` of a `ξ`-manifold is a `ξ`-bordism (for the additive inverse). -/
  doubling_onBor : {s : SingularManifold.{u} X k I} → onMfd s → onBor (doublingBordism s)

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- The **trivial (unoriented) tangential structure** — every manifold and bordism qualifies; the
`ξ`-bordism group recovers the unoriented `Ω^O`. -/
def trivialTangentialStr : TangentialStr X k I where
  onMfd _ := True
  onBor _ := True
  onEmpty := trivial
  onSum _ _ := trivial
  cyl_onBor _ := trivial
  add_onBor _ _ := trivial
  symm_onBor _ := trivial
  mapCyl_onBor _ := trivial
  doubling_onBor _ := trivial

/-! ## The `ξ`-tangential bordism group `Ω^ξ` -/

/-- The **`ξ`-tangential cobordism relation**: a bordism between two `ξ`-manifolds that itself carries
the tangential structure `ξ`. (`Quot` of this is `Ω^ξ`; transitivity/gluing is handled by `Quot`.) -/
def IsTangentiallyBordant.{u} (ξ : TangentialStr.{u} X k I)
    (s t : {s : SingularManifold.{u} X k I // ξ.onMfd s}) : Prop :=
  ∃ b : Bordism.{u} (I.prod (𝓡∂ 1)) s.1 t.1, ξ.onBor b

/-- The **`ξ`-tangential bordism group** `Ω^ξ`: bordism classes of closed `ξ`-manifolds via
`ξ`-bordisms. For `ξ = Pin⁺` this is the goal's `Ω_•^{Pin⁺}`. Reuses the genuine bordism machinery;
`Quot` quotients by the relation's closure (no transitivity/gluing proof needed). -/
def TangentialBordismGrp.{u} (ξ : TangentialStr.{u} X k I) : Type _ :=
  Quot (IsTangentiallyBordant ξ)

/-- The bordism class of a closed `ξ`-manifold. -/
def TangentialBordismGrp.mk.{u} (ξ : TangentialStr.{u} X k I)
    (s : {s : SingularManifold.{u} X k I // ξ.onMfd s}) : TangentialBordismGrp ξ :=
  Quot.mk _ s

/-- `ξ`-bordant manifolds have the same `ξ`-bordism class. -/
theorem TangentialBordismGrp.mk_eq_of_bordant.{u} (ξ : TangentialStr.{u} X k I)
    {s t : {s : SingularManifold.{u} X k I // ξ.onMfd s}} (h : IsTangentiallyBordant ξ s t) :
    TangentialBordismGrp.mk ξ s = TangentialBordismGrp.mk ξ t :=
  Quot.sound h

/-- **Disjoint union `⊕` on `ξ`-bordism classes.** Well-defined: `onSum` keeps the sum a `ξ`-manifold,
and the congruence `s ~ s' ⟹ s ⊔ t ~ s' ⊔ t` is `Bordism.add` of the `ξ`-bordism with the cylinder
(`add_onBor` + `cyl_onBor`), reusing the genuine machinery with no gluing. -/
noncomputable def TangentialBordismGrp.add.{u} (ξ : TangentialStr.{u} X k I)
    (x y : TangentialBordismGrp ξ) : TangentialBordismGrp ξ :=
  Quot.lift₂ (fun s t => TangentialBordismGrp.mk ξ ⟨s.1.sum t.1, ξ.onSum s.2 t.2⟩)
    (fun s _t _t' h => h.elim fun b hb =>
      mk_eq_of_bordant ξ ⟨Bordism.add (reflCylinder s.1) b, ξ.add_onBor (ξ.cyl_onBor s.2) hb⟩)
    (fun _s _s' t h => h.elim fun b hb =>
      mk_eq_of_bordant ξ ⟨Bordism.add b (reflCylinder t.1), ξ.add_onBor hb (ξ.cyl_onBor t.2)⟩)
    x y

@[simp] theorem TangentialBordismGrp.add_mk.{u} (ξ : TangentialStr.{u} X k I)
    (s t : {s : SingularManifold.{u} X k I // ξ.onMfd s}) :
    TangentialBordismGrp.add ξ (TangentialBordismGrp.mk ξ s) (TangentialBordismGrp.mk ξ t) =
      TangentialBordismGrp.mk ξ ⟨s.1.sum t.1, ξ.onSum s.2 t.2⟩ :=
  rfl

/-- `⊕` on `ξ`-bordism classes is **commutative**. -/
theorem TangentialBordismGrp.add_comm.{u} (ξ : TangentialStr.{u} X k I)
    (x y : TangentialBordismGrp ξ) : add ξ x y = add ξ y x := by
  induction x using Quot.ind with | _ s =>
  induction y using Quot.ind with | _ t =>
  exact mk_eq_of_bordant ξ
    ⟨mapCylinder (Diffeomorph.sumComm I s.1.M k t.1.M) (by funext z; rcases z with z | z <;> rfl),
     ξ.mapCyl_onBor (ξ.onSum s.2 t.2)⟩

/-- `⊕` on `ξ`-bordism classes is **associative**. -/
theorem TangentialBordismGrp.add_assoc.{u} (ξ : TangentialStr.{u} X k I)
    (x y z : TangentialBordismGrp ξ) : add ξ (add ξ x y) z = add ξ x (add ξ y z) := by
  induction x using Quot.ind with | _ s =>
  induction y using Quot.ind with | _ t =>
  induction z using Quot.ind with | _ u =>
  exact mk_eq_of_bordant ξ
    ⟨mapCylinder (Diffeomorph.sumAssoc I s.1.M k t.1.M u.1.M)
      (by funext w; rcases w with (w | w) | w <;> rfl),
     ξ.mapCyl_onBor (ξ.onSum (ξ.onSum s.2 t.2) u.2)⟩

/-- The **zero** `ξ`-bordism class: the empty `ξ`-manifold. -/
noncomputable def TangentialBordismGrp.zero.{u} (ξ : TangentialStr.{u} X k I) :
    TangentialBordismGrp ξ :=
  TangentialBordismGrp.mk ξ ⟨emptySM, ξ.onEmpty⟩

/-- `x ⊕ 0 = x`. -/
theorem TangentialBordismGrp.add_zero.{u} (ξ : TangentialStr.{u} X k I)
    (x : TangentialBordismGrp ξ) : add ξ x (zero ξ) = x := by
  induction x using Quot.ind with | _ s =>
  exact mk_eq_of_bordant ξ
    ⟨mapCylinder (Diffeomorph.sumEmpty I s.1.M k (M' := emptySM.M))
      (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim),
     ξ.mapCyl_onBor (ξ.onSum s.2 ξ.onEmpty)⟩

/-- `0 ⊕ x = x`. -/
theorem TangentialBordismGrp.zero_add.{u} (ξ : TangentialStr.{u} X k I)
    (x : TangentialBordismGrp ξ) : add ξ (zero ξ) x = x := by
  rw [add_comm ξ]; exact add_zero ξ x

noncomputable instance (ξ : TangentialStr X k I) : Zero (TangentialBordismGrp ξ) :=
  ⟨TangentialBordismGrp.zero ξ⟩
noncomputable instance (ξ : TangentialStr X k I) : Add (TangentialBordismGrp ξ) :=
  ⟨TangentialBordismGrp.add ξ⟩
/-- `Ω^ξ` for the trivial (and more generally 2-torsion) structure has `neg = id`. -/
instance (ξ : TangentialStr X k I) : Neg (TangentialBordismGrp ξ) := ⟨id⟩

/-- The **`ξ`-tangential bordism group `Ω^ξ` is an additive commutative group** — the genuine bordism
machinery + the tangential closure axioms. (As built the group is 2-torsion, `neg = id`; the Pin⁺
refinement replaces the doubling-neg by structure reversal.) -/
noncomputable instance (ξ : TangentialStr X k I) : AddCommGroup (TangentialBordismGrp ξ) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  add_assoc := TangentialBordismGrp.add_assoc ξ
  zero_add := TangentialBordismGrp.zero_add ξ
  add_zero := TangentialBordismGrp.add_zero ξ
  add_comm := TangentialBordismGrp.add_comm ξ
  neg_add_cancel := fun x => by
    induction x using Quot.ind with | _ s =>
      exact TangentialBordismGrp.mk_eq_of_bordant ξ ⟨doublingBordism s.1, ξ.doubling_onBor s.2⟩
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul := zsmulRec
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

end SKEFTHawking.TangentialBordism
