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

end SKEFTHawking.TangentialBordism
