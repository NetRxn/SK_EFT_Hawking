/-
# Phase 5q.F W4 (faithful tangential layer) — tangential structures carried AS DATA

The faithful refinement giving `Ω₄^{Pin⁺} ≅ ℤ/16` via **chosen** Pin⁺ structures (vs the
existence/Prop-interface of `TangentialBordism.lean`, which gives a coarser admits-Pin⁺ group). The
key finding (lab notebook): the structure-count — `Pin⁺` structures form an `H¹(M;ℤ/2)`-torsor — is what
makes the group `ℤ/16`, so the tangential structure must be carried as DATA (`Mfd s = ` the type of
structures on `s`), not as a `Prop`. The genuine bordism machinery (`BordismGroup.lean`) is reused; this
layer carries the structure data + its restriction along bordism boundaries. Pin⁺ is an instance whose
`Mfd s` is the genuine Pin⁺ structure.
-/
import Mathlib
import SKEFTHawking.BordismGroup

namespace SKEFTHawking.TangentialDataBordism

open SKEFTHawking.BordismTheory
open scoped Manifold

/-- A **tangential structure carried as DATA**: `Mfd s` = the type of tangential structures on the
closed manifold `s` (Pin⁺: the `H¹(s;ℤ/2)`-torsor of Pin⁺ structures); `Bor b σ τ` = the type of
structures on the bordism `b` restricting to `σ`, `τ` on its two boundary ends. Closed under the
operations (empty / disjoint union / cylinder / symmetry) so the structured cobordism relation is
reflexive/symmetric and `⊕`-congruent. -/
structure TangentialData.{u} (X : Type*) [TopologicalSpace X] (k : WithTop ℕ∞)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless] where
  /-- The type of tangential structures on a closed manifold `s`. -/
  Mfd : SingularManifold.{u} X k I → Type u
  /-- The type of structures on a bordism `b` restricting to `σ`, `τ` on the boundary. -/
  Bor : {s t : SingularManifold.{u} X k I} →
    Bordism.{u} (I.prod (𝓡∂ 1)) s t → Mfd s → Mfd t → Type u
  /-- A structure on the empty manifold. -/
  emptyStr : Mfd emptySM
  /-- Disjoint union of structures. -/
  sumStr : {s t : SingularManifold.{u} X k I} → Mfd s → Mfd t → Mfd (s.sum t)
  /-- The cylinder of a structured manifold carries the product structure (for reflexivity). -/
  cylBor : {s : SingularManifold.{u} X k I} → (σ : Mfd s) → Bor (reflCylinder s) σ σ
  /-- Disjoint union of bordism structures (for the `⊕`-congruence). -/
  addBor : {s₁ t₁ s₂ t₂ : SingularManifold.{u} X k I} →
    {b₁ : Bordism.{u} (I.prod (𝓡∂ 1)) s₁ t₁} → {b₂ : Bordism.{u} (I.prod (𝓡∂ 1)) s₂ t₂} →
    {σ₁ : Mfd s₁} → {τ₁ : Mfd t₁} → {σ₂ : Mfd s₂} → {τ₂ : Mfd t₂} →
    Bor b₁ σ₁ τ₁ → Bor b₂ σ₂ τ₂ → Bor (b₁.add b₂) (sumStr σ₁ σ₂) (sumStr τ₁ τ₂)
  /-- The reverse of a bordism structure (for symmetry). -/
  symmBor : {s t : SingularManifold.{u} X k I} → {b : Bordism.{u} (I.prod (𝓡∂ 1)) s t} →
    {σ : Mfd s} → {τ : Mfd t} → Bor b σ τ → Bor b.symm τ σ

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- A **structured manifold**: a closed manifold with a chosen tangential structure. -/
def StrMfd.{u} (ξ : TangentialData.{u} X k I) : Type _ :=
  Σ s : SingularManifold.{u} X k I, ξ.Mfd s

/-- The **structured cobordism relation**: a bordism between the underlying manifolds carrying a
structure that restricts to the chosen boundary structures. -/
def IsDataBordant.{u} (ξ : TangentialData.{u} X k I) (p q : StrMfd ξ) : Prop :=
  ∃ b : Bordism.{u} (I.prod (𝓡∂ 1)) p.1 q.1, Nonempty (ξ.Bor b p.2 q.2)

/-- The **faithful tangential bordism group** `Ω^ξ` of CHOSEN structures (for ξ = Pin⁺, the genuine
`Ω_•^{Pin⁺}` that is `ℤ/16` in degree 4). `Quot` handles transitivity/gluing. -/
def DataBordismGrp.{u} (ξ : TangentialData.{u} X k I) : Type _ :=
  Quot (IsDataBordant ξ)

/-- The class of a structured manifold. -/
def DataBordismGrp.mk.{u} (ξ : TangentialData.{u} X k I) (p : StrMfd ξ) : DataBordismGrp ξ :=
  Quot.mk _ p

/-- Structured-bordant manifolds have the same class. -/
theorem DataBordismGrp.mk_eq_of_bordant.{u} (ξ : TangentialData.{u} X k I) {p q : StrMfd ξ}
    (h : IsDataBordant ξ p q) : DataBordismGrp.mk ξ p = DataBordismGrp.mk ξ q :=
  Quot.sound h

/-- **Disjoint union `⊕` on faithful (structured) bordism classes.** Well-defined: `sumStr` combines the
structures; the congruence is `Bordism.add` of the structured bordism with the cylinder (`addBor` +
`cylBor`), reusing the genuine machinery with no gluing. -/
noncomputable def DataBordismGrp.add.{u} (ξ : TangentialData.{u} X k I)
    (x y : DataBordismGrp ξ) : DataBordismGrp ξ :=
  Quot.lift₂ (fun p q => DataBordismGrp.mk ξ ⟨p.1.sum q.1, ξ.sumStr p.2 q.2⟩)
    (fun p _q _q' h => h.elim fun b hb => hb.elim fun str =>
      mk_eq_of_bordant ξ ⟨Bordism.add (reflCylinder p.1) b, ⟨ξ.addBor (ξ.cylBor p.2) str⟩⟩)
    (fun _p _p' q h => h.elim fun b hb => hb.elim fun str =>
      mk_eq_of_bordant ξ ⟨Bordism.add b (reflCylinder q.1), ⟨ξ.addBor str (ξ.cylBor q.2)⟩⟩)
    x y

@[simp] theorem DataBordismGrp.add_mk.{u} (ξ : TangentialData.{u} X k I) (p q : StrMfd ξ) :
    DataBordismGrp.add ξ (DataBordismGrp.mk ξ p) (DataBordismGrp.mk ξ q) =
      DataBordismGrp.mk ξ ⟨p.1.sum q.1, ξ.sumStr p.2 q.2⟩ :=
  rfl

end SKEFTHawking.TangentialDataBordism
