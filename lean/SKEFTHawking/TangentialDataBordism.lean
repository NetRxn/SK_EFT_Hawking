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
  /-- The structures `sumStr σ τ` and `sumStr τ σ` correspond under `sumComm` (for `⊕`-commutativity). -/
  commBor : {s t : SingularManifold.{u} X k I} → (σ : Mfd s) → (τ : Mfd t) →
    Bor (mapCylinder (Diffeomorph.sumComm I s.M k t.M)
      (by funext z; rcases z with z | z <;> rfl)) (sumStr σ τ) (sumStr τ σ)
  /-- Structures correspond under `sumAssoc` (for `⊕`-associativity). -/
  assocBor : {s t u : SingularManifold.{u} X k I} → (σ : Mfd s) → (τ : Mfd t) → (ρ : Mfd u) →
    Bor (mapCylinder (Diffeomorph.sumAssoc I s.M k t.M u.M)
      (by funext w; rcases w with (w | w) | w <;> rfl))
      (sumStr (sumStr σ τ) ρ) (sumStr σ (sumStr τ ρ))
  /-- `sumStr σ emptyStr` corresponds to `σ` under `sumEmpty` (for the unit law). -/
  unitBor : {s : SingularManifold.{u} X k I} → (σ : Mfd s) →
    Bor (mapCylinder (Diffeomorph.sumEmpty I s.M k (M' := emptySM.M))
      (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim))
      (sumStr σ emptyStr) σ
  /-- **Structure reversal** — the Pin⁺ additive inverse (orientation/structure conjugation). -/
  revStr : {s : SingularManifold.{u} X k I} → Mfd s → Mfd s
  /-- Reversal is functorial on bordism structures. -/
  revBor : {s t : SingularManifold.{u} X k I} → {b : Bordism.{u} (I.prod (𝓡∂ 1)) s t} →
    {σ : Mfd s} → {τ : Mfd t} → Bor b σ τ → Bor b (revStr σ) (revStr τ)
  /-- `(M,σ) ⊔ (M, σ̄)` bounds the cylinder — the inverse law `-[M,σ] + [M,σ] = 0`. -/
  negBor : {s : SingularManifold.{u} X k I} → (σ : Mfd s) →
    Bor (doublingBordism s) (sumStr (revStr σ) σ) emptyStr

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

/-- `⊕` on faithful (structured) bordism classes is **commutative**. -/
theorem DataBordismGrp.add_comm.{u} (ξ : TangentialData.{u} X k I) (x y : DataBordismGrp ξ) :
    add ξ x y = add ξ y x := by
  induction x using Quot.ind with | _ p =>
  induction y using Quot.ind with | _ q =>
  exact mk_eq_of_bordant ξ
    ⟨mapCylinder (Diffeomorph.sumComm I p.1.M k q.1.M) (by funext z; rcases z with z | z <;> rfl),
     ⟨ξ.commBor p.2 q.2⟩⟩

/-- `⊕` on faithful bordism classes is **associative**. -/
theorem DataBordismGrp.add_assoc.{u} (ξ : TangentialData.{u} X k I) (x y z : DataBordismGrp ξ) :
    add ξ (add ξ x y) z = add ξ x (add ξ y z) := by
  induction x using Quot.ind with | _ p =>
  induction y using Quot.ind with | _ q =>
  induction z using Quot.ind with | _ r =>
  exact mk_eq_of_bordant ξ
    ⟨mapCylinder (Diffeomorph.sumAssoc I p.1.M k q.1.M r.1.M)
      (by funext w; rcases w with (w | w) | w <;> rfl), ⟨ξ.assocBor p.2 q.2 r.2⟩⟩

/-- The **zero** faithful bordism class: the empty manifold with its structure. -/
noncomputable def DataBordismGrp.zero.{u} (ξ : TangentialData.{u} X k I) : DataBordismGrp ξ :=
  DataBordismGrp.mk ξ ⟨emptySM, ξ.emptyStr⟩

/-- `x ⊕ 0 = x`. -/
theorem DataBordismGrp.add_zero.{u} (ξ : TangentialData.{u} X k I) (x : DataBordismGrp ξ) :
    add ξ x (zero ξ) = x := by
  induction x using Quot.ind with | _ p =>
  exact mk_eq_of_bordant ξ
    ⟨mapCylinder (Diffeomorph.sumEmpty I p.1.M k (M' := emptySM.M))
      (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim),
     ⟨ξ.unitBor p.2⟩⟩

/-- `0 ⊕ x = x`. -/
theorem DataBordismGrp.zero_add.{u} (ξ : TangentialData.{u} X k I) (x : DataBordismGrp ξ) :
    add ξ (zero ξ) x = x := by
  rw [add_comm ξ]; exact add_zero ξ x

/-- **Negation** = structure reversal (the genuine Pin⁺ inverse, NOT the unoriented identity). -/
noncomputable def DataBordismGrp.neg.{u} (ξ : TangentialData.{u} X k I) (x : DataBordismGrp ξ) :
    DataBordismGrp ξ :=
  Quot.lift (fun p => DataBordismGrp.mk ξ ⟨p.1, ξ.revStr p.2⟩)
    (fun _p _q h => h.elim fun b hb => hb.elim fun str =>
      mk_eq_of_bordant ξ ⟨b, ⟨ξ.revBor str⟩⟩) x

@[simp] theorem DataBordismGrp.neg_mk.{u} (ξ : TangentialData.{u} X k I) (p : StrMfd ξ) :
    DataBordismGrp.neg ξ (DataBordismGrp.mk ξ p) = DataBordismGrp.mk ξ ⟨p.1, ξ.revStr p.2⟩ :=
  rfl

noncomputable instance (ξ : TangentialData X k I) : Zero (DataBordismGrp ξ) :=
  ⟨DataBordismGrp.zero ξ⟩
noncomputable instance (ξ : TangentialData X k I) : Add (DataBordismGrp ξ) :=
  ⟨DataBordismGrp.add ξ⟩
noncomputable instance (ξ : TangentialData X k I) : Neg (DataBordismGrp ξ) :=
  ⟨DataBordismGrp.neg ξ⟩

/-- The **faithful tangential bordism group `Ω^ξ` is an additive commutative group**, with negation =
structure reversal (the genuine Pin⁺ inverse). For ξ = Pin⁺ this is `Ω_•^{Pin⁺}` (ℤ/16 in degree 4). -/
noncomputable instance (ξ : TangentialData X k I) : AddCommGroup (DataBordismGrp ξ) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  add_assoc := DataBordismGrp.add_assoc ξ
  zero_add := DataBordismGrp.zero_add ξ
  add_zero := DataBordismGrp.add_zero ξ
  add_comm := DataBordismGrp.add_comm ξ
  neg_add_cancel := fun x => by
    induction x using Quot.ind with | _ p =>
      exact DataBordismGrp.mk_eq_of_bordant ξ ⟨doublingBordism p.1, ⟨ξ.negBor p.2⟩⟩
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul := zsmulRec
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

end SKEFTHawking.TangentialDataBordism
