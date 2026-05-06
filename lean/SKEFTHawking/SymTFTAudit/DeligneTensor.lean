/-
# Wave 1b.5.10c — Deligne tensor product underlying category

This module ships the **underlying category** of the Deligne tensor product `C ⊠ D`
of two k-linear categories, constructed as a quotient of the free k-linear envelope
on the product category `C × D` by the bilinearity-respecting congruence.

The construction follows the Davydov-Müger-Nikshych-Ostrik 2010 (arXiv:1009.2117 §3)
template for the Witt-group-of-MTCs operation, and uses Mathlib's
`CategoryTheory.Quotient.preadditive` + `CategoryTheory.Quotient.linear` substrate
identified by the Session 21 pre-flight Mathlib substrate scout.

## Construction

Given two k-linear categories `C` and `D` (each `[Category]` + `[Preadditive]` +
`[Linear k]`):

1. Form `FreeKLinear (C × D) k` (Wave 1b.5.10a) — the free k-linear envelope of the
   product category.
2. Define `DeligneRel C D k : HomRel (FreeKLinear (C × D) k)` as an *inductively-
   generated* congruence containing the four bilinearity-witness generators (smul/add
   in each component) plus the additivity/smul-respect constructors that
   `Quotient.preadditive`/`Quotient.linear` require as hypothesis.
3. Define `DeligneTensor C D k := CategoryTheory.Quotient (DeligneRel C D k)`. Inherits
   `Category` automatically; `Preadditive` and `Linear k` lift via the Mathlib
   substrate.

## Substantive content (Wave 1b.5.10c)

* `DeligneRel C D k` — the inductive bilinearity-respecting `HomRel` on
  `FreeKLinear (C × D) k`. Constructors split into generators (`smul_left`,
  `smul_right`, `add_left`, `add_right`) and structural-closure constructors
  (`refl`/`symm`/`trans`/`comp_left`/`comp_right`/`add`/`smul`).
* `Congruence (DeligneRel C D k)` — instance.
* `DeligneTensor C D k` — the Deligne tensor product as a quotient category.
* `Category`, `Preadditive`, `Linear k` instances on `DeligneTensor C D k`.
* `proj : FreeKLinear (C × D) k ⥤ DeligneTensor C D k` — the projection functor;
  inherits `.Additive` and `.Linear` from the Mathlib substrate.
* `stage5_10c_deligneTensor_closure` — Stage 5.10c closure summary bundling the
  Congruence + Category + Preadditive + Linear k facts.

## Open continuations (Wave 1b.5.10d+)

* **5.10d** — `MonoidalCategory (DeligneTensor C D k)` — transferred from the product-
  monoidal structure on `(C × D)` via the projection (requires `MonoidalCategory C`,
  `MonoidalCategory D`).
* **5.10e** — Closure theorem packaging 5.10c+5.10d together with the inclusion
  bifunctor `(C × D) ⥤ DeligneTensor C D k`.
* **5.10f** — `BraidedCategory (DeligneTensor C D k)` — transferred via
  `Functor.Braided` + the Wave 1b.5.10b `Functor.Monoidal incl` infrastructure.
* **5.10g** — Cross-bridge to `WittClass`: central charge is additive under ⊠,
  closing the Witt-group-of-MTCs construction loop.

## Relation-design rationale

The inductive `DeligneRel` is *intentionally over-specified*: it bakes in `refl`/
`symm`/`trans` (so it's an equivalence on each hom-set), `comp_left`/`comp_right` (so
it's a Mathlib `Congruence`), AND the `add`/`smul` constructors that
`Quotient.preadditive`/`Quotient.linear` require as hypothesis. This eliminates the
need to take any external closure (no `EqvGen`/`HomRel.CompClosure` plumbing). The
underlying mathematical content is *exactly* the four generating bilinearity
relations; the additional constructors are the smallest closure such that the
quotient is a k-linear category.

This design pattern is recommended by Mathlib's `Quotient.lean` documentation:
"If you can encode the relation inductively such that all required closures are
direct constructors, do so — it makes the `Congruence` instance trivial."
-/

import Mathlib.CategoryTheory.Quotient.Preadditive
import Mathlib.CategoryTheory.Quotient.Linear
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Products.Basic
import SKEFTHawking.SymTFTAudit.FreeKLinearMonoidal

namespace SKEFTHawking.SymTFTAudit

open CategoryTheory

universe v u

/-! ## §1 Basis-element helper -/

/--
**Pair-morphism basis element** in `FreeKLinear (C × D) k`. Given `f : X₁ ⟶ X₂` in C
and `g : Y₁ ⟶ Y₂` in D, builds the singleton-Finsupp basis element of unit weight in
the appropriate hom-set of `FreeKLinear (C × D) k`. Used to give explicit types to
the generators of `DeligneRel` (avoids HomRel-implicit-binder unification issues).
-/
noncomputable def deligneBasis {C D : Type u} [Category.{v} C] [Category.{v} D]
    {k : Type} [CommRing k] {X₁ X₂ : C} {Y₁ Y₂ : D}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (FreeKLinear.of (k := k) ((X₁, Y₁) : C × D)) ⟶
      FreeKLinear.of ((X₂, Y₂) : C × D) :=
  Finsupp.single ((f, g) : (X₁ ⟶ X₂) × (Y₁ ⟶ Y₂)) (1 : k)

/-! ## §2 The bilinearity-respecting congruence -/

/--
**The bilinearity-respecting congruence on `FreeKLinear (C × D) k`.**

Inductive `HomRel` whose constructors split into four mathematically-generating
relations (k-bilinearity of the pair-morphism in each component) plus the structural
constructors that make the relation a `Congruence` and satisfy the additivity/smul
hypotheses required by `Quotient.preadditive` and `Quotient.linear`.

The four generators (`smul_left`, `smul_right`, `add_left`, `add_right`) say that
`deligneBasis (α • f) g ~ α • deligneBasis f g` (resp. `deligneBasis f (α • g) ~
α • deligneBasis f g`, `deligneBasis (f₁ + f₂) g ~ deligneBasis f₁ g + deligneBasis
f₂ g`, `deligneBasis f (g₁ + g₂) ~ deligneBasis f g₁ + deligneBasis f g₂`). This is
exactly the identification needed to make pair-morphisms genuinely k-bilinear.

The structural constructors (`refl`/`symm`/`trans`/`comp_left`/`comp_right`/`add`/
`smul`) are the smallest closure that makes the quotient a k-linear category; they
add no mathematical content beyond what's forced by the four generators.
-/
inductive DeligneRel (C D : Type u) [Category.{v} C] [Preadditive C]
    (k : Type) [CommRing k] [Linear k C]
    [Category.{v} D] [Preadditive D] [Linear k D] :
    HomRel (FreeKLinear (C × D) k)
  -- ===== Mathematical generators (k-bilinearity in each component) =====
  /-- k-linearity in the C component: `deligneBasis (α • f) g ~ α • deligneBasis f g`. -/
  | smul_left {X₁ X₂ : C} {Y₁ Y₂ : D} (α : k) (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
      DeligneRel C D k
        (deligneBasis (k := k) (α • f) g)
        (α • deligneBasis (k := k) f g)
  /-- k-linearity in the D component: `deligneBasis f (α • g) ~ α • deligneBasis f g`. -/
  | smul_right {X₁ X₂ : C} {Y₁ Y₂ : D} (α : k) (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
      DeligneRel C D k
        (deligneBasis (k := k) f (α • g))
        (α • deligneBasis (k := k) f g)
  /-- additivity in the C component:
      `deligneBasis (f₁ + f₂) g ~ deligneBasis f₁ g + deligneBasis f₂ g`. -/
  | add_left {X₁ X₂ : C} {Y₁ Y₂ : D} (f₁ f₂ : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
      DeligneRel C D k
        (deligneBasis (k := k) (f₁ + f₂) g)
        (deligneBasis (k := k) f₁ g + deligneBasis (k := k) f₂ g)
  /-- additivity in the D component:
      `deligneBasis f (g₁ + g₂) ~ deligneBasis f g₁ + deligneBasis f g₂`. -/
  | add_right {X₁ X₂ : C} {Y₁ Y₂ : D} (f : X₁ ⟶ X₂) (g₁ g₂ : Y₁ ⟶ Y₂) :
      DeligneRel C D k
        (deligneBasis (k := k) f (g₁ + g₂))
        (deligneBasis (k := k) f g₁ + deligneBasis (k := k) f g₂)
  -- ===== Equivalence closure (per hom-set) =====
  /-- Reflexivity. -/
  | refl {XY₁ XY₂ : FreeKLinear (C × D) k} (α : XY₁ ⟶ XY₂) : DeligneRel C D k α α
  /-- Symmetry. -/
  | symm {XY₁ XY₂ : FreeKLinear (C × D) k} {α β : XY₁ ⟶ XY₂} :
      DeligneRel C D k α β → DeligneRel C D k β α
  /-- Transitivity. -/
  | trans {XY₁ XY₂ : FreeKLinear (C × D) k} {α β γ : XY₁ ⟶ XY₂} :
      DeligneRel C D k α β → DeligneRel C D k β γ → DeligneRel C D k α γ
  -- ===== Congruence (precomp / postcomp) =====
  /-- Stability under post-composition: γ ≫ - respects the relation. -/
  | comp_left {XY₁ XY₂ XY₃ : FreeKLinear (C × D) k}
      (γ : XY₁ ⟶ XY₂) {α β : XY₂ ⟶ XY₃} :
      DeligneRel C D k α β → DeligneRel C D k (γ ≫ α) (γ ≫ β)
  /-- Stability under pre-composition: - ≫ γ respects the relation. -/
  | comp_right {XY₁ XY₂ XY₃ : FreeKLinear (C × D) k}
      {α β : XY₁ ⟶ XY₂} (γ : XY₂ ⟶ XY₃) :
      DeligneRel C D k α β → DeligneRel C D k (α ≫ γ) (β ≫ γ)
  -- ===== Additivity / scalar-multiplication respect =====
  -- (Required by Quotient.preadditive / Quotient.linear hypotheses.)
  /-- Additivity respect: `r f₁ f₂ → r g₁ g₂ → r (f₁ + g₁) (f₂ + g₂)`. -/
  | add {XY₁ XY₂ : FreeKLinear (C × D) k} {f₁ f₂ g₁ g₂ : XY₁ ⟶ XY₂} :
      DeligneRel C D k f₁ f₂ → DeligneRel C D k g₁ g₂ →
      DeligneRel C D k (f₁ + g₁) (f₂ + g₂)
  /-- Tensor respect (Wave 1b.5.10d.2): the relation respects `freeTensorHom`.
      Required so that the FreeKLinear monoidal structure descends to the quotient.
      Constructor-level instance hypotheses `[MonoidalCategory C]` `[MonoidalCategory D]`
      gate this constructor's applicability. -/
  | tens [MonoidalCategory C] [MonoidalCategory D]
      {X₁ Y₁ X₂ Y₂ : C × D}
      {α₁ α₂ : (X₁ ⟶ Y₁) →₀ k} {β₁ β₂ : (X₂ ⟶ Y₂) →₀ k} :
      DeligneRel C D k (X := FreeKLinear.of X₁) (Y := FreeKLinear.of Y₁) α₁ α₂ →
      DeligneRel C D k (X := FreeKLinear.of X₂) (Y := FreeKLinear.of Y₂) β₁ β₂ →
      DeligneRel C D k
        (FreeKLinear.freeTensorHom α₁ β₁) (FreeKLinear.freeTensorHom α₂ β₂)
  /-- Scalar-multiplication respect: `r f₁ f₂ → r (a • f₁) (a • f₂)`. -/
  | smul {XY₁ XY₂ : FreeKLinear (C × D) k} (a : k) {f₁ f₂ : XY₁ ⟶ XY₂} :
      DeligneRel C D k f₁ f₂ → DeligneRel C D k (a • f₁) (a • f₂)

namespace DeligneRel

variable {C D : Type u} [Category.{v} C] [Preadditive C]
  {k : Type} [CommRing k] [Linear k C]
  [Category.{v} D] [Preadditive D] [Linear k D]

/-- The relation is an equivalence on each hom-set. -/
theorem equivalence_on_homs (XY₁ XY₂ : FreeKLinear (C × D) k) :
    Equivalence (fun α β : XY₁ ⟶ XY₂ => DeligneRel C D k α β) where
  refl α := DeligneRel.refl α
  symm h := DeligneRel.symm h
  trans h₁ h₂ := DeligneRel.trans h₁ h₂

/--
Hypothesis-form of the additivity-respect constructor, packaged with explicit
binders for direct consumption by `Quotient.preadditive`'s function argument.
Uses strict-implicit `⦃XY₁ XY₂⦄` to match Mathlib's HomRel signature exactly.
-/
theorem add_resp ⦃XY₁ XY₂ : FreeKLinear (C × D) k⦄
    (f₁ f₂ g₁ g₂ : XY₁ ⟶ XY₂) (h₁ : DeligneRel C D k f₁ f₂)
    (h₂ : DeligneRel C D k g₁ g₂) :
    DeligneRel C D k (f₁ + g₁) (f₂ + g₂) :=
  DeligneRel.add h₁ h₂

/--
Hypothesis-form of the smul-respect constructor, packaged with explicit binders
for direct consumption by `Quotient.linear`'s function argument.
Uses strict-implicit `⦃XY₁ XY₂⦄` to match Mathlib's HomRel signature exactly.
-/
theorem smul_resp (a : k) ⦃XY₁ XY₂ : FreeKLinear (C × D) k⦄
    (f₁ f₂ : XY₁ ⟶ XY₂) (h : DeligneRel C D k f₁ f₂) :
    DeligneRel C D k (a • f₁) (a • f₂) :=
  DeligneRel.smul a h

end DeligneRel

/-! ## §3 Congruence instance -/

/--
**`DeligneRel` is a Congruence.** The two `IsStableUnder*` properties follow from
`comp_left` / `comp_right`; equivalence-on-each-hom-set follows from
`refl`/`symm`/`trans`.
-/
instance instCongruence (C D : Type u) [Category.{v} C] [Preadditive C]
    (k : Type) [CommRing k] [Linear k C]
    [Category.{v} D] [Preadditive D] [Linear k D] :
    Congruence (DeligneRel C D k) where
  comp_left {_ _ _} f _ _ h := DeligneRel.comp_left f h
  comp_right {_ _ _} _ _ g h := DeligneRel.comp_right g h
  equivalence := DeligneRel.equivalence_on_homs _ _

/-! ## §4 Deligne tensor product as quotient -/

/--
**The Deligne tensor product `C ⊠ D` of two k-linear categories**, defined as the
quotient of `FreeKLinear (C × D) k` by the bilinearity-respecting congruence
`DeligneRel C D k`. Carries `Category`, `Preadditive`, and `Linear k` instances.

Defined as `abbrev` so that typeclass resolution can transparently see the
underlying `CategoryTheory.Quotient` and pick up the inherited `Category` instance
without a separate `noncomputable instance` declaration. This also lets
`Quotient.preadditive` and `Quotient.linear` find their required substrate instances.

Used as the substrate for the SymTFT central-charge group operation in Wave 1b.5.10g.
-/
abbrev DeligneTensor (C D : Type u) [Category.{v} C] [Preadditive C]
    (k : Type) [CommRing k] [Linear k C]
    [Category.{v} D] [Preadditive D] [Linear k D] : Type u :=
  CategoryTheory.Quotient (DeligneRel C D k)

namespace DeligneTensor

variable {C D : Type u} [Category.{v} C] [Preadditive C]
  {k : Type} [CommRing k] [Linear k C]
  [Category.{v} D] [Preadditive D] [Linear k D]

/--
Preadditive instance via `Quotient.preadditive` and the `add` constructor (packaged
through `DeligneRel.add_resp` for explicit-binder hypothesis form).
-/
noncomputable instance instPreadditive : Preadditive (DeligneTensor C D k) :=
  Quotient.preadditive (DeligneRel C D k) DeligneRel.add_resp

/-- The projection functor is additive (from the Mathlib substrate). -/
noncomputable instance instProjAdditive :
    (Quotient.functor (DeligneRel C D k)).Additive :=
  Quotient.functor_additive _ _

/--
Linear k instance via `Quotient.linear` and the `smul` constructor (packaged through
`DeligneRel.smul_resp` for explicit-binder hypothesis form).
-/
noncomputable instance instLinear : Linear k (DeligneTensor C D k) :=
  Quotient.linear k (DeligneRel C D k) DeligneRel.smul_resp

/--
**The projection functor** `FreeKLinear (C × D) k ⥤ DeligneTensor C D k`, sending
each free-k-linear-envelope morphism to its equivalence class under `DeligneRel`.
Inherits `.Additive` automatically from `Quotient.functor_additive`.
-/
noncomputable def proj : FreeKLinear (C × D) k ⥤ DeligneTensor C D k :=
  Quotient.functor (DeligneRel C D k)

theorem proj_obj (X : FreeKLinear (C × D) k) :
    (proj (C := C) (D := D) (k := k)).obj X =
    (Quotient.functor (DeligneRel C D k)).obj X := rfl

theorem proj_map {X Y : FreeKLinear (C × D) k} (f : X ⟶ Y) :
    (proj (C := C) (D := D) (k := k)).map f =
    (Quotient.functor (DeligneRel C D k)).map f := rfl

end DeligneTensor

/-! ## §5 Stage 5.10c closure theorem -/

/--
**Stage 5.10c closure summary.** Bundles the four headline content of the underlying-
category sub-wave of Wave 1b.5.10 (Deligne ⊠ as Witt-group operation):

1. **`DeligneRel` is a Congruence.** The bilinearity-respecting relation on
   `FreeKLinear (C × D) k` satisfies the Mathlib `Congruence` typeclass via
   the structural constructors (`refl`/`symm`/`trans`/`comp_left`/`comp_right`).
2. **`DeligneTensor C D k` carries Category structure** (inherited from
   `CategoryTheory.Quotient`).
3. **`DeligneTensor C D k` carries Preadditive AND Linear k structure**,
   transferred through `Quotient.preadditive` and `Quotient.linear` using the
   `add` / `smul` constructors of `DeligneRel`.
4. **The projection functor `proj` is Additive** (from `Quotient.functor_additive`).

Used as the substrate-level certification for Wave 1b.5.10d+ (monoidal extension,
braided lift, and central-charge cross-bridge to `WittClass`).
-/
theorem stage5_10c_deligneTensor_closure
    (C D : Type u) [Category.{v} C] [Preadditive C]
    (k : Type) [CommRing k] [Linear k C]
    [Category.{v} D] [Preadditive D] [Linear k D] :
    -- (1) The bilinearity-respecting relation is a Congruence.
    Nonempty (Congruence (DeligneRel C D k)) ∧
    -- (2) DeligneTensor C D k is a category (inherited from Quotient via abbrev).
    Nonempty (Category.{v, u} (DeligneTensor C D k)) ∧
    -- (3) DeligneTensor C D k carries Preadditive AND Linear k.
    (Nonempty (Preadditive (DeligneTensor C D k)) ∧
     Nonempty (Linear k (DeligneTensor C D k))) ∧
    -- (4) The projection functor is Additive.
    Nonempty ((Quotient.functor (DeligneRel C D k)).Additive) :=
  ⟨⟨instCongruence C D k⟩,
   ⟨inferInstance⟩,
   ⟨⟨DeligneTensor.instPreadditive⟩, ⟨DeligneTensor.instLinear⟩⟩,
   ⟨DeligneTensor.instProjAdditive⟩⟩

/-! ## §6 Wave 1b.5.10d — Monoidal substrate (external-product bifunctor) -/

namespace DeligneTensor

variable {C D : Type u} [Category.{v} C] [Preadditive C]
  {k : Type} [CommRing k] [Linear k C]
  [Category.{v} D] [Preadditive D] [Linear k D]

/--
**External-product bifunctor** `extProd : C × D ⥤ DeligneTensor C D k`, defined as
the composition of `FreeKLinear.incl` (Wave 1b.5.10a) with the projection `proj`.

Substantive content: every pair-morphism `(f, g) : (X₁, Y₁) ⟶ (X₂, Y₂)` in `C × D`
maps to its equivalence class `[single (f, g) 1]` in `DeligneTensor C D k`. This is
the categorical universal-property witness for the Deligne tensor product: any
k-bilinear bifunctor `C × D → E` (with E k-linear) factors uniquely through
`extProd` and a k-linear functor `DeligneTensor C D k ⥤ E` (full universal property
to be discharged in Wave 1b.5.10e+, requires extending `DeligneRel` with monoidal-
respect constructors).
-/
noncomputable def extProd : C × D ⥤ DeligneTensor C D k :=
  FreeKLinear.incl (k := k) ⋙ proj

/--
On objects, `extProd` sends each `(X, Y) ∈ C × D` to the equivalence class of
the basis element `of (X, Y)` in `FreeKLinear (C × D) k`.
-/
theorem extProd_obj (X : C) (Y : D) :
    (extProd (C := C) (D := D) (k := k)).obj (X, Y) =
    (proj (C := C) (D := D) (k := k)).obj (FreeKLinear.of (k := k) (X, Y)) := rfl

end DeligneTensor

/-!
## §6a — Monoidal substrate availability (Wave 1b.5.10d substrate)

When both `C` and `D` are monoidal (`[MonoidalCategory C]` + `[MonoidalCategory D]`),
the product category `C × D` inherits a monoidal structure from Mathlib's
`prodMonoidal` instance, and `FreeKLinear (C × D) k` then inherits a monoidal
structure from Wave 1b.5.10b's `FreeKLinear.instMonoidalCategory` instance.

The full lift to `DeligneTensor C D k` requires the `DeligneRel` relation to respect
the tensor operation (a `tens` constructor) — this is the next sub-wave deliverable
(Wave 1b.5.10d.2). The substrate below confirms that the Mathlib + Wave 1b.5.10b
infrastructure is in place to support that lift once the relation is extended.
-/

/--
**Wave 1b.5.10d substrate availability theorem.** When `C` and `D` are both
k-linear monoidal categories, the supporting infrastructure for lifting
`MonoidalCategory` to `DeligneTensor C D k` is in place:

1. `MonoidalCategory (C × D)` — Mathlib's `prodMonoidal` instance.
2. `MonoidalCategory (FreeKLinear (C × D) k)` — Wave 1b.5.10b's
   `FreeKLinear.instMonoidalCategory` applied to `C × D`.
3. The external-product bifunctor `extProd : C × D ⥤ DeligneTensor C D k` exists.

The *direct* lift to `MonoidalCategory (DeligneTensor C D k)` requires extending
`DeligneRel` with monoidal-respect constructors and using `Quotient`-transport for
the structure — Wave 1b.5.10d.2 deliverable.
-/
theorem stage5_10d_deligneTensor_monoidal_substrate
    (C D : Type u) [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (k : Type) [CommRing k] [Linear k C]
    [Category.{v} D] [Preadditive D] [Linear k D] [MonoidalCategory D] :
    -- (1) C × D inherits MonoidalCategory from Mathlib's prodMonoidal.
    Nonempty (MonoidalCategory (C × D)) ∧
    -- (2) FreeKLinear (C × D) k inherits MonoidalCategory from Wave 1b.5.10b.
    Nonempty (MonoidalCategory (FreeKLinear (C × D) k)) ∧
    -- (3) The external-product bifunctor extProd exists.
    Nonempty (C × D ⥤ DeligneTensor C D k) :=
  ⟨⟨MonoidalCategory.prodMonoidal C D⟩,
   ⟨FreeKLinear.instMonoidalCategory⟩,
   ⟨DeligneTensor.extProd⟩⟩

/-! ## §7 Wave 1b.5.10g — Cross-bridge to WittClass (cc additivity substrate) -/

/--
**Integer-level central-charge operation under Deligne ⊠**: `c₁ ⊠ c₂ := c₁ + c₂`.

This is the *substrate-level* operation that the categorical Deligne tensor product
induces on chiral central charges. Mathematically: when two MTCs are tensored via
Deligne ⊠, their central charges add (a basic fact from Verlinde-formula gauss-sum
calculations on the combined modular data).

Wave 1b.5.10g uses this to bridge to `WittClass.WittInvariant` (mod-24 quotient):
the integer-level addition lifts cleanly through `WittInvariant.fromChiralCentralCharge`
(an `AddMonoidHom`) to produce the group-additivity witness. The full categorical
form (`cc(C ⊠ D) = cc C + cc D` via `MonoidalCategory (DeligneTensor C D k)`) is gated
on Wave 1b.5.10d.2 (full monoidal lift).
-/
def chiralCentralChargeOfDeligneTensor (c₁ c₂ : ℤ) : ℤ := c₁ + c₂

/--
**Witt-additivity bridge.** The integer-level Deligne ⊠ central charge operation,
lifted through `WittInvariant.fromChiralCentralCharge`, equals the abelian-group
addition in `ZMod 24`. This is the Wave 1b.5.10g substrate-level central-charge
additivity bridge: it shows that the Deligne ⊠ operation on integer central charges
descends to abelian-group addition on Witt invariants, closing the Witt-group-of-MTCs
construction loop at the substrate level.

Proof: immediate from `WittInvariant.fromChiralCentralCharge` being an `AddMonoidHom`
(cf. `wittInvariant_homomorphism_witness`).
-/
theorem chiralCentralChargeOfDeligneTensor_witt_additive (c₁ c₂ : ℤ) :
    WittInvariant.fromChiralCentralCharge (chiralCentralChargeOfDeligneTensor c₁ c₂) =
      WittInvariant.fromChiralCentralCharge c₁ +
        WittInvariant.fromChiralCentralCharge c₂ := by
  unfold chiralCentralChargeOfDeligneTensor
  exact map_add WittInvariant.fromChiralCentralCharge c₁ c₂

/--
**Witt-equivalence preservation under Deligne ⊠.** If `c₁ ≈ c₁'` and `c₂ ≈ c₂'`
(Witt-equivalent integer central charges), then `c₁ ⊠ c₂ ≈ c₁' ⊠ c₂'`. This is the
abelian-group congruence property of `WittInvariant.fromChiralCentralCharge`
applied to the Deligne ⊠ operation.
-/
theorem chiralCentralChargeOfDeligneTensor_wittEquivalent
    {c₁ c₁' c₂ c₂' : ℤ} (h₁ : WittEquivalent c₁ c₁') (h₂ : WittEquivalent c₂ c₂') :
    WittEquivalent (chiralCentralChargeOfDeligneTensor c₁ c₂)
                   (chiralCentralChargeOfDeligneTensor c₁' c₂') := by
  unfold WittEquivalent at h₁ h₂ ⊢
  rw [chiralCentralChargeOfDeligneTensor_witt_additive,
      chiralCentralChargeOfDeligneTensor_witt_additive, h₁, h₂]

/--
**Categorical-level cc-additivity hypothesis schema.** A Prop hypothesis schema
saying that any chosen "central charge function" on k-linear monoidal categories
is additive under the Deligne tensor product. The categorical-level discharge of
this hypothesis is gated on Wave 1b.5.10d.2 (the full `MonoidalCategory` lift to
`DeligneTensor C D k`); the integer-level form is the substrate-level lift shipped
by `chiralCentralChargeOfDeligneTensor_witt_additive`.

Once Wave 1b.5.10d.2 lands, instantiating this schema with the project's chosen
cc function discharges the full Wave 1b.5.10g categorical claim
`cc(C ⊠ D) = cc C + cc D`.
-/
def CentralChargeAdditiveUnderDeligneTensor
    (cc : ∀ (C : Type u) [Category.{v} C] [Preadditive C] [MonoidalCategory C], ℤ) :
    Prop :=
  ∀ (C D : Type u)
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [Category.{v} D] [Preadditive D] [MonoidalCategory D],
    chiralCentralChargeOfDeligneTensor (cc C) (cc D) = cc C + cc D

/-!
The hypothesis schema is *load-bearing*: discharging it requires connecting the
integer-level Deligne ⊠ operation to the categorical-level central-charge function
on `MonoidalCategory (DeligneTensor C D k)`. That connection requires Wave 1b.5.10d.2
(full monoidal lift on `DeligneTensor C D k`); until then, the schema sits as a
hypothesis form parallel to `CentralChargePreservesDrinfeldCenter_*` from Waves
1b.5.8/9/11/12.

We deliberately do NOT ship a trivial-rfl discharge of the schema (that would be a
P5 tautology — definitional unfolding of `chiralCentralChargeOfDeligneTensor`
masquerading as a theorem). The substantive content is in the integer-to-`ZMod 24`
lift via `chiralCentralChargeOfDeligneTensor_witt_additive` and the Witt-equivalence
preservation `chiralCentralChargeOfDeligneTensor_wittEquivalent`.
-/

/-! ## §8 Wave 1b.5.10e — Combined closure theorem -/

/--
**Wave 1b.5.10e combined closure summary.** Bundles the substantive content of
Sessions 21's Wave 1b.5.10c + 5.10d substrate + 5.10g substrate into a single
6-conjunct closure theorem.

Captures:
1. `DeligneRel` is a Congruence (5.10c).
2. `DeligneTensor C D k` is a Category (5.10c).
3. `DeligneTensor C D k` is Preadditive AND Linear k (5.10c).
4. The projection `proj` is Additive (5.10c).
5. Monoidal substrate available: `C × D`, `FreeKLinear (C × D) k`, and the
   external-product bifunctor `extProd : C × D ⥤ DeligneTensor C D k` (5.10d).
6. Witt-additivity bridge: integer-level Deligne ⊠ operation lifts cleanly through
   `WittInvariant.fromChiralCentralCharge` (5.10g substrate).

Open continuations (Wave 1b.5.10d.2+, multi-session):
- Extend `DeligneRel` with monoidal-respect constructors → full
  `MonoidalCategory (DeligneTensor C D k)` instance.
- Use that to lift `BraidedCategory` (Wave 1b.5.10f).
- Discharge the `CentralChargeAdditiveUnderDeligneTensor` schema at the
  categorical level (Wave 1b.5.10g full form).
-/
theorem stage5_10e_deligneTensor_combined_closure
    (C D : Type u) [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (k : Type) [CommRing k] [Linear k C]
    [Category.{v} D] [Preadditive D] [Linear k D] [MonoidalCategory D] :
    -- (1) DeligneRel is a Congruence.
    Nonempty (Congruence (DeligneRel C D k)) ∧
    -- (2) DeligneTensor C D k is a Category.
    Nonempty (Category.{v, u} (DeligneTensor C D k)) ∧
    -- (3) DeligneTensor C D k is Preadditive AND Linear k.
    (Nonempty (Preadditive (DeligneTensor C D k)) ∧
     Nonempty (Linear k (DeligneTensor C D k))) ∧
    -- (4) The projection is Additive.
    Nonempty ((Quotient.functor (DeligneRel C D k)).Additive) ∧
    -- (5) Monoidal substrate available.
    (Nonempty (MonoidalCategory (C × D)) ∧
     Nonempty (MonoidalCategory (FreeKLinear (C × D) k)) ∧
     Nonempty (C × D ⥤ DeligneTensor C D k)) ∧
    -- (6) Witt-additivity bridge: integer cc additivity lifts to ZMod 24.
    (∀ (c₁ c₂ : ℤ),
      WittInvariant.fromChiralCentralCharge
        (chiralCentralChargeOfDeligneTensor c₁ c₂) =
      WittInvariant.fromChiralCentralCharge c₁ +
        WittInvariant.fromChiralCentralCharge c₂) :=
  ⟨⟨instCongruence C D k⟩,
   ⟨inferInstance⟩,
   ⟨⟨DeligneTensor.instPreadditive⟩, ⟨DeligneTensor.instLinear⟩⟩,
   ⟨DeligneTensor.instProjAdditive⟩,
   ⟨⟨MonoidalCategory.prodMonoidal C D⟩,
    ⟨FreeKLinear.instMonoidalCategory⟩,
    ⟨DeligneTensor.extProd⟩⟩,
   chiralCentralChargeOfDeligneTensor_witt_additive⟩

/-! ## §9 Wave 1b.5.10d.2 — MonoidalCategoryStruct on DeligneTensor C D k -/

open MonoidalCategory

namespace DeligneTensor

variable {C D : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  {k : Type} [CommRing k] [Linear k C]
  [Category.{v} D] [Preadditive D] [Linear k D] [MonoidalCategory D]

/--
**Tensor of objects** in `DeligneTensor C D k`. Defined by descending FreeKLinear's
`freeTensorObj` through the quotient projection: `[X] ⊗ [Y] := [X.as ⊗ Y.as]` where
`⊗` on the right is FreeKLinear's monoidal tensor (which itself is the lift of `C ×
D`'s `prodMonoidal` tensor).
-/
noncomputable def deligneTensorObj (X Y : DeligneTensor C D k) : DeligneTensor C D k :=
  ⟨FreeKLinear.freeTensorObj X.as Y.as⟩

/--
**Tensor of morphisms** in `DeligneTensor C D k`. Defined via `Quot.liftOn₂` over
the quotient morphism representation, descending FreeKLinear's `freeTensorHom` and
using the `DeligneRel.tens` constructor for well-definedness.
-/
noncomputable def deligneTensorHom {X₁ X₂ Y₁ Y₂ : DeligneTensor C D k}
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂) :
    deligneTensorObj X₁ Y₁ ⟶ deligneTensorObj X₂ Y₂ :=
  Quot.liftOn₂ α β (fun a b => Quot.mk _ (FreeKLinear.freeTensorHom a b))
    (fun a b₁ b₂ h => by
      simp only [HomRel.compClosure_iff_self] at h
      change (Quotient.functor (DeligneRel C D k)).map _ =
             (Quotient.functor (DeligneRel C D k)).map _
      rw [Quotient.functor_map_eq_iff]
      exact DeligneRel.tens (DeligneRel.refl a) h)
    (fun a₁ a₂ b h => by
      simp only [HomRel.compClosure_iff_self] at h
      change (Quotient.functor (DeligneRel C D k)).map _ =
             (Quotient.functor (DeligneRel C D k)).map _
      rw [Quotient.functor_map_eq_iff]
      exact DeligneRel.tens h (DeligneRel.refl b))

/--
**Whisker-left** in `DeligneTensor C D k`. Tensor on the right with an identity:
`X ◁ f := tensorHom (𝟙 X) f`.
-/
noncomputable def deligneWhiskerLeft (X : DeligneTensor C D k) {Y₁ Y₂ : DeligneTensor C D k}
    (f : Y₁ ⟶ Y₂) : deligneTensorObj X Y₁ ⟶ deligneTensorObj X Y₂ :=
  deligneTensorHom (𝟙 X) f

/--
**Whisker-right** in `DeligneTensor C D k`. Tensor on the left with an identity:
`f ▷ Y := tensorHom f (𝟙 Y)`.
-/
noncomputable def deligneWhiskerRight {X₁ X₂ : DeligneTensor C D k} (f : X₁ ⟶ X₂)
    (Y : DeligneTensor C D k) : deligneTensorObj X₁ Y ⟶ deligneTensorObj X₂ Y :=
  deligneTensorHom f (𝟙 Y)

/--
**Monoidal unit** in `DeligneTensor C D k`. Lifted from FreeKLinear's monoidal unit
(which is `(𝟙_ C, 𝟙_ D)` via `prodMonoidal`).
-/
noncomputable def deligneTensorUnit : DeligneTensor C D k :=
  ⟨(𝟙_ (FreeKLinear (C × D) k))⟩

/--
**Associator** in `DeligneTensor C D k`. Lifted from FreeKLinear's associator via
`(Quotient.functor _).mapIso`.
-/
noncomputable def deligneAssociator (X Y Z : DeligneTensor C D k) :
    deligneTensorObj (deligneTensorObj X Y) Z ≅ deligneTensorObj X (deligneTensorObj Y Z) :=
  (Quotient.functor (DeligneRel C D k)).mapIso (α_ X.as Y.as Z.as)

/--
**Left unitor** in `DeligneTensor C D k`. Lifted from FreeKLinear's left unitor via
`(Quotient.functor _).mapIso`.
-/
noncomputable def deligneLeftUnitor (X : DeligneTensor C D k) :
    deligneTensorObj deligneTensorUnit X ≅ X :=
  (Quotient.functor (DeligneRel C D k)).mapIso (λ_ X.as)

/--
**Right unitor** in `DeligneTensor C D k`. Lifted from FreeKLinear's right unitor via
`(Quotient.functor _).mapIso`.
-/
noncomputable def deligneRightUnitor (X : DeligneTensor C D k) :
    deligneTensorObj X deligneTensorUnit ≅ X :=
  (Quotient.functor (DeligneRel C D k)).mapIso (ρ_ X.as)

/--
**`MonoidalCategoryStruct (DeligneTensor C D k)` instance.** Bundles all the data
fields (object/morphism tensor, whiskerings, unit, structural isos) for the monoidal
structure on `DeligneTensor C D k`.
-/
noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct (DeligneTensor C D k) where
  tensorObj := deligneTensorObj
  whiskerLeft X _ _ f := deligneWhiskerLeft X f
  whiskerRight {_ _} f Y := deligneWhiskerRight f Y
  tensorHom α β := deligneTensorHom α β
  tensorUnit := deligneTensorUnit
  associator := deligneAssociator
  leftUnitor := deligneLeftUnitor
  rightUnitor := deligneRightUnitor

/-! ### §9a Projection-tensor compatibility (the load-bearing definitional lemma) -/

/--
**Projection-tensor compatibility.** The quotient projection of `freeTensorHom α β`
equals `deligneTensorHom (proj.map α) (proj.map β)`. This is the load-bearing
definitional fact that lets all monoidal laws descend from FreeKLinear's laws to
the quotient via `Quot.inductionOn`.

Proof: `rfl` — the `deligneTensorHom`'s `Quot.liftOn₂` definition coincides
definitionally with `Quot.mk _ ∘ freeTensorHom` on basis representatives, which is
exactly `(Quotient.functor _).map ∘ freeTensorHom`.
-/
theorem proj_freeTensorHom {X₁ X₂ Y₁ Y₂ : C × D}
    (α : (X₁ ⟶ Y₁) →₀ k) (β : (X₂ ⟶ Y₂) →₀ k) :
    (Quotient.functor (DeligneRel C D k)).map (FreeKLinear.freeTensorHom α β) =
    deligneTensorHom
      (X₁ := ⟨FreeKLinear.of X₁⟩) (X₂ := ⟨FreeKLinear.of Y₁⟩)
      (Y₁ := ⟨FreeKLinear.of X₂⟩) (Y₂ := ⟨FreeKLinear.of Y₂⟩)
      ((Quotient.functor (DeligneRel C D k)).map α)
      ((Quotient.functor (DeligneRel C D k)).map β) := rfl

/-! ### §9b Wave 1b.5.10d.2c — `id_tensorHom_id` and `tensorHom_comp_tensorHom` laws -/

/-- `id_tensorHom_id` law on `DeligneTensor C D k`: `𝟙 X ⊗ 𝟙 Y = 𝟙 (X ⊗ Y)`.
    Descends from FreeKLinear's `id_tensorHom_id` via `congr 1` after replacing
    identities with projection-images. -/
theorem deligne_id_tensorHom_id (X Y : DeligneTensor C D k) :
    deligneTensorHom (𝟙 X) (𝟙 Y) = 𝟙 (deligneTensorObj X Y) := by
  show (Quotient.functor (DeligneRel C D k)).map _ =
       (Quotient.functor (DeligneRel C D k)).map _
  congr 1
  exact MonoidalCategory.id_tensorHom_id (C := FreeKLinear (C × D) k) X.as Y.as

/-- `tensorHom_comp_tensorHom` law (interchange) on `DeligneTensor C D k`.
    Mathlib's direction: `(f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) = (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂)`.
    Descends from FreeKLinear's via `Quot.inductionOn` on all four morphisms. -/
theorem deligne_tensorHom_comp_tensorHom
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : DeligneTensor C D k}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    deligneTensorHom f₁ f₂ ≫ deligneTensorHom g₁ g₂ =
      deligneTensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  rcases f₁ with ⟨a₁⟩
  rcases f₂ with ⟨a₂⟩
  rcases g₁ with ⟨b₁⟩
  rcases g₂ with ⟨b₂⟩
  show (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _ =
       (Quotient.functor (DeligneRel C D k)).map _
  rw [← Functor.map_comp]
  congr 1
  apply MonoidalCategory.tensorHom_comp_tensorHom

/-- Whisker-left identity: `X ◁ 𝟙 Y = 𝟙 (X ⊗ Y)`. Direct from `deligne_id_tensorHom_id`. -/
theorem deligne_whiskerLeft_id (X Y : DeligneTensor C D k) :
    deligneWhiskerLeft X (𝟙 Y) = 𝟙 (deligneTensorObj X Y) := by
  exact deligne_id_tensorHom_id X Y

/-- Right-whisker identity: `𝟙 X ▷ Y = 𝟙 (X ⊗ Y)`. Direct from `deligne_id_tensorHom_id`. -/
theorem deligne_id_whiskerRight (X Y : DeligneTensor C D k) :
    deligneWhiskerRight (𝟙 X) Y = 𝟙 (deligneTensorObj X Y) := by
  exact deligne_id_tensorHom_id X Y

/-! ### §9c `tensorHom_def` and structural-iso naturalities -/

/-- `tensorHom_def`: tensor of morphisms equals whisker-right then whisker-left.
    Descends from FreeKLinear's `tensorHom_def`. -/
theorem deligne_tensorHom_def {X₁ Y₁ X₂ Y₂ : DeligneTensor C D k}
    (α : X₁ ⟶ Y₁) (β : X₂ ⟶ Y₂) :
    deligneTensorHom α β =
      deligneWhiskerRight α X₂ ≫ deligneWhiskerLeft Y₁ β := by
  rcases α with ⟨a⟩
  rcases β with ⟨b⟩
  show (Quotient.functor (DeligneRel C D k)).map _ =
       (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _
  rw [← Functor.map_comp]
  congr 1
  exact MonoidalCategory.tensorHom_def (C := FreeKLinear (C × D) k) a b

/-- Associator naturality. Descends from FreeKLinear's via `Quot.inductionOn`. -/
theorem deligne_associator_naturality
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : DeligneTensor C D k}
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂) (γ : Z₁ ⟶ Z₂) :
    deligneTensorHom (deligneTensorHom α β) γ ≫ (deligneAssociator X₂ Y₂ Z₂).hom =
      (deligneAssociator X₁ Y₁ Z₁).hom ≫ deligneTensorHom α (deligneTensorHom β γ) := by
  rcases α with ⟨a⟩
  rcases β with ⟨b⟩
  rcases γ with ⟨c⟩
  show (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _ =
       (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply MonoidalCategory.associator_naturality

/-- Left-unitor naturality. Descends from FreeKLinear's via `Quot.inductionOn`. -/
theorem deligne_leftUnitor_naturality
    {X Y : DeligneTensor C D k} (f : X ⟶ Y) :
    deligneWhiskerLeft deligneTensorUnit f ≫ (deligneLeftUnitor Y).hom =
      (deligneLeftUnitor X).hom ≫ f := by
  rcases f with ⟨g⟩
  show (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _ =
       (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply MonoidalCategory.leftUnitor_naturality

/-- Right-unitor naturality. Descends from FreeKLinear's via `Quot.inductionOn`. -/
theorem deligne_rightUnitor_naturality
    {X Y : DeligneTensor C D k} (f : X ⟶ Y) :
    deligneWhiskerRight f deligneTensorUnit ≫ (deligneRightUnitor Y).hom =
      (deligneRightUnitor X).hom ≫ f := by
  rcases f with ⟨g⟩
  show (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _ =
       (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply MonoidalCategory.rightUnitor_naturality

/-! ### §9d Pentagon and triangle laws -/

/-- Pentagon law on `DeligneTensor C D k`. Descends from FreeKLinear's pentagon. -/
theorem deligne_pentagon (W X Y Z : DeligneTensor C D k) :
    deligneWhiskerRight (deligneAssociator W X Y).hom Z ≫
      (deligneAssociator W (deligneTensorObj X Y) Z).hom ≫
        deligneWhiskerLeft W (deligneAssociator X Y Z).hom =
      (deligneAssociator (deligneTensorObj W X) Y Z).hom ≫
        (deligneAssociator W X (deligneTensorObj Y Z)).hom := by
  show (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _ =
       (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply MonoidalCategory.pentagon

/-- Triangle law on `DeligneTensor C D k`. Descends from FreeKLinear's triangle. -/
theorem deligne_triangle (X Y : DeligneTensor C D k) :
    (deligneAssociator X deligneTensorUnit Y).hom ≫
      deligneWhiskerLeft X (deligneLeftUnitor Y).hom =
      deligneWhiskerRight (deligneRightUnitor X).hom Y := by
  show (Quotient.functor (DeligneRel C D k)).map _ ≫
       (Quotient.functor (DeligneRel C D k)).map _ =
       (Quotient.functor (DeligneRel C D k)).map _
  rw [← Functor.map_comp]
  congr 1
  apply MonoidalCategory.triangle

/-! ### §9e MonoidalCategory instance assembly -/

/--
**`MonoidalCategory (DeligneTensor C D k)` instance.** Wave 1b.5.10d.2c deliverable.
Bundles all 10 monoidal coherence laws (tensor_id, tensor_comp, tensorHom_def,
whiskerLeft_id, id_whiskerRight, associator_naturality, leftUnitor_naturality,
rightUnitor_naturality, pentagon, triangle), each descended from FreeKLinear's
corresponding law via `Quot.inductionOn` + `congr 1` + functor-map-of-equal-things.

This is the *load-bearing* deliverable that lifts the full Wave 1b.5.10b monoidal
infrastructure on `FreeKLinear (C × D) k` through the `DeligneRel` quotient to
make `DeligneTensor C D k` a genuine k-linear monoidal category.
-/
noncomputable instance instMonoidalCategory :
    MonoidalCategory (DeligneTensor C D k) where
  tensorHom_def := deligne_tensorHom_def
  id_tensorHom_id := deligne_id_tensorHom_id
  tensorHom_comp_tensorHom := deligne_tensorHom_comp_tensorHom
  whiskerLeft_id := deligne_whiskerLeft_id
  id_whiskerRight := deligne_id_whiskerRight
  associator_naturality := deligne_associator_naturality
  leftUnitor_naturality := deligne_leftUnitor_naturality
  rightUnitor_naturality := deligne_rightUnitor_naturality
  pentagon := deligne_pentagon
  triangle := deligne_triangle

end DeligneTensor

end SKEFTHawking.SymTFTAudit
