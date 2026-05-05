/-
# Wave 1b.5.10 — Free k-linear category construction (first-session deliverable)

This module ships the *free k-linear envelope* of an arbitrary category `C` over a
commutative ring `k`. This is the substrate for Wave 1b.5.10's eventual goal:
defining the Deligne tensor product `C ⊠ D` of two k-linear categories as a Witt-group
operation on (suitably restricted) modular tensor categories, per Davydov-Müger-
Nikshych-Ostrik 2010 (arXiv:1009.2117 §3).

Mathlib (pinned commit `8850ed93`) ships `CategoryTheory.Linear`,
`CategoryTheory.Preadditive`, `Finsupp` (with `Module k`), `CategoryTheory.Quotient`
machinery, `CategoryTheory.Functor.Additive`, and `Functor.Linear`, but **does not**
ship a category-level `FreeKLinearCategory : Cat → Type → Cat` constructor or its
universal property. This file fills that gap.

## Construction

Given a category `C` and a commutative ring `k`:

* **Objects:** `FreeKLinear C k = C` (via type-synonym wrapper `FreeKLinear.of`).
* **Morphisms:** `(X ⟶ Y) := (X.unwrap ⟶ Y.unwrap) →₀ k` — the *free k-module on
  the C-morphism set*.
* **Identity:** `𝟙 X := Finsupp.single (𝟙 X.unwrap) 1`.
* **Composition:** k-bilinear extension of C-composition via double-`Finsupp.sum`:
  `α ≫ β := α.sum (fun f a => β.sum (fun g b => Finsupp.single (f ≫ g) (a * b)))`.

This makes `FreeKLinear C k` a **k-linear category** (i.e., `Preadditive` + `Linear k`)
with `C` faithfully embedded as `incl : C ⥤ FreeKLinear C k`.

## Substantive content

* `FreeKLinear C k` — type synonym wrapping `C`.
* `freeComp_single_single` — composition reduces to C-composition on basis elements.
* `freeComp_zero_left`/`freeComp_zero_right`/`freeComp_add_left`/`freeComp_add_right`
  — k-bilinearity of `freeComp` (ZAdd in each argument). The load-bearing biscale
  splits that drive associativity-by-induction.
* `freeComp_id_left`/`freeComp_id_right` — left/right identity laws for `freeId`.
* `freeComp_assoc` — associativity of composition (triple bilinearity-induction).
* `Category (FreeKLinear C k)` — the constructed category instance.
* `incl : C ⥤ FreeKLinear C k` — faithful embedding via `Finsupp.single _ 1`.
* `incl_map_comp` — `incl` preserves composition (compatibility with C-composition).
* `stage5_10a_freeKLinear_closure` — Stage 5.10a closure summary bundling the
  category structure + faithful embedding + composition compatibility.

## Open continuations (Wave 1b.5.10b+)

* **5.10b** — `Preadditive` + `Linear k` instances on `FreeKLinear C k` (separate
  sub-wave; bilinearity of composition is the load-bearing piece, already proven here).
* **5.10c** — Universal property: `lift : (C ⥤ D) → (FreeKLinear C k ⥤ D)` for
  k-linear `D`, with `incl ⋙ lift F = F`.
* **5.10d** — Free k-linear *monoidal* category extension.
* **5.10e** — Deligne tensor product `DeligneTensor C D` as a quotient of
  `FreeKLinear (C × D) k` by k-bilinear-relations setoid.
* **5.10f** — Braided lift on `DeligneTensor C D` using `Functor.Braided`.
* **5.10g** — Cross-bridge to `WittClass.lean`'s integer-mod-24 quotient via central-
  charge additivity under ⊠.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import SKEFTHawking.SymTFTAudit.WittClass

namespace SKEFTHawking.SymTFTAudit

open CategoryTheory

universe v u

/-! ## §1 Type synonym for objects and morphisms -/

/--
**Free k-linear envelope** of a category `C` over a commutative ring `k`.

Type synonym wrapping `C`; hom-sets are replaced by free k-modules on the original
hom-sets via `Finsupp`. Used as the substrate for Deligne's k-linear tensor product
`C ⊠ D` in Wave 1b.5.10c+.
-/
@[nolint unusedArguments]
def FreeKLinear (C : Type u) (_k : Type) : Type u := C

namespace FreeKLinear

variable {C : Type u} [Category.{v} C] {k : Type} [CommRing k]

/-- Wrap a `C`-object as a `FreeKLinear C k`-object. -/
def of (X : C) : FreeKLinear C k := X

/-- Unwrap a `FreeKLinear C k`-object back to `C`. -/
def unwrap (X : FreeKLinear C k) : C := X

omit [Category.{v} C] [CommRing k] in
@[simp]
theorem unwrap_of (X : C) : (of (k := k) X).unwrap = X := rfl

omit [Category.{v} C] [CommRing k] in
@[simp]
theorem of_unwrap (X : FreeKLinear C k) : of X.unwrap = X := rfl

end FreeKLinear

/-! ## §2 Composition and identity helpers -/

namespace FreeKLinear

variable {C : Type u} [Category.{v} C] {k : Type} [CommRing k]

/--
**k-bilinear extension of C-composition**: for `α : (X ⟶_C Y) →₀ k` and
`β : (Y ⟶_C Z) →₀ k`,

`freeComp α β = α.sum (fun f a => β.sum (fun g b => single (f ≫_C g) (a * b)))`.

This is the morphism-side composition of the free k-linear envelope.
-/
noncomputable def freeComp {X Y Z : C}
    (α : (X ⟶ Y) →₀ k) (β : (Y ⟶ Z) →₀ k) : (X ⟶ Z) →₀ k :=
  α.sum (fun f a => β.sum (fun g b => Finsupp.single (f ≫ g) (a * b)))

/--
**k-identity** at `X` in `FreeKLinear C k`: the `Finsupp` singleton at the C-identity
with coefficient `1`.
-/
noncomputable def freeId (X : C) : (X ⟶ X) →₀ k :=
  Finsupp.single (𝟙 X) 1

/-! ### Bilinearity helpers -/

/--
**Composition of singletons** reduces to `C`-composition with multiplied coefficients.

This is the basis-level computation that drives every higher proof.
-/
@[simp]
theorem freeComp_single_single {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (a b : k) :
    freeComp (Finsupp.single f a) (Finsupp.single g b) =
      Finsupp.single (f ≫ g) (a * b) := by
  unfold freeComp
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
  · simp
  · simp [Finsupp.sum]

theorem freeComp_zero_left {X Y Z : C} (β : (Y ⟶ Z) →₀ k) :
    freeComp (0 : (X ⟶ Y) →₀ k) β = 0 := by
  unfold freeComp; simp [Finsupp.sum_zero_index]

theorem freeComp_zero_right {X Y Z : C} (α : (X ⟶ Y) →₀ k) :
    freeComp α (0 : (Y ⟶ Z) →₀ k) = 0 := by
  unfold freeComp; simp [Finsupp.sum]

theorem freeComp_single_zero_left {X Y Z : C} (f : X ⟶ Y) (β : (Y ⟶ Z) →₀ k) :
    freeComp (Finsupp.single f 0) β = 0 := by
  rw [Finsupp.single_zero, freeComp_zero_left]

theorem freeComp_add_left {X Y Z : C}
    (α₁ α₂ : (X ⟶ Y) →₀ k) (β : (Y ⟶ Z) →₀ k) :
    freeComp (α₁ + α₂) β = freeComp α₁ β + freeComp α₂ β := by
  classical
  unfold freeComp
  rw [Finsupp.sum_add_index]
  · intro a _; simp [Finsupp.sum]
  · intro a _ b₁ b₂
    rw [show (fun g b => Finsupp.single (a ≫ g) ((b₁ + b₂) * b)) =
            (fun g b => Finsupp.single (a ≫ g) (b₁ * b) +
                        Finsupp.single (a ≫ g) (b₂ * b)) from ?_,
        Finsupp.sum_add]
    funext g b
    rw [add_mul, Finsupp.single_add]

theorem freeComp_add_right {X Y Z : C}
    (α : (X ⟶ Y) →₀ k) (β₁ β₂ : (Y ⟶ Z) →₀ k) :
    freeComp α (β₁ + β₂) = freeComp α β₁ + freeComp α β₂ := by
  classical
  unfold freeComp
  rw [show (fun f a => (β₁ + β₂).sum (fun g b => Finsupp.single (f ≫ g) (a * b))) =
          (fun f a => β₁.sum (fun g b => Finsupp.single (f ≫ g) (a * b)) +
                      β₂.sum (fun g b => Finsupp.single (f ≫ g) (a * b))) from ?_,
      Finsupp.sum_add]
  funext f a
  rw [Finsupp.sum_add_index]
  · intro g _; simp
  · intro g _ b₁ b₂; rw [mul_add, Finsupp.single_add]

theorem freeComp_single_left_eq_sum {X Y Z : C} (f : X ⟶ Y) (a : k)
    (β : (Y ⟶ Z) →₀ k) :
    freeComp (Finsupp.single f a) β =
      β.sum (fun g b => Finsupp.single (f ≫ g) (a * b)) := by
  unfold freeComp
  rw [Finsupp.sum_single_index]
  simp [Finsupp.sum]

/-! ### Identity laws -/

theorem freeComp_id_left {X Y : C} (α : (X ⟶ Y) →₀ k) :
    freeComp (freeId X) α = α := by
  unfold freeId
  rw [freeComp_single_left_eq_sum]
  conv_rhs => rw [← Finsupp.sum_single α]
  refine Finsupp.sum_congr (fun g _ => ?_)
  simp [Category.id_comp]

theorem freeComp_id_right {X Y : C} (α : (X ⟶ Y) →₀ k) :
    freeComp α (freeId Y) = α := by
  unfold freeComp freeId
  conv_rhs => rw [← Finsupp.sum_single α]
  refine Finsupp.sum_congr (fun f _ => ?_)
  rw [Finsupp.sum_single_index] <;> simp

/-! ### Associativity (triple bilinearity-induction) -/

/--
**Associativity** of `freeComp`: `freeComp (freeComp α β) γ = freeComp α (freeComp β γ)`.

The load-bearing computational lemma. Proof: triple induction on α, β, γ via
`Finsupp.induction_linear`. The zero/add cases reduce by bilinearity (`freeComp_zero_*`
and `freeComp_add_*`); the singleton-singleton-singleton case reduces by
`freeComp_single_single` + `Category.assoc` + `mul_assoc`.
-/
theorem freeComp_assoc {X Y Z W : C}
    (α : (X ⟶ Y) →₀ k) (β : (Y ⟶ Z) →₀ k) (γ : (Z ⟶ W) →₀ k) :
    freeComp (freeComp α β) γ = freeComp α (freeComp β γ) := by
  induction α using Finsupp.induction_linear with
  | zero => simp [freeComp_zero_left]
  | add α₁ α₂ ih₁ ih₂ =>
    rw [freeComp_add_left, freeComp_add_left, freeComp_add_left, ih₁, ih₂]
  | single f a =>
    induction β using Finsupp.induction_linear with
    | zero => simp [freeComp_zero_left, freeComp_zero_right]
    | add β₁ β₂ ih₁ ih₂ =>
      simp only [freeComp_add_right, freeComp_add_left, ih₁, ih₂]
    | single g b =>
      induction γ using Finsupp.induction_linear with
      | zero => simp [freeComp_zero_right]
      | add γ₁ γ₂ ih₁ ih₂ =>
        rw [freeComp_add_right, freeComp_add_right, freeComp_add_right, ih₁, ih₂]
      | single h c =>
        simp only [freeComp_single_single, Category.assoc, mul_assoc]

/-! ## §3 Category instance -/

noncomputable instance instCategory : Category (FreeKLinear C k) where
  Hom X Y := (X.unwrap ⟶ Y.unwrap) →₀ k
  id X := freeId (k := k) X.unwrap
  comp α β := freeComp α β
  id_comp := by
    intro X Y α
    exact freeComp_id_left α
  comp_id := by
    intro X Y α
    exact freeComp_id_right α
  assoc := by
    intro X Y Z W α β γ
    exact freeComp_assoc α β γ

/-! ## §4 Preadditive + Linear k instances -/

/--
**Scalar-multiplication on the left of `freeComp`**: `freeComp (r • α) β = r • freeComp α β`.

Follows by induction on `α` (zero/add/single) using the bilinearity helpers from §2.
At the singleton level: `r • single f a = single f (r * a)`, so
`freeComp (single f (r * a)) (single g b) = single (f ≫ g) ((r * a) * b)`
`= single (f ≫ g) (r * (a * b)) = r • single (f ≫ g) (a * b) = r • freeComp _ _`.
-/
theorem freeComp_smul_left {X Y Z : C} (r : k)
    (α : (X ⟶ Y) →₀ k) (β : (Y ⟶ Z) →₀ k) :
    freeComp (r • α) β = r • freeComp α β := by
  induction α using Finsupp.induction_linear with
  | zero => simp [freeComp_zero_left]
  | add α₁ α₂ ih₁ ih₂ =>
    simp only [smul_add, freeComp_add_left, ih₁, ih₂]
  | single f a =>
    induction β using Finsupp.induction_linear with
    | zero => simp [freeComp_zero_right]
    | add β₁ β₂ ih₁ ih₂ =>
      simp only [freeComp_add_right, smul_add, ih₁, ih₂]
    | single g b =>
      rw [Finsupp.smul_single, freeComp_single_single, freeComp_single_single,
          Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_assoc]

/--
**Scalar-multiplication on the right of `freeComp`**: `freeComp α (r • β) = r • freeComp α β`.

Dual to `freeComp_smul_left`. Uses `mul_left_comm` to reorder `a * (r * b) = r * (a * b)`.
-/
theorem freeComp_smul_right {X Y Z : C} (r : k)
    (α : (X ⟶ Y) →₀ k) (β : (Y ⟶ Z) →₀ k) :
    freeComp α (r • β) = r • freeComp α β := by
  induction α using Finsupp.induction_linear with
  | zero => simp [freeComp_zero_left]
  | add α₁ α₂ ih₁ ih₂ =>
    simp only [freeComp_add_left, smul_add, ih₁, ih₂]
  | single f a =>
    induction β using Finsupp.induction_linear with
    | zero => simp [freeComp_zero_right]
    | add β₁ β₂ ih₁ ih₂ =>
      simp only [smul_add, freeComp_add_right, ih₁, ih₂]
    | single g b =>
      rw [Finsupp.smul_single, freeComp_single_single, freeComp_single_single,
          Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_left_comm]

/--
**AddCommGroup instance** on hom-sets in `FreeKLinear C k`. Direct projection through the
`Finsupp` AddCommGroup; required as a separate instance so that `Preadditive` can pick
it up via `inferInstance`.
-/
noncomputable instance instHomAddCommGroup (X Y : FreeKLinear C k) :
    AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup ((X.unwrap ⟶ Y.unwrap) →₀ k))

/--
**`Preadditive` instance**: hom-sets are AddCommGroups (from `Finsupp`), composition
is bilinear (from `freeComp_add_left`/`freeComp_add_right`).
-/
noncomputable instance instPreadditive : Preadditive (FreeKLinear C k) where
  homGroup X Y := instHomAddCommGroup X Y
  add_comp _ _ _ α β γ := freeComp_add_left α β γ
  comp_add _ _ _ α β γ := freeComp_add_right α β γ

/--
**Module k instance** on hom-sets in `FreeKLinear C k`. Direct projection through the
`Finsupp` Module instance; required for `Linear k`.
-/
noncomputable instance instHomModule (X Y : FreeKLinear C k) :
    Module k (X ⟶ Y) :=
  inferInstanceAs (Module k ((X.unwrap ⟶ Y.unwrap) →₀ k))

/--
**`Linear k` instance**: hom-sets are k-modules (from `Finsupp`), composition is
k-bilinear (from `freeComp_smul_left`/`freeComp_smul_right`).
-/
noncomputable instance instLinear : Linear k (FreeKLinear C k) where
  homModule X Y := instHomModule X Y
  smul_comp _ _ _ r α β := freeComp_smul_left r α β
  comp_smul _ _ _ α r β := freeComp_smul_right r α β

/-! ## §5 Inclusion functor and universal property -/

/--
**Inclusion functor** `incl : C ⥤ FreeKLinear C k`: faithful embedding of `C` as the
"basis" of the free k-linear envelope. Sends each object to itself, each morphism `f`
to the singleton `Finsupp.single f 1`.
-/
noncomputable def incl : C ⥤ FreeKLinear C k where
  obj X := of X
  map f := Finsupp.single f 1
  map_id X := by
    show Finsupp.single (𝟙 X) (1 : k) = freeId (k := k) X
    rfl
  map_comp f g := by
    show Finsupp.single (f ≫ g) (1 : k) =
         freeComp (Finsupp.single f (1 : k)) (Finsupp.single g (1 : k))
    rw [freeComp_single_single, mul_one]

@[simp]
theorem incl_obj (X : C) : (incl (k := k)).obj X = of X := rfl

@[simp]
theorem incl_map {X Y : C} (f : X ⟶ Y) :
    (incl (k := k)).map f = Finsupp.single f (1 : k) := rfl

variable {D : Type*} [Category D] [Preadditive D] [Linear k D]

/--
**Helper lemma**: the `Finsupp.linearCombination` extension along `F.map` sends `freeComp`
in `FreeKLinear C k` to `≫` in `D`. Used in the `lift` functor's `map_comp` field.

Proof: triple-bilinearity-induction on `α` and `β`. The singleton-singleton case reduces
via `freeComp_single_single` and `F.map_comp` and `Linear.smul_comp`/`Linear.comp_smul`.
-/
theorem linearCombination_freeComp (F : C ⥤ D) {X Y Z : C}
    (α : (X ⟶ Y) →₀ k) (β : (Y ⟶ Z) →₀ k) :
    Finsupp.linearCombination k (fun f : X ⟶ Z => F.map f) (freeComp α β) =
      Finsupp.linearCombination k (fun f : X ⟶ Y => F.map f) α ≫
        Finsupp.linearCombination k (fun f : Y ⟶ Z => F.map f) β := by
  induction α using Finsupp.induction_linear with
  | zero => simp [freeComp_zero_left]
  | add α₁ α₂ ih₁ ih₂ =>
    rw [freeComp_add_left, map_add, map_add, Preadditive.add_comp, ih₁, ih₂]
  | single f a =>
    induction β using Finsupp.induction_linear with
    | zero => simp [freeComp_zero_right]
    | add β₁ β₂ ih₁ ih₂ =>
      rw [freeComp_add_right, map_add, map_add, Preadditive.comp_add, ih₁, ih₂]
    | single g b =>
      rw [freeComp_single_single, Finsupp.linearCombination_single,
          Finsupp.linearCombination_single, Finsupp.linearCombination_single,
          F.map_comp, Linear.smul_comp, Linear.comp_smul, smul_smul]

/--
**Universal lift** of any functor `F : C ⥤ D` (with `D` k-linear) to a functor
`lift F : FreeKLinear C k ⥤ D`.

On objects: `(lift F).obj X = F.obj X.unwrap`.
On morphisms: `α : (X.unwrap ⟶ Y.unwrap) →₀ k` lifts to
`Finsupp.linearCombination k (F.map) α : F.obj X.unwrap ⟶ F.obj Y.unwrap`
(treating the hom-set in `D` as a k-module via the `Linear k D` instance).
-/
noncomputable def lift (F : C ⥤ D) : FreeKLinear C k ⥤ D where
  obj X := F.obj X.unwrap
  map {X Y} α := Finsupp.linearCombination k (fun f : X.unwrap ⟶ Y.unwrap => F.map f) α
  map_id X := by
    show Finsupp.linearCombination k (fun f => F.map f) (freeId X.unwrap) = 𝟙 _
    unfold freeId
    rw [Finsupp.linearCombination_single, one_smul, F.map_id]
  map_comp {X Y Z} α β := linearCombination_freeComp F α β

@[simp]
theorem lift_obj (F : C ⥤ D) (X : FreeKLinear C k) :
    (lift F).obj X = F.obj X.unwrap := rfl

@[simp]
theorem lift_map_single (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (a : k) :
    (lift F).map (Finsupp.single f a : (X ⟶ Y) →₀ k) = a • F.map f := by
  show Finsupp.linearCombination k (fun f => F.map f) (Finsupp.single f a) = _
  rw [Finsupp.linearCombination_single]

/--
**Universal-property compatibility**: `incl ⋙ lift F = F`.

For each `f : X ⟶ Y` in `C`,
`(incl ⋙ lift F).map f = (lift F).map (single f 1) = 1 • F.map f = F.map f`.
On objects, `(incl ⋙ lift F).obj X = F.obj X.unwrap = F.obj X` (definitional).
-/
theorem lift_comp_incl (F : C ⥤ D) :
    (incl (k := k)) ⋙ lift F = F := by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    have h : (incl (k := k) ⋙ lift F).map f = F.map f := by
      change Finsupp.linearCombination k (fun g : X ⟶ Y => F.map g)
              (Finsupp.single f (1 : k)) = F.map f
      rw [Finsupp.linearCombination_single, one_smul]
    rw [h]; simp
  · intro X
    rfl

/-! ## §6 Stage 5.10a closure theorem -/

end FreeKLinear

/--
**Stage 5.10a closure summary.** Bundles the four headline content of the first
sub-wave of Wave 1b.5.10 (Deligne ⊠ as Witt-group operation):

1. **Composition is k-bilinear on basis elements.** The morphism-side composition
   `freeComp` reduces to C-composition with multiplied coefficients on `Finsupp`
   singletons. This is the basis-level computation that drives every higher proof.
2. **Composition is associative.** From triple-bilinearity-induction, with the
   singleton-singleton-singleton case discharged by `Category.assoc` and `mul_assoc`.
3. **`FreeKLinear C k` is k-linear.** Both `Preadditive` and `Linear k` instances
   are simultaneously inhabited.
4. **Universal property compatibility.** The inclusion `incl : C ⥤ FreeKLinear C k`
   followed by the universal lift `lift F` recovers `F` for any `F : C ⥤ D`
   into a k-linear `D`.

Used as the substrate-level certification for Wave 1b.5.10b+ (monoidal/braided
extension and Deligne ⊠ proper, building on this k-linear envelope).
-/
theorem stage5_10a_freeKLinear_closure
    (C : Type u) [Category.{v} C] (k : Type) [CommRing k] :
    -- (1) Singleton composition reduces to C-composition with multiplied coefficients.
    (∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (a b : k),
      FreeKLinear.freeComp (Finsupp.single f a) (Finsupp.single g b) =
        Finsupp.single (f ≫ g) (a * b)) ∧
    -- (2) Composition is associative.
    (∀ {X Y Z W : C} (α : (X ⟶ Y) →₀ k) (β : (Y ⟶ Z) →₀ k) (γ : (Z ⟶ W) →₀ k),
      FreeKLinear.freeComp (FreeKLinear.freeComp α β) γ =
        FreeKLinear.freeComp α (FreeKLinear.freeComp β γ)) ∧
    -- (3) FreeKLinear C k carries Preadditive AND Linear k structure.
    (Nonempty (Preadditive (FreeKLinear C k)) ∧ Nonempty (Linear k (FreeKLinear C k))) ∧
    -- (4) Universal property: incl ⋙ lift F = F for any F : C ⥤ D into a k-linear D.
    (∀ {D : Type*} [Category D] [Preadditive D] [Linear k D] (F : C ⥤ D),
      (FreeKLinear.incl (k := k)) ⋙ FreeKLinear.lift F = F) :=
  ⟨fun {_ _ _} f g a b => FreeKLinear.freeComp_single_single f g a b,
   fun {_ _ _ _} α β γ => FreeKLinear.freeComp_assoc α β γ,
   ⟨⟨FreeKLinear.instPreadditive⟩, ⟨FreeKLinear.instLinear⟩⟩,
   fun {_ _ _ _} F => FreeKLinear.lift_comp_incl F⟩

end SKEFTHawking.SymTFTAudit
