/-
# Wave 1b.5.10b — Free k-linear monoidal extension (first sub-session deliverable)

This module extends Session 18's `SymTFTAudit/FreeKLinearCategory.lean` with the
**morphism-side** of a monoidal structure on `FreeKLinear C k` when the underlying
category `C` is monoidal.

Object-side and structural data (associator/unitor) lifts are deferred to a
follow-on sub-session because their full discharge requires the morphism-side
machinery shipped here as a prerequisite.

## Construction

Given a monoidal category `C` and a commutative ring `k`, define:

* **`freeTensorHom`**: k-bilinear extension of C's `tensorHom` via double-`Finsupp.sum`:

  `freeTensorHom α β = α.sum (fun f a => β.sum (fun g b => single (f ⊗ₘ g) (a * b)))`.

This is the morphism-side tensor for `MonoidalCategory (FreeKLinear C k)`. It is
constructed in lockstep with Session 18's `freeComp` and inherits the same
triple-bilinearity-induction proof pattern.

## Substantive content

* `freeTensorHom_single_single` — basis-level reduction (tensor of singletons =
  singleton at C-tensor with multiplied coefficients).
* `freeTensorHom_zero_left/right`, `freeTensorHom_add_left/right`,
  `freeTensorHom_smul_left/right` — k-bilinearity in each argument (follows the
  same `Finsupp.induction_linear` pattern as Session 18's `freeComp` helpers).
* `freeTensorHom_id_id` — `freeTensorHom (freeId X) (freeId Y) = freeId (X ⊗ Y)`,
  using C's `tensorHom_id`.
* `freeTensorHom_freeComp_interchange` — **load-bearing interchange law**:

  `freeTensorHom (freeComp α β) (freeComp α' β') =
     freeComp (freeTensorHom α α') (freeTensorHom β β')`.

  The bilinear analog of C's `tensor_comp` law. Proven by triple-bilinearity-
  induction; singleton-singleton-singleton-singleton case discharged by C's
  `tensor_comp` + `mul_comm`/`mul_assoc`.
* `stage5_10b_partial_freeTensorHom_closure` — Stage 5.10b partial closure
  (morphism-side): bundles the singleton reduction + identity-tensor-identity +
  interchange law. **Partial** because object-level associator/unitor lifts
  + pentagon/triangle laws + full `MonoidalCategory (FreeKLinear C k)` instance
  are deferred to the follow-on sub-session(s).

## Open continuations (Wave 1b.5.10b+ follow-on sub-sessions)

* **5.10b.2** — `MonoidalCategoryStruct (FreeKLinear C k)` instance: object-level
  tensor (definitionally inherited from C via the `unwrap`/`of` synonym), unit,
  associator/unitor as `incl.map` lifts of C's structural isomorphisms,
  whiskerLeft/Right via `freeTensorHom`.
* **5.10b.3** — `MonoidalCategory (FreeKLinear C k)` instance: pentagon, triangle,
  naturality-of-associator/unitor laws — all reduce to C's laws via
  bilinearity-induction at the basis level.
* **5.10b.4** — `Functor.LaxMonoidal incl` / `Functor.Monoidal incl` instances.
* **5.10c+** — Deligne ⊠ proper as `FreeKLinear (C × D) k` quotient by
  k-bilinear-relations.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import SKEFTHawking.SymTFTAudit.FreeKLinearCategory

namespace SKEFTHawking.SymTFTAudit

open CategoryTheory MonoidalCategory

universe v u

namespace FreeKLinear

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {k : Type} [CommRing k]

/-! ## §1 Free tensor on morphisms -/

/--
**k-bilinear extension of C's tensor on morphisms**: for
`α : (X₁ ⟶_C Y₁) →₀ k` and `β : (X₂ ⟶_C Y₂) →₀ k`,

`freeTensorHom α β = α.sum (fun f a => β.sum (fun g b => single (f ⊗ₘ g) (a * b)))`.

This is the morphism-side tensor of the free k-linear monoidal envelope. Built in
lockstep with `freeComp`; same bilinearity properties via the same induction
patterns.
-/
noncomputable def freeTensorHom {X₁ Y₁ X₂ Y₂ : C}
    (α : (X₁ ⟶ Y₁) →₀ k) (β : (X₂ ⟶ Y₂) →₀ k) : (X₁ ⊗ X₂ ⟶ Y₁ ⊗ Y₂) →₀ k :=
  α.sum (fun f a => β.sum (fun g b => Finsupp.single (f ⊗ₘ g) (a * b)))

/-! ### Bilinearity helpers -/

/--
**Tensor of singletons** reduces to C-tensor with multiplied coefficients.
The basis-level computation that drives every higher proof.
-/
@[simp]
theorem freeTensorHom_single_single {X₁ Y₁ X₂ Y₂ : C}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (a b : k) :
    freeTensorHom (Finsupp.single f a) (Finsupp.single g b) =
      Finsupp.single (f ⊗ₘ g) (a * b) := by
  unfold freeTensorHom
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
  · simp
  · simp [Finsupp.sum]

theorem freeTensorHom_zero_left {X₁ Y₁ X₂ Y₂ : C} (β : (X₂ ⟶ Y₂) →₀ k) :
    freeTensorHom (0 : (X₁ ⟶ Y₁) →₀ k) β = 0 := by
  unfold freeTensorHom; simp [Finsupp.sum_zero_index]

theorem freeTensorHom_zero_right {X₁ Y₁ X₂ Y₂ : C} (α : (X₁ ⟶ Y₁) →₀ k) :
    freeTensorHom α (0 : (X₂ ⟶ Y₂) →₀ k) = 0 := by
  unfold freeTensorHom; simp [Finsupp.sum]

theorem freeTensorHom_add_left {X₁ Y₁ X₂ Y₂ : C}
    (α₁ α₂ : (X₁ ⟶ Y₁) →₀ k) (β : (X₂ ⟶ Y₂) →₀ k) :
    freeTensorHom (α₁ + α₂) β = freeTensorHom α₁ β + freeTensorHom α₂ β := by
  classical
  unfold freeTensorHom
  rw [Finsupp.sum_add_index]
  · intro a _; simp [Finsupp.sum]
  · intro a _ b₁ b₂
    rw [show (fun g b => Finsupp.single (a ⊗ₘ g) ((b₁ + b₂) * b)) =
            (fun g b => Finsupp.single (a ⊗ₘ g) (b₁ * b) +
                        Finsupp.single (a ⊗ₘ g) (b₂ * b)) from ?_,
        Finsupp.sum_add]
    funext g b
    rw [add_mul, Finsupp.single_add]

theorem freeTensorHom_add_right {X₁ Y₁ X₂ Y₂ : C}
    (α : (X₁ ⟶ Y₁) →₀ k) (β₁ β₂ : (X₂ ⟶ Y₂) →₀ k) :
    freeTensorHom α (β₁ + β₂) = freeTensorHom α β₁ + freeTensorHom α β₂ := by
  classical
  unfold freeTensorHom
  rw [show (fun f a => (β₁ + β₂).sum (fun g b => Finsupp.single (f ⊗ₘ g) (a * b))) =
          (fun f a => β₁.sum (fun g b => Finsupp.single (f ⊗ₘ g) (a * b)) +
                      β₂.sum (fun g b => Finsupp.single (f ⊗ₘ g) (a * b))) from ?_,
      Finsupp.sum_add]
  funext f a
  rw [Finsupp.sum_add_index]
  · intro g _; simp
  · intro g _ b₁ b₂; rw [mul_add, Finsupp.single_add]

theorem freeTensorHom_smul_left {X₁ Y₁ X₂ Y₂ : C} (r : k)
    (α : (X₁ ⟶ Y₁) →₀ k) (β : (X₂ ⟶ Y₂) →₀ k) :
    freeTensorHom (r • α) β = r • freeTensorHom α β := by
  induction α using Finsupp.induction_linear with
  | zero => simp [freeTensorHom_zero_left]
  | add α₁ α₂ ih₁ ih₂ =>
    simp only [smul_add, freeTensorHom_add_left, ih₁, ih₂]
  | single f a =>
    induction β using Finsupp.induction_linear with
    | zero => simp [freeTensorHom_zero_right]
    | add β₁ β₂ ih₁ ih₂ =>
      simp only [freeTensorHom_add_right, smul_add, ih₁, ih₂]
    | single g b =>
      rw [Finsupp.smul_single, freeTensorHom_single_single,
          freeTensorHom_single_single, Finsupp.smul_single,
          smul_eq_mul, smul_eq_mul, mul_assoc]

theorem freeTensorHom_smul_right {X₁ Y₁ X₂ Y₂ : C} (r : k)
    (α : (X₁ ⟶ Y₁) →₀ k) (β : (X₂ ⟶ Y₂) →₀ k) :
    freeTensorHom α (r • β) = r • freeTensorHom α β := by
  induction α using Finsupp.induction_linear with
  | zero => simp [freeTensorHom_zero_left]
  | add α₁ α₂ ih₁ ih₂ =>
    simp only [freeTensorHom_add_left, smul_add, ih₁, ih₂]
  | single f a =>
    induction β using Finsupp.induction_linear with
    | zero => simp [freeTensorHom_zero_right]
    | add β₁ β₂ ih₁ ih₂ =>
      simp only [smul_add, freeTensorHom_add_right, ih₁, ih₂]
    | single g b =>
      rw [Finsupp.smul_single, freeTensorHom_single_single,
          freeTensorHom_single_single, Finsupp.smul_single,
          smul_eq_mul, smul_eq_mul, mul_left_comm]

/-! ## §2 Identity tensor identity -/

/--
**Identity tensor identity**: `freeTensorHom (freeId X) (freeId Y) = freeId (X ⊗ Y)`.

Proof: by `freeTensorHom_single_single` reducing to `single (𝟙 X ⊗ₘ 𝟙 Y) (1 * 1)`,
then C's `tensorHom_id` collapses `𝟙 X ⊗ₘ 𝟙 Y = 𝟙 (X ⊗ Y)`.
-/
theorem freeTensorHom_id_id (X Y : C) :
    freeTensorHom (freeId (k := k) X) (freeId (k := k) Y) = freeId (X ⊗ Y) := by
  unfold freeId
  rw [freeTensorHom_single_single, mul_one, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_whiskerRight]

/-! ## §3 Interchange law (load-bearing) -/

/--
**Interchange law for `freeTensorHom` and `freeComp`**:

`freeTensorHom (freeComp α β) (freeComp α' β') =
   freeComp (freeTensorHom α α') (freeTensorHom β β')`.

The k-bilinear analog of C's `tensor_comp` law (`(f ≫ g) ⊗ₘ (f' ≫ g') =
(f ⊗ₘ f') ≫ (g ⊗ₘ g')`). Proven by quadruple-bilinearity-induction via
`Finsupp.induction_linear`: zero/add cases reduce by bilinearity helpers; the
singleton-singleton-singleton-singleton case discharges via C's `tensor_comp`,
`Finsupp.single`-arithmetic (`a * b * (c * d) = (a * c) * (b * d)`), and
`freeTensorHom_single_single` + `freeComp_single_single`.

This is the load-bearing compatibility for `MonoidalCategory (FreeKLinear C k)`.
-/
theorem freeTensorHom_freeComp_interchange {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
    (α : (X₁ ⟶ Y₁) →₀ k) (β : (Y₁ ⟶ Z₁) →₀ k)
    (α' : (X₂ ⟶ Y₂) →₀ k) (β' : (Y₂ ⟶ Z₂) →₀ k) :
    freeTensorHom (freeComp α β) (freeComp α' β') =
      freeComp (freeTensorHom α α') (freeTensorHom β β') := by
  induction α using Finsupp.induction_linear with
  | zero => simp [freeComp_zero_left, freeTensorHom_zero_left]
  | add α₁ α₂ ih₁ ih₂ =>
    simp only [freeComp_add_left, freeTensorHom_add_left, ih₁, ih₂]
  | single f a =>
    induction β using Finsupp.induction_linear with
    | zero => simp [freeComp_zero_right, freeTensorHom_zero_left]
    | add β₁ β₂ ih₁ ih₂ =>
      simp only [freeComp_add_right, freeTensorHom_add_left, ih₁, ih₂]
    | single g b =>
      induction α' using Finsupp.induction_linear with
      | zero => simp [freeComp_zero_left, freeTensorHom_zero_right]
      | add α₁' α₂' ih₁ ih₂ =>
        simp only [freeComp_add_left, freeTensorHom_add_right,
                   freeComp_add_left, ih₁, ih₂]
      | single f' a' =>
        induction β' using Finsupp.induction_linear with
        | zero => simp [freeComp_zero_right, freeTensorHom_zero_right]
        | add β₁' β₂' ih₁ ih₂ =>
          simp only [freeComp_add_right, freeTensorHom_add_right,
                     freeComp_add_right, ih₁, ih₂]
        | single g' b' =>
          rw [freeComp_single_single, freeComp_single_single,
              freeTensorHom_single_single, freeTensorHom_single_single,
              freeTensorHom_single_single, freeComp_single_single,
              ← MonoidalCategory.tensorHom_comp_tensorHom]
          congr 1
          ring

/-! ## §4 Object-level monoidal structure (sub-wave 5.10b.2) -/

/--
**Tensor object in `FreeKLinear C k`** is the `of`-image of the underlying C-tensor.
Definitionally `tensorObj X Y = X.unwrap ⊗ Y.unwrap`, since `FreeKLinear C k` is a
type synonym for `C`.
-/
def freeTensorObj (X Y : FreeKLinear C k) : FreeKLinear C k :=
  of (X.unwrap ⊗ Y.unwrap)

omit [CommRing k] in
@[simp]
theorem freeTensorObj_unwrap (X Y : FreeKLinear C k) :
    (freeTensorObj X Y).unwrap = X.unwrap ⊗ Y.unwrap := rfl

/-! ## §5 MonoidalCategoryStruct instance -/

/--
**`MonoidalCategoryStruct (FreeKLinear C k)`**. Object-level tensor + unit are
inherited from C (definitionally via the type synonym). Whiskering and tensor on
morphisms are k-bilinear extensions via `freeTensorHom`. Associator and unitors
are `incl`-lifts of C's structural isomorphisms (each iso component becomes
`Finsupp.single (·) 1`).
-/
noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct (FreeKLinear C k) where
  tensorObj X Y := freeTensorObj X Y
  whiskerLeft X _ _ f := freeTensorHom (freeId (k := k) X.unwrap) f
  whiskerRight {_ _} f Y := freeTensorHom f (freeId (k := k) Y.unwrap)
  tensorHom α β := freeTensorHom α β
  tensorUnit := of (𝟙_ C)
  associator X Y Z :=
    (incl (k := k)).mapIso (α_ X.unwrap Y.unwrap Z.unwrap)
  leftUnitor X := (incl (k := k)).mapIso (λ_ X.unwrap)
  rightUnitor X := (incl (k := k)).mapIso (ρ_ X.unwrap)

/-! ### §5a Unfolding lemmas for the structure -/

@[simp]
theorem instMonoidalCategoryStruct_tensorObj (X Y : FreeKLinear C k) :
    X ⊗ Y = freeTensorObj X Y := rfl

@[simp]
theorem instMonoidalCategoryStruct_tensorUnit :
    (𝟙_ (FreeKLinear C k)) = of (𝟙_ C) := rfl

@[simp]
theorem instMonoidalCategoryStruct_whiskerLeft
    (X : FreeKLinear C k) {Y₁ Y₂ : FreeKLinear C k} (f : Y₁ ⟶ Y₂) :
    X ◁ f = freeTensorHom (freeId (k := k) X.unwrap) f := rfl

@[simp]
theorem instMonoidalCategoryStruct_whiskerRight
    {X₁ X₂ : FreeKLinear C k} (f : X₁ ⟶ X₂) (Y : FreeKLinear C k) :
    f ▷ Y = freeTensorHom f (freeId (k := k) Y.unwrap) := rfl

@[simp]
theorem instMonoidalCategoryStruct_tensorHom
    {X₁ Y₁ X₂ Y₂ : FreeKLinear C k} (α : X₁ ⟶ Y₁) (β : X₂ ⟶ Y₂) :
    α ⊗ₘ β = freeTensorHom α β := rfl

@[simp]
theorem instMonoidalCategoryStruct_associator_hom (X Y Z : FreeKLinear C k) :
    (α_ X Y Z).hom = (Finsupp.single (α_ X.unwrap Y.unwrap Z.unwrap).hom (1 : k)) := rfl

@[simp]
theorem instMonoidalCategoryStruct_associator_inv (X Y Z : FreeKLinear C k) :
    (α_ X Y Z).inv = (Finsupp.single (α_ X.unwrap Y.unwrap Z.unwrap).inv (1 : k)) := rfl

@[simp]
theorem instMonoidalCategoryStruct_leftUnitor_hom (X : FreeKLinear C k) :
    (λ_ X).hom = (Finsupp.single (λ_ X.unwrap).hom (1 : k)) := rfl

@[simp]
theorem instMonoidalCategoryStruct_leftUnitor_inv (X : FreeKLinear C k) :
    (λ_ X).inv = (Finsupp.single (λ_ X.unwrap).inv (1 : k)) := rfl

@[simp]
theorem instMonoidalCategoryStruct_rightUnitor_hom (X : FreeKLinear C k) :
    (ρ_ X).hom = (Finsupp.single (ρ_ X.unwrap).hom (1 : k)) := rfl

@[simp]
theorem instMonoidalCategoryStruct_rightUnitor_inv (X : FreeKLinear C k) :
    (ρ_ X).inv = (Finsupp.single (ρ_ X.unwrap).inv (1 : k)) := rfl

/-! ## §6 MonoidalCategory instance (sub-wave 5.10b.3) -/

/-! ### §6a Easy laws — direct algebra on `freeTensorHom`/`freeComp` -/

/--
**`tensorHom_def`** at the FreeKLinear level: the morphism-side tensor agrees
with the whisker-then-whisker composition. Follows from the §3 interchange law
+ the §1/§2 identity laws.
-/
theorem freeTensorHom_eq_freeComp_whiskering {X₁ Y₁ X₂ Y₂ : C}
    (α : (X₁ ⟶ Y₁) →₀ k) (β : (X₂ ⟶ Y₂) →₀ k) :
    freeTensorHom α β =
      freeComp (freeTensorHom α (freeId X₂)) (freeTensorHom (freeId Y₁) β) := by
  rw [← freeTensorHom_freeComp_interchange, freeComp_id_right, freeComp_id_left]

/--
**Identity tensor identity at the FreeKLinear level.** Direct restatement of
`freeTensorHom_id_id` for the FreeKLinear identity morphism.
-/
theorem freeTensorHom_freeId_freeId (X Y : FreeKLinear C k) :
    freeTensorHom (freeId (k := k) X.unwrap) (freeId (k := k) Y.unwrap) =
      freeId (X.unwrap ⊗ Y.unwrap) :=
  freeTensorHom_id_id (k := k) X.unwrap Y.unwrap

/-! ### §6b Naturality + coherence laws — bilinearity-induction to C -/

/--
**Associator naturality**: `((α ⊗ₘ β) ⊗ₘ γ) ≫ (α_ Y₁ Y₂ Y₃).hom =
(α_ X₁ X₂ X₃).hom ≫ (α ⊗ₘ (β ⊗ₘ γ))` in `FreeKLinear C k`. Triple
bilinearity-induction on α, β, γ; the singleton-singleton-singleton case
reduces via `freeTensorHom_single_single` + C's `associator_naturality` +
multiplicative algebra on coefficients.
-/
theorem freeAssociator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    (α : (X₁ ⟶ Y₁) →₀ k) (β : (X₂ ⟶ Y₂) →₀ k) (γ : (X₃ ⟶ Y₃) →₀ k) :
    freeComp (freeTensorHom (freeTensorHom α β) γ)
             (Finsupp.single (α_ Y₁ Y₂ Y₃).hom (1 : k)) =
      freeComp (Finsupp.single (α_ X₁ X₂ X₃).hom (1 : k))
               (freeTensorHom α (freeTensorHom β γ)) := by
  induction α using Finsupp.induction_linear with
  | zero =>
    simp [freeTensorHom_zero_left, freeComp_zero_left, freeComp_zero_right]
  | add α₁ α₂ ih₁ ih₂ =>
    simp only [freeTensorHom_add_left, freeComp_add_left, freeComp_add_right,
               ih₁, ih₂]
  | single f a =>
    induction β using Finsupp.induction_linear with
    | zero =>
      simp [freeTensorHom_zero_right, freeTensorHom_zero_left,
            freeComp_zero_left, freeComp_zero_right]
    | add β₁ β₂ ih₁ ih₂ =>
      simp only [freeTensorHom_add_right, freeTensorHom_add_left,
                 freeComp_add_left, freeComp_add_right, ih₁, ih₂]
    | single g b =>
      induction γ using Finsupp.induction_linear with
      | zero =>
        simp [freeTensorHom_zero_right, freeComp_zero_left, freeComp_zero_right]
      | add γ₁ γ₂ ih₁ ih₂ =>
        simp only [freeTensorHom_add_right, freeComp_add_left,
                   freeComp_add_right, ih₁, ih₂]
      | single h c =>
        rw [freeTensorHom_single_single, freeTensorHom_single_single,
            freeTensorHom_single_single, freeTensorHom_single_single,
            freeComp_single_single, freeComp_single_single,
            MonoidalCategory.associator_naturality]
        congr 1
        ring

/--
**Left-unitor naturality**: `𝟙_ ◁ α ≫ (λ_ Y).hom = (λ_ X).hom ≫ α` in
`FreeKLinear C k`. Single bilinearity-induction on α; the singleton case reduces
via `freeTensorHom_single_single` + C's `leftUnitor_naturality` + algebra.
-/
theorem freeLeftUnitor_naturality {X Y : C} (α : (X ⟶ Y) →₀ k) :
    freeComp (freeTensorHom (freeId (𝟙_ C)) α)
             (Finsupp.single (λ_ Y).hom (1 : k)) =
      freeComp (Finsupp.single (λ_ X).hom (1 : k)) α := by
  induction α using Finsupp.induction_linear with
  | zero =>
    simp [freeTensorHom_zero_right, freeComp_zero_left, freeComp_zero_right]
  | add α₁ α₂ ih₁ ih₂ =>
    simp only [freeTensorHom_add_right, freeComp_add_left, freeComp_add_right,
               ih₁, ih₂]
  | single f a =>
    unfold freeId
    rw [freeTensorHom_single_single, freeComp_single_single,
        freeComp_single_single, ← MonoidalCategory.leftUnitor_naturality,
        ← MonoidalCategory.id_tensorHom]
    congr 1
    ring

/--
**Right-unitor naturality**: `α ▷ 𝟙_ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ α` in
`FreeKLinear C k`. Single bilinearity-induction on α; the singleton case reduces
via `freeTensorHom_single_single` + C's `rightUnitor_naturality` + algebra.
-/
theorem freeRightUnitor_naturality {X Y : C} (α : (X ⟶ Y) →₀ k) :
    freeComp (freeTensorHom α (freeId (𝟙_ C)))
             (Finsupp.single (ρ_ Y).hom (1 : k)) =
      freeComp (Finsupp.single (ρ_ X).hom (1 : k)) α := by
  induction α using Finsupp.induction_linear with
  | zero =>
    simp [freeTensorHom_zero_left, freeComp_zero_left, freeComp_zero_right]
  | add α₁ α₂ ih₁ ih₂ =>
    simp only [freeTensorHom_add_left, freeComp_add_left, freeComp_add_right,
               ih₁, ih₂]
  | single f a =>
    unfold freeId
    rw [freeTensorHom_single_single, freeComp_single_single,
        freeComp_single_single, ← MonoidalCategory.rightUnitor_naturality,
        ← MonoidalCategory.tensorHom_id]
    congr 1
    ring

/--
**Pentagon law** in `FreeKLinear C k`. Each piece of the pentagon involves
only structural isomorphisms of C lifted as `Finsupp.single (·) 1`; the
identity reduces to C's pentagon + multiplicative collapse `1 * 1 * 1 = 1`.
-/
theorem freePentagon (W X Y Z : C) :
    freeComp (freeTensorHom (Finsupp.single (α_ W X Y).hom (1 : k)) (freeId Z))
             (freeComp (Finsupp.single (α_ W (X ⊗ Y) Z).hom (1 : k))
                       (freeTensorHom (freeId W)
                         (Finsupp.single (α_ X Y Z).hom (1 : k)))) =
      freeComp (Finsupp.single (α_ (W ⊗ X) Y Z).hom (1 : k))
               (Finsupp.single (α_ W X (Y ⊗ Z)).hom (1 : k)) := by
  unfold freeId
  rw [freeTensorHom_single_single, freeTensorHom_single_single,
      freeComp_single_single, freeComp_single_single, freeComp_single_single]
  rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
  congr 1
  · exact MonoidalCategory.pentagon W X Y Z
  · ring

/--
**Triangle law** in `FreeKLinear C k`. The structural isos reduce to
`Finsupp.single (·) 1`; identity follows from C's triangle + `mul_one`/`one_mul`.
-/
theorem freeTriangle (X Y : C) :
    freeComp (Finsupp.single (α_ X (𝟙_ C) Y).hom (1 : k))
             (freeTensorHom (freeId X) (Finsupp.single (λ_ Y).hom (1 : k))) =
      freeTensorHom (Finsupp.single (ρ_ X).hom (1 : k)) (freeId Y) := by
  unfold freeId
  rw [freeTensorHom_single_single, freeTensorHom_single_single,
      freeComp_single_single]
  rw [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id]
  congr 1
  · exact MonoidalCategory.triangle X Y
  · ring

/-! ### §6c Full `MonoidalCategory` instance -/

/--
**`MonoidalCategory (FreeKLinear C k)`**. The full monoidal-category structure
on the free k-linear envelope of a monoidal category `C`. All ten coherence
laws are discharged by §6a/§6b. The naturality laws + pentagon + triangle
ultimately reduce to the corresponding laws in `C` via bilinearity-induction
to the singleton level + multiplicative algebra on coefficients.

Sub-wave 5.10b.3 deliverable. Completes the substrate for `Functor.Monoidal incl`
in 5.10b.4 and Deligne ⊠ proper in 5.10c+.
-/
noncomputable instance instMonoidalCategory : MonoidalCategory (FreeKLinear C k) where
  tensorHom_def α β := freeTensorHom_eq_freeComp_whiskering α β
  id_tensorHom_id X Y := freeTensorHom_freeId_freeId X Y
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ :=
    (freeTensorHom_freeComp_interchange f₁ g₁ f₂ g₂).symm
  whiskerLeft_id X Y := freeTensorHom_id_id (k := k) X.unwrap Y.unwrap
  id_whiskerRight X Y := freeTensorHom_id_id (k := k) X.unwrap Y.unwrap
  associator_naturality f₁ f₂ f₃ := freeAssociator_naturality f₁ f₂ f₃
  leftUnitor_naturality f := freeLeftUnitor_naturality f
  rightUnitor_naturality f := freeRightUnitor_naturality f
  pentagon W X Y Z := freePentagon W.unwrap X.unwrap Y.unwrap Z.unwrap
  triangle X Y := freeTriangle X.unwrap Y.unwrap

/-! ## §7 Inclusion functor monoidal structure (sub-wave 5.10b.4) -/

/--
Reduce `freeTensorHom (incl.map f) (freeId X')` to `incl.map (f ▷ X')`. The
inclusion is `f ↦ Finsupp.single f 1`, so on basis elements this is
`Finsupp.single (f ⊗ₘ 𝟙 X') 1 = Finsupp.single (f ▷ X') 1` by C's
`tensorHom_id`.
-/
theorem freeTensorHom_incl_freeId {X Y X' : C} (f : X ⟶ Y) :
    freeTensorHom (Finsupp.single f (1 : k)) (Finsupp.single (𝟙 X') 1) =
      Finsupp.single (f ▷ X') (1 : k) := by
  rw [freeTensorHom_single_single, MonoidalCategory.tensorHom_id, mul_one]

/--
Reduce `freeTensorHom (freeId X') (incl.map f)` to `incl.map (X' ◁ f)`. Dual to
`freeTensorHom_incl_freeId` — uses C's `id_tensorHom`.
-/
theorem freeTensorHom_freeId_incl {X Y X' : C} (f : X ⟶ Y) :
    freeTensorHom (Finsupp.single (𝟙 X') (1 : k)) (Finsupp.single f 1) =
      Finsupp.single (X' ◁ f) (1 : k) := by
  rw [freeTensorHom_single_single, MonoidalCategory.id_tensorHom, one_mul]

/--
**`Functor.LaxMonoidal incl`**: the inclusion `incl : C ⥤ FreeKLinear C k`
preserves tensor on the nose (since `incl.obj X ⊗ incl.obj Y =
of (X ⊗ Y) = incl.obj (X ⊗ Y)` definitionally), so the laxator `μ X Y` and
unit map `ε` are identity morphisms. Naturality + associativity + unitality
reduce to identity-composition + the fact that whiskering of singletons by
`freeId` recovers C's whiskering via `tensorHom_id` / `id_tensorHom`.
-/
noncomputable instance instInclLaxMonoidal :
    (incl (k := k) (C := C)).LaxMonoidal where
  ε := 𝟙 _
  μ _ _ := 𝟙 _
  μ_natural_left {_ _} f X' := by
    simp [instMonoidalCategoryStruct_whiskerRight, freeId, incl_map,
          freeTensorHom_single_single, MonoidalCategory.tensorHom_id,
          freeTensorObj]
  μ_natural_right {_ _} X' f := by
    simp [instMonoidalCategoryStruct_whiskerLeft, freeId, incl_map,
          freeTensorHom_single_single, MonoidalCategory.id_tensorHom,
          freeTensorObj]
  associativity X Y Z := by
    simp [freeTensorObj, incl_map]
  left_unitality X := by
    simp [freeTensorObj, incl_map]
  right_unitality X := by
    simp [freeTensorObj, incl_map]

/--
**`Functor.OplaxMonoidal incl`**: dual to `LaxMonoidal`; oplaxator `δ X Y`
and counit `η` are identity morphisms (since tensor is preserved on the nose).
-/
noncomputable instance instInclOplaxMonoidal :
    (incl (k := k) (C := C)).OplaxMonoidal where
  η := 𝟙 _
  δ _ _ := 𝟙 _
  δ_natural_left {_ _} f X' := by
    simp [instMonoidalCategoryStruct_whiskerRight, freeId, incl_map,
          freeTensorHom_single_single, MonoidalCategory.tensorHom_id,
          freeTensorObj]
  δ_natural_right {_ _} X' f := by
    simp [instMonoidalCategoryStruct_whiskerLeft, freeId, incl_map,
          freeTensorHom_single_single, MonoidalCategory.id_tensorHom,
          freeTensorObj]
  oplax_associativity X Y Z := by
    simp [freeTensorObj, incl_map]
  oplax_left_unitality X := by
    simp [freeTensorObj, incl_map]
  oplax_right_unitality X := by
    simp [freeTensorObj, incl_map]

/--
**`Functor.Monoidal incl`**: the inclusion is *strong* monoidal — `μ ≫ δ = 𝟙`
and `δ ≫ μ = 𝟙` since both are `𝟙 ≫ 𝟙 = 𝟙`. Same for `ε ≫ η`/`η ≫ ε`.

This is the substrate for transferring monoidal/braided structure from a
k-linear category along the inclusion in Wave 1b.5.10c+ (Deligne ⊠ proper).
-/
noncomputable instance instInclMonoidal :
    (incl (k := k) (C := C)).Monoidal where
  ε_η := Category.id_comp _
  η_ε := Category.id_comp _
  μ_δ _ _ := Category.id_comp _
  δ_μ _ _ := Category.id_comp _

/-! ## §8 Stage 5.10b extended closure -/

end FreeKLinear

/--
**Stage 5.10b partial closure (morphism-side)**. Bundles the morphism-side
infrastructure of the free k-linear monoidal envelope:

1. **Tensor of singletons reduces to C-tensor with multiplied coefficients.**
2. **Identity tensor identity equals the tensor identity.**
3. **Interchange law:** `freeTensorHom` and `freeComp` satisfy the bilinear
   analog of C's `tensor_comp`.

**Partial** because the full `MonoidalCategory (FreeKLinear C k)` instance —
requiring object-level associator/unitor lifts (via `incl.map` of C's
structural isomorphisms), pentagon, triangle, and the various naturality
laws — is deferred to follow-on sub-sessions (5.10b.2/5.10b.3).
-/
theorem stage5_10b_partial_freeTensorHom_closure
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (k : Type) [CommRing k] :
    -- (1) Singleton tensor reduces to C-tensor with multiplied coefficients.
    (∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (a b : k),
      FreeKLinear.freeTensorHom (Finsupp.single f a) (Finsupp.single g b) =
        Finsupp.single (f ⊗ₘ g) (a * b)) ∧
    -- (2) Identity tensor identity equals tensor identity.
    (∀ (X Y : C),
      FreeKLinear.freeTensorHom (FreeKLinear.freeId (k := k) X)
                                (FreeKLinear.freeId (k := k) Y) =
        FreeKLinear.freeId (X ⊗ Y)) ∧
    -- (3) Interchange law.
    (∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
       (α : (X₁ ⟶ Y₁) →₀ k) (β : (Y₁ ⟶ Z₁) →₀ k)
       (α' : (X₂ ⟶ Y₂) →₀ k) (β' : (Y₂ ⟶ Z₂) →₀ k),
      FreeKLinear.freeTensorHom (FreeKLinear.freeComp α β)
                                (FreeKLinear.freeComp α' β') =
        FreeKLinear.freeComp (FreeKLinear.freeTensorHom α α')
                             (FreeKLinear.freeTensorHom β β')) :=
  ⟨fun {_ _ _ _} f g a b => FreeKLinear.freeTensorHom_single_single f g a b,
   fun X Y => FreeKLinear.freeTensorHom_id_id X Y,
   fun {_ _ _ _ _ _} α β α' β' =>
     FreeKLinear.freeTensorHom_freeComp_interchange α β α' β'⟩

/--
**Stage 5.10b extended closure (full).** Bundles the morphism-side
infrastructure (Session 19) + object-level structure + monoidal-category
instance + inclusion's monoidal structure (Session 20) into a single
substantive closure summary for the second sub-wave of Wave 1b.5.10:

1. **Tensor of singletons reduces to C-tensor with multiplied coefficients.**
   (From Session 19.)
2. **Identity tensor identity equals tensor identity.** (From Session 19.)
3. **Interchange law:** `freeTensorHom` and `freeComp` satisfy the bilinear
   analog of C's `tensor_comp`. (From Session 19.)
4. **`MonoidalCategoryStruct (FreeKLinear C k)` is inhabited.** (Session 20
   sub-wave 5.10b.2.)
5. **`MonoidalCategory (FreeKLinear C k)` is inhabited.** All ten coherence
   laws hold; naturality + pentagon + triangle reduce to the corresponding
   laws in C via bilinearity-induction at the singleton level. (Session 20
   sub-wave 5.10b.3.)
6. **`Functor.Monoidal incl` is inhabited.** The inclusion preserves tensor
   on the nose: laxator/oplaxator/unit/counit are all identity morphisms;
   strong-monoidality (μ ≫ δ = 𝟙 etc.) follows from `Category.id_comp`.
   (Session 20 sub-wave 5.10b.4.)

The full chain (5.10a free k-linear envelope + 5.10b free k-linear monoidal
extension) provides the complete substrate for Wave 1b.5.10c+ (Deligne ⊠ as
quotient of `FreeKLinear (C × D) k` by k-bilinear-relations setoid + transferred
monoidal/braided structure).
-/
theorem stage5_10b_freeKLinear_monoidal_closure
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (k : Type) [CommRing k] :
    -- (1)–(3) inherited via stage5_10b_partial_freeTensorHom_closure
    (∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (a b : k),
      FreeKLinear.freeTensorHom (Finsupp.single f a) (Finsupp.single g b) =
        Finsupp.single (f ⊗ₘ g) (a * b)) ∧
    (∀ (X Y : C),
      FreeKLinear.freeTensorHom (FreeKLinear.freeId (k := k) X)
                                (FreeKLinear.freeId (k := k) Y) =
        FreeKLinear.freeId (X ⊗ Y)) ∧
    (∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
       (α : (X₁ ⟶ Y₁) →₀ k) (β : (Y₁ ⟶ Z₁) →₀ k)
       (α' : (X₂ ⟶ Y₂) →₀ k) (β' : (Y₂ ⟶ Z₂) →₀ k),
      FreeKLinear.freeTensorHom (FreeKLinear.freeComp α β)
                                (FreeKLinear.freeComp α' β') =
        FreeKLinear.freeComp (FreeKLinear.freeTensorHom α α')
                             (FreeKLinear.freeTensorHom β β')) ∧
    -- (4) MonoidalCategoryStruct
    Nonempty (MonoidalCategoryStruct (FreeKLinear C k)) ∧
    -- (5) MonoidalCategory
    Nonempty (MonoidalCategory (FreeKLinear C k)) ∧
    -- (6) Functor.Monoidal incl
    Nonempty ((FreeKLinear.incl (k := k) (C := C)).Monoidal) :=
  ⟨fun {_ _ _ _} f g a b => FreeKLinear.freeTensorHom_single_single f g a b,
   fun X Y => FreeKLinear.freeTensorHom_id_id X Y,
   fun {_ _ _ _ _ _} α β α' β' =>
     FreeKLinear.freeTensorHom_freeComp_interchange α β α' β',
   ⟨FreeKLinear.instMonoidalCategoryStruct⟩,
   ⟨FreeKLinear.instMonoidalCategory⟩,
   ⟨FreeKLinear.instInclMonoidal⟩⟩

end SKEFTHawking.SymTFTAudit
