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

/-! ## §4 Stage 5.10b partial closure -/

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

end SKEFTHawking.SymTFTAudit
