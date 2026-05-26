/-
# Phase 6r-prime A5 sub-ship (b) — Preadditive on Drinfeld Center

This module ships the substantive **`Preadditive (Center C)`** instance
for any `C : Type u` satisfying:

```
[Category C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
```

The hom-AddCommGroup on `Center.Hom X Y` is built by lifting the
AddCommGroup on `X.1 ⟶ Y.1` through the half-braiding compatibility
condition: if `f.comm` and `g.comm` both hold for the underlying
morphisms `f.f` and `g.f`, then `(f + g).f := f.f + g.f` also satisfies
the comm condition because:

- `((f.f + g.f) ▷ U) ≫ Y.2.β U = X.2.β U ≫ U ◁ (f.f + g.f)`

follows from `MonoidalPreadditive.add_whiskerRight + whiskerLeft_add`
together with `Preadditive.add_comp + comp_add` on the right-hand side
of each component's comm equation.

## Substantive content

This is substantive content (the entire half-braiding compatibility
lift), not a P5 alias. It is required to ship `HasBinaryBiproducts
(Center C)` (the A5 sub-ship (a) Layer 2 follow-on) substantively via
M2 Layer A's `biprodBraidingIso`.

## Phase 6r-prime A5 sub-ship (b) ship

Closes the deferral in `SymTFT/CenterBiproducts.lean` (`HasBinaryBiproducts
(Center C)` cannot be constructed without `Preadditive (Center C)`). The
ship here applies generally to any preadditive monoidal `C`, not just
`VecG_Cat k G`.

## References

- Mathlib `Mathlib.CategoryTheory.Monoidal.Center` (Center.Hom +
  half-braiding compatibility).
- Mathlib `Mathlib.CategoryTheory.Monoidal.Preadditive`
  (MonoidalPreadditive.add_whiskerRight + whiskerLeft_add).
- Mathlib `Mathlib.CategoryTheory.Preadditive.Basic` (Preadditive class).
-/
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Basic

namespace SKEFTHawking.SymTFT

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [MonoidalPreadditive C]

namespace CenterPreadditive

/-! ## §0. Negation lemmas for whiskering

Derived from `MonoidalPreadditive.whiskerLeft_add + zero_whiskerRight`
via the AddCommGroup negation characterization `-a + a = 0`. -/

/-- **Whiskering on the right distributes over negation**: `(-f) ▷ U = -(f ▷ U)`. -/
lemma neg_whiskerRight {X Y : C} (f : X ⟶ Y) (U : C) :
    (-f) ▷ U = -(f ▷ U) := by
  rw [eq_neg_iff_add_eq_zero, ← MonoidalPreadditive.add_whiskerRight,
    neg_add_cancel, MonoidalPreadditive.zero_whiskerRight]

/-- **Whiskering on the left distributes over negation**: `U ◁ (-f) = -(U ◁ f)`. -/
lemma whiskerLeft_neg (U : C) {X Y : C} (f : X ⟶ Y) :
    U ◁ (-f) = -(U ◁ f) := by
  rw [eq_neg_iff_add_eq_zero, ← MonoidalPreadditive.whiskerLeft_add,
    neg_add_cancel, MonoidalPreadditive.whiskerLeft_zero]

/-! ## §1. Addition on Center morphisms

For `f, g : Center.Hom X Y`, define `f + g` by `(f + g).f := f.f + g.f`.
The half-braiding compatibility carries through via `add_whiskerRight`
+ `whiskerLeft_add`. -/

/-- **Addition of Center morphisms** lifting AddCommGroup on the
underlying `X.1 ⟶ Y.1`. Half-braiding compat preserved by
`MonoidalPreadditive`-style additivity of whiskering. -/
def addHom {X Y : CategoryTheory.Center C} (f g : X ⟶ Y) : X ⟶ Y where
  f := f.f + g.f
  comm U := by
    rw [MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp,
      MonoidalPreadditive.whiskerLeft_add, Preadditive.comp_add,
      f.comm, g.comm]

/-- **Zero Center morphism**: `.f := 0`. -/
def zeroHom (X Y : CategoryTheory.Center C) : X ⟶ Y where
  f := 0
  comm U := by
    rw [MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp,
      MonoidalPreadditive.whiskerLeft_zero, Limits.comp_zero]

/-- **Negation of Center morphism**: `.f := -f.f`. -/
def negHom {X Y : CategoryTheory.Center C} (f : X ⟶ Y) : X ⟶ Y where
  f := -f.f
  comm U := by
    have h := f.comm U
    rw [neg_whiskerRight, Preadditive.neg_comp, whiskerLeft_neg,
      Preadditive.comp_neg, h]

/-- **Subtraction of Center morphisms**: `.f := f.f - g.f`. -/
def subHom {X Y : CategoryTheory.Center C} (f g : X ⟶ Y) : X ⟶ Y where
  f := f.f - g.f
  comm U := by
    rw [show f.f - g.f = f.f + (-g.f) from sub_eq_add_neg _ _,
      MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp,
      MonoidalPreadditive.whiskerLeft_add, Preadditive.comp_add,
      neg_whiskerRight, Preadditive.neg_comp, whiskerLeft_neg,
      Preadditive.comp_neg, f.comm, g.comm]

/-- **Natural-number scalar multiplication of Center morphisms**. -/
def nsmulHom {X Y : CategoryTheory.Center C} (n : ℕ) (f : X ⟶ Y) : X ⟶ Y :=
  Nat.recAux (zeroHom X Y) (fun _ rec => addHom rec f) n

/-- **Integer scalar multiplication of Center morphisms**. -/
def zsmulHom {X Y : CategoryTheory.Center C} (n : ℤ) (f : X ⟶ Y) : X ⟶ Y :=
  match n with
  | Int.ofNat k => nsmulHom k f
  | Int.negSucc k => negHom (nsmulHom (k + 1) f)

end CenterPreadditive

/-! ## §2. AddCommGroup instance on Center.Hom

All AddCommGroup laws follow via the `.f` projection from the underlying
AddCommGroup on `X.1 ⟶ Y.1`. We provide all atomic instances (Add, Zero,
Neg, Sub, SMul ℕ, SMul ℤ) explicitly via the `CenterPreadditive.*Hom`
constructors, with each component projection being `rfl`. Then
`Function.Injective.addCommGroup` lifts the full AddCommGroup laws. -/

noncomputable instance instAddCenterHom (X Y : CategoryTheory.Center C) :
    Add (X ⟶ Y) := ⟨CenterPreadditive.addHom⟩

noncomputable instance instZeroCenterHom (X Y : CategoryTheory.Center C) :
    Zero (X ⟶ Y) := ⟨CenterPreadditive.zeroHom X Y⟩

noncomputable instance instNegCenterHom (X Y : CategoryTheory.Center C) :
    Neg (X ⟶ Y) := ⟨CenterPreadditive.negHom⟩

noncomputable instance instSubCenterHom (X Y : CategoryTheory.Center C) :
    Sub (X ⟶ Y) := ⟨CenterPreadditive.subHom⟩

noncomputable instance instSMulNatCenterHom (X Y : CategoryTheory.Center C) :
    SMul ℕ (X ⟶ Y) := ⟨CenterPreadditive.nsmulHom⟩

noncomputable instance instSMulIntCenterHom (X Y : CategoryTheory.Center C) :
    SMul ℤ (X ⟶ Y) := ⟨CenterPreadditive.zsmulHom⟩

@[simp] lemma center_hom_add_f {X Y : CategoryTheory.Center C} (f g : X ⟶ Y) :
    (f + g).f = f.f + g.f := rfl

@[simp] lemma center_hom_zero_f (X Y : CategoryTheory.Center C) :
    (0 : X ⟶ Y).f = 0 := rfl

@[simp] lemma center_hom_neg_f {X Y : CategoryTheory.Center C} (f : X ⟶ Y) :
    (-f).f = -f.f := rfl

@[simp] lemma center_hom_sub_f {X Y : CategoryTheory.Center C} (f g : X ⟶ Y) :
    (f - g).f = f.f - g.f := rfl

@[simp] lemma center_hom_nsmul_f {X Y : CategoryTheory.Center C} (n : ℕ) (f : X ⟶ Y) :
    (n • f).f = n • f.f := by
  show (CenterPreadditive.nsmulHom n f).f = n • f.f
  induction n with
  | zero => show (CenterPreadditive.zeroHom X Y).f = 0 • f.f
            rw [zero_smul]; rfl
  | succ k ih =>
    show (CenterPreadditive.addHom (CenterPreadditive.nsmulHom k f) f).f = (k + 1) • f.f
    show (CenterPreadditive.nsmulHom k f).f + f.f = (k + 1) • f.f
    rw [ih, succ_nsmul]

@[simp] lemma center_hom_zsmul_f {X Y : CategoryTheory.Center C} (n : ℤ) (f : X ⟶ Y) :
    (n • f).f = n • f.f := by
  show (CenterPreadditive.zsmulHom n f).f = n • f.f
  cases n with
  | ofNat k => show (CenterPreadditive.nsmulHom k f).f = (Int.ofNat k) • f.f
               have := center_hom_nsmul_f k f
               show (CenterPreadditive.nsmulHom k f).f = (Int.ofNat k) • f.f
               rw [(show (k • f).f = (CenterPreadditive.nsmulHom k f).f from rfl).symm,
                 center_hom_nsmul_f]
               exact (natCast_zsmul f.f k).symm
  | negSucc k => show (CenterPreadditive.negHom (CenterPreadditive.nsmulHom (k + 1) f)).f =
                   (Int.negSucc k) • f.f
                 show -(CenterPreadditive.nsmulHom (k + 1) f).f = (Int.negSucc k) • f.f
                 rw [(show ((k + 1 : ℕ) • f).f = (CenterPreadditive.nsmulHom (k + 1) f).f from rfl).symm,
                   center_hom_nsmul_f]
                 rw [show (Int.negSucc k) = -(k + 1 : ℤ) from rfl, neg_zsmul]
                 congr 1
                 exact (natCast_zsmul f.f (k + 1)).symm

noncomputable instance instAddCommGroupCenterHom (X Y : CategoryTheory.Center C) :
    AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup
    (fun (f : X ⟶ Y) => f.f)
    (fun f g h => by apply CategoryTheory.Center.ext; exact h)
    rfl
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => center_hom_nsmul_f _ _)
    (fun _ _ => center_hom_zsmul_f _ _)

/-! ## §3. Preadditive instance on Center

Composition is bilinear because composition on the underlying
`X.1 ⟶ Y.1` is bilinear (`Preadditive C`), and Center composition is
`(f ≫ g).f = f.f ≫ g.f`. -/

noncomputable instance instPreadditiveCenter : Preadditive (CategoryTheory.Center C) where
  homGroup X Y := instAddCommGroupCenterHom X Y
  add_comp X Y Z f f' g := by
    apply CategoryTheory.Center.ext
    show (f.f + f'.f) ≫ g.f = f.f ≫ g.f + f'.f ≫ g.f
    exact Preadditive.add_comp _ _ _ _ _ _
  comp_add X Y Z f g g' := by
    apply CategoryTheory.Center.ext
    show f.f ≫ (g.f + g'.f) = f.f ≫ g.f + f.f ≫ g'.f
    exact Preadditive.comp_add _ _ _ _ _ _

end SKEFTHawking.SymTFT
