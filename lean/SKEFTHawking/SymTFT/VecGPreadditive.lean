/-
# Phase 6r-prime A5 sub-ship (a) — Preadditive instances on VecG_Cat

This module ships the minimal preadditive substrate on `VecG_Cat k G` =
`GradedObject (Additive G) (ModuleCat k)` needed for A5's object-level
Lagrangian-algebra ship in `Center (VecG_Cat k G2)`:

- `Preadditive (VecG_Cat k G)` — pointwise from `Preadditive (ModuleCat k)`.

Mathlib's `GradedObject β C` is the pi-type `β → C` with pointwise
morphisms; Preadditive transfers pointwise via Pi.addCommGroup. This
is the foundation for the A5 sub-ship (a)-(b) chain.

## Substantive content discipline

The instance is substantive (real Pi-type AddCommGroup transfer), not
a P5 alias. The categorical-algebra ship in A5 sub-ship (b) consumes
this to lift `MonoidalPreadditive` + `HasBinaryBiproducts` to
`Center (VecG_Cat k G2)` via M2 Layer A's `biprodBraidingIso`.

## References

- Mathlib `Mathlib.CategoryTheory.GradedObject` (β → C category structure).
- Mathlib `Mathlib.CategoryTheory.Preadditive.Basic` (Preadditive class).
- Project `lean/SKEFTHawking/DrinfeldCenterBridge.lean:276`
  (`VecG_Cat k G := GradedObject (Additive G) (ModuleCat.{u} k)`).
- Project `lean/SKEFTHawking/VecGMonoidal.lean` (Monoidal + Braided on
  VecG_Cat + Center).
-/
import SKEFTHawking.DrinfeldCenterBridge
import SKEFTHawking.VecGMonoidal
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.GradedObject.Monoidal

namespace SKEFTHawking

open CategoryTheory

universe u

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-- **`VecG_Cat` is preadditive**: pointwise from the preadditive
structure on `ModuleCat k`. `VecG_Cat k G = GradedObject (Additive G)
(ModuleCat k)` has morphisms `∀ g, X g ⟶ Y g`, which carry the pi-type
AddCommGroup via per-degree ModuleCat hom-AddCommGroups. -/
instance instPreadditiveVecGCat :
    Preadditive (VecG_Cat k G) where
  homGroup X Y := by
    show AddCommGroup (∀ g : Additive G, X g ⟶ Y g)
    infer_instance
  add_comp _ _ _ f f' g := by
    funext n
    exact @Preadditive.add_comp _ _ _ _ _ _ (f n) (f' n) (g n)
  comp_add _ _ _ f g g' := by
    funext n
    exact @Preadditive.comp_add _ _ _ _ _ _ (f n) (g n) (g' n)

/-! ## §2. HasBinaryBiproducts (VecG_Cat k G)

Pointwise via Mathlib's `hasBinaryBiproduct_of_total` for preadditive
categories. The binary biproduct of `X, Y : VecG_Cat k G` is the pointwise
direct sum `(X ⊞ Y) g := X g ⊞ Y g` in `ModuleCat k`. -/

open Limits

/-- **Pointwise binary bicone on `VecG_Cat`** for `X, Y : VecG_Cat k G`.
At each grade `b : Additive G`, the bicone is the canonical biproduct
bicone on `X b` and `Y b` in `ModuleCat k`. -/
@[simps]
noncomputable def vecGPointwiseBinaryBicone (X Y : VecG_Cat k G) :
    BinaryBicone X Y where
  pt b := X b ⊞ Y b
  fst b := biprod.fst
  snd b := biprod.snd
  inl b := biprod.inl
  inr b := biprod.inr
  inl_fst := by funext b; simp
  inl_snd := by funext b; simp
  inr_fst := by funext b; simp
  inr_snd := by funext b; simp

/-- **Total equation for the pointwise binary bicone**: at each grade
`b : Additive G`, the total relation `fst ≫ inl + snd ≫ inr = 𝟙` reduces to
`biprod.total` in `ModuleCat k`. -/
lemma vecGPointwiseBinaryBicone_total (X Y : VecG_Cat k G) :
    (vecGPointwiseBinaryBicone k G X Y).fst ≫ (vecGPointwiseBinaryBicone k G X Y).inl +
        (vecGPointwiseBinaryBicone k G X Y).snd ≫ (vecGPointwiseBinaryBicone k G X Y).inr =
      𝟙 (vecGPointwiseBinaryBicone k G X Y).pt := by
  funext b
  show biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X b ⊞ Y b)
  exact biprod.total

/-- **Per-pair `HasBinaryBiproduct` on `VecG_Cat`** via the pointwise
binary bicone + Mathlib's `hasBinaryBiproduct_of_total`. -/
noncomputable instance instHasBinaryBiproductVecGCat (X Y : VecG_Cat k G) :
    HasBinaryBiproduct X Y :=
  hasBinaryBiproduct_of_total (vecGPointwiseBinaryBicone k G X Y)
    (vecGPointwiseBinaryBicone_total k G X Y)

/-- **`HasBinaryBiproducts` on `VecG_Cat`** — pointwise via per-grade
ModuleCat biproducts. Closes A5 sub-ship (a) part 2. -/
noncomputable instance instHasBinaryBiproductsVecGCat :
    HasBinaryBiproducts (VecG_Cat k G) where
  has_binary_biproduct _ _ := inferInstance

/-! ## §3. MonoidalPreadditive (VecG_Cat k G)

Tensor-on-morphisms is additive in both factors because the Day-convolution
tensor on `GradedObject` is built from `mapBifunctorMapMap` over the bilinear
`tensor : ModuleCat × ModuleCat → ModuleCat` plus colimits, and both
constructions preserve additivity.

Requires the monoidal structure from `VecGMonoidal`, hence the additional
`[Fintype G] [DecidableEq G]` requirements. -/

section MonoidalPreadditiveSection

variable [Fintype G] [DecidableEq G]

open MonoidalCategory

/-- **`MonoidalPreadditive (VecG_Cat k G)`** — substantive Day-convolution
additivity-of-tensor instance. Per-grade `ext` via `mapBifunctorMapObj_ext`
reduces each whisker equation to additivity of the underlying ModuleCat
tensor bifunctor, which holds since `ModuleCat k` is `MonoidalPreadditive`
(equivalently: `tensorLeft X` is an additive functor).

Closes A5 sub-ship (a) part 3. -/
noncomputable instance instMonoidalPreadditiveVecGCat :
    MonoidalPreadditive (VecG_Cat k G) where
  whiskerLeft_zero {X Y Z} := by
    funext n
    apply GradedObject.mapBifunctorMapObj_ext
    intro i j h
    show GradedObject.ιMapBifunctorMapObj _ _ X Y i j n h ≫
        GradedObject.Monoidal.whiskerLeft X (0 : Y ⟶ Z) n = _
    rw [GradedObject.Monoidal.whiskerLeft, GradedObject.Monoidal.tensorHom,
      GradedObject.ι_mapBifunctorMapMap]
    show _ = _ ≫ 0
    show _ ≫ ((curriedTensor (ModuleCat k)).obj (X i)).map 0 ≫ _ = _
    rw [Functor.map_zero, Limits.zero_comp, Limits.comp_zero, Limits.comp_zero]
  zero_whiskerRight {X Y Z} := by
    funext n
    apply GradedObject.mapBifunctorMapObj_ext
    intro i j h
    show GradedObject.ιMapBifunctorMapObj _ _ Y X i j n h ≫
        GradedObject.Monoidal.whiskerRight (0 : Y ⟶ Z) X n = _
    rw [GradedObject.Monoidal.whiskerRight, GradedObject.Monoidal.tensorHom,
      GradedObject.ι_mapBifunctorMapMap]
    show _ = _ ≫ 0
    show ((curriedTensor (ModuleCat k)).map 0).app (X j) ≫ _ = _
    rw [Functor.map_zero, NatTrans.app_zero, Limits.zero_comp, Limits.comp_zero]
  whiskerLeft_add {X Y Z} f g := by
    funext n
    apply GradedObject.mapBifunctorMapObj_ext
    intro i j h
    show GradedObject.ιMapBifunctorMapObj _ _ X Y i j n h ≫
        GradedObject.Monoidal.whiskerLeft X (f + g) n =
      GradedObject.ιMapBifunctorMapObj _ _ X Y i j n h ≫
        (GradedObject.Monoidal.whiskerLeft X f + GradedObject.Monoidal.whiskerLeft X g) n
    rw [GradedObject.Monoidal.whiskerLeft, GradedObject.Monoidal.tensorHom,
      GradedObject.ι_mapBifunctorMapMap]
    have hfg : (f + g) j = f j + g j := rfl
    rw [hfg, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
    show _ + _ = GradedObject.ιMapBifunctorMapObj _ _ X Y i j n h ≫
      (GradedObject.Monoidal.whiskerLeft X f n + GradedObject.Monoidal.whiskerLeft X g n)
    rw [Preadditive.comp_add]
    congr 1 <;>
      rw [GradedObject.Monoidal.whiskerLeft, GradedObject.Monoidal.tensorHom,
        GradedObject.ι_mapBifunctorMapMap]
  add_whiskerRight {X Y Z} f g := by
    funext n
    apply GradedObject.mapBifunctorMapObj_ext
    intro i j h
    show GradedObject.ιMapBifunctorMapObj _ _ Y X i j n h ≫
        GradedObject.Monoidal.whiskerRight (f + g) X n =
      GradedObject.ιMapBifunctorMapObj _ _ Y X i j n h ≫
        (GradedObject.Monoidal.whiskerRight f X + GradedObject.Monoidal.whiskerRight g X) n
    rw [GradedObject.Monoidal.whiskerRight, GradedObject.Monoidal.tensorHom,
      GradedObject.ι_mapBifunctorMapMap]
    have hfg : (f + g) i = f i + g i := rfl
    rw [hfg, Functor.map_add, NatTrans.app_add, Preadditive.add_comp]
    show _ + _ = GradedObject.ιMapBifunctorMapObj _ _ Y X i j n h ≫
      (GradedObject.Monoidal.whiskerRight f X n + GradedObject.Monoidal.whiskerRight g X n)
    rw [Preadditive.comp_add]
    congr 1 <;>
      rw [GradedObject.Monoidal.whiskerRight, GradedObject.Monoidal.tensorHom,
        GradedObject.ι_mapBifunctorMapMap]

end MonoidalPreadditiveSection

end SKEFTHawking
