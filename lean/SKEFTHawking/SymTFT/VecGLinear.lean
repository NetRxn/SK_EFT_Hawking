/-
# `k`-linear structure on `VecG_Cat k G` — the scalar prelude for normalized Frobenius data

`VecGPreadditive` ships `Preadditive (VecG_Cat k G)` + `MonoidalPreadditive (VecG_Cat k G)`,
which give the hom-sets an `AddCommGroup` and make whiskering additive. That is enough for
`ℤ`-scalars (`𝟙 + 𝟙 = (2 : ℤ) • 𝟙`) but NOT enough to **divide by 2** — which is exactly what
the separability normalization of a Frobenius algebra needs (`Δ′ = ½ • Δ`, Kock 2004 §2.4).

This module ships the missing `k`-scalar layer:

* **`instLinearVecGCat`** — `Linear k (VecG_Cat k G)`: each hom-set `∀ g, X g ⟶ Y g` is a
  `k`-module (pointwise from `Linear k (ModuleCat k)`), and composition is `k`-bilinear.
* **`instMonoidalLinearVecGCat`** — `MonoidalLinear k (VecG_Cat k G)`: whiskering is
  `k`-linear, i.e. `X ◁ (r • f) = r • (X ◁ f)` and `(r • f) ▷ X = r • (f ▷ X)`. This is the
  exact `k`-analogue of `instMonoidalPreadditiveVecGCat`'s `whiskerLeft_add` /
  `add_whiskerRight`, proved by the same Day-convolution per-grade route
  (`mapBifunctorMapObj_ext` + `ι_mapBifunctorMapMap`), with `MonoidalLinear k (ModuleCat k)`
  supplying the per-grade scalar pull-through.

`MonoidalLinear` is what lets the scalar action descend to the Drinfeld center: a scaled
morphism `r • f` still satisfies the half-braiding compatibility condition precisely because
whiskering commutes with `•` (see `SymTFT/CenterLinear.lean`).

## References

- Mathlib `Mathlib.CategoryTheory.Linear.Basic` (`Linear` class).
- Mathlib `Mathlib.CategoryTheory.Monoidal.Linear` (`MonoidalLinear` class).
- Mathlib `Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic`
  (`MonoidalLinear R (ModuleCat R)`).
- Project `lean/SKEFTHawking/SymTFT/VecGPreadditive.lean` (the additive predecessor).
-/
import SKEFTHawking.SymTFT.VecGPreadditive
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

namespace SKEFTHawking

open CategoryTheory

universe u

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-! ## §1. `Linear k (VecG_Cat k G)` -/

/-- **`VecG_Cat` is `k`-linear**: pointwise from `Linear k (ModuleCat k)`. Morphisms are
`∀ g : Additive G, X g ⟶ Y g`, which carries the pi-type `k`-module structure from the
per-degree `ModuleCat` hom-modules; composition is `k`-bilinear grade by grade. -/
instance instLinearVecGCat : Linear k (VecG_Cat k G) where
  homModule X Y := by
    show Module k (∀ g : Additive G, X g ⟶ Y g)
    infer_instance
  smul_comp _ _ _ r f g := by
    funext n
    exact Linear.smul_comp _ _ _ r (f n) (g n)
  comp_smul _ _ _ f r g := by
    funext n
    exact Linear.comp_smul _ _ _ (f n) r (g n)

/-! ## §2. `MonoidalLinear k (VecG_Cat k G)` -/

section MonoidalLinearSection

variable [Fintype G] [DecidableEq G]

open MonoidalCategory

/-- Scalars pull out of post-composition in `ModuleCat k`, in the shape `rw` can match against
the Day-convolution insertions (the bare `Linear.smul_comp` pattern does not fire there — its
`Module` instance argument is a metavariable that unifies to a different, though defeq, path).
Stated with the ambient `ModuleCat` hom-modules so the rewrite is syntactic. -/
private theorem moduleCat_smul_comp {k : Type u} [CommRing k] (r : k)
    {A B D : ModuleCat k} (g : A ⟶ B) (g' : B ⟶ D) :
    (r • g) ≫ g' = r • (g ≫ g') := Linear.smul_comp _ _ _ r g g'

/-- Scalars pull out of pre-composition in `ModuleCat k` — the mirror of
`moduleCat_smul_comp`. -/
private theorem moduleCat_comp_smul {k : Type u} [CommRing k] (r : k)
    {A B D : ModuleCat k} (g : A ⟶ B) (g' : B ⟶ D) :
    g ≫ (r • g') = r • (g ≫ g') := Linear.comp_smul _ _ _ g r g'

/-- **`MonoidalLinear k (VecG_Cat k G)`** — the Day-convolution tensor is `k`-linear in each
factor. Per-grade `ext` via `mapBifunctorMapObj_ext` reduces each whisker equation to the
`ModuleCat k` statement `X ◁ (r • f) = r • (X ◁ f)` / `(r • f) ▷ X = r • (f ▷ X)`, supplied by
Mathlib's `MonoidalLinear k (ModuleCat k)`; `moduleCat_smul_comp` / `moduleCat_comp_smul` move
the scalar past the structural insertion `ι`. This is the scalar counterpart of
`instMonoidalPreadditiveVecGCat`. -/
instance instMonoidalLinearVecGCat : MonoidalLinear k (VecG_Cat k G) where
  whiskerLeft_smul X {Y Z} r f := by
    funext n
    apply GradedObject.mapBifunctorMapObj_ext
    intro i j h
    show GradedObject.ιMapBifunctorMapObj _ _ X Y i j n h ≫
        GradedObject.Monoidal.whiskerLeft X (r • f) n =
      GradedObject.ιMapBifunctorMapObj _ _ X Y i j n h ≫
        (r • GradedObject.Monoidal.whiskerLeft X f) n
    rw [GradedObject.Monoidal.whiskerLeft, GradedObject.Monoidal.tensorHom,
      GradedObject.ι_mapBifunctorMapMap]
    have key : ∀ (A : ModuleCat k) {Y' Z' : ModuleCat k} (g : Y' ⟶ Z'),
        ((curriedTensor (ModuleCat k)).obj A).map (r • g) =
          r • (((curriedTensor (ModuleCat k)).obj A).map g) := by
      intro A Y' Z' g; exact MonoidalLinear.whiskerLeft_smul A r g
    rw [show (r • f) j = r • f j from rfl, key, moduleCat_smul_comp r, moduleCat_comp_smul r]
    show r • _ = GradedObject.ιMapBifunctorMapObj _ _ X Y i j n h ≫
      (r • GradedObject.Monoidal.whiskerLeft X f n)
    rw [moduleCat_comp_smul r]
    congr 1
    rw [GradedObject.Monoidal.whiskerLeft, GradedObject.Monoidal.tensorHom,
      GradedObject.ι_mapBifunctorMapMap]
  smul_whiskerRight r {Y Z} f X := by
    funext n
    apply GradedObject.mapBifunctorMapObj_ext
    intro i j h
    show GradedObject.ιMapBifunctorMapObj _ _ Y X i j n h ≫
        GradedObject.Monoidal.whiskerRight (r • f) X n =
      GradedObject.ιMapBifunctorMapObj _ _ Y X i j n h ≫
        (r • GradedObject.Monoidal.whiskerRight f X) n
    rw [GradedObject.Monoidal.whiskerRight, GradedObject.Monoidal.tensorHom,
      GradedObject.ι_mapBifunctorMapMap]
    have key : ∀ {Y' Z' : ModuleCat k} (g : Y' ⟶ Z') (A : ModuleCat k),
        ((curriedTensor (ModuleCat k)).map (r • g)).app A =
          r • (((curriedTensor (ModuleCat k)).map g).app A) := by
      intro Y' Z' g A; exact MonoidalLinear.smul_whiskerRight r g A
    rw [show (r • f) i = r • f i from rfl, key, moduleCat_smul_comp r]
    show r • _ = GradedObject.ιMapBifunctorMapObj _ _ Y X i j n h ≫
      (r • GradedObject.Monoidal.whiskerRight f X n)
    rw [moduleCat_comp_smul]
    congr 1
    rw [GradedObject.Monoidal.whiskerRight, GradedObject.Monoidal.tensorHom,
      GradedObject.ι_mapBifunctorMapMap]

end MonoidalLinearSection

end SKEFTHawking
