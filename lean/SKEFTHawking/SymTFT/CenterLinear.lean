/-
# `R`-linear structure on the Drinfeld center — the scalar layer above `CenterPreadditive`

`CenterPreadditive` lifts the hom-`AddCommGroup` of `C` to `Center C` through the
half-braiding compatibility condition. That gives `ℤ`-scalars only. Normalizing a Frobenius
algebra to a **separable** one (`Δ′ = ½ • Δ`, Kock 2004 §2.4) needs genuine `R`-scalars, so
this module lifts the scalar action the same way:

* **`instMonoidalPreadditiveCenter`** — `MonoidalPreadditive (Center C)` (whiskering in the
  center is additive because it is computed on underlying morphisms). This is the prerequisite
  of `MonoidalLinear` and also subsumes the hand-rolled `center_zero_whiskerRight` /
  `center_whiskerLeft_zero` lemmas in `ElectricAlgebraObject`.
* **`instLinearCenter`** — `Linear R (Center C)`: `(r • f).f := r • f.f`. The half-braiding
  compatibility survives scaling **precisely because whiskering is `R`-linear**
  (`MonoidalLinear R C`); this is the one place the hypothesis is load-bearing.
* **`instMonoidalLinearCenter`** — `MonoidalLinear R (Center C)`, again computed on
  underlying morphisms. Needed to push a scalar through `X ◁ (r • f)` / `(r • f) ▷ X` inside
  the center, which is exactly what transporting the Frobenius laws across a rescaled
  comultiplication requires.

## Substantive content

The scaling-preserves-half-braiding argument is the substantive content: for `f : X ⟶ Y` in
`Center C` with `f.comm U : (f.f ▷ U) ≫ Y.2.β U = X.2.β U ≫ (U ◁ f.f)`, the scaled morphism
satisfies

```
((r • f.f) ▷ U) ≫ Y.2.β U = r • ((f.f ▷ U) ≫ Y.2.β U)
                          = r • (X.2.β U ≫ (U ◁ f.f)) = X.2.β U ≫ (U ◁ (r • f.f))
```

using `MonoidalLinear.smul_whiskerRight`, `Linear.smul_comp`, `Linear.comp_smul` and
`MonoidalLinear.whiskerLeft_smul`. Without `MonoidalLinear R C` the first and last steps fail
and the scalar action does **not** descend to the center.

## References

- Mathlib `Mathlib.CategoryTheory.Monoidal.Center` (`Center.Hom` + half-braiding compat).
- Mathlib `Mathlib.CategoryTheory.Linear.Basic`, `Mathlib.CategoryTheory.Monoidal.Linear`.
- Project `lean/SKEFTHawking/SymTFT/CenterPreadditive.lean` (the additive predecessor).
-/
import SKEFTHawking.SymTFT.CenterPreadditive
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear

namespace SKEFTHawking.SymTFT

open CategoryTheory MonoidalCategory

universe w v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [MonoidalPreadditive C]

/-! ## §1. `MonoidalPreadditive (Center C)` — the prerequisite -/

/-- **Whiskering in the Drinfeld center is additive**, because it is computed on underlying
morphisms and `C` is `MonoidalPreadditive`. Prerequisite for `MonoidalLinear R (Center C)`. -/
noncomputable instance instMonoidalPreadditiveCenter :
    MonoidalPreadditive (CategoryTheory.Center C) where
  whiskerLeft_zero {X Y Z} := by
    apply CategoryTheory.Center.ext
    show X.1 ◁ (0 : Y.1 ⟶ Z.1) = 0
    exact MonoidalPreadditive.whiskerLeft_zero
  zero_whiskerRight {X Y Z} := by
    apply CategoryTheory.Center.ext
    show (0 : Y.1 ⟶ Z.1) ▷ X.1 = 0
    exact MonoidalPreadditive.zero_whiskerRight
  whiskerLeft_add {X Y Z} f g := by
    apply CategoryTheory.Center.ext
    show X.1 ◁ (f.f + g.f) = X.1 ◁ f.f + X.1 ◁ g.f
    exact MonoidalPreadditive.whiskerLeft_add _ _
  add_whiskerRight {X Y Z} f g := by
    apply CategoryTheory.Center.ext
    show (f.f + g.f) ▷ X.1 = f.f ▷ X.1 + g.f ▷ X.1
    exact MonoidalPreadditive.add_whiskerRight _ _

/-! ## §2. The scalar action on center morphisms -/

variable (R : Type w) [Semiring R] [Linear R C] [MonoidalLinear R C]

namespace CenterLinear

/-- **Scalar multiple of a center morphism**: `(r • f).f := r • f.f`. The half-braiding
compatibility is preserved because whiskering is `R`-linear (`MonoidalLinear R C`) — the
substantive content of this module. -/
def smulHom {X Y : CategoryTheory.Center C} (r : R) (f : X ⟶ Y) : X ⟶ Y where
  f := r • f.f
  comm U := by
    rw [MonoidalLinear.smul_whiskerRight, Linear.smul_comp,
      MonoidalLinear.whiskerLeft_smul, Linear.comp_smul, f.comm]

end CenterLinear

noncomputable instance instSMulCenterHom (X Y : CategoryTheory.Center C) :
    SMul R (X ⟶ Y) := ⟨CenterLinear.smulHom R⟩

@[simp] lemma center_hom_smul_f {X Y : CategoryTheory.Center C} (r : R) (f : X ⟶ Y) :
    (r • f).f = r • f.f := rfl

/-- The `R`-module structure on a center hom-set: every axiom is checked on the underlying
morphism via `Center.ext`, where it is the corresponding `Module R (X.1 ⟶ Y.1)` axiom. -/
noncomputable instance instModuleCenterHom (X Y : CategoryTheory.Center C) :
    Module R (X ⟶ Y) where
  one_smul f := by
    apply CategoryTheory.Center.ext
    show (1 : R) • f.f = f.f
    exact one_smul R f.f
  mul_smul r s f := by
    apply CategoryTheory.Center.ext
    show (r * s) • f.f = r • s • f.f
    exact mul_smul r s f.f
  smul_zero r := by
    apply CategoryTheory.Center.ext
    show r • (0 : X.1 ⟶ Y.1) = 0
    exact smul_zero r
  smul_add r f g := by
    apply CategoryTheory.Center.ext
    show r • (f.f + g.f) = r • f.f + r • g.f
    exact smul_add r f.f g.f
  add_smul r s f := by
    apply CategoryTheory.Center.ext
    show (r + s) • f.f = r • f.f + s • f.f
    exact add_smul r s f.f
  zero_smul f := by
    apply CategoryTheory.Center.ext
    show (0 : R) • f.f = 0
    exact zero_smul R f.f

/-! ## §3. `Linear R (Center C)` and `MonoidalLinear R (Center C)` -/

/-- **The Drinfeld center is `R`-linear** whenever `C` is `R`-linear and monoidally
`R`-linear. Composition is `R`-bilinear because it is computed on underlying morphisms. -/
noncomputable instance instLinearCenter : Linear R (CategoryTheory.Center C) where
  homModule X Y := instModuleCenterHom R X Y
  smul_comp X Y Z r f g := by
    apply CategoryTheory.Center.ext
    show (r • f.f) ≫ g.f = r • (f.f ≫ g.f)
    exact Linear.smul_comp _ _ _ r _ _
  comp_smul X Y Z f r g := by
    apply CategoryTheory.Center.ext
    show f.f ≫ (r • g.f) = r • (f.f ≫ g.f)
    exact Linear.comp_smul _ _ _ _ r _

/-- **Whiskering in the Drinfeld center is `R`-linear** — computed on underlying morphisms.
This is what lets a rescaled comultiplication `r • Δ` be pushed through `X ◁ (-)` and
`(-) ▷ X` when transporting Frobenius compatibility to a normalized structure. -/
noncomputable instance instMonoidalLinearCenter :
    MonoidalLinear R (CategoryTheory.Center C) where
  whiskerLeft_smul X {Y Z} r f := by
    apply CategoryTheory.Center.ext
    show X.1 ◁ (r • f.f) = r • (X.1 ◁ f.f)
    exact MonoidalLinear.whiskerLeft_smul _ _ _
  smul_whiskerRight r {Y Z} f X := by
    apply CategoryTheory.Center.ext
    show (r • f.f) ▷ X.1 = r • (f.f ▷ X.1)
    exact MonoidalLinear.smul_whiskerRight _ _ _

end SKEFTHawking.SymTFT
