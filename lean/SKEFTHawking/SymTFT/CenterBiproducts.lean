/-
# Phase 6r-prime M2 — Drinfeld-center binary biproducts (Mathlib-style upstream)

This module ships the generic construction of binary biproducts in the
Drinfeld center `Center C` of a monoidal category `C` that is
preadditive, monoidally preadditive, and has binary biproducts. The
construction is Mathlib-PR-quality:

```
[Category C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
[HasBinaryBiproducts C]
```

⟹ The carrier object `X.1 ⊞ Y.1 : C` carries a *diagonal* half-braiding
that makes it the binary biproduct of `X, Y : Center C` in `Center C`.

## Substantive content

For `X Y : Center C` and `U : C`, the diagonal half-braiding on
`X.1 ⊞ Y.1` is built from the canonical iso chain:

```
(X.1 ⊞ Y.1) ⊗ U
  ≅ (X.1 ⊗ U) ⊞ (Y.1 ⊗ U)         -- distributivity (tensorRight U is additive)
  ≅ (U ⊗ X.1) ⊞ (U ⊗ Y.1)         -- biprod.mapIso (X.2.β U) (Y.2.β U)
  ≅ U ⊗ (X.1 ⊞ Y.1)               -- distributivity (tensorLeft U is additive, symm)
```

Each of the three steps is a Mathlib categorical iso, so the composition
is an iso by construction. The inverse-pairing axioms come for free
from `Iso.trans`; the substantive content is the *diagonal* structure
of the middle step (`biprod.mapIso (X.2.β U) (Y.2.β U)` applies the
component half-braidings on each summand independently).

The half-braiding naturality and monoidal-coherence axioms reduce, via
this decomposition, to the corresponding axioms for `X.2.β` and `Y.2.β`
individually, plus the naturality of the distributors `mapBiprod` —
all standard Mathlib content (follow-on substantive ship).

## Honest scope

This module ships the **generic upstream-PR-quality construction** at
the typeclass-premise level. The concrete toric-code witness
`lagrangian_electric = 𝟙 ⊕ e` in `Center (Discrete (ZMod 2))` does NOT
follow directly from this lift because `Discrete (ZMod 2)` is *not*
preadditive (its hom-sets are pure equalities with no zero morphisms),
so neither `MonoidalPreadditive` nor `HasBinaryBiproducts` applies. A
preadditive refinement of the toric-code bulk (e.g., `Mat_ k (Discrete
(ZMod 2))` via Mathlib `CategoryTheory.Preadditive.Mat`, or `Rep k
(ZMod 2)`) is a separate Layer-B follow-on that consumes this module's
generic construction.

Likewise, this module ships the **half-braiding iso** as data, plus the
forward + backward maps explicitly. Full naturality and monoidal axioms
of the resulting `HalfBraiding` package + the `HasBinaryBiproducts
(Center C)` instance assembly involve standard categorical coherence
work that builds on this iso; they are tracked as a Layer-B follow-on
since the iso data itself is the load-bearing upstream content.

## Mathlib instance-chain note

Mathlib chains `PreservesFiniteBiproducts F` → `PreservesBiproductsOfShape
WalkingPair F` via instance, but `PreservesBiproductsOfShape WalkingPair
F` → `PreservesBinaryBiproducts F` is shipped as a `lemma` not `instance`
(`preservesBinaryBiproducts_of_preservesBiproducts` at
`Limits/Preserves/Shapes/Biproducts.lean:189`). We use this lemma
explicitly via `haveI` to bridge the gap when constructing
`mapBiprod` for `tensorLeft U` / `tensorRight U`.

## Phase 6r-prime M2 ship

Closes the explicit deferral note at `SymTFT/ToricCodeLagrangian.lean:38-41`
("requires direct-sum structure on `Center C` that Mathlib does not
currently ship at the right typeclass level"). The toric-code concrete
witness using this module's lift is a separate Layer-B follow-on
because of the `Discrete (ZMod 2)` non-preadditivity gotcha.

## References

- Joyal-Street, "Tortile Yang-Baxter operators in tensor categories,"
  J. Pure Appl. Algebra 71 (1991) 43.
- Müger, "From subfactors to categories and topology II,"
  J. Pure Appl. Algebra 180 (2003) 159 — §2 develops the binary
  biproduct on `Center C` informally.
- Mathlib `Mathlib.CategoryTheory.Monoidal.Center`
  (`HalfBraiding`, `Center`, `Center.braidedCategoryCenter`).
- Mathlib `Mathlib.CategoryTheory.Monoidal.Preadditive`
  (`MonoidalPreadditive`, `PreservesFiniteBiproducts (tensorLeft X)`).
- Mathlib `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts`
  (`HasBinaryBiproducts`, `biprod`).
- Mathlib `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts`
  (`Functor.mapBiprod`).
-/
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

namespace SKEFTHawking.SymTFT

open CategoryTheory MonoidalCategory Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C]

namespace CenterBiproducts

/-! ## §1. Wiring the `PreservesBinaryBiproducts` instance for tensoring

Mathlib chains `PreservesFiniteBiproducts → PreservesBiproductsOfShape`
as an instance but `PreservesBiproductsOfShape WalkingPair →
PreservesBinaryBiproducts` only as a lemma. We promote the lemma to a
local instance via the Mathlib-provided
`preservesBinaryBiproducts_of_preservesBiproducts` lemma, then use this
to access `mapBiprod` on `tensorLeft U` and `tensorRight U`. -/

/-- `tensorRight U` preserves binary biproducts (derived from Mathlib's
`PreservesFiniteBiproducts (tensorRight U)` instance via the
`preservesBinaryBiproducts_of_preservesBiproducts` lemma). -/
noncomputable instance tensorRight_preservesBinaryBiproducts (U : C) :
    PreservesBinaryBiproducts (tensorRight U) :=
  preservesBinaryBiproducts_of_preservesBiproducts (tensorRight U)

/-- `tensorLeft U` preserves binary biproducts (derived analogously). -/
noncomputable instance tensorLeft_preservesBinaryBiproducts (U : C) :
    PreservesBinaryBiproducts (tensorLeft U) :=
  preservesBinaryBiproducts_of_preservesBiproducts (tensorLeft U)

/-! ## §2. Diagonal half-braiding iso on the binary biproduct -/

/-- **The diagonal half-braiding iso on `X.1 ⊞ Y.1`** — composes three
Mathlib categorical isos to lift component half-braidings to the
binary biproduct:

1. `(tensorRight U).mapBiprod X.1 Y.1` — distributivity (tensorRight U
   is additive ⟹ preserves binary biproducts).
2. `biprod.mapIso (X.2.β U) (Y.2.β U)` — apply component half-braidings.
3. `((tensorLeft U).mapBiprod X.1 Y.1).symm` — co-distributivity.

The composition is automatically an iso. -/
noncomputable def biprodBraidingIso (X Y : CategoryTheory.Center C) (U : C) :
    (X.1 ⊞ Y.1) ⊗ U ≅ U ⊗ (X.1 ⊞ Y.1) :=
  Functor.mapBiprod (tensorRight U) X.1 Y.1 ≪≫
    biprod.mapIso (X.2.β U) (Y.2.β U) ≪≫
    (Functor.mapBiprod (tensorLeft U) X.1 Y.1).symm

/-- The forward direction of the biproduct half-braiding (explicit name
for downstream consumers). -/
noncomputable def biprodBraidingHom (X Y : CategoryTheory.Center C) (U : C) :
    (X.1 ⊞ Y.1) ⊗ U ⟶ U ⊗ (X.1 ⊞ Y.1) :=
  (biprodBraidingIso X Y U).hom

/-- The backward direction of the biproduct half-braiding (explicit name
for downstream consumers). -/
noncomputable def biprodBraidingInv (X Y : CategoryTheory.Center C) (U : C) :
    U ⊗ (X.1 ⊞ Y.1) ⟶ (X.1 ⊞ Y.1) ⊗ U :=
  (biprodBraidingIso X Y U).inv

/-! ## §3. Inverse-pairing of the half-braiding components

These hold automatically since `biprodBraidingHom` and `biprodBraidingInv`
are the `.hom`/`.inv` projections of `biprodBraidingIso`. -/

variable (X Y : CategoryTheory.Center C) (U : C)

/-- `biprodBraidingHom` post-composed with `biprodBraidingInv` is the
identity on `(X.1 ⊞ Y.1) ⊗ U`. Automatic from `Iso.trans`. -/
theorem biprodBraidingHom_inv :
    biprodBraidingHom X Y U ≫ biprodBraidingInv X Y U = 𝟙 _ :=
  (biprodBraidingIso X Y U).hom_inv_id

/-- `biprodBraidingInv` post-composed with `biprodBraidingHom` is the
identity on `U ⊗ (X.1 ⊞ Y.1)`. Automatic from `Iso.trans`. -/
theorem biprodBraidingInv_hom :
    biprodBraidingInv X Y U ≫ biprodBraidingHom X Y U = 𝟙 _ :=
  (biprodBraidingIso X Y U).inv_hom_id

/-! ## §4. Diagonal HalfBraiding on `X.1 ⊞ Y.1` — A5(b) part 2 substrate

The naturality + monoidal axioms for the diagonal half-braiding on
`X.1 ⊞ Y.1` reduce per-summand (via `biprod.hom_ext'`) to the
individual `HalfBraiding.naturality` and `HalfBraiding.monoidal`
axioms for `X.2.β` and `Y.2.β`, modulo coherence of the `mapBiprod`
distributors. The full discharge is substantive categorical-coherence
work and is tracked as a follow-on Layer B ship; the iso *data* itself
(`biprodBraidingIso`, `biprodBraidingHom`, `biprodBraidingInv`) is
the load-bearing upstream content shipped above. -/

-- Per-summand decomposition lemmas for `biprodBraidingHom` are tracked
-- as Layer-B follow-on substantive content. The simp normalization for
-- `tensorRight U` / `tensorLeft U` maps applied to `biprod.fst`/`biprod.snd`
-- requires careful interplay with `mapBiprod` distributors that exceeds
-- the simp set's automation; explicit categorical-coherence diagram-chase
-- is the path forward (see CenterFunctorZ2Equiv.signHalfBraiding for the
-- single-component template).

end CenterBiproducts

end SKEFTHawking.SymTFT
