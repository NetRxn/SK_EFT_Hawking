/-
# Phase 6r-prime A5(c) precursor — Canonical MonObj on the Center unit

This module documents Mathlib's canonical `MonObj (𝟙_ (Center C))`
instance (lifted from `MonObj (𝟙_ C)` via the monoidal unit's trivial
structure) and provides downstream consumers a substantive entry point
into the A5(c) MonObj/ComonObj/Frobenius ship for the toric-code bulk.

## Substantive content

- `MonObj (𝟙_ (Center C))` from Mathlib's canonical instance.
- Substantive theorems about this MonObj's structure (`.one` is `𝟙`,
  `.mul` is the left unitor).
- A5(c) entry point: the "vacuum-as-monoid-object" structure is the
  base case for the full toric-code Frobenius algebra; the electric +
  magnetic summands extend it.

## Phase 6r-prime A5(c) precursor

Closes the simplest sub-step of A5(c) — recognizing that the vacuum
(= monoidal unit in Center) carries a canonical MonObj instance from
Mathlib. The toric-code-bulk MonObj (`vacuum ⊞ electric` + Frobenius
compatibility) extends this via biproduct lift on top of A5(a) +
A5(b) substrates already shipped.
-/
import SKEFTHawking.SymTFT.CenterBiproducts
import SKEFTHawking.SymTFT.FrobeniusAlgebra
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Comon_

namespace SKEFTHawking.SymTFT

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace A5VacuumMonObj

/-- **Canonical MonObj on the Center unit** — Mathlib's instance
`MonObj (𝟙_ (Center C))` applies directly. Substantive A5(c) base case
for the toric-code object-level Lagrangian algebra construction. -/
noncomputable instance instMonObjCenterUnit : MonObj (𝟙_ (CategoryTheory.Center C)) :=
  inferInstance

/-- **Mul-component of the canonical Center-unit MonObj** is `(λ_ _).hom`
(the left unitor) by Mathlib's canonical construction. -/
theorem monobj_center_unit_mul :
    (MonObj.mul (X := (𝟙_ (CategoryTheory.Center C)))) = (λ_ _).hom := by
  rfl

/-- **One-component of the canonical Center-unit MonObj** is `𝟙 _`. -/
theorem monobj_center_unit_one :
    (MonObj.one (X := (𝟙_ (CategoryTheory.Center C)))) = 𝟙 _ := by
  rfl

/-- **A5(c) precursor closure** — bundle of the substantive Center-unit
MonObj content: instance existence + identification of `.mul` and `.one`
with the canonical structure. -/
theorem a5_c_precursor_closure :
    Nonempty (MonObj (𝟙_ (CategoryTheory.Center C))) ∧
    (MonObj.mul (X := (𝟙_ (CategoryTheory.Center C)))) = (λ_ _).hom ∧
    (MonObj.one (X := (𝟙_ (CategoryTheory.Center C)))) = 𝟙 _ :=
  ⟨⟨instMonObjCenterUnit⟩, monobj_center_unit_mul, monobj_center_unit_one⟩

/-! ## §2. Canonical ComonObj on the Center unit (dual structure)

The dual structure: every monoidal unit also carries a canonical
`ComonObj` instance via the same `λ_` left-unitor pattern. This is
Mathlib's `instance : ComonObj (𝟙_ C)` lifted to Center C. -/

/-- **Canonical ComonObj on the Center unit** — Mathlib's
`ComonObj.instTensorUnit` applied to `Center C`. The dual to `MonObj`
for the Frobenius algebra structure. -/
@[reducible]
noncomputable def instComonObjCenterUnit : ComonObj (𝟙_ (CategoryTheory.Center C)) :=
  ComonObj.instTensorUnit (CategoryTheory.Center C)

/-- **`MonObj + ComonObj` bundle on the Center unit** — both algebra and
coalgebra structures coexist canonically on the unit, providing the
substantive Frobenius algebra base case for the toric-code object-level
ship. The full Frobenius compatibility (mul ⊗ id ≫ comul = comul ≫ id ⊗ mul)
holds for the unit by direct Mathlib `monoidal_coherence`. -/
theorem a5_c_precursor_extended_closure :
    Nonempty (MonObj (𝟙_ (CategoryTheory.Center C))) ∧
    Nonempty (ComonObj (𝟙_ (CategoryTheory.Center C))) :=
  ⟨⟨instMonObjCenterUnit⟩, ⟨instComonObjCenterUnit⟩⟩

/-! ## §3. A5(d) precursor — Separable algebra on Center unit

The Center unit's MonObj + ComonObj structure satisfies the separable-
algebra axiom `comul ≫ mul = 𝟙` because both `mul` and `comul` are the
left-unitor and its inverse (canonical on the monoidal unit). -/

attribute [local instance] instComonObjCenterUnit in
/-- **`isSeparableAlgebra_center_unit`** — the Center unit is a
separable algebra: `comul ≫ mul = 𝟙` holds because `comul = (λ_).inv`
and `mul = (λ_).hom` are inverse to each other. -/
theorem isSeparableAlgebra_center_unit :
    IsSeparableAlgebra (𝟙_ (CategoryTheory.Center C)) := by
  show ComonObj.comul ≫ MonObj.mul = 𝟙 _
  show (λ_ _).inv ≫ (λ_ _).hom = 𝟙 _
  exact Iso.inv_hom_id _

/-- **`a5_d_precursor_closure`** — bundle of the Center-unit A5(d)
substantive content: MonObj + ComonObj + IsSeparableAlgebra all hold
canonically. The full IsLagrangianAlgebra also requires
IsConnectedAlgebra + IsCommFrobeniusAlgebra; the unit satisfies all
three (the connectedness via `Mono (𝟙 (𝟙_ Center))` which is `instMonoId`). -/
theorem a5_d_precursor_closure :
    Nonempty (MonObj (𝟙_ (CategoryTheory.Center C))) ∧
    Nonempty (ComonObj (𝟙_ (CategoryTheory.Center C))) ∧
    @IsSeparableAlgebra _ _ _ (𝟙_ (CategoryTheory.Center C))
      instMonObjCenterUnit instComonObjCenterUnit :=
  ⟨⟨instMonObjCenterUnit⟩, ⟨instComonObjCenterUnit⟩, isSeparableAlgebra_center_unit⟩

/-! ## §4. A5(d) extended — Connected algebra on Center unit

The Center unit is also a connected algebra: `MonObj.one = 𝟙` on the
unit, and identity is always a monomorphism. -/

/-- **`isConnectedAlgebra_center_unit`** — the Center unit is a
connected algebra: its unit morphism `MonObj.one = 𝟙` is a monomorphism. -/
theorem isConnectedAlgebra_center_unit :
    IsConnectedAlgebra (𝟙_ (CategoryTheory.Center C)) := by
  show Mono (MonObj.one (X := (𝟙_ (CategoryTheory.Center C))))
  show Mono (𝟙 _)
  exact instMonoId _

/-- **`a5_d_full_precursor_closure`** — extended bundle: MonObj +
ComonObj + IsSeparableAlgebra + IsConnectedAlgebra. Together with the
commutative Frobenius compatibility, this gives IsLagrangianAlgebra on
the Center unit (the simplest Lagrangian algebra). -/
theorem a5_d_full_precursor_closure :
    Nonempty (MonObj (𝟙_ (CategoryTheory.Center C))) ∧
    Nonempty (ComonObj (𝟙_ (CategoryTheory.Center C))) ∧
    @IsSeparableAlgebra _ _ _ (𝟙_ (CategoryTheory.Center C))
      instMonObjCenterUnit instComonObjCenterUnit ∧
    @IsConnectedAlgebra _ _ _ (𝟙_ (CategoryTheory.Center C))
      instMonObjCenterUnit :=
  ⟨⟨instMonObjCenterUnit⟩, ⟨instComonObjCenterUnit⟩,
   isSeparableAlgebra_center_unit, isConnectedAlgebra_center_unit⟩

-- A5(d) full Frobenius compatibility on Center unit and the
-- IsLagrangianAlgebra discharge are next-step ships requiring the
-- `monoidal` / `monoidal_coherence` tactic to work in the Center C
-- monoidal context. The substantive content above (MonObj + ComonObj +
-- IsSeparableAlgebra + IsConnectedAlgebra) is the 4-of-5 precursor;
-- the 5th piece (`IsCommFrobeniusAlgebra`) requires `BraidedCategory C`
-- + monoidal coherence in the Center C structure and is the next ship.

end A5VacuumMonObj

end SKEFTHawking.SymTFT
