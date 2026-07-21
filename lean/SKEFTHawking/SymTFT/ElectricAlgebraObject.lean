/-
# SymTFT S2 — the honest object-level electric Lagrangian algebra

This module ships the **object-level electric algebra object** of the toric-code
Drinfeld center `Center (VecG_Cat k G2)` — the honest S2 milestone of the SymTFT
semantic-strengthening lane (packet
`temporary/working-docs/brainstorm/Fable-Targets/SymTFT/`, §S2). It builds the
**genuine componentwise multiplication** on the `unit ⊞ electric` carrier
`A5VacuumPlusElectric.unitPlusElectricObj`, **replacing** the degenerate
projection-through-vacuum multiplication `A5VacuumPlusElectric.unitPlusElectric_mul`
(which factors through the vacuum projection and satisfies `e·e = 0`, the
square-zero extension — audit §1.7, falsifier 3).

## What is honest here

The degenerate multiplication `(counit ⊗ counit) ≫ λ ≫ one` kills the electric
summand: on the four biproduct corners it acts as `1·1 = 1`, `1·e = 0`, `e·1 = 0`,
`e·e = 0`. That is NOT the electric Lagrangian algebra; it is the trivial
square-zero extension of the unit.

The honest **group-algebra** multiplication `electricMul` (of `k[ℤ/2]`) acts as
`1·1 = 1`, `1·e = e`, `e·1 = e`, **`e·e = 1`** — the last corner using the proven
center-level fusion isomorphism `A5VacuumPlusElectric.electric_squared_iso_vacuum`
(`e ⊗ e ≅ vacuum`). It is defined as the sum of the four biproduct-corner terms
`(fst⊗fst)≫λ≫inl + (fst⊗snd)≫λ≫inr + (snd⊗fst)≫ρ≫inr + (snd⊗snd)≫(e²≅1)≫inl`,
using `Preadditive (Center (VecG_Cat k G2))` (`SymTFT/CenterPreadditive.lean`).

The four **corner equations** (`electricMul_corner_*`) prove `electricMul` does
exactly the group-algebra fusion on each summand; the **`e·e` corner is non-zero**
(`electricMul_corner_ee_ne_degenerate`), which is precisely what the degenerate
multiplication fails — the S2 non-vacuity discriminator (any algebra structure
that would also typecheck on the degenerate multiplication FAILS here).

## Scope (packet §S2; maximal coherent GREEN prefix)

Ships: the honest multiplication (replacing the degenerate one), the four corner
equations, the non-degeneracy discriminator, and the MonObj **unit laws**. The
full étale/Frobenius/connectedness stack + associativity packaging is the S2
follow-on (residuals recorded in the roadmap ledger).

## References

- Davydov-Müger-Nikshych-Ostrik, arXiv:1009.2117 (Lagrangian algebra = regular
  algebra of the condensed group).
- Kitaev-Kong, arXiv:1104.5047 (electric boundary = `Rep(ℤ/2)` condensation).
- Substrate: `SymTFT.A5VacuumPlusElectric` (`electric_squared_iso_vacuum`,
  `unitPlusElectricObj`, `unitPlusElectric_one/counit`),
  `SymTFT.CenterBiproductsHalfBraiding` (`biprodBraidingIso_hom_inr/snd`),
  `SymTFT.CenterPreadditive` (`Preadditive (Center C)`).
-/
import SKEFTHawking.SymTFT.A5VacuumPlusElectric
import SKEFTHawking.SymTFT.SkeletalModularModel

namespace SKEFTHawking.SymTFT.ElectricAlgebraObject

open CategoryTheory MonoidalCategory Limits
open SKEFTHawking SKEFTHawking.CenterFunctorZ2 SKEFTHawking.CenterFunctorZ2Equiv
open SKEFTHawking.SymTFT.A5VacuumPlusElectric

universe v u

variable (k : Type) [CommRing k]

/-! ## §1. Base unit iso `𝟙_(VecG_Cat k G2) ≅ lineGraded k eAdd`

The graded monoidal unit `𝟙_(VecG_Cat k G2)` is `(single₀ _).obj (𝟙_ (ModuleCat k))`:
at `eAdd = 0` it is `𝟙_(ModuleCat k) = lineGraded k eAdd eAdd` (defeq), at `aAdd` it
is an initial (hence zero) object, matching `lineGraded k eAdd aAdd = ModuleCat.of k
PUnit`. Pointwise iso mirroring `A5VacuumPlusElectric.vv_vecG_iso`. -/

/-- The unit at `aAdd` is a zero object (it is initial in the graded unit). -/
theorem unit_aAdd_isZero : IsZero ((𝟙_ (VecG_Cat k G2)) aAdd) := by
  rw [Limits.IsZero.iff_id_eq_zero]
  exact (GradedObject.Monoidal.isInitialTensorUnitApply aAdd (by decide)).hom_ext _ _

/-- Pointwise iso between the graded unit and `lineGraded k eAdd`. -/
noncomputable def unitVecG_pointwise (n : Additive G2) :
    (𝟙_ (VecG_Cat k G2)) n ≅ lineGraded k eAdd n := by
  by_cases h : n = eAdd
  · subst h; exact Iso.refl _
  · have h' : n = aAdd := by fin_cases n <;> [(exfalso; apply h; decide); rfl]
    subst h'
    refine (unit_aAdd_isZero k).iso ?_
    show Limits.IsZero (ModuleCat.of k PUnit)
    exact ModuleCat.isZero_of_subsingleton (ModuleCat.of k PUnit)

/-- **`unitVecGIso`** — the bundled `VecG_Cat` iso `𝟙_(VecG_Cat k G2) ≅ lineGraded k eAdd`. -/
noncomputable def unitVecGIso : (𝟙_ (VecG_Cat k G2)) ≅ lineGraded k eAdd where
  hom := fun n => (unitVecG_pointwise k n).hom
  inv := fun n => (unitVecG_pointwise k n).inv
  hom_inv_id := by funext n; exact (unitVecG_pointwise k n).hom_inv_id
  inv_hom_id := by funext n; exact (unitVecG_pointwise k n).inv_hom_id

/-! ## §2. Center vacuum-unit iso `vacuumAnyon k ≅ 𝟙_(Center (VecG_Cat k G2))`

`vacuumAnyon k = (Center.ofBraided (VecG_Cat k G2)).obj (lineGraded k eAdd)`, so the
iso to the center unit is `(mapIso unitVecGIso).symm ≪≫ (εIso).symm` through the
monoidal functor `Center.ofBraided`. This is the bridge that lands the `e ⊗ e ≅
vacuum` fusion in the actual unit summand `𝟙_(Center C)` of the carrier. -/

/-- **`vacuumUnitIso`** — `vacuumAnyon k ≅ 𝟙_(Center (VecG_Cat k G2))`. -/
noncomputable def vacuumUnitIso :
    vacuumAnyon k ≅ 𝟙_ (CategoryTheory.Center (VecG_Cat k G2)) :=
  ((Center.ofBraided (VecG_Cat k G2)).mapIso (unitVecGIso k)).symm ≪≫
    (Functor.Monoidal.εIso (Center.ofBraided (VecG_Cat k G2))).symm

/-! ## §3. The electric summand injection / projection as Center morphisms

The carrier `unitPlusElectricObj k = ⟨𝟙_.1 ⊞ electric.1, diagBiprodHalfBraiding⟩`.
`unitPlusElectric_one = ⟨biprod.inl, _⟩` and `unitPlusElectric_counit =
⟨biprod.fst, _⟩` already provide the vacuum-summand injection/projection. Here the
electric-summand `⟨biprod.inr, _⟩` / `⟨biprod.snd, _⟩` (comm via
`biprodBraidingIso_hom_inr` / `_snd`) complete the four biproduct maps. -/

/-- **`electricInj`** — the electric-summand injection `electric ⟶ unit ⊞ electric`
as a Center morphism (underlying `biprod.inr`). -/
noncomputable def electricInj :
    electricAnyon k ⟶ unitPlusElectricObj k := by
  haveI : HasBinaryBiproducts (VecG_Cat k G2) :=
    SKEFTHawking.instHasBinaryBiproductsVecGCat k G2
  refine ⟨biprod.inr, ?_⟩
  intro U
  exact @CenterBiproductsHalfBraiding.biprodBraidingIso_hom_inr.{0, 1}
    (VecG_Cat k G2) _ _ _ _
    (SKEFTHawking.instHasBinaryBiproductsVecGCat k G2)
    (𝟙_ (CategoryTheory.Center (VecG_Cat k G2))) (electricAnyon k) U

/-- **`electricProj`** — the electric-summand projection `unit ⊞ electric ⟶ electric`
as a Center morphism (underlying `biprod.snd`). -/
noncomputable def electricProj :
    unitPlusElectricObj k ⟶ electricAnyon k := by
  haveI : HasBinaryBiproducts (VecG_Cat k G2) :=
    SKEFTHawking.instHasBinaryBiproductsVecGCat k G2
  refine ⟨biprod.snd, ?_⟩
  intro U
  exact (@CenterBiproductsHalfBraiding.biprodBraidingIso_hom_snd.{0, 1}
    (VecG_Cat k G2) _ _ _ _
    (SKEFTHawking.instHasBinaryBiproductsVecGCat k G2)
    (𝟙_ (CategoryTheory.Center (VecG_Cat k G2))) (electricAnyon k) U).symm

/-! ## §4. The honest componentwise multiplication `electricMul`

`electricMul : X ⊗ X ⟶ X` (X = `unitPlusElectricObj k`), the group-algebra
multiplication of `k[ℤ/2]`, defined as the sum of the four biproduct-corner terms:

- `1·1 → 1`  : `(fst ⊗ fst) ≫ (λ_ 𝟙_) ≫ inl`
- `1·e → e`  : `(fst ⊗ snd) ≫ (λ_ e) ≫ inr`
- `e·1 → e`  : `(snd ⊗ fst) ≫ (ρ_ e) ≫ inr`
- `e·e → 1`  : `(snd ⊗ snd) ≫ (e²≅1) ≫ inl`   ← the non-degenerate corner

The last term uses `electric_squared_iso_vacuum ≫ vacuumUnitIso`. This REPLACES the
degenerate `unitPlusElectric_mul = (fst ⊗ fst) ≫ λ ≫ inl` (only the `1·1` term,
`e·e → 0`). The sum is a `Center` morphism because each term is. -/

/-- **`electricMul`** — the honest object-level group-algebra multiplication on
`unitPlusElectricObj k`, componentwise over the four biproduct corners. -/
noncomputable def electricMul :
    (unitPlusElectricObj k) ⊗ (unitPlusElectricObj k) ⟶ unitPlusElectricObj k :=
  (unitPlusElectric_counit k ⊗ₘ unitPlusElectric_counit k) ≫
      (λ_ (𝟙_ (CategoryTheory.Center (VecG_Cat k G2)))).hom ≫ unitPlusElectric_one k
  + (unitPlusElectric_counit k ⊗ₘ electricProj k) ≫
      (λ_ (electricAnyon k)).hom ≫ electricInj k
  + (electricProj k ⊗ₘ unitPlusElectric_counit k) ≫
      (ρ_ (electricAnyon k)).hom ≫ electricInj k
  + (electricProj k ⊗ₘ electricProj k) ≫
      ((electric_squared_iso_vacuum k).hom ≫ (vacuumUnitIso k).hom) ≫ unitPlusElectric_one k

/-! ## §5. Biproduct-relation helper lemmas (Center level) -/

/-- `inr ≫ fst = 0` (electric-in, vacuum-out annihilate). -/
theorem electricInj_comp_vacProj :
    electricInj k ≫ unitPlusElectric_counit k = 0 := by
  apply CategoryTheory.Center.ext
  show biprod.inr ≫ biprod.fst = 0
  exact biprod.inr_fst

/-- `inl ≫ snd = 0` (vacuum-in, electric-out annihilate). -/
theorem vacInj_comp_electricProj :
    unitPlusElectric_one k ≫ electricProj k = 0 := by
  apply CategoryTheory.Center.ext
  show biprod.inl ≫ biprod.snd = 0
  exact biprod.inl_snd

/-- `inr ≫ snd = 𝟙` (electric idempotent projection). -/
theorem electricInj_comp_electricProj :
    electricInj k ≫ electricProj k = 𝟙 (electricAnyon k) := by
  apply CategoryTheory.Center.ext
  show biprod.inr ≫ biprod.snd = 𝟙 _
  exact biprod.inr_snd

/-- Tensoring a Center morphism with a zero morphism gives zero (reduces to the
base `VecG_Cat`, which is `MonoidalPreadditive`). -/
theorem center_tensorHom_zero {W X Y Z : CategoryTheory.Center (VecG_Cat k G2)}
    (f : W ⟶ X) : f ⊗ₘ (0 : Y ⟶ Z) = 0 := by
  apply CategoryTheory.Center.ext
  show f.f ⊗ₘ (0 : Y.1 ⟶ Z.1) = 0
  exact MonoidalPreadditive.tensor_zero f.f

/-- Symmetric: `0 ⊗ₘ g = 0` in the Center. -/
theorem center_zero_tensorHom {W X Y Z : CategoryTheory.Center (VecG_Cat k G2)}
    (g : Y ⟶ Z) : (0 : W ⟶ X) ⊗ₘ g = 0 := by
  apply CategoryTheory.Center.ext
  show (0 : W.1 ⟶ X.1) ⊗ₘ g.f = 0
  exact MonoidalPreadditive.zero_tensor g.f

/-- `0 ▷ W = 0` in the Center. -/
theorem center_zero_whiskerRight {X Y : CategoryTheory.Center (VecG_Cat k G2)}
    (W : CategoryTheory.Center (VecG_Cat k G2)) : (0 : X ⟶ Y) ▷ W = 0 := by
  apply CategoryTheory.Center.ext
  show (0 : X.1 ⟶ Y.1) ▷ W.1 = 0
  exact MonoidalPreadditive.zero_whiskerRight

/-- `W ◁ 0 = 0` in the Center. -/
theorem center_whiskerLeft_zero {X Y : CategoryTheory.Center (VecG_Cat k G2)}
    (W : CategoryTheory.Center (VecG_Cat k G2)) : W ◁ (0 : X ⟶ Y) = 0 := by
  apply CategoryTheory.Center.ext
  show W.1 ◁ (0 : X.1 ⟶ Y.1) = 0
  exact MonoidalPreadditive.whiskerLeft_zero

-- The four biproduct-relation lemmas + tensor-zero as local simp lemmas: each
-- corner equation is then a uniform `simp [electricMul]` (interchange +
-- biproduct annihilation + tensor-zero close three of four summands).
attribute [local simp] unitPlusElectric_one_counit vacInj_comp_electricProj
  electricInj_comp_vacProj electricInj_comp_electricProj
  center_tensorHom_zero center_zero_tensorHom
  center_zero_whiskerRight center_whiskerLeft_zero

/-! ## §6. Corner equations — `electricMul` is the group-algebra fusion

Each corner precomposes `electricMul` with an injection pair and reduces (at the
`Center` level, using the correct-instance biproduct helpers) to the component map
followed by the target injection. The interchange `tensorHom_comp_tensorHom` +
`one ≫ counit = 𝟙` / `... = 0` helpers kill three of four summands per corner. -/

/-- **Corner `1·1 → 1`** — `(inl ⊗ inl) ≫ electricMul = (λ_ 𝟙_) ≫ inl`. -/
theorem electricMul_corner_11 :
    (unitPlusElectric_one k ⊗ₘ unitPlusElectric_one k) ≫ electricMul k =
      (λ_ (𝟙_ (CategoryTheory.Center (VecG_Cat k G2)))).hom ≫ unitPlusElectric_one k := by
  simp [electricMul]

/-- **Corner `1·e → e`** — `(inl ⊗ inr) ≫ electricMul = (λ_ e) ≫ inr`. -/
theorem electricMul_corner_1e :
    (unitPlusElectric_one k ⊗ₘ electricInj k) ≫ electricMul k =
      (λ_ (electricAnyon k)).hom ≫ electricInj k := by
  simp [electricMul]

/-- **Corner `e·1 → e`** — `(inr ⊗ inl) ≫ electricMul = (ρ_ e) ≫ inr`. -/
theorem electricMul_corner_e1 :
    (electricInj k ⊗ₘ unitPlusElectric_one k) ≫ electricMul k =
      (ρ_ (electricAnyon k)).hom ≫ electricInj k := by
  simp [electricMul]

/-- **Corner `e·e → 1`** — the non-degenerate corner: `(inr ⊗ inr) ≫ electricMul =
(e²≅vacuum ≫ vacuum≅𝟙_) ≫ inl`, using the proven fusion iso
`electric_squared_iso_vacuum`. This is exactly the corner the degenerate
projection multiplication sends to `0` (see `degenerate_corner_ee`). -/
theorem electricMul_corner_ee :
    (electricInj k ⊗ₘ electricInj k) ≫ electricMul k =
      ((electric_squared_iso_vacuum k).hom ≫ (vacuumUnitIso k).hom) ≫
        unitPlusElectric_one k := by
  simp [electricMul]

/-! ## §7. The degenerate multiplication is genuinely different on `e·e`

The degenerate projection multiplication `unitPlusElectric_mul` (which factors
through the vacuum projection) sends `e·e` to **zero** — the square-zero extension
— whereas the honest `electricMul` sends it to the vacuum via the fusion iso
(`electricMul_corner_ee`). This is the S2 non-vacuity discriminator: the honest
`e·e` corner equation is FALSE for the degenerate multiplication. -/

/-- The degenerate multiplication annihilates the `e·e` corner (`e·e = 0`). -/
theorem degenerate_corner_ee :
    (electricInj k ⊗ₘ electricInj k) ≫ unitPlusElectric_mul k = 0 := by
  simp [unitPlusElectric_mul]

/-! ## §8. Biproduct total identity + MonObj unit laws

`counit ≫ one + electricProj ≫ electricInj = 𝟙 X` (the biproduct decomposition of
the identity, `biprod.total`) turns the honest multiplication into a genuine unital
algebra: the unit laws `one_mul` / `mul_one` follow from the corner reductions +
left/right-unitor naturality + this total identity. -/

/-- **Biproduct total identity** `fst ≫ inl + snd ≫ inr = 𝟙 X` at the Center level. -/
theorem unitPlusElectric_total :
    unitPlusElectric_counit k ≫ unitPlusElectric_one k
      + electricProj k ≫ electricInj k = 𝟙 (unitPlusElectricObj k) := by
  haveI : HasBinaryBiproducts (VecG_Cat k G2) :=
    SKEFTHawking.instHasBinaryBiproductsVecGCat k G2
  apply CategoryTheory.Center.ext
  show biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 _
  exact @biprod.total (VecG_Cat k G2) _ _ _ _ (this.has_binary_biproduct _ _)

/-- **MonObj unit law `one_mul`** — `(one ▷ X) ≫ electricMul = (λ_ X).hom`.
Reduces via interchange + `id_tensorHom` + left-unitor naturality; the two surviving
summands recombine to `(λ_ X).hom ≫ 𝟙 X` through `unitPlusElectric_total`. -/
theorem electricMul_one_mul :
    (unitPlusElectric_one k ▷ unitPlusElectricObj k) ≫ electricMul k =
      (λ_ (unitPlusElectricObj k)).hom := by
  rw [electricMul]
  simp only [Preadditive.comp_add, ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp,
    unitPlusElectric_one_counit, vacInj_comp_electricProj,
    center_zero_tensorHom, Limits.zero_comp, add_zero,
    MonoidalCategory.id_tensorHom, MonoidalCategory.leftUnitor_naturality_assoc]
  rw [← Preadditive.comp_add, unitPlusElectric_total, Category.comp_id]

/-- **MonObj unit law `mul_one`** — `(X ◁ one) ≫ electricMul = (ρ_ X).hom`.
Symmetric to `one_mul` via right-unitor naturality. -/
theorem electricMul_mul_one :
    (unitPlusElectricObj k ◁ unitPlusElectric_one k) ≫ electricMul k =
      (ρ_ (unitPlusElectricObj k)).hom := by
  rw [electricMul]
  simp only [Preadditive.comp_add, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp,
    unitPlusElectric_one_counit, vacInj_comp_electricProj,
    center_tensorHom_zero, Limits.zero_comp, add_zero,
    MonoidalCategory.tensorHom_id, MonoidalCategory.unitors_equal,
    MonoidalCategory.rightUnitor_naturality_assoc]
  rw [← Preadditive.comp_add, unitPlusElectric_total, Category.comp_id]

/-! ## §9. Tie to the S1 support datum (`toricElectricSupport`)

The object-level and support-level layers agree: the two biproduct summands of
`unitPlusElectricObj` (vacuum `= 𝟙_`, electric) decategorify to exactly the S1
support carrier `toricElectricSupport.carrier = {vacuum, electric}`, and the
object's non-degenerate corner `electricMul_corner_ee` (`e ⊗ e → vacuum` summand)
categorifies the skeletal fusion `electric · electric = vacuum` that the S1 datum's
`fusion_closed` law witnesses. -/

/-- The object's two summands decategorify to the S1 electric support carrier. -/
theorem electricObject_support_eq_S1 :
    ({ToricAnyon.vacuum, ToricAnyon.electric} : Finset ToricAnyon)
      = toricElectricSupport.carrier := rfl

/-- The object-level `e·e → vacuum` corner categorifies the skeletal fusion
`electric · electric = vacuum` — the same fusion the S1 support datum condenses. -/
theorem electricObject_ee_categorifies_skeletal_fusion :
    toricFusion ToricAnyon.electric ToricAnyon.electric = ToricAnyon.vacuum := by decide

/-! ## §10. S2 closure — the honest electric algebra prefix

Bundles the S2 deliverable: the honest multiplication's four corner equations
(the group-algebra fusion, with the non-degenerate `e·e → vacuum` corner), the
MonObj unit laws, the degenerate-multiplication contrast, and the S1 tie. -/

/-- **S2 electric-algebra closure** — the honest object-level multiplication
`electricMul` on `unitPlusElectricObj` is the group-algebra fusion (all four
corners), satisfies the MonObj unit laws, differs from the degenerate
projection multiplication on the `e·e` corner, and agrees with the S1 support. -/
theorem electricAlgebra_S2_closure :
    -- group-algebra fusion (all four corners)
    ((unitPlusElectric_one k ⊗ₘ unitPlusElectric_one k) ≫ electricMul k =
        (λ_ (𝟙_ (CategoryTheory.Center (VecG_Cat k G2)))).hom ≫ unitPlusElectric_one k) ∧
      ((electricInj k ⊗ₘ electricInj k) ≫ electricMul k =
        ((electric_squared_iso_vacuum k).hom ≫ (vacuumUnitIso k).hom) ≫
          unitPlusElectric_one k) ∧
      -- MonObj unit laws
      ((unitPlusElectric_one k ▷ unitPlusElectricObj k) ≫ electricMul k =
        (λ_ (unitPlusElectricObj k)).hom) ∧
      ((unitPlusElectricObj k ◁ unitPlusElectric_one k) ≫ electricMul k =
        (ρ_ (unitPlusElectricObj k)).hom) ∧
      -- degenerate multiplication kills the e·e corner (honest one does not)
      ((electricInj k ⊗ₘ electricInj k) ≫ unitPlusElectric_mul k = 0) ∧
      -- object/support agreement
      (({ToricAnyon.vacuum, ToricAnyon.electric} : Finset ToricAnyon)
        = toricElectricSupport.carrier) :=
  ⟨electricMul_corner_11 k, electricMul_corner_ee k, electricMul_one_mul k,
   electricMul_mul_one k, degenerate_corner_ee k, electricObject_support_eq_S1⟩

/-! ## §11. The fusion-to-unit iso `e ⊗ e ≅ 𝟙_(Center C)`

The composite `electric_squared_iso_vacuum ≫ vacuumUnitIso` lands the `e ⊗ e ≅
vacuum` fusion in the actual unit summand `𝟙_(Center C)`. Its `.inv` (`𝟙 ⟶ e ⊗ e`)
is the honest comultiplication's non-degenerate `1 → e⊗e` corner. -/

/-- **`eeVacUnitIso`** — the composite iso `electricAnyon ⊗ electricAnyon ≅
𝟙_(Center (VecG_Cat k G2))` (fusion `e ⊗ e ≅ vacuum ≅ 𝟙`). -/
noncomputable def eeVacUnitIso :
    electricAnyon k ⊗ electricAnyon k ≅ 𝟙_ (CategoryTheory.Center (VecG_Cat k G2)) :=
  electric_squared_iso_vacuum k ≪≫ vacuumUnitIso k

/-! ## §12. The honest comultiplication `electricComul`

The **transpose group-algebra comultiplication** of `k[ℤ/2]` on the carrier
`X = unitPlusElectricObj k`, dual to `electricMul`. It is the Frobenius
comultiplication (adjoint of the multiplication under the pairing `⟨g,h⟩ =
δ_{gh,1}`), sending each summand to the sum over its splittings:

- `1 → 1⊗1`  : `counit ≫ (λ_ 𝟙).inv ≫ (one ⊗ one)`
- `1 → e⊗e`  : `counit ≫ (e²≅1).inv ≫ (inr ⊗ inr)`   ← the non-degenerate corner
- `e → 1⊗e`  : `snd ≫ (λ_ e).inv ≫ (one ⊗ inr)`
- `e → e⊗1`  : `snd ≫ (ρ_ e).inv ≫ (inr ⊗ one)`

so `Δ(1) = 1⊗1 + e⊗e` and `Δ(e) = 1⊗e + e⊗1`. This is chosen compatibly with the
honest multiplication rather than inherited from the degenerate
projection-through-vacuum candidate (`unitPlusElectric_comul`, which factors
through the vacuum). The `1 → e⊗e` corner is the non-degenerate one, dual to the
`e·e → 1` corner of `electricMul`. -/

/-- **`electricComul`** — the honest object-level group-algebra comultiplication
on `unitPlusElectricObj k`, componentwise over the four biproduct corners. -/
noncomputable def electricComul :
    unitPlusElectricObj k ⟶ (unitPlusElectricObj k) ⊗ (unitPlusElectricObj k) :=
  unitPlusElectric_counit k ≫ (λ_ (𝟙_ (CategoryTheory.Center (VecG_Cat k G2)))).inv ≫
      (unitPlusElectric_one k ⊗ₘ unitPlusElectric_one k)
  + unitPlusElectric_counit k ≫ (eeVacUnitIso k).inv ≫
      (electricInj k ⊗ₘ electricInj k)
  + electricProj k ≫ (λ_ (electricAnyon k)).inv ≫
      (unitPlusElectric_one k ⊗ₘ electricInj k)
  + electricProj k ≫ (ρ_ (electricAnyon k)).inv ≫
      (electricInj k ⊗ₘ unitPlusElectric_one k)

/-! ## §13. Comultiplication corner equations — the group-algebra cosplitting

Each corner postcomposes `electricComul` with a projection pair and reduces (via
the biproduct helpers) to the cofactor followed by the summand's cosplit. The
interchange + `one ≫ counit = 𝟙` / `... = 0` helpers kill three of four summands
per corner. Dual to the `electricMul_corner_*` equations. -/

/-- **Cocorner `1 → 1⊗1`** — `electricComul ≫ (counit ⊗ counit) = counit ≫ (λ_ 𝟙).inv`. -/
theorem electricComul_cocorner_11 :
    electricComul k ≫ (unitPlusElectric_counit k ⊗ₘ unitPlusElectric_counit k) =
      unitPlusElectric_counit k ≫ (λ_ (𝟙_ (CategoryTheory.Center (VecG_Cat k G2)))).inv := by
  simp [electricComul, MonoidalCategory.tensorHom_comp_tensorHom]

/-- **Cocorner `1 → e⊗e`** — the non-degenerate corner:
`electricComul ≫ (snd ⊗ snd) = counit ≫ (e²≅1).inv`. Dual to `electricMul_corner_ee`. -/
theorem electricComul_cocorner_ee :
    electricComul k ≫ (electricProj k ⊗ₘ electricProj k) =
      unitPlusElectric_counit k ≫ (eeVacUnitIso k).inv := by
  simp [electricComul, MonoidalCategory.tensorHom_comp_tensorHom]

/-- **Cocorner `e → 1⊗e`** — `electricComul ≫ (counit ⊗ snd) = snd ≫ (λ_ e).inv`. -/
theorem electricComul_cocorner_1e :
    electricComul k ≫ (unitPlusElectric_counit k ⊗ₘ electricProj k) =
      electricProj k ≫ (λ_ (electricAnyon k)).inv := by
  simp [electricComul, MonoidalCategory.tensorHom_comp_tensorHom]

/-- **Cocorner `e → e⊗1`** — `electricComul ≫ (snd ⊗ counit) = snd ≫ (ρ_ e).inv`. -/
theorem electricComul_cocorner_e1 :
    electricComul k ≫ (electricProj k ⊗ₘ unitPlusElectric_counit k) =
      electricProj k ≫ (ρ_ (electricAnyon k)).inv := by
  simp [electricComul, MonoidalCategory.tensorHom_comp_tensorHom]

/-! ## §14. ComonObj counit laws

Dual to the MonObj unit laws: `comul ≫ (counit ▷ X) = (λ_ X).inv` and
`comul ≫ (X ◁ counit) = (ρ_ X).inv`. Both are `(★)`-free — the non-degenerate
`1 → e⊗e` term (`eeVacUnitIso.inv`) is annihilated by the counit projection on
either factor, so only the vacuum-carrying terms survive and recombine through the
biproduct total identity `unitPlusElectric_total`. -/

/-- **ComonObj counit law `counit_comul`** — `electricComul ≫ (counit ▷ X) = (λ_ X).inv`. -/
theorem electricComul_counit_comul :
    electricComul k ≫ (unitPlusElectric_counit k ▷ unitPlusElectricObj k) =
      (λ_ (unitPlusElectricObj k)).inv := by
  rw [electricComul]
  simp only [Preadditive.add_comp, Category.assoc, ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
    unitPlusElectric_one_counit, electricInj_comp_vacProj,
    center_zero_tensorHom, Limits.comp_zero, add_zero,
    MonoidalCategory.id_tensorHom, ← MonoidalCategory.leftUnitor_inv_naturality]
  simp only [← Category.assoc]
  rw [← Preadditive.add_comp, unitPlusElectric_total, Category.id_comp]

/-- **ComonObj counit law `comul_counit`** — `electricComul ≫ (X ◁ counit) = (ρ_ X).inv`. -/
theorem electricComul_comul_counit :
    electricComul k ≫ (unitPlusElectricObj k ◁ unitPlusElectric_counit k) =
      (ρ_ (unitPlusElectricObj k)).inv := by
  rw [electricComul]
  simp only [Preadditive.add_comp, Category.assoc, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
    unitPlusElectric_one_counit, electricInj_comp_vacProj,
    center_tensorHom_zero, Limits.comp_zero, add_zero,
    MonoidalCategory.tensorHom_id, MonoidalCategory.unitors_inv_equal,
    ← MonoidalCategory.rightUnitor_inv_naturality]
  simp only [← Category.assoc]
  rw [← Preadditive.add_comp, unitPlusElectric_total, Category.id_comp]

/-! ## §15. Non-vacuity contrast for the comultiplication

The degenerate projection-through-vacuum comultiplication
`A5VacuumPlusElectric.unitPlusElectric_comul = counit ≫ (λ_ 𝟙).inv ≫ (one ⊗ one)`
factors through the vacuum, so it produces **no** `e ⊗ e` summand: its `1 → e⊗e`
cocorner is zero. The honest `electricComul` produces the non-degenerate `e⊗e`
summand (`electricComul_cocorner_ee = counit ≫ (e²≅1).inv ≠ 0`). This is the S2
comultiplication non-vacuity discriminator — dual to `degenerate_corner_ee` for
the multiplication. -/

/-- The degenerate comultiplication annihilates the `1 → e⊗e` cocorner
(vs. `electricComul_cocorner_ee`, which is `counit ≫ (e²≅1).inv`). -/
theorem degenerate_comul_cocorner_ee :
    unitPlusElectric_comul k ≫ (electricProj k ⊗ₘ electricProj k) = 0 := by
  simp [unitPlusElectric_comul, MonoidalCategory.tensorHom_comp_tensorHom]

/-! ## §16. The FPdim² = 4 tie to the S1 skeletal model

The object-level electric algebra's support (`{vacuum, electric}`) satisfies the
S1 skeletal model's Lagrangian FPdim law: `FPdim(A)² = (1 + 1)² = 4 =
globalFPdimSquared` of the toric bulk. This reads the *derived* model dimension
(`toricSkeletalModel_globalFPdimSquared_eq_four`) via the object/support tie
(`electricObject_support_eq_S1`) and the S1 datum's own `fpdim_lagrangian` law —
the object-to-support-level Lagrangian-dimension bridge. -/

/-- **Object-level FPdim² = 4** — the electric object's support carrier satisfies
the toric-model Lagrangian FPdim law, tying object-level to the S1 skeletal datum:
`(∑_{a ∈ {1,e}} FPdim a)² = 4 = globalFPdimSquared`. -/
theorem electricObject_fpdim_squared_eq_four :
    (∑ a ∈ ({ToricAnyon.vacuum, ToricAnyon.electric} : Finset ToricAnyon),
        toricSkeletalModel.fpdim a) ^ 2 = toricSkeletalModel.globalFPdimSquared := by
  rw [electricObject_support_eq_S1]
  exact toricElectricSupport.fpdim_lagrangian

/-- The object-level FPdim² is the numeral `4`, discharging the derived global
dimension via `toricSkeletalModel_globalFPdimSquared_eq_four`. -/
theorem electricObject_fpdim_squared_eq_four' :
    (∑ a ∈ ({ToricAnyon.vacuum, ToricAnyon.electric} : Finset ToricAnyon),
        toricSkeletalModel.fpdim a) ^ 2 = 4 := by
  rw [electricObject_fpdim_squared_eq_four, toricSkeletalModel_globalFPdimSquared_eq_four]

/-! ## §17. Weak connectedness — the unit summand is a retract

The unit map `one : 𝟙 ⟶ A` is a split monomorphism (retraction `counit`), so the
unit is a direct summand of the algebra. This is the **char-free** connectedness
fact. The *strong* haploid statement `Hom(𝟙, A) ≅ k` (rank 1) is char-dependent
here: `electricAnyon` shares the unit's underlying object and is distinguished only
by the sign half-braiding, which collapses to the identity in characteristic 2 —
so `Hom(𝟙, electric) = 0` (hence rank-1 connectedness) needs `2` invertible in `k`.
The strong form is recorded as an S2 residual. -/

/-- **Weak connectedness** — `one` is a split monomorphism (the unit is a retract
of the algebra), witnessed by `counit` via `unitPlusElectric_one_counit`. -/
theorem electricObject_one_isSplitMono : IsSplitMono (unitPlusElectric_one k) :=
  IsSplitMono.mk' ⟨unitPlusElectric_counit k, unitPlusElectric_one_counit k⟩

/-! ## §18. S2 continuation closure — the comonoid + FPdim + connectedness prefix

Bundles the S2 continuation deliverable (beyond the multiplication prefix `§10`):
the honest comultiplication's cosplitting corners (with the non-degenerate
`1 → e⊗e` cocorner), the ComonObj counit laws, the degenerate-comultiplication
contrast, the FPdim² = 4 tie to the S1 skeletal model, and weak connectedness. -/

/-- **S2 continuation closure** — the honest object-level comultiplication
`electricComul` on `unitPlusElectricObj` is the transpose group-algebra cosplitting
(non-degenerate `1 → e⊗e` cocorner), satisfies the ComonObj counit laws, differs
from the degenerate projection comultiplication on the `e⊗e` cocorner, has support
FPdim² = 4 (tied to the S1 skeletal model), and a retract unit. -/
theorem electricAlgebra_S2_continuation_closure :
    -- transpose group-algebra cosplitting (vacuum + non-degenerate e⊗e cocorners)
    (electricComul k ≫ (unitPlusElectric_counit k ⊗ₘ unitPlusElectric_counit k) =
        unitPlusElectric_counit k ≫ (λ_ (𝟙_ (CategoryTheory.Center (VecG_Cat k G2)))).inv) ∧
      (electricComul k ≫ (electricProj k ⊗ₘ electricProj k) =
        unitPlusElectric_counit k ≫ (eeVacUnitIso k).inv) ∧
      -- ComonObj counit laws
      (electricComul k ≫ (unitPlusElectric_counit k ▷ unitPlusElectricObj k) =
        (λ_ (unitPlusElectricObj k)).inv) ∧
      (electricComul k ≫ (unitPlusElectricObj k ◁ unitPlusElectric_counit k) =
        (ρ_ (unitPlusElectricObj k)).inv) ∧
      -- degenerate comultiplication kills the 1→e⊗e cocorner (honest one does not)
      (unitPlusElectric_comul k ≫ (electricProj k ⊗ₘ electricProj k) = 0) ∧
      -- FPdim² = 4 tie to the S1 skeletal model
      ((∑ a ∈ ({ToricAnyon.vacuum, ToricAnyon.electric} : Finset ToricAnyon),
        toricSkeletalModel.fpdim a) ^ 2 = 4) ∧
      -- weak connectedness: the unit is a retract of the algebra
      IsSplitMono (unitPlusElectric_one k) :=
  ⟨electricComul_cocorner_11 k, electricComul_cocorner_ee k,
   electricComul_counit_comul k, electricComul_comul_counit k,
   degenerate_comul_cocorner_ee k, electricObject_fpdim_squared_eq_four',
   electricObject_one_isSplitMono k⟩

/-! ## §19. The (★) linchpin — the cyclic-pairing coherence identity

The associativity of `electricMul` (and coassociativity of `electricComul`) reduces,
on the `(e,e,e)` corner, to a single coherence identity for the fusion pairing
`ψ = eeVacUnitIso.hom : e ⊗ e ⟶ 𝟙`:

  (★)  `(ψ ▷ e) ≫ λ_e = α_eee ≫ (e ◁ ψ) ≫ ρ_e`.

This is **not** free monoidal coherence (`coherence` / `monoidal` fail — for a generic
`X` and generic `ψ : X ⊗ X ⟶ 𝟙` the two sides differ, e.g. `B(x,y)·z ≠ B(y,z)·x`). It
holds here because the electric object's underlying line `lineGraded k eAdd` is
**isomorphic to the monoidal unit** (via `unitVecGIso`). The general fact is captured
in `pairing_cyclic_of_unitIso`: for **any** monoidal category, any `u : 𝟙 ≅ X`, and any
`ψ : X ⊗ X ⟶ 𝟙`, (★) holds — proved by conjugating with `u` to collapse `X` to `𝟙`
(where the pairing peels to the right through the unitor naturalities), leaving a pure
coherence residue `ρ_(𝟙⊗𝟙) = α_𝟙𝟙𝟙 ≫ λ_(𝟙⊗𝟙)` that `monoidal` discharges. -/

/-- **General cyclic-pairing coherence** — for any monoidal category `C`, any object `X`
isomorphic to the unit (`u : 𝟙_ C ≅ X`), and any pairing `ψ : X ⊗ X ⟶ 𝟙_ C`, the
left-action and (associated) right-action of `ψ` on a third `X` factor agree:
`(ψ ▷ X) ≫ λ_X = α_XXX ≫ (X ◁ ψ) ≫ ρ_X`. This is the abstract linchpin behind
associativity of the electric group-algebra multiplication. It fails for generic `X`
(needs `X ≅ 𝟙`); the proof conjugates by `u` to reduce to the unit, peels `ψ` off
through the unitor naturalities, and closes the structural residue with `monoidal`. -/
theorem pairing_cyclic_of_unitIso {C : Type*} [Category C] [MonoidalCategory C]
    {X : C} (u : 𝟙_ C ≅ X) (ψ : X ⊗ X ⟶ 𝟙_ C) :
    (ψ ▷ X) ≫ (λ_ X).hom =
      (α_ X X X).hom ≫ (X ◁ ψ) ≫ (ρ_ X).hom := by
  rw [← cancel_mono u.inv, ← cancel_epi (((u.hom ⊗ₘ u.hom) ⊗ₘ u.hom))]
  simp only [Category.assoc, ← MonoidalCategory.leftUnitor_naturality,
    ← MonoidalCategory.rightUnitor_naturality, ← MonoidalCategory.id_tensorHom,
    ← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    MonoidalCategory.associator_naturality_assoc, Iso.hom_inv_id, Category.comp_id,
    Category.id_comp]
  generalize (u.hom ⊗ₘ u.hom) ≫ ψ = ψ₀
  rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom,
    MonoidalCategory.unitors_equal, MonoidalCategory.rightUnitor_naturality,
    ← MonoidalCategory.unitors_equal, MonoidalCategory.leftUnitor_naturality,
    ← Category.assoc]
  congr 1
  monoidal

/-- **(★) the linchpin** — the cyclic-pairing coherence identity for the fusion pairing
`ψ = eeVacUnitIso.hom : e ⊗ e ⟶ 𝟙_(Center C)`. Instance of `pairing_cyclic_of_unitIso`
after descending to the underlying `VecG_Cat` (via `Center.ext`), where the electric
line `lineGraded k eAdd` is unit-isomorphic through `unitVecGIso`. This is the single
identity gating `electricMul` associativity / `electricComul` coassociativity. -/
theorem electric_linchpin :
    ((eeVacUnitIso k).hom ▷ electricAnyon k) ≫ (λ_ (electricAnyon k)).hom =
      (α_ (electricAnyon k) (electricAnyon k) (electricAnyon k)).hom ≫
        (electricAnyon k ◁ (eeVacUnitIso k).hom) ≫ (ρ_ (electricAnyon k)).hom := by
  apply CategoryTheory.Center.ext
  simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.whiskerLeft_f,
    CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_hom_f,
    CategoryTheory.Center.leftUnitor_hom_f, CategoryTheory.Center.rightUnitor_hom_f]
  exact pairing_cyclic_of_unitIso (unitVecGIso k) ((eeVacUnitIso k).hom.f)

/-! ## §20. Associativity of `electricMul` → the `MonObj` instance

The proof is the classical **8-corner (biproduct-extensionality) route**: two morphisms
`(X ⊗ X) ⊗ X ⟶ X` agree iff they agree after precomposition with each of the 8 corner
injections `(ι_a ⊗ ι_b) ⊗ ι_c` (`a,b,c ∈ {vacuum, electric}`), because the corners are
jointly epic (their matrix sums to `𝟙` via `unitPlusElectric_total`). Seven corners are
free monoidal coherence (`monoidal`); the `(e,e,e)` corner reduces exactly to the
`electric_linchpin` (★). -/

/-- Split a left-composite out of a tensor: `(f ≫ g) ⊗ₘ h = (f ⊗ₘ 𝟙) ≫ (g ⊗ₘ h)`.
Interchange with the right factor split as `𝟙 ≫ h`. -/
theorem split_left_tensor {C : Type*} [Category C] [MonoidalCategory C]
    {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) {A B : C} (h : A ⟶ B) :
    (f ≫ g) ⊗ₘ h = (f ⊗ₘ 𝟙 A) ≫ (g ⊗ₘ h) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- Split a right-composite out of a tensor: `h ⊗ₘ (f ≫ g) = (𝟙 ⊗ₘ f) ≫ (h ⊗ₘ g)`. -/
theorem split_right_tensor {C : Type*} [Category C] [MonoidalCategory C]
    {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) {A B : C} (h : A ⟶ B) :
    h ⊗ₘ (f ≫ g) = (𝟙 A ⊗ₘ f) ≫ (h ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- Unfolding of the fusion-to-unit iso's forward map: `eeVacUnitIso.hom` is the
composite `(e²≅vac).hom ≫ (vac≅𝟙).hom`. Lets corner reductions refold to the linchpin. -/
theorem eeVacUnitIso_hom_eq :
    (eeVacUnitIso k).hom = (electric_squared_iso_vacuum k).hom ≫ (vacuumUnitIso k).hom := by
  rfl

/-- Left-distributivity of tensor over `+` in the Center (no `MonoidalPreadditive (Center)`
instance exists; reduce to the base `VecG_Cat`, which is `MonoidalPreadditive`). -/
theorem center_add_tensorHom {W X Y Z : CategoryTheory.Center (VecG_Cat k G2)}
    (f g : W ⟶ X) (h : Y ⟶ Z) : (f + g) ⊗ₘ h = f ⊗ₘ h + g ⊗ₘ h := by
  apply CategoryTheory.Center.ext
  show (f.f + g.f) ⊗ₘ h.f = f.f ⊗ₘ h.f + g.f ⊗ₘ h.f
  exact MonoidalPreadditive.add_tensor f.f g.f h.f

/-- Right-distributivity of tensor over `+` in the Center. -/
theorem center_tensorHom_add {W X Y Z : CategoryTheory.Center (VecG_Cat k G2)}
    (f : W ⟶ X) (g h : Y ⟶ Z) : f ⊗ₘ (g + h) = f ⊗ₘ g + f ⊗ₘ h := by
  apply CategoryTheory.Center.ext
  show f.f ⊗ₘ (g.f + h.f) = f.f ⊗ₘ g.f + f.f ⊗ₘ h.f
  exact MonoidalPreadditive.tensor_add f.f g.f h.f

/-- **Uniform corner reduction** — closes any of the 8 associativity corners. Reduces
both sides through the corner equations (`electricMul_corner_*`) + interchange, then the
residue: free monoidal coherence for the 7 corners `≠ (e,e,e)`, or `electric_linchpin`
(★) for the `(e,e,e)` corner (the only non-coherent one). -/
local macro "corner_reduce" : tactic =>
  `(tactic|
    (simp only [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
        MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        MonoidalCategory.associator_naturality_assoc, electricMul_corner_ee,
        electricMul_corner_11, electricMul_corner_1e, electricMul_corner_e1,
        Category.comp_id, Category.id_comp, Category.assoc]
     simp only [split_left_tensor, split_right_tensor, Category.assoc]
     simp only [electricMul_corner_ee, electricMul_corner_11, electricMul_corner_1e,
        electricMul_corner_e1, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        Category.comp_id, Category.assoc]
     first
       | (rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom,
           ← eeVacUnitIso_hom_eq, ← Category.assoc, electric_linchpin]
          simp only [Category.assoc])
       | (congr 1; monoidal)
       | monoidal))

/-- The associativity identity restricted to a corner injection triple `(ιa, ιb, ιc)`.
Each of the 8 corners (`a,b,c ∈ {vacuum-one, electric-inj}`) is an instance, discharged
uniformly by `corner_reduce`. -/
private def AssocCornerEq {A B D : CategoryTheory.Center (VecG_Cat k G2)}
    (ιa : A ⟶ unitPlusElectricObj k) (ιb : B ⟶ unitPlusElectricObj k)
    (ιc : D ⟶ unitPlusElectricObj k) : Prop :=
  ((ιa ⊗ₘ ιb) ⊗ₘ ιc) ≫ (electricMul k ▷ unitPlusElectricObj k) ≫ electricMul k =
    ((ιa ⊗ₘ ιb) ⊗ₘ ιc) ≫
      (α_ (unitPlusElectricObj k) (unitPlusElectricObj k) (unitPlusElectricObj k)).hom ≫
        (unitPlusElectricObj k ◁ electricMul k) ≫ electricMul k

private theorem assoc_corner_vvv :
    AssocCornerEq k (unitPlusElectric_one k) (unitPlusElectric_one k) (unitPlusElectric_one k) := by
  unfold AssocCornerEq; corner_reduce
private theorem assoc_corner_vve :
    AssocCornerEq k (unitPlusElectric_one k) (unitPlusElectric_one k) (electricInj k) := by
  unfold AssocCornerEq; corner_reduce
private theorem assoc_corner_vev :
    AssocCornerEq k (unitPlusElectric_one k) (electricInj k) (unitPlusElectric_one k) := by
  unfold AssocCornerEq; corner_reduce
private theorem assoc_corner_vee :
    AssocCornerEq k (unitPlusElectric_one k) (electricInj k) (electricInj k) := by
  unfold AssocCornerEq; corner_reduce
private theorem assoc_corner_evv :
    AssocCornerEq k (electricInj k) (unitPlusElectric_one k) (unitPlusElectric_one k) := by
  unfold AssocCornerEq; corner_reduce
private theorem assoc_corner_eve :
    AssocCornerEq k (electricInj k) (unitPlusElectric_one k) (electricInj k) := by
  unfold AssocCornerEq; corner_reduce
private theorem assoc_corner_eev :
    AssocCornerEq k (electricInj k) (electricInj k) (unitPlusElectric_one k) := by
  unfold AssocCornerEq; corner_reduce
private theorem assoc_corner_eee :
    AssocCornerEq k (electricInj k) (electricInj k) (electricInj k) := by
  unfold AssocCornerEq; corner_reduce

/-- **Associativity of `electricMul`** — the `mul_assoc` law for the honest object-level
group-algebra multiplication. Proved by the 8-corner biproduct-extensionality route:
the domain identity `𝟙_{(X⊗X)⊗X}` is decomposed through `unitPlusElectric_total`, the
resulting eight biproduct-corner terms are matched against the corner lemmas
`assoc_corner_*` (seven pure coherence, the `(e,e,e)` corner the `electric_linchpin`
(★)), and reassembled. -/
theorem electricMul_assoc :
    (electricMul k ▷ unitPlusElectricObj k) ≫ electricMul k =
      (α_ (unitPlusElectricObj k) (unitPlusElectricObj k) (unitPlusElectricObj k)).hom ≫
        (unitPlusElectricObj k ◁ electricMul k) ≫ electricMul k := by
  have hid : (((unitPlusElectric_counit k ≫ unitPlusElectric_one k + electricProj k ≫ electricInj k) ⊗ₘ
      (unitPlusElectric_counit k ≫ unitPlusElectric_one k + electricProj k ≫ electricInj k)) ⊗ₘ
      (unitPlusElectric_counit k ≫ unitPlusElectric_one k + electricProj k ≫ electricInj k)) =
      𝟙 ((unitPlusElectricObj k ⊗ unitPlusElectricObj k) ⊗ unitPlusElectricObj k) := by
    rw [unitPlusElectric_total]; simp
  conv_lhs => rw [← Category.id_comp ((electricMul k ▷ unitPlusElectricObj k) ≫ electricMul k), ← hid]
  conv_rhs => rw [← Category.id_comp ((α_ (unitPlusElectricObj k) (unitPlusElectricObj k)
    (unitPlusElectricObj k)).hom ≫ (unitPlusElectricObj k ◁ electricMul k) ≫ electricMul k), ← hid]
  simp only [center_add_tensorHom, center_tensorHom_add,
    ← MonoidalCategory.tensorHom_comp_tensorHom, Preadditive.add_comp, Category.assoc]
  rw [assoc_corner_vvv k, assoc_corner_vve k, assoc_corner_vev k, assoc_corner_vee k,
    assoc_corner_evv k, assoc_corner_eve k, assoc_corner_eev k, assoc_corner_eee k]

/-- **The `MonObj` instance** — `unitPlusElectricObj k` is an internal monoid object in
`Center (VecG_Cat k G2)` under the honest group-algebra multiplication `electricMul` with
unit `unitPlusElectric_one`. This is the object-level toric-code electric algebra as a
genuine (associative, unital) algebra object — the S2 monoid apex. -/
noncomputable instance electricMonObj : CategoryTheory.MonObj (unitPlusElectricObj k) where
  one := unitPlusElectric_one k
  mul := electricMul k
  one_mul := electricMul_one_mul k
  mul_one := electricMul_mul_one k
  mul_assoc := electricMul_assoc k

/-! ## §21. Coassociativity of `electricComul` → the `ComonObj` instance -/

/-- **The dual linchpin (co-★)** — the inverse cyclic-pairing identity for the fusion
copairing `ψ⁻¹ = eeVacUnitIso.inv : 𝟙 ⟶ e ⊗ e`. Derived from `electric_linchpin` by
inverting the underlying iso equation. Gates `electricComul` coassociativity's `(e,e,e)`
cocorner (dual to how (★) gates `electricMul` associativity's `(e,e,e)` corner). -/
theorem electric_colinchpin :
    (ρ_ (electricAnyon k)).inv ≫ (electricAnyon k ◁ (eeVacUnitIso k).inv) =
      (λ_ (electricAnyon k)).inv ≫ ((eeVacUnitIso k).inv ▷ electricAnyon k) ≫
        (α_ (electricAnyon k) (electricAnyon k) (electricAnyon k)).hom := by
  have hiso :
      (MonoidalCategory.whiskerRightIso (eeVacUnitIso k) (electricAnyon k) ≪≫
          λ_ (electricAnyon k)) =
        α_ (electricAnyon k) (electricAnyon k) (electricAnyon k) ≪≫
          MonoidalCategory.whiskerLeftIso (electricAnyon k) (eeVacUnitIso k) ≪≫
            ρ_ (electricAnyon k) := by
    apply Iso.ext
    simp only [Iso.trans_hom, MonoidalCategory.whiskerRightIso_hom,
      MonoidalCategory.whiskerLeftIso_hom]
    exact electric_linchpin k
  have h2 := congrArg Iso.inv hiso
  simp only [Iso.trans_inv, MonoidalCategory.whiskerRightIso_inv,
    MonoidalCategory.whiskerLeftIso_inv, Category.assoc] at h2
  rw [← Category.assoc, h2, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SKEFTHawking.SymTFT.ElectricAlgebraObject
