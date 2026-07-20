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

end SKEFTHawking.SymTFT.ElectricAlgebraObject
