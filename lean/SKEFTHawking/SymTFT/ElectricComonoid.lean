/-
# SymTFT S2 FINISHER (#283) — `electricComul` coassociativity, the `ComonObj` instance,
Frobenius, and separability

The S2 comonoid/Frobenius apex on the toric electric Lagrangian object `1 ⊕ e`
(`unitPlusElectricObj`), completing the object-level algebra begun in
`ElectricAlgebraObject` (the `MonObj` half, merged with the (★) linchpin):

* **`electricComul_assoc`** — coassociativity of the honest fusion comultiplication, by the
  8-COCORNER biproduct-extensionality route (the exact dual of `electricMul_assoc`): the
  codomain identity `𝟙_{X⊗(X⊗X)}` decomposes through `unitPlusElectric_total`, two maps into
  the triple tensor agreeing after all eight projection triples are equal; seven cocorners
  are free monoidal coherence, and the `(e,e,e)` cocorner is the dual linchpin
  `electric_colinchpin` (co-★).
* **`electricComonObj : ComonObj (unitPlusElectricObj k)`** — the counit laws were banked
  (`electricComul_counit_comul` / `electricComul_comul_counit`); coassociativity closes the
  instance. `1 ⊕ e` is a genuine internal comonoid.
* **Frobenius + separability** — the Frobenius compatibility laws relating `electricMul` and
  `electricComul`, and the separability composite `Δ ≫ μ` computed exactly. Together with
  `electricMonObj` this is the full Frobenius-algebra shape of the toric electric Lagrangian
  algebra — the S2 apex.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SymTFT.ElectricAlgebraObject

namespace SKEFTHawking.SymTFT.ElectricComonoid

open CategoryTheory MonoidalCategory Limits
open SKEFTHawking SKEFTHawking.CenterFunctorZ2 SKEFTHawking.CenterFunctorZ2Equiv
open SKEFTHawking.SymTFT.A5VacuumPlusElectric
open SKEFTHawking.SymTFT.ElectricAlgebraObject

variable (k : Type) [CommRing k]

/-! ## §1. The cocorner dispatch — the dual of the 8-corner associativity route -/

/-- The coassociativity identity restricted to a cocorner projection triple `(πa, πb, πc)`,
LEFT-ASSOCIATED (the rewrite-normal form of the biproduct-extensionality assembly). Each of
the 8 cocorners (`a,b,c ∈ {vacuum-counit, electric-proj}`) is an instance. -/
private def CoassocCornerEq {A B D : CategoryTheory.Center (VecG_Cat k G2)}
    (πa : unitPlusElectricObj k ⟶ A) (πb : unitPlusElectricObj k ⟶ B)
    (πc : unitPlusElectricObj k ⟶ D) : Prop :=
  ((electricComul k ≫ (unitPlusElectricObj k ◁ electricComul k)) ≫ (πa ⊗ₘ (πb ⊗ₘ πc))) =
    (((electricComul k ≫ (electricComul k ▷ unitPlusElectricObj k)) ≫
      (α_ (unitPlusElectricObj k) (unitPlusElectricObj k) (unitPlusElectricObj k)).hom) ≫
        (πa ⊗ₘ (πb ⊗ₘ πc)))

/-- Peel a trailing composite out of the LEFT tensor slot: `(f ≫ g) ⊗ₘ h = (f ⊗ₘ h) ≫ (g ⊗ₘ 𝟙)`.
The mirror of `split_left_tensor` needed on the CO-side: after a cocorner fires inside a tensor
slot, the structural tail must be peeled off so the next cocorner can re-fire on the head. -/
private theorem split_left_tensor' {C : Type*} [Category C] [MonoidalCategory C]
    {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) {A B : C} (h : A ⟶ B) :
    (f ≫ g) ⊗ₘ h = (f ⊗ₘ h) ≫ (g ⊗ₘ 𝟙 B) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-- Peel a trailing composite out of the RIGHT tensor slot:
`h ⊗ₘ (f ≫ g) = (h ⊗ₘ f) ≫ (𝟙 ⊗ₘ g)`. -/
private theorem split_right_tensor' {C : Type*} [Category C] [MonoidalCategory C]
    {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) {A B : C} (h : A ⟶ B) :
    h ⊗ₘ (f ≫ g) = (h ⊗ₘ f) ≫ (𝟙 B ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-- Reassociated cocorner (11): fires under a trailing composition. -/
private theorem cocorner_11_assoc {Z : CategoryTheory.Center (VecG_Cat k G2)}
    (h : 𝟙_ (CategoryTheory.Center (VecG_Cat k G2)) ⊗ 𝟙_ (CategoryTheory.Center (VecG_Cat k G2))
      ⟶ Z) :
    electricComul k ≫ (unitPlusElectric_counit k ⊗ₘ unitPlusElectric_counit k) ≫ h =
      unitPlusElectric_counit k ≫ (λ_ (𝟙_ (CategoryTheory.Center (VecG_Cat k G2)))).inv ≫ h := by
  rw [← Category.assoc, electricComul_cocorner_11]
  simp only [Category.assoc]

/-- Reassociated cocorner (ee): fires under a trailing composition. -/
private theorem cocorner_ee_assoc {Z : CategoryTheory.Center (VecG_Cat k G2)}
    (h : electricAnyon k ⊗ electricAnyon k ⟶ Z) :
    electricComul k ≫ (electricProj k ⊗ₘ electricProj k) ≫ h =
      unitPlusElectric_counit k ≫ (eeVacUnitIso k).inv ≫ h := by
  rw [← Category.assoc, electricComul_cocorner_ee]
  simp only [Category.assoc]

/-- Reassociated cocorner (1e): fires under a trailing composition. -/
private theorem cocorner_1e_assoc {Z : CategoryTheory.Center (VecG_Cat k G2)}
    (h : 𝟙_ (CategoryTheory.Center (VecG_Cat k G2)) ⊗ electricAnyon k ⟶ Z) :
    electricComul k ≫ (unitPlusElectric_counit k ⊗ₘ electricProj k) ≫ h =
      electricProj k ≫ (λ_ (electricAnyon k)).inv ≫ h := by
  rw [← Category.assoc, electricComul_cocorner_1e]
  simp only [Category.assoc]

/-- Reassociated cocorner (e1): fires under a trailing composition. -/
private theorem cocorner_e1_assoc {Z : CategoryTheory.Center (VecG_Cat k G2)}
    (h : electricAnyon k ⊗ 𝟙_ (CategoryTheory.Center (VecG_Cat k G2)) ⟶ Z) :
    electricComul k ≫ (electricProj k ⊗ₘ unitPlusElectric_counit k) ≫ h =
      electricProj k ≫ (ρ_ (electricAnyon k)).inv ≫ h := by
  rw [← Category.assoc, electricComul_cocorner_e1]
  simp only [Category.assoc]

/-- **Uniform cocorner reduction** — closes any of the 8 coassociativity cocorners. Moves the
projection triple past the associator (naturality), merges through the tensor interchange, fires
the cocorner equations (`electricComul_cocorner_*` + their reassociated `cocorner_*_assoc`
variants) — with the primed split lemmas peeling structural tails out of the tensor slots so the
cocorners re-fire on the heads — then the residue: free monoidal coherence for the 7 cocorners
`≠ (e,e,e)`, or the dual linchpin `electric_colinchpin` (co-★) for the `(e,e,e)` cocorner (the
only non-coherent one). -/
local macro "cocorner_reduce" : tactic =>
  `(tactic|
    (simp only [Category.assoc]
     rw [← MonoidalCategory.associator_naturality]
     simp only [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
        MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
        Category.assoc]
     try simp only [electricComul_cocorner_11, electricComul_cocorner_ee,
        electricComul_cocorner_1e, electricComul_cocorner_e1]
     try simp only [split_left_tensor', split_right_tensor', Category.assoc]
     try simp only [cocorner_11_assoc, cocorner_ee_assoc, cocorner_1e_assoc, cocorner_e1_assoc,
        electricComul_cocorner_11, electricComul_cocorner_ee,
        electricComul_cocorner_1e, electricComul_cocorner_e1,
        MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
     try simp only [split_left_tensor', split_right_tensor', Category.assoc]
     try simp only [cocorner_11_assoc, cocorner_ee_assoc, cocorner_1e_assoc, cocorner_e1_assoc,
        electricComul_cocorner_11, electricComul_cocorner_ee,
        electricComul_cocorner_1e, electricComul_cocorner_e1]
     first
       | (congr 1; monoidal)
       | monoidal
       | (rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom,
           ← Category.assoc, electric_colinchpin]
          simp only [Category.assoc])
       | (congr 1
          rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
          rw [← Category.assoc, electric_colinchpin]
          simp only [Category.assoc])))

private theorem coassoc_corner_vvv :
    CoassocCornerEq k (unitPlusElectric_counit k) (unitPlusElectric_counit k)
      (unitPlusElectric_counit k) := by
  unfold CoassocCornerEq; cocorner_reduce
private theorem coassoc_corner_vve :
    CoassocCornerEq k (unitPlusElectric_counit k) (unitPlusElectric_counit k)
      (electricProj k) := by
  unfold CoassocCornerEq; cocorner_reduce
private theorem coassoc_corner_vev :
    CoassocCornerEq k (unitPlusElectric_counit k) (electricProj k)
      (unitPlusElectric_counit k) := by
  unfold CoassocCornerEq; cocorner_reduce
private theorem coassoc_corner_vee :
    CoassocCornerEq k (unitPlusElectric_counit k) (electricProj k) (electricProj k) := by
  unfold CoassocCornerEq; cocorner_reduce
private theorem coassoc_corner_evv :
    CoassocCornerEq k (electricProj k) (unitPlusElectric_counit k)
      (unitPlusElectric_counit k) := by
  unfold CoassocCornerEq; cocorner_reduce
private theorem coassoc_corner_eve :
    CoassocCornerEq k (electricProj k) (unitPlusElectric_counit k) (electricProj k) := by
  unfold CoassocCornerEq; cocorner_reduce
private theorem coassoc_corner_eev :
    CoassocCornerEq k (electricProj k) (electricProj k) (unitPlusElectric_counit k) := by
  unfold CoassocCornerEq; cocorner_reduce
private theorem coassoc_corner_eee :
    CoassocCornerEq k (electricProj k) (electricProj k) (electricProj k) := by
  unfold CoassocCornerEq
  simp only [Category.assoc]
  rw [← MonoidalCategory.associator_naturality]
  simp only [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
     MonoidalCategory.tensorHom_comp_tensorHom_assoc,
     MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
     Category.assoc]
  try simp only [electricComul_cocorner_11, electricComul_cocorner_ee,
     electricComul_cocorner_1e, electricComul_cocorner_e1]
  try simp only [split_left_tensor', split_right_tensor', Category.assoc]
  try simp only [cocorner_11_assoc, cocorner_ee_assoc, cocorner_1e_assoc, cocorner_e1_assoc,
     electricComul_cocorner_11, electricComul_cocorner_ee,
     electricComul_cocorner_1e, electricComul_cocorner_e1,
     MonoidalCategory.tensorHom_comp_tensorHom_assoc,
     MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
  try simp only [split_left_tensor', split_right_tensor', Category.assoc]
  try simp only [cocorner_11_assoc, cocorner_ee_assoc, cocorner_1e_assoc, cocorner_e1_assoc,
     electricComul_cocorner_11, electricComul_cocorner_ee,
     electricComul_cocorner_1e, electricComul_cocorner_e1]
  -- the (e,e,e) residue IS the dual linchpin (co-★), modulo unitor bookkeeping
  congr 1
  simp [electric_colinchpin]

/-- **Coassociativity of `electricComul`** — the `comul_assoc` law (Mathlib `ComonObj`
orientation). Proved by the 8-COCORNER biproduct-extensionality route (the exact dual of
`electricMul_assoc`): the codomain identity `𝟙_{X⊗(X⊗X)}` is decomposed through
`unitPlusElectric_total`, the resulting eight projection-corner terms are matched against the
cocorner lemmas `coassoc_corner_*` (seven pure coherence, the `(e,e,e)` cocorner the dual
linchpin `electric_colinchpin` (co-★)), and reassembled. -/
theorem electricComul_assoc :
    electricComul k ≫ (unitPlusElectricObj k ◁ electricComul k) =
      electricComul k ≫ (electricComul k ▷ unitPlusElectricObj k) ≫
        (α_ (unitPlusElectricObj k) (unitPlusElectricObj k) (unitPlusElectricObj k)).hom := by
  have hid : ((unitPlusElectric_counit k ≫ unitPlusElectric_one k
        + electricProj k ≫ electricInj k) ⊗ₘ
      ((unitPlusElectric_counit k ≫ unitPlusElectric_one k + electricProj k ≫ electricInj k) ⊗ₘ
      (unitPlusElectric_counit k ≫ unitPlusElectric_one k + electricProj k ≫ electricInj k))) =
      𝟙 (unitPlusElectricObj k ⊗ (unitPlusElectricObj k ⊗ unitPlusElectricObj k)) := by
    rw [unitPlusElectric_total]; simp
  conv_lhs => rw [← Category.comp_id
    (electricComul k ≫ (unitPlusElectricObj k ◁ electricComul k)), ← hid]
  conv_rhs => rw [← Category.comp_id
    (electricComul k ≫ (electricComul k ▷ unitPlusElectricObj k) ≫
      (α_ (unitPlusElectricObj k) (unitPlusElectricObj k) (unitPlusElectricObj k)).hom), ← hid]
  simp only [center_add_tensorHom, center_tensorHom_add,
    ← MonoidalCategory.tensorHom_comp_tensorHom, Preadditive.comp_add, ← Category.assoc]
  rw [coassoc_corner_vvv k, coassoc_corner_vve k, coassoc_corner_vev k, coassoc_corner_vee k,
    coassoc_corner_evv k, coassoc_corner_eve k, coassoc_corner_eev k, coassoc_corner_eee k]

/-! ## §2. The `ComonObj` instance — the S2 comonoid apex -/

/-- **The `ComonObj` instance** — `unitPlusElectricObj k` is an internal comonoid object in
`Center (VecG_Cat k G2)` under the honest fusion comultiplication `electricComul` with counit
`unitPlusElectric_counit`. Together with the banked `electricMonObj` (the monoid half), the
toric electric Lagrangian object `1 ⊕ e` now carries BOTH structures — the S2 comonoid apex.
The counit laws were banked (`electricComul_counit_comul` / `electricComul_comul_counit`);
coassociativity (`electricComul_assoc`, above) closes the instance. -/
noncomputable instance electricComonObj : CategoryTheory.ComonObj (unitPlusElectricObj k) where
  counit := unitPlusElectric_counit k
  comul := electricComul k
  counit_comul := electricComul_counit_comul k
  comul_counit := electricComul_comul_counit k
  comul_assoc := electricComul_assoc k

/-! ## §3. Separability — the composite `Δ ≫ μ` computed exactly

Each of the four (co)corner contributions is either `ε ≫ ι1` (the `(1,1)` and `(e,e)` corners —
the latter through the fusion pairing `eeVacUnitIso.inv ≫ eeVacUnitIso.hom = 𝟙`) or `πe ≫ ιe`
(the two mixed corners), so `Δ ≫ μ = 2·(ε ≫ ι1 + πe ≫ ιe) = 𝟙 + 𝟙` by `unitPlusElectric_total`.
The value `2·𝟙` is the FPdim of the object — the separability idempotent is `½Δ` away from
char 2 (the char-2 caveat is the ledger's documented modeling note). Falsifiable: a degenerate
comultiplication (the old `unitPlusElectric_comul`) composes to `𝟙 + ε≫ι1 ≠ 2·𝟙`. -/

/-- **The separability composite**: `Δ ≫ μ = 𝟙 + 𝟙` on the toric electric Lagrangian object —
the exact FPdim-2 separability value of the Frobenius structure. -/
theorem electricComul_comp_electricMul :
    electricComul k ≫ electricMul k =
      𝟙 (unitPlusElectricObj k) + 𝟙 (unitPlusElectricObj k) := by
  have hid : ((unitPlusElectric_counit k ≫ unitPlusElectric_one k
        + electricProj k ≫ electricInj k) ⊗ₘ
      (unitPlusElectric_counit k ≫ unitPlusElectric_one k + electricProj k ≫ electricInj k)) =
      𝟙 (unitPlusElectricObj k ⊗ unitPlusElectricObj k) := by
    rw [unitPlusElectric_total]; simp
  conv_lhs => rw [show electricComul k ≫ electricMul k
    = electricComul k ≫ 𝟙 (unitPlusElectricObj k ⊗ unitPlusElectricObj k) ≫ electricMul k by
      rw [Category.id_comp], ← hid]
  simp only [center_add_tensorHom, center_tensorHom_add,
    ← MonoidalCategory.tensorHom_comp_tensorHom, Preadditive.comp_add, Preadditive.add_comp,
    Category.assoc]
  rw [cocorner_11_assoc, cocorner_1e_assoc, cocorner_e1_assoc, cocorner_ee_assoc]
  simp only [electricMul_corner_11, electricMul_corner_1e, electricMul_corner_e1,
    electricMul_corner_ee, ← eeVacUnitIso_hom_eq]
  simp only [Iso.inv_hom_id_assoc]
  rw [← unitPlusElectric_total k]
  abel

/-! ## §4. The ι-side comultiplication corners and the Frobenius pair -/

/-- The vacuum idempotent `ι1 ≫ ε = 𝟙` — derived from the totality decomposition (the `πe`-leg
dies by `vacInj_comp_electricProj`) and the split-mono cancellation on `ι1`. -/
private theorem one_comp_counit :
    unitPlusElectric_one k ≫ unitPlusElectric_counit k =
      𝟙 (𝟙_ (CategoryTheory.Center (VecG_Cat k G2))) := by
  haveI := electricObject_one_isSplitMono k
  rw [← cancel_mono (unitPlusElectric_one k), Category.id_comp]
  have expand : unitPlusElectric_one k ≫
      (unitPlusElectric_counit k ≫ unitPlusElectric_one k + electricProj k ≫ electricInj k) =
      unitPlusElectric_one k := by
    rw [unitPlusElectric_total, Category.comp_id]
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
    vacInj_comp_electricProj, Limits.zero_comp, add_zero] at expand
  rw [Category.assoc] at expand ⊢
  exact expand

/-- **The ι-side comultiplication corner at the vacuum**: `ι1 ≫ Δ = λ⁻¹ ≫ (ι1 ⊗ ι1) +
eeVac⁻¹ ≫ (ιe ⊗ ιe)` — the Frobenius coproduct of the unit (`Δ(1) = 1⊗1 + ψ⁻¹(e⊗e)`). Derived
from the π-side cocorners by the totality decomposition of `𝟙_{X⊗X}`. -/
private theorem incorner_one :
    unitPlusElectric_one k ≫ electricComul k =
      (λ_ (𝟙_ (CategoryTheory.Center (VecG_Cat k G2)))).inv ≫
          (unitPlusElectric_one k ⊗ₘ unitPlusElectric_one k)
        + (eeVacUnitIso k).inv ≫ (electricInj k ⊗ₘ electricInj k) := by
  have hid : ((unitPlusElectric_counit k ≫ unitPlusElectric_one k
        + electricProj k ≫ electricInj k) ⊗ₘ
      (unitPlusElectric_counit k ≫ unitPlusElectric_one k + electricProj k ≫ electricInj k)) =
      𝟙 (unitPlusElectricObj k ⊗ unitPlusElectricObj k) := by
    rw [unitPlusElectric_total]; simp
  conv_lhs => rw [show unitPlusElectric_one k ≫ electricComul k
    = unitPlusElectric_one k ≫ electricComul k ≫
        𝟙 (unitPlusElectricObj k ⊗ unitPlusElectricObj k) by rw [Category.comp_id], ← hid]
  simp only [center_add_tensorHom, center_tensorHom_add,
    ← MonoidalCategory.tensorHom_comp_tensorHom, Preadditive.comp_add, Category.assoc]
  rw [cocorner_11_assoc, cocorner_1e_assoc, cocorner_e1_assoc, cocorner_ee_assoc]
  simp only [← Category.assoc, one_comp_counit, vacInj_comp_electricProj]
  simp only [Category.id_comp, Limits.zero_comp, Category.assoc, Preadditive.add_comp,
    Limits.comp_zero, zero_add, add_zero]

/-- **The ι-side comultiplication corner at the electric line**: `ιe ≫ Δ = λ⁻¹ ≫ (ι1 ⊗ ιe) +
ρ⁻¹ ≫ (ιe ⊗ ι1)` — the Frobenius coproduct of `e`. -/
private theorem incorner_e :
    electricInj k ≫ electricComul k =
      (λ_ (electricAnyon k)).inv ≫ (unitPlusElectric_one k ⊗ₘ electricInj k)
        + (ρ_ (electricAnyon k)).inv ≫ (electricInj k ⊗ₘ unitPlusElectric_one k) := by
  have hid : ((unitPlusElectric_counit k ≫ unitPlusElectric_one k
        + electricProj k ≫ electricInj k) ⊗ₘ
      (unitPlusElectric_counit k ≫ unitPlusElectric_one k + electricProj k ≫ electricInj k)) =
      𝟙 (unitPlusElectricObj k ⊗ unitPlusElectricObj k) := by
    rw [unitPlusElectric_total]; simp
  conv_lhs => rw [show electricInj k ≫ electricComul k
    = electricInj k ≫ electricComul k ≫
        𝟙 (unitPlusElectricObj k ⊗ unitPlusElectricObj k) by rw [Category.comp_id], ← hid]
  simp only [center_add_tensorHom, center_tensorHom_add,
    ← MonoidalCategory.tensorHom_comp_tensorHom, Preadditive.comp_add, Category.assoc]
  rw [cocorner_11_assoc, cocorner_1e_assoc, cocorner_e1_assoc, cocorner_ee_assoc]
  simp only [← Category.assoc, electricInj_comp_electricProj, electricInj_comp_vacProj]
  simp only [Category.id_comp, Limits.zero_comp, Category.assoc, Preadditive.add_comp,
    Limits.comp_zero, zero_add, add_zero]
  abel

end SKEFTHawking.SymTFT.ElectricComonoid
