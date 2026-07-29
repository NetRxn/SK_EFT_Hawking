/-
# Phase 6r-prime A5 sub-ship (b) part 2a — Diagonal HalfBraiding data

This module attempts a substantive **`diagBiprodHalfBraiding`** building
on `CenterBiproducts.biprodBraidingIso`. The β data is
`biprodBraidingIso X Y U`; the monoidal + naturality axioms are
attempted via the Mathlib default `cat_disch` tactic.

The full HasBinaryBiproducts (Center C) instance requires either (i)
discharge of the HalfBraiding axioms via the explicit per-summand
tactic skeleton (Center.tensorObj template ~150 LoC) or (ii) substantive
categorical-coherence work that is the next Layer-B ship.

If `cat_disch` closes the axioms (which it does for many simple
HalfBraidings via Mathlib's built-in coherence database), then the
diagonal HalfBraiding ships here as a complete substantive object.

## Substantive content

The β data `biprodBraidingIso X Y U` is the M2 Layer A load-bearing
iso composition (distributor + per-summand half-braiding + co-
distributor). Whether or not `cat_disch` closes the axioms, this
module documents the construction path. If `cat_disch` fails for the
axioms, the next Layer-B ship would replace the `cat_disch` calls
with explicit per-summand reductions via `biprod.hom_ext'` +
`HalfBraiding.naturality`/`.monoidal` applied per-component.
-/
import SKEFTHawking.SymTFT.CenterBiproducts
import SKEFTHawking.SymTFT.CenterPreadditive

namespace SKEFTHawking.SymTFT

open CategoryTheory MonoidalCategory Limits CenterBiproducts

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C]

namespace CenterBiproductsHalfBraiding

-- A5(b)-pt2a substrate (HalfBraiding data); full HasBinaryBiproducts
-- (Center C) requires both this HalfBraiding data + BinaryBicone
-- structure with .comm conditions on each component morphism.
-- The monoidal + naturality axioms remain Layer-B follow-on.

/-- **Diagonal half-braiding β data on `X.1 ⊞ Y.1`** — the M2 Layer A
isomorphism `biprodBraidingIso X Y U`. This is the load-bearing data
of the would-be `HalfBraiding (X.1 ⊞ Y.1)` instance for A5(b)-pt2;
the monoidal + naturality axioms remain Layer-B follow-on. -/
noncomputable def diagBiprodBeta (X Y : CategoryTheory.Center C) (U : C) :
    (X.1 ⊞ Y.1) ⊗ U ≅ U ⊗ (X.1 ⊞ Y.1) :=
  biprodBraidingIso X Y U

/-- **Hom-direction of diagonal β** for downstream consumers. -/
noncomputable def diagBiprodBetaHom (X Y : CategoryTheory.Center C) (U : C) :
    (X.1 ⊞ Y.1) ⊗ U ⟶ U ⊗ (X.1 ⊞ Y.1) :=
  (diagBiprodBeta X Y U).hom

/-- **Inv-direction of diagonal β** for downstream consumers. -/
noncomputable def diagBiprodBetaInv (X Y : CategoryTheory.Center C) (U : C) :
    U ⊗ (X.1 ⊞ Y.1) ⟶ (X.1 ⊞ Y.1) ⊗ U :=
  (diagBiprodBeta X Y U).inv

/-- **`diagBiprodBeta` is an iso (forward-backward)** — automatic from
`Iso.trans` in the underlying `biprodBraidingIso`. -/
@[simp]
theorem diagBiprodBeta_hom_inv (X Y : CategoryTheory.Center C) (U : C) :
    diagBiprodBetaHom X Y U ≫ diagBiprodBetaInv X Y U = 𝟙 _ :=
  (diagBiprodBeta X Y U).hom_inv_id

/-- **`diagBiprodBeta` is an iso (backward-forward)** — automatic. -/
@[simp]
theorem diagBiprodBeta_inv_hom (X Y : CategoryTheory.Center C) (U : C) :
    diagBiprodBetaInv X Y U ≫ diagBiprodBetaHom X Y U = 𝟙 _ :=
  (diagBiprodBeta X Y U).inv_hom_id

/-! ## §2. Attempt to ship the full diagonal HalfBraiding

`cat_disch` (Mathlib's default categorical-discharger tactic) is
attempted as the proof for the monoidal + naturality axioms. -/

/-! ## §2. Per-summand biprod-naturality lemmas for `biprodBraidingIso`

The diagonal `biprodBraidingIso X Y U.hom` projects to component
HalfBraiding actions via `biprod.fst` and `biprod.snd` on the right
factor. These are the load-bearing lemmas for the per-summand
discharge of the HalfBraiding monoidal + naturality axioms. -/

/-- **`biprodBraidingIso_hom_inl`** — the `biprod.inl ▷ U` composition
with `biprodBraidingIso X Y U .hom` equals the X-component HalfBraiding
followed by `U ◁ biprod.inl`. This is the per-summand identity that
the diagonal HalfBraiding axioms reduce to via `biprod.hom_ext'`. -/
theorem biprodBraidingIso_hom_inl (X Y : CategoryTheory.Center C) (U : C) :
    (biprod.inl ▷ U) ≫ (CenterBiproducts.biprodBraidingIso X Y U).hom =
      (X.2.β U).hom ≫ (U ◁ biprod.inl) := by
  -- Strategy: reduce LHS via biprod composition lemmas + whiskerRight functoriality
  -- + biprod inl/fst/snd universal property + zero_whiskerRight.
  simp only [CenterBiproducts.biprodBraidingIso, Iso.trans_hom, biprod.mapIso_hom,
    Iso.symm_hom, Functor.mapBiprod_hom, Functor.mapBiprod_inv,
    Functor.id_obj]
  -- After simp: goal involves biprod.lift, biprod.map, biprod.desc with explicit whiskerings.
  -- Use biprod's universal property: prove via biprod.hom_ext post-composing with biprod.fst/biprod.snd.
  -- But the codomain is U ⊗ (X ⊞ Y) — not directly a biprod-target.
  -- Alternative: just rewrite step by step using biprod.lift composition + functoriality.
  -- (tensorRight U).map f = f ▷ U definitionally; (tensorLeft U).map f = U ◁ f.
  change (biprod.inl ▷ U) ≫
      biprod.lift (biprod.fst ▷ U) (biprod.snd ▷ U) ≫
        biprod.map (X.2.β U).hom (Y.2.β U).hom ≫
          biprod.desc (U ◁ biprod.inl) (U ◁ biprod.inr) = _
  -- Step 1: (biprod.inl ▷ U) ≫ biprod.lift (biprod.fst ▷ U) (biprod.snd ▷ U) = biprod.inl (via universal property).
  have h1 : (biprod.inl ▷ U) ≫ biprod.lift (biprod.fst ▷ U) (biprod.snd ▷ U) =
      (biprod.inl : X.1 ⊗ U ⟶ (X.1 ⊗ U) ⊞ (Y.1 ⊗ U)) := by
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst,
          ← MonoidalCategory.comp_whiskerRight, biprod.inl_fst,
          MonoidalCategory.id_whiskerRight, biprod.inl_fst]
    · rw [Category.assoc, biprod.lift_snd,
          ← MonoidalCategory.comp_whiskerRight, biprod.inl_snd,
          MonoidalPreadditive.zero_whiskerRight, biprod.inl_snd]
  rw [← Category.assoc, h1, ← Category.assoc, biprod.inl_map,
      Category.assoc, biprod.inl_desc]

theorem biprodBraidingIso_hom_inr (X Y : CategoryTheory.Center C) (U : C) :
    (biprod.inr ▷ U) ≫ (CenterBiproducts.biprodBraidingIso X Y U).hom =
      (Y.2.β U).hom ≫ (U ◁ biprod.inr) := by
  simp only [CenterBiproducts.biprodBraidingIso, Iso.trans_hom, biprod.mapIso_hom,
    Iso.symm_hom, Functor.mapBiprod_hom, Functor.mapBiprod_inv]
  change (biprod.inr ▷ U) ≫
      biprod.lift (biprod.fst ▷ U) (biprod.snd ▷ U) ≫
        biprod.map (X.2.β U).hom (Y.2.β U).hom ≫
          biprod.desc (U ◁ biprod.inl) (U ◁ biprod.inr) = _
  have h1 : (biprod.inr ▷ U) ≫ biprod.lift (biprod.fst ▷ U) (biprod.snd ▷ U) =
      (biprod.inr : Y.1 ⊗ U ⟶ (X.1 ⊗ U) ⊞ (Y.1 ⊗ U)) := by
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst,
          ← MonoidalCategory.comp_whiskerRight, biprod.inr_fst,
          MonoidalPreadditive.zero_whiskerRight, biprod.inr_fst]
    · rw [Category.assoc, biprod.lift_snd,
          ← MonoidalCategory.comp_whiskerRight, biprod.inr_snd,
          MonoidalCategory.id_whiskerRight, biprod.inr_snd]
  rw [← Category.assoc, h1, ← Category.assoc, biprod.inr_map,
      Category.assoc, biprod.inr_desc]

/-! ## §2b. Dual per-summand reductions — `biprodBraidingIso ≫ (U ◁ biprod.fst)`

The DUAL lemmas to `biprodBraidingIso_hom_inl/inr`: composing the diagonal
half-braiding on the OUT direction with `U ◁ biprod.fst` (resp. `U ◁
biprod.snd`) projects to the per-component half-braiding followed by
`biprod.fst ▷ U` (resp. `biprod.snd ▷ U`). These are the substrate for
the ComonObj.counit (resp. dual) ship on the diagonal carrier. -/

/-- **`biprodBraidingIso_hom_fst`** — composing the diagonal braiding's
`.hom` with `U ◁ biprod.fst` projects to the X-component half-braiding
composed with `biprod.fst ▷ U`. Dual of `biprodBraidingIso_hom_inl`. -/
theorem biprodBraidingIso_hom_fst (X Y : CategoryTheory.Center C) (U : C) :
    (CenterBiproducts.biprodBraidingIso X Y U).hom ≫ (U ◁ biprod.fst) =
      (biprod.fst ▷ U) ≫ (X.2.β U).hom := by
  simp only [CenterBiproducts.biprodBraidingIso, Iso.trans_hom, biprod.mapIso_hom,
    Iso.symm_hom, Functor.mapBiprod_hom, Functor.mapBiprod_inv]
  change (biprod.lift (biprod.fst ▷ U) (biprod.snd ▷ U) ≫
      biprod.map (X.2.β U).hom (Y.2.β U).hom ≫
        biprod.desc (U ◁ biprod.inl) (U ◁ biprod.inr)) ≫ (U ◁ biprod.fst) = _
  -- Reduce desc ≫ (U ◁ fst) via biprod.inl_fst / biprod.inr_fst at U-tensor level.
  have h_desc : (biprod.desc (U ◁ biprod.inl) (U ◁ biprod.inr)) ≫ (U ◁ biprod.fst) =
      (biprod.fst : (U ⊗ X.1) ⊞ (U ⊗ Y.1) ⟶ U ⊗ X.1) := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc,
          ← MonoidalCategory.whiskerLeft_comp, biprod.inl_fst,
          MonoidalCategory.whiskerLeft_id, biprod.inl_fst]
    · rw [← Category.assoc, biprod.inr_desc,
          ← MonoidalCategory.whiskerLeft_comp, biprod.inr_fst,
          MonoidalPreadditive.whiskerLeft_zero, biprod.inr_fst]
  rw [Category.assoc, Category.assoc, h_desc, biprod.map_fst, ← Category.assoc,
      biprod.lift_fst]

/-- **`biprodBraidingIso_hom_snd`** — analogous to `biprodBraidingIso_hom_fst`
for the Y summand. -/
theorem biprodBraidingIso_hom_snd (X Y : CategoryTheory.Center C) (U : C) :
    (CenterBiproducts.biprodBraidingIso X Y U).hom ≫ (U ◁ biprod.snd) =
      (biprod.snd ▷ U) ≫ (Y.2.β U).hom := by
  simp only [CenterBiproducts.biprodBraidingIso, Iso.trans_hom, biprod.mapIso_hom,
    Iso.symm_hom, Functor.mapBiprod_hom, Functor.mapBiprod_inv]
  change (biprod.lift (biprod.fst ▷ U) (biprod.snd ▷ U) ≫
      biprod.map (X.2.β U).hom (Y.2.β U).hom ≫
        biprod.desc (U ◁ biprod.inl) (U ◁ biprod.inr)) ≫ (U ◁ biprod.snd) = _
  have h_desc : (biprod.desc (U ◁ biprod.inl) (U ◁ biprod.inr)) ≫ (U ◁ biprod.snd) =
      (biprod.snd : (U ⊗ X.1) ⊞ (U ⊗ Y.1) ⟶ U ⊗ Y.1) := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc,
          ← MonoidalCategory.whiskerLeft_comp, biprod.inl_snd,
          MonoidalPreadditive.whiskerLeft_zero, biprod.inl_snd]
    · rw [← Category.assoc, biprod.inr_desc,
          ← MonoidalCategory.whiskerLeft_comp, biprod.inr_snd,
          MonoidalCategory.whiskerLeft_id, biprod.inr_snd]
  rw [Category.assoc, Category.assoc, h_desc, biprod.map_snd, ← Category.assoc,
      biprod.lift_snd]

/-! ## §3. Biproduct-tensor ext lemma — Mathlib-PR-quality substrate

The key technical lemma: morphisms `(X ⊞ Y) ⊗ U ⟶ W` are determined by
their compositions with `biprod.inl ▷ U` and `biprod.inr ▷ U`. Follows
from `Functor.mapBiprod (tensorRight U) X Y` being an iso whose inverse
equals `biprod.desc (biprod.inl ▷ U) (biprod.inr ▷ U)`.

This is the substrate that enables the per-summand discharge of the
diagonal HalfBraiding axioms below. -/

/-- **`biprodTensor_hom_ext`** — morphisms out of `(X ⊞ Y) ⊗ U` are
determined by their compositions with `biprod.inl ▷ U` and `biprod.inr ▷
U`. Mathlib-PR-quality lemma; follows from `tensorRight U` preserving
binary biproducts. -/
theorem biprodTensor_hom_ext {X Y : C} {U W : C} {f g : (X ⊞ Y) ⊗ U ⟶ W}
    (h_inl : (biprod.inl ▷ U) ≫ f = (biprod.inl ▷ U) ≫ g)
    (h_inr : (biprod.inr ▷ U) ≫ f = (biprod.inr ▷ U) ≫ g) :
    f = g := by
  set e := Functor.mapBiprod (tensorRight U) X Y with e_def
  have inv_inl : biprod.inl ≫ e.inv = biprod.inl ▷ U := by
    rw [e_def]; simp; exact biprod.inl_desc _ _
  have inv_inr : biprod.inr ≫ e.inv = biprod.inr ▷ U := by
    rw [e_def]; simp; exact biprod.inr_desc _ _
  have key : e.inv ≫ f = e.inv ≫ g := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, ← Category.assoc, inv_inl]; exact h_inl
    · rw [← Category.assoc, ← Category.assoc, inv_inr]; exact h_inr
  exact (cancel_epi e.inv).mp key

/-! ## §4. Diagonal HalfBraiding monoidal + naturality axioms -/

/-- **Naturality of the diagonal half-braiding** — discharged per-summand
via `biprodTensor_hom_ext` + `biprodBraidingIso_hom_inl`/`_inr` + per-
component `HalfBraiding.naturality` for `X.2` / `Y.2` + `whisker_exchange`. -/
theorem diagBiprodBeta_naturality (X Y : CategoryTheory.Center C) {U U' : C}
    (f : U ⟶ U') :
    ((X.1 ⊞ Y.1) ◁ f) ≫ (biprodBraidingIso X Y U').hom =
      (biprodBraidingIso X Y U).hom ≫ (f ▷ (X.1 ⊞ Y.1)) := by
  apply biprodTensor_hom_ext
  · calc (biprod.inl ▷ U) ≫ ((X.1 ⊞ Y.1) ◁ f) ≫ (biprodBraidingIso X Y U').hom
        = (X.1 ◁ f) ≫ (biprod.inl ▷ U') ≫ (biprodBraidingIso X Y U').hom := by
          rw [← Category.assoc, ← whisker_exchange, Category.assoc]
      _ = (X.1 ◁ f) ≫ (X.2.β U').hom ≫ (U' ◁ biprod.inl) := by
          rw [biprodBraidingIso_hom_inl]
      _ = (X.2.β U).hom ≫ (f ▷ X.1) ≫ (U' ◁ biprod.inl) := by
          rw [← Category.assoc, X.2.naturality, Category.assoc]
      _ = (X.2.β U).hom ≫ (U ◁ biprod.inl) ≫ (f ▷ (X.1 ⊞ Y.1)) := by
          rw [← Category.assoc, whisker_exchange, Category.assoc]
      _ = (biprod.inl ▷ U) ≫ (biprodBraidingIso X Y U).hom ≫ (f ▷ (X.1 ⊞ Y.1)) := by
          rw [← Category.assoc, ← biprodBraidingIso_hom_inl, Category.assoc]
  · calc (biprod.inr ▷ U) ≫ ((X.1 ⊞ Y.1) ◁ f) ≫ (biprodBraidingIso X Y U').hom
        = (Y.1 ◁ f) ≫ (biprod.inr ▷ U') ≫ (biprodBraidingIso X Y U').hom := by
          rw [← Category.assoc, ← whisker_exchange, Category.assoc]
      _ = (Y.1 ◁ f) ≫ (Y.2.β U').hom ≫ (U' ◁ biprod.inr) := by
          rw [biprodBraidingIso_hom_inr]
      _ = (Y.2.β U).hom ≫ (f ▷ Y.1) ≫ (U' ◁ biprod.inr) := by
          rw [← Category.assoc, Y.2.naturality, Category.assoc]
      _ = (Y.2.β U).hom ≫ (U ◁ biprod.inr) ≫ (f ▷ (X.1 ⊞ Y.1)) := by
          rw [← Category.assoc, whisker_exchange, Category.assoc]
      _ = (biprod.inr ▷ U) ≫ (biprodBraidingIso X Y U).hom ≫ (f ▷ (X.1 ⊞ Y.1)) := by
          rw [← Category.assoc, ← biprodBraidingIso_hom_inr, Category.assoc]

/-- **Monoidal coherence of the diagonal half-braiding** — discharged
per-summand via `biprodTensor_hom_ext` + `biprodBraidingIso_hom_inl`/`_inr`
+ per-component `HalfBraiding.monoidal` for `X.2` / `Y.2` + a 5-step
chain of associator naturalities + functor distributions + monoidal
coherence. The RHS reduction (post per-summand projection) uses:
1. `associator_inv_naturality_left` to push `biprod.inl ▷ (U⊗U')` past `(α_).inv`.
2. `← comp_whiskerRight` to combine `(biprod.inl ▷ U) ▷ U'` with `(biprodBraidingIso X Y U).hom ▷ U'`.
3. `biprodBraidingIso_hom_inl` to reduce `(biprod.inl ▷ U) ≫ (biprodBraidingIso X Y U).hom`.
4. `associator_naturality_middle` to push `(U ◁ biprod.inl) ▷ U'` past `(α_).hom`.
5. `← whiskerLeft_comp` to combine `U ◁ (biprod.inl ▷ U')` with `U ◁ (biprodBraidingIso X Y U').hom`.
6. `biprodBraidingIso_hom_inl` again to reduce `(biprod.inl ▷ U') ≫ (biprodBraidingIso X Y U').hom`.
7. `associator_inv_naturality_right` to push `U ◁ U' ◁ biprod.inl` past `(α_).inv`.

After both reductions, the equality is pure monoidal coherence. -/
theorem diagBiprodBeta_monoidal (X Y : CategoryTheory.Center C) (U U' : C) :
    (biprodBraidingIso X Y (U ⊗ U')).hom =
      (α_ (X.1 ⊞ Y.1) U U').inv ≫
        ((biprodBraidingIso X Y U).hom ▷ U') ≫
          (α_ U (X.1 ⊞ Y.1) U').hom ≫
            (U ◁ (biprodBraidingIso X Y U').hom) ≫
              (α_ U U' (X.1 ⊞ Y.1)).inv := by
  apply biprodTensor_hom_ext
  · -- inl case: reduce LHS via inl_lemma + X.2.monoidal; reduce RHS via 7-step chain
    rw [biprodBraidingIso_hom_inl, X.2.monoidal,
        associator_inv_naturality_left_assoc,
        ← comp_whiskerRight_assoc, biprodBraidingIso_hom_inl, comp_whiskerRight_assoc,
        associator_naturality_middle_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, biprodBraidingIso_hom_inl,
        MonoidalCategory.whiskerLeft_comp_assoc,
        associator_inv_naturality_right]
    monoidal
  · rw [biprodBraidingIso_hom_inr, Y.2.monoidal,
        associator_inv_naturality_left_assoc,
        ← comp_whiskerRight_assoc, biprodBraidingIso_hom_inr, comp_whiskerRight_assoc,
        associator_naturality_middle_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, biprodBraidingIso_hom_inr,
        MonoidalCategory.whiskerLeft_comp_assoc,
        associator_inv_naturality_right]
    monoidal

/-- **The diagonal `HalfBraiding (X.1 ⊞ Y.1)` — A5(b)-pt2 FULL SHIP**.
The β data is `biprodBraidingIso`; monoidal + naturality axioms are
discharged via the per-summand reduction `biprodTensor_hom_ext` +
component `HalfBraiding.monoidal/naturality` of `X.2` / `Y.2`. -/
noncomputable def diagBiprodHalfBraiding (X Y : CategoryTheory.Center C) :
    HalfBraiding (X.1 ⊞ Y.1) where
  β U := biprodBraidingIso X Y U
  monoidal U U' := diagBiprodBeta_monoidal X Y U U'
  naturality f := diagBiprodBeta_naturality X Y f

end CenterBiproductsHalfBraiding

end SKEFTHawking.SymTFT
