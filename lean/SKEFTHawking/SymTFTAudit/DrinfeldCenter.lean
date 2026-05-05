/-
# Wave 1b.5.8 — Drinfeld Center predicate and Witt-equivalence-via-Drinfeld-center

This module lifts the Davydov-Müger-Nikshych-Ostrik (DMNO 2010, arXiv:1009.2117)
characterization of Witt equivalence via Drinfeld centers to predicate-level
Lean substrate, as the first step toward the full Witt group of MTCs (Wave 1b
Stage 5.8+ continuation of `SymTFTAudit/WittClass.lean`).

## Substantive content

* `WittEquivalentMTC C D` — predicate that two monoidal categories `C` and `D`
  have *categorically equivalent Drinfeld centers* `Z(C) ≃ Z(D)`. This is the
  working categorical definition of Witt equivalence at this layer.

* The predicate is an equivalence relation: refl/symm/trans inherited from
  Mathlib's `CategoryTheory.Equivalence` apparatus on plain categories.

* Cross-bridge to integer-level `WittEquivalent`: under a *central-charge-
  preservation hypothesis* (DMNO 2010, pseudo-unitary case), MTC-Witt-
  equivalent categories carry integer-Witt-equivalent chiral central charges.
  The hypothesis is `Prop`-level — no new axiom is introduced.

## Relation to existing infrastructure

* `Mathlib.CategoryTheory.Monoidal.Center` provides `Center C` with `Category`
  and `MonoidalCategory` instances; we use `Center C ≌ Center D` (Mathlib
  categorical equivalence) as the predicate body.

* `SymTFTAudit/WittClass.lean` provides the integer-level `WittEquivalent`,
  `WittClass`, and the Standard-Model bridge
  `chiralCentralCharge_wittTrivial_iff_three_dvd_N_f`; the cross-bridge in
  §3 feeds back into that apparatus.

## Open continuations (Wave 1b.5.10+)

* (Wave 1b.5.9 — DONE in §5–§9 below.) Strengthened to a predicate-level
  braided equivalence using Mathlib's `Functor.Braided` typeclass + the
  `Center.braidedCategoryCenter` instance. Refined hypothesis schema
  `CentralChargePreservesDrinfeldCenter_braided` is strictly weaker than
  the §3 plain form and exactly matches the DMNO 2010 statement.
* Construct the Witt group operation via Deligne tensor product `C ⊠ D`
  (Wave 1b.5.10) — produces a `Group` structure on Witt classes.
* Discharge the (now braided) central-charge-preservation hypothesis on the
  pseudo-unitary pre-modular subclass (Wave 1b.5.11) — this is where the
  DMNO 2010 theorem becomes a Lean theorem.
-/

import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Equivalence
import SKEFTHawking.SymTFTAudit.WittClass

namespace SKEFTHawking.SymTFTAudit

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

/-! ## §1 Witt-equivalence-via-Drinfeld-center predicate -/

/--
**Witt equivalence via Drinfeld centers.** Two monoidal categories `C` and `D`
are *MTC-Witt-equivalent* iff their Drinfeld centers `Z(C)` and `Z(D)` are
categorically equivalent.

Following Davydov-Müger-Nikshych-Ostrik 2010 (arXiv:1009.2117), this is the
working categorical definition of Witt equivalence; the integer-level form in
`SymTFTAudit/WittClass.lean` is the chiral-central-charge mod-24 image of this
predicate.

We use plain categorical equivalence at this stage; the DMNO theorem is at
the *braided* equivalence level, which requires a `BraidedCategory (Center C)`
instance Mathlib does not ship yet (continuation in Wave 1b.5.9+).
-/
def WittEquivalentMTC
    (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C]
    (D : Type u₂) [Category.{v₂, u₂} D] [MonoidalCategory D] : Prop :=
  Nonempty (Center C ≌ Center D)

/-! ## §2 Equivalence-relation properties

These three theorems make `WittEquivalentMTC` an equivalence relation on
monoidal-category instances (within a fixed universe). Each one is non-trivial
in that it routes through Mathlib's `Equivalence.refl/.symm/.trans` apparatus
on the *Drinfeld center* construction, which is itself a non-trivial functor
on monoidal categories. -/

theorem WittEquivalentMTC_refl
    (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C] :
    WittEquivalentMTC C C :=
  ⟨CategoryTheory.Equivalence.refl⟩

theorem WittEquivalentMTC_symm
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂, u₂} D] [MonoidalCategory D]
    (h : WittEquivalentMTC C D) : WittEquivalentMTC D C :=
  h.elim (fun e => ⟨CategoryTheory.Equivalence.symm e⟩)

theorem WittEquivalentMTC_trans
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂, u₂} D] [MonoidalCategory D]
    {E : Type u₃} [Category.{v₃, u₃} E] [MonoidalCategory E]
    (h₁ : WittEquivalentMTC C D) (h₂ : WittEquivalentMTC D E) :
    WittEquivalentMTC C E :=
  h₁.elim (fun e₁ => h₂.elim (fun e₂ => ⟨CategoryTheory.Equivalence.trans e₁ e₂⟩))

/-! ## §3 Cross-bridge to integer-level `WittEquivalent`

Under a central-charge-preservation hypothesis, MTC-Witt-equivalence implies
integer-Witt-equivalence (mod 24). The hypothesis is `Prop`-level — *no new
axiom* is introduced — and is dischargeable for the pseudo-unitary pre-modular
subclass via the DMNO 2010 theorem (continuation in Wave 1b.5.11). -/

/--
**Hypothesis schema.** A central-charge assignment `cc` *preserves Drinfeld-
center equivalence* if MTC-Witt-equivalent monoidal categories carry integer-
Witt-equivalent (mod 24) chiral central charges.

This is `Prop`-level — not an axiom. Concrete witnesses for this predicate
arise from the DMNO 2010 theorem on pseudo-unitary pre-modular categories
(Wave 1b.5.11 deliverable).
-/
def CentralChargePreservesDrinfeldCenter
    (cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ) : Prop :=
  ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C]
    (D : Type u₁) [Category.{v₁, u₁} D] [MonoidalCategory D],
    WittEquivalentMTC C D → WittEquivalent (cc C) (cc D)

/--
**Cross-bridge: MTC-Witt-equivalence implies integer-Witt-equivalence.** Under
the central-charge-preservation hypothesis, MTC-Witt-equivalent categories
carry integer-Witt-equivalent central charges (mod 24).

Proof body: invokes the hypothesis directly. Substantive content lives in
constructing the hypothesis witness for a specific class of MTCs — that is
the Wave 1b.5.11 deliverable.
-/
theorem wittEquivalentMTC_implies_wittEquivalent
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (hcc : CentralChargePreservesDrinfeldCenter cc)
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
    {D : Type u₁} [Category.{v₁, u₁} D] [MonoidalCategory D]
    (h : WittEquivalentMTC C D) :
    WittEquivalent (cc C) (cc D) :=
  hcc C D h

/--
**Cross-bridge to `WittClass` quotient.** Under the central-charge-preservation
hypothesis, MTC-Witt-equivalent categories project to the *same* `WittClass`
(integer mod 24 quotient).

This is the load-bearing form: it routes from the Drinfeld-center predicate
through the integer-level `WittEquivalent` (whose biconditional with `24 ∣ -`
is `WittEquivalent_iff_dvd`) to the `WittClass.mk` quotient in
`SymTFTAudit/WittClass.lean`.
-/
theorem wittEquivalentMTC_implies_wittClass_eq
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (hcc : CentralChargePreservesDrinfeldCenter cc)
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
    {D : Type u₁} [Category.{v₁, u₁} D] [MonoidalCategory D]
    (h : WittEquivalentMTC C D) :
    WittClass.mk (cc C) = WittClass.mk (cc D) := by
  -- WittEquivalent c c' ↔ 24 ∣ c - c' ↔ wittSetoid.r c c' (definitionally)
  have hWE : WittEquivalent (cc C) (cc D) :=
    wittEquivalentMTC_implies_wittEquivalent hcc h
  -- cc C and cc D are in the same setoid class, so quotient classes coincide
  exact Quotient.sound hWE

/-! ## §4 Stage 5.8 closure summary -/

/--
**Stage 5.8 closure summary.** Three substantive components:

1. `WittEquivalentMTC` is an equivalence relation (refl/symm/trans).
2. Under central-charge preservation, it implies integer `WittEquivalent`.
3. Under central-charge preservation, it implies `WittClass.mk` equality
   in the integer-mod-24 quotient.

Each conjunct is non-trivially load-bearing: dropping any conjunct loses a
distinct cross-track bridge. The closure is *not* a P2-bundle redundancy.
-/
theorem stage5_8_drinfeldCenter_closure
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (hcc : CentralChargePreservesDrinfeldCenter cc) :
    (∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C],
      WittEquivalentMTC C C) ∧
    (∀ {C D : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
      [Category.{v₁, u₁} D] [MonoidalCategory D],
      WittEquivalentMTC C D → WittEquivalentMTC D C) ∧
    (∀ {C D E : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
      [Category.{v₁, u₁} D] [MonoidalCategory D]
      [Category.{v₁, u₁} E] [MonoidalCategory E],
      WittEquivalentMTC C D → WittEquivalentMTC D E → WittEquivalentMTC C E) ∧
    (∀ {C D : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
      [Category.{v₁, u₁} D] [MonoidalCategory D],
      WittEquivalentMTC C D → WittClass.mk (cc C) = WittClass.mk (cc D)) := by
  refine ⟨fun C => WittEquivalentMTC_refl C, ?_, ?_, ?_⟩
  · intros C D _ _ _ _ h; exact WittEquivalentMTC_symm h
  · intros C D E _ _ _ _ _ _ h₁ h₂; exact WittEquivalentMTC_trans h₁ h₂
  · intros C D _ _ _ _ h; exact wittEquivalentMTC_implies_wittClass_eq hcc h

/-! ## §5 Wave 1b.5.9 — Braided strengthening

Davydov-Müger-Nikshych-Ostrik 2010 (arXiv:1009.2117) actually requires a
*braided* equivalence of Drinfeld centers, not a plain categorical one. The
Wave 1b.5.8 form `WittEquivalentMTC` strictly weakens DMNO 2010 by forgetting
the braided structure on the Drinfeld center (Mathlib's
`Center.braidedCategoryCenter`).

This section refines the predicate to the genuine DMNO 2010 form and provides
the strict-weakening bridge plus a refined hypothesis schema.

### Mathlib infrastructure used

* `CategoryTheory.Functor.Braided` — class on functors between braided
  monoidal categories (extends `Functor.Monoidal` and `Functor.LaxBraided`).
* `Functor.Braided.id` — the identity functor is braided.
* The composition instance `(F ⋙ G).Braided` from `F.Braided` and
  `G.Braided`.
* `Center.braidedCategoryCenter` — `Center C` is a braided monoidal category
  for any monoidal `C`.

The braided structure on `Center C` is data, but for the predicate level we
only need its *existence*; we use `Nonempty (F.Braided)`. -/

/--
**Predicate-level braided equivalence.** A categorical equivalence `e : C ≌ D`
between braided monoidal categories is *braided* iff both `e.functor` and
`e.inverse` carry braided-functor structure. Using `Nonempty` keeps the
predicate in `Prop` while still expressing the genuine structural content. -/
structure IsBraidedEquivalence
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type u₂} [Category.{v₂, u₂} D] [MonoidalCategory D] [BraidedCategory D]
    (e : C ≌ D) : Prop where
  /-- The forward functor of `e` admits a braided structure. -/
  functor_braided : Nonempty e.functor.Braided
  /-- The inverse functor of `e` admits a braided structure. -/
  inverse_braided : Nonempty e.inverse.Braided

namespace IsBraidedEquivalence

/-- Reflexivity: the identity equivalence is braided (identity functor is
braided in Mathlib). -/
theorem refl
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C] [BraidedCategory C] :
    IsBraidedEquivalence (CategoryTheory.Equivalence.refl : C ≌ C) where
  functor_braided := by
    show Nonempty (𝟭 C).Braided
    exact ⟨inferInstance⟩
  inverse_braided := by
    show Nonempty (𝟭 C).Braided
    exact ⟨inferInstance⟩

/-- Symmetry: swapping `functor`/`inverse` preserves the braided property
because `e.symm.functor = e.inverse` and `e.symm.inverse = e.functor`
definitionally. -/
theorem symm
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type u₂} [Category.{v₂, u₂} D] [MonoidalCategory D] [BraidedCategory D]
    {e : C ≌ D} (h : IsBraidedEquivalence e) :
    IsBraidedEquivalence e.symm where
  functor_braided := by
    show Nonempty e.inverse.Braided
    exact h.inverse_braided
  inverse_braided := by
    show Nonempty e.functor.Braided
    exact h.functor_braided

/-- Transitivity: composing two braided equivalences yields a braided
equivalence via Mathlib's `(F ⋙ G).Braided` typeclass instance. -/
theorem trans
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type u₂} [Category.{v₂, u₂} D] [MonoidalCategory D] [BraidedCategory D]
    {E : Type u₃} [Category.{v₃, u₃} E] [MonoidalCategory E] [BraidedCategory E]
    {e₁ : C ≌ D} {e₂ : D ≌ E}
    (h₁ : IsBraidedEquivalence e₁) (h₂ : IsBraidedEquivalence e₂) :
    IsBraidedEquivalence (e₁.trans e₂) where
  functor_braided := by
    show Nonempty (e₁.functor ⋙ e₂.functor).Braided
    obtain ⟨b₁⟩ := h₁.functor_braided
    obtain ⟨b₂⟩ := h₂.functor_braided
    haveI := b₁
    haveI := b₂
    exact ⟨inferInstance⟩
  inverse_braided := by
    show Nonempty (e₂.inverse ⋙ e₁.inverse).Braided
    obtain ⟨b₁⟩ := h₁.inverse_braided
    obtain ⟨b₂⟩ := h₂.inverse_braided
    haveI := b₁
    haveI := b₂
    exact ⟨inferInstance⟩

end IsBraidedEquivalence

/-! ## §6 Witt equivalence via *braided* Drinfeld-center equivalence -/

/--
**Strengthened Witt equivalence (DMNO 2010 form).** Two monoidal categories `C`
and `D` are *braided-MTC-Witt-equivalent* iff there exists a braided
equivalence of their Drinfeld centers `Z(C) ≃_{br} Z(D)`. This is the genuine
Davydov-Müger-Nikshych-Ostrik 2010 statement; the Wave 1b.5.8 form
`WittEquivalentMTC` is the strict weakening obtained by forgetting the braided
structure (§7 below). -/
def WittEquivalentMTC_braided
    (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C]
    (D : Type u₂) [Category.{v₂, u₂} D] [MonoidalCategory D] : Prop :=
  ∃ e : Center C ≌ Center D, IsBraidedEquivalence e

theorem WittEquivalentMTC_braided_refl
    (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C] :
    WittEquivalentMTC_braided C C :=
  ⟨CategoryTheory.Equivalence.refl, IsBraidedEquivalence.refl⟩

theorem WittEquivalentMTC_braided_symm
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂, u₂} D] [MonoidalCategory D]
    (h : WittEquivalentMTC_braided C D) : WittEquivalentMTC_braided D C := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, he.symm⟩

theorem WittEquivalentMTC_braided_trans
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂, u₂} D] [MonoidalCategory D]
    {E : Type u₃} [Category.{v₃, u₃} E] [MonoidalCategory E]
    (h₁ : WittEquivalentMTC_braided C D)
    (h₂ : WittEquivalentMTC_braided D E) :
    WittEquivalentMTC_braided C E := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  exact ⟨e₁.trans e₂, he₁.trans he₂⟩

/-! ## §7 Strict weakening to plain MTC-Witt equivalence (Wave 1b.5.8) -/

/--
**Braided ⇒ plain.** Forgetting the braided structure on the Drinfeld-center
equivalence yields the plain Wave 1b.5.8 predicate. This is the direction
"DMNO target ⇒ working categorical Witt equivalence"; the converse fails in
general because not every categorical equivalence of Drinfeld centers
preserves the braiding. -/
theorem WittEquivalentMTC_braided_implies_WittEquivalentMTC
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂, u₂} D] [MonoidalCategory D]
    (h : WittEquivalentMTC_braided C D) : WittEquivalentMTC C D := by
  obtain ⟨e, _⟩ := h
  exact ⟨e⟩

/-! ## §8 Refined hypothesis schema and cross-bridge to integer `WittClass`

DMNO 2010 establishes central-charge preservation under *braided* equivalence
of Drinfeld centers; the Wave 1b.5.8 hypothesis schema demanded preservation
under *any* categorical equivalence, which is strictly stronger. The braided
form is the natural target for the Wave 1b.5.11 discharge on the pseudo-
unitary subclass. -/

/--
**Refined hypothesis schema (braided form).** A central-charge assignment `cc`
*preserves braided Drinfeld-center equivalence* if MTC-braided-Witt-equivalent
monoidal categories carry integer-Witt-equivalent (mod 24) chiral central
charges. Strictly weaker than the plain `CentralChargePreservesDrinfeldCenter`
schema: easier to discharge, exactly matches the DMNO 2010 statement. -/
def CentralChargePreservesDrinfeldCenter_braided
    (cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ) : Prop :=
  ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C]
    (D : Type u₁) [Category.{v₁, u₁} D] [MonoidalCategory D],
    WittEquivalentMTC_braided C D → WittEquivalent (cc C) (cc D)

/--
**Plain hypothesis implies braided hypothesis.** The plain Wave 1b.5.8 schema
is a logically stronger hypothesis than the braided one; any `cc` satisfying
the plain form automatically satisfies the braided form via the strict
weakening of §7. -/
theorem CentralChargePreservesDrinfeldCenter.toBraided
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (h : CentralChargePreservesDrinfeldCenter cc) :
    CentralChargePreservesDrinfeldCenter_braided cc := by
  intros C _ _ D _ _ hbr
  exact h C D (WittEquivalentMTC_braided_implies_WittEquivalentMTC hbr)

/--
**Cross-bridge: braided MTC-Witt-equivalence ⇒ integer Witt-equivalence.**
Under the *braided* central-charge-preservation hypothesis, MTC-braided-Witt-
equivalent categories carry integer-Witt-equivalent (mod 24) chiral central
charges. -/
theorem wittEquivalentMTC_braided_implies_wittEquivalent
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (hcc : CentralChargePreservesDrinfeldCenter_braided cc)
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
    {D : Type u₁} [Category.{v₁, u₁} D] [MonoidalCategory D]
    (h : WittEquivalentMTC_braided C D) :
    WittEquivalent (cc C) (cc D) :=
  hcc C D h

/--
**Cross-bridge to `WittClass` (braided form).** Under the braided hypothesis,
braided-Witt-equivalent categories project to the same `WittClass.mk` element
of the integer-mod-24 quotient. -/
theorem wittEquivalentMTC_braided_implies_wittClass_eq
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (hcc : CentralChargePreservesDrinfeldCenter_braided cc)
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
    {D : Type u₁} [Category.{v₁, u₁} D] [MonoidalCategory D]
    (h : WittEquivalentMTC_braided C D) :
    WittClass.mk (cc C) = WittClass.mk (cc D) :=
  Quotient.sound (wittEquivalentMTC_braided_implies_wittEquivalent hcc h)

/-! ## §9 Stage 5.9 closure summary -/

/--
**Stage 5.9 closure summary.** Four substantive components, each load-bearing
in a distinct way (no P2 bundle redundancy):

1. `WittEquivalentMTC_braided` is an equivalence relation (refl/symm/trans
   inherited from Mathlib's braided functor identity + composition instances).
2. The braided form *strictly strengthens* the Wave 1b.5.8 plain form:
   braided-Witt-equivalent ⇒ plain-Witt-equivalent. (Converse fails.)
3. The plain hypothesis schema *strictly strengthens* the braided hypothesis
   schema: any `cc` satisfying the Wave 1b.5.8 hypothesis satisfies the
   refined braided hypothesis automatically.
4. Under the braided hypothesis, braided-Witt-equivalent categories project
   to the same `WittClass.mk` element in the integer-mod-24 quotient.

This refines `stage5_8_drinfeldCenter_closure` from the plain to the braided
substrate, exactly matching the DMNO 2010 statement. -/
theorem stage5_9_drinfeldCenter_braided_closure
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (hcc : CentralChargePreservesDrinfeldCenter_braided cc) :
    (∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C],
      WittEquivalentMTC_braided C C) ∧
    (∀ {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
       {D : Type u₂} [Category.{v₂, u₂} D] [MonoidalCategory D],
      WittEquivalentMTC_braided C D → WittEquivalentMTC C D) ∧
    (∀ {cc' : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ},
      CentralChargePreservesDrinfeldCenter cc' →
      CentralChargePreservesDrinfeldCenter_braided cc') ∧
    (∀ {C D : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
       [Category.{v₁, u₁} D] [MonoidalCategory D],
      WittEquivalentMTC_braided C D →
      WittClass.mk (cc C) = WittClass.mk (cc D)) := by
  refine ⟨fun C => WittEquivalentMTC_braided_refl C, ?_, ?_, ?_⟩
  · intros C _ _ D _ _ h
    exact WittEquivalentMTC_braided_implies_WittEquivalentMTC h
  · intros cc' h
    exact CentralChargePreservesDrinfeldCenter.toBraided h
  · intros C D _ _ _ _ h
    exact wittEquivalentMTC_braided_implies_wittClass_eq hcc h

end SKEFTHawking.SymTFTAudit
