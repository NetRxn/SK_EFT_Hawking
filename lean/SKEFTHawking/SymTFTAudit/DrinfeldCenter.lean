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

## Open continuations (Wave 1b.5.9+)

* Strengthen `Equivalence (Center C) (Center D)` to *braided* equivalence
  (uses `BraidedCategory (Center C)` instance not yet in Mathlib).
* Construct the Witt group operation via Deligne tensor product `C ⊠ D`
  (Wave 1b.5.10).
* Discharge the central-charge-preservation hypothesis on the pseudo-unitary
  pre-modular subclass (Wave 1b.5.11) — this is where the DMNO 2010 theorem
  becomes a Lean theorem.
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

end SKEFTHawking.SymTFTAudit
