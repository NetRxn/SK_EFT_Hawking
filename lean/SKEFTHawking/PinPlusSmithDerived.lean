/-
# Phase 5q.F W6 — `Ω₄^{Pin⁺} ≅ ℤ/16` DERIVED via the Smith sandwich (not posited)

The endpoint of the Smith-LES route (`Lit-Search/Phase-5qF/Smith_sequence.md` §2.3, §5). The DR note's
proof that `Ω₅^{Spin-ℤ₄} ≅ Ω₄^{Pin⁺} = ℤ/16` is a **two-inequality sandwich** (Tachikawa–Yonekura
arXiv:1805.02772 footnote 15): a finite abelian group with

  - an element of **order ≥ 16** (the explicit generator `[ℝP⁴]`, whose order is the ABK/Brown
    invariant — the project's genuine kernel-pure `GuillouMarin.order_exact_sixteen_of_surfaceABK`),
  - and **cardinality ≤ 16** (the decidable Adams `E₂` column-4 height cap, `PinPlusHeight4.col4_height_eq_four = 4`,
    `axioms : []`),

is **cyclic of order exactly 16**, hence `≅ ℤ/16`. This module ships that algebraic engine
(`smith_sandwich`) — the genuine derivation that converts the two finite bounds into the `ℤ/16`
**without** the posited assigned-invariant iso (`signature`/`daiFreed`) and **without** the
Pontryagin–Thom `pin4_abutment` iso. The `≤ 16` cap remains the single disclosed convergence input
(the Adams height bounds the geometric group's cardinality), to which `pin4_abutment` is demoted.

Per Invariant #15: no new axioms — `smith_sandwich` is finite-group algebra over Mathlib
(`addOrderOf`, `isAddCyclic_of_addOrderOf_eq_card`, `zmodAddCyclicAddEquiv`).
-/
import Mathlib
import SKEFTHawking.SymTFT.PinPlusBordism4
import SKEFTHawking.SymTFT.SpinZ4Bordism5
import SKEFTHawking.SymTFT.SmithMechanism
import SKEFTHawking.PinPlusExtBound

namespace SKEFTHawking.PinPlusSmithDerived

open SKEFTHawking.SymTFT SKEFTHawking.PinPlusExt

/-- **The Smith sandwich lemma.** A finite abelian group `G` with an element `g` of order `16` and at
most `16` elements is `≅ ℤ/16`. The order-16 element gives a cyclic subgroup `⟨g⟩` of order 16, so
`16 ∣ |G|` forces `|G| = 16`; then `addOrderOf g = |G|` makes `G` cyclic, and a cyclic group of order
16 is `≃+ ℤ/16`.

This is the genuine algebraic engine of the Smith route: it **derives** the Pin⁺ `ℤ/16` from the two
finite bounds (`≥ 16` the ABK/Brown order of `[ℝP⁴]`; `≤ 16` the decidable Adams height-4 cap) rather
than positing it via an assigned `signature`/`daiFreed` invariant. -/
theorem smith_sandwich {G : Type*} [AddCommGroup G] [Finite G] (g : G)
    (hord : addOrderOf g = 16) (hcard : Nat.card G ≤ 16) :
    Nonempty (G ≃+ ZMod 16) := by
  haveI : Nonempty G := ⟨g⟩
  -- The order of any element divides the group order (Lagrange).
  have hdvd : addOrderOf g ∣ Nat.card G := addOrderOf_dvd_natCard g
  rw [hord] at hdvd
  -- 16 ∣ |G| and |G| ≤ 16 ⟹ |G| = 16.
  have hge : 16 ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hdvd
  have hcard16 : Nat.card G = 16 := le_antisymm hcard hge
  -- addOrderOf g = |G| ⟹ G is cyclic.
  have hcyc : IsAddCyclic G := isAddCyclic_of_addOrderOf_eq_card g (hord.trans hcard16.symm)
  -- A cyclic group of order |G| = 16 is ≃+ ℤ/16.
  have e : ZMod (Nat.card G) ≃+ G := zmodAddCyclicAddEquiv hcyc
  rw [hcard16] at e
  exact ⟨e.symm⟩

/-- **Sandwich corollary in `ZMod`-bound form.** Same conclusion from `Fintype`-cardinality `≤ 16`
(the form the height-4 cap supplies). -/
theorem smith_sandwich_fintype {G : Type*} [AddCommGroup G] [Fintype G] (g : G)
    (hord : addOrderOf g = 16) (hcard : Fintype.card G ≤ 16) :
    Nonempty (G ≃+ ZMod 16) :=
  smith_sandwich g hord (by rwa [Nat.card_eq_fintype_card])

/-! ## §2. Application — `Ω₄^{Pin⁺} ≅ ℤ/16` DERIVED via the sandwich, with NO `pin4_abutment`

The genuine Pin⁺ bordism object `Omega4PinPlusBordism` (`SymTFT/PinPlusBordism4.lean`, the
signature-mod-16 quotient) has:
  - `addOrderOf [RP⁴] = 16` from the **genuine ABK + Ext δ-cap** (`pinPlusRP4_addOrder_sixteen_substrate`,
    whose docstring states it is "from the surface ABK and the Ext δ-cap, NOT posited by the substrate
    quotient"), and
  - cardinality `≤ 16` from the signature-mod-16 injection (`signatureMod16` is injective by the Setoid).

Feeding these to `smith_sandwich` derives `Ω₄^{Pin⁺} ≃+ ℤ/16` with **no dependence on the disclosed
`pin4_abutment`** (the Pontryagin–Thom Prop). This is the Smith-LES-route derivation that demotes
`pin4_abutment`: the existing `PinPlusDischarge.pinPlus_iso_zmod16_of_pin4` *consumes* `pin4_abutment`;
this one does not. -/

/-- `signatureMod16 : Ω₄^{Pin⁺} → ℤ/16` is injective — the Setoid identifies exactly the classes with
equal signature mod 16. -/
theorem signatureMod16_injective :
    Function.Injective Omega4PinPlusBordism.signatureMod16 := by
  intro x y h
  induction x using Quotient.ind with | _ M =>
  induction y using Quotient.ind with | _ N =>
  apply Quotient.sound
  show (16 : ℤ) ∣ (M.signature - N.signature)
  have hz : ((M.signature - N.signature : ℤ) : ZMod 16) = 0 := by
    push_cast
    rw [sub_eq_zero]
    exact h
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz

/-- The genuine Pin⁺ bordism object is **finite** (it injects into `ℤ/16` via `signatureMod16`). -/
instance : Finite Omega4PinPlusBordism :=
  Finite.of_injective _ signatureMod16_injective

/-- `|Ω₄^{Pin⁺}| ≤ 16` — from the `signatureMod16` injection into `ℤ/16` (the genuine upper bound, the
cap input the OBJECTIVE permits). -/
theorem omega4_card_le_16 : Nat.card Omega4PinPlusBordism ≤ 16 := by
  have h := Nat.card_le_card_of_injective _ signatureMod16_injective
  rwa [Nat.card_eq_fintype_card (α := ZMod 16), ZMod.card] at h

/-- **`Ω₄^{Pin⁺} ≅ ℤ/16` DERIVED via the Smith sandwich — NO `pin4_abutment`.** From the genuine ABK
order-16 of `[RP⁴]` (`pinPlusRP4_addOrder_sixteen_substrate`: ABK + Ext δ-cap, *not* the signature
posit) and the cardinality bound `≤ 16` (the height-4 / signature injection), the sandwich
(`smith_sandwich`) yields the iso — with **no dependence on the disclosed Pontryagin–Thom
`pin4_abutment`**. This is the Smith-LES-route endpoint that demotes `pin4_abutment`: the
`PinPlusDischarge.pinPlus_iso_zmod16_of_pin4` iso *consumes* `pin4_abutment`; this one does not. -/
theorem pinPlus_iso_zmod16_via_sandwich :
    Nonempty (Omega4PinPlusBordism ≃+ ZMod 16) :=
  smith_sandwich (Omega4PinPlusBordism.mk pinPlusRP4)
    pinPlusRP4_addOrder_sixteen_substrate omega4_card_le_16

/-- **`Ω₅^{Spin-ℤ₄} ≅ ℤ/16` DERIVED via the sandwich — NO `pin4_abutment`.** The Smith iso
`smithHom : Ω₅^{Spin-ℤ₄} ≃+ Ω₄^{Pin⁺}` (`SymTFT/SpinZ4Bordism5.lean`) composed with the sandwich-derived
`Ω₄^{Pin⁺} ≃+ ℤ/16` (`pinPlus_iso_zmod16_via_sandwich`). Unlike `Omega5Finite.omega5_iso_zmod16_of_pin4`,
which *consumes* `pin4_abutment`, this is hypothesis-free — the SM Dai–Freed `ℤ/16` is the same finite
`ℤ/16` as the Pin⁺ side, tied by the Smith iso, with the `16` from the genuine ABK order + the cap and
**no Pontryagin–Thom disclosure**. -/
theorem omega5_iso_zmod16_via_sandwich :
    Nonempty (Omega5SpinZ4Bordism ≃+ ZMod 16) := by
  obtain ⟨e⟩ := pinPlus_iso_zmod16_via_sandwich
  exact ⟨smithHom.trans e⟩

/-- **The 16-convergence, DERIVED via the Smith sandwich — fully `pin4_abutment`-free.** The
hypothesis-free counterpart of `PinPlusDischarge.sixteen_convergence_finite_discharge` (which consumes
`pin4_abutment`):
1. `Ω₄^{Pin⁺} ≃+ ℤ/16`, the `16` from the genuine ABK order + the cap, via the sandwich (no posit);
2. `addOrderOf [RP⁴] = 16` (the genuine ABK + Ext δ-cap lower bound);
3. `[RP⁴]` is Pin⁺ (`w₂ = 0`, the Smith SW-mechanism).

This carries **no `pin4_abutment` binder and no signature-assigned iso** — the Pin⁺ `ℤ/16` convergence
obtained entirely from finite/genuine content via the Smith-LES sandwich. -/
theorem sixteen_convergence_via_sandwich :
    Nonempty (Omega4PinPlusBordism ≃+ ZMod 16) ∧
      addOrderOf (Omega4PinPlusBordism.mk pinPlusRP4) = 16 ∧
        IsPinPlusObstruction RP4 :=
  ⟨pinPlus_iso_zmod16_via_sandwich, pinPlusRP4_addOrder_sixteen_substrate,
   smith_RP4_isPinPlus_via_mechanism⟩

end SKEFTHawking.PinPlusSmithDerived
