/-
# Phase 5q.H — E5 · the geometric-faithfulness CARDINALITY bridge

The honest bridge connecting the **finite E5 Adams-abutment chart** to the **smooth genuine
bordism carrier**, making the residual geometric-faithfulness wall precise as a single cardinality
inequality.

## The wall, restated precisely

The genuine `Ω₄^{Pin⁺} ≅ ℤ/16` on the smooth W4 carrier `DataBordismGrp (pinPlusGMTiedData …)` is
kernel-proven (`PinPlusGMWitness`) to reduce, *canonically* (all three injectivity routes — Thom,
Kirby–Taylor §5, Smith-LES — are apex-equivalent, `SETTLED_FORKS.md`
`5qH-injectivity-routes-all-equal-one-completeness-prop`), to a **single completeness node**: that the
surjective computed grade `abkGMTied16 : carrier →+ ZMod 16` is injective. Equivalently, since the grade
is already surjective (`abkGMTied16_surjective`, kernel-pure, over real manifolds), the node is exactly
the **upper cardinality cap** `Nat.card carrier ≤ 16`.

The **E5 spectral side** independently computes this `16` as a *finite, decidable* Ext-cokernel height:
`Nat.card adamsAbutment = 2 ^ (col4 height) = 2⁴ = 16`, where the column-`t−s=4` `δ = ·h₀` cokernel
height is `PinHeight4.col4_height_eq_four` (`axioms: []`, fully `decide`-able F₂ linear algebra).

This module ties the two together: it exhibits the geometric-faithfulness identification
`carrier ≃+ adamsAbutment` (= `ℤ/16`) as **equivalent, given the (proven) surjectivity, to the single
cardinality inequality** `Nat.card carrier ≤ Nat.card adamsAbutment`. So the residual is no longer an
disclosed (non-finite) iso (`pin4_abutment` / `smith_inflow_z16`): it is the sharp, honestly-stated inequality
"**the smooth Pin⁺ bordism carrier has cardinality at most the E5 Ext-cokernel height** `2^(col4 height)`".
Nothing here is disclosed — the surjectivity is proven, the abutment cardinality is the decidable E5
chart, and the equivalence is finite-group counting. The one inequality that remains open IS the wall
(the ABP/AHSS `≤ 16` completeness — the relative fundamental class `[W,∂W]` + surgery, Mathlib-absent,
`SETTLED_FORKS.md`).

## Honest scope

Kernel-pure (`{propext, Classical.choice, Quot.sound}`). No new axiom, no `sorry`, no
`native_decide`/`maxHeartbeats`. This does NOT discharge the wall; it makes the wall **precise and
connected to the finite E5 chart** — the `card_le` against the decidable Adams height, rather than a bare
literal `16` or a bare `Nonempty (… ≃+ …)`. The `≤` half (ABP completeness) is the single scoped
residual, already tracked as `smith_inflow_z16` (atlas keystone) / `hbound` (grade-0 injectivity).

## References
- `PinPlusGMWitness` — the surjective tied grade + the grade-0-injectivity reduction (all routes equal).
- `PinPlusAdamsAbutment` — `adamsAbutment := ZMod (2 ^ height4)`, `adamsAbutment_card = 16` from
  `col4_height_eq_four`.
- `Lit-Search/Phase-5qF/discharge_pin4_abutment_route.md` — the W4–W6 Smith-LES derivation route.
- `docs/dev-loops/SETTLED_FORKS.md` — `5qH-injectivity-routes-all-equal-one-completeness-prop` (the
  canonical single-node reduction); `synthetic-grade-ker-bot-nogo` (free-grade `ker=⊥` is FALSE).
-/
import Mathlib
import SKEFTHawking.PinPlusGMWitness
import SKEFTHawking.PinPlusAdamsAbutment

namespace SKEFTHawking.PinPlusFaithfulnessCardBridge

open scoped Manifold
open SKEFTHawking.PinPlusGMWitness SKEFTHawking.PinPlusAdamsAbutment
open SKEFTHawking.TangentialDataBordism SKEFTHawking.PinPlusGMTiedData

universe u

/-! ## §1. The abstract counting bridge (surjective onto ℤ/16 + card ≤ 16 ⟹ iso) -/

/-- **A finite group surjecting onto `ℤ/16` with cardinality `≤ 16` is `≅ ℤ/16`.** Pure finite-group
counting: a surjection `f : G →+ ZMod 16` forces `16 ∣ Nat.card G` (`card_dvd_of_surjective`), so with
`Nat.card G ≤ 16` and `0 < Nat.card G` (finite, nonempty via the surjection) we get `Nat.card G = 16`,
whence `f` is bijective (surjective + equal finite cardinality) and an isomorphism. This is the abstract
engine of the geometric-faithfulness bridge: the ONLY nontrivial hypothesis is the cardinality cap. -/
theorem iso_zmod16_of_surjective_of_card_le {G : Type*} [AddCommGroup G] [Finite G]
    (f : G →+ ZMod 16) (hsurj : Function.Surjective f) (hle : Nat.card G ≤ 16) :
    Nonempty (G ≃+ ZMod 16) := by
  have hdvd : (16 : ℕ) ∣ Nat.card G := by
    have := AddSubgroup.card_dvd_of_surjective f hsurj
    rwa [Nat.card_zmod] at this
  have hcard : Nat.card G = 16 := Nat.le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
  haveI : Fintype G := Fintype.ofFinite G
  have hbij : Function.Bijective f := by
    refine (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, Nat.card_zmod]
  exact ⟨AddEquiv.ofBijective f hbij⟩

/-! ## §2. The E5 chart value: `Nat.card adamsAbutment = Nat.card (ZMod 16) = 16` (decidable height) -/

/-- **The E5 Adams-abutment cardinality is the `ZMod 16` cardinality.** `Nat.card adamsAbutment =
2 ^ height4 = 2⁴ = 16 = Nat.card (ZMod 16)`, the `16` being the decidable column-4 `δ = ·h₀` Ext-cokernel
height `col4_height_eq_four` (`axioms: []`). This equation is what lets the geometric `card ≤ 16` cap be
stated against the *finite E5 chart* rather than a bare literal. -/
theorem abutment_card_eq_zmod16_card : Nat.card adamsAbutment = Nat.card (ZMod 16) := by
  rw [adamsAbutment_card, Nat.card_zmod]

/-! ## §3. The geometric-faithfulness identification, reduced to the single cardinality inequality -/

/-- **`Ω₄^{Pin⁺} ≅ ℤ/16` on the smooth carrier, from the cardinality cap against the E5 abutment.** The
genuine tied W4 carrier `DataBordismGrp (pinPlusGMTiedData …)` carries the surjective computed grade
`abkGMTied16` (`abkGMTied16_surjective`, kernel-pure, over real manifolds-with-boundary). GIVEN it is
finite and its cardinality is at most the **E5 Adams-abutment cardinality** `Nat.card adamsAbutment`
(= `2^(col4 height)` = 16, the decidable Ext-cokernel height), the carrier is `≃+ ℤ/16`.

This is the honest form of the geometric-faithfulness identification: the residual is the single
cardinality inequality `card(smooth carrier) ≤ (E5 finite chart height)`, NOT an disclosed (non-finite) iso.
The inequality's `≤` direction is the ABP/AHSS completeness (`smith_inflow_z16` / `hbound`), the
Mathlib-absent wall; everything else (the surjection, the abutment cardinality, the counting) is
proven. -/
theorem omega4PinPlusGMTied_equiv_zmod16_of_card_le_abutment
    [Finite (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))]
    (hle : Nat.card (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
        ≤ Nat.card adamsAbutment) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  iso_zmod16_of_surjective_of_card_le (abkGMTied16 (k := 0) (I := 𝓡 4)) abkGMTied16_surjective
    (by rwa [adamsAbutment_card] at hle)

/-- **The bridge equivalence: the geometric-faithfulness iso ⟺ the cardinality cap against the E5
abutment** (given finiteness). The `Nonempty (carrier ≃+ ZMod 16)` identification and the single
inequality `Nat.card carrier ≤ Nat.card adamsAbutment` are **equivalent**:
* (⟸) is `omega4PinPlusGMTied_equiv_zmod16_of_card_le_abutment` (the surjectivity + counting);
* (⟹) is the transport of `Nat.card (ZMod 16) = Nat.card adamsAbutment` back through the iso.

So the entire remaining content of the geometric-faithfulness identification is *exactly* the finite
cardinality inequality against the decidable E5 chart — the wall is pinned to one honest inequality, no
disclosed-iso hypothesis remaining. -/
theorem iso_iff_card_le_abutment
    [Finite (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))] :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) ↔
      Nat.card (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) ≤ Nat.card adamsAbutment := by
  constructor
  · rintro ⟨e⟩
    rw [Nat.card_congr e.toEquiv, ← abutment_card_eq_zmod16_card]
  · exact omega4PinPlusGMTied_equiv_zmod16_of_card_le_abutment

end SKEFTHawking.PinPlusFaithfulnessCardBridge
