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

namespace SKEFTHawking.PinPlusSmithDerived

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

end SKEFTHawking.PinPlusSmithDerived
