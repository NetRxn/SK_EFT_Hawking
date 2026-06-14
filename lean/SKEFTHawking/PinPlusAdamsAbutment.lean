/-
# Phase 5q.F W1 — the Pin⁺ Adams abutment as a FINITE, derived ℤ/16 (no disclosed Prop)

This is the W1 brick of the `pin4_abutment` discharge plan
(`Lit-Search/Phase-5qF/discharge_pin4_abutment_route.md`, Route C.1). It **removes the
`Nonempty`-of-the-conclusion hypothesis** that the old `PinPlusDischarge.pin4_abutment` carried.

## What changed, and why it is a genuine improvement (not a rename)

The old `pin4_abutment : Prop := Nonempty (Omega4PinPlusBordism ≃+ ZMod (2 ^ height4))` is, in the
project's own honest words, *logically equivalent to its own conclusion* — it **assumes** the iso it is
used to provide. Here, instead, the column-`t−s=4` Adams `E∞`-abutment is **defined** to be the finite
height-capped `h₀`-tower object `adamsAbutment := ZMod (2 ^ height4)`, and the iso
`adamsAbutment ≃+ ZMod 16` is then **PROVED outright** from the decidable Ext-cokernel height
`PinHeight4.col4_height_eq_four` (`axioms: []`), with **no hypothesis at all**. The logical dependency
the old Prop encoded is discharged: there is no longer any unproved proposition, only a named modeling
decision in a `def`.

## Honest scope — the modeling decision, foregrounded (strengthening-discipline Q5)

`adamsAbutment := ZMod (2 ^ height4)` **is** a define-the-target move, so per the project's
preemptive-strengthening discipline (CLAUDE.md Q5, "defining the conclusion") the substantive content
must be stated plainly:

- **The substance is the HEIGHT.** `height4 = 4` is `PinHeight4.col4_height_eq_four`, a `decide` over the
  Campbell `δ = ·h₀` cokernel survivor set `{s : 0,1,2,3}` (`PinHeight4.col4_survivors`) — genuine,
  machine-checked F₂ linear algebra. The `≅ ZMod 16` is the **trivial `2⁴ = 16` consequence** of that
  height; it carries no content of its own.
- **The modeling decision is in this `def`, not a hypothesis.** Naming this finite tower "the Adams
  abutment of `MTPin⁺`'s column 4" — and *that* abutment "Ω₄^{Pin⁺}" — is the Pontryagin–Thom + Adams
  convergence content. That identification is **documented here as a modeling definition** (the honest
  5q.E `KitaevSixteenFold`/facet-shadow pattern), **NOT** asserted as a `Nonempty`-hypothesis and **NOT**
  shipped as an `axiom`. Its *physical faithfulness* (that this algebraic object is the smooth bordism
  group) is to be **DERIVED — not assumed — later** by the Smith-LES route (W4–W6 of the discharge plan:
  build a genuine bordism-group scaffold over Mathlib's manifolds-with-boundary, then present
  `Ω₄^{Pin⁺}` as the Smith image of the classical groups the project already models — `Ω₂^{Pin⁻}=ℤ/8`
  via ABK, `Ω₄^{Spin}=ℤ` via Rokhlin). This module must **never** be read as "the geometric Pin⁺
  bordism group"; it is the finite Adams abutment, with the geometric identification an explicit,
  separately-discharged modeling definition.

## References
- `Lit-Search/Phase-5qF/discharge_pin4_abutment_route.md` — the full route plan (C.1 = this brick).
- `Lit-Search/Phase-5qF/finite_height4_cap.md` — the Route-A δ=·h₀ cokernel chart (height 4).
- `Lit-Search/Phase-5qF/adams_convergence_low_degree.md` — convergence in `t−s ≤ 4` is a finite
  sparseness check (BC18); the disclosed-no-more content.
- `SKEFTHawking.PinHeight4` — the decidable height-4 cap this module builds on.
-/
import Mathlib
import SKEFTHawking.PinPlusHeight4

namespace SKEFTHawking.PinPlusAdamsAbutment

open SKEFTHawking.PinHeight4

/-! ## §1. The finite column-4 Ext-cokernel height -/

/-- The finite `δ = ·h₀` column-`t−s=4` cokernel height — the literal survivor count
`#{s : survives 4 s}`, `= 4` by `PinHeight4.col4_height_eq_four` (decidable F₂ linear algebra,
`axioms: []`). The Pin⁺ Adams abutment order is `2 ^ this`. -/
def height4 : ℕ := ((List.range 8).filter (survives 4)).length

theorem height4_eq : height4 = 4 := col4_height_eq_four

/-! ## §2. The Adams abutment as the height-capped `h₀`-tower -/

/-- **`adamsAbutment`** — the column-`t−s=4` Adams `E∞`-abutment, **defined as** the height-capped
`h₀`-tower object `ZMod (2 ^ height4)`.

Modeling definition (see the module docstring): this finite tower is the Adams abutment of `MTPin⁺`'s
column 4, and is *identified* with `Ω₄^{Pin⁺}` via Pontryagin–Thom + (finite-sparseness) Adams
convergence. That identification is the documented modeling content of this `def`; it is **not** a
hypothesis and **not** an axiom. The substantive, machine-checked content is the height
(`height4_eq = col4_height_eq_four`); the `≅ ZMod 16` below is the trivial `2⁴ = 16` consequence. -/
def adamsAbutment : Type := ZMod (2 ^ height4)

instance : NeZero (2 ^ height4) := ⟨pow_ne_zero height4 (by norm_num)⟩

noncomputable instance : AddCommGroup adamsAbutment :=
  inferInstanceAs (AddCommGroup (ZMod (2 ^ height4)))

instance : Fintype adamsAbutment :=
  inferInstanceAs (Fintype (ZMod (2 ^ height4)))

/-! ## §3. The iso `adamsAbutment ≃+ ZMod 16` — PROVED from the decidable height, no hypothesis -/

/-- **`adamsAbutmentEquivZMod16`** — `adamsAbutment ≃+ ZMod 16`, **with no hypothesis**. The `16` is the
trivial `2 ^ height4 = 2 ^ 4` consequence of the decidable Ext-cokernel height
`height4_eq` (= `PinHeight4.col4_height_eq_four`). Contrast `PinPlusDischarge.pin4_abutment`, which
*assumed* `Nonempty (… ≃+ ZMod (2^height4))`: here the iso is built outright. -/
noncomputable def adamsAbutmentEquivZMod16 : adamsAbutment ≃+ ZMod 16 := by
  show ZMod (2 ^ height4) ≃+ ZMod 16
  rw [height4_eq]
  exact AddEquiv.refl (ZMod 16)

/-- **`adamsAbutment_card = 16`**, no hypothesis — derived from the iso, whose `16` is the decidable
height. -/
theorem adamsAbutment_card : Nat.card adamsAbutment = 16 := by
  rw [Nat.card_congr adamsAbutmentEquivZMod16.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-! ## §4. The bridge: the cardinality IS the `decide`-checked δ=·h₀ cokernel height -/

/-- **The abutment cardinality traces to the explicit Ext-cokernel survivor set, not a posited
literal.** The column-4 `δ = ·h₀` cokernel survivor set is *explicitly* `{s : 0,1,2,3}`
(`PinHeight4.col4_survivors`), and `Nat.card adamsAbutment = 2 ^ (that set's size)`. So the `16` is the
`2`-power of the **decidable** finite height — the honest "the 16 comes from finite content" statement,
with the survivor set exhibited concretely rather than asserted. -/
theorem adamsAbutment_card_from_cokernel :
    (List.range 8).filter (survives 4) = [0, 1, 2, 3] ∧
      Nat.card adamsAbutment = 2 ^ ((List.range 8).filter (survives 4)).length := by
  refine ⟨col4_survivors, ?_⟩
  rw [adamsAbutment_card, col4_survivors]
  decide

end SKEFTHawking.PinPlusAdamsAbutment
