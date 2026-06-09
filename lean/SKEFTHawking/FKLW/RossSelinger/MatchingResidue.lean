/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 16) — the elementary matching-residue reduction engine

The dim-4 column-lemma reduction step (`ReductionStep`, inc 15) lowers a unit column's denominator
exponent. The **per-pair engine** is elementary — and, crucially, **needs no `kmm_lemma3` /
`native_decide`**: that lemma proves the stronger *optimal* T-count reduction, but the column lemma only
needs *some* reduction.

The fact: two entries `x, y ∈ ℤ[ω]` with the **same residue mod √2** (`√2 ∣ x − y`) have BOTH Hadamard
combinations `√2`-divisible — `x + y = (x − y) + 2y` and `√2 ∣ 2y` always — so `(x ± y)/√2 ∈ ℤ[ω]`,
i.e. an `H`-combination of two matching entries lowers their denominator exponent by one. This is the
kernel-pure core of the dim-4 reduction (the pairing — that matching max-denExp entries exist, forced by
the unit-column / parity condition — is the remaining Giles–Selinger combinatorial input).

## Headlines

  * `ZOmega.dividesSqrt2_add` / `dividesSqrt2_two_mul` — `√2 ∣ ·` is additive; `√2 ∣ 2y` always.
  * `ZOmega.dividesSqrt2_add_of_dividesSqrt2_sub` — `√2 ∣ x − y ⟹ √2 ∣ x + y`.
  * `ZOmegaSqrt2.denExp_mk_succ_le_of_dividesSqrt2` — a `√2`-divisible numerator at level `k+1` clears
    to denominator exponent `≤ k` (the actual reduction).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.Sde

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **`√2 ∣ ·` is additive**: matching the residue is a subgroup condition. -/
theorem dividesSqrt2_add {x y : ZOmega} (hx : dividesSqrt2 x) (hy : dividesSqrt2 y) :
    dividesSqrt2 (x + y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩ <;> simp only [add_a, add_b, add_c, add_d] <;> omega

/-- **`√2 ∣ 2y` always** (`2 = √2²`): doubling lands in the `√2`-ideal. -/
theorem dividesSqrt2_two_mul (y : ZOmega) : dividesSqrt2 (y + y) := by
  refine ⟨?_, ?_⟩ <;> simp only [add_a, add_b, add_c, add_d] <;> omega

/-- **Matching residues reduce both Hadamard combinations.** If `x ≡ y (mod √2)` (`√2 ∣ x − y`), then
`√2 ∣ x + y` too — `x + y = (x − y) + 2y`, and `√2 ∣ 2y` always. So BOTH `(x ± y)/√2 ∈ ℤ[ω]`: an
`H`-combination of two matching entries lowers their denominator exponent. **Elementary — no
`kmm_lemma3` / `native_decide`.** -/
theorem dividesSqrt2_add_of_dividesSqrt2_sub {x y : ZOmega} (h : dividesSqrt2 (x - y)) :
    dividesSqrt2 (x + y) := by
  rw [show x + y = (x - y) + (y + y) from by ring]
  exact dividesSqrt2_add h (dividesSqrt2_two_mul y)

end ZOmega

namespace ZOmegaSqrt2

/-- **The reduction**: a `√2`-divisible numerator at denominator level `k + 1` clears to denominator
exponent `≤ k`. (`lowestDenExp` peels one `√2` when the numerator is `√2`-divisible.) Combined with
`dividesSqrt2_add_of_dividesSqrt2_sub`, an `H`-combination of two matching entries (cleared at `k + 1`)
has denominator exponent `≤ k`. -/
theorem denExp_mk_succ_le_of_dividesSqrt2 {z : ZOmega} (h : ZOmega.dividesSqrt2 z) (k : ℕ) :
    denExp (mk z (k + 1)) ≤ k := by
  rw [denExp_mk, ZOmega.lowestDenExp_succ, if_pos h]
  exact ZOmega.lowestDenExp_le _ _

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
