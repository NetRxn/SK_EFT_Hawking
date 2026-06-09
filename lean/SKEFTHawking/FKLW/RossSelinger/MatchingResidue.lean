/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 16) — matching-residue `√2`-divisibility facts

Elementary `ℤ[ω]` divisibility-by-`√2` facts used in the dim-4 column-lemma reduction step
(`ReductionStep`, inc 15): `√2 ∣ ·` is additive, `√2 ∣ 2y` always, and a `√2`-divisible numerator at
denominator level `k+1` clears to denominator exponent `≤ k`.

**Scope note (corrected 2026-06-09, inc 22 — supersedes this increment's earlier `kmm_lemma3` framing).**
These `√2`-clearing facts are part of the row-operation toolkit but do not by themselves furnish the
reduction. The key subtlety (correct, and confirmed by kernel `#eval`): an `H`-combination of two entries
`x ≡ y (mod √2)` at `colDenExp = s` gives `(x ± y)/√2^{s+1}`, which land at denExp `≤ s` (since `√2 ∣ x ± y`)
but are generically **not** at `s−1` — dropping a level needs `√2² = 2 ∣ x ± y`, i.e. **mod-2** alignment,
not merely mod-`√2`. The Giles–Selinger row operation (Lemma 4, `GilesSelingerRowOp.lean`) supplies the
mod-2 alignment via `Tᵐ` phase control (choose `m` with `x ≡ ωᵐy (mod 2)`), giving the genuine
denominator drop — **elementary and kernel-pure, NOT `kmm_lemma3`**. (`kmm_lemma3` is the finer SO(3)/`|·|²`
optimal-T-count for *ancilla-free single-qubit* synthesis — a different result the dim-4 column lemma does
not use; its `O(lde) = O(log 1/ε)` exponent-1 optimality comes from Giles–Selinger directly.)

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

/-- **Matching residues: both Hadamard combinations are `√2`-divisible.** If `x ≡ y (mod √2)`
(`√2 ∣ x − y`), then `√2 ∣ x + y` too — `x + y = (x − y) + 2y`, and `√2 ∣ 2y` always. So both
`(x ± y)/√2 ∈ ℤ[ω]`. (NB: mod-`√2` matching clears *one* `√2`, keeping the combined entries at denExp
`≤ s` — it does NOT by itself reach `s−1`; that needs **mod-2** alignment via `Tᵐ`, the Giles–Selinger
row op `core_step` in `GilesSelingerRowOp.lean`. See the module docstring.) -/
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
