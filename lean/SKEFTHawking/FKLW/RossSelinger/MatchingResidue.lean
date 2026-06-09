/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 16) — matching-residue `√2`-divisibility facts

Elementary `ℤ[ω]` divisibility-by-`√2` facts used in the dim-4 column-lemma reduction step
(`ReductionStep`, inc 15): `√2 ∣ ·` is additive, `√2 ∣ 2y` always, and a `√2`-divisible numerator at
denominator level `k+1` clears to denominator exponent `≤ k`.

**Scope correction (vs. this increment's original framing).** These lemmas are correct, but they do
**not** by themselves furnish the reduction step, and `kmm_lemma3` IS needed:

  * An `H`-combination of two entries `x ≡ y (mod √2)` at `colDenExp = s` gives `(x ± y)/√2^{s+1}`;
    since `√2 ∣ x ± y` these land at denExp `≤ s`, but `(x+y)/√2` is generically NOT further
    `√2`-divisible (that needs `√2² = 2 ∣ x+y`, not just `√2`). So the combined entries sit at denExp
    **`= s`, not `s−1`** — matching-residue + `H` does **not** lower `colDenExp`. The genuine reduction
    is the `|·|²` 2-adic-valuation (`gde`) argument — exactly `kmm_lemma3`.
  * The KMM headline is **exponent-1 `O(log 1/ε)`** word length, i.e. the *optimal* T-count, which is
    precisely what `kmm_lemma3` establishes; a suboptimal reduction would inflate the exponent.

So `ReductionStep` reuses the dim-2 `reduceStep` + `kmm_lemma3_column` (the tolerated `native_decide`
site Track 3 eliminates → retroactively kernel-pure). These facts remain useful scaffolding for the
`√2`-clearing bookkeeping in that reduction.

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
`(x ± y)/√2 ∈ ℤ[ω]`. (NB: this clears *one* `√2`, dropping the combined entries to denExp `≤ s` at
`colDenExp = s` — it does NOT lower `colDenExp` to `s−1`; that needs the `|·|²`-valuation `kmm_lemma3`
argument. See the module docstring.) -/
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
