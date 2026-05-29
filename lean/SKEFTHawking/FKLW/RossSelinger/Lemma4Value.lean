/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — KMM Lemma 4 value-form (`gde(|x|²) ≤ 1` for cleared `x`)

KMM Lemma 4 (arXiv:1206.5236 §3) has two parts for the cleared column numerators
`x, y : ℤ[ω]` of a unitary:

  1. **equal sde** — `gde(|x|²) = gde(|y|²)` (shipped as the `denExp` core
     `ZOmegaSqrt2.denExp_normSq_col0_eq` + the clearing connection);
  2. **bounded by `1`** — the common gde is in `{0, 1}`.

This file ships part (2): a numerator `x` in *lowest terms* (`√2 ∤ x`) has
`gde(|x|², √2) ≤ 1`. The argument is the parity fact behind KMM Prop 1: if
`√2² = 2 ∣ |x|²` then (`dividesSqrt2_of_dvdSqrt2Pow_normSq_two`, the `ZMod 2`
decide) `√2 ∣ x` — contrapositive gives `¬(√2² ∣ |x|²)`, i.e. `gde(|x|²) ≤ 1`.

Concretely: `gde(|x|²) ≥ 2 ⟺ 2 ∣ P ∧ 2 ∣ Q` (`P = a²+b²+c²+d²`, `Q = ab+bc+cd−ad`
the squared-modulus coordinates), and `2∣P ∧ 2∣Q ⟹ a ≡ c ∧ b ≡ d (mod 2) = √2 ∣ x`.

This is the `j ∈ {0,1}` hypothesis of `kmm_lemma3_column` for the cleared column
numerators (which `√2 ∤ x` by construction of the clearing).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected (the `ZMod 2` parity decide in
  `dividesSqrt2_of_dvdSqrt2Pow_normSq_two` is a kernel `decide`).

-/

import SKEFTHawking.FKLW.RossSelinger.CrossTermGde

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **KMM Lemma 4 (value bound)**: a numerator in lowest terms (`√2 ∤ x`) has
squared-modulus gde at most `1`: `gdePeel (|x|²) fuel ≤ 1`.

If `fuel ≤ 1` the bound is immediate (`gdePeel ≤ fuel`); otherwise
`gdePeel ≥ 2` would give `√2² ∣ |x|²` (`dvdSqrt2Pow_iff_le_gdePeel`), whence
`√2 ∣ x` (`dividesSqrt2_of_dvdSqrt2Pow_normSq_two`, the `ZMod 2` parity decide),
contradicting `√2 ∤ x`. -/
theorem gdePeel_normSq_le_one_of_not_dividesSqrt2 {x : ZOmega}
    (h : ¬ dividesSqrt2 x) (fuel : ℕ) : gdePeel (normSq x) fuel ≤ 1 := by
  by_cases hf : fuel ≤ 1
  · exact le_trans (gdePeel_le_fuel _ _) hf
  · by_contra hc
    have h2 : dvdSqrt2Pow (normSq x) 2 :=
      (dvdSqrt2Pow_iff_le_gdePeel (by omega : 2 ≤ fuel)).mpr (by omega)
    exact h (dividesSqrt2_of_dvdSqrt2Pow_normSq_two h2)

end ZOmega

end SKEFTHawking.RossSelinger
