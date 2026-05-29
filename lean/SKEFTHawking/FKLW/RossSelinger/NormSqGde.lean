/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — squared modulus on `ZOmega` + its gde (KMM Lemma 5 substrate)

The KMM exact-synthesis reduction (arXiv:1206.5236) tracks the
`√2`-greatest-dividing-exponent of the **squared modulus** `|x|² = x · conj x`
of the cleared column numerators `x, y ∈ ℤ[ω]`. Numerically (validated by
`scripts/kmm_zomega_reference_oracle.py` over 18304 realizable columns) the
reduction step needs the gde of `|x + ωᵏy|²`, **not** divisibility of
`x + ωᵏy` itself — there is no mod-`√2` shortcut.

This file ships the squared modulus on the base ring `ZOmega` (where the cleared
numerators live; `|x|²` is a real element of `ℤ[√2] ⊂ ℤ[ω]`), its ring algebra
(`normSq_mul`, `normSq_add` cross-term, `|ωᵏy|² = |y|²`), and the gde value
`gdeNormSq x := gdePeel (normSq x)` together with the bridge to the
`dvdSqrt2Pow` predicate. This is the substrate KMM **Lemma 5**
(`gde(|x+y|²) ≥ min(m, 1 + ⌊(gde|x|² + gde|y|²)/2⌋)`) is proved over.

## Headline results

  * `ZOmega.normSq x := x * conj x` — squared modulus (a real `ℤ[√2]` element).
  * `ZOmega.isReal_normSq` — `conj (normSq x) = normSq x`.
  * `ZOmega.normSq_mul` / `normSq_add` / `normSq_pow` — ring algebra.
  * `ZOmega.normSq_omega_pow_mul` — `|ωᵏ·y|² = |y|²` (`ωᵏ` is a unit modulus 1).
  * `ZOmega.gdeNormSq x fuel := gdePeel (normSq x) fuel` — `gde(|x|², √2)`.
  * `ZOmega.dvdSqrt2Pow_normSq_iff_le_gdeNormSq` — predicate↔value bridge for
    `|x|²`.

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §3, Lemma 5 + Prop 1.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.GdeValue

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **Squared modulus** `|x|² = x · conj x`, a real element of `ℤ[√2] ⊂ ℤ[ω]`. -/
def normSq (x : ZOmega) : ZOmega := x * conj x

@[simp] theorem normSq_zero : normSq 0 = 0 := by rw [normSq, conj_zero, mul_zero]

@[simp] theorem normSq_one : normSq 1 = 1 := by rw [normSq, conj_one, mul_one]

/-- **`|x|²` is real** (conjugation-fixed): `conj (normSq x) = normSq x`. -/
theorem isReal_normSq (x : ZOmega) : conj (normSq x) = normSq x := by
  rw [normSq, conj_mul, conj_conj, mul_comm]

/-- **`normSq` is multiplicative**: `|x·y|² = |x|²·|y|²`. -/
theorem normSq_mul (x y : ZOmega) : normSq (x * y) = normSq x * normSq y := by
  simp only [normSq, conj_mul]; ring

/-- **Squared modulus of a sum** (the cross-term KMM Lemma 5 analyzes):
`|x+y|² = |x|² + |y|² + (x·conj y + y·conj x)`. -/
theorem normSq_add (x y : ZOmega) :
    normSq (x + y) = normSq x + normSq y + (x * conj y + y * conj x) := by
  simp only [normSq, conj_add]; ring

/-- **`normSq` of a power**: `|x^k|² = |x|²^k`. -/
theorem normSq_pow (x : ZOmega) (k : ℕ) : normSq (x ^ k) = normSq x ^ k := by
  induction k with
  | zero => simp only [pow_zero, normSq_one]
  | succ n ih => rw [pow_succ, normSq_mul, ih, pow_succ]

/-- **`|ω|² = 1`** (`ω` is a unit of modulus one). -/
@[simp] theorem normSq_omega : normSq ω = 1 := by decide

/-- **`|ωᵏ|² = 1`**. -/
@[simp] theorem normSq_omega_pow (k : ℕ) : normSq (ω ^ k) = 1 := by
  rw [normSq_pow, normSq_omega, one_pow]

/-- **`|ωᵏ·y|² = |y|²`** (multiplying by the unit `ωᵏ` preserves the squared
modulus — the invariance KMM Lemma 3's `k`-search relies on). -/
theorem normSq_omega_pow_mul (k : ℕ) (y : ZOmega) : normSq (ω ^ k * y) = normSq y := by
  rw [normSq_mul, normSq_omega_pow, one_mul]

/-! ## gde of the squared modulus -/

/-- **`gde(|x|², √2)`**, fuel-bounded: the greatest dividing exponent of the
squared modulus. This is the quantity KMM Lemmas 3–5 track. -/
def gdeNormSq (x : ZOmega) (fuel : ℕ) : ℕ := gdePeel (normSq x) fuel

@[simp] theorem gdeNormSq_def (x : ZOmega) (fuel : ℕ) :
    gdeNormSq x fuel = gdePeel (normSq x) fuel := rfl

/-- **Predicate↔value bridge for `|x|²`**: for `m ≤ fuel`,
`√2^m ∣ |x|² ↔ m ≤ gdeNormSq x fuel`. -/
theorem dvdSqrt2Pow_normSq_iff_le_gdeNormSq {x : ZOmega} {m fuel : ℕ} (hm : m ≤ fuel) :
    dvdSqrt2Pow (normSq x) m ↔ m ≤ gdeNormSq x fuel :=
  dvdSqrt2Pow_iff_le_gdePeel hm

/-- **`|ωᵏ·y|²` has the same gde as `|y|²`** (modulus invariance lifted to gde). -/
theorem gdeNormSq_omega_pow_mul (k : ℕ) (y : ZOmega) (fuel : ℕ) :
    gdeNormSq (ω ^ k * y) fuel = gdeNormSq y fuel := by
  rw [gdeNormSq, gdeNormSq, normSq_omega_pow_mul]

end ZOmega

end SKEFTHawking.RossSelinger
