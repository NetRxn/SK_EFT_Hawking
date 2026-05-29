/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — non-archimedean gde arithmetic (KMM Lemma 5 toolkit)

KMM Lemma 5 (arXiv:1206.5236) bounds `gde(|x+y|², √2)` from the cross-term
expansion `|x+y|² = |x|² + |y|² + (x·conj y + y·conj x)`. The assembly of that
bound from the cross-term estimate uses the **non-archimedean** behaviour of the
`√2`-divisibility predicate `dvdSqrt2Pow` (`= gde(·,√2) ≥ m`):

  * closed under addition at a fixed level (`gde(p+q) ≥ min(gde p, gde q)`);
  * sub-additive-reverse under multiplication (`gde(z·w) ≥ gde z + gde w`);
  * `√2^m ∣ √2^m` and `√2^m ∣ 0`.

These are clean `dvd` facts (validated against `scripts/kmm_zomega_reference_oracle.py`
which numerically confirms the full Lemma 5 inequality they assemble). This file
ships the toolkit; the substantive cross-term bound
`gde(x·conj y + y·conj x) ≥ 1 + ⌊(gde|x|² + gde|y|²)/2⌋` and Lemma 5 itself build
on top of it.

## Headline results

  * `ZOmega.dvdSqrt2Pow_add` — `dvdSqrt2Pow z m → dvdSqrt2Pow w m → dvdSqrt2Pow (z+w) m`.
  * `ZOmega.dvdSqrt2Pow_min` — the `min`-level non-archimedean form.
  * `ZOmega.dvdSqrt2Pow_neg` / `dvdSqrt2Pow_zero` — closure facts.
  * `ZOmega.dvdSqrt2Pow_mul_of` — `dvdSqrt2Pow z a → dvdSqrt2Pow w b → dvdSqrt2Pow (z*w) (a+b)`.
  * `ZOmega.dvdSqrt2Pow_sqrt2_pow_self` — `dvdSqrt2Pow (√2^m) m`.
  * `ZOmega.gdePeel_add_ge` / `gdePeel_mul_ge` — the gde-value consequences.

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §3, Lemma 5.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.GdeValue

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **`√2^m ∣ 0`**: zero is divisible at every level. -/
@[simp] theorem dvdSqrt2Pow_zero_elt (m : ℕ) : dvdSqrt2Pow (0 : ZOmega) m := by
  rw [dvdSqrt2Pow_iff]; exact dvd_zero _

/-- **`dvdSqrt2Pow` is closed under negation**. -/
theorem dvdSqrt2Pow_neg {z : ZOmega} {m : ℕ} (h : dvdSqrt2Pow z m) :
    dvdSqrt2Pow (-z) m := by
  rw [dvdSqrt2Pow_iff] at h ⊢; exact (dvd_neg).mpr h

/-- **Non-archimedean closure under addition (same level)**:
`√2^m ∣ z` and `√2^m ∣ w` imply `√2^m ∣ (z+w)`. -/
theorem dvdSqrt2Pow_add {z w : ZOmega} {m : ℕ}
    (hz : dvdSqrt2Pow z m) (hw : dvdSqrt2Pow w m) : dvdSqrt2Pow (z + w) m := by
  rw [dvdSqrt2Pow_iff] at hz hw ⊢; exact dvd_add hz hw

/-- **Non-archimedean `min` form**: `gde(z+w) ≥ min(gde z, gde w)`, in predicate
form — `√2^a ∣ z`, `√2^b ∣ w` ⟹ `√2^(min a b) ∣ (z+w)`. -/
theorem dvdSqrt2Pow_min {z w : ZOmega} {a b : ℕ}
    (hz : dvdSqrt2Pow z a) (hw : dvdSqrt2Pow w b) :
    dvdSqrt2Pow (z + w) (min a b) :=
  dvdSqrt2Pow_add (dvdSqrt2Pow_antitone (min_le_left a b) hz)
    (dvdSqrt2Pow_antitone (min_le_right a b) hw)

/-- **Sub-additive-reverse under multiplication**: `√2^a ∣ z` and `√2^b ∣ w`
imply `√2^(a+b) ∣ (z·w)` (i.e. `gde(z·w) ≥ gde z + gde w`). -/
theorem dvdSqrt2Pow_mul_of {z w : ZOmega} {a b : ℕ}
    (hz : dvdSqrt2Pow z a) (hw : dvdSqrt2Pow w b) :
    dvdSqrt2Pow (z * w) (a + b) := by
  rw [dvdSqrt2Pow_iff] at hz hw ⊢
  rw [pow_add]
  exact mul_dvd_mul hz hw

/-- **`√2^m ∣ √2^m`**: a power of `√2` is divisible by itself at its own level
(`gde(√2^m) ≥ m`). -/
@[simp] theorem dvdSqrt2Pow_sqrt2_pow_self (m : ℕ) : dvdSqrt2Pow (sqrt2 ^ m) m := by
  rw [dvdSqrt2Pow_iff]

/-! ## gde-value consequences (via the predicate↔value bridge) -/

/-- **gde-value non-archimedean bound**: `min a b ≤ gdePeel (z+w) fuel` whenever
`√2^a ∣ z`, `√2^b ∣ w` and `min a b ≤ fuel`. -/
theorem gdePeel_add_ge {z w : ZOmega} {a b fuel : ℕ}
    (hz : dvdSqrt2Pow z a) (hw : dvdSqrt2Pow w b) (hf : min a b ≤ fuel) :
    min a b ≤ gdePeel (z + w) fuel :=
  (dvdSqrt2Pow_iff_le_gdePeel hf).mp (dvdSqrt2Pow_min hz hw)

/-- **gde-value product bound**: `a + b ≤ gdePeel (z*w) fuel` whenever
`√2^a ∣ z`, `√2^b ∣ w` and `a + b ≤ fuel`. -/
theorem gdePeel_mul_ge {z w : ZOmega} {a b fuel : ℕ}
    (hz : dvdSqrt2Pow z a) (hw : dvdSqrt2Pow w b) (hf : a + b ≤ fuel) :
    a + b ≤ gdePeel (z * w) fuel :=
  (dvdSqrt2Pow_iff_le_gdePeel hf).mp (dvdSqrt2Pow_mul_of hz hw)

end ZOmega

end SKEFTHawking.RossSelinger
