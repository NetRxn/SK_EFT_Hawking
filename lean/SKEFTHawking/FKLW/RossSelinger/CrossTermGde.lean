/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — the KMM Lemma 5 cross-term "+1" mechanism

KMM Lemma 5 (arXiv:1206.5236) bounds `gde(|x+y|², √2)` via the cross-term
`c = x·conj y + y·conj x` (a real element, `normSq_add`):

  `gde(|x+y|²) ≥ min(gde(√2^M), gde(c)) = min(M, gde(c))`     (non-archimedean)

and the "+1" in Lemma 5's `1 + ⌊(gde|x|² + gde|y|²)/2⌋` comes from a **clean,
valuation-free** estimate of `gde(c)`, validated numerically in
`scripts/kmm_zomega_reference_oracle.py` (0 violations) and routed here through
elementary `√2`-divisibility:

  * **Trace is always `√2`-divisible** (`dividesSqrt2_add_conj`):
    `√2 ∣ (w + conj w)` for *every* `w` (its `ω²`-coord is `0`, its constant
    coord is even, and its `ω³`/`ω`-coords are negatives).
  * Hence the **"+1" lemma** (`dvdSqrt2Pow_add_conj`): `√2^m ∣ u ⟹
    √2^(m+1) ∣ (u + conj u)` — factor `√2^m` out of `u` (and of `conj u`,
    since `conj` fixes `√2`), leaving a trace `√2`-divisible by the above.

Combined (next file) with the **halving** `√2^(2m) ∣ |u|² ⟹ √2^m ∣ u` and
`|u|² = |x|²·|y|²` (for `u = x·conj y`), this gives
`gde(c) ≥ 1 + ⌊(gde|x|² + gde|y|²)/2⌋` with no `v₂` closed form — the substrate
KMM Lemma 5 assembles from via the `GdeArith` non-archimedean toolkit.

## Headline results

  * `ZOmega.dividesSqrt2_add_conj` — `√2 ∣ (w + conj w)`.
  * `ZOmega.normSq_sqrt2` — `|√2|² = 2`.
  * `ZOmega.dvdSqrt2Pow_add_conj` — `√2^m ∣ u ⟹ √2^(m+1) ∣ (u + conj u)`.

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §3, Lemma 5.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.NormSqGde
import SKEFTHawking.FKLW.RossSelinger.GdeArith
import SKEFTHawking.FKLW.RossSelinger.Conj

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **The trace `w + conj w` is always `√2`-divisible**. In coordinates
`w + conj w = ⟨w.a − w.c, 0, w.c − w.a, 2·w.d⟩`, whose `ω²`-coord is `0`, whose
constant coord is even, and whose `ω³`/`ω`-coords are negatives — so it meets
the `dividesSqrt2` criterion `(a ≡ c) ∧ (b ≡ d) (mod 2)`. -/
theorem dividesSqrt2_add_conj (w : ZOmega) : dividesSqrt2 (w + conj w) := by
  unfold dividesSqrt2
  simp only [add_a, add_b, add_c, add_d, conj_a, conj_b, conj_c, conj_d]
  omega

/-- **`|√2|² = 2`** (`conj` fixes `√2`, so `|√2|² = √2·√2 = 2`). -/
@[simp] theorem normSq_sqrt2 : normSq sqrt2 = 2 := by decide

/-- **The KMM Lemma 5 "+1" lemma**: `√2^m ∣ u ⟹ √2^(m+1) ∣ (u + conj u)`.

Write `u = √2^m · v`; since `conj` fixes powers of `√2`, `conj u = √2^m · conj v`,
so `u + conj u = √2^m · (v + conj v)`. The trace `v + conj v` is `√2`-divisible
(`dividesSqrt2_add_conj`), supplying the extra factor of `√2`. -/
theorem dvdSqrt2Pow_add_conj {u : ZOmega} {m : ℕ} (h : dvdSqrt2Pow u m) :
    dvdSqrt2Pow (u + conj u) (m + 1) := by
  rw [dvdSqrt2Pow_iff] at h ⊢
  obtain ⟨v, hv⟩ := h
  have hcj : conj u = sqrt2 ^ m * conj v := by rw [hv, conj_mul, conj_sqrt2_pow]
  have hsum : u + conj u = sqrt2 ^ m * (v + conj v) := by rw [hcj, hv]; ring
  obtain ⟨t, ht⟩ := (dividesSqrt2_iff_dvd (v + conj v)).mp (dividesSqrt2_add_conj v)
  refine ⟨t, ?_⟩
  rw [hsum, ht, pow_succ]; ring

end ZOmega

end SKEFTHawking.RossSelinger
