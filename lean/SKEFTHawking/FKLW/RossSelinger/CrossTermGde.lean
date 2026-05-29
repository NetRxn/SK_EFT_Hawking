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
import Mathlib.Data.ZMod.Basic

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

/-! ## The halving lemma `√2^(2m) ∣ |u|² ⟹ √2^m ∣ u` -/

/-- **Peeling a `√2` factor at the predicate level**:
`dvdSqrt2Pow (√2·z) (k+1) ↔ dvdSqrt2Pow z k` (`√2·z` is always `√2`-divisible
and its quotient is `z`). -/
theorem dvdSqrt2Pow_sqrt2_mul (z : ZOmega) (k : ℕ) :
    dvdSqrt2Pow (sqrt2 * z) (k + 1) ↔ dvdSqrt2Pow z k := by
  rw [dvdSqrt2Pow_succ, divSqrt2_sqrt2_mul]
  exact and_iff_right (dividesSqrt2_sqrt2_mul z)

/-- **Halving base case** (`m = 1`): `√2² ∣ |u|² ⟹ √2 ∣ u`, i.e.
`dvdSqrt2Pow (normSq u) 2 → dividesSqrt2 u`. The `ω³`- and constant-coordinates
of `|u|²` are even; reducing those evenness facts modulo `2` and the goal
`dividesSqrt2 u` (`u.a ≡ u.c ∧ u.b ≡ u.d`) all to `ZMod 2` leaves a finite
parity tautology, closed by `decide` over the four coordinate residues. -/
theorem dividesSqrt2_of_dvdSqrt2Pow_normSq_two {u : ZOmega}
    (h : dvdSqrt2Pow (normSq u) 2) : dividesSqrt2 u := by
  have h2 : (2 : ZOmega) ∣ normSq u := by
    have hp := (dvdSqrt2Pow_iff (normSq u) 2).mp h
    rwa [show (sqrt2 : ZOmega) ^ 2 = 2 from by decide] at hp
  obtain ⟨w, hw⟩ := h2
  -- the `ω³`- and constant-coordinates of `|u|²` are even
  have ca : ((normSq u).a : ZMod 2) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨w.a, by rw [hw, two_mul, add_a]; push_cast; ring⟩
  have cd : ((normSq u).d : ZMod 2) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨w.d, by rw [hw, two_mul, add_d]; push_cast; ring⟩
  -- reduce both evenness facts and the goal to `ZMod 2`, then `decide`
  have goal2 : (u.a : ZMod 2) = (u.c : ZMod 2) ∧ (u.b : ZMod 2) = (u.d : ZMod 2) := by
    simp only [normSq, mul_a, mul_d, conj_a, conj_b, conj_c, conj_d] at ca cd
    push_cast at ca cd
    revert ca cd
    generalize (u.a : ZMod 2) = A
    generalize (u.b : ZMod 2) = B
    generalize (u.c : ZMod 2) = C
    generalize (u.d : ZMod 2) = D
    revert A B C D
    decide
  obtain ⟨g1, g2⟩ := goal2
  refine ⟨?_, ?_⟩
  · have hac : ((u.a - u.c : ℤ) : ZMod 2) = 0 := by push_cast; rw [g1]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hac; omega
  · have hbd : ((u.b - u.d : ℤ) : ZMod 2) = 0 := by push_cast; rw [g2]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hbd; omega

/-- **The halving lemma** (`√2`-vs-`𝔭` ramification fact): `√2^(2m) ∣ |u|²`
implies `√2^m ∣ u`. Proved by induction on `m`: the base case
(`dividesSqrt2_of_dvdSqrt2Pow_normSq_two`) supplies `√2 ∣ u`, then
`|u|² = 2·|u/√2|² = √2²·|u/√2|²` lets two `√2`-peels (`dvdSqrt2Pow_sqrt2_mul`)
recurse. Validated by `scripts/kmm_zomega_reference_oracle.py` (0 violations). -/
theorem dvdSqrt2Pow_normSq_half : ∀ (m : ℕ) (u : ZOmega),
    dvdSqrt2Pow (normSq u) (2 * m) → dvdSqrt2Pow u m := by
  intro m
  induction m with
  | zero => intro u _; exact trivial
  | succ n ih =>
    intro u h
    have hdiv : dividesSqrt2 u :=
      dividesSqrt2_of_dvdSqrt2Pow_normSq_two (dvdSqrt2Pow_antitone (by omega) h)
    rw [dvdSqrt2Pow_succ]
    refine ⟨hdiv, ih (divSqrt2 u) ?_⟩
    have hns : normSq u = sqrt2 * (sqrt2 * normSq (divSqrt2 u)) := by
      conv_lhs => rw [(divSqrt2_spec hdiv).symm]
      rw [normSq_mul, normSq_sqrt2, show (2 : ZOmega) = sqrt2 * sqrt2 from by decide, mul_assoc]
    rw [hns, show 2 * (n + 1) = 2 * n + 1 + 1 from by ring] at h
    rw [dvdSqrt2Pow_sqrt2_mul, dvdSqrt2Pow_sqrt2_mul] at h
    exact h

end ZOmega

end SKEFTHawking.RossSelinger
