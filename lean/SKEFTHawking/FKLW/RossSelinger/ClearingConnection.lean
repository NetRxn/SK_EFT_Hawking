/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — the clearing connection (ZOmegaSqrt2 sde ↔ ZOmega gde)

KMM tracks `sde(|z|²) = denExp (normSq z)` for the matrix entries `z : ZOmegaSqrt2`
(= `ℤ[1/√2, i]`), while KMM Lemma 3 — and our `kmm_lemma3_column` — controls the
**`√2`-gde** `gdePeel (ZOmega.normSq x)` of the *cleared numerator* `x : ℤ[ω]`. This
file ships the bridge between the two: clearing `z` by its denominator exponent and
relating the squared-modulus denominator exponent to the numerator's gde.

For `z : ZOmegaSqrt2` with `s = denExp z` and cleared numerator `x` (so
`√2^s · z = of x`), the squared modulus clears at `2s`:

  `√2^(2s) · |z|² = of (|x|²)`     (`sqrt2_pow_normSq_clearing`)

and therefore

  `denExp (|z|²) = 2·s − gde(|x|², √2)`     (`denExp_normSq_eq_of_clearing`)

via `|z|² = (|x|²)/√2^(2s) = mk (|x|²) (2s)` and the complementarity
`lowestDenExp + gdePeel = fuel` (`ZOmega.lowestDenExp_add_gdePeel`) — `denExp`'s
engine `lowestDenExp` returns the *residual* exponent while `gdePeel` returns the
*peel count*, and they sum to the fuel.

## Headline results

  * `ZOmega.lowestDenExp_add_gdePeel` — `lowestDenExp z k + gdePeel z k = k`.
  * `ZOmegaSqrt2.normSq_of` — `|of x|² = of |x|²` (normSq commutes with clearing).
  * `ZOmegaSqrt2.sqrt2_pow_normSq_clearing` — `√2^(2s)·|z|² = of |x|²`.
  * `ZOmegaSqrt2.denExp_normSq_eq_of_clearing` — `denExp |z|² = 2s − gde(|x|²)`.
  * `ZOmegaSqrt2.denExp_normSq_clearing` — the packaged existential (with the
    cleared numerator).

This is the linchpin of integration plan (B): combined with `reduceStep_zero_zero`
(`|z'|² = |z+ωᵏw|²/2`) and `kmm_lemma3_column` it turns the residue-level reduction
existence into an actual `denExp(|z₀₀|²)` decrease (fuel-sufficiency).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected (kernel-pure).

-/

import SKEFTHawking.FKLW.RossSelinger.NormSqGde
import SKEFTHawking.FKLW.RossSelinger.Conj
import SKEFTHawking.FKLW.RossSelinger.Sde

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **`lowestDenExp` and `gdePeel` are complementary**: `lowestDenExp z k +
gdePeel z k = k`. Both run the same `√2`-peel recursion — `lowestDenExp` returns
the *residual* fuel (denominator exponent), `gdePeel` the *peel count* (gde) — so
they sum to the fuel. This is the bridge from `denExp`'s engine to the gde. -/
theorem lowestDenExp_add_gdePeel (z : ZOmega) (k : ℕ) :
    lowestDenExp z k + gdePeel z k = k := by
  induction k generalizing z with
  | zero => simp
  | succ n ih =>
    rw [lowestDenExp_succ, gdePeel_succ]
    by_cases h : dividesSqrt2 z
    · rw [if_pos h, if_pos h]; have := ih (divSqrt2 z); omega
    · rw [if_neg h, if_neg h]

end ZOmega

namespace ZOmegaSqrt2

/-- **`invSqrt2 ^ n = mk 1 n`** (the `n`-fold `1/√2` is the fraction `1/√2^n`). -/
theorem invSqrt2_pow_eq (n : ℕ) : (invSqrt2 : ZOmegaSqrt2) ^ n = mk 1 n := by
  induction n with
  | zero => rw [pow_zero, one_def]
  | succ m ih => rw [pow_succ, ih, invSqrt2_def, mk_mul]; norm_num

/-- **`normSq` commutes with clearing**: `|of x|² = of |x|²`. -/
@[simp] theorem normSq_of (x : ZOmega) : normSq (of x) = of (ZOmega.normSq x) := by
  rw [normSq, conj_of, ← of_mul, ZOmega.normSq]

/-- **The squared modulus clears at twice the exponent**: if `√2^s · z = of x`
(`x` the cleared numerator of `z`) then `√2^(2s) · |z|² = of |x|²`. The two
factors of `√2^s` clear `z` and `conj z` (the latter via `conj_sqrt2_pow`). -/
theorem sqrt2_pow_normSq_clearing {z : ZOmegaSqrt2} {s : ℕ} {x : ZOmega}
    (h : (sqrt2 : ZOmegaSqrt2) ^ s * z = of x) :
    (sqrt2 : ZOmegaSqrt2) ^ (2 * s) * normSq z = of (ZOmega.normSq x) := by
  have hconj : (sqrt2 : ZOmegaSqrt2) ^ s * conj z = of (ZOmega.conj x) := by
    rw [← conj_sqrt2_pow s, ← conj_mul, h, conj_of]
  calc (sqrt2 : ZOmegaSqrt2) ^ (2 * s) * normSq z
      = ((sqrt2 : ZOmegaSqrt2) ^ s * z) * ((sqrt2 : ZOmegaSqrt2) ^ s * conj z) := by
        rw [normSq, show 2 * s = s + s from by ring, pow_add]; ring
    _ = of x * of (ZOmega.conj x) := by rw [h, hconj]
    _ = of (ZOmega.normSq x) := by rw [← of_mul, ZOmega.normSq]

/-- **The clearing connection (value form)**: from the squared-modulus clearing
`√2^(2s) · |z|² = of |x|²`, the squared-modulus denominator exponent is

  `denExp (|z|²) = 2·s − gde(|x|², √2)`.

`|z|² = (|x|²)/√2^(2s) = mk |x|² (2s)`, so `denExp |z|² = lowestDenExp |x|² (2s)`,
and complementarity (`lowestDenExp_add_gdePeel`) rewrites it as `2s − gdePeel`. -/
theorem denExp_normSq_eq_of_clearing {z : ZOmegaSqrt2} {s : ℕ} {x : ZOmega}
    (hclear : (sqrt2 : ZOmegaSqrt2) ^ (2 * s) * normSq z = of (ZOmega.normSq x)) :
    denExp (normSq z) = 2 * s - ZOmega.gdePeel (ZOmega.normSq x) (2 * s) := by
  have hz : normSq z = mk (ZOmega.normSq x) (2 * s) := by
    have hmul : (invSqrt2 : ZOmegaSqrt2) ^ (2 * s) * ((sqrt2 : ZOmegaSqrt2) ^ (2 * s) * normSq z)
              = (invSqrt2 : ZOmegaSqrt2) ^ (2 * s) * of (ZOmega.normSq x) := by rw [hclear]
    rw [← mul_assoc, ← mul_pow, invSqrt2_mul_sqrt2, one_pow, one_mul] at hmul
    rw [hmul, invSqrt2_pow_eq, of_def, mk_mul]; norm_num
  rw [hz, denExp_mk]
  have := ZOmega.lowestDenExp_add_gdePeel (ZOmega.normSq x) (2 * s)
  omega

/-- **The clearing connection (packaged)**: every `z : ZOmegaSqrt2` has a cleared
numerator `x` (`√2^(denExp z) · z = of x`) with

  `denExp (|z|²) = 2·(denExp z) − gde(|x|², √2)`.

The bridge from the matrix-entry `sde(|z|²)` (what KMM tracks) to the `ℤ[ω]`-gde of
the cleared numerator (what `kmm_lemma3_column` controls). -/
theorem denExp_normSq_clearing (z : ZOmegaSqrt2) :
    ∃ x : ZOmega, (sqrt2 : ZOmegaSqrt2) ^ denExp z * z = of x ∧
      denExp (normSq z) = 2 * denExp z - ZOmega.gdePeel (ZOmega.normSq x) (2 * denExp z) := by
  obtain ⟨x, hx⟩ := exists_of_sqrt2_pow_smul z
  exact ⟨x, hx, denExp_normSq_eq_of_clearing (sqrt2_pow_normSq_clearing hx)⟩

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
