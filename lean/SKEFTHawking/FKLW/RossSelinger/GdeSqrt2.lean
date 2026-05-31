/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — greatest-dividing-exponent substrate (`√2^m ∣ z`)

KMM's exact synthesis (arXiv:1206.5236) uses the *greatest dividing
exponent* `gde(z, √2)` — the largest `m` with `√2^m ∣ z` in `ℤ[ω]`.
Lemma 4 bounds `gde(|x|²) ≤ 1` for cleared unitary entries, and Lemma 3 /
Prop 1 reason over `√2`-divisibility of `|x + ω^k y|²`.

This file ships the **decidable divisibility predicate** `dvdSqrt2Pow z m`
(`√2^m ∣ z`, computed by peeling `√2` factors `m` times via `divSqrt2`)
and proves it characterizes genuine divisibility `√2^m ∣ z`. The peel
form is `decide`-friendly (finite, structural on `m`),
which is what the KMM residue/parity case-analysis needs.

## Headline results

  * `ZOmega.dividesSqrt2_iff_dvd` — `dividesSqrt2 z ↔ √2 ∣ z`.
  * `ZOmega.dvdSqrt2Pow z m` — decidable predicate (peel `m` times).
  * `ZOmega.dvdSqrt2Pow_iff` — `dvdSqrt2Pow z m ↔ √2^m ∣ z`.

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §2 (gde) + §3 (Lemma 3,
    Prop 1).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.Sde

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **`dividesSqrt2` is genuine divisibility by `√2`**. -/
theorem dividesSqrt2_iff_dvd (z : ZOmega) : dividesSqrt2 z ↔ sqrt2 ∣ z := by
  constructor
  · intro h; exact ⟨divSqrt2 z, (divSqrt2_spec h).symm⟩
  · rintro ⟨w, rfl⟩; exact dividesSqrt2_sqrt2_mul w

/-- **Decidable `√2^m`-divisibility**, computed by peeling `√2` factors
`m` times. `dvdSqrt2Pow z (m+1)` holds iff `√2 ∣ z` and the quotient is
`√2^m`-divisible. -/
def dvdSqrt2Pow (z : ZOmega) : ℕ → Prop
  | 0 => True
  | m + 1 => dividesSqrt2 z ∧ dvdSqrt2Pow (divSqrt2 z) m

@[simp] theorem dvdSqrt2Pow_zero (z : ZOmega) : dvdSqrt2Pow z 0 = True := rfl

theorem dvdSqrt2Pow_succ (z : ZOmega) (m : ℕ) :
    dvdSqrt2Pow z (m + 1) = (dividesSqrt2 z ∧ dvdSqrt2Pow (divSqrt2 z) m) := rfl

instance decDvdSqrt2Pow (z : ZOmega) (m : ℕ) : Decidable (dvdSqrt2Pow z m) := by
  induction m generalizing z with
  | zero => exact isTrue trivial
  | succ n ih =>
    have : Decidable (dvdSqrt2Pow (divSqrt2 z) n) := ih (divSqrt2 z)
    rw [dvdSqrt2Pow_succ]
    exact inferInstance

/-- **`dvdSqrt2Pow` characterizes genuine `√2^m`-divisibility**:
`dvdSqrt2Pow z m ↔ √2^m ∣ z`. -/
theorem dvdSqrt2Pow_iff (z : ZOmega) (m : ℕ) : dvdSqrt2Pow z m ↔ sqrt2 ^ m ∣ z := by
  induction m generalizing z with
  | zero => simp
  | succ n ih =>
    rw [dvdSqrt2Pow_succ]
    constructor
    · rintro ⟨hdiv, hrest⟩
      obtain ⟨u, hu⟩ := (ih (divSqrt2 z)).mp hrest
      refine ⟨u, ?_⟩
      rw [pow_succ, mul_comm (sqrt2 ^ n) sqrt2, mul_assoc, ← hu, divSqrt2_spec hdiv]
    · rintro ⟨u, hu⟩
      have hdiv : dividesSqrt2 z := by
        rw [dividesSqrt2_iff_dvd]
        exact ⟨sqrt2 ^ n * u, by rw [hu, pow_succ]; ring⟩
      refine ⟨hdiv, (ih (divSqrt2 z)).mpr ?_⟩
      refine ⟨u, ?_⟩
      apply sqrt2_mul_cancel
      rw [divSqrt2_spec hdiv, hu]
      rw [pow_succ]; ring

end ZOmega

end SKEFTHawking.RossSelinger
