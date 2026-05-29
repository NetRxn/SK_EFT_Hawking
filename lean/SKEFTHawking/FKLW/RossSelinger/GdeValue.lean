/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — the greatest-dividing-exponent VALUE `gde(z, √2)`

`GdeSqrt2.lean` ships the divisibility *predicate* `dvdSqrt2Pow z m` (`√2^m ∣ z`,
i.e. `gde(z,√2) ≥ m`). KMM Lemma 3 / Lemma 5 (arXiv:1206.5236) reason over gde
*values* and their arithmetic (`gde(|x+y|²) ≥ 1 + ⌊(gde|x|² + gde|y|²)/2⌋`), so
this file ships a **`ℕ`-valued** gde computed by peeling `√2` up to a `fuel`
bound.

`gdePeel z fuel` counts the number of times `√2` divides `z`, capped at `fuel`.
Structural recursion on the fuel makes it terminate trivially and stay
`decide`-reducible. For `fuel ≥` the true `gde(z,√2)` it returns the exact gde;
the bridge to the predicate layer is

  `m ≤ fuel → (dvdSqrt2Pow z m ↔ m ≤ gdePeel z fuel)`   (`dvdSqrt2Pow_iff_le_gdePeel`)

so a single sufficiently large fuel computes the gde for every element occurring
in the KMM recursion (whose `√2`-levels are bounded by the matrix `sde`).

## Headline results

  * `ZOmega.gdePeel : ZOmega → ℕ → ℕ` — fuel-bounded gde.
  * `ZOmega.gdePeel_le_fuel` — `gdePeel z fuel ≤ fuel`.
  * `ZOmega.dvdSqrt2Pow_antitone` — `dvdSqrt2Pow` is antitone in the exponent.
  * `ZOmega.dvdSqrt2Pow_gdePeel` — `√2^(gdePeel z fuel) ∣ z`.
  * `ZOmega.dvdSqrt2Pow_iff_le_gdePeel` — the predicate ↔ value bridge.
  * `ZOmega.gdePeel_mono_fuel` — `gdePeel` is monotone, and stabilizes once
    `fuel` exceeds the true gde.

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §3 (gde), Lemmas 3–5, Prop 1.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.GdeSqrt2

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **Greatest dividing exponent `gde(z, √2)`, fuel-bounded**: the number of
times `√2` divides `z`, capped at `fuel`. Structural recursion on the fuel. -/
def gdePeel (z : ZOmega) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => if dividesSqrt2 z then gdePeel (divSqrt2 z) fuel + 1 else 0

@[simp] theorem gdePeel_zero (z : ZOmega) : gdePeel z 0 = 0 := rfl

theorem gdePeel_succ (z : ZOmega) (fuel : ℕ) :
    gdePeel z (fuel + 1)
      = if dividesSqrt2 z then gdePeel (divSqrt2 z) fuel + 1 else 0 := rfl

/-- **The fuel-bounded gde never exceeds the fuel**. -/
theorem gdePeel_le_fuel (z : ZOmega) (fuel : ℕ) : gdePeel z fuel ≤ fuel := by
  induction fuel generalizing z with
  | zero => simp
  | succ n ih =>
    rw [gdePeel_succ]
    split
    · exact Nat.succ_le_succ (ih (divSqrt2 z))
    · exact Nat.zero_le _

/-- **`dvdSqrt2Pow` is antitone in the exponent**: `m ≤ m'` and `√2^m' ∣ z`
imply `√2^m ∣ z`. -/
theorem dvdSqrt2Pow_antitone {z : ZOmega} {m m' : ℕ} (h : m ≤ m')
    (hd : dvdSqrt2Pow z m') : dvdSqrt2Pow z m := by
  rw [dvdSqrt2Pow_iff] at hd ⊢
  exact dvd_trans (pow_dvd_pow sqrt2 h) hd

/-- **`√2^(gdePeel z fuel)` genuinely divides `z`**: every peel is a real
`√2`-division. -/
theorem dvdSqrt2Pow_gdePeel (z : ZOmega) (fuel : ℕ) :
    dvdSqrt2Pow z (gdePeel z fuel) := by
  induction fuel generalizing z with
  | zero => exact trivial
  | succ n ih =>
    rw [gdePeel_succ]
    split
    · next hdiv => exact ⟨hdiv, ih (divSqrt2 z)⟩
    · exact trivial

/-- **The predicate ↔ value bridge**: for `m ≤ fuel`, `√2^m ∣ z` iff
`m ≤ gdePeel z fuel`. -/
theorem dvdSqrt2Pow_iff_le_gdePeel {z : ZOmega} {m fuel : ℕ} (hm : m ≤ fuel) :
    dvdSqrt2Pow z m ↔ m ≤ gdePeel z fuel := by
  induction fuel generalizing z m with
  | zero =>
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    simp
  | succ n ih =>
    cases m with
    | zero => simp
    | succ k =>
      rw [dvdSqrt2Pow_succ, gdePeel_succ]
      by_cases hdiv : dividesSqrt2 z
      · rw [if_pos hdiv, Nat.succ_le_succ_iff]
        have hk : k ≤ n := Nat.le_of_succ_le_succ hm
        constructor
        · rintro ⟨_, hrest⟩; exact (ih hk).mp hrest
        · intro hle; exact ⟨hdiv, (ih hk).mpr hle⟩
      · rw [if_neg hdiv]
        simp [hdiv]

/-- **`gdePeel` is monotone in the fuel**. -/
theorem gdePeel_mono_fuel (z : ZOmega) {f f' : ℕ} (h : f ≤ f') :
    gdePeel z f ≤ gdePeel z f' := by
  have hle : gdePeel z f ≤ f := gdePeel_le_fuel z f
  have hdvd : dvdSqrt2Pow z (gdePeel z f) := dvdSqrt2Pow_gdePeel z f
  exact (dvdSqrt2Pow_iff_le_gdePeel (le_trans hle h)).mp hdvd

end ZOmega

end SKEFTHawking.RossSelinger
