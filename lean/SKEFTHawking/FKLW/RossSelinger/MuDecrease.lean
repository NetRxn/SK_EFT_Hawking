/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — the `μ`-decrease engine (KMM Algorithm 1 step)

The KMM reduction measure is `μ(M) := denExp(|M₀₀|²) = sde(|z₀₀|²)` (the
squared-modulus smallest denominator exponent of the top-left entry, the quantity
KMM Algorithm 1 decrements). This file builds the engine that one `reduceStep`
strictly decreases `μ` whenever `μ(M) ≥ 4` — the fuel-sufficiency input for the
`Nonempty KMMReduction` discharge.

This first layer ships the **per-entry cleared-form** infrastructure:

  * `of_sqrt2_eq` — `of √2 = √2` (the `ℤ[ω]`-`√2` lifts to the `ZOmegaSqrt2`-`√2`).
  * `not_dividesSqrt2_clearedNum` — the cleared numerator at `denExp z` is in
    lowest terms (`√2 ∤ x`), from minimality of `denExp`.
  * `gdePeel_stabilizes` — `gdePeel z m = gdePeel z f` once `f` exceeds the value
    (`gdePeel z f < f`), reconciling the fuel-`4` `kmm_lemma3_column` with the
    fuel-`2s` clearing connection.
  * `denExp_normSq_le` — `denExp(|z|²) ≤ 2·denExp z`.
  * `entry_cleared_form` — for `denExp z ≥ 2`: the cleared numerator `x` has
    `gde(|x|²) ≤ 1` (KMM Lemma 4) and `denExp(|z|²) = 2·denExp z − gde(|x|²)`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected (kernel-pure).

-/

import SKEFTHawking.FKLW.RossSelinger.ClearingConnection
import SKEFTHawking.FKLW.RossSelinger.Lemma4Value

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **`gdePeel` stabilizes once the fuel exceeds the reached value**: if
`gdePeel z f < f` (peeling stopped before the fuel ran out — so the value is the
true gde) then any larger fuel gives the same value. Reconciles the fuel-`4`
`kmm_lemma3_column` with the fuel-`2s` `denExp` clearing connection. -/
theorem gdePeel_stabilizes {z : ZOmega} {f m : ℕ} (hlt : gdePeel z f < f) (hm : f ≤ m) :
    gdePeel z m = gdePeel z f := by
  refine le_antisymm ?_ (gdePeel_mono_fuel z hm)
  have hnd : ¬ dvdSqrt2Pow z (gdePeel z f + 1) := by
    intro hd
    have := (dvdSqrt2Pow_iff_le_gdePeel (by omega : gdePeel z f + 1 ≤ f)).mp hd
    omega
  by_contra hgt
  exact hnd (dvdSqrt2Pow_antitone (by omega : gdePeel z f + 1 ≤ gdePeel z m)
    (dvdSqrt2Pow_gdePeel z m))

end ZOmega

namespace ZOmegaSqrt2

/-- **`of √2 = √2`**: the `ℤ[ω]`-`√2` maps to the `ZOmegaSqrt2`-`√2`. -/
theorem of_sqrt2_eq : (of ZOmega.sqrt2) = (sqrt2 : ZOmegaSqrt2) := by
  have h := sqrt2_pow_eq 1
  rw [pow_one, pow_one] at h
  rw [← of_def] at h
  exact h.symm

/-- **The cleared numerator at `denExp z` is in lowest terms** (`√2 ∤ x`) when
`denExp z ≥ 1`. If `√2 ∣ x` then `x = √2·x'`, and cancelling one `√2` shows
`√2^(denExp z − 1)·z` is `ℤ[ω]`-valued, contradicting the minimality of `denExp z`. -/
theorem not_dividesSqrt2_clearedNum {z : ZOmegaSqrt2} {x : ZOmega}
    (hx : (sqrt2 : ZOmegaSqrt2) ^ denExp z * z = of x) (hpos : 1 ≤ denExp z) :
    ¬ ZOmega.dividesSqrt2 x := by
  intro hdvd
  have hw : ZOmega.sqrt2 * ZOmega.divSqrt2 x = x := ZOmega.divSqrt2_spec hdvd
  set w := ZOmega.divSqrt2 x with hwdef
  have hstep : (sqrt2 : ZOmegaSqrt2) ^ denExp z * z = sqrt2 * of w := by
    rw [hx, ← hw, of_mul, of_sqrt2_eq]
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hpos
  have hpow : (sqrt2 : ZOmegaSqrt2) ^ denExp z = sqrt2 * sqrt2 ^ t := by
    rw [ht, pow_add, pow_one]
  rw [hpow, mul_assoc] at hstep
  have hcancel : (sqrt2 : ZOmegaSqrt2) ^ t * z = of w := by
    have h2 := congrArg (fun u => invSqrt2 * u) hstep
    simp only [← mul_assoc, invSqrt2_mul_sqrt2, one_mul] at h2
    exact h2
  have hle : denExp z ≤ t := denExp_le_of_smul_eq_of hcancel
  omega

/-- **`denExp(|z|²) ≤ 2·denExp z`**: clearing `z` by `√2^(denExp z)` clears `|z|²`
by `√2^(2·denExp z)`. -/
theorem denExp_normSq_le (z : ZOmegaSqrt2) : denExp (normSq z) ≤ 2 * denExp z := by
  obtain ⟨x, hx⟩ := exists_of_sqrt2_pow_smul z
  exact denExp_le_of_smul_eq_of (sqrt2_pow_normSq_clearing hx)

/-- **Per-entry cleared form** (KMM Lemma 4, value form): for `denExp z ≥ 2`, the
cleared numerator `x` (`√2^(denExp z)·z = of x`) has squared-modulus gde `≤ 1`, and

  `denExp(|z|²) = 2·denExp z − gde(|x|²)`.

(`x` is lowest-terms by `not_dividesSqrt2_clearedNum` ⟹ `gde(|x|²) ≤ 1` by
`gdePeel_normSq_le_one_of_not_dividesSqrt2`; the `denExp` identity is the clearing
connection, with the fuel reconciled `2·denExp z → 4` by `gdePeel_stabilizes`.) -/
theorem entry_cleared_form {z : ZOmegaSqrt2} (hs : 2 ≤ denExp z) :
    ∃ x : ZOmega, (sqrt2 : ZOmegaSqrt2) ^ denExp z * z = of x ∧
      ZOmega.gdePeel (ZOmega.normSq x) 4 ≤ 1 ∧
      denExp (normSq z) = 2 * denExp z - ZOmega.gdePeel (ZOmega.normSq x) 4 := by
  obtain ⟨x, hx⟩ := exists_of_sqrt2_pow_smul z
  have hnd : ¬ ZOmega.dividesSqrt2 x := not_dividesSqrt2_clearedNum hx (by omega)
  have hle1 : ZOmega.gdePeel (ZOmega.normSq x) 4 ≤ 1 :=
    ZOmega.gdePeel_normSq_le_one_of_not_dividesSqrt2 hnd 4
  have hμ := denExp_normSq_eq_of_clearing (sqrt2_pow_normSq_clearing hx)
  have hstab : ZOmega.gdePeel (ZOmega.normSq x) (2 * denExp z) = ZOmega.gdePeel (ZOmega.normSq x) 4 :=
    ZOmega.gdePeel_stabilizes (by omega) (by omega)
  exact ⟨x, hx, hle1, by rw [hμ, hstab]⟩

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
