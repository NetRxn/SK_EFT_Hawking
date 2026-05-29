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
import SKEFTHawking.FKLW.RossSelinger.UnitaryT
import SKEFTHawking.FKLW.RossSelinger.DenExpValuation
import SKEFTHawking.FKLW.RossSelinger.ReduceStepColumn
import SKEFTHawking.FKLW.RossSelinger.KMMLemma3Column
import SKEFTHawking.FKLW.RossSelinger.UnitColumnCongruence

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

/-- **Column cleared form** (for a unitary in the reduction regime): both column-0
entries clear at a *common* exponent `s` with lowest-terms numerators of equal gde
`j ∈ {0,1}`, and `μ(M) = denExp(|M₀₀|²) = 2s − j`.

For a unitary, `denExp(|M₀₀|²) = denExp(|M₁₀|²)` (`denExp_normSq_col0_eq`); with
`denExp(|z|²) = 2·denExp z − j_z` (`entry_cleared_form`) and `j_z ∈ {0,1}`, parity
forces `denExp(M₀₀) = denExp(M₁₀) =: s` and `j₀ = j₁ =: j`. So `s` clears both
entries to lowest-terms numerators `x, y` with `gde(|x|²) = gde(|y|²) = j`. -/
theorem column_cleared {M : Mat2} (hu : IsUnitaryT M) (h4 : 4 ≤ denExp (normSq (M 0 0))) :
    ∃ (s j : ℕ) (x y : ZOmega), 2 ≤ s ∧ j < 2 ∧
      (sqrt2 : ZOmegaSqrt2) ^ s * M 0 0 = of x ∧ (sqrt2 : ZOmegaSqrt2) ^ s * M 1 0 = of y ∧
      ZOmega.gdePeel (ZOmega.normSq x) 4 = j ∧ ZOmega.gdePeel (ZOmega.normSq y) 4 = j ∧
      denExp (normSq (M 0 0)) = 2 * s - j := by
  have hcol : denExp (normSq (M 0 0)) = denExp (normSq (M 1 0)) := denExp_normSq_col0_eq hu
  have hd0 : 2 ≤ denExp (M 0 0) := by have := denExp_normSq_le (M 0 0); omega
  have hd1 : 2 ≤ denExp (M 1 0) := by have := denExp_normSq_le (M 1 0); omega
  obtain ⟨x, hMx, hx1, hμ0⟩ := entry_cleared_form hd0
  obtain ⟨y, hMy, hy1, hμ1⟩ := entry_cleared_form hd1
  have hboth : denExp (M 0 0) = denExp (M 1 0) ∧
      ZOmega.gdePeel (ZOmega.normSq x) 4 = ZOmega.gdePeel (ZOmega.normSq y) 4 := by
    constructor <;> omega
  obtain ⟨hdeq, hgeq⟩ := hboth
  refine ⟨denExp (M 0 0), ZOmega.gdePeel (ZOmega.normSq x) 4, x, y,
    hd0, by omega, hMx, ?_, rfl, hgeq.symm, by omega⟩
  rw [hdeq]; exact hMy

/-- **`ωᵏ` clears trivially**: `ωS^k = of (ωᵏ)` (the runtime `ω` is `of ω`, and
`of` is multiplicative). -/
theorem ωS_pow_eq (k : ℕ) : CliffordTGate.ωS ^ k = of (ZOmega.ω ^ k) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, show CliffordTGate.ωS = of ZOmega.ω from rfl, ← of_mul]

/-- **The `μ`-decrease step (KMM Algorithm 1 iteration).** For a unitary `M` with
`μ(M) := denExp(|M₀₀|²) ≥ 4`, some `H·Tᵏ` reduction step strictly decreases `μ`:

  `∃ k, denExp(|(reduceStep M k)₀₀|²) < denExp(|M₀₀|²)`.

This is the fuel-sufficiency input for the `Nonempty KMMReduction` discharge. Proof:
clear column `0` at common exponent `s` (`column_cleared`) into lowest-terms `x, y`
with `gde(|x|²) = gde(|y|²) = j ∈ {0,1}` and `μ(M) = 2s − j`; the unit-column
congruences (`unit_col_congruences`) feed `kmm_lemma3_column` (target index `2`,
i.e. `Δgde = 3`), giving `k` with `gde(|x+ωᵏy|²) = j + 3`; the new top-left entry
clears as `√2^(s+1)·z' = x + ωᵏy` (`reduceStep_zero_zero`), so
`μ(reduceStep M k) = 2(s+1) − gde(|x+ωᵏy|²) ≤ 2s − j − 1 < μ(M)` (the `gdePeel`
fuel `2(s+1) ≥ 4` only increases the gde, by `gdePeel_mono_fuel`). -/
theorem mu_decrease {M : Mat2} (hu : IsUnitaryT M) (h4 : 4 ≤ denExp (normSq (M 0 0))) :
    ∃ k : Fin 4, denExp (normSq ((KMM.reduceStep M k) 0 0)) < denExp (normSq (M 0 0)) := by
  obtain ⟨s, j, x, y, hs2, hj2, hMx, hMy, hgx, hgy, hμM⟩ := column_cleared hu h4
  have h1 : normSq (M 0 0) + normSq (M 1 0) = 1 := unitary_col0_normSq hu
  obtain ⟨hP, hQ⟩ := unit_col_congruences hMx hMy h1 hs2
  obtain ⟨kn, hkn4, hgde⟩ := ZOmega.kmm_lemma3_column x y j hj2 hgx hgy hP hQ 2 (by omega)
  refine ⟨⟨kn, hkn4⟩, ?_⟩
  have hsq : (sqrt2 : ZOmegaSqrt2) ^ (s + 1) * invSqrt2 = sqrt2 ^ s := by
    rw [pow_succ, mul_assoc, sqrt2_mul_invSqrt2, mul_one]
  have hz' : (sqrt2 : ZOmegaSqrt2) ^ (s + 1) * ((KMM.reduceStep M ⟨kn, hkn4⟩) 0 0)
      = of (x + ZOmega.ω ^ kn * y) := by
    rw [KMM.reduceStep_zero_zero, show ((⟨kn, hkn4⟩ : Fin 4) : ℕ) = kn from rfl, ωS_pow_eq,
      of_add, of_mul, ← hMx, ← hMy, ← mul_assoc, hsq]
    ring
  have hμ' := denExp_normSq_eq_of_clearing (sqrt2_pow_normSq_clearing hz')
  have hmono : ZOmega.gdePeel (ZOmega.normSq (x + ZOmega.ω ^ kn * y)) 4
      ≤ ZOmega.gdePeel (ZOmega.normSq (x + ZOmega.ω ^ kn * y)) (2 * (s + 1)) :=
    ZOmega.gdePeel_mono_fuel _ (by omega)
  have hGle : ZOmega.gdePeel (ZOmega.normSq (x + ZOmega.ω ^ kn * y)) (2 * (s + 1)) ≤ 2 * (s + 1) :=
    ZOmega.gdePeel_le_fuel _ _
  rw [hμ', hμM]
  omega

end ZOmegaSqrt2

namespace KMM

open ZOmegaSqrt2

/-- **The KMM reduction measure** `μ(M) = sde(|z₀₀|²) = denExp(|M₀₀|²)` — the quantity
KMM Algorithm 1 decrements. (`chooseReductionComp` in `KMMCompute.lean` tracks the
*matrix* sde `sdeC`; this `μ` is the squared-modulus sde KMM actually uses.) -/
def muMeasure (M : Mat2) : ℕ := denExp (normSq (M 0 0))

/-- **The `μ`-tracking reduction selector**: the first `k ∈ {0,1,2,3}` whose
reduction step strictly lowers `μ`, or `none`. The KMM-faithful selector. -/
def chooseReductionMu (M : Mat2) : Option (Fin 4) :=
  (List.finRange 4).find? (fun k => decide (muMeasure (reduceStep M k) < muMeasure M))

/-- **By construction the selected `k` strictly reduces `μ`**. -/
theorem chooseReductionMu_reduces {M : Mat2} {k : Fin 4} (h : chooseReductionMu M = some k) :
    muMeasure (reduceStep M k) < muMeasure M := by
  rw [chooseReductionMu] at h
  have hp := List.find?_some h
  simpa using hp

/-- **Fuel-sufficiency**: for a unitary `M` with `μ(M) ≥ 4`, the selector succeeds.
This is the KMM Lemma 3 existence (via `ZOmegaSqrt2.mu_decrease`) packaged as the
`chooseReductionMu` success the recursion needs to keep descending. -/
theorem chooseReductionMu_succeeds {M : Mat2} (hu : IsUnitaryT M) (h4 : 4 ≤ muMeasure M) :
    ∃ k : Fin 4, chooseReductionMu M = some k := by
  obtain ⟨k, hk⟩ := mu_decrease hu h4
  have hsome : ((List.finRange 4).find?
      (fun j => decide (muMeasure (reduceStep M j) < muMeasure M))).isSome := by
    rw [List.find?_isSome]
    exact ⟨k, List.mem_finRange k, by simpa using hk⟩
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨k', hk'⟩

/-- **Finiteness substrate for the `𝕊₃` base case**: `μ(M) ≤ 3` bounds the top-left
entry's `√2`-denominator exponent, `denExp(M₀₀) ≤ 2`. (`μ = 2·denExp(M₀₀) − gde(|x|²)`
with `gde ≤ 1`, so `2·denExp(M₀₀) ≤ μ + 1 ≤ 4`.) Together with unitarity (`|M₀₀| ≤ 1`)
this makes the `μ ≤ 3` orbit finite — the precondition for the base-case coverage. -/
theorem denExp_le_two_of_muMeasure_le_three {M : Mat2} (h : muMeasure M ≤ 3) :
    denExp (M 0 0) ≤ 2 := by
  by_cases hd : denExp (M 0 0) ≤ 1
  · omega
  · have hd2 : 2 ≤ denExp (M 0 0) := by omega
    obtain ⟨x, hx, hg, hμ⟩ := entry_cleared_form hd2
    unfold muMeasure at h
    omega

end KMM

end SKEFTHawking.RossSelinger
