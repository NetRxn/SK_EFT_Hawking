/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 14) — the dim-4 column-lemma base case, assembled

The dim-4 exact-synthesis column lemma inducts on the denominator exponent down to `0`. This file
assembles the **base case**: a denominator-exponent-`0` unit column is column-realizable.

The pieces: a `denExp 0` entry is `ℤ[ω]`-valued (`of z`, via `denExp_le_iff` at `k = 0`); the unit
identity `Σ |v i|² = 1` transports through the ring embedding (`normSq_of`, `of` injective) to
`Σ |z i|² = 1` over `ℤ[ω]`; the base-case number theory (`unit_col_zero_denExp_structure` +
`normSq_eq_one_iff_omega_pow`) gives one unit entry `z_{i₀} = ωᵏ` with the rest `0`; so the column is
`ωᵏ·e_{i₀}`, realizable by `isColRealizableWithin_omega_pow_basis` (inc 13).

## Headline

  * `Gate2.base_case` — **a denExp-0 unit column `v : Fin 2 × Fin 2 → ℤ[ω][1/√2]` is
    column-realizable** (within `k + 2 ≤ 9` `Gate2` gates). The induction anchor of the column lemma.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.ColumnSynthesis
import SKEFTHawking.FKLW.RossSelinger.ColumnBaseCase
import SKEFTHawking.FKLW.RossSelinger.ClearingConnection
import SKEFTHawking.FKLW.RossSelinger.Sde

set_option autoImplicit false

open scoped Matrix

namespace SKEFTHawking.RossSelinger
namespace Gate2

open ZOmegaSqrt2

/-- **The dim-4 column-lemma base case.** A column `v : Fin 2 × Fin 2 → ZOmegaSqrt2` with denominator
exponent `0` everywhere (`ℤ[ω]`-valued entries) that is a unit vector (`Σ |v i|² = 1`) is the first
column of a `Gate2` Clifford+T word — it equals `ωᵏ·e_{i₀}` (one unit entry, the rest `0`) and is
realizable within `k + 2` gates. -/
theorem base_case (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (hden : ∀ i, denExp (v i) = 0)
    (hunit : ∑ i, normSq (v i) = 1) :
    ∃ L, IsColRealizableWithin v L := by
  have hinj : Function.Injective (of : ZOmega → ZOmegaSqrt2) := by
    intro a b hab; rw [of_def, of_def, mk_eq_mk_iff] at hab; simpa using hab
  have hof : ∀ i, ∃ z, v i = of z := fun i => by
    obtain ⟨w, hw⟩ := (denExp_le_iff (x := v i) (k := 0)).mp (le_of_eq (hden i))
    refine ⟨w, ?_⟩
    rw [← one_mul (v i), ← pow_zero (sqrt2 : ZOmegaSqrt2)]
    exact hw
  choose z hz using hof
  have hzsum : ∑ i, ZOmega.normSq (z i) = 1 := by
    have hof1 : of (∑ i, ZOmega.normSq (z i)) = (1 : ZOmegaSqrt2) := by
      rw [show of (∑ i, ZOmega.normSq (z i)) = ∑ i, of (ZOmega.normSq (z i)) from
        map_sum ofRingHom _ _, ← hunit]
      exact Finset.sum_congr rfl fun i _ => by rw [hz i, normSq_of]
    exact hinj (hof1.trans of_one.symm)
  obtain ⟨i₀, hone, hzero⟩ := ZOmega.unit_col_zero_denExp_structure z hzsum
  obtain ⟨k, _, hzk⟩ := ZOmega.normSq_eq_one_iff_omega_pow.mp hone
  refine ⟨k + 2, ?_⟩
  have hv_eq : v = (fun i => if i = i₀ then CliffordTGate.ωS ^ k else 0) := by
    funext i
    rw [hz i]
    by_cases hi : i = i₀
    · subst hi
      rw [hzk, if_pos rfl]
      have : of (ZOmega.ω ^ k) = (of ZOmega.ω) ^ k := map_pow ofRingHom ZOmega.ω k
      rw [this]; rfl
    · rw [hzero i hi, if_neg hi]; rfl
  rw [hv_eq]
  exact isColRealizableWithin_omega_pow_basis k i₀.1 i₀.2

end Gate2
end SKEFTHawking.RossSelinger
