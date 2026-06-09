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

/-! ### The column denominator exponent and the induction skeleton

The column lemma inducts on the **column denominator exponent** `colDenExp v` (the max `√2`-denominator
exponent over the entries) down to the base case `colDenExp v = 0`. Each reduction step left-multiplies
by an `O(1)` realizable `g` lowering `colDenExp`, so by `smul_left` (inc 10) the realizability climbs
back up. This isolates the **one** remaining synthesis piece — the reduction step — as `ReductionStep`. -/

/-- **Column denominator exponent**: the largest `√2`-denominator exponent among the entries. The
measure the dim-4 column lemma inducts on. -/
def colDenExp (v : Fin 2 × Fin 2 → ZOmegaSqrt2) : ℕ := Finset.univ.sup fun i => denExp (v i)

/-- Each entry's denominator exponent is `≤ colDenExp`. -/
theorem denExp_le_colDenExp (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (i : Fin 2 × Fin 2) :
    denExp (v i) ≤ colDenExp v :=
  Finset.le_sup (f := fun i => denExp (v i)) (Finset.mem_univ i)

/-- **Base case via the measure**: a `colDenExp`-`0` unit column is column-realizable (every entry has
denominator exponent `0`, so `base_case` applies). -/
theorem isColRealizableWithin_of_colDenExp_zero (v : Fin 2 × Fin 2 → ZOmegaSqrt2)
    (h0 : colDenExp v = 0) (hunit : ∑ i, normSq (v i) = 1) : ∃ L, IsColRealizableWithin v L :=
  base_case v (fun i => Nat.le_zero.mp (h0 ▸ denExp_le_colDenExp v i)) hunit

/-- **The reduction-step property** (budget `C`): every unit column with positive denominator exponent
factors as `g · v'` for a realizable `g` (within `C`) and a **strictly-lower-`colDenExp`** unit column
`v'`. This is the dim-4 Giles–Selinger residue reduction — the one remaining synthesis brick (it reuses
the dim-2 `reduceStep` + `kmm_lemma3`, the tolerated-`native_decide` site Track 3 will eliminate). -/
def ReductionStep (C : ℕ) : Prop :=
  ∀ v : Fin 2 × Fin 2 → ZOmegaSqrt2, (∑ i, normSq (v i) = 1) → 0 < colDenExp v →
    ∃ (g : Mat4) (v' : Fin 2 × Fin 2 → ZOmegaSqrt2),
      IsRealizableWithin g C ∧ v = g.mulVec v' ∧ (∑ i, normSq (v' i) = 1) ∧
        colDenExp v' < colDenExp v

/-- **The dim-4 column lemma, reduced to the reduction step.** Given the reduction step (budget `C`),
**every unit column is column-realizable** — by strong induction on `colDenExp`: at `0` use the base
case; otherwise factor `v = g · v'` (lower `colDenExp`), realize `v'` by induction, and climb back via
`smul_left` (`g` realizable, budgets add). This is the unconditional column lemma modulo the single
residue-reduction brick; assembling that brick (reusing the dim-2 substrate) completes circuit `C`. -/
theorem colLemma_of_reductionStep {C : ℕ} (hred : ReductionStep C)
    (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (hunit : ∑ i, normSq (v i) = 1) :
    ∃ L, IsColRealizableWithin v L := by
  suffices H : ∀ n v, colDenExp v = n → (∑ i, normSq (v i) = 1) → ∃ L, IsColRealizableWithin v L from
    H (colDenExp v) v rfl hunit
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro v hn hv
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact isColRealizableWithin_of_colDenExp_zero v (hn.trans h0) hv
    · obtain ⟨g, v', hg, hveq, hv'unit, hv'lt⟩ := hred v hv (hn ▸ hpos)
      obtain ⟨L', hL'⟩ := IH (colDenExp v') (hn ▸ hv'lt) v' rfl hv'unit
      refine ⟨C + L', ?_⟩
      rw [hveq]
      exact IsColRealizableWithin.smul_left hg hL'

end Gate2
end SKEFTHawking.RossSelinger
