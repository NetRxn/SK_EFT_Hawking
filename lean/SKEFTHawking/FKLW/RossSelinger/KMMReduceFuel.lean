/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — the `kmmReduce` fuel recursion + correctness

Assembles the runtime KMM synthesis recursion from the computable step
(`reduceStep`/`chooseReductionComp`, `KMMCompute.lean`) and the S/Z-compressed
reconstruction word (`reconWordC`):

  `kmmReduceFuel base n M` = peel `H·Tᵏ` (via the `chooseReductionComp` selector)
  up to `n` times, prepending each reconstruction syllable `reconWordC k`, then
  emit the base-finder word `base M` once no reducing `k` is found or the fuel
  runs out.

**Correctness (`interp_kmmReduceFuel`) is fully Lemma-3-INDEPENDENT**: it needs
only that each reconstruction step left-inverts the peel
(`interp_reconWordC_reduceStep`, purely algebraic) and that the base finder is
correct on realizable inputs. It does NOT need the sde to actually decrease — so
this is the `correct` field of `KMMReduction`, discharged *now*, parameterized on
a base finder.

What remains for the full discharge (DR-gated, see roadmap §3b): KMM **Lemma 3**
(the `chooseReductionComp` search succeeds when `sdeC ≥ 4`) gives termination /
fuel-sufficiency and the **length bound** `≤ N₃ + 4·sdeC` (each syllable is
`≤ 4` gates by `reconWordC_length_le_four`); plus the base finder itself
(`cliffordLookup`/𝕊₃ + the `N₃` numeral). Together those + this correctness
theorem construct a concrete `KMMReduction` and discharge `Nonempty KMMReduction`.

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) Algorithm 1.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.KMMCompute

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate

/-- **The KMM synthesis fuel recursion**: peel `H·Tᵏ` (selected by
`chooseReductionComp`) up to `n` times, prepending each reconstruction syllable
`reconWordC k`; emit `base M` at the leaves. -/
def kmmReduceFuel (base : Mat2 → List CliffordTGate) : ℕ → Mat2 → List CliffordTGate
  | 0, M => base M
  | n + 1, M =>
    match chooseReductionComp M with
    | some k => reconWordC (k : ℕ) ++ kmmReduceFuel base n (reduceStep M k)
    | none => base M

@[simp] theorem kmmReduceFuel_zero (base : Mat2 → List CliffordTGate) (M : Mat2) :
    kmmReduceFuel base 0 M = base M := rfl

/-- **Correctness of the fuel recursion** (Lemma-3-independent): if the base
finder is correct on realizable matrices, then `interp (kmmReduceFuel base n M) = M`
for every realizable `M`. Each peel is reconstructed exactly by `reconWordC`
(`interp_reconWordC_reduceStep`); realizability is preserved down the recursion
(`isCliffordTRealizable_H_T_pow_mul`); the base case is the hypothesis. -/
theorem interp_kmmReduceFuel (base : Mat2 → List CliffordTGate)
    (hbase : ∀ M, IsCliffordTRealizable M → interp (base M) = M) :
    ∀ (n : ℕ) (M : Mat2), IsCliffordTRealizable M → interp (kmmReduceFuel base n M) = M := by
  intro n
  induction n with
  | zero => intro M hM; rw [kmmReduceFuel_zero]; exact hbase M hM
  | succ n ih =>
    intro M hM
    cases hc : chooseReductionComp M with
    | none =>
      have he : kmmReduceFuel base (n + 1) M = base M := by simp only [kmmReduceFuel, hc]
      rw [he]; exact hbase M hM
    | some k =>
      have he : kmmReduceFuel base (n + 1) M
              = reconWordC (k : ℕ) ++ kmmReduceFuel base n (reduceStep M k) := by
        simp only [kmmReduceFuel, hc]
      have hstep : IsCliffordTRealizable (reduceStep M k) := by
        rw [reduceStep]; exact isCliffordTRealizable_H_T_pow_mul (k : ℕ) hM
      rw [he, interp_append, ih (reduceStep M k) hstep]
      exact interp_reconWordC_reduceStep M k

/-- **Fuel length bound** (Lemma-3-independent): if the base finder emits words of
length `≤ N₃`, then `(kmmReduceFuel base n M).length ≤ N₃ + 4·n`. Each peel adds
the `≤ 4`-gate syllable `reconWordC k` (`reconWordC_length_le_four`); there are at
most `n` peels. This is the per-step half of the KMM Corollary-1 length bound
`≤ N₃ + 4·sde` — the remaining gap (fuel `n = sde` suffices, i.e. at most `sde`
peels reach the base) is exactly KMM Lemma 3 (DR-gated). -/
theorem length_kmmReduceFuel_le (base : Mat2 → List CliffordTGate) (N₃ : ℕ)
    (hbase : ∀ M, (base M).length ≤ N₃) :
    ∀ (n : ℕ) (M : Mat2), (kmmReduceFuel base n M).length ≤ N₃ + 4 * n := by
  intro n
  induction n with
  | zero => intro M; rw [kmmReduceFuel_zero]; simpa using hbase M
  | succ n ih =>
    intro M
    cases hc : chooseReductionComp M with
    | none =>
      have he : kmmReduceFuel base (n + 1) M = base M := by simp only [kmmReduceFuel, hc]
      rw [he]; exact le_trans (hbase M) (by omega)
    | some k =>
      have he : kmmReduceFuel base (n + 1) M
              = reconWordC (k : ℕ) ++ kmmReduceFuel base n (reduceStep M k) := by
        simp only [kmmReduceFuel, hc]
      have h1 : (reconWordC (k : ℕ)).length ≤ 4 :=
        reconWordC_length_le_four (k : ℕ) (by have := k.isLt; omega)
      have h2 := ih (reduceStep M k)
      rw [he, List.length_append]
      omega

end KMM

end SKEFTHawking.RossSelinger
