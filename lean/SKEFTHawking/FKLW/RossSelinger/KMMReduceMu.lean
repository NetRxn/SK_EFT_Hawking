/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — the `μ`-tracking KMM recursion (correct + length-bounded)

`kmmReduceMu base n M` is the KMM Algorithm-1 recursion driven by the
KMM-faithful `μ`-selector `chooseReductionMu` (squared-modulus sde, not the
scaffold's matrix sde): peel `H·Tᵏ` (selected by `chooseReductionMu`) up to `n`
times, prepending each reconstruction syllable `reconWordC k`; emit `base M` at the
leaves.

  * `interp_kmmReduceMu` — **correctness with termination**: for realizable `M` with
    `μ(M) ≤ n` (fuel sufficient), `interp (kmmReduceMu base n M) = M`, provided the
    base finder is correct on realizable matrices with `μ ≤ 3`. The recursion
    provably bottoms out at `μ ≤ 3` (fuel-sufficiency `chooseReductionMu_succeeds`:
    a unitary with `μ ≥ 4` always has a reducing `k`, so `chooseReductionMu = none`
    forces `μ ≤ 3`), so the base finder need only handle the `𝕊₃` orbit.
  * `length_kmmReduceMu` — **KMM Corollary 1**: if the base emits words of length
    `≤ N₃`, then `(kmmReduceMu base n M).length ≤ N₃ + 4·n`. With `n = μ(M)` this is
    `≤ N₃ + 4·sde(|z₀₀|²)` — the honest KMM gate-count bound.

Together with `n := μ(M)` (so `μ(M) ≤ n` is trivial) and a `cliffordLookup` base
finder (correct on `μ ≤ 3`, length `≤ N₃`), these construct a concrete
`KMMReduction` and discharge `Nonempty KMMReduction`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.MuDecrease
import SKEFTHawking.FKLW.RossSelinger.UnitaryClosure

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2

/-- **The `μ`-tracking KMM synthesis recursion**: peel `H·Tᵏ` (selected by
`chooseReductionMu`) up to `n` times, prepending each reconstruction syllable
`reconWordC k`; emit `base M` at the leaves. -/
def kmmReduceMu (base : Mat2 → List CliffordTGate) : ℕ → Mat2 → List CliffordTGate
  | 0, M => base M
  | n + 1, M =>
    match chooseReductionMu M with
    | some k => reconWordC (k : ℕ) ++ kmmReduceMu base n (reduceStep M k)
    | none => base M

@[simp] theorem kmmReduceMu_zero (base : Mat2 → List CliffordTGate) (M : Mat2) :
    kmmReduceMu base 0 M = base M := rfl

/-- **Correctness with termination**: for realizable `M` with `μ(M) ≤ n`,
`interp (kmmReduceMu base n M) = M`, given the base finder correct on realizable
`μ ≤ 3` matrices. The recursion bottoms at `μ ≤ 3` because a unitary with `μ ≥ 4`
always has a reducing `k` (`chooseReductionMu_succeeds`, via `mu_decrease`), so
`chooseReductionMu M = none ⟹ μ(M) ≤ 3`; each peel is reconstructed exactly by
`reconWordC` and preserves realizability. -/
theorem interp_kmmReduceMu (base : Mat2 → List CliffordTGate)
    (hbase : ∀ M, IsCliffordTRealizable M → muMeasure M ≤ 3 → interp (base M) = M) :
    ∀ (n : ℕ) (M : Mat2), IsCliffordTRealizable M → muMeasure M ≤ n →
      interp (kmmReduceMu base n M) = M := by
  intro n
  induction n with
  | zero => intro M hM hμ; rw [kmmReduceMu]; exact hbase M hM (by omega)
  | succ n ih =>
    intro M hM hμ
    cases hc : chooseReductionMu M with
    | none =>
      have he : kmmReduceMu base (n + 1) M = base M := by simp only [kmmReduceMu, hc]
      rw [he]
      have hu := isUnitaryT_of_isCliffordTRealizable hM
      have h3 : muMeasure M ≤ 3 := by
        by_contra h
        obtain ⟨k, hk⟩ := chooseReductionMu_succeeds hu (by omega)
        rw [hc] at hk; simp at hk
      exact hbase M hM h3
    | some k =>
      have he : kmmReduceMu base (n + 1) M
              = reconWordC (k : ℕ) ++ kmmReduceMu base n (reduceStep M k) := by
        simp only [kmmReduceMu, hc]
      have hred : muMeasure (reduceStep M k) < muMeasure M := chooseReductionMu_reduces hc
      have hstepR : IsCliffordTRealizable (reduceStep M k) := by
        rw [reduceStep]; exact isCliffordTRealizable_H_T_pow_mul (k : ℕ) hM
      rw [he, interp_append, ih (reduceStep M k) hstepR (by omega), interp_reconWordC_reduceStep]

/-- **Length bound (KMM Corollary 1)**: if the base emits words of length `≤ N₃`,
then `(kmmReduceMu base n M).length ≤ N₃ + 4·n`. Each peel adds the `≤ 4`-gate
syllable `reconWordC k`; at most `n` peels. With `n = μ(M)` this is the honest
`n_g ≤ N₃ + 4·sde(|z₀₀|²)`. -/
theorem length_kmmReduceMu (base : Mat2 → List CliffordTGate) (N₃ : ℕ)
    (hbase : ∀ M, (base M).length ≤ N₃) :
    ∀ (n : ℕ) (M : Mat2), (kmmReduceMu base n M).length ≤ N₃ + 4 * n := by
  intro n
  induction n with
  | zero => intro M; rw [kmmReduceMu]; simpa using hbase M
  | succ n ih =>
    intro M
    cases hc : chooseReductionMu M with
    | none =>
      have he : kmmReduceMu base (n + 1) M = base M := by simp only [kmmReduceMu, hc]
      rw [he]; exact le_trans (hbase M) (by omega)
    | some k =>
      have he : kmmReduceMu base (n + 1) M
              = reconWordC (k : ℕ) ++ kmmReduceMu base n (reduceStep M k) := by
        simp only [kmmReduceMu, hc]
      have h1 : (reconWordC (k : ℕ)).length ≤ 4 :=
        reconWordC_length_le_four (k : ℕ) (by have := k.isLt; omega)
      have h2 := ih (reduceStep M k)
      rw [he, List.length_append]; omega

end KMM

end SKEFTHawking.RossSelinger
