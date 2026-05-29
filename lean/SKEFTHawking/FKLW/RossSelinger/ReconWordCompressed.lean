/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — S/Z-compressed KMM reconstruction syllable

KMM Algorithm 1 (arXiv:1206.5236) reduces `sde(|z₀₀|²)` by `1` per step,
left-multiplying by `H·Tᵏ` with `k ∈ {0,1,2,3}`; the synthesized circuit emits
the inverse syllable `Tᵏ⁻¹·H = T^(8−k)·H`, which the length bound
`n_g ≤ N₃ + 4·sde` counts as **≤ 4 gates** per step.

`KMMReduce.reconWord k := replicate (8−k) .T ++ [.H]` spells `T^(8−k)` as up to
**8 raw `T` gates** (for `k ≤ 3`, `8−k ∈ {5,6,7,8}`), so its length is `6..9` —
which only yields the weaker bound `N₃ + 9·sde`. This file ships the
**gate-count-optimal** reconstruction syllable, spelling `T^(8−k)` with the
Clifford gates `S = T²` and `Z = T⁴`:

  * `k = 0` :  `T⁸ = I`        ↦ `[H]`          (length 1)
  * `k = 1` :  `T⁷ = Z·S·T`    ↦ `[Z, S, T, H]` (length 4)
  * `k = 2` :  `T⁶ = Z·S`      ↦ `[Z, S, H]`    (length 3)
  * `k = 3` :  `T⁵ = Z·T`      ↦ `[Z, T, H]`    (length 3)

Every syllable has **length ≤ 4** (`reconWordC_length_le_four`), and interprets
to the *same* operator `T^(8−k)·H` as `KMMReduce.reconWord k`
(`interp_reconWordC_eq`), so the reduction-step correctness identity
`interp_reconWordC_mul` follows directly from `KMMReduce.interp_reconWord_mul`.
This is the syllable the `KMMReduction.length_bound` (`N₃ + 4·k`) assembly uses.

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) Algorithm 1 + Corollary 1.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.KMMReduce

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate

/-! ## 1. `S = T²` and `Z = T⁴` as gate matrices -/

/-- **`S = T²`** (gate-matrix form). -/
theorem gateMatrix_S_eq : gateMatrix .S = gateMatrix .T ^ 2 := by
  rw [pow_two]; exact T_mul_T_eq_S.symm

/-- **`Z = T⁴`** (gate-matrix form): `T⁴ = (T²)² = S² = Z`. The `*` here is the
heterogeneous `Matrix` HMul, so the `Monoid` power lemmas are used as defeq
*terms* (the `reconWord_inv` idiom), not via `rw`. -/
theorem gateMatrix_Z_eq : gateMatrix .Z = gateMatrix .T ^ 4 :=
  calc gateMatrix .Z
      = gateMatrix .S * gateMatrix .S := S_mul_S_eq_Z.symm
    _ = gateMatrix .T ^ 2 * gateMatrix .T ^ 2 := by rw [gateMatrix_S_eq]
    _ = gateMatrix .T ^ (2 + 2) := (pow_add (gateMatrix .T) 2 2).symm
    _ = gateMatrix .T ^ 4 := by norm_num

/-! ## 2. The compressed `T`-power runs `Z·S·T`, `Z·S`, `Z·T` -/

/-- **`Z·S = T⁶`**. -/
theorem interp_ZS : interp [.Z, .S] = gateMatrix .T ^ 6 := by
  have e : interp [.Z, .S] = gateMatrix .Z * gateMatrix .S := by
    rw [interp_cons, interp_singleton]
  rw [e, gateMatrix_Z_eq, gateMatrix_S_eq]
  exact (pow_add (gateMatrix .T) 4 2).symm

/-- **`Z·T = T⁵`**. -/
theorem interp_ZT : interp [.Z, .T] = gateMatrix .T ^ 5 := by
  have e : interp [.Z, .T] = gateMatrix .Z * gateMatrix .T := by
    rw [interp_cons, interp_singleton]
  rw [e, gateMatrix_Z_eq]
  exact (pow_succ (gateMatrix .T) 4).symm

/-- **`Z·S·T = T⁷`** (routed through `interp_ZS` to avoid 3-factor associativity
on the heterogeneous `Matrix` HMul). -/
theorem interp_ZST : interp [.Z, .S, .T] = gateMatrix .T ^ 7 := by
  have e : interp [.Z, .S, .T] = interp [.Z, .S] * gateMatrix .T := by
    rw [show ([.Z, .S, .T] : List CliffordTGate) = [.Z, .S] ++ [.T] from rfl,
        interp_append, interp_singleton]
  rw [e, interp_ZS]
  exact (pow_succ (gateMatrix .T) 6).symm

/-! ## 3. The compressed reconstruction word -/

/-- **S/Z-compressed reconstruction syllable** for the KMM peel of `H·Tᵏ`,
`k ≤ 3`: `T^(8−k)·H` spelled with the Clifford gates `S = T²`, `Z = T⁴` so the
syllable is `≤ 4` gates. (Falls back to `KMMReduce.reconWord` for `k ≥ 4`, which
the KMM recursion never hits since `k ∈ {0,1,2,3}`.) -/
def reconWordC : ℕ → List CliffordTGate
  | 0 => [.H]
  | 1 => [.Z, .S, .T, .H]
  | 2 => [.Z, .S, .H]
  | 3 => [.Z, .T, .H]
  | j + 4 => reconWord (j + 4)

/-- **The compressed syllable interprets to `T^(8−k)·H`** (for `k ≤ 3`), the same
operator as `KMMReduce.reconWord k`. -/
theorem interp_reconWordC (k : ℕ) (hk : k ≤ 3) :
    interp (reconWordC k) = gateMatrix .T ^ (8 - k) * gateMatrix .H := by
  rcases k with _ | _ | _ | _ | k
  · show interp [.H] = gateMatrix .T ^ 8 * gateMatrix .H
    rw [interp_singleton, gateMatrix_T_pow_eight]
    exact (one_mul _).symm
  · show interp [.Z, .S, .T, .H] = gateMatrix .T ^ 7 * gateMatrix .H
    rw [show ([.Z, .S, .T, .H] : List CliffordTGate) = [.Z, .S, .T] ++ [.H] from rfl,
        interp_append, interp_ZST, interp_singleton]
  · show interp [.Z, .S, .H] = gateMatrix .T ^ 6 * gateMatrix .H
    rw [show ([.Z, .S, .H] : List CliffordTGate) = [.Z, .S] ++ [.H] from rfl,
        interp_append, interp_ZS, interp_singleton]
  · show interp [.Z, .T, .H] = gateMatrix .T ^ 5 * gateMatrix .H
    rw [show ([.Z, .T, .H] : List CliffordTGate) = [.Z, .T] ++ [.H] from rfl,
        interp_append, interp_ZT, interp_singleton]
  · exact absurd hk (by omega)

/-- **The compressed syllable equals the raw `reconWord`** on interpretation
(`k ≤ 3`): both are `T^(8−k)·H`. -/
theorem interp_reconWordC_eq (k : ℕ) (hk : k ≤ 3) :
    interp (reconWordC k) = interp (reconWord k) := by
  rw [interp_reconWordC k hk, interp_reconWord]

/-- **Reduction-step correctness with the compressed syllable**: for `k ≤ 3`,
`interp (reconWordC k) · (H · Tᵏ · M) = M`. Inherits `interp_reconWord_mul`. -/
theorem interp_reconWordC_mul (k : ℕ) (hk : k ≤ 3) (M : Mat2) :
    interp (reconWordC k) * (gateMatrix .H * gateMatrix .T ^ k * M) = M := by
  rw [interp_reconWordC_eq k hk]
  exact interp_reconWord_mul k (by omega) M

/-- **The compressed syllable has length `≤ 4`** (`k ≤ 3`). This is the per-step
gate budget behind the `N₃ + 4·k` length bound. -/
theorem reconWordC_length_le_four (k : ℕ) (hk : k ≤ 3) :
    (reconWordC k).length ≤ 4 := by
  rcases k with _ | _ | _ | _ | k
  · decide
  · decide
  · decide
  · decide
  · exact absurd hk (by omega)

end KMM

end SKEFTHawking.RossSelinger
