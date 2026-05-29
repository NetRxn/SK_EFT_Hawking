/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — unit-column congruences (for `kmm_lemma3_column`)

`kmm_lemma3_column` needs the unit-column congruences `(|x|²+|y|²).d ≡ 0` and
`(|x|²+|y|²).c ≡ 0 (mod 8)` for the cleared column numerators `x, y : ℤ[ω]` of a
unitary matrix. This file supplies them.

For a unitary column `(z, w)` over `ZOmegaSqrt2` (`|z|² + |w|² = 1`,
`unitary_col0_normSq`) cleared at a common exponent `s` (`x = √2^s·z`,
`y = √2^s·w` both `ℤ[ω]`-valued), the cleared squared moduli sum to a pure
power of two:

  `|x|² + |y|² = √2^(2s) = 2^s`   (`clearedCol_normSq_sum`)

— a real `ℤ[ω]` element with rational coordinate `2^s` and `√2`-coordinate `0`
(`ZOmega.sqrt2_pow_two_mul_coords`). For `s ≥ 3`, `8 ∣ 2^s`, so both coordinates
vanish `mod 8` (`unit_col_congruences`) — exactly the `Pform`-sum and `Qform`-sum
hypotheses of `kmm_lemma3_column`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected (kernel-pure; the `(2:ZMod 8)^3
  = 0` step is a `decide`).

-/

import SKEFTHawking.FKLW.RossSelinger.ClearingConnection
import SKEFTHawking.FKLW.RossSelinger.UnitaryT
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **Coordinates of `√2^(2s)` in `ℤ[ω]`**: `√2^(2s) = 2^s` is a pure rational
integer, with `√2`-coordinate `0` and rational coordinate `2^s`. Induction on `s`
via `√2² = 2` (so `√2^(2(n+1)) = √2^(2n) + √2^(2n)`). -/
theorem sqrt2_pow_two_mul_coords (s : ℕ) :
    (sqrt2 ^ (2 * s)).c = 0 ∧ (sqrt2 ^ (2 * s)).d = 2 ^ s := by
  induction s with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨ihc, ihd⟩ := ih
    have hstep : sqrt2 ^ (2 * (n + 1)) = sqrt2 ^ (2 * n) + sqrt2 ^ (2 * n) := by
      rw [show 2 * (n + 1) = 2 * n + 2 from by ring, pow_add]
      have h2 : sqrt2 ^ 2 = (2 : ZOmega) := by decide
      rw [h2]; ring
    rw [hstep, add_c, add_d, ihc, ihd]
    exact ⟨by omega, by rw [pow_succ]; omega⟩

end ZOmega

namespace ZOmegaSqrt2

/-- **Cleared column squared moduli sum to `√2^(2s)`**: for a unit column
`|z|² + |w|² = 1` cleared at a common exponent `s` (`√2^s·z = of x`, `√2^s·w =
of y`), `|x|² + |y|² = √2^(2s)` in `ℤ[ω]`. Clear the unit identity by `√2^(2s)`
(`sqrt2_pow_normSq_clearing` on each entry, `of` injective). -/
theorem clearedCol_normSq_sum {z w : ZOmegaSqrt2} {s : ℕ} {x y : ZOmega}
    (hz : (sqrt2 : ZOmegaSqrt2) ^ s * z = of x) (hw : (sqrt2 : ZOmegaSqrt2) ^ s * w = of y)
    (h1 : normSq z + normSq w = 1) :
    ZOmega.normSq x + ZOmega.normSq y = ZOmega.sqrt2 ^ (2 * s) := by
  have hcomb : (sqrt2 : ZOmegaSqrt2) ^ (2 * s) * normSq z
        + (sqrt2 : ZOmegaSqrt2) ^ (2 * s) * normSq w
      = (sqrt2 : ZOmegaSqrt2) ^ (2 * s) * (normSq z + normSq w) := by ring
  have key : of (ZOmega.normSq x) + of (ZOmega.normSq y) = of (ZOmega.sqrt2 ^ (2 * s)) := by
    rw [← sqrt2_pow_normSq_clearing hz, ← sqrt2_pow_normSq_clearing hw, hcomb, h1, mul_one,
      sqrt2_pow_eq, of_def]
  rw [← of_add] at key
  rw [of_def, of_def, mk_eq_mk_iff] at key
  simpa using key

/-- **Unit-column congruences (for `kmm_lemma3_column`)**: for a unit column cleared
at a common exponent `s ≥ 2`, the cleared squared-modulus sum satisfies

  `2·(|x|² + |y|²).d ≡ 0`  (i.e. `(|x|² + |y|²).d ∈ {0,4}`)  and  `(|x|² + |y|²).c ≡ 0  (mod 8)`.

`|x|²+|y|² = √2^(2s)` has `.d = 2^s` (`≡ 0` for `s ≥ 3`, `≡ 4` for `s = 2`) and
`.c = 0`; in both cases `2·2^s = 2^(s+1) ≡ 0` for `s ≥ 2`. The `≡ 4` case is exactly
the `m = 2` / `sde(|z|²) = 4` boundary the reduction passes through. These are
exactly the `Pform`-sum/`Qform`-sum hypotheses of `kmm_lemma3_column`. -/
theorem unit_col_congruences {z w : ZOmegaSqrt2} {s : ℕ} {x y : ZOmega}
    (hz : (sqrt2 : ZOmegaSqrt2) ^ s * z = of x) (hw : (sqrt2 : ZOmegaSqrt2) ^ s * w = of y)
    (h1 : normSq z + normSq w = 1) (hs : 2 ≤ s) :
    2 * ((ZOmega.normSq x + ZOmega.normSq y).d : ZMod 8) = 0 ∧
      ((ZOmega.normSq x + ZOmega.normSq y).c : ZMod 8) = 0 := by
  have hsum := clearedCol_normSq_sum hz hw h1
  obtain ⟨hc, hd⟩ := ZOmega.sqrt2_pow_two_mul_coords s
  rw [hsum]
  refine ⟨?_, ?_⟩
  · rw [hd]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
    push_cast
    have h0 : (2 : ZMod 8) * 2 ^ 2 = 0 := by decide
    rw [pow_add, ← mul_assoc, h0, zero_mul]
  · rw [hc]; simp

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
