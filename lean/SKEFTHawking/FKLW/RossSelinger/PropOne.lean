/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — KMM Proposition 1 (gde of a real element)

The gde-value bridge for the KMM Lemma 3 ↔ `ZOmega` connection needs to compute
`gde(|x|², √2)` from the integer coordinates of the (real) squared modulus. KMM
Proposition 1 (arXiv:1206.5236 p. 12) does this via the `2`-adic valuations of
the two `ℤ[√2]`-coordinates. The first step — reproduced here — is that the
`√2`-peel of a *real* element `z = A + √2·B` (`A = z.d`, `B = z.c`) is the
Euclidean swap `(A, B) ↦ (B, A/2)`, so the fuel-bounded gde `gdePeel` of a real
element equals a pure-`ℤ` recursion `peelN A B` on its coordinates.

  * `peelN A B fuel` — peel `√2` while the constant coordinate is even, swapping
    `(A, B) ↦ (B, A/2)`. The integer shadow of `gdePeel` on the real subring.
  * `gdePeel_real_eq_peelN` — `conj z = z ⟹ gdePeel z fuel = peelN z.d z.c fuel`.

The closed form `peelN A B = 2·min(v₂A, v₂B) + [v₂A > v₂B]` (Prop 1 proper) and
its mod-`8` reduction to `Coord4.gde` build on this.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.GdeValue
import SKEFTHawking.FKLW.RossSelinger.RealSubring

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **Integer shadow of the `√2`-peel on the real subring**: peel `√2` while the
constant coordinate `A` is even, performing the Euclidean swap `(A, B) ↦ (B, A/2)`. -/
def peelN (A B : ℤ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => if 2 ∣ A then peelN B (A / 2) fuel + 1 else 0

@[simp] theorem peelN_zero (A B : ℤ) : peelN A B 0 = 0 := rfl

/-- **`gdePeel` of a real element is `peelN` of its `ℤ[√2]`-coordinates**:
for `conj z = z`, `gdePeel z fuel = peelN z.d z.c fuel`. Each `√2`-peel of a real
element is the swap `(z.d, z.c) ↦ (z.c, z.d/2)` (`divSqrt2_of_isReal`), and the
peel stays in the real subring (`isReal_divSqrt2`). -/
theorem gdePeel_real_eq_peelN {z : ZOmega} (h : conj z = z) (fuel : ℕ) :
    gdePeel z fuel = peelN z.d z.c fuel := by
  induction fuel generalizing z with
  | zero => simp
  | succ n ih =>
    rw [gdePeel_succ, peelN]
    by_cases hd : dividesSqrt2 z
    · have h2 : 2 ∣ z.d := (dividesSqrt2_of_isReal h).mp hd
      have hreal' : conj (divSqrt2 z) = divSqrt2 z := isReal_divSqrt2 h h2
      have hd' : (divSqrt2 z).d = z.c := by rw [divSqrt2_of_isReal h h2]
      have hc' : (divSqrt2 z).c = z.d / 2 := by rw [divSqrt2_of_isReal h h2]
      rw [if_pos hd, if_pos h2, ih hreal', hd', hc']
    · have h2 : ¬ (2 : ℤ) ∣ z.d := fun hh => hd ((dividesSqrt2_of_isReal h).mpr hh)
      rw [if_neg hd, if_neg h2]

end ZOmega

end SKEFTHawking.RossSelinger
