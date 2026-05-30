/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item G — ℤ[√2] = `Zsqrtd 2` ring structure (Prop 3.2.7 / two-squares sub-arc)

`RelativeNorm.normSq_real_sumSq` reduces the §6 relative-norm equation `t†t = β` (Prop 3.2.7) to
**writing `β` as a sum of two squares in `ℤ[√2]`**. This file builds the `ℤ[√2]` ring structure
(via Mathlib's `Zsqrtd 2`) needed for that two-squares theorem, following the `GaussianInt`
(`ℤ[i]`) template: `IsDomain` (this file) → `EuclideanDomain` (next, via norm-rounding division)
→ the Gaussian-integers-over-`ℤ[√2]` two-squares argument.

Mathlib's `Zsqrtd 2` carries `CommRing` but not `IsDomain`/`EuclideanDomain`. `IsDomain` follows
from the injective embedding `Zsqrtd.toReal : ℤ√2 →+* ℝ` (`a + b√2 ↦ a + b·√2`, injective since
`2` is not a perfect square) pulling back the domain structure of `ℝ`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new axioms): respected.

-/

import Mathlib.NumberTheory.Zsqrtd.ToReal
import Mathlib.Algebra.Order.Round

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-- `2` is not a perfect square in `ℤ` (the hypothesis of `Zsqrtd.toReal_injective` for `d = 2`):
`|n| ≤ 1 ⟹ n² ≤ 1 < 2`, and `|n| ≥ 2 ⟹ n² ≥ 4 > 2`. -/
theorem two_ne_sq (n : ℤ) : (2 : ℤ) ≠ n * n := by
  intro h
  have hself : (n.natAbs : ℤ) * (n.natAbs : ℤ) = n * n := Int.natAbs_mul_self' n
  have hnn : (0 : ℤ) ≤ (n.natAbs : ℤ) := Nat.cast_nonneg _
  rcases (by omega : n.natAbs ≤ 1 ∨ 2 ≤ n.natAbs) with hb | hb
  · have h1 : (n.natAbs : ℤ) ≤ 1 := by exact_mod_cast hb
    nlinarith [hself, hnn, h1]
  · have h2 : (2 : ℤ) ≤ (n.natAbs : ℤ) := by exact_mod_cast hb
    nlinarith [hself, h2]

/-- **`ℤ[√2]` is an integral domain.** Pulled back along the injective ring homomorphism
`Zsqrtd.toReal : ℤ√2 →+* ℝ` (injective by `two_ne_sq`) from the domain `ℝ`. The first ring-theoretic
brick of the two-squares-over-`ℤ[√2]` sub-arc (toward Prop 3.2.7 / Item G). -/
noncomputable instance : IsDomain (Zsqrtd 2) :=
  (Zsqrtd.toReal_injective (by norm_num) two_ne_sq).isDomain _

/-- **The norm-Euclidean rounding bound for `ℤ[√2]`** — the crux of `EuclideanDomain (ℤ[√2])`.
`ℤ[√2]`'s norm `N(a+b√2) = a² − 2b²` is *indefinite*, so the division-with-remainder argument
hinges on this absolute bound on the norm of a nearest-integer rounding error: for any rational
`u, v`, the error `(u − ⌊u⌉) + (v − ⌊v⌉)√2` has `|N| = |(u−⌊u⌉)² − 2(v−⌊v⌉)²| < 1`. (Each
coordinate error is `≤ 1/2`, so `(u−⌊u⌉)² ≤ 1/4` and `2(v−⌊v⌉)² ≤ 1/2`, giving the value in
`[−1/2, 1/4] ⊂ (−1,1)`.) Quotient `q := ⌊a/b⌉` over `ℚ(√2)` then yields `|N(a − bq)| =
|N(b)|·|N(error)| < |N(b)|`, the Euclidean descent. -/
theorem zsqrt2_round_norm_lt (u v : ℚ) :
    |(u - round u) ^ 2 - 2 * (v - round v) ^ 2| < 1 := by
  have he : |u - (round u : ℚ)| ≤ 1 / 2 := abs_sub_round u
  have hf : |v - (round v : ℚ)| ≤ 1 / 2 := abs_sub_round v
  have he2 : (u - round u) ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_abs (u - (round u : ℚ)), he, abs_nonneg (u - (round u : ℚ))]
  have hf2 : (v - round v) ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_abs (v - (round v : ℚ)), hf, abs_nonneg (v - (round v : ℚ))]
  rw [abs_lt]
  constructor <;> nlinarith [sq_nonneg (u - (round u : ℚ)), sq_nonneg (v - (round v : ℚ)), he2, hf2]

end SKEFTHawking.RossSelinger
