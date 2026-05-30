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

end SKEFTHawking.RossSelinger
