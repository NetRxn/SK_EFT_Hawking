/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — `denExp` is non-archimedean; KMM Lemma 4

The `√2`-denominator exponent `denExp` is (the negative of) a valuation,
hence **non-archimedean**: `denExp (a+b) ≤ max (denExp a) (denExp b)`, with
equality when the two exponents differ. This file proves those properties
from the clearing characterization `denExp_le_iff`, then derives the core
of **KMM Lemma 4**: for a unitary `M`, the two entries of a column have
equal `sde(|·|²)` (`denExp (normSq (M 0 0)) = denExp (normSq (M 1 0))`),
because `|z|² + |w|² = 1` has `denExp 0` and unequal exponents would force
the sum's exponent to be the (positive) max.

## Headline results

  * `ZOmegaSqrt2.denExp_neg` — `denExp (-x) = denExp x`.
  * `ZOmegaSqrt2.denExp_add_le` — `denExp (a+b) ≤ max (denExp a) (denExp b)`.
  * `ZOmegaSqrt2.denExp_add_eq_max_of_ne` — equality when exponents differ.
  * `ZOmegaSqrt2.denExp_normSq_col0_eq` — **KMM Lemma 4 core** (unitary ⟹
    equal column `sde(|·|²)`).

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §3, Lemma 4.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.UnitaryT
import SKEFTHawking.FKLW.RossSelinger.Sde

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmegaSqrt2

/-- **`denExp` is negation-invariant**: `denExp (-x) = denExp x`. -/
theorem denExp_neg (x : ZOmegaSqrt2) : denExp (-x) = denExp x := by
  apply le_antisymm
  · rw [denExp_le_iff]
    obtain ⟨w, hw⟩ := denExp_le_iff.mp (le_refl (denExp x))
    refine ⟨-w, ?_⟩
    have hmn : (sqrt2 : ZOmegaSqrt2) ^ denExp x * -x
             = -((sqrt2 : ZOmegaSqrt2) ^ denExp x * x) := by ring
    rw [hmn, hw, ← of_neg]
  · rw [denExp_le_iff]
    obtain ⟨w, hw⟩ := denExp_le_iff.mp (le_refl (denExp (-x)))
    refine ⟨-w, ?_⟩
    have hmn : (sqrt2 : ZOmegaSqrt2) ^ denExp (-x) * x
             = -((sqrt2 : ZOmegaSqrt2) ^ denExp (-x) * -x) := by ring
    rw [hmn, hw, ← of_neg]

/-- **`denExp` is non-archimedean (sub-additive)**:
`denExp (a + b) ≤ max (denExp a) (denExp b)`. -/
theorem denExp_add_le (a b : ZOmegaSqrt2) :
    denExp (a + b) ≤ max (denExp a) (denExp b) := by
  rw [denExp_le_iff]
  obtain ⟨wa, hwa⟩ := denExp_le_iff.mp (le_max_left (denExp a) (denExp b))
  obtain ⟨wb, hwb⟩ := denExp_le_iff.mp (le_max_right (denExp a) (denExp b))
  refine ⟨wa + wb, ?_⟩
  have hd : (sqrt2 : ZOmegaSqrt2) ^ max (denExp a) (denExp b) * (a + b)
          = (sqrt2 : ZOmegaSqrt2) ^ max (denExp a) (denExp b) * a
            + (sqrt2 : ZOmegaSqrt2) ^ max (denExp a) (denExp b) * b := by ring
  rw [hd, hwa, hwb, ← of_add]

/-- **Strong (equality) form when the exponents differ**:
`denExp a ≠ denExp b ⟹ denExp (a + b) = max (denExp a) (denExp b)`. -/
theorem denExp_add_eq_max_of_ne {a b : ZOmegaSqrt2} (h : denExp a ≠ denExp b) :
    denExp (a + b) = max (denExp a) (denExp b) := by
  refine le_antisymm (denExp_add_le a b) ?_
  -- a = (a + b) + (-b), so denExp a ≤ max (denExp (a+b)) (denExp b)
  have ha : denExp a ≤ max (denExp (a + b)) (denExp b) := by
    have := denExp_add_le (a + b) (-b)
    rw [denExp_neg] at this
    have he : a + b + -b = a := by ring
    rwa [he] at this
  -- b = (a + b) + (-a), so denExp b ≤ max (denExp (a+b)) (denExp a)
  have hb : denExp b ≤ max (denExp (a + b)) (denExp a) := by
    have := denExp_add_le (a + b) (-a)
    rw [denExp_neg] at this
    have he : a + b + -a = b := by ring
    rwa [he] at this
  omega

/-- **`denExp` is sub-multiplicative**: `denExp (x·y) ≤ denExp x + denExp y`
(the valuation property `v(xy) = v(x)+v(y)` as an inequality on the
denominator exponent). The `/2 = ·invSqrt2²` step in KMM Lemma 3 uses this. -/
theorem denExp_mul_le (x y : ZOmegaSqrt2) :
    denExp (x * y) ≤ denExp x + denExp y := by
  rw [denExp_le_iff]
  obtain ⟨wx, hwx⟩ := denExp_le_iff.mp (le_refl (denExp x))
  obtain ⟨wy, hwy⟩ := denExp_le_iff.mp (le_refl (denExp y))
  refine ⟨wx * wy, ?_⟩
  have hd : (sqrt2 : ZOmegaSqrt2) ^ (denExp x + denExp y) * (x * y)
          = ((sqrt2 : ZOmegaSqrt2) ^ denExp x * x) * ((sqrt2 : ZOmegaSqrt2) ^ denExp y * y) := by
    rw [pow_add]; ring
  rw [hd, hwx, hwy, ← of_mul]

/-- **`denExp invSqrt2 = 1`** (`1/√2` has denominator exponent one). -/
@[simp] theorem denExp_invSqrt2 : denExp invSqrt2 = 1 := by
  rw [invSqrt2_def, denExp_mk]; decide

/-- **KMM Lemma 4 (core)**: for a unitary `M`, the two column-0 entries
have equal squared-modulus `sde`: `denExp (|M₀₀|²) = denExp (|M₁₀|²)`.

`|M₀₀|² + |M₁₀|² = 1` (`unitary_col0_normSq`) has `denExp 0`; if the two
exponents differed, the non-archimedean equality would force the sum's
exponent to be their (positive) maximum — contradiction. -/
theorem denExp_normSq_col0_eq {M : Mat2} (h : IsUnitaryT M) :
    denExp (normSq (M 0 0)) = denExp (normSq (M 1 0)) := by
  by_contra hne
  have hsum : normSq (M 0 0) + normSq (M 1 0) = 1 := unitary_col0_normSq h
  have hmax := denExp_add_eq_max_of_ne hne
  rw [hsum, denExp_one] at hmax
  omega

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
