/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 1(b) — `ℤ[√2][i] = GaussInt2` is an integral domain

The next brick toward the two-squares-over-`ℤ[√2]` descent (Ross thesis Prop 3.2.7) / the even-power
relative-norm criterion: `GaussInt2 = ℤ[√2][i]` is an **integral domain**, via its positive-definite
relative norm `N(re + im·i) = re² + im²`.

The key fact is `norm_eq_zero` (`re² + im² = 0 ⟺ re = im = 0` over `ℤ[√2]`). Crucially this needs **no
real embedding of `ℤ[√2]`** (Mathlib has none for `Zsqrtd 2`): at the integer-coordinate level,
`re² + im² = 0` unfolds to `a₁² + 2a₂² + b₁² + 2b₂² = 0` over ℤ — a sum of four non-negative integers,
forcing each coordinate to vanish (`nlinarith`). `NoZeroDivisors`/`IsDomain` then follow from
multiplicativity of the norm into the domain `ℤ[√2]` (`norm_mul`).

## Headlines

  * `zsqrt2_sq_add_sq_eq_zero` — `a² + b² = 0 ⟺ a = 0 ∧ b = 0` for `a b : ℤ[√2]` (formal reality of
    `ℤ[√2]` at the coordinate level).
  * `GaussInt2.norm_eq_zero` — `x.norm = 0 ⟺ x = 0`.
  * `GaussInt2.instIsDomain` — `ℤ[√2][i]` is an integral domain.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.Zsqrt2GaussianInt

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-- **`ℤ[√2]` is formally real at the coordinate level**: `a² + b² = 0 ⟺ a = 0 ∧ b = 0` for
`a, b : ℤ[√2]`. Expanding to integer coordinates, `a² + b² = 0` has real part
`a.re² + 2·a.im² + b.re² + 2·b.im² = 0` — a sum of four non-negative integers — so every coordinate
vanishes. (No real embedding of `ℤ[√2]` is needed.) -/
theorem zsqrt2_sq_add_sq_eq_zero {a b : Zsqrtd 2} : a ^ 2 + b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h' := congrArg Zsqrtd.re h
    simp only [pow_two, Zsqrtd.re_add, Zsqrtd.re_mul, show Zsqrtd.re (0 : Zsqrtd 2) = 0 from rfl] at h'
    have hn1 := mul_self_nonneg a.re
    have hn2 := mul_self_nonneg a.im
    have hn3 := mul_self_nonneg b.re
    have hn4 := mul_self_nonneg b.im
    refine ⟨Zsqrtd.ext ?_ ?_, Zsqrtd.ext ?_ ?_⟩
    · exact mul_self_eq_zero.mp (by nlinarith)
    · exact mul_self_eq_zero.mp (by nlinarith)
    · exact mul_self_eq_zero.mp (by nlinarith)
    · exact mul_self_eq_zero.mp (by nlinarith)
  · rintro ⟨ha, hb⟩
    rw [ha, hb]; ring

namespace GaussInt2

/-- **The relative norm vanishes only at `0`**: `x.norm = 0 ⟺ x = 0`. -/
@[simp] theorem norm_eq_zero {x : GaussInt2} : x.norm = 0 ↔ x = 0 := by
  rw [norm_def, zsqrt2_sq_add_sq_eq_zero]
  constructor
  · rintro ⟨hre, him⟩; exact GaussInt2.ext hre him
  · intro h; rw [h]; exact ⟨rfl, rfl⟩

instance : Nontrivial GaussInt2 :=
  ⟨0, 1, by intro h; simpa using congrArg GaussInt2.re h⟩

instance : NoZeroDivisors GaussInt2 where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    have hn : x.norm * y.norm = 0 := by rw [← norm_mul, h]; simp [norm_def]
    rcases mul_eq_zero.mp hn with h1 | h1
    · exact Or.inl (norm_eq_zero.mp h1)
    · exact Or.inr (norm_eq_zero.mp h1)

/-- **`ℤ[√2][i]` is an integral domain.** -/
instance instIsDomain : IsDomain GaussInt2 := NoZeroDivisors.to_isDomain _

end GaussInt2

end SKEFTHawking.RossSelinger
