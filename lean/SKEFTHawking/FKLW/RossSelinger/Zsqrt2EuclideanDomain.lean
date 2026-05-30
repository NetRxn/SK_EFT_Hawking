/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 — `EuclideanDomain (ℤ[√2])` (Prop 3.2.7 / Item-I two-squares sub-arc)

`ℤ[√2] = Zsqrtd 2` carries `CommRing` + `IsDomain` (`Zsqrt2.lean`) but Mathlib has no
`EuclideanDomain` instance for it (only `GaussianInt = Zsqrtd (-1)`). This file builds it,
following the `GaussianInt` template — but ℤ[√2]'s norm `N(a+b√2) = a² − 2b²` is
**indefinite** (can be negative), so the Euclidean measure is `(norm z).natAbs` and the
division-with-remainder bound rests on the absolute rounding bound
`zsqrt2_round_norm_lt : |(u−⌊u⌉)² − 2(v−⌊v⌉)²| < 1` (`Zsqrt2.lean`) rather than a single
positive-definite field embedding.

This `EuclideanDomain` ⟹ `ℤ[√2]` is a PID/UFD — the substrate for the two-squares-over-ℤ[√2]
representability (Ross thesis Prop 3.2.7, `RelativeNorm.normSq_real_sumSq` reduction), which
in turn supplies the residual-`t` existence Item I's unconditional `compile_correct` needs.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.Zsqrt2
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.EuclideanDomain.Defs

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

open Zsqrtd

/-- `ℤ[√2]`'s norm vanishes only at `0` (specialization of `Zsqrtd.norm_eq_zero` at the
non-square `d = 2`, via `two_ne_sq`). -/
theorem zsqrt2_norm_ne_zero {y : Zsqrtd 2} (hy : y ≠ 0) : Zsqrtd.norm y ≠ 0 :=
  fun h => hy ((Zsqrtd.norm_eq_zero two_ne_sq y).mp h)

/-- **Conjugation preserves the norm**: `N(ȳ) = N(y)` (since `N(a+b√2) = a²−2b²` is even in `b`). -/
theorem zsqrt2_norm_star (y : Zsqrtd 2) : Zsqrtd.norm (star y) = Zsqrtd.norm y := by
  obtain ⟨a, b⟩ := y
  simp [Zsqrtd.star_mk, Zsqrtd.norm_def]

/-- **Division** in `ℤ[√2]`: round the `ℚ(√2)` quotient `x·ȳ / N(y)` coordinate-wise. -/
noncomputable instance : Div (Zsqrtd 2) :=
  ⟨fun x y => ⟨round (((x * star y).re : ℚ) / (Zsqrtd.norm y : ℚ)),
               round (((x * star y).im : ℚ) / (Zsqrtd.norm y : ℚ))⟩⟩

theorem zsqrt2_div_def (x y : Zsqrtd 2) :
    x / y = (⟨round (((x * star y).re : ℚ) / (Zsqrtd.norm y : ℚ)),
             round (((x * star y).im : ℚ) / (Zsqrtd.norm y : ℚ))⟩ : Zsqrtd 2) := rfl

/-- **Remainder** in `ℤ[√2]`: `x % y = x − y·(x / y)`. -/
noncomputable instance : Mod (Zsqrtd 2) := ⟨fun x y => x - y * (x / y)⟩

theorem zsqrt2_mod_def (x y : Zsqrtd 2) : x % y = x - y * (x / y) := rfl

/-- **The key integer identity** behind the Euclidean descent:
`N(y)·N(x%y) = (A.re − N·q.re)² − 2·(A.im − N·q.im)²`, where `A = x·ȳ`, `N = N(y)`,
`q = x/y`. Derived from `ȳ·(x%y) = A − N·q` and `N(ȳ·r) = N(y)·N(r)`. -/
theorem zsqrt2_norm_mul_norm_mod (x y : Zsqrtd 2) :
    Zsqrtd.norm y * Zsqrtd.norm (x % y)
      = ((x * star y).re - Zsqrtd.norm y * (x / y).re) ^ 2
        - 2 * ((x * star y).im - Zsqrtd.norm y * (x / y).im) ^ 2 := by
  have hstar : star y * (x % y) = x * star y - (Zsqrtd.norm y : Zsqrtd 2) * (x / y) := by
    rw [zsqrt2_mod_def, mul_sub, mul_comm (star y) x, ← mul_assoc,
        mul_comm (star y) y, ← Zsqrtd.norm_eq_mul_conj]
  have hnorm : Zsqrtd.norm y * Zsqrtd.norm (x % y)
      = Zsqrtd.norm (x * star y - (Zsqrtd.norm y : Zsqrtd 2) * (x / y)) := by
    rw [← hstar, Zsqrtd.norm_mul, zsqrt2_norm_star]
  rw [hnorm, Zsqrtd.norm_def]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_mul, Zsqrtd.im_mul,
    Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  ring

/-- **Euclidean descent**: for `y ≠ 0`, `|N(x % y)| < |N(y)|` (as `ℕ` via `natAbs`).
The remainder's norm is `N(y)·((u−⌊u⌉)² − 2(v−⌊v⌉)²)` with `u,v` the `ℚ(√2)` quotient
coordinates, and the parenthesized factor is `< 1` in absolute value (`zsqrt2_round_norm_lt`). -/
theorem zsqrt2_natAbs_norm_mod_lt (x : Zsqrtd 2) {y : Zsqrtd 2} (hy : y ≠ 0) :
    (Zsqrtd.norm (x % y)).natAbs < (Zsqrtd.norm y).natAbs := by
  set N : ℤ := Zsqrtd.norm y with hN
  have hN0 : N ≠ 0 := zsqrt2_norm_ne_zero hy
  set u : ℚ := ((x * star y).re : ℚ) / (N : ℚ) with hu
  set v : ℚ := ((x * star y).im : ℚ) / (N : ℚ) with hv
  -- The division rounds u, v.
  have hqre : ((x / y).re : ℚ) = (round u : ℚ) := by rw [zsqrt2_div_def]
  have hqim : ((x / y).im : ℚ) = (round v : ℚ) := by rw [zsqrt2_div_def]
  -- Cast the key identity to ℚ and factor out N².
  have hkey : (N : ℚ) * (Zsqrtd.norm (x % y) : ℚ)
      = (N : ℚ) ^ 2 * ((u - round u) ^ 2 - 2 * (v - round v) ^ 2) := by
    have h := zsqrt2_norm_mul_norm_mod x y
    have hQ : ((Zsqrtd.norm y * Zsqrtd.norm (x % y) : ℤ) : ℚ)
        = (((x * star y).re - Zsqrtd.norm y * (x / y).re) ^ 2
          - 2 * ((x * star y).im - Zsqrtd.norm y * (x / y).im) ^ 2 : ℤ) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ℚ) h
    push_cast at hQ
    have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
    -- A.re = N*u, A.im = N*v  (since u = A.re/N, N ≠ 0).
    have hAre : ((x * star y).re : ℚ) = (N : ℚ) * u := by
      rw [hu]; field_simp
    have hAim : ((x * star y).im : ℚ) = (N : ℚ) * v := by
      rw [hv]; field_simp
    rw [hAre, hAim, hqre, hqim] at hQ
    rw [hQ]; ring
  -- Cancel N: norm(x%y) = N * (round-error norm), |error norm| < 1.
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  have hnormQ : (Zsqrtd.norm (x % y) : ℚ)
      = (N : ℚ) * ((u - round u) ^ 2 - 2 * (v - round v) ^ 2) := by
    apply mul_left_cancel₀ hNQ
    rw [hkey]; ring
  have hlt : |(u - round u) ^ 2 - 2 * (v - round v) ^ 2| < 1 := zsqrt2_round_norm_lt u v
  have hbound : |(Zsqrtd.norm (x % y) : ℚ)| < |(N : ℚ)| := by
    rw [hnormQ, abs_mul]
    calc |(N : ℚ)| * |(u - round u) ^ 2 - 2 * (v - round v) ^ 2|
        < |(N : ℚ)| * 1 := by
          apply mul_lt_mul_of_pos_left hlt
          rw [abs_pos]; exact hNQ
      _ = |(N : ℚ)| := mul_one _
  -- Convert |·| over ℚ to natAbs over ℤ.
  rw [← Int.cast_abs, ← Int.cast_abs] at hbound
  have : |Zsqrtd.norm (x % y)| < |N| := by exact_mod_cast hbound
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at this
  exact_mod_cast this

/-- **`mul_left_not_lt` ingredient**: `|N(x)| ≤ |N(x·y)|` for `y ≠ 0` (norm is multiplicative
and `|N(y)| ≥ 1`). -/
theorem zsqrt2_natAbs_norm_le_mul_left (x : Zsqrtd 2) {y : Zsqrtd 2} (hy : y ≠ 0) :
    (Zsqrtd.norm x).natAbs ≤ (Zsqrtd.norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have hy1 : 1 ≤ (Zsqrtd.norm y).natAbs :=
    Nat.one_le_iff_ne_zero.mpr (fun h => zsqrt2_norm_ne_zero hy (Int.natAbs_eq_zero.mp h))
  exact Nat.le_mul_of_pos_right _ hy1

instance : Nontrivial (Zsqrtd 2) := ⟨⟨0, 1, by decide⟩⟩

/-- **`ℤ[√2]` is a Euclidean domain.** Division/remainder by nearest-`ℚ(√2)`-rounding, with the
indefinite-norm Euclidean measure `(norm ·).natAbs` and the rounding-error descent
`zsqrt2_natAbs_norm_mod_lt`. The PID/UFD substrate for the two-squares-over-ℤ[√2] (Prop 3.2.7). -/
noncomputable instance : EuclideanDomain (Zsqrtd 2) :=
  { (inferInstance : CommRing (Zsqrtd 2)),
    (inferInstance : Nontrivial (Zsqrtd 2)) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by intro x; rw [zsqrt2_div_def]; simp [Zsqrtd.ext_iff]
    quotient_mul_add_remainder_eq := fun x y => by rw [zsqrt2_mod_def]; ring
    r := fun a b => (Zsqrtd.norm a).natAbs < (Zsqrtd.norm b).natAbs
    r_wellFounded := (measure fun a : Zsqrtd 2 => (Zsqrtd.norm a).natAbs).wf
    remainder_lt := fun a b hb => zsqrt2_natAbs_norm_mod_lt a hb
    mul_left_not_lt := fun a b hb =>
      not_lt.mpr (zsqrt2_natAbs_norm_le_mul_left a hb) }

end SKEFTHawking.RossSelinger
