/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 11) — the dim-4 column-lemma base case (number-theoretic heart)

The dim-4 exact synthesis (column lemma) inducts on the denominator exponent down to `0`. At
denominator exponent `0` the column has entries in `ℤ[ω]` and is a unit vector; this file proves its
structure: **exactly one entry is a unit (`ωᵏ`), the rest are `0`** — so the column is `ωᵏ·eᵢ`, which
is realizable by the basis-state permutation (`isColRealizableWithin_basis`, inc 10b) plus a global
`ω`-phase.

Crucially this needs **no** total-positivity / Galois-conjugate / Kronecker argument: since `normSq`
lands in `ℤ[ω]` with rational coordinate `(|z|²).d = a²+b²+c²+d²` (`normSq_coords`), the unit-column
identity `Σ |zᵢ|² = 1` reduces to the elementary **sum-of-four-squares** facts `Σ Pᵢ = 1` with each
`Pᵢ = aᵢ²+bᵢ²+cᵢ²+dᵢ² ≥ 0` — one `Pᵢ = 1`, the rest `0`.

## Headlines

  * `ZOmega.normSq_eq_one_iff_omega_pow` — `|z|² = 1 ↔ z = ωᵏ` for some `k < 8` (the units of `ℤ[ω]`
    of modulus 1 are exactly the 8th roots of unity; `⟸` is `normSq_omega_pow`, `⟹` is sum-of-four-
    squares = 1).
  * `ZOmega.normSq_eq_zero_iff` — `|z|² = 0 ↔ z = 0`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` (the per-case `z = ωᵏ` checks are kernel `decide` on bounded integer coordinates).
  Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.RelativeNorm
import SKEFTHawking.FKLW.RossSelinger.NormSqGde
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **`|z|² = 0 ↔ z = 0`** in `ℤ[ω]`: the rational coordinate `(|z|²).d = a²+b²+c²+d²` is `0` iff all
coordinates vanish. -/
theorem normSq_eq_zero_iff {z : ZOmega} : normSq z = 0 ↔ z = 0 := by
  obtain ⟨a, b, c, d⟩ := z
  constructor
  · intro h
    rw [normSq_coords] at h
    have hP : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 0 := by
      have := congrArg ZOmega.d h; simpa using this
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hd : d = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    rw [ha, hb, hc, hd]; rfl
  · intro h; rw [h, normSq_zero]

/-- **`|z|² = 1 ↔ z = ωᵏ`** (`k < 8`): the modulus-1 elements of `ℤ[ω]` are exactly the 8th roots of
unity. `⟸` is `normSq_omega_pow`; `⟹` reduces (`normSq_coords`) to `a²+b²+c²+d² = 1`, whose only
integer solutions are the signed basis vectors `±eᵢ = ω^{0..7}`. -/
theorem normSq_eq_one_iff_omega_pow {z : ZOmega} : normSq z = 1 ↔ ∃ k, k < 8 ∧ z = ω ^ k := by
  constructor
  · intro h
    obtain ⟨a, b, c, d⟩ := z
    rw [normSq_coords] at h
    have hP : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := by
      have := congrArg ZOmega.d h; simpa using this
    have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
    have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
    have hd2 : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have ha : -1 ≤ a ∧ a ≤ 1 := ⟨by nlinarith [sq_nonneg (a + 1)], by nlinarith [sq_nonneg (a - 1)]⟩
    have hb : -1 ≤ b ∧ b ≤ 1 := ⟨by nlinarith [sq_nonneg (b + 1)], by nlinarith [sq_nonneg (b - 1)]⟩
    have hc : -1 ≤ c ∧ c ≤ 1 := ⟨by nlinarith [sq_nonneg (c + 1)], by nlinarith [sq_nonneg (c - 1)]⟩
    have hd : -1 ≤ d ∧ d ≤ 1 := ⟨by nlinarith [sq_nonneg (d + 1)], by nlinarith [sq_nonneg (d - 1)]⟩
    obtain ⟨ha1, ha2'⟩ := ha; obtain ⟨hb1, hb2'⟩ := hb
    obtain ⟨hc1, hc2'⟩ := hc; obtain ⟨hd1, hd2'⟩ := hd
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
      first | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ | exact ⟨2, by decide, by decide⟩ | exact ⟨3, by decide, by decide⟩ | exact ⟨4, by decide, by decide⟩ | exact ⟨5, by decide, by decide⟩ | exact ⟨6, by decide, by decide⟩ | exact ⟨7, by decide, by decide⟩ | exact absurd hP (by decide)
  · rintro ⟨k, _, rfl⟩; exact normSq_omega_pow k

end ZOmega

end SKEFTHawking.RossSelinger
