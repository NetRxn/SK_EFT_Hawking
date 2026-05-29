/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — the real subring ℤ[√2] ⊂ ℤ[ω] (KMM Prop 1 substrate)

KMM tracks `sde(|z|²)` of matrix entries, and `|z|²` is a **real** element
of `ℤ[ω]` (fixed by complex conjugation), lying in the subring `ℤ[√2]`.
Prop 1 computes `gde(a + √2·b, √2)` for such real elements from the
`2`-adic valuations of the integers `a, b`. This file ships the real-
subring infrastructure those statements need.

## Coordinates of a real element

`conj z = z ↔ z.a = −z.c ∧ z.b = 0` (`isReal_iff`). A real element is
therefore `⟨−c, 0, c, d⟩ = d + √2·c` (`real_eq`), i.e. `a + √2·b` with
`a = z.d`, `b = z.c`.

## The gde recursion engine (Prop 1)

For a real `z` (so `= a + √2·b`, `a = z.d`, `b = z.c`):

  * `dividesSqrt2 z ↔ 2 ∣ z.d`  (`dividesSqrt2_of_isReal`): `√2 ∣ z` iff
    the constant coordinate `a` is even.
  * `divSqrt2 z = ⟨−z.d/2, 0, z.d/2, z.c⟩`  (`divSqrt2_of_isReal`): one
    `√2`-peel performs the **swap** `(a, b) ↦ (b, a/2)`.

Iterating the peel is the Euclidean-style recursion that yields `gde` and
Prop 1's parity rule (`gde` even ⟺ `v₂(b) ≥ v₂(a)`).

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §2-3, Prop 1.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.Sde

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **A `ZOmega` element is real iff `conj z = z`**, equivalently
`z.a = −z.c ∧ z.b = 0` (so `z = ⟨−c, 0, c, d⟩`). -/
theorem isReal_iff (z : ZOmega) : conj z = z ↔ z.a = -z.c ∧ z.b = 0 := by
  rw [ZOmega.ext_iff]
  simp only [conj_a, conj_b, conj_c, conj_d, and_true]
  omega

/-- **`√2`-divisibility of a real element**: `√2 ∣ z ↔ 2 ∣ z.d` (the
constant coordinate `a = z.d` is even). -/
theorem dividesSqrt2_of_isReal {z : ZOmega} (h : conj z = z) :
    dividesSqrt2 z ↔ 2 ∣ z.d := by
  rw [isReal_iff] at h
  obtain ⟨ha, hb⟩ := h
  simp only [dividesSqrt2]
  omega

/-- **One `√2`-peel of a real `√2`-divisible element is the swap
`(a,b) ↦ (b, a/2)`**: when `2 ∣ z.d` (i.e. `√2 ∣ z`),
`divSqrt2 z = ⟨−(z.d/2), 0, z.d/2, z.c⟩` (again a real element, new
`a = z.c`, new `b = z.d/2`). The `2 ∣ z.d` hypothesis pins the integer
division (`(−z.d)/2 = −(z.d/2)` holds for even `z.d`). -/
theorem divSqrt2_of_isReal {z : ZOmega} (h : conj z = z) (hd : 2 ∣ z.d) :
    divSqrt2 z = ⟨-(z.d / 2), 0, z.d / 2, z.c⟩ := by
  rw [isReal_iff] at h
  obtain ⟨ha, hb⟩ := h
  apply ZOmega.ext
  · show (z.b - z.d) / 2 = -(z.d / 2); omega
  · show (z.a + z.c) / 2 = 0; omega
  · show (z.b + z.d) / 2 = z.d / 2; omega
  · show (z.c - z.a) / 2 = z.c; omega

/-- **The peel of a real `√2`-divisible element is real** (the swap stays
in `ℤ[√2]`). -/
theorem isReal_divSqrt2 {z : ZOmega} (h : conj z = z) (hd : 2 ∣ z.d) :
    conj (divSqrt2 z) = divSqrt2 z := by
  rw [divSqrt2_of_isReal h hd, isReal_iff]
  exact ⟨rfl, rfl⟩

end ZOmega

end SKEFTHawking.RossSelinger
