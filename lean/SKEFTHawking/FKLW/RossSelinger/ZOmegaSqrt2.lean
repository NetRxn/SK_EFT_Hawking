/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item E (M2) — `ZOmegaSqrt2 := ℤ[ω][1/√2]`

Ships the **theory-layer** representation of `ℤ[ω][1/√2]` via Mathlib's
`Localization.Away` machinery, with the key arithmetic fact `√2² = 2`
discharged at the substrate level.

Per Pre-Implementation Research Dossier §1.7, there are two viable
representations:

  **(A) Localization.Away (clean theory):**
       `def ZOmegaSqrt2 := Localization.Away (sqrt2 : ZOmega)`
       Uses Mathlib's `Localization.Away.Basic` + `Localization.Basic`
       (`Localization.mk`, `IsLocalization.lift`). Inherits `CommRing`
       automatically. Non-computable but mathematically clean.

  **(B) Runtime pair representation:**
       `(z : ZOmega, k : ℕ)` representing `z / (√2)^k`, with equivalence
       `(z, k) ∼ (√2·z, k+1)`. `native_decide`-friendly but requires
       custom CommRing proof obligations.

This file ships **(A)** as the substrate definition. The runtime
representation **(B)** and the runtime↔theory equivalence proof are
deferred to a follow-on (substantial multi-session work; ~600 LoC per
DR estimate). Downstream consumers (KMM exact synthesis in Item F, the
constructive base finder in Item G) use the localization API of (A);
runtime cross-validation requires (B), which lands later.

## Mathematical structure (verified by direct computation in M1)

`√2 = ω + ω⁻¹ = ω − ω³ = ⟨−1, 0, 1, 0⟩ : ZOmega`. Computation in M1's
multiplication table gives:

  `√2² = ⟨-1, 0, 1, 0⟩ · ⟨-1, 0, 1, 0⟩ = ⟨0, 0, 0, 2⟩ = 2`

So `√2 ∈ ZOmega` is a non-zero divisor (in fact a non-unit; norm 4), and
`Localization.Away (√2)` is the principal localization at this element.

## Headline definitions

  * `ZOmega.sqrt2 := ω − ω³ ∈ ZOmega` — the canonical square root of 2.
  * `ZOmega.sqrt2_sq : sqrt2 * sqrt2 = 2` — defining identity.
  * `ZOmegaSqrt2 := Localization.Away (sqrt2 : ZOmega)` — theory-layer
    representation.
  * `ZOmegaSqrt2.sqrt2 : ZOmegaSqrt2` — `sqrt2` lifted to the localization.
  * `ZOmegaSqrt2.invSqrt2 : ZOmegaSqrt2` — the multiplicative inverse of
    `√2` in the localization.
  * `ZOmegaSqrt2.invSqrt2_mul_sqrt2 : invSqrt2 * sqrt2 = 1` — defining
    identity for the inverse.

## Deferred to follow-ons

  * Pair representation `ZOmegaSqrt2Runtime` + CommRing + DecidableEq.
  * `ZOmegaSqrt2Runtime ≃+* ZOmegaSqrt2` equivalence.
  * `ZOmegaSqrt2.toComplex` via the universal property
    (`Localization.lift` with the ring-hom `ZOmega →+* ℂ` from M1, once
    the M1 `toComplex` ring-hom multiplicativity ships).

## References

  * Pre-Implementation Research Dossier §1.7 (dual-representation design).
  * Mathlib's `Mathlib.RingTheory.Localization.Away.Basic`,
    `Mathlib.RingTheory.Localization.Basic`.
  * Mathlib's `Mathlib.RingTheory.Localization.Defs`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ZOmega
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-! ## 1. `sqrt2` element in ZOmega -/

/-- **`sqrt2 = ω - ω³` as a `ZOmega` element**.

In tuple form `(a, b, c, d) = (-1, 0, 1, 0)`. The defining equation
`sqrt2² = 2` is discharged by direct computation in M1's multiplication
table; the result is the constant `2 = (0, 0, 0, 2)`. -/
def sqrt2 : ZOmega := ⟨-1, 0, 1, 0⟩

@[simp] theorem sqrt2_a : sqrt2.a = -1 := rfl
@[simp] theorem sqrt2_b : sqrt2.b = 0 := rfl
@[simp] theorem sqrt2_c : sqrt2.c = 1 := rfl
@[simp] theorem sqrt2_d : sqrt2.d = 0 := rfl

/-- **The defining identity** `sqrt2² = 2`. -/
theorem sqrt2_sq : sqrt2 * sqrt2 = (2 : ZOmega) := by
  show sqrt2 * sqrt2 = (⟨0, 0, 0, 2⟩ : ZOmega)
  ext <;> simp <;> ring

/-- **`sqrt2` is a non-zero element of `ZOmega`**. -/
theorem sqrt2_ne_zero : sqrt2 ≠ 0 := by decide

/-- **Complex conjugation fixes `sqrt2`** (since `√2 = ω + ω⁻¹` is real).

The Galois automorphism `σ_7 = conj` fixes the real subfield `ℚ(√2)`
of `ℚ(ζ_8)`; `√2` lies in this subfield. -/
theorem conj_sqrt2 : conj sqrt2 = sqrt2 := by
  ext <;> simp

/-- **The `σ_3` Galois automorphism sends `sqrt2 ↦ -sqrt2`**.

`σ_3(ω) = ω³`, so `σ_3(√2) = σ_3(ω - ω³) = ω³ - ω⁹ = ω³ - ω = -√2`. -/
theorem σ3_sqrt2 : σ3 sqrt2 = -sqrt2 := by
  ext <;> simp

/-- **The `σ_5` Galois automorphism sends `sqrt2 ↦ -sqrt2`**.

`σ_5(ω) = -ω`, so `σ_5(√2) = σ_5(ω - ω³) = -ω - (-ω)³ = -ω + ω³ = -√2`. -/
theorem σ5_sqrt2 : σ5 sqrt2 = -sqrt2 := by
  ext <;> simp

end ZOmega

/-! ## 2. `ZOmegaSqrt2` as `Localization.Away (sqrt2 : ZOmega)` -/

/-- **The ring `ℤ[ω][1/√2]`** as the principal localization of `ZOmega`
at the canonical square root of 2.

Provides the substrate for Ross-Selinger 2014 Clifford+T exact synthesis:
the algorithm's grid-problem solutions lie in this ring, and the
Kliuchnikov-Maslov-Mosca exact synthesis algorithm produces words over
ZOmegaSqrt2 entries.

Inherits `CommRing`, `Algebra ZOmega`, and the localization universal
property from Mathlib's `Localization.Away.Basic`. -/
def ZOmegaSqrt2 : Type := Localization.Away (ZOmega.sqrt2)

namespace ZOmegaSqrt2

/-- The inherited `CommRing` instance. -/
noncomputable instance : CommRing ZOmegaSqrt2 :=
  (inferInstanceAs (CommRing (Localization.Away ZOmega.sqrt2)))

/-- The inherited `Algebra ZOmega ZOmegaSqrt2` instance — the canonical
ring-hom `ZOmega →+* ZOmegaSqrt2` lifts every `ZOmega` element. -/
noncomputable instance : Algebra ZOmega ZOmegaSqrt2 :=
  (inferInstanceAs (Algebra ZOmega (Localization.Away ZOmega.sqrt2)))

/-- The canonical `IsLocalization` instance from Mathlib. -/
noncomputable instance : IsLocalization (Submonoid.powers ZOmega.sqrt2) ZOmegaSqrt2 :=
  (inferInstanceAs (IsLocalization (Submonoid.powers ZOmega.sqrt2)
    (Localization.Away ZOmega.sqrt2)))

/-- **`sqrt2` lifted to `ZOmegaSqrt2`**: the image of `ZOmega.sqrt2`
under the canonical algebra-map. -/
noncomputable def sqrt2 : ZOmegaSqrt2 :=
  algebraMap ZOmega ZOmegaSqrt2 ZOmega.sqrt2

/-- **`sqrt2` (lifted)** is a unit in `ZOmegaSqrt2` — the entire purpose
of the localization. -/
theorem sqrt2_isUnit : IsUnit (sqrt2 : ZOmegaSqrt2) := by
  unfold sqrt2
  exact @IsLocalization.map_units _ _ (Submonoid.powers ZOmega.sqrt2) _ _ _ _
    ⟨ZOmega.sqrt2, Submonoid.mem_powers _⟩

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
