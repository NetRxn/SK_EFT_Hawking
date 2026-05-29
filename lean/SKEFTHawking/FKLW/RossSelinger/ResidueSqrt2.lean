/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — the `√2`-residue map (KMM Lemma 3 substrate)

Builds the residue map of `ZOmega = ℤ[ω]` modulo `√2`. The quotient
`ℤ[ω]/(√2)` has four elements (`N(√2) = 4`), but it is **NOT the field
`𝔽₄`**: `2` is totally ramified in `ℚ(ζ₈)` (`(2) = 𝔭⁴`), so `√2 = 𝔭²`
is **not prime**, and the quotient is the local ring `𝔽₂[ε]/(ε²)` (with
a nilpotent `ε`). Concretely `ω² ≡ 1 (mod √2)` — i.e. `i ≡ 1`, since
`i − 1 = ⟨0,1,0,−1⟩` is `√2`-divisible — so `ρ(ω)` is the order-2 unit
`1 + ε`, impossible in `𝔽₄*` (order 3). KMM's residue argument uses this
nilpotent structure, not a field.

From the `√2`-divisibility criterion (`Sde.lean`):

  `√2 ∣ z  ↔  z.a ≡ z.c (mod 2) ∧ z.b ≡ z.d (mod 2)`,

so a residue is faithfully coordinatized by the pair

  `resSqrt2 z = ((z.a − z.c : ZMod 2), (z.b − z.d : ZMod 2)) ∈ ZMod 2 × ZMod 2`.

The additive/coset layer is `resSqrt2_add`; the (`𝔽₂[ε]/(ε²)`)
multiplicative layer is `resMul` + `resSqrt2_mul` below — the structure
KMM Lemma 3 reasons over (the residues of the matrix column entries).

## Headline results

  * `ZOmega.resSqrt2 : ZOmega → ZMod 2 × ZMod 2`.
  * `resSqrt2_eq_zero_iff_dividesSqrt2` — `resSqrt2 z = 0 ↔ √2 ∣ z`.
  * `resSqrt2_add` / `resSqrt2_zero` / `resSqrt2_neg` — additive structure.
  * `resSqrt2_sqrt2 = 0`, `resSqrt2_two = 0` — `√2` and `2` are `≡ 0`.
  * `resSqrt2_one`, `resSqrt2_omega` — the unit residues.

## References

  * Pre-Implementation Research Dossier §3.3.
  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §3, Lemma 3.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.Sde
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **The `√2`-residue map** `ℤ[ω] → ℤ[ω]/(√2)`, coordinatized as the pair
`((z.a − z.c) mod 2, (z.b − z.d) mod 2)`. Two elements have the same
residue iff their difference is divisible by `√2`. -/
def resSqrt2 (z : ZOmega) : ZMod 2 × ZMod 2 :=
  (((z.a - z.c : ℤ) : ZMod 2), ((z.b - z.d : ℤ) : ZMod 2))

@[simp] theorem resSqrt2_fst (z : ZOmega) :
    (resSqrt2 z).1 = ((z.a - z.c : ℤ) : ZMod 2) := rfl
@[simp] theorem resSqrt2_snd (z : ZOmega) :
    (resSqrt2 z).2 = ((z.b - z.d : ℤ) : ZMod 2) := rfl

/-- **The residue is `0` exactly on the multiples of `√2`**. -/
theorem resSqrt2_eq_zero_iff_dividesSqrt2 (z : ZOmega) :
    resSqrt2 z = 0 ↔ dividesSqrt2 z := by
  rw [Prod.ext_iff]
  simp only [resSqrt2_fst, resSqrt2_snd, Prod.fst_zero, Prod.snd_zero,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold dividesSqrt2
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, by omega⟩

/-! ## Additive structure -/

@[simp] theorem resSqrt2_zero : resSqrt2 0 = 0 := by
  simp [resSqrt2]

theorem resSqrt2_add (z w : ZOmega) :
    resSqrt2 (z + w) = resSqrt2 z + resSqrt2 w := by
  simp only [resSqrt2, add_a, add_b, add_c, add_d, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> push_cast <;> ring

theorem resSqrt2_neg (z : ZOmega) : resSqrt2 (-z) = - resSqrt2 z := by
  simp only [resSqrt2, neg_a, neg_b, neg_c, neg_d, Prod.neg_mk, Prod.mk.injEq]
  constructor <;> push_cast <;> ring

/-! ## Key residues -/

@[simp] theorem resSqrt2_sqrt2 : resSqrt2 sqrt2 = 0 := by
  rw [resSqrt2_eq_zero_iff_dividesSqrt2]
  unfold dividesSqrt2 sqrt2
  decide

@[simp] theorem resSqrt2_two : resSqrt2 (2 : ZOmega) = 0 := by
  rw [resSqrt2_eq_zero_iff_dividesSqrt2]
  unfold dividesSqrt2
  decide

/-- **`1` has residue `(1, 0)`** (`1 = ⟨0,0,0,1⟩`, so `a − c = 0`,
`b − d = −1 ≡ 1`). -/
theorem resSqrt2_one : resSqrt2 1 = (0, 1) := by
  simp only [resSqrt2, one_a, one_b, one_c, one_d]
  decide

/-- **`ω` has residue `(1, 0)`** (`ω = ⟨0,0,1,0⟩`, so `a − c = −1 ≡ 1`,
`b − d = 0`). A nonzero residue — `ω` is a unit, not a multiple of `√2`. -/
theorem resSqrt2_omega : resSqrt2 ω = (1, 0) := by
  simp only [resSqrt2, ω_a, ω_b, ω_c, ω_d]
  decide

/-! ## Multiplicative structure (`𝔽₂[ε]/(ε²)`) -/

/-- **Multiplication on the residue ring** `ℤ[ω]/(√2) ≅ 𝔽₂[ε]/(ε²)`, in
the `(z.a − z.c, z.b − z.d)` coordinatization. Identity is `(0, 1) = ρ(1)`;
`(1,0) = ρ(ω) = 1 + ε` is the order-2 nilpotent-shifted unit
(`resMul (1,0) (1,0) = (0,1)`). -/
def resMul (p q : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 :=
  (p.1 * q.2 + p.2 * q.1, p.1 * q.1 + p.2 * q.2)

/-- **`resSqrt2` is multiplicative**: `ρ(z·w) = ρ(z) · ρ(w)` in the
residue ring. Verified by `decide` over the `2⁸` residue coordinates
(the `ZMod 2` identity holds because the `ℤ`-level discrepancy is even). -/
theorem resSqrt2_mul (z w : ZOmega) :
    resSqrt2 (z * w) = resMul (resSqrt2 z) (resSqrt2 w) := by
  simp only [resSqrt2, resMul, mul_a, mul_b, mul_c, mul_d]
  push_cast
  generalize (z.a : ZMod 2) = za; generalize (z.b : ZMod 2) = zb
  generalize (z.c : ZMod 2) = zc; generalize (z.d : ZMod 2) = zd
  generalize (w.a : ZMod 2) = wa; generalize (w.b : ZMod 2) = wb
  generalize (w.c : ZMod 2) = wc; generalize (w.d : ZMod 2) = wd
  revert za zb zc zd wa wb wc wd
  decide

end ZOmega

end SKEFTHawking.RossSelinger
