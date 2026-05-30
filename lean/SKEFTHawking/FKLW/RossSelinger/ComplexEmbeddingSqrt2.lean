/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item G — the `ℤ[ω][1/√2] → ℂ` ring embedding

Lifts `ZOmega.toComplex : ℤ[ω] →+* ℂ` (`ComplexEmbedding.lean`) through the
`√2`-localization quotient to `ZOmegaSqrt2.toComplex : ZOmegaSqrt2 →+* ℂ`,
`mk z k ↦ ZOmega.toComplex z / s2C^k` where `s2C = ZOmega.toComplex √2` (a complex
number with `s2C² = 2`, hence `≠ 0`, which is all the quotient lift's
well-definedness requires — the exact `s2C = (√2 : ℝ)` identification is deferred
to where the operator-norm approximation needs it).

This is the abstract↔analytic bridge: KMM exact synthesis produces a `Mat2` over
`ZOmegaSqrt2`; `toComplex` maps it into `ℂ`, where Item G's `cliffordTBaseFinder_kmm`
states its `SU(2, ℂ)` operator-norm approximation.

## Headline results

  * `ZOmegaSqrt2.s2C = ZOmega.toComplex √2`; `s2C_sq : s2C² = 2`; `s2C_ne_zero`.
  * `ZOmegaSqrt2.toComplex : ZOmegaSqrt2 →+* ℂ`.
  * `ZOmegaSqrt2.toComplex_mk : toComplex (mk z k) = ZOmega.toComplex z / s2C^k`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ComplexEmbedding
import SKEFTHawking.FKLW.RossSelinger.ZOmegaSqrt2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- `ω = e^{iπ/4} = (√2/2)(1 + i)` in `ℂ`. -/
theorem omegaC_eq : omegaC = (Real.sqrt 2 / 2 : ℂ) * (1 + Complex.I) := by
  rw [omegaC, Complex.exp_mul_I,
    show ((Real.pi : ℂ) / 4) = ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring

/-- `ω² = i` (`e^{iπ/4}² = e^{iπ/2} = i`). -/
theorem omegaC_sq : omegaC ^ 2 = Complex.I := by
  rw [omegaC, ← Complex.exp_nat_mul,
    show ((2:ℕ):ℂ) * (↑Real.pi / 4 * Complex.I) = ((Real.pi / 2 : ℝ):ℂ) * Complex.I by
      push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

end ZOmega

namespace ZOmegaSqrt2

/-- **`√2` embedded in `ℂ`** (as `ZOmega.toComplex √2`). -/
noncomputable def s2C : ℂ := ZOmega.toComplex ZOmega.sqrt2

theorem s2C_def : s2C = ZOmega.toComplex ZOmega.sqrt2 := rfl

/-- `s2C² = 2` (the defining `√2² = 2` pushed through the ring hom). -/
theorem s2C_sq : s2C ^ 2 = 2 := by rw [s2C, ← map_pow, sq, ZOmega.sqrt2_sq, map_ofNat]

theorem s2C_ne_zero : s2C ≠ 0 := by
  intro h; have := s2C_sq; rw [h] at this; norm_num at this

/-- **`s2C` is the real `√2`**: `ZOmega.toComplex √2 = (√2 : ℝ)`. The exact analytic
identification (`√2 = ω(1 − i)` via `ω = (√2/2)(1+i)`, `ω² = i`). -/
theorem s2C_eq : s2C = (Real.sqrt 2 : ℂ) := by
  have hs : s2C = ZOmega.omegaC - ZOmega.omegaC ^ 2 * ZOmega.omegaC := by
    rw [s2C, ZOmega.sqrt2, ZOmega.toComplex_apply]; push_cast; ring
  rw [hs, ZOmega.omegaC_sq, ZOmega.omegaC_eq]
  linear_combination (-(Real.sqrt 2 : ℂ) / 2) * Complex.I_sq

/-- The underlying function of the embedding (the `Frac`-quotient lift). -/
noncomputable def toComplexFun : ZOmegaSqrt2 → ℂ :=
  Quotient.lift (fun f : Frac => ZOmega.toComplex f.num / s2C ^ f.den) (by
    intro a b h
    have heq : a.num * ZOmega.sqrt2 ^ b.den = b.num * ZOmega.sqrt2 ^ a.den := h
    have hC : ZOmega.toComplex a.num * s2C ^ b.den = ZOmega.toComplex b.num * s2C ^ a.den := by
      have := congrArg ZOmega.toComplex heq; simpa [map_mul, map_pow, s2C] using this
    rw [div_eq_div_iff (pow_ne_zero _ s2C_ne_zero) (pow_ne_zero _ s2C_ne_zero)]; exact hC)

theorem toComplexFun_mk (z : ZOmega) (k : ℕ) :
    toComplexFun (mk z k) = ZOmega.toComplex z / s2C ^ k := rfl

/-- **The `ℤ[ω][1/√2] → ℂ` ring homomorphism** (evaluation at `ω = e^{iπ/4}`, `√2 ↦ s2C`). -/
noncomputable def toComplex : ZOmegaSqrt2 →+* ℂ where
  toFun := toComplexFun
  map_one' := by rw [one_def, toComplexFun_mk, map_one, pow_zero, div_one]
  map_zero' := by rw [zero_def, toComplexFun_mk, map_zero, zero_div]
  map_mul' := by
    rintro ⟨⟨z1, k1⟩⟩ ⟨⟨z2, k2⟩⟩
    show toComplexFun (mk z1 k1 * mk z2 k2) = toComplexFun (mk z1 k1) * toComplexFun (mk z2 k2)
    rw [mk_mul]
    simp only [toComplexFun_mk, map_mul, pow_add]
    field_simp
  map_add' := by
    rintro ⟨⟨z1, k1⟩⟩ ⟨⟨z2, k2⟩⟩
    show toComplexFun (mk z1 k1 + mk z2 k2) = toComplexFun (mk z1 k1) + toComplexFun (mk z2 k2)
    rw [mk_add, toComplexFun_mk, toComplexFun_mk, toComplexFun_mk, map_add, map_mul, map_mul,
      map_pow, map_pow, ← s2C_def, pow_add,
      div_add_div _ _ (pow_ne_zero k1 s2C_ne_zero) (pow_ne_zero k2 s2C_ne_zero)]
    ring

@[simp] theorem toComplex_mk (z : ZOmega) (k : ℕ) :
    toComplex (mk z k) = ZOmega.toComplex z / s2C ^ k := rfl

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
