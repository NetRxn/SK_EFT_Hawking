/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item G — the `ℤ[ω] → ℂ` ring embedding

`ZOmega = ℤ[ω]` with `ω = e^{iπ/4}` a primitive 8th root of unity (minimal
polynomial `x⁴ + 1`). This file ships the canonical evaluation ring homomorphism
`ZOmega.toComplex : ZOmega →+* ℂ`, `⟨a,b,c,d⟩ ↦ a·ω³ + b·ω² + c·ω + d` with
`ω = Complex.exp(π/4·I)`. It is the foundation for the `ZOmegaSqrt2 → ℂ` embedding
and the eventual bridge connecting KMM exact synthesis (over `ZOmegaSqrt2`) to the
`SU(2, ℂ)` operator-norm approximation of Item G.

## Headline results

  * `ZOmega.omegaC = e^{iπ/4}`; `ZOmega.omegaC_pow_four : ω⁴ = -1`.
  * `ZOmega.toComplex : ZOmega →+* ℂ` — the evaluation ring hom.
  * `ZOmega.toComplex_apply` — the explicit four-term value.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ZOmega
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **The primitive 8th root of unity** `ω = e^{iπ/4} ∈ ℂ`. -/
noncomputable def omegaC : ℂ := Complex.exp ((Real.pi / 4) * Complex.I)

/-- **`ω⁴ = -1`** in `ℂ` (`ω` is a primitive 8th root of unity, minimal poly `x⁴+1`). -/
theorem omegaC_pow_four : omegaC ^ 4 = -1 := by
  have h : omegaC ^ 4 = Complex.exp (↑Real.pi * Complex.I) := by
    rw [omegaC, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [h, Complex.exp_pi_mul_I]

/-- **`ℤ[ω] → ℂ` evaluation** at `ω = e^{iπ/4}`: `⟨a,b,c,d⟩ ↦ a·ω³ + b·ω² + c·ω + d`. -/
noncomputable def toComplexFun (z : ZOmega) : ℂ :=
  (z.a : ℂ) * omegaC ^ 3 + (z.b : ℂ) * omegaC ^ 2 + (z.c : ℂ) * omegaC + (z.d : ℂ)

/-- **The `ℤ[ω] → ℂ` ring homomorphism** (evaluation at `ω = e^{iπ/4}`). Multiplicativity
is the `ω⁴ = -1` reduction of the convolution product. -/
noncomputable def toComplex : ZOmega →+* ℂ where
  toFun := toComplexFun
  map_one' := by simp [toComplexFun]
  map_zero' := by simp [toComplexFun]
  map_add' x y := by
    simp only [toComplexFun, ZOmega.add_a, ZOmega.add_b, ZOmega.add_c, ZOmega.add_d]
    push_cast; ring
  map_mul' x y := by
    simp only [toComplexFun, ZOmega.mul_a, ZOmega.mul_b, ZOmega.mul_c, ZOmega.mul_d]
    push_cast
    linear_combination
      (-((x.a : ℂ) * y.c + x.b * y.b + x.c * y.a)) * omegaC_pow_four
      + (-((x.a : ℂ) * y.b + x.b * y.a) * omegaC) * omegaC_pow_four
      + (-((x.a : ℂ) * y.a) * omegaC ^ 2) * omegaC_pow_four

@[simp] theorem toComplex_apply (z : ZOmega) :
    toComplex z = (z.a : ℂ) * omegaC ^ 3 + (z.b : ℂ) * omegaC ^ 2 + (z.c : ℂ) * omegaC + (z.d : ℂ) :=
  rfl

end ZOmega

end SKEFTHawking.RossSelinger
