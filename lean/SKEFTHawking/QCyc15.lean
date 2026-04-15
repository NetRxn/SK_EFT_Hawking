/-
# Q(ζ₁₅): 15th Cyclotomic Field

Degree 8 over ℚ. Minimal polynomial Φ₁₅(x) = x⁸ − x⁷ + x⁵ − x⁴ + x³ − x + 1.

Used for SU(3)₂ S-matrix and T-matrix verification (first rank-6 MTC modular
data formalized in a proof assistant).

## Reduction rule

  ζ⁸ = ζ⁷ − ζ⁵ + ζ⁴ − ζ³ + ζ − 1

As reduction coefficients `r : Fin 8 → ℚ`:
  r = ![-1, 1, 0, -1, 1, -1, 0, 1]

## Key algebraic constants

From the deep research `Lit-Search/Phase-5i/5i-SU(3)₂ modular tensor
category- exact data over Q(ζ₁₅).md`:

  √5 = ζ³ − ζ⁶ − ζ⁹ + ζ¹² (Gauss sum) = (1, 0, -2, 2, 0, 0, 0, -2)
  φ  = (1+√5)/2           = (1, 0, -1, 1, 0, 0, 0, -1)
  1/φ = φ − 1              = (0, 0, -1, 1, 0, 0, 0, -1)
  ω₃ = e^{2πi/3} = ζ⁵     = (0, 0, 0, 0, 0, 1, 0, 0)

## Phase 5i Wave 4c (2026-04-15)

First instance of the `PolyQuotQ` generic construction at degree 8 for a
proper cyclotomic field (QCyc16 is also degree 8 but minimal polynomial
x⁸ + 1 is simpler). Validates that `mulReduce` handles the Φ₁₅
minimal polynomial's 7-term reduction.

## References

- Deep research: `Lit-Search/Phase-5i/5i-SU(3)₂ modular tensor category-
  exact data over Q(ζ₁₅).md`
- Washington, *Introduction to Cyclotomic Fields* (Springer 1997)
-/

import Mathlib
import SKEFTHawking.PolyQuotQ

namespace SKEFTHawking

/-- Q(ζ₁₅) via the generic polynomial quotient construction. -/
abbrev QCyc15 := PolyQuotQ 8

namespace QCyc15

/-- Reduction coefficients for Q(ζ₁₅): ζ⁸ = ζ⁷ − ζ⁵ + ζ⁴ − ζ³ + ζ − 1.

Read off from Φ₁₅(x) = x⁸ − x⁷ + x⁵ − x⁴ + x³ − x + 1 by
rearranging: x⁸ = x⁷ − x⁵ + x⁴ − x³ + x − 1. Seven non-zero reduction
coefficients (Φ₁₅ is the densest cyclotomic polynomial of degree 8).

Multiplication routes through the generic `PolyQuotQ.mulReduce`. The
initial QCyc15 build was pathologically slow (7+ min with chained
muls), which led to identifying a lazy-closure-reeval bug in the
generic `mulReduce`: the returned struct's `coeffs` field was a lazy
closure over the double sum, causing each chained mul to re-execute
its inputs' full computations. The fix (materializing the output to
an Array before wrapping in the struct, see `PolyQuotQ.mulReduce`)
restored O(n³) per-mul performance for all cyclotomic degrees. -/
def reduction : Fin 8 → ℚ := ![-1, 1, 0, -1, 1, -1, 0, 1]

/-- Multiplication on Q(ζ₁₅) via the generic mulReduce. -/
instance : Mul QCyc15 where
  mul x y := PolyQuotQ.mulReduce 8 reduction x y

/-- One = ⟨![1, 0, 0, 0, 0, 0, 0, 0]⟩. -/
instance : One QCyc15 := ⟨⟨![1, 0, 0, 0, 0, 0, 0, 0]⟩⟩

/-! ## Primitive root and key algebraic constants -/

/-- ζ = ζ₁₅ = e^{2πi/15}. -/
def zeta : QCyc15 := ⟨![0, 1, 0, 0, 0, 0, 0, 0]⟩

/-- ζ² -/
def zeta2 : QCyc15 := ⟨![0, 0, 1, 0, 0, 0, 0, 0]⟩

/-- ζ³ -/
def zeta3 : QCyc15 := ⟨![0, 0, 0, 1, 0, 0, 0, 0]⟩

/-- ζ⁴ -/
def zeta4 : QCyc15 := ⟨![0, 0, 0, 0, 1, 0, 0, 0]⟩

/-- ζ⁵ = ω₃ (primitive cube root of unity). -/
def zeta5 : QCyc15 := ⟨![0, 0, 0, 0, 0, 1, 0, 0]⟩

/-- ζ⁶ -/
def zeta6 : QCyc15 := ⟨![0, 0, 0, 0, 0, 0, 1, 0]⟩

/-- ζ⁷ -/
def zeta7 : QCyc15 := ⟨![0, 0, 0, 0, 0, 0, 0, 1]⟩

/-- √5 as 8-tuple in Q(ζ₁₅) basis (Gauss sum). -/
def sqrt5 : QCyc15 := ⟨![1, 0, -2, 2, 0, 0, 0, -2]⟩

/-- Golden ratio φ = (1+√5)/2. -/
def phi : QCyc15 := ⟨![1, 0, -1, 1, 0, 0, 0, -1]⟩

/-- 1/φ = φ − 1. -/
def phi_inv : QCyc15 := ⟨![0, 0, -1, 1, 0, 0, 0, -1]⟩

/-! ## Fundamental identities -/

/-- The defining cyclotomic relation: ζ⁸ − ζ⁷ + ζ⁵ − ζ⁴ + ζ³ − ζ + 1 = 0,
    equivalently ζ⁸ = ζ⁷ − ζ⁵ + ζ⁴ − ζ³ + ζ − 1.
    Verify: ζ · ζ⁷ = ζ⁸ should reduce to the expected 8-tuple. -/
theorem zeta_times_zeta7 : zeta * zeta7 = ⟨![-1, 1, 0, -1, 1, -1, 0, 1]⟩ := by
  native_decide

/-- ζ¹⁵ = 1 (primitive 15th root). Verified via chained mulReduce:
    ζ² · ζ² · ζ² · ζ² · ζ⁷ = ζ¹⁵ should equal 1. -/
theorem zeta15_eq_one :
    zeta2 * zeta2 * zeta2 * zeta2 * zeta7 = 1 := by native_decide

/-- (√5)² = 5. Foundational algebraic identity. -/
theorem sqrt5_sq : sqrt5 * sqrt5 = ⟨![5, 0, 0, 0, 0, 0, 0, 0]⟩ := by native_decide

/-- φ² = φ + 1 (golden ratio defining relation). -/
theorem phi_sq_eq_phi_plus_one : phi * phi = phi + 1 := by native_decide

/-- φ · (1/φ) = 1. -/
theorem phi_mul_phi_inv : phi * phi_inv = 1 := by native_decide

/-- ω₃³ = (ζ⁵)³ = ζ¹⁵ = 1 (cube root of unity). -/
theorem omega3_cubed : zeta5 * zeta5 * zeta5 = 1 := by native_decide

/-- ω₃ + ω₃² + 1 = 0 (cyclotomic relation for Z/3). -/
theorem omega3_sum_zero :
    zeta5 + zeta5 * zeta5 + 1 = 0 := by native_decide

/-! ## Module summary -/

/--
QCyc15 module: Q(ζ₁₅) via generic PolyQuotQ construction.

- Degree 8 over ℚ, minimal polynomial Φ₁₅
- Key constants: ζ, ζ², ..., ζ⁷, √5, φ, 1/φ, ω₃ = ζ⁵
- Fundamental identities proved: ζ¹⁵ = 1, (√5)² = 5, φ² = φ+1, φ·(1/φ) = 1
- Zero sorry, all native_decide
- First instance of PolyQuotQ at degree 8 for a proper cyclotomic field
- Enables SU(3)₂ S-matrix and T-matrix verification (SU3k2SMatrix.lean)
-/
theorem qcyc15_summary : True := trivial

end QCyc15

end SKEFTHawking
