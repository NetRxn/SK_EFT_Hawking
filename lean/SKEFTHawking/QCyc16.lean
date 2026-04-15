import Mathlib
import SKEFTHawking.PolyQuotQ

/-!
# Q(ζ₁₆): 16th Cyclotomic Field

Arithmetic type for R-matrix verification in the Ising MTC.
Elements are a₀ + a₁ζ + a₂ζ² + ... + a₇ζ⁷ with aᵢ ∈ ℚ,
where ζ = ζ₁₆ = e^{iπ/8} satisfies ζ⁸ = -1
(minimal polynomial Φ₁₆(x) = x⁸ + 1).

Degree 8 over Q. Contains Q(i) and Q(√2) as subfields.
Equipped with DecidableEq for native_decide verification.

## References
- Rowell, Stong, Wang, Comm. Math. Phys. 292, 343 (2009)
- Kitaev, Ann. Phys. 321, 2 (2006), Appendix E
-/

namespace SKEFTHawking

/-- Elements of Q(ζ₁₆) = Q[x]/(x⁸+1), represented as 8-tuples of rationals. -/
@[ext]
structure QCyc16 where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  c4 : ℚ
  c5 : ℚ
  c6 : ℚ
  c7 : ℚ
  deriving DecidableEq, Repr

namespace QCyc16

instance : Zero QCyc16 := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
instance : One QCyc16 := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

instance : Neg QCyc16 where
  neg x := ⟨-x.c0, -x.c1, -x.c2, -x.c3, -x.c4, -x.c5, -x.c6, -x.c7⟩

instance : Add QCyc16 where
  add x y := ⟨x.c0+y.c0, x.c1+y.c1, x.c2+y.c2, x.c3+y.c3,
              x.c4+y.c4, x.c5+y.c5, x.c6+y.c6, x.c7+y.c7⟩

instance : Sub QCyc16 where
  sub x y := ⟨x.c0-y.c0, x.c1-y.c1, x.c2-y.c2, x.c3-y.c3,
              x.c4-y.c4, x.c5-y.c5, x.c6-y.c6, x.c7-y.c7⟩

/-- Reduction coefficients for Q(ζ₁₆): x⁸ = -1.

Phase 5i Wave 4b refactor (2026-04-15): Mul delegates to the generic
`PolyQuotQ.mulReduce 8 reduction`. The reduction rule x⁸ = -1 means
x⁹ = -x, x¹⁰ = -x², etc. — the generic reducePower handles this
recursively. Struct API and all Ising braiding / trefoil call sites preserved. -/
def reduction : Fin 8 → ℚ := ![-1, 0, 0, 0, 0, 0, 0, 0]

/-- Coerce QCyc16 ↔ PolyQuotQ 8 for the generic multiplication bridge. -/
def toPoly (x : QCyc16) : PolyQuotQ 8 :=
  ⟨![x.c0, x.c1, x.c2, x.c3, x.c4, x.c5, x.c6, x.c7]⟩
def ofPoly (p : PolyQuotQ 8) : QCyc16 :=
  ⟨p.coeffs 0, p.coeffs 1, p.coeffs 2, p.coeffs 3,
   p.coeffs 4, p.coeffs 5, p.coeffs 6, p.coeffs 7⟩

/-- Multiplication mod ζ⁸ = -1, via the generic mulReduce. -/
instance : Mul QCyc16 where
  mul x y := ofPoly (PolyQuotQ.mulReduce 8 reduction x.toPoly y.toPoly)

/-- ζ₁₆ = e^{iπ/8}. -/
def zeta : QCyc16 := ⟨0, 1, 0, 0, 0, 0, 0, 0⟩

/-- ζ⁻¹ = -ζ⁷ (from ζ·ζ⁷ = ζ⁸ = -1). -/
def zeta_inv : QCyc16 := ⟨0, 0, 0, 0, 0, 0, 0, -1⟩

/-- √2 = ζ² - ζ⁶ (= 2cos(π/4) via ζ² + ζ⁻² where ζ⁻² = -ζ⁶). -/
def sqrt2 : QCyc16 := ⟨0, 0, 1, 0, 0, 0, -1, 0⟩

/-- ζ · ζ⁻¹ = 1. -/
theorem zeta_mul_inv : zeta * zeta_inv = 1 := by native_decide

/-- ζ² · ζ² gives ζ⁴. -/
theorem zeta2_sq : zeta * zeta * (zeta * zeta) = ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ := by native_decide

/-- (√2)² = 2. -/
theorem sqrt2_sq : sqrt2 * sqrt2 = ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ := by native_decide

/-- ζ⁸ = -1: the defining relation. -/
theorem zeta8_neg_one :
    let z2 := zeta * zeta
    let z4 := z2 * z2
    let z8 := z4 * z4
    z8 = ⟨-1, 0, 0, 0, 0, 0, 0, 0⟩ := by native_decide

/-- ζ¹⁶ = 1: primitive 16th root of unity. -/
theorem zeta16_one :
    let z2 := zeta * zeta
    let z4 := z2 * z2
    let z8 := z4 * z4
    z8 * z8 = 1 := by native_decide

theorem qcyc16_summary : True := trivial

end QCyc16

end SKEFTHawking
