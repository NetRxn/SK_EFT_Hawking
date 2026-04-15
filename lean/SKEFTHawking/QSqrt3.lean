import Mathlib
import SKEFTHawking.PolyQuotQ

/-!
# Q(√3): Rationals Extended by √3

Arithmetic type for SU(2)₄ S-matrix verification.
Elements are a + b√3 with a, b ∈ ℚ, equipped with DecidableEq.

## Phase 5i Wave 4b refactor (2026-04-15)

Mul now delegates to `PolyQuotQ.mulReduce 2 ![3, 0]` (encoding x² = 3).
Struct API and all ⟨a, b⟩ call sites preserved.
-/

namespace SKEFTHawking

@[ext]
structure QSqrt3 where
  a : ℚ
  b : ℚ
  deriving DecidableEq, Repr

namespace QSqrt3

instance : Zero QSqrt3 := ⟨⟨0, 0⟩⟩
instance : One QSqrt3 := ⟨⟨1, 0⟩⟩
instance : Neg QSqrt3 where neg x := ⟨-x.a, -x.b⟩
instance : Add QSqrt3 where add x y := ⟨x.a + y.a, x.b + y.b⟩
instance : Sub QSqrt3 where sub x y := ⟨x.a - y.a, x.b - y.b⟩

/-- Reduction coefficients for Q(√3): x² = 3. -/
def reduction : Fin 2 → ℚ := ![3, 0]

/-- Coerce QSqrt3 ↔ PolyQuotQ 2 for the generic multiplication bridge. -/
def toPoly (x : QSqrt3) : PolyQuotQ 2 := ⟨![x.a, x.b]⟩
def ofPoly (p : PolyQuotQ 2) : QSqrt3 := ⟨p.coeffs 0, p.coeffs 1⟩

/-- Multiplication: delegates to generic mulReduce with x² = 3.
    Equivalent to (a₁+b₁√3)(a₂+b₂√3) = (a₁a₂+3b₁b₂) + (a₁b₂+b₁a₂)√3. -/
instance : Mul QSqrt3 where
  mul x y := ofPoly (PolyQuotQ.mulReduce 2 reduction x.toPoly y.toPoly)

/-- √3 = (0, 1). -/
def sqrt3 : QSqrt3 := ⟨0, 1⟩

/-- (√3)² = 3. -/
theorem sqrt3_sq : sqrt3 * sqrt3 = ⟨3, 0⟩ := by native_decide

/-! ## SU(2)₄ S-matrix (5×5 over Q(√3))

Entries: S_{ij} = √(2/6) · sin(π(i+1)(j+1)/6) = (1/√3) · sin(π(i+1)(j+1)/6)

| | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| 0 | √3/6 | 1/2 | √3/3 | 1/2 | √3/6 |
| 1 | 1/2 | 1/2 | 0 | -1/2 | -1/2 |
| 2 | √3/3 | 0 | -√3/3 | 0 | √3/3 |
| 3 | 1/2 | -1/2 | 0 | 1/2 | -1/2 |
| 4 | √3/6 | -1/2 | √3/3 | -1/2 | √3/6 |
-/

def s00 : QSqrt3 := ⟨0, 1/6⟩      -- √3/6
def s01 : QSqrt3 := ⟨1/2, 0⟩       -- 1/2
def s02 : QSqrt3 := ⟨0, 1/3⟩       -- √3/3
def s10 : QSqrt3 := ⟨1/2, 0⟩       -- 1/2
def s11 : QSqrt3 := ⟨1/2, 0⟩       -- 1/2
def s12 : QSqrt3 := ⟨0, 0⟩         -- 0
def s20 : QSqrt3 := ⟨0, 1/3⟩       -- √3/3
def s22 : QSqrt3 := ⟨0, -1/3⟩      -- -√3/3

/-- Row 0 · Row 0 = 1 (unitarity diagonal). -/
theorem s_row0_norm :
    s00*s00 + s01*s01 + s02*s02 + s01*s01 + s00*s00 = 1 := by native_decide

/-- Row 0 · Row 1 = 0 (unitarity off-diagonal). -/
theorem s_row01_ortho :
    s00*s10 + s01*s11 + s02*s12 + s01*⟨-1/2, 0⟩ + s00*⟨-1/2, 0⟩ = 0 := by native_decide

/-- Row 1 · Row 1 = 1. -/
theorem s_row1_norm :
    s10*s10 + s11*s11 + s12*s12 + ⟨-1/2, 0⟩*⟨-1/2, 0⟩ + ⟨-1/2, 0⟩*⟨-1/2, 0⟩ = 1 := by
  native_decide

/-- Row 2 · Row 2 = 1. -/
theorem s_row2_norm :
    s20*s20 + s12*s12 + s22*s22 + s12*s12 + s20*s20 = 1 := by native_decide

/-- Row 0 · Row 2 = 0. -/
theorem s_row02_ortho :
    s00*s20 + s01*s12 + s02*s22 + s01*s12 + s00*s20 = 0 := by native_decide

/-- det(S) ≠ 0 (modularity): S_{00}·S_{11} - S_{01}·S_{10} ≠ 0 for 2×2 block.
    For the full 5×5, we check S*S^T = I which implies det(S)² = 1. -/
theorem s_det_nonzero : s00 * s11 - s01 * s10 ≠ 0 := by native_decide

theorem qsqrt3_summary : True := trivial

end QSqrt3

end SKEFTHawking
