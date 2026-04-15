import Mathlib
import SKEFTHawking.PolyQuotQ

/-!
# Q(√2): Rationals Extended by √2

Arithmetic type for F-symbol verification in the Ising MTC.
Elements are a + b√2 with a, b ∈ ℚ, equipped with DecidableEq
for native_decide verification of pentagon equations.

This is a quadratic number field — all arithmetic is exact.

## Phase 5i Wave 4a refactor (2026-04-15)

QSqrt2 retains its struct API (`a b : ℚ` fields, `⟨1, 0⟩` syntax) for
backward compatibility with 23+ existing call sites in FPDimension.lean,
MugerCenter.lean, SU2kMTC.lean, and others. The `Mul` instance now
delegates to the generic `PolyQuotQ.mulReduce` with reduction coefficients
`![2, 0]` (encoding x² = 2), validating that native_decide still reduces
through the generic layer. Arithmetic is bit-for-bit equivalent to the
prior hand-rolled version — the consolidation is purely in the polynomial
reduction logic, which now lives in one place.
-/

namespace SKEFTHawking

/-- Elements of Q(√2) = {a + b√2 : a, b ∈ ℚ}. -/
structure QSqrt2 where
  a : ℚ
  b : ℚ
  deriving DecidableEq, Repr

namespace QSqrt2

@[ext]
theorem ext {x y : QSqrt2} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; simp_all

instance : Zero QSqrt2 := ⟨⟨0, 0⟩⟩
instance : One QSqrt2 := ⟨⟨1, 0⟩⟩

instance : Neg QSqrt2 where
  neg x := ⟨-x.a, -x.b⟩

instance : Add QSqrt2 where
  add x y := ⟨x.a + y.a, x.b + y.b⟩

instance : Sub QSqrt2 where
  sub x y := ⟨x.a - y.a, x.b - y.b⟩

/-! ## Coercion to PolyQuotQ 2 and reduction-backed multiplication

The `Mul` instance routes through `PolyQuotQ.mulReduce 2 ![2, 0]`, proving
that the generic computable-arithmetic infrastructure handles this case
correctly while preserving QSqrt2's `⟨a, b⟩` struct API. -/

/-- Reduction coefficients for Q(√2): x² = 2. -/
def reduction : Fin 2 → ℚ := ![2, 0]

/-- Coerce QSqrt2 into the generic PolyQuotQ 2 representation. -/
def toPoly (x : QSqrt2) : PolyQuotQ 2 := ⟨![x.a, x.b]⟩

/-- Coerce back from PolyQuotQ 2 to QSqrt2. -/
def ofPoly (p : PolyQuotQ 2) : QSqrt2 := ⟨p.coeffs 0, p.coeffs 1⟩

/-- Multiplication: delegates to the generic mulReduce with x² = 2.
    Equivalent to the hand-rolled formula
    (a₁+b₁√2)(a₂+b₂√2) = (a₁a₂+2b₁b₂) + (a₁b₂+b₁a₂)√2
    but computed through the shared polynomial-reduction infrastructure. -/
instance : Mul QSqrt2 where
  mul x y := ofPoly (PolyQuotQ.mulReduce 2 reduction x.toPoly y.toPoly)

/-- Simp lemmas to expose ℚ arithmetic inside QSqrt2. -/
@[simp] theorem add_a (x y : QSqrt2) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : QSqrt2) : (x + y).b = x.b + y.b := rfl
@[simp] theorem zero_a : (0 : QSqrt2).a = 0 := rfl
@[simp] theorem zero_b : (0 : QSqrt2).b = 0 := rfl

/-- AddCommMonoid instance — needed for Finset.sum in pentagon equation. -/
instance : AddCommMonoid QSqrt2 where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  nsmul := nsmulRec

/-- Key values for Ising F-symbols. -/
def sqrt2_inv : QSqrt2 := ⟨0, 1/2⟩       -- 1/√2 = √2/2 = 0 + (1/2)√2
def neg_sqrt2_inv : QSqrt2 := ⟨0, -1/2⟩   -- -1/√2
def neg_one : QSqrt2 := ⟨-1, 0⟩           -- -1

/-- Verify: (1/√2)² = 1/2. -/
theorem sqrt2_inv_sq : sqrt2_inv * sqrt2_inv = ⟨1/2, 0⟩ := by native_decide

/-- Verify: (1/√2)·(1/√2) + (1/√2)·(1/√2) = 1. (Row orthogonality) -/
theorem hadamard_row_norm :
    sqrt2_inv * sqrt2_inv + sqrt2_inv * sqrt2_inv = 1 := by native_decide

/-- Verify: (1/√2)·(1/√2) + (1/√2)·(-1/√2) = 0. (Row orthogonality) -/
theorem hadamard_row_ortho :
    sqrt2_inv * sqrt2_inv + sqrt2_inv * neg_sqrt2_inv = 0 := by native_decide

end QSqrt2

end SKEFTHawking
