import Mathlib

/-!
# Q(√2): Rationals Extended by √2

Arithmetic type for F-symbol verification in the Ising MTC.
Elements are a + b√2 with a, b ∈ ℚ, equipped with DecidableEq
for native_decide verification of pentagon equations.

This is a quadratic number field — all arithmetic is exact.
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

/-- Multiplication: (a₁+b₁√2)(a₂+b₂√2) = (a₁a₂+2b₁b₂) + (a₁b₂+b₁a₂)√2. -/
instance : Mul QSqrt2 where
  mul x y := ⟨x.a * y.a + 2 * x.b * y.b,
              x.a * y.b + x.b * y.a⟩

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
