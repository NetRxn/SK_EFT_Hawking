import Mathlib

/-!
# Q(√5): Rationals Extended by √5

Arithmetic type for F-symbol verification in the Fibonacci MTC.
Elements are a + b√5 with a, b ∈ ℚ, equipped with DecidableEq
for native_decide verification of pentagon equations.

Key values:
  φ = (1+√5)/2 = (1/2, 1/2)     — golden ratio
  φ⁻¹ = (√5-1)/2 = (-1/2, 1/2)  — inverse golden ratio
  -φ⁻¹ = (1-√5)/2 = (1/2, -1/2)
-/

namespace SKEFTHawking

/-- Elements of Q(√5) = {a + b√5 : a, b ∈ ℚ}. -/
structure QSqrt5 where
  a : ℚ
  b : ℚ
  deriving DecidableEq, Repr

namespace QSqrt5

instance : Zero QSqrt5 := ⟨⟨0, 0⟩⟩
instance : One QSqrt5 := ⟨⟨1, 0⟩⟩

instance : Neg QSqrt5 where
  neg x := ⟨-x.a, -x.b⟩

instance : Add QSqrt5 where
  add x y := ⟨x.a + y.a, x.b + y.b⟩

instance : Sub QSqrt5 where
  sub x y := ⟨x.a - y.a, x.b - y.b⟩

/-- Multiplication: (a₁+b₁√5)(a₂+b₂√5) = (a₁a₂+5b₁b₂) + (a₁b₂+b₁a₂)√5. -/
instance : Mul QSqrt5 where
  mul x y := ⟨x.a * y.a + 5 * x.b * y.b,
              x.a * y.b + x.b * y.a⟩

/-- Golden ratio φ = (1+√5)/2. -/
def phi : QSqrt5 := ⟨1/2, 1/2⟩

/-- Inverse golden ratio φ⁻¹ = (√5-1)/2. -/
def phi_inv : QSqrt5 := ⟨-1/2, 1/2⟩

/-- Negative inverse golden ratio -φ⁻¹ = (1-√5)/2. -/
def neg_phi_inv : QSqrt5 := ⟨1/2, -1/2⟩

/-- φ · φ⁻¹ = 1. -/
theorem phi_mul_phi_inv : phi * phi_inv = 1 := by native_decide

/-- φ² = φ + 1 (defining relation of the golden ratio). -/
theorem phi_sq : phi * phi = phi + 1 := by native_decide

/-- (φ⁻¹)² = 1 - φ⁻¹ (equiv: (φ⁻¹)² + φ⁻¹ = 1). -/
theorem phi_inv_sq : phi_inv * phi_inv = 1 - phi_inv := by native_decide

/- Fibonacci F-matrix (isotopy gauge):
   F^τ_{τττ} = [[φ⁻¹, φ⁻¹], [1, -φ⁻¹]]
   F² = I verified entry by entry. -/

/-- F²(0,0): φ⁻¹·φ⁻¹ + φ⁻¹·1 = 1. Uses (φ⁻¹)² = 1-φ⁻¹. -/
theorem fib_F_involutory_00 :
    phi_inv * phi_inv + phi_inv * 1 = 1 := by native_decide

/-- F²(0,1): φ⁻¹·φ⁻¹ + φ⁻¹·(-φ⁻¹) = 0. -/
theorem fib_F_involutory_01 :
    phi_inv * phi_inv + phi_inv * neg_phi_inv = 0 := by native_decide

/-- F²(1,0): 1·φ⁻¹ + (-φ⁻¹)·1 = 0. -/
theorem fib_F_involutory_10 :
    1 * phi_inv + neg_phi_inv * 1 = 0 := by native_decide

/-- F²(1,1): 1·φ⁻¹ + (-φ⁻¹)·(-φ⁻¹) = 1. -/
theorem fib_F_involutory_11 :
    1 * phi_inv + neg_phi_inv * neg_phi_inv = 1 := by native_decide

end QSqrt5

end SKEFTHawking
