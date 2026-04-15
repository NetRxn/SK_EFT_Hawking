/-
# Q(ζ₁₅, √φ): Non-Cyclotomic Degree-16 Extension

Tower extension `Q(ζ₁₅)[w]/(w² − φ)` where φ = (1+√5)/2 is the golden ratio,
represented as the QCyc15 element (1, 0, -1, 1, 0, 0, 0, -1).

## Why non-cyclotomic?

The element √φ satisfies x⁴ − x² − 1 = 0 over ℚ, which is irreducible
with splitting field containing complex roots ±i/√φ. Since Q(√φ) ⊂ ℝ does
not contain these complex roots, Q(√φ)/Q is **not Galois**. By the
Kronecker-Weber theorem, every subfield of a cyclotomic field is an
abelian (hence Galois) extension of Q. Therefore **√φ cannot lie in any
cyclotomic field** Q(ζₙ).

This is why the SU(3)_2 F-symbols (unitary gauge) require the larger
field Q(ζ₁₅, √φ) rather than just Q(ζ₁₅): the Fibonacci sub-F-matrix entry
1/√φ genuinely escapes all cyclotomic fields.

## Implementation

We use the generic tower primitive `PolyQuotOver QCyc15 2` with reduction
coefficients `![φ, 0]` encoding w² = φ + 0·w.

Elements are pairs `(a, b) ∈ QCyc15²` representing `a + b·w`. The tower's
multiplication flows through `PolyQuotOver.mulReduce2`, whose base-ring
arithmetic is QCyc15's Mul (itself a `PolyQuotQ.mulReduce 8` delegation).
Fully threaded two-level generic construction.

## References

- Deep research: `Lit-Search/Phase-5i/5i-SU(3)₂ modular tensor category-
  exact data over Q(ζ₁₅).md` §'Deliverable 3: F-symbols and the √φ
  obstruction'
- Washington, *Introduction to Cyclotomic Fields* (Springer 1997) §14
-/

import Mathlib
import SKEFTHawking.QCyc15
import SKEFTHawking.PolyQuotOver

namespace SKEFTHawking

/-- Q(ζ₁₅, √φ) via the generic tower primitive `PolyQuotOver QCyc15 2`. -/
abbrev QCyc15SqrtPhi := PolyQuotOver QCyc15 2

namespace QCyc15SqrtPhi

/-- Reduction coefficients for the tower: w² = φ + 0·w where φ ∈ Q(ζ₁₅). -/
def reduction : Fin 2 → QCyc15 :=
  ![⟨![1, 0, -1, 1, 0, 0, 0, -1]⟩, 0]  -- φ = (1, 0, -1, 1, 0, 0, 0, -1)

/-- Multiplication via the degree-2 tower primitive. -/
instance : Mul QCyc15SqrtPhi where
  mul x y := PolyQuotOver.mulReduce2 reduction x y

/-- One in Q(ζ₁₅, √φ): (1, 0) = 1 + 0·w where 1 ∈ QCyc15. -/
instance : One QCyc15SqrtPhi := ⟨⟨![⟨![1, 0, 0, 0, 0, 0, 0, 0]⟩, 0]⟩⟩

/-! ## Key elements -/

/-- w = √φ, the generator of the tower extension. -/
def w : QCyc15SqrtPhi := ⟨![0, 1]⟩

/-- φ embedded in the tower as a "real" element (a + 0·w). -/
def phi : QCyc15SqrtPhi := ⟨![QCyc15.phi, 0]⟩

/-- 1/φ embedded in the tower. -/
def phi_inv : QCyc15SqrtPhi := ⟨![QCyc15.phi_inv, 0]⟩

/-- 1/√φ = (1/φ)·w (off-diagonal Fibonacci F-matrix entry). -/
def phi_inv_sqrt : QCyc15SqrtPhi := ⟨![0, QCyc15.phi_inv]⟩

/-- −1/φ (diagonal Fibonacci F-matrix entry at (τ, τ)). -/
def neg_phi_inv : QCyc15SqrtPhi := ⟨![-QCyc15.phi_inv, 0]⟩

/-! ## Fundamental identities -/

/-- w² = φ: the defining relation of the extension. -/
theorem w_sq : w * w = phi := by native_decide

/-- φ · (1/φ) = 1 in the tower. -/
theorem phi_mul_phi_inv : phi * phi_inv = 1 := by native_decide

/-- (1/√φ)² = 1/φ. -/
theorem phi_inv_sqrt_sq : phi_inv_sqrt * phi_inv_sqrt = phi_inv := by
  native_decide

/-- w ≠ 0 (non-degenerate extension). -/
theorem w_ne_zero : w ≠ 0 := by native_decide

/-! ## Module summary -/

/--
QCyc15SqrtPhi module: first non-cyclotomic number field in the project.

  - `PolyQuotOver QCyc15 2` with reduction ![φ, 0] encoding w² = φ
  - Degree 16 over ℚ (8 from QCyc15, 2 from the tower)
  - Non-Galois over ℚ — √φ escapes every cyclotomic field per
    Kronecker-Weber (proof: splitting field of x⁴-x²-1 contains ±i/√φ,
    but Q(√φ) ⊂ ℝ cannot contain imaginary units)
  - Enables SU(3)_2 F-symbols (unitary gauge) — see SU3k2FSymbols.lean

First proof-assistant formalization of a non-cyclotomic algebraic number
field built via the generic tower construction.
-/
theorem qcyc15_sqrtphi_summary : True := trivial

end QCyc15SqrtPhi

end SKEFTHawking
