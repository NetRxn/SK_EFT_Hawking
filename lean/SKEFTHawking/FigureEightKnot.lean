import SKEFTHawking.QCyc16
import SKEFTHawking.IsingBraiding
import Mathlib

/-!
# Figure-Eight Knot Invariant from Ising MTC

## Overview

Computes the RT invariant of the figure-eight knot (4₁) from the Ising MTC
braiding data. The figure-eight is the simplest non-torus prime knot and
requires 3-strand braid representation (unlike the trefoil which only needs
2 strands).

The braid word is σ₁σ₂⁻¹σ₁σ₂⁻¹ in B₃ (writhe w = 0).
In the fusion basis {1, ψ} of σ⊗σ:
  σ₁ = R_diag = diag(R₁, Rψ)
  σ₂ = F · R_diag · F   (F is self-inverse for Ising Hadamard)
  σ₂⁻¹ = F · R_diag⁻¹ · F

All matrix arithmetic over QCyc16. Verified by native_decide.

## References

- Deep research: Phase-5f/Braid groups and RT invariants in Lean 4
- Kauffman & Lins, "Temperley-Lieb Recoupling Theory" (1994)
-/

namespace SKEFTHawking.FigureEightKnot

open IsingBraiding QCyc16

/-! ## 1. Matrix representation over QCyc16

The 2×2 matrices act on the fusion space {1, ψ} of σ⊗σ.
We represent matrices as 4-tuples (a₀₀, a₀₁, a₁₀, a₁₁).
-/

/-- 2×2 matrix over QCyc16, stored as (a₀₀, a₀₁, a₁₀, a₁₁). -/
structure Mat2 where
  a00 : QCyc16
  a01 : QCyc16
  a10 : QCyc16
  a11 : QCyc16
  deriving DecidableEq, Repr

namespace Mat2

def mul (A B : Mat2) : Mat2 :=
  ⟨A.a00 * B.a00 + A.a01 * B.a10,
   A.a00 * B.a01 + A.a01 * B.a11,
   A.a10 * B.a00 + A.a11 * B.a10,
   A.a10 * B.a01 + A.a11 * B.a11⟩

instance : Mul Mat2 := ⟨Mat2.mul⟩

/-- Trace = a₀₀ + a₁₁. -/
def tr (A : Mat2) : QCyc16 := A.a00 + A.a11

/-- Identity matrix. -/
def one : Mat2 := ⟨⟨1,0,0,0,0,0,0,0⟩, ⟨0,0,0,0,0,0,0,0⟩,
                    ⟨0,0,0,0,0,0,0,0⟩, ⟨1,0,0,0,0,0,0,0⟩⟩

end Mat2

/-! ## 2. Ising braid matrices -/

/-- σ₁ = R_diag = diag(R₁, Rψ) where R₁ = ζ⁻¹, Rψ = ζ³. -/
def sigma1 : Mat2 :=
  ⟨R1_sigma, ⟨0,0,0,0,0,0,0,0⟩, ⟨0,0,0,0,0,0,0,0⟩, Rpsi_sigma⟩

/-- σ₁⁻¹ = diag(R₁⁻¹, Rψ⁻¹) = diag(-ζ⁷... actually R₁⁻¹ = ζ, Rψ⁻¹ = ?).
    R₁ = ζ⁻¹, so R₁⁻¹ = ζ. Rψ = ζ³, so Rψ⁻¹ = ζ⁻³ = -ζ⁵. -/
def sigma1_inv : Mat2 :=
  ⟨zeta, ⟨0,0,0,0,0,0,0,0⟩, ⟨0,0,0,0,0,0,0,0⟩, ⟨0,0,0,0,0,-1,0,0⟩⟩

/-- F = (1/√2) [[1, 1], [1, -1]] (Ising Hadamard, self-inverse). -/
def F_matrix : Mat2 :=
  ⟨sqrt2_inv_cyc, sqrt2_inv_cyc, sqrt2_inv_cyc, -sqrt2_inv_cyc⟩

/-- σ₂ = F · σ₁ · F (F is self-inverse). -/
def sigma2 : Mat2 := F_matrix * sigma1 * F_matrix

/-- σ₂⁻¹ = F · σ₁⁻¹ · F. -/
def sigma2_inv : Mat2 := F_matrix * sigma1_inv * F_matrix

/-! ## 3. Verify F is self-inverse -/

/-- F² = I (Hadamard property). -/
theorem F_sq_identity : F_matrix * F_matrix = Mat2.one := by native_decide

/-! ## 4. Figure-eight knot computation

Braid word: σ₁ · σ₂⁻¹ · σ₁ · σ₂⁻¹ (writhe w = 0).
The representation matrix is the product of these four matrices.
Since writhe = 0, no twist correction needed.
RT(figure-eight, σ) = tr_q(product) / d_σ.
-/

/-- The braid word product: σ₁ · σ₂⁻¹ · σ₁ · σ₂⁻¹. -/
def figure_eight_matrix : Mat2 :=
  sigma1 * sigma2_inv * sigma1 * sigma2_inv

/-- Quantum trace: d₁·M₀₀ + dψ·M₁₁ = M₀₀ + M₁₁ (since d₁=dψ=1). -/
def figure_eight_trace : QCyc16 :=
  Mat2.tr figure_eight_matrix

/-- **Figure-eight knot quantum trace = -1.**
    The trace is the scalar -1 ∈ QCyc16.
    Normalized by d_σ = √2: RT(4₁, σ) = -1/√2.

    The figure-eight is amphichiral (equal to its mirror), so the
    invariant is real. The Jones polynomial V_{4₁}(q) = q² - q + 1 - q⁻¹ + q⁻²
    at q = i gives V(i) = -1 + (-i) + 1 - i + (-1) = -1-2i... actually
    the RT invariant from SU(2)₂ = Ising gives a specific evaluation, not
    the full Jones polynomial. -/
theorem figure_eight_trace_neg_one :
    figure_eight_trace = ⟨-1, 0, 0, 0, 0, 0, 0, 0⟩ := by native_decide

/-- The normalized RT invariant: trace / d_σ = -1/√2 = -√2/2. -/
theorem figure_eight_normalized :
    figure_eight_trace * sqrt2_inv_cyc = ⟨0, 0, -1/2, 0, 0, 0, 1/2, 0⟩ := by native_decide

/-- Verify σ₁ · σ₁⁻¹ = I (sanity check). -/
theorem sigma1_inv_check : sigma1 * sigma1_inv = Mat2.one := by native_decide

/-- Verify σ₂ · σ₂⁻¹ = I (sanity check). -/
theorem sigma2_inv_check : sigma2 * sigma2_inv = Mat2.one := by native_decide

/-! ## 5. Module Summary -/

/-! ## Module summary

FigureEightKnot: first 3-strand knot invariant from verified MTC data.
  - Mat2: 2×2 matrix type over QCyc16 with DecidableEq
  - F² = I: Hadamard self-inverse PROVED
  - σ₁·σ₁⁻¹ = I, σ₂·σ₂⁻¹ = I: inverse checks PROVED
  - **Figure-eight trace = -1: PROVED** (first 3-strand knot invariant from MTC)
  - Normalized: RT(4₁, σ) = -1/√2 PROVED
  - Zero sorry, zero axioms. All native_decide over QCyc16.
-/
end SKEFTHawking.FigureEightKnot
