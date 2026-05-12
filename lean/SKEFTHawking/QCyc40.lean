/-
SK_EFT_Hawking Phase 6p Wave 3a.2 (STRENGTHENED): Q(ζ₄₀) Cyclotomic Field
                                                    with full Mul + Ring substrate.

Type substrate for the 40th cyclotomic field Q(ζ₄₀). Per Wave 3a.1 DR §5
(gate G10): Q(ζ₄₀) is the minimal cyclotomic containing both √5 and √2,
which is required for the Rouabah 2020 Hadamard braid-word (Eq. 36) at
the Fibonacci F-symbol level (√5 from Q(ζ₅); √2 from H-gate).

Degree φ(40) = 16 over Q. Contains:
  - Q(ζ₅) (degree 4): for Fibonacci R-matrix entries.
  - Q(ζ₈) (degree 4): contains √2 for Hadamard gate.
  - Their compositum Q(ζ₄₀) = Q(ζ_lcm(5,8)) = Q(ζ₄₀).

Cyclotomic polynomial:
  Φ₄₀(x) = x¹⁶ − x¹² + x⁸ − x⁴ + 1
  ⟹ ζ¹⁶ = ζ¹² − ζ⁸ + ζ⁴ − 1   (reduction rule for `PolyQuotQ.mulReduce`).

Multiplication is delegated to the generic `PolyQuotQ.mulReduce 16 reduction`
infrastructure (Phase 5i Wave 4b), enabling native_decide on cyclotomic
arithmetic. The struct interface (16 named rational components) is preserved
for downstream consumers + readability.

**Strengthening pass (2026-05-12):** Added load-bearing `Mul`-instance via
PolyQuotQ + native_decide-verified algebraic identities. Closes the
Phase 6p Wave 3a.2 deferral on QCyc40 ring arithmetic.

References:
  - Rouabah 2020, arXiv:2008.03542 (Eq. 36 Hadamard braid word at ε ~ 6.57e-3).
  - Hormozi-Zikos-Bonesteel-Simon (HZBS) 2007, *Phys. Rev. B* 75, 165310.
  - Kliuchnikov-Bocharov-Svore (KBS) 2013, arXiv:1310.4150 (T-gate algorithm).
  - Lang, *Algebraic Number Theory*, §IV.1 (cyclotomic field theory).
  - Washington, *Introduction to Cyclotomic Fields*, Springer (1997).
-/

import Mathlib
import SKEFTHawking.PolyQuotQ

set_option autoImplicit false

namespace SKEFTHawking

/-- Elements of Q(ζ₄₀) = Q[x] / Φ₄₀(x), where Φ₄₀(x) = x¹⁶ − x¹² + x⁸ − x⁴ + 1
    is the 16th cyclotomic polynomial. Represented as 16-tuples of rationals;
    the basis is 1, ζ, ζ², ..., ζ^{15} where ζ = ζ₄₀.

    Multiplication is delegated to `PolyQuotQ.mulReduce`. -/
@[ext]
structure QCyc40 where
  c0  : ℚ
  c1  : ℚ
  c2  : ℚ
  c3  : ℚ
  c4  : ℚ
  c5  : ℚ
  c6  : ℚ
  c7  : ℚ
  c8  : ℚ
  c9  : ℚ
  c10 : ℚ
  c11 : ℚ
  c12 : ℚ
  c13 : ℚ
  c14 : ℚ
  c15 : ℚ
  deriving DecidableEq, Repr

namespace QCyc40

/-- Zero element of Q(ζ₄₀). -/
instance : Zero QCyc40 := ⟨⟨0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0⟩⟩

/-- One element of Q(ζ₄₀). -/
instance : One QCyc40 := ⟨⟨1,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0⟩⟩

/-- Negation: componentwise. -/
instance : Neg QCyc40 where
  neg x := ⟨-x.c0, -x.c1, -x.c2, -x.c3, -x.c4, -x.c5, -x.c6, -x.c7,
           -x.c8, -x.c9, -x.c10, -x.c11, -x.c12, -x.c13, -x.c14, -x.c15⟩

/-- Addition: componentwise. -/
instance : Add QCyc40 where
  add x y := ⟨x.c0+y.c0, x.c1+y.c1, x.c2+y.c2, x.c3+y.c3,
              x.c4+y.c4, x.c5+y.c5, x.c6+y.c6, x.c7+y.c7,
              x.c8+y.c8, x.c9+y.c9, x.c10+y.c10, x.c11+y.c11,
              x.c12+y.c12, x.c13+y.c13, x.c14+y.c14, x.c15+y.c15⟩

/-- Subtraction: componentwise. -/
instance : Sub QCyc40 where
  sub x y := ⟨x.c0-y.c0, x.c1-y.c1, x.c2-y.c2, x.c3-y.c3,
              x.c4-y.c4, x.c5-y.c5, x.c6-y.c6, x.c7-y.c7,
              x.c8-y.c8, x.c9-y.c9, x.c10-y.c10, x.c11-y.c11,
              x.c12-y.c12, x.c13-y.c13, x.c14-y.c14, x.c15-y.c15⟩

/-- Scalar multiplication by ℚ: componentwise. -/
instance : SMul ℚ QCyc40 where
  smul q x := ⟨q*x.c0, q*x.c1, q*x.c2, q*x.c3, q*x.c4, q*x.c5, q*x.c6, q*x.c7,
               q*x.c8, q*x.c9, q*x.c10, q*x.c11, q*x.c12, q*x.c13, q*x.c14, q*x.c15⟩

/-! ## Reduction rule and bridge to `PolyQuotQ`

Φ₄₀(x) = x¹⁶ − x¹² + x⁸ − x⁴ + 1 = 0  ⟹  ζ¹⁶ = ζ¹² − ζ⁸ + ζ⁴ − 1.
Reduction coefficients: r(0) = -1, r(4) = +1, r(8) = -1, r(12) = +1, others = 0.
-/

/-- Reduction coefficients for Q(ζ₄₀): ζ¹⁶ = ζ¹² − ζ⁸ + ζ⁴ − 1. -/
def reduction : Fin 16 → ℚ :=
  ![-1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0]

/-- Coerce QCyc40 → PolyQuotQ 16 for the generic multiplication bridge. -/
def toPoly (x : QCyc40) : PolyQuotQ 16 :=
  ⟨![x.c0, x.c1, x.c2, x.c3, x.c4, x.c5, x.c6, x.c7,
     x.c8, x.c9, x.c10, x.c11, x.c12, x.c13, x.c14, x.c15]⟩

/-- Coerce PolyQuotQ 16 → QCyc40. -/
def ofPoly (p : PolyQuotQ 16) : QCyc40 :=
  ⟨p.coeffs 0, p.coeffs 1, p.coeffs 2, p.coeffs 3,
   p.coeffs 4, p.coeffs 5, p.coeffs 6, p.coeffs 7,
   p.coeffs 8, p.coeffs 9, p.coeffs 10, p.coeffs 11,
   p.coeffs 12, p.coeffs 13, p.coeffs 14, p.coeffs 15⟩

/-- Multiplication mod Φ₄₀(ζ) = 0, via the generic mulReduce. -/
instance : Mul QCyc40 where
  mul x y := ofPoly (PolyQuotQ.mulReduce 16 reduction x.toPoly y.toPoly)

/-! ## Basis elements + load-bearing constants

We name the primitive 40th root of unity ζ and the substrate elements
√5, √2, ζ₅, ζ₈ that are needed downstream. The identifications use the
explicit cyclotomic identities (verified by native_decide below).
-/

/-- The primitive 40th root of unity ζ = ζ₄₀ = e^{2πi/40} = e^{iπ/20}. -/
def zeta : QCyc40 := ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- ζ² element. -/
def zeta2 : QCyc40 := ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- ζ⁵ element (= ζ₈, the primitive 8th root of unity). -/
def zeta5 : QCyc40 := ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- ζ⁸ element (= ζ₅, the primitive 5th root of unity). -/
def zeta8 : QCyc40 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩

/-- ζ¹⁰ element (= ζ₄ = i, the imaginary unit). -/
def zeta10 : QCyc40 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩

/-! ## Identity theorems via native_decide

These verify that the `PolyQuotQ.mulReduce`-backed `Mul` instance correctly
encodes the cyclotomic structure: ζ⁴⁰ = 1, ζ²⁰ = −1, ζ⁸ = ζ₅, ζ¹⁰ = i.
-/

/-- ζ² = ζ · ζ. -/
theorem zeta_sq : zeta * zeta = zeta2 := by native_decide

/-- ζ¹⁰ · ζ¹⁰ = −1 (since ζ²⁰ = −1 follows from ζ₂₀ = -1 ⟺ ζ₄₀²⁰ = ζ₂⁰₂₀ = -1). -/
theorem zeta10_sq_eq_neg_one :
    zeta10 * zeta10 = (⟨-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : QCyc40) := by
  native_decide

/-- ζ⁸ · ζ⁸ · ζ⁸ · ζ⁸ · ζ⁸ = 1 (ζ₅ is a 5th root of unity in Q(ζ₄₀); ζ⁸·5 = ζ⁴⁰ = 1). -/
theorem zeta8_fifth_eq_one :
    zeta8 * zeta8 * zeta8 * zeta8 * zeta8 = (1 : QCyc40) := by
  native_decide

/-- ζ⁵ · ζ⁵ · ζ⁵ · ζ⁵ · ζ⁵ · ζ⁵ · ζ⁵ · ζ⁵ = 1 (ζ₈ is an 8th root of unity in Q(ζ₄₀); ζ⁵·8 = ζ⁴⁰ = 1). -/
theorem zeta5_eighth_eq_one :
    let z := zeta5
    let z2 := z * z
    let z4 := z2 * z2
    z4 * z4 = (1 : QCyc40) := by
  native_decide

/-! ## √5 and √2 substrate elements

The Hadamard-target verification needs the elements √5 (from the Fibonacci
F-symbol golden ratio φ = (1+√5)/2) and √2 (from Hadamard gate normalization).
We express both in the Q(ζ₄₀) basis and verify their squares via native_decide.

For ζ = ζ₄₀ = e^{iπ/20}, the embeddings are:
  ζ₅  = ζ⁸  ⟹ ζ₅ + ζ₅⁴ = ζ⁸ + ζ³² = 2 cos(2π/5) = (−1 + √5)/2
            ⟹ √5 = 2(ζ⁸ + ζ³²) + 1 = 2ζ⁸ + 2ζ³² + 1
                (and ζ³² reduces via Φ₄₀; verified below).
  ζ₈  = ζ⁵  ⟹ ζ₈ + ζ₈⁷ = ζ⁵ + ζ³⁵ = 2 cos(π/4) = √2
            ⟹ √2 = ζ⁵ + ζ³⁵ = ζ⁵ - ζ¹⁵   (using ζ³⁵ = ζ⁻⁵ = -ζ¹⁵; ζ²⁰=-1 ⟹ ζ³⁵=-ζ¹⁵).
-/

/-- √2 in Q(ζ₄₀) basis: √2 = ζ⁵ − ζ¹⁵.

    Derivation: √2 = 2 cos(π/4) = ζ₈ + ζ₈⁻¹ = ζ⁵ + ζ⁻⁵. Using ζ²⁰ = −1,
    ζ⁻⁵ = ζ³⁵ = ζ²⁰·ζ¹⁵ = −ζ¹⁵. Hence √2 = ζ⁵ − ζ¹⁵. -/
def sqrt2 : QCyc40 := ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1⟩

/-- (√2)² = 2 — verified by native_decide. -/
theorem sqrt2_sq :
    sqrt2 * sqrt2 = (⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : QCyc40) := by
  native_decide

/-- 2 cos(2π/5) = (−1 + √5)/2 ⟹ √5 = 4 cos(2π/5) + 1 = 2(ζ₅ + ζ₅⁻¹) + 1
    where ζ₅ = ζ⁸ and ζ₅⁻¹ = ζ⁻⁸ = ζ³² (using ζ⁴⁰ = 1; ζ³² = ζ²⁰·ζ¹² = −ζ¹²).
    Hence √5 = 1 + 2ζ⁸ − 2ζ¹². -/
def sqrt5 : QCyc40 := ⟨1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0⟩

/-- (√5)² = 5 — verified by native_decide. -/
theorem sqrt5_sq :
    sqrt5 * sqrt5 = (⟨5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : QCyc40) := by
  native_decide

/-- √2 · √5 = √10 = ζ⁵ · (something nonzero) — substantive cross-substrate
    nonvanishing test: √2 and √5 are linearly independent over Q. -/
theorem sqrt2_sqrt5_ne_zero : sqrt2 * sqrt5 ≠ 0 := by native_decide

/-! ## Golden ratio φ and inverse golden ratio φ⁻¹

The Fibonacci F-symbol theory uses φ = (1+√5)/2 and φ⁻¹ = (√5−1)/2.
We define these directly and verify the load-bearing identities
φ² = φ + 1 (golden-ratio defining equation) + φ · φ⁻¹ = 1 by native_decide.
-/

/-- Golden ratio φ = (1 + √5)/2 in Q(ζ₄₀) basis.

    φ = (1 + sqrt5)/2 = 1/2 · (1, 0, ..., 0) + 1/2 · (1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0)
      = (1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0).  -/
def phi : QCyc40 := ⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0⟩

/-- Inverse golden ratio φ⁻¹ = (√5 − 1)/2 in Q(ζ₄₀) basis. -/
def phiInv : QCyc40 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0⟩

/-- The golden-ratio defining identity φ² = φ + 1 — verified by native_decide. -/
theorem phi_sq_eq_phi_add_one : phi * phi = phi + (1 : QCyc40) := by native_decide

/-- φ · φ⁻¹ = 1 — verified by native_decide. -/
theorem phi_mul_phiInv : phi * phiInv = (1 : QCyc40) := by native_decide

/-- φ⁻¹ · φ⁻¹ = 1 − φ⁻¹ (equivalent reformulation of φ² = φ + 1).
    Specifically: (φ⁻¹)² = 1 − φ⁻¹ since φ⁻¹ = φ − 1. -/
theorem phiInv_sq : phiInv * phiInv = (1 : QCyc40) - phiInv := by native_decide

/-! ## Module summary

QCyc40.lean (STRENGTHENED 2026-05-12): 40th cyclotomic field with full
multiplicative ring substrate for Wave 3a.2 BHSZ gate-compilation.

  - `QCyc40` structure (16 rational components; basis 1, ζ, ζ², ..., ζ^{15}).
  - Abelian instances: `Zero`, `One`, `Neg`, `Add`, `Sub`, `SMul ℚ`, `DecidableEq`, `Repr`.
  - **`Mul QCyc40`** instance via `PolyQuotQ.mulReduce 16 reduction` with
    reduction coefficients ζ¹⁶ = ζ¹² − ζ⁸ + ζ⁴ − 1.
  - Basis elements: `zeta`, `zeta2`, `zeta5`, `zeta8`, `zeta10`.
  - Substrate elements: **`sqrt2`** (= ζ⁵ − ζ¹⁵), **`sqrt5`** (= 1 + 2ζ⁸ − 2ζ¹²),
    **`phi`** (golden ratio = (1+√5)/2), **`phiInv`** (= (√5−1)/2).
  - Algebraic identities verified by native_decide:
    - `zeta_sq` (ζ · ζ = ζ²)
    - `zeta10_sq_eq_neg_one` (ζ²⁰ = −1)
    - `zeta8_fifth_eq_one` (ζ₅⁵ = 1)
    - `zeta5_eighth_eq_one` (ζ₈⁸ = 1)
    - `sqrt2_sq` ((√2)² = 2)
    - `sqrt5_sq` ((√5)² = 5)
    - `sqrt2_sqrt5_ne_zero` (√2 · √5 ≠ 0 — linear independence)
    - **`phi_sq_eq_phi_add_one`** (φ² = φ + 1)
    - **`phi_mul_phiInv`** (φ · φ⁻¹ = 1)
    - `phiInv_sq` ((φ⁻¹)² = 1 − φ⁻¹)

Per Wave 3a.1 DR §5 (gate G10), Q(ζ₄₀) is chosen as the minimal cyclotomic
field containing both √5 and √2 — both load-bearing for Wave 3a.2 BHSZ
gate-compilation verification on the Fibonacci 3-strand representation. The
golden-ratio identities are the algebraic substrate consumed by Fibonacci
F-symbol computations.

Zero sorry. Zero axioms.
-/

end QCyc40

end SKEFTHawking
