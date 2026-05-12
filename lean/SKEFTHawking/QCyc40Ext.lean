/-
SK_EFT_Hawking Phase 6p Wave 3a.2.2 substrate: QCyc40Ext = Q(ζ₄₀)[w]/(w² − φ).

The minimal field containing all Fibonacci 3-strand R and F-matrix entries
(over Q(ζ₅), via ζ₅ = ζ₄₀⁸) AND the Hadamard normalization 1/√2 (in Q(ζ₈),
via ζ₈ = ζ₄₀⁵), AND the √φ entry of the F-matrix off-diagonal — the latter
of which is NOT in any cyclotomic field by Kronecker-Weber (Q(√φ)/Q is a
degree-4 non-abelian extension with Galois group D₄).

Construction: Q(ζ₄₀, √φ) = QCyc40[w]/(w² − phi), a degree-32 extension of Q
(= 16·2). Elements: pairs (re, im) ∈ QCyc40 × QCyc40 representing re + im·w
where w := √φ satisfies w² = φ = (1+√5)/2 ∈ Q(ζ₄₀).

Multiplication: (a + bw)(c + dw) = ac + adw + bcw + bdw²
                                 = (ac + bd·φ) + (ad + bc)·w.

This is parallel in form to `QCyc5Ext = Q(ζ₅)[w]/(w² − φ)` (the degree-8
field used in `FibonacciQutrit.lean` for the 3-strand qutrit representation),
but the base ring is QCyc40 instead of QCyc5 — so we natively have √2 in
the base, enabling exact-rational Hadamard-target verification.

Per Phase 6p Wave 3a.2.2 substrate scout (2026-05-12):
  - Wave 3a.2.2a (this module): QCyc40Ext substrate, ~150 LoC.
  - Wave 3a.2.2b (companion): Fibonacci 3-strand qubit-sector representation
    lift to Mat2K_40_Ext (~200 LoC).
  - Wave 3a.2.2c (verification): native_decide on `‖ρ(rouabah_hadamard) − H‖²_F ≤ ε²`
    over QCyc40Ext (~100 LoC).

**Substantive finding:** The Phase 6p Roadmap §Wave 3a.2.2a placeholder
"embed : QCyc5Ext → QCyc40 mapping ζ₅ → ζ⁸ and √φ → (1+√5)/2 = phi" is
INCORRECT — it would assert √φ = φ, which fails (φ² = φ + 1 ≠ φ unless
φ ∈ {0, 1}, neither of which holds). The correct construction is the
degree-32 extension QCyc40[w]/(w² − φ) shipped here. The Kronecker-Weber
obstruction means there is no degree-≤16 cyclotomic field containing √φ.

References:
  - Lang, *Algebraic Number Theory* §IV.1 (cyclotomic field theory).
  - Washington, *Introduction to Cyclotomic Fields* (1997) Ch. 2 (real subfields).
  - `QCyc5Ext.lean` (parallel construction over Q(ζ₅) for Fibonacci qutrit).
  - `QCyc40.lean` (the base field; provides `phi`, `phi_mul_phiInv`, `sqrt2_sq`).
-/

import Mathlib
import SKEFTHawking.QCyc40

set_option autoImplicit false

namespace SKEFTHawking

/-! ## 1. The extension field K = Q(ζ₄₀, √φ)

Elements are pairs (a, b) ∈ QCyc40² representing a + b·w where w² = φ.
The Fibonacci F-matrix off-diagonal entry φ⁻¹/² appears as the `im`
component (with coefficient `phiInv`, since (phiInv · w)² = phiInv² · phi
= phiInv · (phi · phiInv) = phiInv via phi · phiInv = 1).
-/

/-- Elements of K = Q(ζ₄₀)[w]/(w² − φ). Pairs (re, im) ∈ QCyc40 × QCyc40
    representing re + im · w where w = √φ. -/
@[ext]
structure QCyc40Ext where
  re : QCyc40
  im : QCyc40
  deriving DecidableEq, Repr

namespace QCyc40Ext

/-- Zero element. -/
instance : Zero QCyc40Ext := ⟨⟨0, 0⟩⟩

/-- One element. -/
instance : One QCyc40Ext := ⟨⟨1, 0⟩⟩

/-- Negation: componentwise. -/
instance : Neg QCyc40Ext where
  neg x := ⟨-x.re, -x.im⟩

/-- Addition: componentwise. -/
instance : Add QCyc40Ext where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

/-- Subtraction: componentwise. -/
instance : Sub QCyc40Ext where
  sub x y := ⟨x.re - y.re, x.im - y.im⟩

/-! ## 2. Multiplication using w² = φ

(a + bw)(c + dw) = ac + adw + bcw + bdw²
                 = (ac + bd · φ) + (ad + bc) · w.
-/

/-- Multiplication in K: (a + bw)(c + dw) = (ac + bd · φ) + (ad + bc) · w
    where φ is the golden ratio in QCyc40. -/
instance : Mul QCyc40Ext where
  mul x y := ⟨x.re * y.re + x.im * y.im * QCyc40.phi,
              x.re * y.im + x.im * y.re⟩

/-- Scalar multiplication by ℚ (lifted from QCyc40's ℚ-action componentwise). -/
instance : SMul ℚ QCyc40Ext where
  smul q x := ⟨q • x.re, q • x.im⟩

/-! ## 3. The generator w = √φ and substrate elements -/

/-- The generator w = √φ. -/
def w : QCyc40Ext := ⟨0, 1⟩

/-- Embed a QCyc40 element into K as the "real" part. -/
def ofQCyc40 (x : QCyc40) : QCyc40Ext := ⟨x, 0⟩

/-- The defining relation w² = φ embedded in K. -/
theorem w_sq : w * w = ofQCyc40 QCyc40.phi := by native_decide

/-- w ≠ 0. -/
theorem w_ne_zero : w ≠ 0 := by native_decide

/-- φ embedded in K (as a "real" element). -/
def phi_ext : QCyc40Ext := ofQCyc40 QCyc40.phi

/-- φ⁻¹ embedded in K. -/
def phiInv_ext : QCyc40Ext := ofQCyc40 QCyc40.phiInv

/-- The Fibonacci F-matrix off-diagonal entry φ⁻¹/² = φ⁻¹ · √φ
    (since (φ⁻¹ · √φ)² = φ⁻² · φ = φ⁻¹, matching the diagonal entry). -/
def phi_inv_sqrt : QCyc40Ext := ⟨0, QCyc40.phiInv⟩

/-- (φ⁻¹/²)² = φ⁻¹: squaring the off-diagonal F-entry gives the diagonal. -/
theorem phi_inv_sqrt_sq : phi_inv_sqrt * phi_inv_sqrt = phiInv_ext := by native_decide

/-- φ_ext · φ_ext = φ_ext + 1 (golden ratio identity lifted from QCyc40). -/
theorem phi_ext_sq_eq_phi_ext_add_one :
    phi_ext * phi_ext = phi_ext + (1 : QCyc40Ext) := by native_decide

/-- φ_ext · φInv_ext = 1 (lifted from QCyc40.phi_mul_phiInv). -/
theorem phi_ext_mul_phiInv_ext : phi_ext * phiInv_ext = (1 : QCyc40Ext) := by native_decide

/-! ## 4. Embedding QCyc40 → QCyc40Ext

The "real part" embedding x ↦ ⟨x, 0⟩ preserves 0 and 1 by definitional
unfolding. Ring-homomorphism properties (preservation of +, −, *) involve
QCyc40's non-Ring multiplicative structure and are deferred to a follow-up
substrate sub-wave; they are not load-bearing for any current consumer
(Wave 3a.2.2's Rouabah verification + Wave 3a.2.3c's T-gate target both
use `ofQCyc40` only as a data lift, not as a ring homomorphism).
-/

/-- Embedding preserves zero. -/
theorem ofQCyc40_zero : ofQCyc40 0 = (0 : QCyc40Ext) := rfl

/-- Embedding preserves one. -/
theorem ofQCyc40_one : ofQCyc40 1 = (1 : QCyc40Ext) := rfl

/-! ## 5. Hadamard target entries over QCyc40Ext

The Hadamard gate H = (1/√2) · ((1, 1), (1, -1)) has entries in Q(√2) ⊂ Q(ζ₄₀)
already. We expose them in QCyc40Ext (with `im = 0`) for the unified
Fibonacci-3-strand qubit-sector × Hadamard-target comparison over the
combined field. -/

/-- The 1/√2 element in QCyc40Ext (with im = 0). Concretely, 1/√2 = (√2)/2
    in QCyc40, lifted to QCyc40Ext via `ofQCyc40`. -/
def invSqrt2_ext : QCyc40Ext :=
  ofQCyc40 ((1/2 : ℚ) • QCyc40.sqrt2)

/-- (1/√2)² = 1/2 in QCyc40Ext (lifted from QCyc40 via sqrt2_sq). -/
theorem invSqrt2_ext_sq : invSqrt2_ext * invSqrt2_ext =
    ofQCyc40 ((1/2 : ℚ) • (1 : QCyc40)) := by
  native_decide

/-! ## 6. Module summary

QCyc40Ext.lean (Phase 6p Wave 3a.2.2a, 2026-05-12): the degree-32 number
field K = Q(ζ₄₀, √φ) for Fibonacci 3-strand qubit-sector × Hadamard
combined verification.

  - `QCyc40Ext` structure (re, im : QCyc40); pair (a, b) represents a + b·w.
  - Instances: `Zero`, `One`, `Neg`, `Add`, `Sub`, `Mul`, `SMul ℚ`, `DecidableEq`, `Repr`.
  - `w := ⟨0, 1⟩` (= √φ); `ofQCyc40 x := ⟨x, 0⟩` (real-part embedding).
  - **`w_sq : w * w = ofQCyc40 phi`** (defining relation, native_decide).
  - `w_ne_zero` (native_decide).
  - `phi_ext`, `phiInv_ext` — golden ratio + inverse embedded.
  - **`phi_inv_sqrt : QCyc40Ext`** (= ⟨0, phiInv⟩) — the F-matrix off-diagonal.
  - **`phi_inv_sqrt_sq : phi_inv_sqrt² = phiInv_ext`** (native_decide).
  - `phi_ext_sq_eq_phi_ext_add_one`, `phi_ext_mul_phiInv_ext` (lifted golden-ratio identities).
  - `ofQCyc40_zero`, `ofQCyc40_one` — preservation of 0, 1 by definitional unfolding.
  - `invSqrt2_ext` — Hadamard normalization in QCyc40Ext.
  - **`invSqrt2_ext_sq`** — (1/√2)² = 1/2 (native_decide).

Substantive content delivered:
  (a) Concrete degree-32 extension field substrate for Fibonacci F-matrix
      off-diagonal × Hadamard combined verification.
  (b) Defining relation w² = φ verified by Lean kernel (native_decide).
  (c) The Phase 6p Roadmap's INCORRECT placeholder mapping "√φ → phi" is
      corrected here: √φ is a genuine new generator, not in any cyclotomic.
  (d) Substrate ready for Wave 3a.2.2b Fibonacci 3-strand qubit-sector
      rep `fibRep3Qubit : BraidWord 3 → Mat2K_40_Ext` and
      Wave 3a.2.3c T-gate target embedding.

Zero sorry. Zero new project-local axioms.
-/

end QCyc40Ext

end SKEFTHawking
