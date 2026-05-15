import Mathlib
import SKEFTHawking.PolyQuotQ

/-!
# Q(ζ₅): 5th Cyclotomic Field

Arithmetic type for R-matrix verification in the Fibonacci MTC.
Elements are a₀ + a₁ζ + a₂ζ² + a₃ζ³ with aᵢ ∈ ℚ,
where ζ = ζ₅ = e^{2πi/5} satisfies ζ⁴ + ζ³ + ζ² + ζ + 1 = 0.

Degree 4 over Q. Contains Q(√5) as the real subfield:
  √5 = 2ζ² + 2ζ + 1 = 1 + 2ζ + 2ζ²

Reduction rule: ζ⁴ = -1 - ζ - ζ² - ζ³

## Key values for Fibonacci braiding
  R₁ = ζ³ = e^{-4πi/5}       (vacuum channel R-eigenvalue)
  Rτ = -ζ⁴ = 1+ζ+ζ²+ζ³      (τ-channel R-eigenvalue, = -ζ⁴)
  θτ = ζ² = e^{4πi/5}        (topological twist)
  φ⁻¹ = ζ + ζ⁴ = ζ - 1 - ζ - ζ² - ζ³ = -1 - ζ² - ζ³  (inverse golden ratio)

## References
- Deep research: Phase-5e/Complete braiding data for the Fibonacci MTC
- Rowell, Stong, Wang, Comm. Math. Phys. 292, 343 (2009)
-/

namespace SKEFTHawking

/-- Elements of Q(ζ₅) = Q[x]/(x⁴+x³+x²+x+1).
    Coefficients for 1, ζ, ζ², ζ³. Reduction: ζ⁴ = -1-ζ-ζ²-ζ³. -/
@[ext]
structure QCyc5 where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  deriving DecidableEq, Repr

namespace QCyc5

instance : Zero QCyc5 := ⟨0, 0, 0, 0⟩
instance : One QCyc5 := ⟨1, 0, 0, 0⟩

instance : Neg QCyc5 where
  neg x := ⟨-x.c0, -x.c1, -x.c2, -x.c3⟩

instance : Add QCyc5 where
  add x y := ⟨x.c0+y.c0, x.c1+y.c1, x.c2+y.c2, x.c3+y.c3⟩

instance : Sub QCyc5 where
  sub x y := ⟨x.c0-y.c0, x.c1-y.c1, x.c2-y.c2, x.c3-y.c3⟩

/-- Reduction coefficients for Q(ζ₅): x⁴ = -1 - x - x² - x³.

Phase 5i Wave 4b refactor (2026-04-15): Mul now delegates to
`PolyQuotQ.mulReduce 4 reduction` via toPoly/ofPoly coercions.
Struct API and all Fibonacci MTC / hexagon / trefoil call sites preserved. -/
def reduction : Fin 4 → ℚ := ![-1, -1, -1, -1]

/-- Coerce QCyc5 ↔ PolyQuotQ 4 for the generic multiplication bridge. -/
def toPoly (x : QCyc5) : PolyQuotQ 4 := ⟨![x.c0, x.c1, x.c2, x.c3]⟩
def ofPoly (p : PolyQuotQ 4) : QCyc5 :=
  ⟨p.coeffs 0, p.coeffs 1, p.coeffs 2, p.coeffs 3⟩

/-- Multiplication mod ζ⁴ = -1 - ζ - ζ² - ζ³, via the generic mulReduce. -/
instance : Mul QCyc5 where
  mul x y := ofPoly (PolyQuotQ.mulReduce 4 reduction x.toPoly y.toPoly)

/-! ## Key Constants -/

/-- ζ₅ = e^{2πi/5}. -/
def zeta : QCyc5 := ⟨0, 1, 0, 0⟩

/-- R₁ = ζ³ = e^{-4πi/5} (Fibonacci R-matrix vacuum channel). -/
def R1 : QCyc5 := ⟨0, 0, 0, 1⟩

/-- Rτ = -ζ⁴ = 1+ζ+ζ²+ζ³ (Fibonacci R-matrix τ-channel). -/
def Rtau : QCyc5 := ⟨1, 1, 1, 1⟩

/-- θτ = ζ² = e^{4πi/5} (topological twist for τ). -/
def theta_tau : QCyc5 := ⟨0, 0, 1, 0⟩

/-- φ⁻¹ = (√5-1)/2 = ζ + ζ⁴ = -1 - ζ² - ζ³ (inverse golden ratio in Q(ζ₅)). -/
def phi_inv : QCyc5 := ⟨-1, 0, -1, -1⟩

/-! ## Fundamental Identities -/

/-- ζ⁵ = 1: primitive 5th root. -/
theorem zeta5_one :
    let z2 := zeta * zeta
    let z4 := z2 * z2
    z4 * zeta = 1 := by native_decide

/-- ζ⁴ + ζ³ + ζ² + ζ + 1 = 0: cyclotomic relation. -/
theorem cyclotomic_relation :
    let z2 := zeta * zeta
    let z3 := z2 * zeta
    let z4 := z3 * zeta
    z4 + z3 + z2 + zeta + 1 = 0 := by native_decide

/-- R₁ = Rτ²: the critical identity connecting R-eigenvalues. -/
theorem R1_eq_Rtau_sq : Rtau * Rtau = R1 := by native_decide

/-! ## Hexagon Equations (E1, E2, E3) -/

/-- **E1:** R₁² = φ⁻¹ + Rτ. -/
theorem hexagon_E1 : R1 * R1 = phi_inv + Rtau := by native_decide

/-- **E2:** R₁ · Rτ = φ⁻¹ · (1 - Rτ). -/
theorem hexagon_E2 : R1 * Rtau = phi_inv * (1 - Rtau) := by native_decide

/-- **E3:** Rτ² + φ⁻¹ · Rτ + 1 = 0. -/
theorem hexagon_E3 : Rtau * Rtau + phi_inv * Rtau + 1 = 0 := by native_decide

/-! ## Twist and Gauss Sum -/

/-- θτ = (Rτ)⁻² = Rτ⁻², verified as θτ · Rτ² = 1.
    Since Rτ² = R₁ (proved above), this is θτ · R₁ = 1. -/
theorem twist_from_R : theta_tau * R1 = 1 := by native_decide

/-- Writhe-removal: θτ = (R₁ + φ·Rτ)/φ, equivalently φ·θτ = R₁ + φ·Rτ.
    Using φ = 1 + φ⁻¹ (in Q(ζ₅): φ = -ζ²-ζ³): check θτ·φ = R₁ + (1+phi_inv)*Rtau -/
theorem writhe_removal :
    let phi := (1 : QCyc5) + phi_inv
    theta_tau * phi = R1 + phi * Rtau := by native_decide

/-! ## Fibonacci Trefoil Knot Invariant

The right-handed trefoil = closure of σ₁³ (writhe w=3).
For τ-colored 2-strand braids:
  tr_q(R³) = d₁·R₁³ + dτ·Rτ³
where d₁=1, dτ=φ (golden ratio).
Normalize by dτ and writhe-correct by θτ^{-3}.
-/

/-- φ = (1+√5)/2 = 1 + φ⁻¹ = -ζ²-ζ³ in Q(ζ₅). -/
def phi : QCyc5 := (1 : QCyc5) + phi_inv

/-- φ is the golden ratio: φ² = φ + 1. -/
theorem phi_golden : phi * phi = phi + 1 := by native_decide

/-- R₁³ = ζ⁹ = ζ⁴ (since ζ⁵=1). -/
theorem R1_cubed : R1 * R1 * R1 = ⟨-1, -1, -1, -1⟩ := by native_decide

/-- Rτ³ = (-ζ⁴)³ = -ζ¹² = -ζ². -/
theorem Rtau_cubed : Rtau * Rtau * Rtau = ⟨0, 0, -1, 0⟩ := by native_decide

/-- Quantum trace: d₁·R₁³ + dτ·Rτ³ = R₁³ + φ·Rτ³. -/
def fib_quantum_trace_R3 : QCyc5 := R1 * R1 * R1 + phi * (Rtau * Rtau * Rtau)

/-- θτ⁻¹ = ζ⁻² = ζ³ (since ζ⁵=1). -/
def theta_tau_inv : QCyc5 := ⟨0, 0, 0, 1⟩

/-- θτ · θτ⁻¹ = 1. -/
theorem theta_inv_check : theta_tau * theta_tau_inv = 1 := by native_decide

/-- θτ⁻³ = ζ⁻⁶ = ζ⁴ (since -6 ≡ 4 mod 5)... actually ζ⁻⁶ = ζ⁻¹ = ζ⁴. -/
theorem theta_inv_cubed :
    theta_tau_inv * theta_tau_inv * theta_tau_inv = ⟨-1, -1, -1, -1⟩ := by native_decide

/-- **Fibonacci trefoil (unnormalized):** θτ⁻³ · tr_q(R³). -/
def fib_trefoil_unnorm : QCyc5 :=
  theta_tau_inv * theta_tau_inv * theta_tau_inv * fib_quantum_trace_R3

/-- The Fibonacci trefoil unnormalized = φ · (some value).
    We need to check: θτ⁻³·(R₁³ + φ·Rτ³)/dτ = RT(trefoil).
    Since dτ = φ, the normalized result is fib_trefoil_unnorm / φ.
    **Fibonacci trefoil (unnormalized) = (-1,-1,-1,1) in Q(ζ₅).** -/
theorem fib_trefoil_value :
    fib_trefoil_unnorm = ⟨-1, -1, -1, 1⟩ := by native_decide

/-- Hopf link from Fibonacci: tr_q(R²)/dτ where R² = diag(R₁², Rτ²).
    tr_q(R²) = R₁² + φ·Rτ² = R₁² + φ·R₁ (since Rτ²=R₁).
    = R₁(1+φ) = R₁·(φ+1) = R₁·φ² -/
def fib_hopf_trace : QCyc5 := R1 * R1 + phi * (Rtau * Rtau)

/-- **Fibonacci Hopf link quantum trace = -1.** This is the scalar -1 in Q(ζ₅).
    Matches S_{ττ}/S_{0τ} = (S_{02}²)/(S_{00}·S_{02}) computed from the S-matrix. -/
theorem fib_hopf_value : fib_hopf_trace = ⟨-1, 0, 0, 0⟩ := by native_decide

/-! ## Component projection simp lemmas

These `rfl`-lemmas tag the field-projection equalities so that `simp`
reduces e.g. `(x + y).c0` to `x.c0 + y.c0`. They are the foundation for
the `AddCommGroup` instance below and any downstream abstract-algebra
reasoning. -/

@[simp] theorem add_c0 (x y : QCyc5) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 (x y : QCyc5) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem add_c2 (x y : QCyc5) : (x + y).c2 = x.c2 + y.c2 := rfl
@[simp] theorem add_c3 (x y : QCyc5) : (x + y).c3 = x.c3 + y.c3 := rfl
@[simp] theorem sub_c0 (x y : QCyc5) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 (x y : QCyc5) : (x - y).c1 = x.c1 - y.c1 := rfl
@[simp] theorem sub_c2 (x y : QCyc5) : (x - y).c2 = x.c2 - y.c2 := rfl
@[simp] theorem sub_c3 (x y : QCyc5) : (x - y).c3 = x.c3 - y.c3 := rfl
@[simp] theorem neg_c0 (x : QCyc5) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 (x : QCyc5) : (-x).c1 = -x.c1 := rfl
@[simp] theorem neg_c2 (x : QCyc5) : (-x).c2 = -x.c2 := rfl
@[simp] theorem neg_c3 (x : QCyc5) : (-x).c3 = -x.c3 := rfl
@[simp] theorem zero_c0 : (0 : QCyc5).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : QCyc5).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : QCyc5).c2 = 0 := rfl
@[simp] theorem zero_c3 : (0 : QCyc5).c3 = 0 := rfl

/-! ## Additive commutative group structure

`QCyc5 ≃ ℚ⁴` as an additive group, so `AddCommGroup` lifts pointwise
from ℚ via the four-component projection. All axioms reduce to the
corresponding ℚ axioms (one per component) through `ext + simp + ring`.

This instance does NOT register a `Ring`/`CommRing` structure — the
multiplication `(· * ·)` on `QCyc5` delegates to
`PolyQuotQ.mulReduce 4 reduction` whose `Array.ofFn` + bang-indexed
power-table representation is intentionally opaque to symbolic
simp/decide reasoning (the design enables `native_decide` evaluation at
the cost of abstract-algebra integration). See
`docs/adrs/ADR-001-commring-qcyc5ext-roadmap.md` for the discharge plan
and the multi-PR path to a full `CommRing` instance.

Downstream consumers gain immediate access to:
- `Mathlib.Algebra.AddTorsor` machinery
- `Pi`-type `AddCommGroup` for `Fin n → QCyc5` (e.g., coefficient vectors)
- `Finsupp` and free-module constructions over `QCyc5`. -/
instance instAddCommGroup : AddCommGroup QCyc5 where
  add := (· + ·)
  zero := 0
  neg x := -x
  sub := (· - ·)
  nsmul n x := ⟨n • x.c0, n • x.c1, n • x.c2, n • x.c3⟩
  zsmul n x := ⟨n • x.c0, n • x.c1, n • x.c2, n • x.c3⟩
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  nsmul_zero a := by ext <;> simp
  nsmul_succ n a := by ext <;> (show (n+1) • _ = n • _ + _; rw [succ_nsmul])
  zsmul_zero' a := by ext <;> simp
  zsmul_succ' n a := by
    ext <;> (
      show (Int.ofNat n + 1) • _ = _
      rw [add_smul, one_smul]; simp)
  zsmul_neg' n a := by
    ext <;> (
      show Int.negSucc n • _ = _
      simp [Int.negSucc_eq]; ring)

/-- `n • x` projects component-wise (ℕ scalar action). -/
@[simp] theorem nsmul_c0 (n : ℕ) (x : QCyc5) : (n • x).c0 = n • x.c0 := rfl
@[simp] theorem nsmul_c1 (n : ℕ) (x : QCyc5) : (n • x).c1 = n • x.c1 := rfl
@[simp] theorem nsmul_c2 (n : ℕ) (x : QCyc5) : (n • x).c2 = n • x.c2 := rfl
@[simp] theorem nsmul_c3 (n : ℕ) (x : QCyc5) : (n • x).c3 = n • x.c3 := rfl
/-- `n • x` projects component-wise (ℤ scalar action). -/
@[simp] theorem zsmul_c0 (n : ℤ) (x : QCyc5) : (n • x).c0 = n • x.c0 := rfl
@[simp] theorem zsmul_c1 (n : ℤ) (x : QCyc5) : (n • x).c1 = n • x.c1 := rfl
@[simp] theorem zsmul_c2 (n : ℤ) (x : QCyc5) : (n • x).c2 = n • x.c2 := rfl
@[simp] theorem zsmul_c3 (n : ℤ) (x : QCyc5) : (n • x).c3 = n • x.c3 := rfl

/-! ## Module Summary -/

/-! ## Module summary

QCyc5 module: Q(ζ₅) for Fibonacci braiding.
  - All arithmetic exact over Q⁴ with DecidableEq
  - **`AddCommGroup QCyc5`** registered (pointwise lift from ℚ⁴)
  - Component projection simp lemmas for `+`, `-`, `neg`, `0`, `n•`
  - ζ⁵ = 1 PROVED (native_decide)
  - Cyclotomic relation PROVED
  - R₁ = Rτ² PROVED, hexagon E1/E2/E3 ALL PROVED
  - Twist consistency PROVED
  - **Fibonacci trefoil: PROVED** (native_decide)
  - **Fibonacci Hopf link: PROVED** (native_decide)
  - φ² = φ+1 PROVED (golden ratio)
  - Zero sorry, zero axioms.

  CommRing is intentionally NOT registered — the `mulReduce` machinery
  is opaque to symbolic simp/decide, blocking the conventional
  `ext + ring` discharge of `mul_assoc` / distributivity. See
  `docs/adrs/ADR-001-commring-qcyc5ext-roadmap.md`.
-/
end QCyc5

end SKEFTHawking
