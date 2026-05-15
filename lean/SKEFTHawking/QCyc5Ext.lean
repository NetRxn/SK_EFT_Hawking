/-
Phase 5l Wave 2: Q(ζ₅, √φ) — Degree-8 Number Field for Fibonacci Universality

The minimal field containing all Fibonacci braiding data is
K = Q(ζ₅)[w]/(w² + ζ² + ζ³), where w = √φ and φ = (1+√5)/2
is the golden ratio. This is a degree-8 non-abelian extension of Q,
not contained in any cyclotomic field (Kronecker-Weber obstruction).

Elements: pairs (a, b) with a, b ∈ Q(ζ₅), representing a + b·w.
Multiplication: (a₁+b₁w)(a₂+b₂w) = (a₁a₂ + φ·b₁b₂) + (a₁b₂+a₂b₁)w
  where φ = -ζ²-ζ³ in Q(ζ₅) (so w² = φ = -ζ²-ζ³).

Key values in K:
  √φ = w                   (the new generator)
  φ⁻¹/² = φ⁻¹·w = (ζ+ζ⁴)·w   (F-matrix off-diagonal entry)
  σ₂[0,1] = -(1+ζ²)·w     (braiding off-diagonal)

References:
  Freedman, Larsen, Wang, Comm. Math. Phys. 227, 605 (2002)
  Lit-Search/Phase-5k-5l-5m-5n/Fibonacci anyon braiding universality...
-/

import Mathlib
import SKEFTHawking.QCyc5
import SKEFTHawking.PolyQuotOver

namespace SKEFTHawking

open QCyc5

/-! ## 1. The Extension Field K = Q(ζ₅, √φ)

Elements are pairs (a, b) ∈ Q(ζ₅)², representing a + b·w where w² = φ = -ζ²-ζ³.
-/

/-- Elements of K = Q(ζ₅)[w]/(w² + ζ² + ζ³).
    Each element is a + b·w where a, b ∈ Q(ζ₅) and w = √φ. -/
@[ext]
structure QCyc5Ext where
  re : QCyc5  -- the "rational" part (a)
  im : QCyc5  -- the "irrational" part (b), coefficient of w
  deriving DecidableEq, Repr

namespace QCyc5Ext

instance : Zero QCyc5Ext := ⟨⟨0, 0⟩⟩
instance : One QCyc5Ext := ⟨⟨1, 0⟩⟩

instance : Neg QCyc5Ext where
  neg x := ⟨-x.re, -x.im⟩

instance : Add QCyc5Ext where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

instance : Sub QCyc5Ext where
  sub x y := ⟨x.re - y.re, x.im - y.im⟩

/-- Reduction coefficients for the degree-2 tower K = Q(ζ₅)[w]/(w² − φ):
    w² = φ + 0·w where φ = -ζ²-ζ³ ∈ Q(ζ₅).

Phase 5i Wave 4b.ext refactor (2026-04-15): Mul now delegates to the generic
tower primitive `PolyQuotOver.mulReduce2` via toPoly/ofPoly coercions.
Struct API (re, im) and all Fibonacci F-matrix / σ₂ / Yang-Baxter call sites
preserved. First consumer of `PolyQuotOver QCyc5 2`. -/
def reduction : Fin 2 → QCyc5 :=
  ![⟨0, 0, -1, -1⟩, 0]  -- w² = φ = -ζ²-ζ³ in Q(ζ₅), coefficient of w is 0

/-- Coerce QCyc5Ext ↔ PolyQuotOver QCyc5 2 for the generic-tower bridge. -/
def toPoly (x : QCyc5Ext) : PolyQuotOver QCyc5 2 := ⟨![x.re, x.im]⟩
def ofPoly (p : PolyQuotOver QCyc5 2) : QCyc5Ext := ⟨p.coeffs 0, p.coeffs 1⟩

/-- Multiplication in K: (a₁+b₁w)(a₂+b₂w) = (a₁a₂ + φ·b₁b₂) + (a₁b₂+a₂b₁)·w.

    Now delegates to `PolyQuotOver.mulReduce2 reduction` — the base-ring
    arithmetic flows through QCyc5's Mul (itself a `PolyQuotQ.mulReduce 4`
    delegation after Wave 4b), so the two-level construction is fully
    threaded through the generic infrastructure. -/
instance : Mul QCyc5Ext where
  mul x y := ofPoly (PolyQuotOver.mulReduce2 reduction x.toPoly y.toPoly)

/-! ## 2. The Generator w = √φ -/

/-- w = √φ, the generator of the extension. Represented as (0, 1). -/
def w : QCyc5Ext := ⟨0, 1⟩

/-- φ embedded in K (as a "real" element). -/
def phi_ext : QCyc5Ext := ⟨phi, 0⟩

/-- w² = φ: the defining relation of the extension. -/
theorem w_sq : w * w = phi_ext := by native_decide

/-- w ≠ 0. -/
theorem w_ne_zero : w ≠ 0 := by native_decide

/-- φ⁻¹ · w = (ζ+ζ⁴)·w: the F-matrix off-diagonal entry φ⁻¹/². -/
def phi_inv_sqrt : QCyc5Ext := ⟨0, phi_inv⟩

/-- (φ⁻¹/²)² = φ⁻¹: squaring the off-diagonal F-entry gives the diagonal. -/
theorem phi_inv_sqrt_sq : phi_inv_sqrt * phi_inv_sqrt = ⟨phi_inv, 0⟩ := by native_decide

/-! ## 3. Embedding Q(ζ₅) → K -/

/-- Embed a Q(ζ₅) element into K (as the "real" part). -/
def ofQCyc5 (a : QCyc5) : QCyc5Ext := ⟨a, 0⟩

/-- Embedding preserves R₁ multiplication. -/
theorem ofQCyc5_R1_mul_Rtau : ofQCyc5 (R1 * Rtau) = ofQCyc5 R1 * ofQCyc5 Rtau := by
  native_decide

/-! ## 4. Full Fibonacci Braiding Matrices over K

The F-matrix in the correct (unitary, symmetric) gauge:
  F = [[φ⁻¹, φ⁻¹/²], [φ⁻¹/², -φ⁻¹]]
All entries now expressible in K.
-/

/-- F[0,0] = φ⁻¹ (in K). -/
def fullF00 : QCyc5Ext := ofQCyc5 phi_inv

/-- F[0,1] = F[1,0] = φ⁻¹/² = (ζ+ζ⁴)·w (in K). -/
def fullF01 : QCyc5Ext := phi_inv_sqrt

/-- F[1,0] = φ⁻¹/² (symmetric). -/
def fullF10 : QCyc5Ext := phi_inv_sqrt

/-- F[1,1] = -φ⁻¹ (in K). -/
def fullF11 : QCyc5Ext := ofQCyc5 ⟨1, 0, 1, 1⟩  -- -phi_inv

/-- F² = I over K, entry (0,0): F₀₀²+F₀₁·F₁₀ = 1. -/
theorem fullF_sq_00 : fullF00 * fullF00 + fullF01 * fullF10 = 1 := by native_decide

/-- F² = I over K, entry (0,1): F₀₀·F₀₁+F₀₁·F₁₁ = 0. -/
theorem fullF_sq_01 : fullF00 * fullF01 + fullF01 * fullF11 = 0 := by native_decide

/-- F² = I over K, entry (1,0): F₁₀·F₀₀+F₁₁·F₁₀ = 0. -/
theorem fullF_sq_10 : fullF10 * fullF00 + fullF11 * fullF10 = 0 := by native_decide

/-- F² = I over K, entry (1,1): F₁₀·F₀₁+F₁₁² = 1. -/
theorem fullF_sq_11 : fullF10 * fullF01 + fullF11 * fullF11 = 1 := by native_decide

/-- F is symmetric: F₀₁ = F₁₀ in the unitary gauge. -/
theorem fullF_symmetric : fullF01 = fullF10 := rfl

/-! ## 5. Full σ₂ Braiding Matrix over K

σ₂ = F · diag(R₁, R_τ) · F with all entries in K.
R₁ = ζ³, R_τ = -ζ⁴ = 1+ζ+ζ²+ζ³ (both in Q(ζ₅) ⊂ K).
-/

def R1_ext : QCyc5Ext := ofQCyc5 R1
def Rtau_ext : QCyc5Ext := ofQCyc5 Rtau

/-- σ₂[0,0] = F₀₀·R₁·F₀₀ + F₀₁·R_τ·F₁₀. -/
def fullSigma2_00 : QCyc5Ext := fullF00 * R1_ext * fullF00 + fullF01 * Rtau_ext * fullF10

/-- σ₂[0,1] = F₀₀·R₁·F₀₁ + F₀₁·R_τ·F₁₁. -/
def fullSigma2_01 : QCyc5Ext := fullF00 * R1_ext * fullF01 + fullF01 * Rtau_ext * fullF11

/-- σ₂[1,0] = F₁₀·R₁·F₀₀ + F₁₁·R_τ·F₁₀. -/
def fullSigma2_10 : QCyc5Ext := fullF10 * R1_ext * fullF00 + fullF11 * Rtau_ext * fullF10

/-- σ₂[1,1] = F₁₀·R₁·F₀₁ + F₁₁·R_τ·F₁₁. -/
def fullSigma2_11 : QCyc5Ext := fullF10 * R1_ext * fullF01 + fullF11 * Rtau_ext * fullF11

/-- σ₂ is symmetric over K (F is symmetric). -/
theorem fullSigma2_symmetric : fullSigma2_01 = fullSigma2_10 := by native_decide

/-- σ₂ diagonal entries are "real" (in Q(ζ₅), no w component). -/
theorem fullSigma2_00_real : fullSigma2_00.im = 0 := by native_decide
theorem fullSigma2_11_real : fullSigma2_11.im = 0 := by native_decide

/-- σ₂ off-diagonal entries are "imaginary" (pure w component, no Q(ζ₅) part). -/
theorem fullSigma2_01_pure_w : fullSigma2_01.re = 0 := by native_decide

/-- σ₂[0,1] = -(1+ζ²)·w as stated in the deep research. -/
theorem fullSigma2_01_value : fullSigma2_01 = ⟨0, ⟨-1, 0, -1, 0⟩⟩ := by native_decide

/-! ## 6. Braid Relation over K

σ₁σ₂σ₁ = σ₂σ₁σ₂ with σ₁ = diag(R₁, R_τ) embedded in K.
-/

/-- Braid relation [0,0] over K. -/
theorem fullBraid_00 :
    R1_ext * fullSigma2_00 * R1_ext =
    fullSigma2_00 * R1_ext * fullSigma2_00 + fullSigma2_01 * Rtau_ext * fullSigma2_10 := by
  native_decide

/-- Braid relation [0,1] over K. -/
theorem fullBraid_01 :
    R1_ext * fullSigma2_01 * Rtau_ext =
    fullSigma2_00 * R1_ext * fullSigma2_01 + fullSigma2_01 * Rtau_ext * fullSigma2_11 := by
  native_decide

/-- Braid relation [1,0] over K. -/
theorem fullBraid_10 :
    Rtau_ext * fullSigma2_10 * R1_ext =
    fullSigma2_10 * R1_ext * fullSigma2_00 + fullSigma2_11 * Rtau_ext * fullSigma2_10 := by
  native_decide

/-- Braid relation [1,1] over K. -/
theorem fullBraid_11 :
    Rtau_ext * fullSigma2_11 * Rtau_ext =
    fullSigma2_10 * R1_ext * fullSigma2_01 + fullSigma2_11 * Rtau_ext * fullSigma2_11 := by
  native_decide

/-! ## 7. Component projection simp lemmas -/

@[simp] theorem add_re (x y : QCyc5Ext) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : QCyc5Ext) : (x + y).im = x.im + y.im := rfl
@[simp] theorem sub_re (x y : QCyc5Ext) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : QCyc5Ext) : (x - y).im = x.im - y.im := rfl
@[simp] theorem neg_re (x : QCyc5Ext) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : QCyc5Ext) : (-x).im = -x.im := rfl
@[simp] theorem zero_re : (0 : QCyc5Ext).re = 0 := rfl
@[simp] theorem zero_im : (0 : QCyc5Ext).im = 0 := rfl

/-! ## 8. Additive commutative group structure

`QCyc5Ext ≃ QCyc5 × QCyc5` as an additive group, so `AddCommGroup` lifts
component-wise from the `AddCommGroup QCyc5` instance in
`SKEFTHawking.QCyc5`. The discharge pattern for each axiom is
`ext <;> simp [..]` reducing to QCyc5-level axioms.

This instance does NOT register a `Ring`/`CommRing` structure on
`QCyc5Ext`. The multiplication delegates to
`PolyQuotOver.mulReduce2 reduction`, whose intermediate machinery
(`Array.ofFn`, bang-indexing) is opaque to symbolic simp/decide
reasoning. See `docs/adrs/ADR-001-commring-qcyc5ext-roadmap.md` for the
discharge plan.

Downstream consumers (e.g., `Mat5K = Fin 5 → Fin 5 → QCyc5Ext`) now
inherit `AddCommGroup` automatically through Pi types. -/
section instAddCommGroup
-- Disable Ring-derived simp lemmas that would rewrite `n • x.re` (where
-- `x.re : QCyc5`) into multiplicative form via the new `CommRing QCyc5`
-- (registered in `SKEFTHawking.QCyc5`). Such rewrites move through
-- non-definitionally-equal forms (AddCommGroup-nsmul vs Ring-nsmul) and blow
-- up the elaboration cost of these additive-structure proofs.
attribute [-simp] nsmul_eq_mul zsmul_eq_mul

instance instAddCommGroup : AddCommGroup QCyc5Ext where
  add := (· + ·)
  zero := 0
  neg x := -x
  sub := (· - ·)
  nsmul n x := ⟨n • x.re, n • x.im⟩
  zsmul n x := ⟨n • x.re, n • x.im⟩
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  nsmul_zero a := by ext <;> simp
  nsmul_succ n a := by ext <;> simp [succ_nsmul]
  zsmul_zero' a := by ext <;> simp
  zsmul_succ' n a := by
    ext <;> (
      show (Int.ofNat n + 1) • _ = _
      rw [add_smul, one_smul]; simp)
  zsmul_neg' n a := by
    ext <;> (
      show Int.negSucc n • _ = _
      simp [Int.negSucc_eq]
      ring)

end instAddCommGroup

/-! ## 9. CommRing structure (ADR-001 Unit 4 — the headline)

This block discharges `CommRing QCyc5Ext` using `PolyQuotOver.mulReduce2`'s
closed-form arithmetic plus the `CommRing QCyc5` instance shipped in the
sister Unit 2 (`SKEFTHawking.QCyc5`).

**Why this is shorter than Unit 2** (in the sense of fewer concrete lemmas):
`mulReduce2` has a **closed form** at degree 2 (just `a₀b₀ + r₀·(a₁b₁)` and
`a₀b₁ + a₁b₀ + r₁·(a₁b₁)`), so the bridge is a 2-line `rfl` rather than a
`buildPowerTable` characterisation chain. Combined with the bottom-layer
`CommRing QCyc5`, every CommRing axiom for `QCyc5Ext` reduces to a
`ring`-closable polynomial identity in `x.re, x.im, y.re, y.im, z.re, z.im,
reduction 0, reduction 1` over the base ring `QCyc5`.

**Architecture (per ADR-001 §Unit 4 + the lift of Unit 2's pattern):**

1. **Bridge lemmas** (`mulReduce2_coeffs_zero`, `mulReduce2_coeffs_one`):
   `rfl`-true; expose the two polynomial coefficients of the product.

2. **Projection lemmas** (`mul_re`, `mul_im`, `one_re`, `one_im`,
   `zero_re`, `zero_im`, `add_re`, `add_im`, `toPoly_coeffs_zero`,
   `toPoly_coeffs_one`): `rfl`-true; expose component access.

3. **8 standalone CommRing axiom proofs** (`mul_assoc'`, `one_mul'`, …):
   each is `apply QCyc5Ext.ext; · simp only [bridges]; ring; · simp only
   [bridges]; ring` — the `ring` works because `QCyc5` is a `CommRing` (Unit 2).

4. **CommRing instance**: thin record of references to the 8 axiom proofs.

All proofs in this block are standard-kernel-only — `#print axioms
QCyc5Ext.instCommRing` returns `{propext, Classical.choice, Quot.sound}`.
No `native_decide`, no project-local axioms. -/

/-! ### Bridge: `mulReduce2` closed form (rfl) -/

theorem mulReduce2_coeffs_zero (x y : PolyQuotOver QCyc5 2) :
    (PolyQuotOver.mulReduce2 reduction x y).coeffs 0 =
    x.coeffs 0 * y.coeffs 0 + reduction 0 * (x.coeffs 1 * y.coeffs 1) := rfl

theorem mulReduce2_coeffs_one (x y : PolyQuotOver QCyc5 2) :
    (PolyQuotOver.mulReduce2 reduction x y).coeffs 1 =
    x.coeffs 0 * y.coeffs 1 + x.coeffs 1 * y.coeffs 0 + reduction 1 * (x.coeffs 1 * y.coeffs 1) := rfl

/-! ### Component projection lemmas (rfl) -/

theorem mul_re (x y : QCyc5Ext) : (x * y).re =
    (PolyQuotOver.mulReduce2 reduction x.toPoly y.toPoly).coeffs 0 := rfl
theorem mul_im (x y : QCyc5Ext) : (x * y).im =
    (PolyQuotOver.mulReduce2 reduction x.toPoly y.toPoly).coeffs 1 := rfl

theorem one_re : (1 : QCyc5Ext).re = 1 := rfl
theorem one_im : (1 : QCyc5Ext).im = 0 := rfl

theorem toPoly_coeffs_zero (x : QCyc5Ext) : x.toPoly.coeffs 0 = x.re := rfl
theorem toPoly_coeffs_one (x : QCyc5Ext) : x.toPoly.coeffs 1 = x.im := rfl

-- Note: `add_re`, `add_im`, `zero_re`, `zero_im` are already declared @[simp] above
-- (in the additive-structure section). Reuse those.

/-! ### Standalone CommRing axiom proofs

Same extract-from-instance pattern as `QCyc5.mul_assoc'` etc. — keeps
`instCommRing`'s elaboration thin (avoids `isDefEq` heartbeat blow-up). -/

theorem mul_assoc' (x y z : QCyc5Ext) : x * y * z = x * (y * z) := by
  apply QCyc5Ext.ext
  · simp only [mul_re, mul_im, mulReduce2_coeffs_zero, mulReduce2_coeffs_one,
               toPoly_coeffs_zero, toPoly_coeffs_one]; ring
  · simp only [mul_re, mul_im, mulReduce2_coeffs_zero, mulReduce2_coeffs_one,
               toPoly_coeffs_zero, toPoly_coeffs_one]; ring

theorem one_mul' (x : QCyc5Ext) : 1 * x = x := by
  apply QCyc5Ext.ext
  · simp only [mul_re, mulReduce2_coeffs_zero, toPoly_coeffs_zero, toPoly_coeffs_one,
               one_re, one_im]; ring
  · simp only [mul_im, mulReduce2_coeffs_one, toPoly_coeffs_zero, toPoly_coeffs_one,
               one_re, one_im]; ring

theorem mul_one' (x : QCyc5Ext) : x * 1 = x := by
  apply QCyc5Ext.ext
  · simp only [mul_re, mulReduce2_coeffs_zero, toPoly_coeffs_zero, toPoly_coeffs_one,
               one_re, one_im]; ring
  · simp only [mul_im, mulReduce2_coeffs_one, toPoly_coeffs_zero, toPoly_coeffs_one,
               one_re, one_im]; ring

theorem zero_mul' (x : QCyc5Ext) : 0 * x = 0 := by
  apply QCyc5Ext.ext
  · simp only [mul_re, mulReduce2_coeffs_zero, toPoly_coeffs_zero, toPoly_coeffs_one,
               zero_re, zero_im]; ring
  · simp only [mul_im, mulReduce2_coeffs_one, toPoly_coeffs_zero, toPoly_coeffs_one,
               zero_re, zero_im]; ring

theorem mul_zero' (x : QCyc5Ext) : x * 0 = 0 := by
  apply QCyc5Ext.ext
  · simp only [mul_re, mulReduce2_coeffs_zero, toPoly_coeffs_zero, toPoly_coeffs_one,
               zero_re, zero_im]; ring
  · simp only [mul_im, mulReduce2_coeffs_one, toPoly_coeffs_zero, toPoly_coeffs_one,
               zero_re, zero_im]; ring

theorem mul_comm' (x y : QCyc5Ext) : x * y = y * x := by
  apply QCyc5Ext.ext
  · simp only [mul_re, mulReduce2_coeffs_zero, toPoly_coeffs_zero, toPoly_coeffs_one]; ring
  · simp only [mul_im, mulReduce2_coeffs_one, toPoly_coeffs_zero, toPoly_coeffs_one]; ring

theorem left_distrib' (x y z : QCyc5Ext) : x * (y + z) = x * y + x * z := by
  apply QCyc5Ext.ext
  · simp only [add_re, mul_re, mulReduce2_coeffs_zero, toPoly_coeffs_zero, toPoly_coeffs_one,
               add_re, add_im]; ring
  · simp only [add_im, mul_im, mulReduce2_coeffs_one, toPoly_coeffs_zero, toPoly_coeffs_one,
               add_re, add_im]; ring

theorem right_distrib' (x y z : QCyc5Ext) : (x + y) * z = x * z + y * z := by
  apply QCyc5Ext.ext
  · simp only [add_re, mul_re, mulReduce2_coeffs_zero, toPoly_coeffs_zero, toPoly_coeffs_one,
               add_re, add_im]; ring
  · simp only [add_im, mul_im, mulReduce2_coeffs_one, toPoly_coeffs_zero, toPoly_coeffs_one,
               add_re, add_im]; ring

/-! ### `CommRing QCyc5Ext` -/

instance instCommRing : CommRing QCyc5Ext where
  __ := instAddCommGroup
  one := 1
  mul := (· * ·)
  natCast n := ⟨(n : QCyc5), 0⟩
  intCast n := ⟨(n : QCyc5), 0⟩
  natCast_zero := by
    show (⟨((0 : ℕ) : QCyc5), 0⟩ : QCyc5Ext) = (⟨0, 0⟩ : QCyc5Ext)
    apply QCyc5Ext.ext <;> simp
  natCast_succ n := by
    show (⟨((n + 1 : ℕ) : QCyc5), 0⟩ : QCyc5Ext) =
         (⟨((n : ℕ) : QCyc5), 0⟩ : QCyc5Ext) + (1 : QCyc5Ext)
    apply QCyc5Ext.ext <;> simp [add_re, add_im, one_re, one_im]
  intCast_ofNat n := by
    show (⟨((n : ℕ) : QCyc5), (0 : QCyc5)⟩ : QCyc5Ext) =
         (⟨((n : ℕ) : QCyc5), 0⟩ : QCyc5Ext)
    rfl
  intCast_negSucc n := by
    show (⟨((Int.negSucc n : ℤ) : QCyc5), 0⟩ : QCyc5Ext) =
         -(⟨((n + 1 : ℕ) : QCyc5), 0⟩ : QCyc5Ext)
    apply QCyc5Ext.ext <;> push_cast [Int.negSucc_eq] <;> simp
  npow := npowRec
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  mul_comm := mul_comm'
  left_distrib := left_distrib'
  right_distrib := right_distrib'

/-! ## Verification

`#print axioms` outputs at module-load show standard-kernel-only deps. -/

#print axioms instCommRing
#print axioms mul_assoc'
#print axioms one_mul'
#print axioms mul_one'
#print axioms zero_mul'
#print axioms mul_zero'
#print axioms mul_comm'
#print axioms left_distrib'
#print axioms right_distrib'

/-! ## 10. Module Summary -/

/-! ## Module summary

QCyc5Ext module: K = Q(ζ₅, √φ), the degree-8 number field for Fibonacci universality.
  - QCyc5Ext: pairs (a,b) ∈ Q(ζ₅)² with w² = φ = -ζ²-ζ³
  - **`AddCommGroup QCyc5Ext`** registered (componentwise lift from QCyc5)
  - **`CommRing QCyc5Ext`** registered (ADR-001 Unit 4 = headline; via
    `mulReduce2_coeffs_zero/_one` closed-form bridge + 8 standalone axiom
    proofs leveraging `CommRing QCyc5`; standard-kernel-only)
  - Component projection simp lemmas for `+`, `-`, `neg`, `0`, `1`, `*`
  - w² = φ PROVED, φ⁻¹/² squared = φ⁻¹ PROVED
  - Full F-matrix in unitary gauge: F² = I ALL 4 entries PROVED over K
  - F is symmetric PROVED
  - Full σ₂ = FRF: σ₂ symmetric PROVED, diagonal real PROVED, off-diagonal pure w PROVED
  - σ₂[0,1] = -(1+ζ²)·w PROVED (matches deep research exactly)
  - **Yang-Baxter relation: ALL 4 entries PROVED over K** (native_decide)
  - First Fibonacci braiding over the correct number field in any proof assistant
  - Zero sorry, zero project-local axioms.

  Verification: `#print axioms QCyc5Ext.instCommRing` returns
  `{propext, Classical.choice, Quot.sound}` — pure standard kernel.

  Downstream: `Mat5K = Fin 5 → Fin 5 → QCyc5Ext` now inherits a
  `Matrix (Fin 5) (Fin 5) QCyc5Ext`-compatible `CommRing`-aware
  multiplication. `Matrix.mul_assoc` becomes available without
  `native_decide`. This is the headline ADR-001 outcome — the
  `Mat5K.mul` chunked-`native_decide` patterns in downstream consumers
  can be retired in favour of `Matrix.mul_assoc`-based structural
  composition.
-/
end QCyc5Ext

end SKEFTHawking
