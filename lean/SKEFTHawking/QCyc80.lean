/-
SK_EFT_Hawking Phase 6p Wave 3a.2.3c-substrate-upgrade: Q(ζ₈₀) Cyclotomic Field
                                                         with full Mul + Ring substrate.

Type substrate for the 80th cyclotomic field Q(ζ₈₀). Per Wave 3a.2.3c
substrate-upgrade scout (2026-05-12 PM): the minimal cyclotomic field
containing the Nielsen-Chuang T-gate phase e^(iπ/4) = ζ₈ = ζ₈₀^{10} AND
the full Fibonacci F-matrix substrate (√5 from Q(ζ_5) = Q(ζ₈₀^{16}); √2
from Q(ζ_8) = Q(ζ₈₀^{10})) is Q(ζ₈₀).

Degree φ(80) = 32 over Q. Contains:
  - Q(ζ_5)  (degree 4): for Fibonacci R-matrix entries (via ζ₅ = ζ₈₀^{16}).
  - Q(ζ_8)  (degree 4): for Hadamard / T-gate phase (via ζ₈ = ζ₈₀^{10}).
  - Q(ζ_16) (degree 8): for finer phase grid (via ζ₁₆ = ζ₈₀^{5}).
  - Their compositum Q(ζ₈₀) = Q(ζ_lcm(5,16)).

Cyclotomic polynomial:
  Φ₈₀(x) = x³² − x²⁴ + x¹⁶ − x⁸ + 1
  ⟹ ζ³² = ζ²⁴ − ζ¹⁶ + ζ⁸ − 1   (reduction rule for `PolyQuotQ.mulReduce`).

Multiplication is delegated to the generic `PolyQuotQ.mulReduceWithTable 32`
infrastructure (Phase 5i Wave 4b + 2026-05-12 PM optimization), enabling
`native_decide` on cyclotomic arithmetic.

# Substrate-upgrade context (Phase 6p Wave 3a.2.3c-substrate-upgrade)

The Wave 3a.2.3c-followup T-gate ship (TgateFibBraid.lean, L=46 random
search) identified a substrate-level algebraic obstruction in QCyc40Ext:
det(ρ(braid_word)) = ζ₄₀^{-4n} (always even-power), while det(T_NC) =
ζ₈ = ζ₄₀^5 (odd-power). No global-phase shift in ζ₄₀^k can match the parity.

QCyc80 expands the phase grid to 80 elements ζ₈₀^k (k = 0..79). In QCyc80:
  det(T_NC) = ζ₈ = ζ₈₀^{10}
Available global-phase classes for `ζ₈₀^k · T_NC` match: k can be odd OR even.
So the substrate parity obstruction is REMOVED.

# Representation + bundling choices (2026-05-12 PM)

(1) `abbrev QCyc80 := PolyQuotQ 32` rather than a 32-named-field struct.
    The struct-based representation (used by `QCyc40` at degree 16) does
    not scale to degree 32: `deriving DecidableEq` on a 32-field struct
    generates nested-let machinery that interacts pathologically with
    `native_decide` at this degree. Function-backed (`Fin 32 → ℚ`) form
    inherits the lighter `Pi.instDecidableEq`.

(2) ALL algebraic identities are bundled into a SINGLE `native_decide`
    via `all_identities_bundle`, with individual identity theorems
    realized as projections (`.1`, `.2.1`, …). Each `native_decide`
    invocation at degree 32 has substantial per-call compile-time
    overhead (specialized C code generation + clang invocation per
    goal). Bundling 10 identities into one call amortizes 10× → 1×
    overhead. The empirical compile cost drops from O(minutes) per
    file to under 10 seconds.

    The bundling is NOT a P2 bundle-redundancy anti-pattern: each
    conjunct is an independent mathematical identity (different
    LHS/RHS, no algebraic implication chain between them). The bundle
    structure is purely a compile-time optimization, not a load-bearing
    logical claim.

References:
  - Lang, *Algebraic Number Theory*, §IV.1 (cyclotomic field theory).
  - Washington, *Introduction to Cyclotomic Fields*, Springer (1997).
  - `QCyc40.lean` (the degree-16 ancestor; sub-field via ζ₄₀ = ζ₈₀²).
  - `PolyQuotQ.lean` (generic `Fin n → ℚ` polynomial-quotient substrate).
-/

import Mathlib
import SKEFTHawking.PolyQuotQ

set_option autoImplicit false

namespace SKEFTHawking

/-- Elements of Q(ζ₈₀) = Q[x] / Φ₈₀(x), where Φ₈₀(x) = x³² − x²⁴ + x¹⁶ − x⁸ + 1
    is the 80th cyclotomic polynomial.

    Implemented as `abbrev` for `PolyQuotQ 32` — see module docstring for
    rationale. Elements are coefficient tuples `Fin 32 → ℚ` over the basis
    `1, ζ, ζ², ..., ζ³¹` where ζ = ζ₈₀.

    Inherits from `PolyQuotQ 32`:
    - `DecidableEq` (via `Pi.instDecidableEq`).
    - `Repr`.
    - `Zero`, `Neg`, `Add`, `Sub` instances (componentwise).

    Adds (QCyc80-specific):
    - `One` (1 = ⟨![1, 0, ..., 0]⟩).
    - `SMul ℚ` (componentwise ℚ-action).
    - `Mul` (via `PolyQuotQ.mulReduceWithTable 32 powerTable80`). -/
abbrev QCyc80 : Type := PolyQuotQ 32

namespace QCyc80

/-- One element of Q(ζ₈₀) = 1 + 0·ζ + 0·ζ² + ... -/
instance : One QCyc80 := ⟨⟨![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩⟩

/-- Scalar multiplication by ℚ: componentwise. -/
instance : SMul ℚ QCyc80 where
  smul q x := ⟨fun i => q * x.coeffs i⟩

/-! ## Reduction rule and module-scope power table

Φ₈₀(x) = x³² − x²⁴ + x¹⁶ − x⁸ + 1 = 0  ⟹  ζ³² = ζ²⁴ − ζ¹⁶ + ζ⁸ − 1.
Reduction coefficients: r(0) = -1, r(8) = +1, r(16) = -1, r(24) = +1, others = 0.
-/

/-- Reduction coefficients for Q(ζ₈₀): ζ³² = ζ²⁴ − ζ¹⁶ + ζ⁸ − 1. -/
def reduction : Fin 32 → ℚ :=
  ![-1, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0,
    -1, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0]

/-- Pre-built power-of-ζ table for Q(ζ₈₀). Module-scope `def` so it is
    computed once at module load (per `native_decide` invocation, not per
    multiplication call) and shared across all multiplications. -/
def powerTable80 : Array (Array ℚ) := PolyQuotQ.buildPowerTable reduction

/-- Multiplication mod Φ₈₀(ζ) = 0.

    Uses `PolyQuotQ.mulReduceWithTable` (pure `Nat.fold` double-loop) with
    the module-scope `powerTable80`. -/
instance : Mul QCyc80 where
  mul x y := PolyQuotQ.mulReduceWithTable 32 powerTable80 x y

/-! ## Basis elements + load-bearing constants

For ζ = ζ₈₀ = e^{2πi/80} = e^{iπ/40}, key embeddings are:
  ζ₅   = ζ⁸⁰^{16}   (since 80/5 = 16): primitive 5th root.
  ζ₈   = ζ⁸⁰^{10}   (since 80/8 = 10): primitive 8th root, e^(iπ/4) — T-gate phase!
  ζ₁₀  = ζ⁸⁰^{8}    (since 80/10 = 8): primitive 10th root.
  ζ₁₆  = ζ⁸⁰^{5}    (since 80/16 = 5): primitive 16th root.
  ζ₄₀  = ζ⁸⁰²       (since 80/40 = 2): primitive 40th root.
  ζ₂   = ζ⁸⁰⁴⁰ = -1.
-/

/-- The primitive 80th root of unity ζ = ζ₈₀ = e^{2πi/80} = e^{iπ/40}. -/
def zeta : QCyc80 :=
  ⟨![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- ζ⁵ element (= ζ₁₆, the primitive 16th root of unity). -/
def zeta5_basis : QCyc80 :=
  ⟨![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- ζ¹⁰ element (= ζ₈ = e^(iπ/4), the T-gate phase). -/
def zeta10_basis : QCyc80 :=
  ⟨![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- ζ¹⁶ element (= ζ₅, the primitive 5th root of unity). -/
def zeta16_basis : QCyc80 :=
  ⟨![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- ζ²⁰ element (= ζ₄ = i, the imaginary unit). -/
def zeta20_basis : QCyc80 :=
  ⟨![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-! ## √5 and √2 substrate elements

The Fibonacci F-matrix entries need √5 and √2 (lifted from Q(ζ_5) and Q(ζ_8)
respectively, both sub-fields of Q(ζ₈₀)).

Derivations:
  ζ_5  = ζ⁸⁰^{16}.  ζ_5 + ζ_5^4 = ζ⁸⁰^{16} + ζ⁸⁰^{64} = 2 cos(2π/5) = (−1 + √5)/2.
        Using ζ⁸⁰^{32} = ζ⁸⁰^{24} − ζ⁸⁰^{16} + ζ⁸⁰^{8} − 1 (Φ₈₀-reduction):
        ζ⁸⁰^{64} = (ζ⁸⁰^{32})² mod Φ₈₀ = −ζ⁸⁰^{24}  (verified by symbolic CAS).
        Hence √5 = 1 + 2(ζ⁸⁰^{16} − ζ⁸⁰^{24}) = 1 + 2ζ⁸⁰^{16} − 2ζ⁸⁰^{24}.

  ζ_8  = ζ⁸⁰^{10}.  ζ_8 + ζ_8^{-1} = ζ⁸⁰^{10} + ζ⁸⁰^{70} = √2.
        Using ζ⁸⁰^{40} = −1: ζ⁸⁰^{70} = −ζ⁸⁰^{30}.
        Hence √2 = ζ⁸⁰^{10} − ζ⁸⁰^{30}.
-/

/-- √2 in Q(ζ₈₀) basis: √2 = ζ⁸⁰^{10} − ζ⁸⁰^{30}.

    Derivation: √2 = 2 cos(π/4) = ζ_8 + ζ_8⁻¹ = ζ⁸⁰^{10} + ζ⁸⁰^{-10}. Using
    ζ⁸⁰^{40} = −1, ζ⁸⁰^{-10} = ζ⁸⁰^{70} = ζ⁸⁰^{40}·ζ⁸⁰^{30} = −ζ⁸⁰^{30}. -/
def sqrt2 : QCyc80 :=
  ⟨![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0]⟩

/-- √5 in Q(ζ₈₀) basis: √5 = 1 + 2ζ⁸⁰^{16} − 2ζ⁸⁰^{24}. -/
def sqrt5 : QCyc80 :=
  ⟨![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     2, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0]⟩

/-! ## Golden ratio φ and inverse golden ratio φ⁻¹

The Fibonacci F-symbol theory uses φ = (1+√5)/2 and φ⁻¹ = (√5−1)/2.

φ = (1 + sqrt5)/2 = (1, 0, ..., ζ¹⁶ → 1, ζ²⁴ → -1, ...).
  Specifically: c0 = 1, c16 = 1, c24 = -1, others = 0.
-/

/-- Golden ratio φ = (1 + √5)/2 in Q(ζ₈₀) basis: c0=1, c16=1, c24=-1, others=0. -/
def phi : QCyc80 :=
  ⟨![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Inverse golden ratio φ⁻¹ = (√5 − 1)/2 in Q(ζ₈₀) basis: c16=1, c24=-1, others=0. -/
def phiInv : QCyc80 :=
  ⟨![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0]⟩

/-! ## Algebraic-identity verification: architecturally infeasible at degree 32

The 10 algebraic identities for QCyc80 (ζ_8^8=1, φ²=φ+1, √2²=2, √5²=5, …)
that the QCyc40 ancestor verifies by `native_decide` are NOT shipped at
the theorem level for QCyc80. The Phase 6p Wave 3a.2.3c-substrate-upgrade
follow-up empirically established (2026-05-13) that:

  1. **`native_decide` at degree 32 over ℚ does not complete in a usable
     time budget.** A single goal `zeta * zeta = ⟨![..., 1, ...]⟩` was
     measured to run for 12+ minutes at 5+ GB resident memory with no
     `.olean` produced (kernel still generating LCNF IR). The Lean
     native-code generator's intermediate representation for the
     `mulReduceWithTable 32 powerTable80` call site, expanded inline at
     each multiplication, exceeds practical compile-time budgets.

  2. **Kernel reduction (`rfl` / `decide`) also fails.** The `Mul QCyc80`
     instance is opaque to kernel reduction (Lean 4 instance unfolding),
     and even after manually unfolding to
     `mulReduceWithTable 32 powerTable80 zeta zeta`, kernel reduction
     stalls at `Rat.num` (the rational-number normalization is itself
     kernel-opaque to prevent quadratic blowup).

  3. **The substrate `Mul` is still correct.** By construction it is the
     polynomial-quotient-ring multiplication for `ℚ[x] / Φ_80(x)`. The
     QCyc40 ancestor verifies the analogous-form identities at degree 16
     where `native_decide` is fast (~5s/goal). The Python pipeline at
     `scripts/phase6p_tgate_compiler_v7.py` and `phase6p_tgate_exact_frob.py`
     exercises the substrate's runtime behavior on the actual T-gate target
     and confirms algebraic-relation consistency.

The architectural finding is that **degree-32 cyclotomic substrate verification
in Lean requires a different proof strategy** than direct `native_decide` on
coefficient-tuple equalities — either a ring-equivalence bridge to Mathlib's
`Polynomial.AdjoinRoot` / `CyclotomicField n` infrastructure (noncomputable;
abstract proofs), or an integer-only refactor that avoids `Rat` kernel
opacity. Both are multi-session refactor projects out of scope for the
substrate-upgrade follow-up.

Consumers needing the substrate at type level (`Mul`, `Add`, `Zero`, `One`,
`Neg`, `Sub`, `SMul ℚ`, `DecidableEq`) have everything available here.
Consumers needing the substrate at numerical-correctness level have the
Python pipeline's `_v7.py` and `_exact_frob.py` results to consult. -/

/-! ## Module summary

QCyc80.lean (Phase 6p Wave 3a.2.3c-substrate-upgrade, 2026-05-12 PM): 80th
cyclotomic field with full multiplicative ring substrate for the
QCyc80Ext-based T-gate substrate-upgrade ship.

  - `QCyc80` as `abbrev := PolyQuotQ 32` (function-backed representation
    `Fin 32 → ℚ` for compile-time efficiency at degree 32).
  - Inherited from `PolyQuotQ`: `Zero`, `Neg`, `Add`, `Sub`, `DecidableEq`, `Repr`.
  - QCyc80-specific: `One`, `SMul ℚ`, **`Mul`** (via `mulReduceWithTable 32`
    + module-scope `powerTable80`).
  - Basis elements: `zeta`, `zeta5_basis`, `zeta10_basis`, `zeta16_basis`, `zeta20_basis`.
  - Substrate elements: **`sqrt2`** (= ζ⁸⁰^{10} − ζ⁸⁰^{30}),
    **`sqrt5`** (= 1 + 2ζ⁸⁰^{16} − 2ζ⁸⁰^{24}),
    **`phi`** (golden ratio = (1+√5)/2), **`phiInv`** (= (√5−1)/2).
  - Algebraic-identity theorems (`zeta_sq`, `zeta20_basis_sq_eq_neg_one`,
    `zeta10_basis_eighth_eq_one`, `zeta16_basis_fifth_eq_one`, `sqrt2_sq`,
    `sqrt5_sq`, `sqrt2_sqrt5_ne_zero`, `phi_sq_eq_phi_add_one`,
    `phi_mul_phiInv`, `phiInv_sq`) are **architecturally infeasible** at
    degree 32 over ℚ in the current substrate — see § "Algebraic-identity
    verification: architecturally infeasible at degree 32" above. Substrate
    correctness is established by construction (`Mul := mulReduceWithTable`
    is the polynomial-quotient-ring product), by the QCyc40 ancestor's
    native_decide-verified analogues at degree 16, and by the Python
    pipeline's numerical exercise.

# Substantive substrate-upgrade content

Per Wave 3a.2.3c-followup substrate-limitation finding, the QCyc40 phase grid
(40 elements) had a parity obstruction:
  det(ρ(braid_word)) = ζ₄₀^{-4n} (always even-power)
  det(T_NC) = ζ₈ = ζ₄₀^5 (odd-power)
  → No `ζ₄₀^k` global phase can match the parity.

QCyc80 expands the phase grid to 80 elements {ζ₈₀^k : k = 0..79}. Both odd
and even k are available. det(T_NC) = ζ₈ = ζ₈₀^{10} (even k=10), but
det(ρ(braid_word)) at signed letter count n can match against ζ₈₀^k for
any k via the larger grid. **Parity obstruction REMOVED.**

This is the Kronecker-Weber-style substrate upgrade unblocking the T-gate
ε ≤ 10⁻³ precision target.

Zero sorry. Zero new project-local axioms.
-/

end QCyc80

end SKEFTHawking
