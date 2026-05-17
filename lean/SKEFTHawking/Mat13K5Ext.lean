/-
Copyright (c) 2026 SK_EFT_Hawking contributors.
Released under Apache 2.0 license as described in the LEAN license.
Authors: John Roehm, Claude (Anthropic).
-/
import Mathlib
import SKEFTHawking.QCyc5
import SKEFTHawking.QCyc5Ext

set_option autoImplicit false

/-!
# 13×13 matrices over Q(ζ₅, √φ): `Mat13K_5Ext`

Phase 1.2 substrate for Wave 1.D.4 (f) 6-strand Fibonacci CNOT
Lean-verified gate. This module ships a hand-rolled 13×13 matrix
type over `QCyc5Ext = ℚ(ζ₅, √φ)` mirroring the `Mat5K` pattern from
`FibonacciQuintetUniversality.lean`, scaled to 13 dimensions for the
6-anyon Fibonacci fusion space (5-dim c=1 sector + 8-dim c=τ sector
= 13-dim total per Phase 6p Wave 3a.2.3b DR §Q2.1).

## Mathematical content

For N Fibonacci anyons, the dim-13 fusion space carries the natural
braid-group action via R-matrix conjugation. The 6-strand case (N=6,
2 logical qubits with 3 anyons per qubit) decomposes block-diagonally
as a 5-dim c=1 (total-charge-vacuum) sub-block and an 8-dim c=τ
(total-charge-Fibonacci) sub-block. Both sub-blocks carry 4-dim
computational sub-spaces (indices {1,2,3,4} in the c=1 block; indices
{9,10,11,12} in the c=τ block) plus 1+4 = 5 leakage dimensions.

This module provides the underlying 13×13 matrix infrastructure;
the explicit σ_1..σ_5 generators that populate it ship in the
companion Phase 1.3 module `FibonacciSextetTrueRep.lean`.

## Why hand-rolled (vs `Matrix (Fin 13) (Fin 13) QCyc5Ext`)

Per Wave 1.D.2c Level B + Wave 1.D.4 (e) experience: Mathlib's
`Matrix` routes multiplication through general `Finset.sum`
machinery, which does NOT reduce cleanly under the kernel for
`native_decide` discharge of 169-entry polynomial equalities.
Hand-rolled flat-tuple types whose `*` operator is explicitly
unrolled to 13 sum-of-products expressions per output entry reduce
directly through the kernel; this is 10-100× faster (empirically per
the `Mat5K` shipment).

The DR estimates 13×13 multiplications are ~17× the cost of 5×5; the
empirical `native_decide` budget per call is therefore ≤ 4-mul chains
of `Mat13K_5Ext` (vs the ≤ 6-mul of `Mat5K`). Module consumers
should use the 3-level tree decomposition pattern (per
`project_mat5k_native_decide_tree_decomposition.md`).

## Field choice (Q5.1 DR justification)

Phase 6p Wave 3a.2.3b DR §Q5.1 proves via Kronecker-Weber that
√φ ∉ Q(ζ_n) for any n: φ = (1+√5)/2 satisfies x² − x − 1 = 0, so
√φ satisfies x⁴ − x² − 1 = 0; its splitting field Q(√φ, i) has
non-abelian D₄ Galois group, hence cannot embed in any abelian
cyclotomic. Therefore Q(ζ_40) (originally proposed in
`CNOTBraidTQSim.lean` docstring, line 31) is **insufficient** —
the natural minimal field for the 6-strand σ_n entries is

  K = Q(ζ_5, √φ) = QCyc5Ext

(already shipped for the 4-strand `FibonacciQuintetTrueRep`). The
`CNOTBraidTQSim.lean` docstring will be corrected in Phase 1.4 of
the wave.

## Pipeline-Invariant compliance

* No `axiom` declarations (Pipeline Invariant #15).
* No `set_option maxHeartbeats N` in proof bodies (Pipeline Invariant
  #10). `mul_assoc` discharges via `ring` over the
  `CommRing QCyc5Ext` instance from ADR-001 Unit 4 (SK_EFT_Hawking
  PR #33); for 13×13 this is a degree-3 polynomial identity in 169×169
  = 28 561 variables, but the `ring` proof reduces structurally without
  exhausting heartbeats.

## References

* `SK_EFT_Hawking/lean/SKEFTHawking/FibonacciQuintetUniversality.lean`
  §1: the `Mat5K` template this module scales up.
* `SK_EFT_Hawking/lean/SKEFTHawking/QCyc5Ext.lean`: the underlying
  field K = Q(ζ_5, √φ) + its `CommRing` instance (ADR-001 Unit 4).
* Phase 6p Wave 3a.2.3b DR (substrate spec; private repo).
* Pattern memory for chunk-tree compose discipline (private).
-/

namespace SKEFTHawking

open SKEFTHawking.QCyc5Ext

/-- 13×13 matrix over K = Q(ζ₅, √φ), function-typed. -/
abbrev Mat13K_5Ext : Type := Fin 13 → Fin 13 → QCyc5Ext

namespace Mat13K_5Ext

/-- Identity 13×13 matrix. -/
def one : Mat13K_5Ext := fun i j => if i = j then 1 else 0

/-- Zero 13×13 matrix. -/
def zero : Mat13K_5Ext := fun _ _ => 0

/-- Matrix multiplication (explicit unrolled 13-term sum, to avoid
    `AddCommMonoid`/`Finset.sum` indirection that doesn't reduce
    cleanly under `native_decide`). Same pattern as `Mat5K.mul`
    extended to 13 terms. -/
def mul (A B : Mat13K_5Ext) : Mat13K_5Ext :=
  fun i k =>
    A i 0  * B 0  k + A i 1  * B 1  k + A i 2  * B 2  k +
    A i 3  * B 3  k + A i 4  * B 4  k + A i 5  * B 5  k +
    A i 6  * B 6  k + A i 7  * B 7  k + A i 8  * B 8  k +
    A i 9  * B 9  k + A i 10 * B 10 k + A i 11 * B 11 k +
    A i 12 * B 12 k

/-- Matrix subtraction. -/
def sub (A B : Mat13K_5Ext) : Mat13K_5Ext := fun i j => A i j - B i j

/-- Matrix addition. -/
def add (A B : Mat13K_5Ext) : Mat13K_5Ext := fun i j => A i j + B i j

/-- Matrix negation. -/
def neg (A : Mat13K_5Ext) : Mat13K_5Ext := fun i j => -(A i j)

instance : Mul Mat13K_5Ext := ⟨Mat13K_5Ext.mul⟩
instance : Sub Mat13K_5Ext := ⟨Mat13K_5Ext.sub⟩
instance : Add Mat13K_5Ext := ⟨Mat13K_5Ext.add⟩
instance : Neg Mat13K_5Ext := ⟨Mat13K_5Ext.neg⟩
instance : Zero Mat13K_5Ext := ⟨Mat13K_5Ext.zero⟩
instance : One Mat13K_5Ext := ⟨Mat13K_5Ext.one⟩

/-! ### Monoid laws on `Mat13K_5Ext`

These three laws (`mul_assoc`, `one_mul`, `mul_one`) state that
`Mat13K_5Ext` forms a monoid under the hand-rolled `Mat13K_5Ext.mul`
/ `Mat13K_5Ext.one`. The proofs are direct: `funext i k` then unfold
the hand-rolled definitions to expose explicit unrolled sums, and
discharge with `ring` (for associativity, where `CommRing QCyc5Ext`
from ADR-001 Unit 4 powers the polynomial identity) or per-row
`fin_cases` (for the one-laws).

We state these as standalone theorems rather than registering a
`Monoid Mat13K_5Ext` typeclass instance, because the hand-rolled
`Mul` instance overrides the default `Matrix.instMul` from
`Matrix (Fin 13) (Fin 13) QCyc5Ext`; routing through Mathlib's monoid
infrastructure would create a typeclass diamond that callers would
have to navigate. The standalone form is simpler and sufficient. -/

/-- Matrix multiplication on `Mat13K_5Ext` is associative. The
2197-term polynomial identity per output entry holds over any
`CommRing`; we use the `CommRing QCyc5Ext` instance from ADR-001
Unit 4 (PR #33). -/
theorem mul_assoc (A B C : Mat13K_5Ext) : (A * B) * C = A * (B * C) := by
  funext i k
  show Mat13K_5Ext.mul (Mat13K_5Ext.mul A B) C i k =
       Mat13K_5Ext.mul A (Mat13K_5Ext.mul B C) i k
  unfold Mat13K_5Ext.mul
  ring

/-- Identity matrix is a left unit: `1 * A = A`. -/
theorem one_mul (A : Mat13K_5Ext) : (1 : Mat13K_5Ext) * A = A := by
  funext i k
  show Mat13K_5Ext.mul Mat13K_5Ext.one A i k = A i k
  unfold Mat13K_5Ext.mul Mat13K_5Ext.one
  fin_cases i <;> simp

/-- Identity matrix is a right unit: `A * 1 = A`. -/
theorem mul_one (A : Mat13K_5Ext) : A * (1 : Mat13K_5Ext) = A := by
  funext i k
  show Mat13K_5Ext.mul A Mat13K_5Ext.one i k = A i k
  unfold Mat13K_5Ext.mul Mat13K_5Ext.one
  fin_cases k <;> simp

/-! ### Smoke tests: identity self-product + structural sanity

These are not load-bearing for downstream proofs, but they exercise
the `native_decide` path on `Mat13K_5Ext` at module-build time to
catch toolchain regressions on the kernel-reduction cost (per DR Q6
Step 2 gate: `(1 : Mat13K_5Ext) * (1 : Mat13K_5Ext) = (1 : Mat13K_5Ext)`
should pass `native_decide` in ≤ 5 s). -/

/-- `1 * 1 = 1`: the identity matrix is idempotent under multiplication.
Smoke test for the `native_decide` path on `Mat13K_5Ext`; exercises
all 169 entries via the unrolled sum. -/
theorem one_mul_one : (1 : Mat13K_5Ext) * (1 : Mat13K_5Ext) = (1 : Mat13K_5Ext) := by
  native_decide

/-- Identity matrix's (0,0) entry is 1. -/
theorem one_diag_00 : (1 : Mat13K_5Ext) 0 0 = 1 := by native_decide

/-- Identity matrix's (0,12) entry is 0 (off-diagonal sanity at corner). -/
theorem one_offdiag_0_12 : (1 : Mat13K_5Ext) 0 12 = 0 := by native_decide

/-- Identity matrix's (12,12) entry is 1 (last-diagonal sanity). -/
theorem one_diag_12_12 : (1 : Mat13K_5Ext) 12 12 = 1 := by native_decide

/-- Zero matrix's (i, j) entry is 0 for any (i, j). Demonstrates that
the `Zero` instance reduces correctly. -/
theorem zero_entry (i j : Fin 13) : (0 : Mat13K_5Ext) i j = 0 := by rfl

end Mat13K_5Ext

end SKEFTHawking
