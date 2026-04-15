/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the LEAN license.
Authors: John Roehm, Claude (Anthropic)
-/
import Mathlib

-- TODO (Mathlib-upstream PR): narrow these imports. Key minimal set is
-- approximately:
--   import Mathlib.Data.Fin.VecNotation        (for `![..]` literal syntax)
--   import Mathlib.Data.Fintype.Fin            (for `Fintype (Fin n)`)
--   import Mathlib.Data.Rat.Defs               (for `ℚ`)
--   import Mathlib.Algebra.BigOperators.Group.Finset.Basic  (for `Finset.sum`)
-- Exact narrowing is deferred to the Mathlib review cycle where Zulip
-- discussion will identify the canonical set.

/-!
# Computable polynomial quotient rings over `ℚ`

This module provides `PolyQuotQ n`, a computable representation of
`ℚ[x]/(p(x))` for a monic polynomial `p` of degree `n`, as coefficient
tuples `Fin n → ℚ` over the basis `{1, x, ..., x^{n-1}}`. The reduction
rule `x^n = Σᵢ reductionCoeffs(i) · x^i` is supplied to multiplication as
a plain parameter.

All arithmetic is fully computable — no `Finsupp`, no `Quotient`, no
`Classical.decEq`. This makes the construction compatible with
`native_decide`, in contrast to Mathlib's `AdjoinRoot`, `CyclotomicField`,
and `RingQuot` primitives, which are all noncomputable for decidability
purposes (they inherit `Classical.decEq` from `Finsupp`-based polynomial
infrastructure).

## Main definitions

* `PolyQuotQ n`: coefficient-tuple representation of `ℚ[x]/(p)` at degree `n`,
  with `Add`, `Sub`, `Neg`, `Zero` instances plus `DecidableEq` derived.
* `PolyQuotQ.shiftByXArr`: "multiply by `x`" on the coefficient array, using
  the reduction rule once.
* `PolyQuotQ.buildPowerTable`: the `(2n − 1) × n` reduction table, storing
  the coefficient tuple of `x^m mod p` for each `m ∈ [0, 2n − 2]`.
* `PolyQuotQ.mulReduce`: generic multiplication via explicit power table
  plus eager output materialization.

## Implementation notes

The multiplication uses an explicit `Array (Array ℚ)` power table
(`buildPowerTable`) rather than closure-based recursion. Closure-chain
implementations have two independent performance pitfalls under
`native_decide`:

1. **Exponential branching.** A "split into `n` reduction pieces" recursion
   on the degree spawns `n` sub-calls per step, giving `O(n^n)` leaf
   computations for unmemoized queries. Manageable at sparse reductions
   (e.g. `Φ₁₆(x) = x⁸ + 1`, 1 nonzero coefficient) but pathological at
   dense ones (e.g. `Φ₁₅`, 7 nonzero coefficients).
2. **Lazy closure re-evaluation.** Returning the struct as
   `⟨fun k => big_sum⟩` means each query re-executes the sum and
   re-queries the inputs' `coeffs`. For chained multiplications
   `(a * b) * c`, the outer mul's queries to `(a * b).coeffs` cascade
   through the chain exponentially.

Both problems are eliminated here: `buildPowerTable` computes the
reduction table explicitly with `O(n²)` setup and `O(1)` lookup, and
`mulReduce` materializes its output into `outArr : Array ℚ` before
wrapping it in the returned struct, giving `O(1)` access per query and
breaking the cascade. Total per-call complexity: `O(n³)`.

## Relationship to Mathlib's `AdjoinRoot`

A noncomputable `RingEquiv` to `AdjoinRoot p` (for appropriate `p`) may be
provided in a follow-up module to transfer abstract field-theoretic
results (field, `NumberField`, Galois theory) while keeping all
computation on the `PolyQuotQ` side. Such a bridge lives entirely in
`Prop` and does not need to evaluate.

## References

- L. Washington, *Introduction to Cyclotomic Fields*, Springer (1997).
- J. Xu, *Computation models for polynomials and finitely supported
  functions*, mathlib4 wiki (2025) — documents the underlying
  `Finsupp`/`Classical` obstruction that motivates this module.
-/

namespace SKEFTHawking

/-- Elements of `ℚ[x]/(p(x))` for a monic polynomial `p` of degree `n`,
    represented as coefficient tuples over the basis `{1, x, ..., x^{n-1}}`.

    `coeffs i` is the coefficient of `x^i`.

    `DecidableEq` is derived automatically: `Fin n` is `Fintype` and `ℚ`
    has computable `DecidableEq`, so `Fin n → ℚ` inherits pointwise
    decidable equality via `Pi.instDecidableEq`. -/
@[ext]
structure PolyQuotQ (n : ℕ) where
  /-- The coefficient function, indexed by degree. -/
  coeffs : Fin n → ℚ
  deriving DecidableEq, Repr

namespace PolyQuotQ

variable {n : ℕ}

/-! ## Arithmetic that does not depend on the reduction rule -/

instance : Zero (PolyQuotQ n) := ⟨⟨fun _ => 0⟩⟩

instance : Neg (PolyQuotQ n) where
  neg x := ⟨fun i => -x.coeffs i⟩

instance : Add (PolyQuotQ n) where
  add x y := ⟨fun i => x.coeffs i + y.coeffs i⟩

instance : Sub (PolyQuotQ n) where
  sub x y := ⟨fun i => x.coeffs i - y.coeffs i⟩

/-! ## Multiplication via an explicit power table -/

/-- Multiply the element represented by `prev` by `x` and reduce modulo `p`.

    Given `prev[k]` = coefficient of `x^k` in some element (with `k < n`),
    the product `x · prev` before reduction has `prev[k - 1]` at position
    `k ≥ 1` and `prev[n - 1]` at position `n`. Substituting
    `x^n = Σᵢ rᵢ xⁱ` yields

      new[k] = (prev[k - 1] if k > 0 else 0) + prev[n - 1] · r_k.

    For `n = 0` the input array is returned unchanged (vacuous case). -/
def shiftByXArr (r : Fin n → ℚ) (prev : Array ℚ) : Array ℚ :=
  if _ : 0 < n then
    let topVal := prev[n - 1]!
    Array.ofFn (fun k : Fin n =>
      let shifted := if k.val = 0 then 0 else prev[k.val - 1]!
      shifted + topVal * r k)
  else prev

/-- The `(2n − 1) × n` reduction table. Entry `m` is the coefficient tuple
    of `x^m mod p`.

    The first `n` entries are unit vectors: `x^0, x^1, ..., x^{n-1}` reduce
    to themselves. The remaining `n − 1` entries (for `m = n, n+1, …, 2n−2`)
    are built by repeatedly applying `shiftByXArr`. Total: `O(n²)` work. -/
def buildPowerTable (r : Fin n → ℚ) : Array (Array ℚ) :=
  let base : Array (Array ℚ) :=
    Array.ofFn (n := n) (fun m : Fin n =>
      Array.ofFn (fun k : Fin n => if k.val = m.val then 1 else 0))
  Nat.fold (n - 1) (fun _ _ acc =>
    acc.push (shiftByXArr r (acc[acc.size - 1]!))) base

/-- Multiplication in `ℚ[x]/(p)` using the reduction rule
    `x^n = Σᵢ reductionCoeffs(i) · xⁱ`.

    Uses `buildPowerTable` for `O(1)` power lookups, then materializes the
    full output coefficient tuple into `outArr` eagerly. Materialization
    breaks the lazy closure re-evaluation cascade that would otherwise
    make chained multiplications exponentially slow — see the module
    docstring's implementation notes. Total per-call cost: `O(n³)`. -/
def mulReduce (n : ℕ) (r : Fin n → ℚ) (x y : PolyQuotQ n) : PolyQuotQ n :=
  let table := buildPowerTable r
  let xArr : Array ℚ := Array.ofFn (n := n) (fun i : Fin n => x.coeffs i)
  let yArr : Array ℚ := Array.ofFn (n := n) (fun i : Fin n => y.coeffs i)
  let outArr : Array ℚ := Array.ofFn (n := n) (fun k : Fin n =>
    Finset.univ.sum (fun p : Fin n =>
      Finset.univ.sum (fun q : Fin n =>
        xArr[p.val]! * yArr[q.val]! *
          (table[p.val + q.val]!)[k.val]!)))
  ⟨fun k => outArr[k.val]!⟩

/-! ## Sanity checks

These examples verify `mulReduce` on concrete reduction rules at the
degrees we care about. They double as self-documenting usage examples. -/

/-- In `ℚ[x]/(x² - 2) = Q(√2)`: `√2 · √2 = 2`. Reduction `![2, 0]`. -/
example : mulReduce 2 ![2, 0] ⟨![0, 1]⟩ ⟨![0, 1]⟩ = ⟨![2, 0]⟩ := by
  native_decide

/-- In `ℚ[x]/(x² - 2) = Q(√2)`: `(1 + √2)² = 3 + 2√2`. -/
example : mulReduce 2 ![2, 0] ⟨![1, 1]⟩ ⟨![1, 1]⟩ = ⟨![3, 2]⟩ := by
  native_decide

/-- In `ℚ[x]/(x² + x + 1) = Q(ζ₃)`: `ζ · ζ · ζ = 1`, verified via a
    chained multiplication (stress-tests the materialization fix that
    prevents exponential cascade through chained `mulReduce` calls). -/
example : mulReduce 2 ![-1, -1]
            (mulReduce 2 ![-1, -1] ⟨![0, 1]⟩ ⟨![0, 1]⟩) ⟨![0, 1]⟩
          = ⟨![1, 0]⟩ := by
  native_decide

/-- In `ℚ[x]/(x⁴ + x³ + x² + x + 1) = Q(ζ₅)`: `ζ⁵ = 1`, verified via a
    5-deep chained multiplication at degree 4. -/
example : mulReduce 4 ![-1, -1, -1, -1]
            (mulReduce 4 ![-1, -1, -1, -1]
              (mulReduce 4 ![-1, -1, -1, -1]
                (mulReduce 4 ![-1, -1, -1, -1]
                  ⟨![0, 1, 0, 0]⟩ ⟨![0, 1, 0, 0]⟩)
                ⟨![0, 1, 0, 0]⟩)
              ⟨![0, 1, 0, 0]⟩)
            ⟨![0, 1, 0, 0]⟩
          = ⟨![1, 0, 0, 0]⟩ := by
  native_decide

end PolyQuotQ

end SKEFTHawking
