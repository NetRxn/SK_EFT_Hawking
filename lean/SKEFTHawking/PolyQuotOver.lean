/-
# PolyQuotOver: Generic Tower Extension K[w]/(p(w))

Generic construction of K[w]/(p(w)) over a base ring K, as coefficient
tuples over the basis {1, w, ..., w^{m-1}}, where p is monic of degree m.

This is the tower analog of `PolyQuotQ` (which is specialized to K = ℚ).
Parametric in base ring K and tower degree m — supports any base with
`DecidableEq`, `AddCommMonoid`, `One`, `Mul`.

## Use case

For QCyc5Ext = Q(ζ₅)[w]/(w² − φ), instantiate as `PolyQuotOver QCyc5 2`
with reduction `![φ, 0]` encoding w² = φ where φ = -ζ²-ζ³ ∈ Q(ζ₅).

## Architecture

Same pattern as `PolyQuotQ`:
- `reducePowerOver r p k` returns coefficient of w^k in w^p after reduction,
  recursive in p with well-founded decrease
- `mulReduceOver m r x y` computes the product via double-sum + reducePower

Requires `AddCommMonoid K` for `Finset.sum`. For degree-2 towers the bare-bones
version `mulReduce2` (below) works without AddCommMonoid.

## Phase 5i Wave 4b.ext (2026-04-15)

This completes the number-field consolidation begun in Wave 4a/4b:
every field in the project now arrives via either `PolyQuotQ n` (over ℚ)
or `PolyQuotOver K m` (over some other `PolyQuotQ n`).

## References

- Deep research: `Lit-Search/Phase-5i/5i-Decidable algebraic number fields
  for Lean 4 + Mathlib.md` (recommends tower construction for iterated extensions)
- Companion: `PolyQuotQ.lean` (base ℚ case)
-/

import Mathlib
import SKEFTHawking.PolyQuotQ

namespace SKEFTHawking

/-! ## 1. Generic Structure -/

/-- Elements of K[w]/(p(w)) where p is monic of degree m, as m-tuples over K. -/
@[ext]
structure PolyQuotOver (K : Type) [DecidableEq K] (m : ℕ) where
  coeffs : Fin m → K

/-- Manual `DecidableEq` instance. `deriving` cannot propagate the
    `[DecidableEq K]` bound through the generic parameter; we discharge
    it by reducing to pointwise equality on the `coeffs` function (decidable
    via `Pi.instDecidableEq` since `Fin m` is finite). -/
instance instDecidableEqPolyQuotOver {K : Type} [DecidableEq K] {m : ℕ} :
    DecidableEq (PolyQuotOver K m) := fun x y =>
  decidable_of_iff (x.coeffs = y.coeffs)
    ⟨fun h => PolyQuotOver.ext h, fun h => by cases h; rfl⟩

namespace PolyQuotOver

variable {K : Type} [DecidableEq K] {m : ℕ}

/-! ## 2. Reduction-free arithmetic -/

instance [Zero K] : Zero (PolyQuotOver K m) := ⟨⟨fun _ => 0⟩⟩

instance [Zero K] [One K] : One (PolyQuotOver K m) :=
  ⟨⟨fun i => if i.val = 0 then (1 : K) else (0 : K)⟩⟩

instance [Neg K] : Neg (PolyQuotOver K m) where
  neg x := ⟨fun i => -x.coeffs i⟩

instance [Add K] : Add (PolyQuotOver K m) where
  add x y := ⟨fun i => x.coeffs i + y.coeffs i⟩

instance [Sub K] : Sub (PolyQuotOver K m) where
  sub x y := ⟨fun i => x.coeffs i - y.coeffs i⟩

/-! ## 3. Generic power reduction

For base K with `AddCommMonoid + One + Mul`, `reducePowerOver r p k` returns
the coefficient of w^k in w^p after reduction mod p(w). Same recursive
structure as PolyQuotQ.reducePower. -/

/-- Coefficient of w^k in w^p after full reduction mod the minimal polynomial. -/
def reducePowerOver [AddCommMonoid K] [One K] [Mul K]
    (r : Fin m → K) (p : ℕ) (k : Fin m) : K :=
  if p < m then
    if p = k.val then (1 : K) else (0 : K)
  else
    Finset.univ.sum (fun i : Fin m =>
      r i * reducePowerOver r (p - m + i.val) k)
  termination_by p
  decreasing_by
    have hin : i.val < m := i.isLt
    omega

/-- Generic multiplication: delegates to reducePowerOver + Finset.sum.

**Known limitations (Phase 5i Wave 4 follow-up):**
1. `reducePowerOver` uses exponential split-into-m-pieces recursion, so
   dense reduction polynomials (≥ 3 nonzero reduction coefficients) cause
   native_decide perf blowup at higher degrees. The `PolyQuotQ.mulReduce`
   counterpart (over ℚ) was rewritten with an Array-based power table
   and eager output materialization to avoid both the exponential recursion
   AND lazy-closure reeval bug (see PolyQuotQ.mulReduce docstring).
2. The returned struct's `.coeffs` is a lazy closure over the Finset.sum —
   chained muls will cascade. Users of `mulReduceOver` with more than 2
   chained muls should materialize intermediate results.

The degree-2 specialization `mulReduce2` (below) does not suffer from
these issues and is the current default for degree-2 towers. Generalizing
to higher-degree towers via the Array-based approach is deferred. -/
def mulReduceOver [AddCommMonoid K] [One K] [Mul K]
    (m : ℕ) (r : Fin m → K) (x y : PolyQuotOver K m) : PolyQuotOver K m :=
  ⟨fun k => Finset.univ.sum (fun p : Fin m =>
             Finset.univ.sum (fun q : Fin m =>
               x.coeffs p * y.coeffs q * reducePowerOver r (p.val + q.val) k))⟩

/-! ## 4. Degree-2 specialization (no AddCommMonoid required)

For the common case of degree-2 towers (e.g., Q(K)[w]/(w² - r₀ - r₁·w)),
we provide a closed-form multiplication that only requires `Zero + Add + Mul`.
This is useful for bases that have arithmetic but not the full `AddCommMonoid`
typeclass wiring. -/

/-- Degree-2 tower multiplication in closed form.

    Given w² = r₀ + r₁·w and elements x = x₀ + x₁·w, y = y₀ + y₁·w:
      x·y = (x₀·y₀ + r₀·x₁·y₁) + (x₀·y₁ + x₁·y₀ + r₁·x₁·y₁)·w

    Pre-computes both output coefficients eagerly to prevent the
    lazy-closure-reeval bug (see PolyQuotQ.mulReduce docstring): without
    the eager captures `c0`, `c1`, each query to the result's `.coeffs`
    would re-run the inner arithmetic and cascade through chained muls. -/
def mulReduce2 [Zero K] [Add K] [Mul K]
    (r : Fin 2 → K) (x y : PolyQuotOver K 2) : PolyQuotOver K 2 :=
  let a0 := x.coeffs 0
  let a1 := x.coeffs 1
  let b0 := y.coeffs 0
  let b1 := y.coeffs 1
  let c0 := a0 * b0 + r 0 * (a1 * b1)
  let c1 := a0 * b1 + a1 * b0 + r 1 * (a1 * b1)
  ⟨fun i => if i.val = 0 then c0 else c1⟩

/-! ## 5. Sanity check

Test the degree-2 primitive on a concrete numeric tower: Q[w]/(w² - 2)
— this is just Q(√2) but viewed as a tower K[w]/(w² - 2) with K = ℚ. -/

/-- In Q[w]/(w² − 2): w · w = 2. Using mulReduce2 with r = ![2, 0]. -/
example :
    mulReduce2 (K := ℚ) ![2, 0] ⟨![0, 1]⟩ ⟨![0, 1]⟩ = ⟨![2, 0]⟩ := by
  native_decide

/-- In Q[w]/(w² − 2): (1 + w)² = 3 + 2w. -/
example :
    mulReduce2 (K := ℚ) ![2, 0] ⟨![1, 1]⟩ ⟨![1, 1]⟩ = ⟨![3, 2]⟩ := by
  native_decide

/-- In Q[w]/(w² + w + 1) = Q(ζ₃): w · w = -1 - w. Using r = ![-1, -1]. -/
example :
    mulReduce2 (K := ℚ) ![-1, -1] ⟨![0, 1]⟩ ⟨![0, 1]⟩ = ⟨![-1, -1]⟩ := by
  native_decide

/-! ## 6. Module summary -/

/--
PolyQuotOver module: Generic tower extension K[w]/(p(w)).

- `PolyQuotOver K m`: coefficient-tuple representation over base ring K
- `mulReduceOver`: generic mul for degree m (requires AddCommMonoid K)
- `mulReduce2`: degree-2 closed-form (requires only Zero + Add + Mul K)
- `reducePowerOver r p k`: coefficient of w^k in w^p after reduction

**Companion to `PolyQuotQ`.** Every algebraic number field in this project
now arrives via either `PolyQuotQ n` (over ℚ) or `PolyQuotOver K m` (over
some other `PolyQuotQ n`).

**Status (Phase 5i Wave 4b.ext, 2026-04-15):**
- Generic infrastructure complete
- Sanity checks at degree 2 over ℚ pass native_decide
- First user: QCyc5Ext = Q(ζ₅)[w]/(w² − φ) via `mulReduce2`
-/
theorem polyquotover_summary : True := trivial

end PolyQuotOver
end SKEFTHawking
