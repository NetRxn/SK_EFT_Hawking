/-
# Phase 5q.H (K8b interior) — the E₈ absorption identity

The second leaf of the Milnor–Husemoller route to
`EvenUnimodularIndefiniteSplit.StableNegRank16` (see `OddIndefiniteUnitVector` for the first).

The odd-form classification `⟨1⟩^p ⊕ ⟨−1⟩^q` cannot be reached by peeling unit vectors alone: the peel
can strand an EVEN definite residual (an `E₈` summand), which represents no odd value and so admits no
further unit peel. What rescues the induction is that a single `⟨1⟩` **absorbs** an `E₈`:

  `⟨1⟩ ⊕ ⟨−1⟩⁸  ≅  ⟨1⟩ ⊕ (−E₈)`      (rank 9, signature `−7`).

This module proves that identity **explicitly and unconditionally** — no classification input — by
exhibiting the change of basis. The witness is the classical degree-1 del Pezzo / `K^⊥ = E₈`
configuration inside the odd unimodular lattice `I₁,₈ = ⟨1⟩ ⊕ ⟨−1⟩⁸` with basis `e₀` (norm `+1`),
`e₁,…,e₈` (norm `−1`):

* the canonical class `K = −3e₀ + e₁ + ⋯ + e₈`, which has `K·K = 9 − 8 = 1` and is characteristic;
* the eight simple roots spanning `K^⊥`, each of norm `−2`:
  `e₁−e₂`, `e₀−e₁−e₂−e₃`, `e₂−e₃`, `e₃−e₄`, `e₄−e₅`, `e₅−e₆`, `e₆−e₇`, `e₇−e₈`
  — ordered to match `E8lit`'s Bourbaki node labelling (trivalent node at index `3`, arms `{1}`,
  `{2,0}`, `{4,5,6,7}`), so their Gram matrix is exactly `−E8lit`.

`(K, α₀, …, α₇)` is a ℤ-basis of `I₁,₈` (`e8AbsorbP` is unimodular, exhibited by the explicit inverse
`e8AbsorbQ`), and its Gram matrix is `⟨1⟩ ⊕ (−E₈)`. Both facts are closed by kernel `decide` on
integer literals — no `native_decide`.

The module also proves the **companion hyperbolic absorption** `⟨1⟩ ⊕ H ≅ ⟨1⟩ ⊕ ⟨1⟩ ⊕ ⟨−1⟩`
(`intCongr_oneHyp_I21`). `H` and `±E₈` are the only blocks an even unimodular summand contributes, so
the two identities together are exactly what the induction needs to absorb ANY even residual stranded
by a unit peel.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.E8Literal
import SKEFTHawking.HyperbolicNormalForm
import SKEFTHawking.SpinSigmaGenerator

namespace SKEFTHawking

open Matrix

/-- The odd unimodular lattice `I₁,₈ = ⟨1⟩ ⊕ ⟨−1⟩⁸` of rank 9 and signature `−7`, as an explicit
diagonal literal. -/
def I18 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, -1]

/-- `⟨1⟩ ⊕ (−E₈)` as an explicit rank-9 literal (the `decide`-friendly form of
`SpinSigmaRoute.blockDiag 1 (-E8lit)`, which is `noncomputable`). -/
def oneNegE8 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, -2, 0, 1, 0, 0, 0, 0, 0;
     0, 0, -2, 0, 1, 0, 0, 0, 0;
     0, 1, 0, -2, 1, 0, 0, 0, 0;
     0, 0, 1, 1, -2, 1, 0, 0, 0;
     0, 0, 0, 0, 1, -2, 1, 0, 0;
     0, 0, 0, 0, 0, 1, -2, 1, 0;
     0, 0, 0, 0, 0, 0, 1, -2, 1;
     0, 0, 0, 0, 0, 0, 0, 1, -2]

/-- **The absorbing change of basis.** Columns are the del Pezzo configuration
`(K, e₁−e₂, e₀−e₁−e₂−e₃, e₂−e₃, e₃−e₄, e₄−e₅, e₅−e₆, e₆−e₇, e₇−e₈)` expressed in the standard basis
`e₀,…,e₈` of `I₁,₈`, with `K = −3e₀ + e₁ + ⋯ + e₈`. -/
def e8AbsorbP : Matrix (Fin 9) (Fin 9) ℤ :=
  !![-3, 0, 1, 0, 0, 0, 0, 0, 0;
     1, 1, -1, 0, 0, 0, 0, 0, 0;
     1, -1, -1, 1, 0, 0, 0, 0, 0;
     1, 0, -1, -1, 1, 0, 0, 0, 0;
     1, 0, 0, 0, -1, 1, 0, 0, 0;
     1, 0, 0, 0, 0, -1, 1, 0, 0;
     1, 0, 0, 0, 0, 0, -1, 1, 0;
     1, 0, 0, 0, 0, 0, 0, -1, 1;
     1, 0, 0, 0, 0, 0, 0, 0, -1]

/-- The explicit integer inverse of `e8AbsorbP` (integral because `det e8AbsorbP = 1`). Exhibiting it
replaces a 9×9 kernel determinant (`9! = 362880` terms) by a single 9×9 product. -/
def e8AbsorbQ : Matrix (Fin 9) (Fin 9) ℤ :=
  !![-3, -1, -1, -1, -1, -1, -1, -1, -1;
     -5, -1, -2, -2, -2, -2, -2, -2, -2;
     -8, -3, -3, -3, -3, -3, -3, -3, -3;
     -10, -3, -3, -4, -4, -4, -4, -4, -4;
     -15, -5, -5, -5, -6, -6, -6, -6, -6;
     -12, -4, -4, -4, -4, -5, -5, -5, -5;
     -9, -3, -3, -3, -3, -3, -4, -4, -4;
     -6, -2, -2, -2, -2, -2, -2, -3, -3;
     -3, -1, -1, -1, -1, -1, -1, -1, -2]

/-- **The inverse-exhibition identity** `P · Q = 1` — kernel `decide` on integer literals. -/
theorem e8AbsorbP_mul_inv : e8AbsorbP * e8AbsorbQ = 1 := by decide

/-- `e8AbsorbP` is unimodular: its determinant is a unit, exhibited by `e8AbsorbQ`. -/
theorem e8AbsorbP_det_isUnit : IsUnit e8AbsorbP.det := by
  have h : e8AbsorbP.det * e8AbsorbQ.det = 1 := by
    rw [← Matrix.det_mul, e8AbsorbP_mul_inv, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ h

/-- **The Gram computation** `Pᵀ · I₁,₈ · P = ⟨1⟩ ⊕ (−E₈)` — kernel `decide`. The `[0][0]` entry is
`K·K = 1`; the first row/column vanishes because every `αᵢ` lies in `K^⊥`; the lower-right `8×8` block
is the Gram matrix of the eight simple roots, which is `−E8lit`. -/
theorem e8AbsorbP_gram : e8AbsorbPᵀ * I18 * e8AbsorbP = oneNegE8 := by decide

/-- **`oneNegE8` really is `⟨1⟩ ⊕ (−E₈)`** — the bridge from the `decide`-friendly literal to the
project's `blockDiag` shape, so downstream consumers see the structured form. -/
theorem oneNegE8_eq_blockDiag :
    oneNegE8 = SpinSigmaRoute.blockDiag (1 : Matrix (Fin 1) (Fin 1) ℤ) (-E8lit) := by
  rw [SpinSigmaRoute.blockDiag_def]
  decide

/-- **The E₈ absorption identity: `⟨1⟩ ⊕ ⟨−1⟩⁸ ≅ ⟨1⟩ ⊕ (−E₈)`.**

An `E₈` summand is invisible to an odd unimodular form: adjoining a single `⟨1⟩` to `−E₈` diagonalizes
it completely. This is the step that keeps the Milnor–Husemoller II.4.3 induction from stalling on an
even definite residual, and it is proved here **explicitly** — the witness is the del Pezzo
configuration `(K, K^⊥ simple roots)`, checked by kernel `decide`, with no classification input and no
`native_decide`.

Sanity check on the invariants: both sides have rank `9` and signature `1 − 8 = −7`, and both are odd
(the `⟨1⟩` has odd diagonal) and unimodular (`det E8lit = 1`). -/
theorem intCongr_I18_oneNegE8 : IntCongr I18 oneNegE8 :=
  ⟨e8AbsorbP, e8AbsorbP_det_isUnit, e8AbsorbP_gram⟩

/-- The absorption identity in `blockDiag` form: `I₁,₈ ≅ ⟨1⟩ ⊕ (−E₈)`. -/
theorem intCongr_I18_blockDiag_one_negE8 :
    IntCongr I18 (SpinSigmaRoute.blockDiag (1 : Matrix (Fin 1) (Fin 1) ℤ) (-E8lit)) := by
  rw [← oneNegE8_eq_blockDiag]; exact intCongr_I18_oneNegE8

/-! ### The companion: a hyperbolic plane is absorbed too

Every even unimodular indefinite form is built from `H` and `±E₈` blocks, so the Milnor–Husemoller
induction needs BOTH absorptions. The hyperbolic one is the rank-3 identity
`⟨1⟩ ⊕ ⟨1⟩ ⊕ ⟨−1⟩ ≅ ⟨1⟩ ⊕ H`, witnessed by `(e+v, −e+w, e+v−w)` in the basis `(e, v, w)` with
`e·e = 1`, `v·v = w·w = 0`, `v·w = 1`. -/

/-- `⟨1⟩ ⊕ ⟨1⟩ ⊕ ⟨−1⟩` (rank 3, signature `1`). -/
def I21 : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 1, 0; 0, 0, -1]

/-- `⟨1⟩ ⊕ H` (rank 3, signature `1`) — the odd form with a hyperbolic summand. -/
def oneHyp : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

/-- The absorbing change of basis for `⟨1⟩ ⊕ ⟨1⟩ ⊕ ⟨−1⟩ ≅ ⟨1⟩ ⊕ H`, read the other way: columns
`(e+v, −e+w, e+v−w)` of the source basis `(e, v, w)` of `⟨1⟩ ⊕ H`. -/
def hypAbsorbP : Matrix (Fin 3) (Fin 3) ℤ := !![1, -1, 1; 1, 0, 1; 0, 1, -1]

/-- Explicit inverse of `hypAbsorbP` (`det = −1`). -/
def hypAbsorbQ : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 1; -1, 1, 0; -1, 1, -1]

theorem hypAbsorbP_mul_inv : hypAbsorbP * hypAbsorbQ = 1 := by decide

theorem hypAbsorbP_det_isUnit : IsUnit hypAbsorbP.det := by
  have h : hypAbsorbP.det * hypAbsorbQ.det = 1 := by
    rw [← Matrix.det_mul, hypAbsorbP_mul_inv, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ h

theorem hypAbsorbP_gram : hypAbsorbPᵀ * oneHyp * hypAbsorbP = I21 := by decide

/-- **The hyperbolic absorption identity: `⟨1⟩ ⊕ H ≅ ⟨1⟩ ⊕ ⟨1⟩ ⊕ ⟨−1⟩`.**

A single `⟨1⟩` diagonalizes a hyperbolic plane. Together with `intCongr_I18_oneNegE8` this covers both
even blocks (`H` and `E₈`) that an even unimodular summand can contribute, which is what keeps the
Milnor–Husemoller II.4.3 induction from stalling once a unit peel leaves an even residual. -/
theorem intCongr_oneHyp_I21 : IntCongr oneHyp I21 :=
  ⟨hypAbsorbP, hypAbsorbP_det_isUnit, hypAbsorbP_gram⟩

end SKEFTHawking
