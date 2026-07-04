/-
# Phase 5q.H · E1 — the integral intersection form `H²(M⁴;ℤ) × H²(M⁴;ℤ) → ℤ` (pre-matrix)

Substrate-G foundation brick (Option-A from-scratch). Assembles the **integral intersection form** of a
closed oriented charted 4-manifold as a *symmetric* ℤ-bilinear map
`interFormInt : Cohomology X 2 →ₗ[ℤ] Cohomology X 2 →ₗ[ℤ] ℤ`, `interFormInt a b = ⟨a ∪ b, [M]⟩`.

The integral cohomology ring through degree 4 is already built (kernel-pure, on main):
`SingularCohomologyInt.Cohomology X n` (integral cochain complex + `Hⁿ(X;ℤ)`, δ²=0) and the integral cup
product `SingularCohomologyInt.cupH24 : Cohomology X 2 →ₗ[ℤ] Cohomology X 2 →ₗ[ℤ] Cohomology X 4` together
with graded-commutativity `SingularCohomologyInt.cupH24_symm`. What this module adds is the *evaluation
against the fundamental class*, turning the H⁴-valued cup product into a ℤ-valued symmetric form.

## The fundamental class enters as a disclosed tracked datum (the new ℤ ingredient: orientation)

The mod-2 blueprint (`PoincareDualityConstruct.fundamentalFunctional = kroneckerH.flip fundamentalClass`)
pairs a *constructed* mod-2 fundamental class `[M] ∈ H₄(M;ℤ/2)` — which needs **no orientation** (every
closed manifold is ℤ/2-orientable). Over ℤ the fundamental class `[M] ∈ H₄(M;ℤ)` exists only for an
**oriented** manifold, and constructing it (plus the integral Kronecker pairing `H⁴(M;ℤ) × H₄(M;ℤ) → ℤ`,
neither of which is on main — the on-main homology/Kronecker tower is entirely over `ZMod 2`) is the later
community-scale work.

Per this dispatch's scope (the goal is the FORM, not yet the geometric orientation theorem), the
fundamental class is carried as the linear functional it *induces* on `H⁴`:

  `IntFundamentalClass X` — a one-field structure holding `eval : Cohomology X 4 →ₗ[ℤ] ℤ`, i.e. the
  integral evaluation pairing `⟨·, [M]⟩` **as a datum**.

This is the disclosed tracked-datum pattern (registered in `HYPOTHESIS_REGISTRY` as
`intFundamentalClass_eval_datum`). Its discharge = build integral singular homology `H₄(M;ℤ)`, the
orientation class `[M]`, and the integral Kronecker pairing `kroneckerHInt`, then instantiate
`eval := (kroneckerHInt (m+2)).flip [M]` — exactly mirroring the mod-2 `fundamentalFunctional`. Everything
in THIS module (the assembly + symmetry) holds for an *arbitrary* such functional, so it is discharged for
free the moment the geometric `[M]` is built.

All proofs kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCupInt

namespace SKEFTHawking.SingularCohomologyInt

open SKEFTHawking.SingularCohomologyInt

variable {X : TopCat}

/-! ## §1. The integral fundamental class as a disclosed evaluation datum -/

/-- **The integral fundamental class `[M] ∈ H₄(M;ℤ)`, carried as its induced evaluation functional.**

A one-field structure holding the **integral Kronecker/evaluation pairing** `⟨·, [M]⟩` of a closed
oriented charted 4-manifold: the ℤ-linear functional `Cohomology X 4 →ₗ[ℤ] ℤ` that a genuine fundamental
class `[M] ∈ H₄(M;ℤ)` induces on top-degree integral cohomology, `ω ↦ ⟨ω, [M]⟩`.

This is the integral analogue of the mod-2 `PoincareDualityConstruct.fundamentalFunctional`
(`= kroneckerH.flip fundamentalClass`), packaged as a **datum** because — unlike the ℤ/2 case — over ℤ
the class needs an orientation and the integral homology + Kronecker tower it descends from is not yet on
main. Disclosed tracked hypothesis `intFundamentalClass_eval_datum` (discharge: build `H₄(M;ℤ)` + `[M]` +
`kroneckerHInt`, then `eval := kroneckerHInt.flip [M]`). Every result in this module holds for an arbitrary
such `eval`, so the disclosed datum is the *only* unproved input to the intersection form. -/
structure IntFundamentalClass (X : TopCat) where
  /-- The integral evaluation pairing `⟨·, [M]⟩ : H⁴(X;ℤ) →ₗ[ℤ] ℤ` against the fundamental class. -/
  eval : Cohomology X 4 →ₗ[ℤ] ℤ

/-! ## §2. The integral intersection form and its symmetry -/

/-- **The integral intersection form** `H²(M⁴;ℤ) × H²(M⁴;ℤ) → ℤ`, `(a,b) ↦ ⟨a ∪ b, [M]⟩`, as a genuine
ℤ-**bilinear** map: the integral cup product `cupH24` post-composed with the fundamental-class evaluation
`fc.eval`. Bilinearity is inherited from `cupH24` (ℤ-bilinear) and `fc.eval` (ℤ-linear) via `compr₂`.

This is the pre-matrix intersection form: the object whose Gram matrix on a free basis of `H²(M;ℤ)` is the
even-unimodular integer form the DONE lattice leg (`AlgebraicRokhlin.IsEvenUnimodular` +
`LatticeSignature.latticeSig`) consumes for `σ ÷ 16`. The free-basis extraction, unimodularity (Poincaré
duality) and evenness (Wu) are LATER bricks — this module stops at the symmetric bilinear form. -/
noncomputable def interFormInt (fc : IntFundamentalClass X) :
    Cohomology X 2 →ₗ[ℤ] Cohomology X 2 →ₗ[ℤ] ℤ :=
  cupH24.compr₂ fc.eval

/-- **`interFormInt a b = ⟨a ∪ b, [M]⟩`** — the intersection form evaluates a pair by cupping and pairing
against the fundamental class. -/
@[simp] theorem interFormInt_apply (fc : IntFundamentalClass X) (a b : Cohomology X 2) :
    interFormInt fc a b = fc.eval (cupH24 a b) :=
  LinearMap.compr₂_apply cupH24 fc.eval a b

/-- **The integral intersection form is symmetric** — `⟨a ∪ b, [M]⟩ = ⟨b ∪ a, [M]⟩`. Immediate from
graded-commutativity of the integral cup product at bidegree `(2,2)` (`cupH24_symm`, Koszul sign
`(-1)^{2·2} = +1`): the H⁴ classes `a ∪ b` and `b ∪ a` are equal, so evaluating either against `[M]`
agrees. This equips `interFormInt` with the symmetric-bilinear-form structure the signature leg needs. -/
theorem interFormInt_symm (fc : IntFundamentalClass X) (a b : Cohomology X 2) :
    interFormInt fc a b = interFormInt fc b a := by
  rw [interFormInt_apply, interFormInt_apply, cupH24_symm]

/-- **Packaged symmetry-of-arguments** — `interFormInt fc` is a symmetric ℤ-bilinear map (the `∀ a b`
form of `interFormInt_symm`), the exact hypothesis a `LinearMap.IsSymm` / Gram-matrix builder consumes. -/
theorem interFormInt_isSymm (fc : IntFundamentalClass X) :
    ∀ a b : Cohomology X 2, interFormInt fc a b = interFormInt fc b a :=
  interFormInt_symm fc

end SKEFTHawking.SingularCohomologyInt
