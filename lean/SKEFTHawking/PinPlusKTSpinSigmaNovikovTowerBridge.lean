/-
# Phase 5q.H close-out (#190) — THE MATRIX-MODEL IDENTIFICATION: the boundary form of `∂W`

`PinPlusKTSpinSigmaNovikovRealSubstrate.NovikovRealPairLES Bd` is the ℝ-linear-algebra engine that
DERIVES the Novikov `half` residual from a pair-LES/Kronecker/adjunction triple; its consumers speak the
**matrix language**, manipulating the block form `Bd = blockDiag (II M_p) (−II M_q)` as an abstract
`Matrix (Fin n) (Fin n) ℤ`. The `#187` integral pair-LES tower (`SingularRelativeCohomDeltaInt`) speaks the
**cohomology language**, over a generic pair `(X, S)`. This module is the first, fully-constructible girder
of the bridge between them — **the form identification** (steps 1–3 of the tower→Novikov identification):

* **§1 orientation reversal** — the reversed-orientation fundamental class `⟨−[M]⟩` and its effect on the
  intersection form (`interMatrix (reverse fc) B = −interMatrix fc B`). The `−II M_q` end of `∂W`.
* **§2 the boundary form identification (the headline)** — for a `SpinSigmaAtoms` bundle and a data-bordant
  pair `(p, q)`, the intersection matrix of the genuine boundary manifold `∂W = M_p ⊔ (−M_q)`, in the block
  basis (`intH2BasisSum`, the `#164` sum machinery), IS the consumer's block form
  `blockDiag (II M_p) (−II M_q)`. So the abstract `Bd` the Novikov substrate manipulates is literally the
  Gram matrix of the boundary manifold's integral intersection form — `H²(∂W;ℤ) ≅ Fin n → ℤ` carrying
  `interFormInt` to `Bd`. The boundary form's even-unimodularity (hence `radical = ⊥`, the substrate's
  `hbdnd`) is inherited from the ends' Wu/PD data.

## What remains — the cup-vs-Kronecker mediation (the named wall, escalated)

The substrate's PD-intertwining `hadj : ⟨ι*a ∪ v, [∂W]⟩ = ⟨a, δv⟩` (`rest2 ⊣ delta` under the Kronecker
pairing) is the classical "half lives, half dies" duality: it relates the **boundary cup form** on the
closed 4-manifold `∂W` (LHS — grounded here as `interFormInt` of the boundary manifold) to the **relative
Kronecker pairing** of an `H²(W)` class against the pair connecting map `δ : H²(∂W) → H³(W,∂W)` (RHS). The
`#187` tower supplies only the `δ ⊣ ∂` adjunction (`relKroneckerHInt_deltaRelHInt`: `⟨δz, [c]⟩ = ⟨z, ∂c⟩`);
the absolute cup-cap adjunction (`kroneckerHInt_cupH24`/`interFormInt_eq_kroneckerHInt_capHInt`) covers only
the closed-manifold cup against `[M]`. The mediation `⟨ι*a ∪ v, [∂W]⟩ = ⟨a, δv⟩` is genuine **relative
Poincaré–Lefschetz duality** of the pair `(W, ∂W)` — a relative cap product `H²(W) × H₄(W,∂W) → H₂(W)`
against `[W,∂W]` — which is NOT in-tree. That relative-PL cup mediation (plus the geometric bordism `W`
providing `rest2`/`delta`/`pairing` as tracked cohomology data of a 5-dimensional `W`) is the remaining
input, isolated to exactly the `hadj` field. This module discharges the FORM half of that field: its LHS is
the boundary manifold's `interFormInt`, coordinatised to `Bd`.

Dimension discipline: `∂W = M_p ⊔ (−M_q)` the 4-dimensional ends; the forms on `H²`; the (still-open) tower
at `(W, ∂W)` degrees `2 → 3`; `k₀`-free; the identification rides the GENUINE `intH2Basis` free-basis data
(no synthetic grade).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinSigmaNovikovRealSubstrate
import SKEFTHawking.IntersectionMatrixDisjointSumInt

namespace SKEFTHawking.PinPlusKTSpinSigmaNovikovTowerBridge

variable {k : WithTop ℕ∞}

open scoped Manifold
open SKEFTHawking SKEFTHawking.SingularCohomologyInt SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinSigmaAtom
open SKEFTHawking.PinPlusKTSpinSigmaNovikovRealSubstrate

noncomputable section

/-! ## §1. Orientation reversal of the integral fundamental class -/

variable {X : TopCat}

/-- **The reversed-orientation fundamental class** `⟨−[M]⟩`. `IntFundamentalClass` is carried by its
evaluation functional `⟨·, [M]⟩`; reversing orientation negates it (`⟨·, −[M]⟩ = −⟨·, [M]⟩`). This is the
`−M_q` end of the boundary `∂W = M_p ⊔ (−M_q)` at the level of the disclosed datum. -/
def intFundClassReverse (fc : IntFundamentalClass X) : IntFundamentalClass X :=
  ⟨-fc.eval⟩

@[simp] theorem intFundClassReverse_eval (fc : IntFundamentalClass X) :
    (intFundClassReverse fc).eval = -fc.eval := rfl

/-- **Orientation reversal negates the intersection form.** `⟨a ∪ b, −[M]⟩ = −⟨a ∪ b, [M]⟩`. -/
theorem interFormInt_reverse (fc : IntFundamentalClass X) (a b : Cohomology X 2) :
    interFormInt (intFundClassReverse fc) a b = -interFormInt fc a b := by
  rw [interFormInt_apply, interFormInt_apply, intFundClassReverse_eval, LinearMap.neg_apply]

/-- **Orientation reversal negates the intersection matrix** `interMatrix (reverse fc) B = −interMatrix fc B`
(entrywise, from `interFormInt_reverse`). The Gram-matrix form of the `−M_q` orientation reversal. -/
theorem interMatrix_reverse (fc : IntFundamentalClass X) (B : IntH2Basis X) :
    interMatrix (intFundClassReverse fc) B = -interMatrix fc B := by
  ext i j
  rw [interMatrix_apply, Matrix.neg_apply, interMatrix_apply, interFormInt_reverse]

/-! ## §2. The boundary form identification — `II(∂W) = blockDiag (II M_p) (−II M_q)` -/

variable {prov : CharPairWProviderPerOp (𝓡 4) k}

/-- **The boundary intersection matrix, in coordinates, IS the consumer's block form (HEADLINE).**

For a `SpinSigmaAtoms` bundle `a` and a pair of carrier manifolds `p, q`, the integral intersection matrix
of the genuine boundary manifold `∂W = M_p ⊔ (−M_q)` — its fundamental class the disjoint-sum class with the
`q`-end orientation-reversed (`intFundClassSum … (a.fc p) (reverse (a.fc q))`), its `H²(∂W;ℤ)` free basis the
block basis `intH2BasisSum (a.B p) (a.B q)` — equals, entry for entry, the block form
`blockDiag (II M_p) (−II M_q)` that `NovikovRealPairLES.Bd` manipulates. This is `#164`'s
`interMatrix_disjointSum_eq_blockDiag` composed with the `§1` orientation reversal: the matrix-model
identification of the boundary form. The abstract `Bd` is literally the Gram matrix of `interFormInt` on the
boundary manifold's `intH2Basis` — the honest `H²(∂W;ℤ) ≅ Fin n → ℤ` identification carrying `interFormInt`
to `Bd`. -/
theorem boundaryInterMatrix_eq_blockDiag (a : SpinSigmaAtoms prov)
    (p q : StrMfd (spinEmptyData prov)) :
    interMatrix
        (intFundClassSum (TopCat.of p.1.M) (TopCat.of q.1.M) (a.fc p) (intFundClassReverse (a.fc q)))
        (intH2BasisSum (TopCat.of p.1.M) (TopCat.of q.1.M) (a.B p) (a.B q))
      = blockDiag (interMatrix (a.fc p) (a.B p)) (-interMatrix (a.fc q) (a.B q)) := by
  rw [interMatrix_disjointSum_eq_blockDiag, interMatrix_reverse]

/-- **The boundary form is even-unimodular** (hence `radical = ⊥`, the substrate's `hbdnd`).
`blockDiag (II M_p) (−II M_q)` is even-unimodular: each end is even-unimodular from its Wu (`w₂ = 0`, EVEN)
and PD (UNIMODULAR) data, orientation reversal preserves even-unimodularity, and the block-diagonal sum of
two even-unimodular forms is even-unimodular. So the geometric boundary form supplies the substrate's
boundary-nondegeneracy `hbdnd` for free. -/
theorem boundaryForm_isEvenUnimodular (a : SpinSigmaAtoms prov)
    (p q : StrMfd (spinEmptyData prov)) :
    IsEvenUnimodular (blockDiag (interMatrix (a.fc p) (a.B p)) (-interMatrix (a.fc q) (a.B q))) := by
  have heuP := isEvenUnimodular_of_intPD (a.fc p) (a.B p) (a.wu p) (a.pd p)
  have heuQ := isEvenUnimodular_of_intPD (a.fc q) (a.B q) (a.wu q) (a.pd q)
  exact isEvenUnimodular_blockDiag _ _ heuP (isEvenUnimodular_neg _ heuQ)

/-- **The boundary form is nondegenerate over `ℝ` — the substrate's `hbdnd`, grounded geometrically.**
The `ℝ`-tensored boundary quadratic form `(Bd.map ℤ↪ℝ).toQuadraticMap'` has trivial radical, directly from
even-unimodularity (`boundaryForm_isEvenUnimodular`). This is *exactly* the `NovikovRealPairLES.hbdnd` field
the substrate requires — so a per-pair substrate built for the geometric boundary form gets its
boundary-nondegeneracy for free from the ends' Wu/PD data, no separate hypothesis. -/
theorem boundaryForm_radical_eq_bot (a : SpinSigmaAtoms prov)
    (p q : StrMfd (spinEmptyData prov)) :
    ((blockDiag (interMatrix (a.fc p) (a.B p)) (-interMatrix (a.fc q) (a.B q))).map
        (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ :=
  (boundaryForm_isEvenUnimodular a p q).radical_eq_bot

end

end SKEFTHawking.PinPlusKTSpinSigmaNovikovTowerBridge
