/-
# Phase 5q.H · E1 — `IntPoincareDuality` DISCHARGED at the two in-tree witnesses

`IntersectionFormUnimodularInt.IntPoincareDuality` is registered in `HYPOTHESIS_REGISTRY` as the
disclosed datum `intPoincareDuality_perfectPairing_datum`, tier `discharge_future`. The determinant
criterion (`IntPDDetCriterion.intPoincareDualityOfUnimodular`) turns any *proved* unimodularity of the
integer Gram matrix into that datum — and both of the arc's concrete witness carriers already have
their Gram matrix computed unconditionally. So the datum is CONSTRUCTED, not disclosed, at:

* **`S⁴`** — `SphereWitnessTowerInt.sphere4IntH2Basis` is the rank-0 basis of `H²(S⁴;ℤ) = 0`, so the
  Gram matrix is the empty `0×0` matrix with `det = 1`. Degenerate (`b₂ = 0`) but honest: it holds for
  EVERY fundamental-class datum, with zero geometric input.
* **`S²×S²`** — `SphereProdGramPinRetire.sphereProd_s2s2_evenUnimodular'` proves the rank-2 Gram matrix
  even unimodular with NO hypotheses (the Künneth/EZ congruence `interMatrix ≅ Hyp`). This witness is
  **not** degenerate: `b₂ = 2` and the form is the hyperbolic plane.

Together these are the non-vacuity anchor for the criterion: its hypothesis set is inhabited in tree,
at a witness with a nonzero intersection form, with no disclosed input whatsoever. They are also the
first two in-tree discharges of `intPoincareDuality_perfectPairing_datum`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.IntPoincareDualityDetCriterion
import SKEFTHawking.SphereProdGramPinRetire
import SKEFTHawking.SphereWitnessTowerInt

namespace SKEFTHawking.IntPDWitnesses

open SKEFTHawking SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SphereWitnessTowerInt (sphere4IntH2Basis sphereProdHDataComputed SphereProdT)
open SKEFTHawking.SphereProdHFourInt (sphereProdIntFundClassHonest)
open SKEFTHawking.SphereProdGramPinRetire (sphereProd_s2s2_evenUnimodular')

noncomputable section

/-! ## §1. `S⁴` — the degenerate witness (`b₂ = 0`) -/

/-- **The `S⁴` Gram determinant is `1`** — the intersection matrix on the rank-0 basis
`sphere4IntH2Basis` is the empty `0×0` matrix, whose determinant is the empty product. Holds for every
fundamental-class datum. -/
@[simp] theorem sphere4_interMatrix_det (fc : IntFundamentalClass (Sph 4)) :
    (interMatrix fc sphere4IntH2Basis).det = 1 :=
  Matrix.det_fin_zero

/-- **INTEGRAL POINCARÉ DUALITY AT `S⁴`, for every fundamental-class datum.** The first in-tree
discharge of `intPoincareDuality_perfectPairing_datum`. It is the degenerate case — `H²(S⁴;ℤ) = 0`, so
the perfect pairing is the unique map `0 → 0` — but it is a genuine construction of the datum with no
disclosed input, and it fixes the criterion's hypothesis set as inhabited. -/
def sphere4IntPoincareDuality (fc : IntFundamentalClass (Sph 4)) : IntPoincareDuality fc :=
  IntPDDetCriterion.intPoincareDualityOfIsUnitDet fc sphere4IntH2Basis
    (by rw [sphere4_interMatrix_det]; exact isUnit_one)

/-! ## §2. `S²×S²` — the NON-degenerate witness (`b₂ = 2`, hyperbolic form) -/

/-- **INTEGRAL POINCARÉ DUALITY AT `S²×S²`, UNCONDITIONALLY.** The substantive witness: the rank-2
intersection matrix of the honest product fundamental class on the computed basis is even unimodular
with no hypotheses (`sphereProd_s2s2_evenUnimodular'`, i.e. the Künneth/EZ congruence to `Hyp`), and
the determinant criterion converts unimodularity into the perfect-pairing datum.

This is what makes the whole `IntPDDetCriterion` route non-vacuous: a carrier with `b₂ = 2` and a
nonzero intersection form on which the disclosed `IntPoincareDuality` is *derived*, not assumed. -/
def sphereProdIntPoincareDuality : IntPoincareDuality sphereProdIntFundClassHonest :=
  IntPDDetCriterion.intPoincareDualityOfUnimodular sphereProdIntFundClassHonest
    sphereProdHDataComputed.intH2Basis sphereProd_s2s2_evenUnimodular'.2.1

/-- **The `S²×S²` perfect pairing computes as the intersection form** — the `toDualEquiv_apply` field
read back, confirming the constructed equivalence is the intersection form itself and not some
unrelated iso of `H²(S²×S²;ℤ)` with its dual. -/
theorem sphereProdIntPoincareDuality_apply (a b : Cohomology (SphereProdT) 2) :
    sphereProdIntPoincareDuality.toDualEquiv a b = interFormInt sphereProdIntFundClassHonest a b :=
  sphereProdIntPoincareDuality.toDualEquiv_apply a b

end

end SKEFTHawking.IntPDWitnesses
