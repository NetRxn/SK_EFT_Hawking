/-
# Phase 5q.H (N6 seam, layer 3) — the carrier hook: `PinPlusCertK` feeds the σ÷16 leg

The literal E4-carrier end of the N6 wiring seam. The Pin⁺ tied carrier certifies spin through
`PinPlusCertK I s` (the `w₂ = 0` certificate in Wu-formula presentation, the `cert` field of
`PinPlusTiedData.TiedStr`); the σ÷16 leg consumes spin as `wuClass2 = 0` (`v₂ = 0`). This module
instantiates the vocabulary bridge (`WuClass1Orientation`, oriented ⟹ `v₁ = 0` ⟹ the two
presentations agree) at the carrier's own objects, so a **carrier-certified singular manifold with
an integral orientation consumes the σ÷16 leg directly** — no Wu-theory re-derivation at the
call site:

* `wuClass2_eq_zero_of_certK` — the certificate yields the leg's `hv2` input;
* `spinWuDatum_of_certK` — the full `SpinWuDatum` at `intFundamentalClassOfIntOrientation o`;
* `sixteen_dvd_latticeSig_of_orientation_certK` — `16 ∣ σ` with the spin input supplied by
  `PinPlusCertK` (a `TiedStr` caller passes `σ.cert`; the `T2Space` instance matches the `t2`
  field by proof irrelevance).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.WuClass1Orientation
import SKEFTHawking.PinPlusTiedData

namespace SKEFTHawking.PinPlusCertSpinSeam

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt (SpinWuDatum IntH2Basis interMatrix)
open SKEFTHawking.IntOrientationSection
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityWu (wuClass2)
open SKEFTHawking.PinPlusTiedData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
  {k : WithTop ℕ∞}

/-- **The carrier certificate yields the leg's spin input**: at a nonempty Hausdorff
carrier-certified singular 4-manifold with an integral orientation, `wuClass2 = 0` — the σ÷16
leg's `hv2` binder, discharged from `PinPlusCertK` through the oriented Wu-vocabulary bridge. -/
theorem wuClass2_eq_zero_of_certK {s : SingularManifold PUnit k I} (hcert : PinPlusCertK I s)
    [T2Space s.M] [Nonempty s.M] (o : IntOrientation s.M) :
    wuClass2 (poincareDual4Mid_of_closed (M := s.M)) = 0 :=
  SKEFTHawking.WuClass1Orientation.wuClass2_eq_zero_of_wuW2_eq_zero o hcert

/-- **`SpinWuDatum` from the carrier certificate** — the composed end of the N6 seam at the
carrier's objects: a `PinPlusCertK`-certified singular manifold with an integral orientation
produces the full spin-Wu datum the σ÷16 leg's machinery consumes
(via `spinWuDatum_of_closed`). A `TiedStr` caller passes `σ.cert`. -/
noncomputable def spinWuDatum_of_certK {s : SingularManifold PUnit k I}
    (hcert : PinPlusCertK I s) [T2Space s.M] [Nonempty s.M] (o : IntOrientation s.M) :
    SpinWuDatum (intFundamentalClassOfIntOrientation o) :=
  SKEFTHawking.WuClass1Orientation.spinWuDatum_of_closed_wuW2 o hcert

/-- **The σ÷16 leg fed by the carrier certificate**: `16 ∣ σ` at a plus-oriented
carrier-certified singular 4-manifold. The spin input is `PinPlusCertK I s` (the tied carrier's
`w₂`-certificate); the remaining open inputs are unchanged (N4 `kron`/`hkron`, N5 `B`,
N2 `htopo`). Witness manifolds certified on the E4 carrier side consume the σ÷16 leg directly. -/
theorem sixteen_dvd_latticeSig_of_orientation_certK {s : SingularManifold PUnit k I}
    (hcert : PinPlusCertK I s) [T2Space s.M] [Nonempty s.M]
    (d : IntOrientationData s.M) (h1 : ∀ x, d.orient x = 1)
    (kron : Homology (TopCat.of s.M) 2 ≃ₗ[ℤ]
      Module.Dual ℤ (SKEFTHawking.SingularCohomologyInt.Cohomology (TopCat.of s.M) 2))
    (hkron : ∀ (h : Homology (TopCat.of s.M) 2)
      (b : SKEFTHawking.SingularCohomologyInt.Cohomology (TopCat.of s.M) 2),
      kron h b = kroneckerHInt 2 b h)
    (B : IntH2Basis (TopCat.of s.M))
    (htopo : (2 : ℤ) ∣ SKEFTHawking.latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) B) / 8) :
    (16 : ℤ) ∣ SKEFTHawking.latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) B) :=
  SKEFTHawking.WuClass1Orientation.sixteen_dvd_latticeSig_of_orientation_wuW2 d h1 kron hkron B
    hcert htopo

end SKEFTHawking.PinPlusCertSpinSeam
