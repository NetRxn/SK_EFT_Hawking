/-
# Phase 5q.H (N6 seam, layer 2) — oriented ⟹ `v₁ = 0`, and the `w₂`-certificate ⟹ `v₂ = 0` bridge

The E2↔E4 **vocabulary seam** (gap-map N6): the σ÷16 leg's spin input is the Wu-class statement
`hv2 : wuClass2 (poincareDual4Mid_of_closed) = 0` (`v₂ = 0`), while the Pin⁺ carrier certifies spin
through the Wu-formula `w₂` (`PinPlusCertK`-style: `wuW2 = v₂ + v₁² = 0`). The bridge between the
two presentations is the classical Wu fact `v₁ = w₁` — **on an oriented manifold `v₁ = 0`**, so
`w₂ = 0 ⟺ v₂ = v₁² = 0`. This module DERIVES that fact (no frozen Prop):

* `wuClass1_eq_zero_of_intOrientation` — `v₁ = 0` at any closed integrally-oriented charted
  4-manifold. `v₁` is the PD representative of `x ↦ ⟨Sq¹x, [M]₂⟩`; the orientation gives
  `[M]₂ = red [M]_ℤ` (`IntOrientation.redCompat`), and the Bockstein annihilates integrally-liftable
  classes (`BocksteinIntegralLift.kroneckerH_Sq1_redHomology`), so the represented functional is `0`
  and PD-nondegeneracy forces `v₁ = 0`. (Literature: Wu's formula `w = Sq(v)` gives `w₁ = v₁` in
  degree 1; orientable ⟺ `w₁ = 0`. Both directions here are *derived* from the singular substrate.)
* `wuClass2_eq_zero_of_wuW2_eq_zero` — **the seam bridge**: carrier-side `wuW2 = 0` + orientation
  ⟹ leg-side `wuClass2 = 0`, via `wuW2_eq_zero_iff_closed` (`w₂ = 0 ⟺ v₂ = v₁²`) and `v₁ = 0`.
* `spinWuDatum_of_closed_wuW2` — the composed end: orientation + `w₂`-certificate ⟹ the full
  `SpinWuDatum (intFundamentalClassOfIntOrientation o)` (via `spinWuDatum_of_closed`).
* `sixteen_dvd_latticeSig_of_orientation_wuW2` — the σ÷16 leg consuming the carrier-side spin
  vocabulary directly: `hv2` is REPLACED by `wuW2 = 0`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.BocksteinIntegralLift
import SKEFTHawking.SixteenDvdOfOrientationSpin

namespace SKEFTHawking.WuClass1Orientation

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt (SpinWuDatum IntH2Basis interMatrix)
open SKEFTHawking.IntOrientationSection
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.PoincareDualityWu (wuClass2)
open SKEFTHawking.PoincareDualityWuFormula

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **The first Wu class of a closed oriented 4-manifold vanishes** — `v₁ = 0` (the Wu-formula fact
`v₁ = w₁` combined with orientable ⟺ `w₁ = 0`, DERIVED, not frozen). `v₁` is the Poincaré-dual
representative of the functional `x ↦ ⟨Sq¹x, [M]₂⟩` on `H³`; the integral orientation supplies
`[M]₂ = red [M]_ℤ` (`redCompat`), and the Bockstein pairs to zero against every integrally-liftable
class (`BocksteinIntegralLift.kroneckerH_Sq1_redHomology`), so the represented functional is
identically `0` and the PD-nondegeneracy of the `(1,3)` pairing forces `v₁ = 0`. -/
theorem wuClass1_eq_zero_of_intOrientation (o : IntOrientation M) :
    wuClass1 (poincareDual4Lo_of_closed (M := M)) = 0 := by
  have hfun : wuFunctional1 (poincareDual4Lo_of_closed (M := M)) = 0 := by
    apply LinearMap.ext
    intro x
    show fundamentalFunctional (m := 2) (M := M) (SKEFTHawking.SingularBockstein.Sq1 x) = 0
    rw [fundamentalFunctional_apply, ← intOrientation_redHomology_fundClass o]
    exact SKEFTHawking.BocksteinIntegralLift.kroneckerH_Sq1_redHomology x o.fundClass
  rw [wuClass1, hfun, Equiv.symm_apply_eq, Equiv.ofBijective_apply, map_zero]

/-- **The N6 seam bridge**: the carrier-side spin certificate (`wuW2 = 0`, the Wu-formula `w₂`
presentation used by `PinPlusCertK`/the Pin⁺ tower) plus an integral orientation yields the
σ÷16 leg's spin input (`wuClass2 = 0`, the `v₂` presentation consumed by
`spinWuDatum_of_closed`). Via `wuW2_eq_zero_iff_closed` (`w₂ = 0 ⟺ v₂ = v₁²`) and the derived
`v₁ = 0` — so on an oriented manifold the two mod-2 spin vocabularies agree. -/
theorem wuClass2_eq_zero_of_wuW2_eq_zero (o : IntOrientation M)
    (hw2 : wuW2 (poincareDual4Mid_of_closed (M := M)) (poincareDual4Lo_of_closed (M := M)) = 0) :
    wuClass2 (poincareDual4Mid_of_closed (M := M)) = 0 := by
  rw [(wuW2_eq_zero_iff_closed (M := M)).mp hw2, wuClass1_eq_zero_of_intOrientation o, map_zero]

/-- **`SpinWuDatum` from the carrier-side certificate**: an integral orientation plus the
Wu-formula spin certificate `wuW2 = 0` construct the full spin-Wu datum at
`intFundamentalClassOfIntOrientation o` — the composed end of the N6 seam
(`spinWuDatum_of_closed` fed through the vocabulary bridge). -/
noncomputable def spinWuDatum_of_closed_wuW2 (o : IntOrientation M)
    (hw2 : wuW2 (poincareDual4Mid_of_closed (M := M)) (poincareDual4Lo_of_closed (M := M)) = 0) :
    SpinWuDatum (intFundamentalClassOfIntOrientation o) :=
  SKEFTHawking.SpinWuDatumClosed.spinWuDatum_of_closed o
    (wuClass2_eq_zero_of_wuW2_eq_zero o hw2)

/-- **The σ÷16 leg fed by the carrier-side spin vocabulary**: `16 ∣ σ` at a plus-oriented closed
charted 4-manifold whose spin condition arrives as the Wu-formula certificate `wuW2 = 0` (the
Pin⁺-carrier presentation) instead of the leg's native `v₂ = 0`. Open inputs otherwise unchanged:
the H₂ Kronecker duality `kron`/`hkron` (N4), the basis `B` (N5), and E2's topological factor
`htopo : 2 ∣ σ/8` (N2). Closes the N6 wiring seam at the leg. -/
theorem sixteen_dvd_latticeSig_of_orientation_wuW2 (d : IntOrientationData M)
    (h1 : ∀ x, d.orient x = 1)
    (kron : Homology (TopCat.of M) 2 ≃ₗ[ℤ]
      Module.Dual ℤ (SKEFTHawking.SingularCohomologyInt.Cohomology (TopCat.of M) 2))
    (hkron : ∀ (h : Homology (TopCat.of M) 2)
      (b : SKEFTHawking.SingularCohomologyInt.Cohomology (TopCat.of M) 2),
      kron h b = kroneckerHInt 2 b h)
    (B : IntH2Basis (TopCat.of M))
    (hw2 : wuW2 (poincareDual4Mid_of_closed (M := M)) (poincareDual4Lo_of_closed (M := M)) = 0)
    (htopo : (2 : ℤ) ∣ SKEFTHawking.latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) B) / 8) :
    (16 : ℤ) ∣ SKEFTHawking.latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) B) :=
  SKEFTHawking.SixteenDvdOfOrientationSpin.sixteen_dvd_latticeSig_of_orientation_spin d h1
    kron hkron B (wuClass2_eq_zero_of_wuW2_eq_zero (intOrientationOfData d) hw2) htopo

end SKEFTHawking.WuClass1Orientation
