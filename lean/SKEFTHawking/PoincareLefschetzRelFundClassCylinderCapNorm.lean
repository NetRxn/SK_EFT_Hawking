import Mathlib
import SKEFTHawking.SingularNormalizationPInfty
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapPrism

/-!
# Phase 5q.H Track 2 — the terminal FIRE with the normalization statement DISCHARGED

The predecessor collapsed the entire Track-2 nondeg (Eilenberg–Zilber cap-cross projection) side to the
single classical statement `PrismProjKillsHomology` (the `t`-independent projection prism kills homology
= singular normalization) and pre-wired the fire constructor
`CylinderWAdmPinned.ofClosedPDSuspIntertwinePrismProjKills`, which consumes `hkill`.

`SingularNormalizationPInfty.prismProjKillsHomology_holds` now **proves** that statement for *every*
space (via the Dold–Kan `PInfty` normalization: the projection prism is a sum of degeneracies, killed by
`PInfty`, hence a boundary by Mathlib's `homotopyPInftyToId`). So `hkill` drops entirely: the terminal
`ofClosedPDSuspIntertwineNorm` consumes ONLY `{hwu, basePD, M-finiteness}` — nothing from the cap-cross
tower and no normalization residual survives.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapPrism
open SKEFTHawking.SingularNormalizationPInfty

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapNorm

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
variable [PreconnectedSpace M] [T1Space (cylW M)]

/-- **The terminal FIRE constructor, normalization DISCHARGED.** Feeds the now-proved
`prismProjKillsHomology_holds (TopCat.of M)` into `ofClosedPDSuspIntertwinePrismProjKills`, so the
*entire* Track-2 nondeg side is discharged unconditionally. Partial application: the remaining `hwu`
argument (the Wu-formula obstruction `wuW2 … = 0`) is left open. The post-fire `CylinderWAdmPinned M`
residual row is therefore exactly `{hwu, basePD, M-finiteness}` — nothing from the cap-cross tower and
no normalization residual survives. -/
def CylinderWAdmPinned.ofClosedPDSuspIntertwineNorm
    (findimM1 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 1))
    (findimM2 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 2))
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (basePD : Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3)) :=
  CylinderWAdmPinned.ofClosedPDSuspIntertwinePrismProjKills findimM1 findimM2 hM2 hM3 hM4 basePD
    (prismProjKillsHomology_holds (TopCat.of M))

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapNorm
