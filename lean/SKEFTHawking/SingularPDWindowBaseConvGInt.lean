/-
# Phase 5q.H (E1 CSC-PD tower) — the `hbaseConvG` discharge (integral)

Discharges the chart-agnostic base-case hypothesis `HbaseConvG M zM hzM` of `pdWindowPInt_univ` from the
now-complete zero-posit D⁰ base case (`openDuality₀_bijective_of_chartConvexInt`) plus the fundamental-class
datum of `zM` (the cycle property `hcyc` + the local-generator/orientation property `hloc`). This removes
`hbaseConvG` as a threaded hypothesis, leaving `pdWindowPInt_univ` resting only on `hcoreG` (the torsion-safe
connecting core) + the honest orientation input `hloc`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularPDWindowInt
import SKEFTHawking.SingularBaseCaseD0Int

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityMVConnSquareInt (castChainInt chainBoundary_castChainInt_eq_zero)
open SKEFTHawking.SingularPDWindowInt (HbaseConvG pdWindowPInt_of_chartConvex)

namespace SKEFTHawking.SingularPDWindowBaseConvGInt

/-- **`hbaseConvG` discharged from the D⁰ base case + the fundamental-class datum** (integral): given the
oriented fundamental cycle `zM` restricting to the local generator at every point (`hloc`), the chart-agnostic
base case `HbaseConvG M zM hzM` holds — each chart-convex `W` gets `pdWindowPInt` via
`pdWindowPInt_of_chartConvex` with `hD0` supplied by the zero-posit
`openDuality₀_bijective_of_chartConvexInt`. -/
theorem hbaseConvG_of_localGenInt {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcyc : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    (hloc : ∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
        (X := TopCat.of M) x (2 + 2)
        (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = (SKEFTHawking.SingularBaseCaseD0Int.localIsoComplInt x).symm 1) :
    HbaseConvG M zM hzM := by
  intro U' V' hU' hV' e' W hWo hWU' Cw hCwconv hCwopen pw hpw hCwV hWe'
  exact pdWindowPInt_of_chartConvex
    (fun S j => SKEFTHawking.SingularRelBoundariesProjectiveInt.relBoundariesInt_projective S j)
    hU' hV' e' hCwconv hCwopen hpw hCwV hWo hWU' hWe' zM hzM
    (SKEFTHawking.SingularBaseCaseD0Int.openDuality₀_bijective_of_chartConvexInt
      hU' hV' e' hCwconv hCwopen hpw hCwV hWo hWU' hWe'
      (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM) hcyc hloc)

end SKEFTHawking.SingularPDWindowBaseConvGInt
