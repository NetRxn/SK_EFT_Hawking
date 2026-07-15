import Mathlib
import SKEFTHawking.PinPlusCylDataDischargeDisconnected

/-!
# Phase 5q.H — THE COMPONENT DECOMPOSITION (Route 2, staged)

Building the five-field `DisconnectedCylCore M` (`D, hM4, nd14, nd23, hwu`) for a NONEMPTY
DISCONNECTED closed charted 4-manifold from the finite component decomposition.

The connectedness dependence of the connected engine is genuinely irreducible: it localises to the
punctured-top-vanishing `H₄(M∖σ) = 0` (`…CylinderOpenTopVanish.openManifold_top_homology_eq_zero`),
which is FALSE for disconnected `M` (the other closed components survive with nonzero top homology).
Route 2 routes around this via the finite clopen component decomposition + the binary clopen-split
engine `SingularDisjointUnionHn.splitHnEquiv`, peeling one component at a time.
-/

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PinPlusCylDataDischarge
open SKEFTHawking.PinPlusCylDataDischargeDisconnected

namespace SKEFTHawking.PinPlusCylDataDischargeDisconnectedComponents

noncomputable section

variable (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-! ## §1. Finiteness of the connected components of a compact charted manifold. -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **A charted space over a locally-connected model is locally connected** (the model
`EuclideanSpace ℝ (Fin 4)` is locally connected; `ChartedSpace.locallyConnectedSpace`). -/
theorem locallyConnected_charted : LocallyConnectedSpace M :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M

omit [T2Space M] [Nonempty M] in
/-- **A compact charted manifold has finitely many connected components** (locally connected +
compact; `instFiniteConnectedComponentsOfLocallyConnectedSpaceOfCompactSpace`). -/
theorem finite_connectedComponents : Finite (ConnectedComponents M) := by
  haveI := locallyConnected_charted M
  infer_instance

end

end SKEFTHawking.PinPlusCylDataDischargeDisconnectedComponents
