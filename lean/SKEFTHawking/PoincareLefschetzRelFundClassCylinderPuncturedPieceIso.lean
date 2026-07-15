/-
# Phase 5q.H (W-A arm 4) — the `puncV` MV piece is `ℤ/2`

Capstone on the piece iso `PoincareLefschetzRelFundClassCylinderPuncturedPiece.puncVPieceEquiv`:
for a `T1` topological manifold `M` modelled on `ℝᵐ'⁺²`, the `M`-punctured MV piece of the
punctured product is the base **local** homology `H_{m'+2}(M, M∖σ) ≅ ℤ/2`
(`SingularChartBridge.manifoldLocalIso`), so

  `H_{m'+2}(M×I, (M∖σ)×I) ≅ ℤ/2`.

This is the two-element input the relative-MV LES dimension count needs at the `puncV` piece (in the
degree matching `M`'s top local homology) — the reusable arithmetic feeding any route-B closure of the
interior local-Künneth nonvanishing.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPiece
import SKEFTHawking.SingularChartBridge

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPiece

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPieceIso

noncomputable section

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T1Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-- **The `puncV` MV piece is `ℤ/2`.** Composing the piece iso (interval contraction)
`H_{m'+2}(M×I, (M∖σ)×I) ≅ H_{m'+2}(M, M∖σ)` with the chart↔excision bridge
`H_{m'+2}(M, M∖σ) ≅ ℤ/2` (`manifoldLocalIso`): the `M`-punctured piece of the punctured-product cover
is two-element in the degree of `M`'s top local homology. -/
def puncVLocalIso (x : ↑(cyl (TopCat.of M))) :
    RelativeHomology (X := cyl (TopCat.of M)) (puncV x) (m' + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  (puncVPieceEquiv x (m' + 1)).symm.trans
    (SKEFTHawking.SingularChartBridge.manifoldLocalIso (m := m') x.1)

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPieceIso
