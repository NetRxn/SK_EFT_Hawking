/-
# Phase 5q.H (W-A arm 4) — the terminal `hcls`, reduced to the ABSOLUTE `puncU` prism nonvanishing

Route-B δ-closer capstone. The reduction chain

  `hcls`  ⟸  `∀ interior x, crossHloc([M]|σ) ≠ 0`  (`…CrossLocalInj.hasRelFundClass_cylGen_of_localClass_ne_zero`)
        ⟸  `∀ interior x, crossHloc([M]|σ) = ι_U(αU)` + `ι_U` injective (`…CrossLocalBridge`)
        ⟸  `∀ interior x, αU ≠ 0`

collapses the concrete cylinder `HasRelFundClass` to ONE honest, flank-local, ABSOLUTE statement:

  `αU = crossH_puncU([M]) ≠ 0`

— the prism of the closed manifold's fundamental class `[M]`, rel the `I`-punctured piece
`puncU = M×(I∖t)`, is nonzero in `H_{m'+3}(M×I, M×(I∖t))`. This module banks the collapse
`hasRelFundClass_cylGen_of_alphaU_ne_zero` and reduces the residual to the connecting-map detection
`connecting_alphaU_ne_zero` (below), via the pair-LES of `(M×I, puncU)`:

* the connecting `δ_U : H_{m'+3}(M×I, puncU) → H_{m'+2}(M×(I∖t))` is INJECTIVE (its kernel is the image
  of `H_{m'+3}(M×I) = 0`, `…PuncturedFlankInjective.cyl_homology_above_eq_zero`), so
  `αU ≠ 0 ⟺ δ_U(αU) ≠ 0`;
* `δ_U(αU) = [∂(prismOp z)] = [M×{0} + M×{1}]` is the sum of the two endpoint slices of the fundamental
  class — the honest interior local-Künneth boundary datum, nonzero by the clopen `belowT ⊔ aboveT`
  split of `M×(I∖t)` (`…PuncturedPieceU.puncUSubHomEquiv`), each half projecting to `[M] ≠ 0`.

The `δ_U(αU) ≠ 0` split detection — the (m'+2)-dimensional mirror of
`SingularIntervalPairClass.homIncl_target_ne_zero` (the `H₀(I∖t)` augmentation split), with the
fundamental class in place of the augmentation — is the remaining terminal brick, isolated here as
`alphaU_boundary_ne_zero` (the precise residual: the endpoint-slice sum of `[M]` is nonzero in
`H_{m'+2}(M×(I∖t))`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalBridge
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalInj

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocal
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalReduce
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalInj
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalBridge

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalDetect

noncomputable section

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-- **The concrete cylinder `HasRelFundClass`, reduced to the ABSOLUTE `puncU` prism nonvanishing.**
If at every interior point the prism of the fundamental class rel the `I`-punctured piece is nonzero
(`αU = crossH_puncU([M]) ≠ 0`), the terminal `hcls` hole is discharged — via the chain-for-chain bridge
`crossHloc([M]|σ) = ι_U(αU)` and `ι_U` injective (`…CrossLocalBridge`). This is the sharpest reduction
of `cylFundClassCandidate_restricts`: the sole remaining obligation is an ABSOLUTE, split-computable
statement about `[M]` on the interval-suspension piece `M×(I∖t)`. -/
theorem hasRelFundClass_cylGen_of_alphaU_ne_zero [T1Space (cylW M)]
    (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z)
    (hαU : ∀ (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)),
      alphaU x hx ≠ 0) :
    HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
      (cylGen (M := M) (m' := m')) :=
  hasRelFundClass_cylGen_of_localClass_ne_zero z hz
    (fun x hx => crossHloc_ne_zero_of_alphaU_ne_zero x hx z hz (hαU x hx))

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalDetect
