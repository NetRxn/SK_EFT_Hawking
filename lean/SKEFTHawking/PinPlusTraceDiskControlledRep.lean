/-
# Phase 5q.H — the controlled disk representative inherits detection (the transfer lemma)

`PinPlusTraceDiskCorePair.diskDetectChain` is the canonical `.choose` detecting chain for the disk
`D⁵`: it detects the interior generator at every point off the boundary sphere
(`diskDetectChain_hdet`), but its boundary is *unexposed* — the obstruction (#184 wall) to the seam
split `∂cHa = incl_# cSeam + vOut` the capstone cover-glue needs.

This module supplies the tool that lets a **controlled** representative — one whose boundary is
constructed and hence computable — inherit the detection *without re-proving it*, via the
relative-homology invariance of detection (`SingularRelClassHomologous.relClassOf_eq_of_homologous`).
Concretely: any chain `cCtrl` that differs from `diskDetectChain` by a boundary `∂w` plus a chain `e`
supported in the boundary sphere is homologous to it rel `{y}ᶜ` for every interior point `y` (the
sphere avoids `y`), so it detects at `y` too.

* `detecting_of_homologous_to_diskDetectChain` — the transfer: `cCtrl = diskDetectChain + ∂w + e`
  (`e` sphere-supported) `⟹` `cCtrl` detects the interior generator at every off-sphere point.

Downstream: a cone/fundamental-simplex representative with computable boundary `∂cCtrl ∈ C(sphere)`
that is homologous to `diskDetectChain` supplies the disk detecting triple (`hcHa := hc`,
`hdetHa := detecting_of_homologous_to_diskDetectChain`) while exposing the computable boundary the
seam split consumes. The remaining geometric residual is isolated to the *homology hypothesis*
`cCtrl = diskDetectChain + ∂w + e` (equivalently: `∂cCtrl` and `∂diskDetectChain` represent the same
`S⁴` fundamental class) — no longer the detection itself.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceDiskCorePair
import SKEFTHawking.SingularRelClassHomologous

namespace SKEFTHawking.PinPlusTraceDiskControlledRep

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.DiskChartGeneric (D5)

/-- **A controlled representative homologous to `diskDetectChain` inherits its detection.** If
`cCtrl` differs from the canonical disk detecting chain by a boundary `∂w` plus a chain `e`
supported in the boundary sphere `{‖v‖ = 1}`, then `cCtrl` detects the interior local generator at
every point `y` off the sphere — exactly `diskDetectChain_hdet`, transported along the homology.
The sphere avoids the interior point `y`, so it is `{y}ᶜ`-supported, and detection is a
relative-`{y}ᶜ`-homology invariant. This discharges the `hdetHa` field of the disk detecting triple
for any controlled (computable-boundary) representative, leaving only the homology hypothesis
`hrel`. -/
theorem detecting_of_homologous_to_diskDetectChain
    (cCtrl : SingularChain (TopCat.of D5) (3 + 2))
    (w : SingularChain (TopCat.of D5) (3 + 3))
    (e : SingularChain (TopCat.of D5) (3 + 2))
    (he : e ∈ subspaceChains (X := TopCat.of D5)
      {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 2))
    (hrel : cCtrl = PinPlusTraceDiskCorePair.diskDetectChain
      + chainBoundary (TopCat.of D5) (3 + 2) w + e)
    (hc : chainBoundary (TopCat.of D5) (3 + 1) cCtrl
      ∈ subspaceChains (X := TopCat.of D5) {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1))
    (y : D5) (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}) :
    relClassOf (X := TopCat.of D5) ({y}ᶜ) 3 cCtrl
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) hc) ≠ 0 := by
  have hsub : {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} ⊆ ({y}ᶜ : Set ↑(TopCat.of D5)) :=
    Set.subset_compl_singleton_iff.mpr hy
  rw [SingularRelClassHomologous.relClassOf_eq_of_homologous hsub 3 hrel he
      (subspaceChains_mono hsub (3 + 1) hc)
      (subspaceChains_mono hsub (3 + 1) PinPlusTraceDiskCorePair.diskDetectChain_hc)]
  exact PinPlusTraceDiskCorePair.diskDetectChain_hdet y hy

end SKEFTHawking.PinPlusTraceDiskControlledRep
