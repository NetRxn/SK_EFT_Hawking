/-
# Phase 5q.H close-out — THE DISK-SIDE SEAM SPLIT: the engine instantiated at `diskDetectChain`.

The seam-split engine (`PinPlusTraceCapstoneSeamSplit`) applied to the banked disk detecting chain
`diskDetectChain` (#191/#...): for any two-set OPEN cover `{U, V}` of the boundary sphere
`{v | ‖v‖ = 1} = ∂D⁵`, the controlled rep `Sdᵘ diskDetectChain` has

* `∂(Sdᵘ diskDetectChain) = mapChain (ambIncl U) cU + vOut` — the attached part a pushforward from the
  subtype `↥U`, the free part `vOut ∈ subspaceChains V` (the exact `hsplitHa` shape),
* `∂(Sdᵘ diskDetectChain)` still supported in `{v | ‖v‖ = 1}` (the `hcHa` boundary-support),
* interior detection preserved: `Sdᵘ diskDetectChain` detects the local generator at every disk-
  interior point (the `hdetHa` shape), inherited from `diskDetectChain_hdet` across subdivision.

So the disk side of `hasClass_ofTransfer`'s inputs (`cHa := Sdᵘ diskDetectChain`, `hcHa`, `hdetHa`, and
the disk half of the transfer split) reduces to the SINGLE concrete residual: **provide the open cover
`{U, V}` of the boundary sphere with `S ⊆ U` and `∂D⁵ ∖ S ⊆ V`.**

**The residual (honest, NOT here).** The concrete cover fights `S` being CLOSED: the attached part
lands over an open nbhd `U ⊇ S`, not over `S` itself, and the two attaching legs demand the SHARED
seam chain (co-adaptation across `φ`). Refining `↥U`-content down to `↥S` (the collar retraction) and
the co-adaptation are the genuine geometric atoms; this module supplies everything the engine can, at
the concrete disk chain.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project
axiom, no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneSeamSplit
import SKEFTHawking.PinPlusTraceDiskCorePair

namespace SKEFTHawking.PinPlusTraceDiskSeamSplit

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularSubdivision
open SKEFTHawking.PinPlusTraceCapstoneSeamSplit
open SKEFTHawking.DiskChartGeneric (D5)

noncomputable section

/-- **The disk-side seam split of `diskDetectChain`, over an open cover of the boundary sphere.** For
an open cover `{U, V}` of the disk boundary sphere `{v | ‖v‖ = 1} = ∂D⁵`, the controlled rep
`Sdᵘ diskDetectChain` (`μ` from the subdivision engine) simultaneously:
(1) splits its boundary `∂(Sdᵘ diskDetectChain) = mapChain (ambIncl U) cU + vOut` — attached part a
pushforward from `↥U`, free part `vOut ∈ subspaceChains V`;
(2) keeps its boundary supported in the sphere `{v | ‖v‖ = 1}`;
(3) inherits `diskDetectChain`'s interior detection (nonzero local class off the sphere).
The complete disk-side supply of `hasClass_ofTransfer`, reduced to providing the cover. -/
theorem diskDetectChain_subtype_boundary_split {U V : Set D5} (hU : IsOpen U) (hV : IsOpen V)
    (hcover : {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} ⊆ U ∪ V) :
    ∃ (μ : ℕ) (cU : SingularChain (sub (X := TopCat.of D5) U) (3 + 1))
        (vOut : SingularChain (TopCat.of D5) (3 + 1)),
      vOut ∈ subspaceChains (X := TopCat.of D5) V (3 + 1)
      ∧ chainBoundary (TopCat.of D5) (3 + 1)
            ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] PinPlusTraceDiskCorePair.diskDetectChain)
          = mapChain (ambIncl (X := TopCat.of D5) U) (3 + 1) cU + vOut
      ∧ chainBoundary (TopCat.of D5) (3 + 1)
            ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] PinPlusTraceDiskCorePair.diskDetectChain)
          ∈ subspaceChains {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1)
      ∧ ∀ (y : D5) (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}),
          relClassOf (X := TopCat.of D5) ({y}ᶜ) 3
              ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] PinPlusTraceDiskCorePair.diskDetectChain)
              (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1)
                (chainBoundary_singularSd_iterate_mem 3 PinPlusTraceDiskCorePair.diskDetectChain
                  PinPlusTraceDiskCorePair.diskDetectChain_hc μ)) ≠ 0 := by
  obtain ⟨μ, cU, vOut, hvOut, hsplit, hmem⟩ :=
    exists_subtype_boundary_split_of_relCycle (X := TopCat.of D5) hU hV hcover
      PinPlusTraceDiskCorePair.diskDetectChain PinPlusTraceDiskCorePair.diskDetectChain_hc
  refine ⟨μ, cU, vOut, hvOut, hsplit, hmem, fun y hy => ?_⟩
  rw [relClassOf_singularSd_iterate_eq 3 PinPlusTraceDiskCorePair.diskDetectChain
    PinPlusTraceDiskCorePair.diskDetectChain_hc μ y hy]
  exact PinPlusTraceDiskCorePair.diskDetectChain_hdet y hy

end

end SKEFTHawking.PinPlusTraceDiskSeamSplit
