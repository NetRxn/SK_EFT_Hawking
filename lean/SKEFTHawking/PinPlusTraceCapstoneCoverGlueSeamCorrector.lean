/-
# Phase 5q.H close-out — THE CAPSTONE hasClass FROM A SEAM CORRECTOR CHAIN (the sharpest residual)

`PinPlusTraceCapstoneCoverGlueSeam.hasClass_ofSeam` lands the capstone `hasClass` field from the disk
detecting triple + a `CapstoneSeamDatum` (a `SeamCollarChainDatum` at the capstone carrier). This
module composes it with the corrector-builder `SeamCollarChainDatum.ofCorrector`
(`SingularRelativeCoverMVSeamCorrector`) to land `hasClass` DIRECTLY from a single **corrector chain**
`p` plus its four genuinely-geometric facts — the datum's bookkeeping (`e`, `E`, `hcongr`, `he`, `hE`)
discharged.

So the deepest capstone atom reduces, for connected `s.M`, to EXACTLY:

* the `D⁵` relative-fundamental (detecting) triple `cHa`/`hcHa`/`hdetHa` (the parallel lane's output);
* one **corrector chain** `p` on the carrier with (i) `∂p ∈ C(∂W)`, (ii) `∂(glued - p) ∈ C(∂W)`,
  (iii) `p` detects the local generator at every seam point off `∂W`, and (iv) the mismatch
  `glued - p` supported off the seam overlap `range fromCyl ∩ range fromHandle`

where `glued = push cCyl + push cHa` is the two-core glued chain. This is the minimal geometric shape
of the remaining collar-chain construction (a Mayer–Vietoris partition of the glued relative-
fundamental chain into a seam-detecting rel-cycle `p` and an away rel-cycle `glued - p`), now stated
as a single Lean entry point rather than a nine-field datum.

**Fences.** No collar chain is constructed — `p` is a supplied input (THE COLLAR FORK). Additive
module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCoverGlueSeam
import SKEFTHawking.SingularRelativeCoverMVSeamCorrector

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SingularRelativeCoverMVSeam
open SKEFTHawking.SingularSurgeryCoreDetect
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlue
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueCyl
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueSeam

namespace SKEFTHawking.PinPlusTraceCapstoneCoverGlueSeamCorrector

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The capstone seam datum, built from a corrector chain.** The `CapstoneSeamDatum` inhabited from
one corrector chain `p` on the carrier plus its four genuinely-geometric facts — the boundary-in-`∂W`
facts `hpS`/`heS`, the seam detection `hp_det`, and the off-overlap mismatch support `hagree`. The
five bookkeeping fields of the underlying `SeamCollarChainDatum` are discharged by
`SeamCollarChainDatum.ofCorrector`. -/
def CapstoneSeamDatum.ofCorrector
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (p : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2))
    (hpS : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) p
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    (heS : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
            (3 + 2) (capstoneCylChain s S hS φ hφ hφinj)
          + closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
            (3 + 2) cHa - p)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    (hagree : closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChain s S hS φ hφ hφinj)
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 2) cHa - p
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
            ∩ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)ᶜ (3 + 2))
    (hp_det : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3 p
          (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) hpS) ≠ 0) :
    CapstoneSeamDatum s t S hS φ hφ hφinj cd hseam d cHa :=
  SeamCollarChainDatum.ofCorrector hpS heS hagree hp_det

/-- **The capstone `hasClass`, landed from the disk triple + a seam corrector chain.** The single
sharpest entry point: the deepest capstone atom (`CapstoneAmbientSupply.hasClass`, equivalently the
`hasClass` argument of `TraceRelFundLeaves.ofCapstone`) is produced, for connected `s.M`, from
exactly {the `D⁵` relative-fundamental triple `cHa`/`hcHa`/`hdetHa`, one corrector chain `p` with its
four geometric facts}. Chains `CapstoneSeamDatum.ofCorrector` into `hasClass_ofSeam`. -/
def hasClass_ofCorrector
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1))
    (hdetHa : ∀ (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
        (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) ({y}ᶜ) 3 cHa
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) hcHa) ≠ 0)
    (p : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2))
    (hpS : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) p
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    (heS : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
            (3 + 2) (capstoneCylChain s S hS φ hφ hφinj)
          + closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
            (3 + 2) cHa - p)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    (hagree : closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChain s S hS φ hφ hφinj)
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 2) cHa - p
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
            ∩ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)ᶜ (3 + 2))
    (hp_det : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3 p
          (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) hpS) ≠ 0) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  hasClass_ofSeam s t S hS φ hφ hφinj cd hseam d cHa hcHa hdetHa
    (CapstoneSeamDatum.ofCorrector s t S hS φ hφ hφinj cd hseam d cHa p hpS heS hagree hp_det)

end

end SKEFTHawking.PinPlusTraceCapstoneCoverGlueSeamCorrector
