/-
# Phase 5q.H close-out — THE CYLINDER-SIDE FEED OF THE CAPSTONE COVER-GLUE (residual discharge)

Probe module: discharge the cylinder-side triple of `capstone_hasClass_ofCoreChains` from the engine
`exists_cylinder_detecting_chain`, and package the remaining residuals.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCoverGlue
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderChainRep

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
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderChainRep
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlue

namespace SKEFTHawking.PinPlusTraceCapstoneCoverGlueCyl

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- The cylinder end `.B = s.M × I` of the capstone is `T1` (product of Hausdorff factors). -/
instance : T1Space (cylW s.M) := inferInstance

/-- The cylinder boundary-support set `BdB = ∂(M × I) = M × {⊥,⊤}` re-read on the capstone's
cylinder end `.B`. -/
def capstoneCylBdB : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B :=
  (cylModel 2).boundary (cylW s.M)

/-- The cylinder engine's detecting chain, re-read on the capstone's cylinder end `.B` in degree
`3 + 2`. -/
def capstoneCylChain :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2) :=
  (exists_cylinder_detecting_chain (M := s.M) (m' := 2)).choose

/-- The cylinder chain's boundary is supported in `BdB = M × {⊥,⊤}`. -/
theorem capstoneCyl_hc :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
        (capstoneCylChain s S hS φ hφ hφinj)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          (capstoneCylBdB s S hS φ hφ hφinj) (3 + 1) :=
  (exists_cylinder_detecting_chain (M := s.M) (m' := 2)).choose_spec.choose

/-- The cylinder chain detects the local generator at every interior cylinder point. -/
theorem capstoneCyl_hdet (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
    (hy : y ∉ capstoneCylBdB s S hS φ hφ hφinj) :
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) ({y}ᶜ) 3
        (capstoneCylChain s S hS φ hφ hφinj)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1)
          (capstoneCyl_hc s S hS φ hφ hφinj)) ≠ 0 :=
  (exists_cylinder_detecting_chain (M := s.M) (m' := 2)).choose_spec.choose_spec y hy

/-! ## §2. The narrowed cover-glue residual — the cylinder side discharged. -/

/-- **The capstone cover-glue residual with the cylinder side discharged.** The four residuals of
`capstone_hasClass_ofCoreChains`, with the cylinder-side triple (`cCyl`/`hcCyl`/`hdetCyl`, `BdB`
fixed to `M × {⊥,⊤}`) SUPPLIED from the cylinder engine (`exists_cylinder_detecting_chain`, for
connected `s.M`). What remains is exactly: the `D⁵` detecting chain `cHa` with its boundary support
`BdHa`/`hcHa` and intrinsic detection `hdetHa`; the two boundary-absorb facts `habsorbB`/`habsorbHa`;
the mod-2 seam-cancellation `hbd`; and the overlap-zone straddle detection `hdetAB`. Each field is a
genuine geometric atom on a concrete chain; none is a completeness Prop and none demands detection at
a closed piece's frontier. `toHasClass` fires `capstone_hasClass_ofCoreChains` with the cylinder side
discharged — landing the exact `CapstoneAmbientSupply.hasClass` field. -/
structure CapstoneCoverGlueResidual where
  /-- the `D⁵` handle-side chain (residual 1: the disk detecting chain). -/
  cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)
  /-- the mod-2 seam-cancellation of the pushed sum (residual 3). -/
  hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
      (closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChain s S hS φ hφ hφinj)
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 2) cHa)
    ∈ subspaceChains
        (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)
  /-- the cylinder boundary-absorb fact (residual 2, cyl side): `∂W ∪` the handle core absorbs the
  cylinder's manifold boundary `M × {⊥,⊤}`. -/
  habsorbB : ∀ y ∈ capstoneCylBdB s S hS φ hφ hφinj,
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl y
      ∈ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ∪ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle
  /-- the `D⁵`-side boundary-support set (the disk's boundary sphere region). -/
  BdHa : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha
  /-- the handle boundary-absorb fact (residual 2, handle side): `∂W ∪` the cylinder core absorbs the
  disk's boundary-support set. -/
  habsorbHa : ∀ y ∈ BdHa, (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle y
    ∈ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      ∪ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
  /-- the `D⁵` chain's boundary is supported in `BdHa`. -/
  hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
    ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) BdHa (3 + 1)
  /-- the `D⁵` chain detects the local generator at every disk-interior point (residual 1). -/
  hdetHa : ∀ (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (hy : y ∉ BdHa),
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) ({y}ᶜ) 3 cHa
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) hcHa) ≠ 0
  /-- the overlap-zone straddle detection (residual 4): the glued chain detects on the seam collar. -/
  hdetAB : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
    x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
    x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
      (closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChain s S hS φ hφ hφinj)
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 2) cHa)
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) hbd) ≠ 0

/-- **The narrowed residual supplies the capstone `hasClass` field.** Fires
`capstone_hasClass_ofCoreChains` with the cylinder-side triple discharged from the engine
(`capstoneCylChain`/`capstoneCyl_hc`/`capstoneCyl_hdet`, `BdB = M × {⊥,⊤}`) and the `D⁵`-side +
gluing residuals supplied by the row — producing the exact type of `CapstoneAmbientSupply.hasClass`
(and of the `hasClass` argument of `TraceRelFundLeaves.ofCapstone`). So the deepest capstone atom is
reduced to inhabiting `CapstoneCoverGlueResidual` for connected `s.M`. -/
def CapstoneCoverGlueResidual.toHasClass
    (R : CapstoneCoverGlueResidual s t S hS φ hφ hφinj cd hseam d) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  capstone_hasClass_ofCoreChains s t S hS φ hφ hφinj cd hseam d
    (capstoneCylChain s S hS φ hφ hφinj) R.cHa R.hbd R.habsorbB
    (capstoneCyl_hc s S hS φ hφ hφinj) (capstoneCyl_hdet s S hS φ hφ hφinj)
    R.habsorbHa R.hcHa R.hdetHa R.hdetAB

end

end SKEFTHawking.PinPlusTraceCapstoneCoverGlueCyl
