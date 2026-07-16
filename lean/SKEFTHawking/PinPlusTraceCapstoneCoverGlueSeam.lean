/-
# Phase 5q.H close-out — THE CAPSTONE COVER-GLUE FROM A SEAM DATUM (the two collar-chain residuals landed)

The narrowed capstone residual `CapstoneCoverGlueResidualDisk`
(`PinPlusTraceCapstoneCoverGlueDisk.lean`) has, after the cylinder side + the two boundary-absorbs +
`BdHa = S⁴` are all discharged, exactly FIVE fields: the `D⁵` detecting triple `cHa`/`hcHa`/`hdetHa`
(the disk's relative fundamental class — the parallel lane's `{β, hincl}`) and the two collar-chain
residuals `hbd` (the mod-2 seam-cancellation) and `hdetAB` (the overlap straddle detection).

This module lands the two collar-chain residuals from a single **seam collar-decomposition datum**
(`SingularSurgeryCoreDetect.CoreSeamDatum` at the capstone's handle-attachment carrier). The datum
names the honest geometric content once — a collar product chain `p` (the `SeamCollarDatum`'s
`S_att`-side chain × the collar interval, supplied by construction), an away-error `e`, the
chain-level seam agreement `push capstoneCylChain + push cHa = p + e`, the two boundary-in-`∂W`
facts, and the collar chain's overlap detection — and the carrier-level suppliers
`coreChains_hbd_of_seam`/`coreChains_hdetAB_of_seam` fire it into the `hbd`/`hdetAB` field types
verbatim.

**The assembly.** `CapstoneCoverGlueResidualDisk_ofSeam` takes the disk detecting triple (the
parallel lane's output) and the capstone seam datum, and inhabits the full
`CapstoneCoverGlueResidualDisk`. `hasClass_ofSeam` chains through `.toHasClass` to land the exact
`CapstoneAmbientSupply.hasClass` field (equivalently the `hasClass` argument of
`TraceRelFundLeaves.ofCapstone`). So the deepest capstone atom reduces, for connected `s.M`, to
exactly {the `D⁵` relative fundamental class, a seam collar-decomposition datum} — the two
collar-chain residuals now a transparent collar-product-chain datum, not black-box hypotheses.

**Fences.** No general collar theorem — the seam datum's collar chain `p` is a supplied concrete
chain, never a theorem (THE COLLAR FORK). No detection at a closed piece's frontier (the banned
partition route): the overlap detection is the collar chain's own, via the congruence.

Additive module (imports the disk residual + the carrier-level seam supplier; touches no membrane
module). Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom,
no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
import SKEFTHawking.SingularSurgeryCoreDetectSeam

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

namespace SKEFTHawking.PinPlusTraceCapstoneCoverGlueSeam

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The capstone seam collar-decomposition datum** — the `CoreSeamDatum` at the capstone's
handle-attachment carrier `ktHandleAttachment s.M D⁵ S φ`, boundary set `∂W`, degree `3`, cylinder
chain `capstoneCylChain`, and the disk detecting chain `cHa`. Its fields are the honest seam
residuals: the collar product chain, the away-error, the chain-level seam agreement, the
boundary-in-`∂W` facts, and the collar chain's overlap detection. -/
abbrev CapstoneSeamDatum
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)) : Type :=
  CoreSeamDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj)
    (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 3
    (capstoneCylChain s S hS φ hφ hφinj) cHa

/-- **The disk detecting triple + a seam datum inhabit `CapstoneCoverGlueResidualDisk`.** The disk
side `cHa`/`hcHa`/`hdetHa` (the parallel lane's `{β, hincl}` — the disk's relative fundamental class)
is passed through; the two collar-chain residuals `hbd`/`hdetAB` are DISCHARGED from the capstone
seam datum `D` via the carrier-level suppliers. -/
def CapstoneCoverGlueResidualDisk_ofSeam
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1))
    (hdetHa : ∀ (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
        (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) ({y}ᶜ) 3 cHa
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) hcHa) ≠ 0)
    (D : CapstoneSeamDatum s t S hS φ hφ hφinj cd hseam d cHa) :
    PinPlusTraceCapstoneCoverGlueDisk.CapstoneCoverGlueResidualDisk s t S hS φ hφ hφinj cd hseam d where
  cHa := cHa
  hcHa := hcHa
  hdetHa := hdetHa
  hbd := coreChains_hbd_of_seam (ktHandleAttachment s.M D5 S hS φ hφ hφinj) D
  hdetAB := fun x hx hxA hxB =>
    coreChains_hdetAB_of_seam (ktHandleAttachment s.M D5 S hS φ hφ hφinj) D x hx hxA hxB

/-- **The capstone `hasClass` from the disk detecting triple + a seam datum.** Chains
`CapstoneCoverGlueResidualDisk_ofSeam` into `.toHasClass`, landing the exact type of
`CapstoneAmbientSupply.hasClass` (equivalently the `hasClass` argument of
`TraceRelFundLeaves.ofCapstone`). So the deepest capstone atom reduces, for connected `s.M`, to
{the `D⁵` relative fundamental class, a seam collar-decomposition datum}. -/
def hasClass_ofSeam
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1))
    (hdetHa : ∀ (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
        (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) ({y}ᶜ) 3 cHa
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) hcHa) ≠ 0)
    (D : CapstoneSeamDatum s t S hS φ hφ hφinj cd hseam d cHa) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  (CapstoneCoverGlueResidualDisk_ofSeam s t S hS φ hφ hφinj cd hseam d cHa hcHa hdetHa D).toHasClass

end

end SKEFTHawking.PinPlusTraceCapstoneCoverGlueSeam
