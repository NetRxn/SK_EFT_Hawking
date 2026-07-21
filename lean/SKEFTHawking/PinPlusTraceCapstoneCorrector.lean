/-
# Phase 5q.H close-out (#212, the gate-passing boundary) — THE CONTROLLED SEAM-CORRECTOR DATUM

**The round-13 gate's 8-point frozen specification, implemented (the CONSUMER half).** The 2026-07-20
codex shape-gate FAILED the proposed `CapstoneSeamCollarPair` repair (empty-K/zero-split fake; the
corrector suppliable independently of the split; `hasClass_ofTransferCorrector` type-locked to the
DEAD `CapstoneSeamTransfer` — settled fork `seam-transfer-open-support-uninhabitable`, #210). The
gate then specified the exact gate-passing boundary. This module builds it:

* **`CapstoneSeamCorrectorT`** — the controlled-cylinder corrector datum, the ONLY shape the supply
  side will consume (spec point 8). Fields: the fundamental cycle `z` + its class pin `hz` (the
  CONTROLLED representative — detection flows from `hz`, not from an arbitrary cycle), the corrector
  chain `p` as inspectable DATA (spec 3), the four seam facts `hpS`/`heS`/`hagree`/`hp_det` with
  `heS` stored EXPLICITLY (spec 6 — NOT derived through the dead transfer's `hbd_ofTransfer`,
  spec 2), and the anti-fake guard **`nonzero_of_genuine`** (spec 7): genuine attachment (the
  top face `z@⊤` NOT supported away from `range φ`) forces `p ≠ 0`.
* **`hasClass` is DERIVED, never stored** (spec 8): `CapstoneSeamCorrectorT.toHasClass` routes the
  four facts through `SeamCollarChainDatum.ofCorrector` (the four-fact minimal interface) into the
  carrier-level seam suppliers (`coreChains_hbd_of_seam` / `coreChains_hdetAB_of_seam`) and fires
  `capstone_hasClass_ofCoreChains` with the banked canonical disk triple
  (`diskDetectChain`/`_hc`/`_hdet`) and the controlled cylinder triple
  (`capstoneCylT_hc`/`capstoneCylT_hdet` at `hz`). The conclusion is the EXACT
  `CapstoneAmbientSupply.hasClass` field type — the downstream rows
  (`PinPlusTraceCapstoneInhabit:307`, `PinPlusTraceCapstoneSupplyMV:110`,
  `PinPlusTraceCapstoneMembraneWeld:257`) consume it as-is.

**What is deliberately NOT here (the PRODUCER half — the construction wave):**
`correctorT_of_collarPair : CollarPairBuild → CapstoneSeamCorrectorT` — the genuine collar-prism/
MV-partition construction from inspectable split data (`K` with the `hcoreHit` guard, subdivision
counts, split chains — spec points 3–5, 7). Its `CollarPairBuild` interface is NOT frozen here:
the fields encode the actual prism construction, and freezing them before the construction design
re-runs the hcompat mistake. The gate's constraints on it are recorded above and in the task-#212
spec; the producer is the remaining deep brick.

**Fences honored:** spec 1 (no `CapstoneSeamCollarPair` supply field — no such structure exists
here); spec 2 (nothing routes through `CapstoneSeamTransfer` / `hbd_ofTransfer` /
`hasClass_ofTransferCorrector` — the import of `PinPlusTraceCapstoneSeamTransfer` is ONLY for the
§2 controlled-representative declarations `capstoneCylChainT`/`capstoneCylT_hc`/`capstoneCylT_hdet`,
which are transfer-free); THE COLLAR FORK (no collar chain is constructed — `p` is supplied input).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
import SKEFTHawking.PinPlusTraceDiskCorePair

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SingularRelativeCoverMVSeam
open SKEFTHawking.SingularSurgeryCoreDetect
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlue
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueCyl
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceDiskCorePair

namespace SKEFTHawking.PinPlusTraceCapstoneCorrector

section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §1. The controlled corrector datum (the gate-passing consumed shape) -/

/-- **THE CONTROLLED SEAM-CORRECTOR DATUM** (round-13 gate spec, the consumed boundary — spec
point 8). The whole seam content of the capstone `hasClass`, over the CONTROLLED cylinder
representative `capstoneCylChainT z` (class-pinned by `hz`) and the CANONICAL disk chain
`diskDetectChain`:

* `z` / `hz` — the fundamental cycle of the source 4-manifold, with its class pin (detection
  flows from `hz`);
* `p` — the corrector chain, inspectable DATA (spec 3);
* `hpS` / `heS` / `hagree` / `hp_det` — the four seam facts of the minimal corrector interface
  (`SeamCollarChainDatum.ofCorrector`), with `heS` stored EXPLICITLY (spec 6; never through the
  dead transfer, spec 2);
* `nonzero_of_genuine` — the anti-fake guard (spec 7): if the top face `z@⊤` genuinely meets the
  attaching region (is NOT supported in `M × {⊤} ∖ range φ`), the corrector cannot be zero. -/
structure CapstoneSeamCorrectorT where
  /-- the fundamental cycle of the source 4-manifold. -/
  z : cycles (TopCat.of s.M) (2 + 2)
  /-- the class pin: `z` represents THE fundamental class. -/
  hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
    = Homology.mk (TopCat.of s.M) (2 + 2) z
  /-- the corrector chain (inspectable data — spec 3). -/
  p : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)
  /-- fact 1: the corrector's boundary is a boundary-chain. -/
  hpS : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) p
    ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)
  /-- fact 2 (stored EXPLICITLY — spec 6): the mismatch's boundary is a boundary-chain. -/
  heS : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
      (closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 2) (diskDetectChain)
        - p)
    ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)
  /-- fact 4: the mismatch is supported OFF the overlap of the two cores. -/
  hagree : closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
      + closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
        (3 + 2) (diskDetectChain)
      - p
    ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
          ∩ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)ᶜ (3 + 2)
  /-- fact 3: the corrector detects the local generator at every overlap point off `∂W`. -/
  hp_det : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3 p
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) hpS) ≠ 0
  /-- **the anti-fake guard (spec 7)**: genuine attachment — the top face `z@⊤` NOT supported in
  the un-attached region `M × {⊤} ∖ range φ` — forces a nonzero corrector. -/
  nonzero_of_genuine :
    mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
    p ≠ 0

/-! ## §2. The derivation chain — `hasClass` from the corrector, transfer-free -/

variable {s t S hS φ hφ hφinj cd hseam d}

/-- The corrector's four facts assemble the seam collar-decomposition datum over the controlled
cylinder representative and the canonical disk chain — via the minimal four-fact interface
(`SeamCollarChainDatum.ofCorrector`), never the dead transfer. -/
noncomputable def CapstoneSeamCorrectorT.seamDatum
    (R : CapstoneSeamCorrectorT s t S hS φ hφ hφinj cd hseam d) :
    CoreSeamDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 3
      (capstoneCylChainT s S hS φ hφ hφinj R.z) (diskDetectChain) :=
  SeamCollarChainDatum.ofCorrector R.hpS R.heS R.hagree R.hp_det

/-- **THE CAPSTONE `hasClass`, DERIVED from the controlled corrector datum** (spec point 8 —
derived, never stored). Fires `capstone_hasClass_ofCoreChains` with: the controlled cylinder triple
(`capstoneCylT_hc`/`capstoneCylT_hdet` at the corrector's `hz`), the banked canonical disk triple
(`diskDetectChain_hc`/`diskDetectChain_hdet`), the two boundary-absorbs from the surgered-end
datum, and the seam-cancellation + straddle detection discharged from the corrector's seam datum
(`coreChains_hbd_of_seam`/`coreChains_hdetAB_of_seam`). The conclusion is the EXACT
`CapstoneAmbientSupply.hasClass` field type. -/
noncomputable def CapstoneSeamCorrectorT.toHasClass
    (R : CapstoneSeamCorrectorT s t S hS φ hφ hφinj cd hseam d) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  capstone_hasClass_ofCoreChains s t S hS φ hφ hφinj cd hseam d
    (capstoneCylChainT s S hS φ hφ hφinj R.z) (diskDetectChain)
    (coreChains_hbd_of_seam (ktHandleAttachment s.M D5 S hS φ hφ hφinj) R.seamDatum)
    (capstone_habsorbB s t S hS φ hφ hφinj cd hseam d)
    (capstoneCylT_hc s S hS φ hφ hφinj R.z)
    (capstoneCylT_hdet s S hS φ hφ hφinj R.z R.hz)
    (capstone_habsorbHa s t S hS φ hφ hφinj cd hseam d)
    (diskDetectChain_hc)
    (fun y hy => diskDetectChain_hdet y hy)
    (fun x hx hxA hxB =>
      coreChains_hdetAB_of_seam (ktHandleAttachment s.M D5 S hS φ hφ hφinj) R.seamDatum
        x hx hxA hxB)

end

end SKEFTHawking.PinPlusTraceCapstoneCorrector
