/-
# Phase 5q.H close-out — THE KRS SUPPLY CONSOLIDATION: the single end-to-end residual row

After ~15 waves of reductions the KRS lane's suppliers are scattered across a dozen modules. This
module produces the ONE authoritative statement: **`KRSResidualRow`** — every genuinely-remaining
atom of the kernel-reduces-to-spin supply as a field with its provenance wave and builder
obligation — and **`kernelReducesToSpin_of_residualRow`** — the one theorem: a ∀-`p` supply of the
row discharges the deep KT §5 kernel-null binder `KernelReducesToSpin prov`. Pure wiring of banked
suppliers; zero new mathematical content.

**The substitution ledger** (what fell, and to what):

* `hasClass` (the deepest capstone atom) — REPLACED by `{z, hz, T, hdetAB}` via
  `hasClass_ofTransfer` (`PinPlusTraceCapstoneSeamTransfer`, #178): the controlled cylinder
  representative `capstoneCylChainT z` (named cross-product chain, not a `.choose` artifact) plus
  the BANKED disk detecting triple `diskDetectChain`/`_hc`/`_hdet`
  (`PinPlusTraceDiskCorePair`, #170) plus the chain-level seam-transfer datum
  `CapstoneSeamTransfer` plus the straddle detection `hdetAB`.
* `mv` (the MV cover row) — REPLACED by the `CapstoneMVTransferRow.ofPieces` inputs
  (`PinPlusTraceCapstoneMVPieces`, #175): the cover `A`/`B`/`hcov`, the two pinned piece homeos
  `eA`/`eB`, the overlap comparison triple `YAB`/`eAB`/`hYAB`, and the boundary comparison
  `YBd`/`eBd` + clopen two-closed-ends split `U`/`hU`/`M1`/`M2`/`e1`/`e2`.
* `dimeq14`/`dimeq23` (the two Betti equalities) — REPLACED by the two flip (right-side)
  nondegeneracies `nondeg14flip`/`nondeg23flip` via `capstone_dimeq14_of_flip`/
  `capstone_dimeq23_of_flip` (`PinPlusTraceCapstoneNumericsReduce`, #175 brick 4).
* `hwu` (the Wu vanishing) — REPLACED by the two Steenrod–Kronecker functional vanishings
  `hwf14`/`hwf23` via `capstone_hwu_of_steenrodKronecker` (`PinPlusTraceCapstoneNumericsReduce`,
  #181): the genuine `v₁(W) = 0` / `v₂(W) = 0` spin inputs, no `sqOp` gaming.

**Two wiring findings** (the consolidation's own discoveries, stated honestly):

1. **The controlled-representative route charges two NEW source certificates.**
   `hasClass_ofTransfer` requires `[Nonempty p'.1.M]` and `[PreconnectedSpace p'.1.M]` (the
   fundamental cycle `z` of the source lives on a nonempty connected closed 4-manifold) — neither
   is a field of `CapstoneAmbientSupplyWeldedMV` (which carries only `hsT2`) nor supplied by the
   `SingularManifold` instance stock (which gives `CompactSpace` and `ChartedSpace` for free). The
   residual row therefore carries `hsNe`/`hsConn` — atoms the seam-transfer reduction silently
   priced in; the builder owes a connected nonempty surgered representative.
2. **The packaged membrane datum does NOT absorb the general row's membrane atoms.**
   `TraceMembraneLeaves.ofTauMembraneWeldDatum` (`PinPlusCharPairEmptySourceRealization`, #183) is
   typed under `[IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)]` — the TERMINAL KRS step only. For the
   general per-`p` row (`0 < p.2.n`, source surface generally nonempty) the nine membrane atoms
   `real`/`htaylor`/`hlag`/`HAQ`/`weld`/`hQ`/`glueσ`/`glueτ`/`chartQ` remain irreducible and are
   kept verbatim.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneSupplyMV
import SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
import SKEFTHawking.PinPlusTraceCapstoneMVPieces
import SKEFTHawking.PinPlusTraceCapstoneNumericsReduce
import SKEFTHawking.PinPlusTraceDiskCorePair

open scoped Manifold
open Topology
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusTraceMembranePresented
open SKEFTHawking.PinPlusKTSurgeryTrace
open SKEFTHawking.PinPlusKTSurgeryTraceConsumers
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCohomologyMV
open SKEFTHawking.PinPlusTraceCapstoneMembraneWeld
open SKEFTHawking.PinPlusTraceCapstoneSupplyMV
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneMVPieces
open SKEFTHawking.PinPlusTraceCapstoneNumericsReduce
open SKEFTHawking.PinPlusTraceDiskCorePair

namespace SKEFTHawking.PinPlusTraceCapstoneResidualRow

noncomputable section

/-! ## §1. The derived deepest atom — `hasClass` from `{z, hz, T, hdetAB}` over the banked disk
triple. Stated once, consumed by the row's numerics field types. -/

section Derived

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The derived deepest atom** — the capstone `hasClass` from the residual atoms
`{z, hz, T, hdetAB}`, the disk detecting triple BANKED (`diskDetectChain`/`_hc`/`_hdet`). This is
`hasClass_ofTransfer` at `cHa := diskDetectChain`; it exists so the residual row's numerics field
types can name the ONE derived witness. -/
theorem residualHasClass (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    (T : CapstoneSeamTransfer s S hS φ hφ hφinj z diskDetectChain)
    (hdetAB : ∀ (w : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (hw : w ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
        w ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
        w ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({w}ᶜ) 3
        (closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
            (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
          + closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
            (3 + 2) diskDetectChain)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hw) (3 + 1)
          (hbd_ofTransfer s t S hS φ hφ hφinj cd hseam d T)) ≠ 0) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  hasClass_ofTransfer s t S hS φ hφ hφinj cd hseam d z hz
    diskDetectChain diskDetectChain_hc diskDetectChain_hdet T hdetAB

end Derived

variable {prov : CharPairWProviderPerOp (𝓡 4) 0}

/-! ## §2. THE RESIDUAL ROW — every genuinely-remaining atom, with provenance and builder
obligation per field. -/

/-- **THE KRS RESIDUAL ROW** — the single authoritative enumeration of what remains open on the
kernel-reduces-to-spin lane after ~15 waves of reductions. Every field is a genuinely-remaining
atom (documented with its provenance wave and what the builder owes); every reduced obligation of
`CapstoneAmbientSupplyWeldedMV` is DERIVED from these by `toSupplyMV`. No field is a completeness
Prop over the bordism group: the ∀-quantified fields (`hdetAB`, `hYAB`, `hwf14`/`hwf23`,
`glueσ`/`glueτ`) quantify only over points/degrees of the builder's own constructed objects. -/
structure KRSResidualRow (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) where
  /-- **[surgery data | #166 capstone opening]** the isotropic class to surger. -/
  x : Fin p.2.n → ZMod 2
  /-- **[surgery data | #166]** the class is nonzero. -/
  hx0 : x ≠ 0
  /-- **[surgery data | #166]** the framing obstruction vanishes. -/
  hxq : p.2.q.q x = 0
  /-- **[surgery data | #166]** the surgered representative. Builder owes: the KT surgery output. -/
  p' : StrMfd (pinPlusCharPairData prov).toTangentialData
  /-- **[surgery data | #166]** the KT surgery drops the enhancement rank by exactly 2. -/
  hrank : p'.2.n + 2 = p.2.n
  /-- **[source certificate | #166]** the source manifold is Hausdorff. -/
  hsT2 : T2Space p'.1.M
  /-- **[source certificate | NEW at consolidation (#186), priced in by #178]** the source manifold
  is nonempty — demanded by the controlled-representative route (the fundamental cycle `z`).
  Builder owes: a nonempty surgered representative. -/
  hsNe : Nonempty p'.1.M
  /-- **[source certificate | NEW at consolidation (#186), priced in by #178]** the source manifold
  is preconnected — demanded by the controlled-representative route (`ℤ/2` fundamental-class
  detection is per-component). Builder owes: a connected surgered representative (or a
  per-component refinement of the transfer). -/
  hsConn : PreconnectedSpace p'.1.M
  /-- **[attaching data | #166]** the attaching region `S ⊆ D⁵`. -/
  S : Set D5
  /-- **[attaching data | #166]** `S` is closed. -/
  hS : IsClosed S
  /-- **[attaching data | #166]** the attaching map `φ : S → M × I`. -/
  φ : ↥S → p'.1.M × Set.Icc (0 : ℝ) 1
  /-- **[attaching data | #166]** `φ` is continuous. -/
  hφ : Continuous φ
  /-- **[attaching data | #166]** `φ` is injective. -/
  hφinj : Function.Injective φ
  /-- **[seam collar | #173]** the seam-collar datum on the glued carrier. -/
  cd : SeamCollarDatum (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).carrier
  /-- **[seam collar | #173]** the seam containment. -/
  hseam : (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd
  /-- **[surgered end | #167]** the surgered-end datum (boundary-absorb certificates). -/
  d : SurgeredEndDatum p'.1 p.1 S hS φ hφ hφinj cd hseam
  /-- **[hasClass atom | #178 seam transfer]** a fundamental 4-cycle of the source. Builder owes: a
  cycle representative of `[M]`. -/
  z : cycles (TopCat.of p'.1.M) (2 + 2)
  /-- **[hasClass atom | #178]** `z` represents the mod-2 fundamental class. -/
  hz :
    letI := hsT2
    haveI := hsNe
    SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := p'.1.M)
      = Homology.mk (TopCat.of p'.1.M) (2 + 2) z
  /-- **[hasClass atom | #178]** the chain-level seam-transfer datum over the BANKED
  `diskDetectChain`: the top-face split, the disk-boundary split, and the literal seam-face
  transfer. THE genuinely φ-geometric atom. Builder owes: the two supports and the shared-face
  equality for the concrete attaching map. -/
  T :
    letI := hsT2
    CapstoneSeamTransfer p'.1 S hS φ hφ hφinj z diskDetectChain
  /-- **[hasClass atom | #178]** the straddle detection at seam-overlap points — the honest
  irreducible seam atom (fact (3) at `p := glued`). Builder owes: local detection of the glued
  controlled chain at points in `range fromCyl ∩ range fromHandle` off `∂W`. -/
  hdetAB :
    letI := hsT2
    ∀ (w : (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).carrier)
      (hw : w ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)),
      w ∈ Set.range (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).fromCyl →
      w ∈ Set.range (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).fromHandle →
      relClassOf (X := TopCat.of (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).carrier) ({w}ᶜ) 3
        (closedEmbeddingChain
            (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
            (3 + 2) (capstoneCylChainT p'.1 S hS φ hφ hφinj z)
          + closedEmbeddingChain
            (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
            (3 + 2) diskDetectChain)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hw) (3 + 1)
          (hbd_ofTransfer p'.1 p.1 S hS φ hφ hφinj cd hseam d T)) ≠ 0
  /-- **[MV cover atom | #175]** the cyl-side piece of the MV cover. -/
  A :
    letI := hsT2
    Set ↑(TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
  /-- **[MV cover atom | #175]** the handle-side piece of the MV cover. -/
  B :
    letI := hsT2
    Set ↑(TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
  /-- **[MV cover atom | #175]** the interiors of `A`, `B` cover `W`. -/
  hcov :
    letI := hsT2
    (⋃ U ∈ ({A, B} : Set (Set ↑(TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W))),
      interior U) = Set.univ
  /-- **[MV cover atom | #175, deferred to the Fable lane by #181]** the cyl-side piece homeo onto
  the construction's own cylinder. Builder owes: the thickened-piece retraction. -/
  eA :
    letI := hsT2
    ↑(sub A) ≃ₜ (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).B
  /-- **[MV cover atom | #175, deferred to the Fable lane by #181]** the handle-side piece homeo
  onto `D⁵`. -/
  eB :
    letI := hsT2
    ↑(sub B) ≃ₜ (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).Ha
  /-- **[MV cover atom | #175]** the seam-overlap comparison space. -/
  YAB : TopCat
  /-- **[MV cover atom | #175]** the overlap comparison homeo. Builder owes: the seam-zone product
  structure. -/
  eAB :
    letI := hsT2
    ↑(sub (A ∩ B)) ≃ₜ ↑YAB
  /-- **[MV cover atom | #175]** all-degree homology finiteness of the overlap comparison space
  (∀ over degrees of the builder's OWN chosen `YAB` — not a completeness Prop). -/
  hYAB : ∀ n, FiniteDimensional (ZMod 2) (Homology YAB n)
  /-- **[MV cover atom | #175]** the boundary comparison space. -/
  YBd : TopCat
  /-- **[MV cover atom | #175]** the boundary comparison homeo `∂W ≃ YBd`. -/
  eBd :
    letI := hsT2
    ↑(sub (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)) ≃ₜ ↑YBd
  /-- **[MV cover atom | #175]** the clopen split of the boundary comparison into the two ends. -/
  U : Set ↑YBd
  /-- **[MV cover atom | #175]** the split is clopen. -/
  hU : IsClopen U
  /-- **[MV cover atom | #175]** the first-end comparison manifold. -/
  M1 : Type
  /-- topology on `M1`. -/
  [instTopM1 : TopologicalSpace M1]
  /-- `M1` Hausdorff. -/
  [instT2M1 : T2Space M1]
  /-- `M1` compact. -/
  [instCompactM1 : CompactSpace M1]
  /-- `M1` a closed 4-manifold. -/
  [instChartM1 : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M1]
  /-- **[MV cover atom | #175]** the second-end comparison manifold. -/
  M2 : Type
  /-- topology on `M2`. -/
  [instTopM2 : TopologicalSpace M2]
  /-- `M2` Hausdorff. -/
  [instT2M2 : T2Space M2]
  /-- `M2` compact. -/
  [instCompactM2 : CompactSpace M2]
  /-- `M2` a closed 4-manifold. -/
  [instChartM2 : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M2]
  /-- **[MV cover atom | #175]** the first-end homeo (intended: `sub U ≃ M`). -/
  e1 : ↑(sub U) ≃ₜ M1
  /-- **[MV cover atom | #175]** the second-end homeo (intended: `sub Uᶜ ≃ M′`). -/
  e2 : ↑(sub Uᶜ) ≃ₜ M2
  /-- **[Lefschetz numerics | #166, kept]** `(1,4)` left Lefschetz non-degeneracy (typed at the
  DERIVED `hasClass`). Builder owes: cup-pairing injectivity on `H¹`. -/
  nondeg14 :
    letI := hsT2
    haveI := hsNe
    haveI := hsConn
    Function.Injective
      ⇑((relCupH14 (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (residualHasClass p'.1 p.1 S hS φ hφ hφinj cd hseam d z hz T
            hdetAB)).toRelFundClassDatum.mu)
  /-- **[Lefschetz numerics | NEW shape from #175 brick 4]** `(1,4)` flip (right-side)
  non-degeneracy — replaces the `dimeq14` Betti equality via `capstone_dimeq14_of_flip`. -/
  nondeg14flip :
    letI := hsT2
    haveI := hsNe
    haveI := hsConn
    Function.Injective
      ⇑((relCupH14 (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (residualHasClass p'.1 p.1 S hS φ hφ hφinj cd hseam d z hz T
            hdetAB)).toRelFundClassDatum.mu).flip
  /-- **[Lefschetz numerics | #166, kept]** `(2,3)` left Lefschetz non-degeneracy. -/
  nondeg23 :
    letI := hsT2
    haveI := hsNe
    haveI := hsConn
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (residualHasClass p'.1 p.1 S hS φ hφ hφinj cd hseam d z hz T
            hdetAB)).toRelFundClassDatum.mu)
  /-- **[Lefschetz numerics | NEW shape from #175 brick 4]** `(2,3)` flip non-degeneracy —
  replaces `dimeq23`. -/
  nondeg23flip :
    letI := hsT2
    haveI := hsNe
    haveI := hsConn
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (residualHasClass p'.1 p.1 S hS φ hφ hφinj cd hseam d z hz T
            hdetAB)).toRelFundClassDatum.mu).flip
  /-- **[spin content | #181]** the `(1,4)` Steenrod–Kronecker functional vanishing
  `⟨relSq¹ ·, [W,∂W]⟩ = 0` — the genuine `v₁(W) = 0` spin input (no `sqOp` gaming; see
  `wuFunctional_ofRelFund14`). Builder owes: the ends' `PinPlusCertK` transport across the glue. -/
  hwf14 :
    letI := hsT2
    haveI := hsNe
    haveI := hsConn
    wuFunctional
      (LefschetzWuDatum.ofRelFund14
        (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (residualHasClass p'.1 p.1 S hS φ hφ hφinj cd hseam d z hz T
            hdetAB)).toRelFundClassDatum
        (CapstoneCohomologyMVDatum.toFindimAbs14 p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (letI := instTopM1; letI := instT2M1; letI := instCompactM1; letI := instChartM1
           letI := instTopM2; letI := instT2M2; letI := instCompactM2; letI := instChartM2
           (CapstoneMVTransferRow.ofPieces p'.1 p.1 S hS φ hφ hφinj cd hseam d A B hcov eA eB
             YAB eAB hYAB YBd eBd U hU e1 e2).toMVDatum))
        (CapstoneCohomologyMVDatum.toFindimRel14 p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (letI := instTopM1; letI := instT2M1; letI := instCompactM1; letI := instChartM1
           letI := instTopM2; letI := instT2M2; letI := instCompactM2; letI := instChartM2
           (CapstoneMVTransferRow.ofPieces p'.1 p.1 S hS φ hφ hφinj cd hseam d A B hcov eA eB
             YAB eAB hYAB YBd eBd U hU e1 e2).toMVDatum))
        nondeg14
        (capstone_dimeq14_of_flip p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (residualHasClass p'.1 p.1 S hS φ hφ hφinj cd hseam d z hz T hdetAB)
          (letI := instTopM1; letI := instT2M1; letI := instCompactM1; letI := instChartM1
           letI := instTopM2; letI := instT2M2; letI := instCompactM2; letI := instChartM2
           (CapstoneMVTransferRow.ofPieces p'.1 p.1 S hS φ hφ hφinj cd hseam d A B hcov eA eB
             YAB eAB hYAB YBd eBd U hU e1 e2).toMVDatum)
          nondeg14 nondeg14flip)) = 0
  /-- **[spin content | #181]** the `(2,3)` Steenrod–Kronecker functional vanishing
  `⟨relSq² ·, [W,∂W]⟩ = 0` — the genuine `v₂(W) = 0` spin input. -/
  hwf23 :
    letI := hsT2
    haveI := hsNe
    haveI := hsConn
    wuFunctional
      (LefschetzWuDatum.ofRelFund23
        (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (residualHasClass p'.1 p.1 S hS φ hφ hφinj cd hseam d z hz T
            hdetAB)).toRelFundClassDatum
        (CapstoneCohomologyMVDatum.toFindimAbs23 p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (letI := instTopM1; letI := instT2M1; letI := instCompactM1; letI := instChartM1
           letI := instTopM2; letI := instT2M2; letI := instCompactM2; letI := instChartM2
           (CapstoneMVTransferRow.ofPieces p'.1 p.1 S hS φ hφ hφinj cd hseam d A B hcov eA eB
             YAB eAB hYAB YBd eBd U hU e1 e2).toMVDatum))
        (CapstoneCohomologyMVDatum.toFindimRel23 p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (letI := instTopM1; letI := instT2M1; letI := instCompactM1; letI := instChartM1
           letI := instTopM2; letI := instT2M2; letI := instCompactM2; letI := instChartM2
           (CapstoneMVTransferRow.ofPieces p'.1 p.1 S hS φ hφ hφinj cd hseam d A B hcov eA eB
             YAB eAB hYAB YBd eBd U hU e1 e2).toMVDatum))
        nondeg23
        (capstone_dimeq23_of_flip p'.1 p.1 S hS φ hφ hφinj cd hseam d
          (residualHasClass p'.1 p.1 S hS φ hφ hφinj cd hseam d z hz T hdetAB)
          (letI := instTopM1; letI := instT2M1; letI := instCompactM1; letI := instChartM1
           letI := instTopM2; letI := instT2M2; letI := instCompactM2; letI := instChartM2
           (CapstoneMVTransferRow.ofPieces p'.1 p.1 S hS φ hφ hφinj cd hseam d A B hcov eA eB
             YAB eAB hYAB YBd eBd U hU e1 e2).toMVDatum)
          nondeg23 nondeg23flip)) = 0
  /-- **[membrane | #168/#172, irreducible in general (finding 2)]** the DERIVED-basis membrane
  realization. -/
  real :
    letI := hsT2
    GeoRealizationTied (TopCat.of p'.2.surf.M) (TopCat.of p.2.surf.M) p'.2.basis p.2.basis
  /-- **[membrane | #168]** the membrane kernel is Taylor-leg-vanishing. -/
  htaylor : TaylorLegVanishes p'.2.q p.2.q (real.toMembrane p'.2.q p.2.q).L
  /-- **[membrane | #168]** the membrane kernel is jointly Lagrangian. -/
  hlag : JointLagrangian p'.2.q p.2.q (real.toMembrane p'.2.q p.2.q).L
  /-- **[membrane | #172]** the membrane presented as a handle attachment. -/
  HAQ : HandleAttachment.{0, 0}
  /-- **[membrane | #172]** the membrane weld into the actual carrier. -/
  weld :
    letI := hsT2
    HandleAttachment.Weld HAQ (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj)
  /-- **[membrane | #172]** the membrane presentation homeomorphism. -/
  hQ : (↑real.Q : Type) ≃ₜ HAQ.carrier
  /-- **[membrane | #172]** glue (σ-end), welded form. -/
  glueσ :
    letI := hsT2
    ∀ y : ↑(sub real.U),
      weld.carrierMap (hQ (real.ι (subInclCM real.U y)))
        = (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).e (Sum.inl (p'.2.emb (real.homσ y)))
  /-- **[membrane | #172]** glue (τ-end), welded form. -/
  glueτ :
    letI := hsT2
    ∀ y : ↑(sub real.Uᶜ),
      weld.carrierMap (hQ (real.ι (subInclCM real.Uᶜ y)))
        = (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).e (Sum.inr (p.2.emb (real.homτ y)))
  /-- **[membrane | #172]** `Q` charts over the 3-dim membrane model. -/
  chartQ : ChartedSpace MembraneModel ↑real.Q

/-! ## §3. The row rebuilds the MV'd supply — every reduced obligation DERIVED. -/

/-- **The residual row rebuilds the MV'd welded supply** — `hasClass` from the transfer route,
`mv` from the piece row, the two Betti equalities from the flip nondegeneracies, the Wu vanishing
from the two Steenrod–Kronecker functional vanishings; everything else verbatim. -/
def KRSResidualRow.toSupplyMV
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (R : KRSResidualRow prov p) : CapstoneAmbientSupplyWeldedMV prov p where
  x := R.x
  hx0 := R.hx0
  hxq := R.hxq
  p' := R.p'
  hrank := R.hrank
  hsT2 := R.hsT2
  S := R.S
  hS := R.hS
  φ := R.φ
  hφ := R.hφ
  hφinj := R.hφinj
  cd := R.cd
  hseam := R.hseam
  d := R.d
  hasClass :=
    letI := R.hsT2
    haveI := R.hsNe
    haveI := R.hsConn
    residualHasClass R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d R.z R.hz R.T R.hdetAB
  mv :=
    letI := R.hsT2
    letI := R.instTopM1; letI := R.instT2M1; letI := R.instCompactM1; letI := R.instChartM1
    letI := R.instTopM2; letI := R.instT2M2; letI := R.instCompactM2; letI := R.instChartM2
    (CapstoneMVTransferRow.ofPieces R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d
      R.A R.B R.hcov R.eA R.eB R.YAB R.eAB R.hYAB R.YBd R.eBd R.U R.hU R.e1 R.e2).toMVDatum
  nondeg14 := R.nondeg14
  dimeq14 :=
    letI := R.hsT2
    haveI := R.hsNe
    haveI := R.hsConn
    letI := R.instTopM1; letI := R.instT2M1; letI := R.instCompactM1; letI := R.instChartM1
    letI := R.instTopM2; letI := R.instT2M2; letI := R.instCompactM2; letI := R.instChartM2
    capstone_dimeq14_of_flip R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d
      (residualHasClass R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d R.z R.hz R.T
        R.hdetAB)
      ((CapstoneMVTransferRow.ofPieces R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d
        R.A R.B R.hcov R.eA R.eB R.YAB R.eAB R.hYAB R.YBd R.eBd R.U R.hU R.e1 R.e2).toMVDatum)
      R.nondeg14 R.nondeg14flip
  nondeg23 := R.nondeg23
  dimeq23 :=
    letI := R.hsT2
    haveI := R.hsNe
    haveI := R.hsConn
    letI := R.instTopM1; letI := R.instT2M1; letI := R.instCompactM1; letI := R.instChartM1
    letI := R.instTopM2; letI := R.instT2M2; letI := R.instCompactM2; letI := R.instChartM2
    capstone_dimeq23_of_flip R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d
      (residualHasClass R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d R.z R.hz R.T
        R.hdetAB)
      ((CapstoneMVTransferRow.ofPieces R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d
        R.A R.B R.hcov R.eA R.eB R.YAB R.eAB R.hYAB R.YBd R.eBd R.U R.hU R.e1 R.e2).toMVDatum)
      R.nondeg23 R.nondeg23flip
  hwu :=
    letI := R.hsT2
    haveI := R.hsNe
    haveI := R.hsConn
    letI := R.instTopM1; letI := R.instT2M1; letI := R.instCompactM1; letI := R.instChartM1
    letI := R.instTopM2; letI := R.instT2M2; letI := R.instCompactM2; letI := R.instChartM2
    capstone_hwu_of_steenrodKronecker R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d
      (residualHasClass R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d R.z R.hz R.T
        R.hdetAB)
      ((CapstoneMVTransferRow.ofPieces R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d
        R.A R.B R.hcov R.eA R.eB R.YAB R.eAB R.hYAB R.YBd R.eBd R.U R.hU R.e1 R.e2).toMVDatum)
      R.nondeg14
      (capstone_dimeq14_of_flip R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d
        (residualHasClass R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d R.z R.hz R.T
          R.hdetAB)
        ((CapstoneMVTransferRow.ofPieces R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d
          R.A R.B R.hcov R.eA R.eB R.YAB R.eAB R.hYAB R.YBd R.eBd R.U R.hU R.e1 R.e2).toMVDatum)
        R.nondeg14 R.nondeg14flip)
      R.nondeg23
      (capstone_dimeq23_of_flip R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d
        (residualHasClass R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d R.z R.hz R.T
          R.hdetAB)
        ((CapstoneMVTransferRow.ofPieces R.p'.1 p.1 R.S R.hS R.φ R.hφ R.hφinj R.cd R.hseam R.d
          R.A R.B R.hcov R.eA R.eB R.YAB R.eAB R.hYAB R.YBd R.eBd R.U R.hU R.e1 R.e2).toMVDatum)
        R.nondeg23 R.nondeg23flip)
      R.hwf14 R.hwf23
  real := R.real
  htaylor := R.htaylor
  hlag := R.hlag
  HAQ := R.HAQ
  weld := R.weld
  hQ := R.hQ
  glueσ := R.glueσ
  glueτ := R.glueτ
  chartQ := R.chartQ

/-! ## §4. THE ONE THEOREM — the residual row supply discharges the KRS binder. -/

/-- **THE KRS SUPPLY, CONSOLIDATED.** A ∀-`p` supply of the residual row — one
`KRSResidualRow prov p` per non-spin brown-0 representative, every field a genuinely-remaining
atom with named provenance — discharges the deep KT §5 kernel-null binder
`KernelReducesToSpin prov`. Pure wiring of the banked suppliers; the single authoritative
statement of what remains open on the KRS lane. -/
theorem kernelReducesToSpin_of_residualRow
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n → KRSResidualRow prov p) :
    KernelReducesToSpin prov :=
  kernelReducesToSpin_of_capstoneWeldedMVSupply
    (fun p hbrown hpos => (H p hbrown hpos).toSupplyMV)

/-- **The Brown fence persists at the consolidated grade** — no instantiation of the residual row
can launder a Brown-violating surgery step. -/
theorem KRSResidualRow.brown_eq
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (R : KRSResidualRow prov p) :
    R.p'.2.q.brown = p.2.q.brown :=
  R.toSupplyMV.brown_eq

end

/-! ## §5. THE ROUND-12 GATE INVENTORY — every consumption-relevant shape introduced since
round 11, flagged **[∀-Prop]** (completeness-adjacent — a universally-quantified Prop consumed as
a hypothesis; the gate must adjudicate whether the quantifier ranges over the builder's own
constructed object, which is benign, or over the bordism group / all representatives, which is
the completeness-Prop exploit surface) vs **[data]** (Type-valued constructed data — the gates'
preferred currency).

### The trace leaf rows' evolutions (the supply spine)
* `CapstoneAmbientSupplyWelded` (`PinPlusTraceCapstoneMembraneWeld`) — **[data]** row; carrier
  presentation `HAW`/`hW` discharged free.
* `CapstoneAmbientSupplyWeldedMV` (`PinPlusTraceCapstoneSupplyMV`, #175 brick 3) — **[data]** row;
  four findim atoms → one `mv` field.
* `KRSResidualRow` (THIS MODULE, #186) — **[data]** row; `hasClass`/`mv`/`dimeq*`/`hwu` all
  derived. Its ∀-fields (`hdetAB` over carrier points, `hYAB` over degrees, `glueσ`/`glueτ` over
  membrane points, `hwf14`/`hwf23` functional equations) are object-local — quantified over the
  builder's own constructed spaces, NOT over the bordism group. Gate should confirm exactly that.
* `TraceRelFundLeaves.ofCapstone` / `TraceWAdmLeaves.ofRelFundLeaves` /
  `TraceMembraneLeaves.ofCapstoneWelded` — **[data]** constructors (leaf rows from the supply).

### The transfer / corrector data (the hasClass lane)
* `SeamCollarChainDatum` (`SingularRelativeCoverMVSeam`, #173) — **[data]**; the honest form after
  chain-level cancellation was PROVEN false for `.choose` representatives.
* `SeamCollarChainDatum.ofCorrector_ofHbd` + `hasClass_ofCorrector`
  (`SingularRelativeCoverMVSeamCorrector`, #176) — corrector consumption: `p` **[data]** chain +
  facts `hpS` **[Prop, object-local]**, `hagree` **[Prop, object-local]**, `hp_det`
  **[∀-Prop over carrier points — object-local]**.
* `CapstoneSeamTransfer` (`PinPlusTraceCapstoneSeamTransfer`, #178) — **[data]**; the two splits +
  the literal seam-face transfer; THE φ-geometric atom. `hasClass_ofTransfer` /
  `hasClass_ofTransferCorrector` are its consumers.

### The controlled representatives (the `.choose` verdict: these ARE the route)
* `crossChain z` detecting triple (`…SeamTransfer` §1) + `capstoneCylChainT` (§2) — **[data]**
  NAMED chains with proven `hc`/`hdet` legs; kill the `.choose`-opacity wall.
* `diskDetectChain` + `_hc`/`_hdet` (`PinPlusTraceDiskCorePair`, #170) — **[data]** BANKED
  parameterless canonical chain (the `.choose` of the PROVEN `hasRelFundClass_D5` — a legitimate
  choice from an unconditional existence, not an unexamined hypothesis).

### The MV / numerics shapes
* `CapstoneCohomologyMVDatum` (`PinPlusTraceCapstoneCohomologyMV`, #175 brick 1–2) — **[data]**
  cover + four all-degree finiteness fields (∀ over ℕ degrees — object-local).
* `CapstoneMVTransferRow` + `.ofPieces` (`PinPlusTraceCapstoneMVPieces`) — **[data]**; four
  comparison triples; cyl/disk targets pinned, stock auto-discharged.
* `capstone_dimeq14_of_flip` / `capstone_dimeq23_of_flip` / `capstone_hwu_of_steenrodKronecker`
  (`PinPlusTraceCapstoneNumericsReduce`, #175 brick 4 + #181) — suppliers; inputs are flip
  nondegeneracies **[Prop, object-local]** + functional vanishings **[Prop, object-local]**.

### The packaged membrane datum (terminal step ONLY)
* `TauMembraneWeldDatum` + `TraceMembraneLeaves.ofTauMembraneWeldDatum` + `brown_zero` /
  `brown_preserved` (`PinPlusCharPairEmptySourceRealization`, #183) — **[data]** package under
  `[IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)]`; its `hq`/`hlagK` are ∀-Props over the datum's OWN
  bounding kernel (object-local, and PROVEN load-bearing via the `brown_zero` anti-vacuity
  bridge). ⚠ Terminal-step-only — does NOT absorb the general row's membrane atoms (finding 2).

### The Novikov substrate + atoms (the σ-descent lane)
* `NovikovRealPairLES` (`PinPlusKTSpinSigmaNovikovRealSubstrate`, #182) — **[data]** per-boundary-
  matrix ℝ-substrate; `latticeSig_eq_of_realPairLES` = the `hcob` sibling engine.
* `NovikovBoundaryRestriction` (`PinPlusKTSpinSigmaNovikovOpener`, #180) — **[data]** per-matrix.
* `NovikovHalfDimAtom` (`…NovikovOpener`) — ⚠ **[∀-Prop — COMPLETENESS-ADJACENT]**: quantifies
  over ALL data-bordant pairs `p q` of the spin-empty substrate. Gate must vet any claimed
  discharge for the free-binder exploit.
* `NovikovCoIsoAtom` (`PinPlusKTSpinSigmaNovikovHalfDim`, #174/#177) — ⚠ **[∀-Prop —
  COMPLETENESS-ADJACENT]**: same ∀ data-bordant-pairs shape (∃ isotropic co-isotropic `L`).
* `SpinSigmaAtoms` (`PinPlusKTSpinSigmaAtom`) — **[data]** bundle, but its `fc`/`B`/`wu`/`pd`
  fields are Π-over-ALL-representatives function fields — ⚠ functionally completeness-adjacent
  (a total assignment over `StrMfd`, not a per-object datum). Gate should treat any claimed
  inhabitation with the same suspicion as a ∀-Prop.

### The collapse atom (the sector-geometric lane)
* `RankZeroCollapsesToEmptySurf` (`PinPlusKTSectorGeometricReduce`, #179) — ⚠ **[∀-Prop —
  COMPLETENESS-ADJACENT]**: ∀ spin-sector representative, ∃ one-step collapse bordism. Honest and
  strictly-stronger per the round-9 re-triage, but a gate-level ∀ nonetheless.

### The canonical bundle's disclosure fields
* `CanonicalSpinSigmaAtoms` (`PinPlusKTSpinSigmaCanonicalBundle`) — extends `SpinSigmaAtoms` with
  `fc_sum`/`B_sum` — ⚠ **[∀-Prop over pairs]**, but DISCLOSURE equalities (coherence of the
  bundle's own canonical choices, not new geometric content); discharges `InterMatrixBlockAtom`
  and σ-additivity as THEOREMS, reducing the σ-descent to `hbord` alone.

### The dual-spin row
* `PinPlusKTDualSpinConstruction` (#180) — the orientability adjudication; the row =
  {transversal V **[data]**, spin vanishings **[Prop, object-local]**, `hcob` **[∀-Prop —
  COMPLETENESS-ADJACENT]** (= the Novikov sibling; see `latticeSig_eq_of_realPairLES`)}.
-/

end SKEFTHawking.PinPlusTraceCapstoneResidualRow
