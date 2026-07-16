/-
# Phase 5q.H close-out — THE SEAM-TRANSFER SUPPLY: `htransfer` CONSTRUCTED, the capstone `hasClass`
# reduced to the two co-adapted splits + the straddle detection.

The Fable layer (`PinPlusTraceCapstoneSeamTransfer.lean`) reduced the welded-capstone `hasClass`
existence to `hasClass_ofTransfer {z, hz, the disk triple, T : CapstoneSeamTransfer, hdetAB}`, and
flagged the transfer datum's **literal seam-face transfer** `htransfer`
(`push_fromCyl wAtt = push_fromHandle uAtt`) as "THE genuinely φ-geometric atom". This module
**discharges that atom** and re-packages the reduction:

* **§0 — the closed-embedding pushforward IS a plain pushforward.**
  `closedEmbeddingChain_eq_mapChain`: `closedEmbeddingChain hj n c = mapChain ⟨j, hj.continuous⟩ n c`
  (the corestriction-then-include equals the full pushforward, via `mapChain_ambIncl` + `mapChain_comp`).
* **§1 — the glue transfer, constructed.** `closedEmbeddingChain_mapChain_glue_eq`: for a common
  source chain `c` and two legs `g₁`/`g₂` into the two pieces that agree after pushing
  (`⟨j₁⟩∘g₁ = ⟨j₂⟩∘g₂`), the two closed-embedding pushforwards of `g₁ c`/`g₂ c` agree. This is the
  chain-level `HandleAttachment.glue` computation — a mapChain-naturality identity, NOT an atom.
* **§2 — the transfer datum from a common seam chain (`htransfer` GONE).**
  `CapstoneSeamTransferSeam` carries a single seam chain `cSeam : SingularChain ↥S (3+1)` plus the
  two co-adapted split-remainders `wOut`/`vOut` (top-face un-attached / free-sphere) with their two
  split equations (`z@⊤ = φ_# cSeam + wOut`, `∂cHa = incl_# cSeam + vOut`) and the two supports.
  `toTransfer` produces the full `CapstoneSeamTransfer` with `wAtt := φ_# cSeam`, `uAtt := incl_# cSeam`,
  and `htransfer` DISCHARGED from §1 (`fromCyl ∘ φ = fromHandle ∘ incl` — the glue).
* **§3 — the capstone `hasClass` field supplier + the narrowed residual.**
  `CapstoneSeamTransferResidual` bundles the exact remaining inputs of `hasClass_ofTransfer` — the
  banked fundamental cycle `{z, hz}`, the banked disk detecting triple (`diskDetectChain`), the
  seam-transfer core `{cSeam, wOut/vOut splits}` (`htransfer`-free), and the straddle detection
  `hdetAB` — and `toHasClass` FIRES `hasClass_ofTransfer`, landing the exact
  `CapstoneAmbientSupplyWeldedMV.hasClass` field type. So the deepest capstone atom, for connected
  `s.M`, is exactly `{a fundamental cycle of M, the two co-adapted seam splits, the straddle
  detection}` — the literal transfer no longer among the residuals.

**Dimension discipline.** `M` a closed source 4-manifold; `z` a 4-cycle; the seam chain `cSeam` and
the split-remainders `wOut`/`vOut` are 4-chains (degree `3+1`); the piece chains 5-chains; detection
in local degree `3`.

**Fences.** No collar theorem; the two seam SPLITS (`hsplit`/`hsplitHa`) and the straddle detection
`hdetAB` remain the honest co-adapted geometric residuals (they encode the subdivision/collar
adaptation of `z` and `cHa` to the attaching map). The controlled representatives are the route —
never the opaque `.choose` (SETTLED_FORKS `capstone-choose-representative-corrector-uninhabitable`).

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project
axiom, no `native_decide`, no `maxHeartbeats`.
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
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlue
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
open SKEFTHawking.PinPlusTraceDiskCorePair
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer

namespace SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply

noncomputable section

/-! ## §0. The closed-embedding pushforward is a plain pushforward. -/

section GenericBridge

variable {P : Type} [TopologicalSpace P] {Wc : Type} [TopologicalSpace Wc]

/-- **The closed-embedding pushforward equals the full singular pushforward.** `closedEmbeddingChain`
corestricts along the embedding homeomorphism and then includes; that composite is exactly the plain
`mapChain` of the full embedding map (`mapChain_ambIncl` bridges `chainIncl` to `mapChain (ambIncl)`,
then `mapChain_comp` composes). The clean form that turns `htransfer` into a naturality identity. -/
theorem closedEmbeddingChain_eq_mapChain {j : P → Wc} (hj : Topology.IsEmbedding j) (n : ℕ)
    (c : SingularChain (TopCat.of P) n) :
    closedEmbeddingChain hj n c
      = mapChain (X := TopCat.of P) (Y := TopCat.of Wc) ⟨j, hj.continuous⟩ n c := by
  rw [closedEmbeddingChain, ← mapChain_ambIncl, ← mapChain_comp]
  rfl

end GenericBridge

/-! ## §1. The glue transfer — a mapChain-naturality identity, not an atom. -/

section GenericGlue

variable {Q : Type} [TopologicalSpace Q] {P₁ P₂ Wc : Type}
  [TopologicalSpace P₁] [TopologicalSpace P₂] [TopologicalSpace Wc]

/-- **The chain-level glue transfer.** Two pieces `P₁`/`P₂` closed-embedded into `Wc` by `j₁`/`j₂`,
a common source chain `c` on `Q`, and two legs `g₁ : Q → P₁`, `g₂ : Q → P₂` whose post-compositions
into `Wc` agree (`j₁ ∘ g₁ = j₂ ∘ g₂` — the `HandleAttachment.glue` identity). Then the two
closed-embedding pushforwards of `g₁_# c` and `g₂_# c` are literally equal. Both reduce to
`mapChain (j₁ ∘ g₁) c = mapChain (j₂ ∘ g₂) c` (via §0 + `mapChain_comp`), collapsed by the leg
agreement. This discharges `CapstoneSeamTransfer.htransfer` for seam-chain-derived faces. -/
theorem closedEmbeddingChain_mapChain_glue_eq {j₁ : P₁ → Wc} (hj₁ : Topology.IsEmbedding j₁)
    {j₂ : P₂ → Wc} (hj₂ : Topology.IsEmbedding j₂)
    (g₁ : C(TopCat.of Q, TopCat.of P₁)) (g₂ : C(TopCat.of Q, TopCat.of P₂))
    (hcomp : (⟨j₁, hj₁.continuous⟩ : C(TopCat.of P₁, TopCat.of Wc)).comp g₁
        = (⟨j₂, hj₂.continuous⟩ : C(TopCat.of P₂, TopCat.of Wc)).comp g₂)
    (n : ℕ) (c : SingularChain (TopCat.of Q) n) :
    closedEmbeddingChain hj₁ n (mapChain g₁ n c) = closedEmbeddingChain hj₂ n (mapChain g₂ n c) := by
  rw [closedEmbeddingChain_eq_mapChain, closedEmbeddingChain_eq_mapChain,
    ← mapChain_comp, ← mapChain_comp, hcomp]

end GenericGlue

/-! ## §2. The transfer datum from a common seam chain — `htransfer` discharged. -/

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- The cylinder-side seam leg `↥S → s.M × I`, the attaching map as a bundled continuous map into the
cylinder end `cyl (TopCat.of s.M)` (`.B` defeq). -/
def seamLegCyl : C(TopCat.of ↥S, cyl (TopCat.of s.M)) := ⟨φ, hφ⟩

/-- The handle-side seam leg `↥S → D⁵ = Ha`, the closed-subtype inclusion of the attaching region,
typed at the handle end `(ktHandleAttachment …).Ha` (defeq `D⁵`). -/
def seamLegHa : C(TopCat.of ↥S, TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- **The seam core of the transfer datum** — the `htransfer`-free presentation. A single seam chain
`cSeam` on the attaching region `↥S`, together with the two co-adapted split-remainders `wOut`
(un-attached top face) and `vOut` (free boundary sphere) and their split equations. The attached
faces `wAtt`/`uAtt` are NOT carried — they are forced to be `cSeam` pushed along the two seam legs,
so their literal transfer is automatic (§1). -/
structure CapstoneSeamTransferSeam (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)) where
  /-- the common seam chain on the attaching region `↥S` (degree `3+1`). -/
  cSeam : SingularChain (TopCat.of ↥S) (3 + 1)
  /-- the un-attached part of the cylinder's top face `z@⊤`. -/
  wOut : SingularChain (cyl (TopCat.of s.M)) (3 + 1)
  /-- the top-face split: `z@⊤ = (seam leg)_# cSeam + wOut`. -/
  hsplit : mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
      (z : SingularChain (TopCat.of s.M) (3 + 1))
    = mapChain (seamLegCyl s S φ hφ) (3 + 1) cSeam + wOut
  /-- the un-attached part is supported in the un-attached top face `M × {⊤} ∖ range φ`. -/
  hwOut : wOut ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1)
  /-- the free-sphere part of the disk boundary `∂cHa`. -/
  vOut : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
  /-- the disk-boundary split: `∂cHa = (seam leg)_# cSeam + vOut`. -/
  hsplitHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
    = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cSeam + vOut
  /-- the free-sphere part is supported in the free boundary sphere `S⁴ ∖ S`. -/
  hvOut : vOut ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1)

/-- **The seam core builds the full transfer datum — `htransfer` DISCHARGED.** The attached faces are
`wAtt := (φ-leg)_# cSeam`, `uAtt := (incl-leg)_# cSeam`; their literal transfer
`push_fromCyl wAtt = push_fromHandle uAtt` is the chain-level `HandleAttachment.glue`
(`fromCyl ∘ φ = fromHandle ∘ incl`), landed by `closedEmbeddingChain_mapChain_glue_eq` (§1). The two
splits and the two supports pass through. So `CapstoneSeamTransfer` reduces to the seam core: the
literal transfer is no longer a residual. -/
def CapstoneSeamTransferSeam.toTransfer
    {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (R : CapstoneSeamTransferSeam s S hS φ hφ hφinj z cHa) :
    CapstoneSeamTransfer s S hS φ hφ hφinj z cHa where
  wAtt := mapChain (seamLegCyl s S φ hφ) (3 + 1) R.cSeam
  wOut := R.wOut
  hsplit := R.hsplit
  hwOut := R.hwOut
  uAtt := mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) R.cSeam
  vOut := R.vOut
  hsplitHa := R.hsplitHa
  hvOut := R.hvOut
  htransfer :=
    closedEmbeddingChain_mapChain_glue_eq
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
      (seamLegCyl s S φ hφ) (seamLegHa s S hS φ hφ hφinj)
      (ContinuousMap.ext (fun a => (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a))
      (3 + 1) R.cSeam

/-! ## §3. The capstone `hasClass` field supplier + the narrowed residual. -/

/-- **The narrowed capstone residual — the exact remaining inputs of `hasClass_ofTransfer`.** For
connected `s.M`, bundles the honest atoms left after the literal transfer is discharged (§2): the
banked fundamental cycle `{z, hz}` of the closed source 4-manifold `M`, the seam-transfer core
`seam` (the common seam chain + the two co-adapted splits + supports; `htransfer`-free), over the
banked disk detecting chain `diskDetectChain`, and the straddle detection `hdetAB` at the seam. No
completeness Prop; the literal transfer is no longer among the residuals. -/
structure CapstoneSeamTransferResidual where
  /-- a fundamental cycle of the closed source 4-manifold `M` (banked from the connected engine). -/
  z : cycles (TopCat.of s.M) (2 + 2)
  /-- `z` represents the fundamental class. -/
  hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z
  /-- the `htransfer`-free seam-transfer core over the banked disk detecting chain. -/
  seam : CapstoneSeamTransferSeam s S hS φ hφ hφinj z diskDetectChain
  /-- the overlap-zone straddle detection: the glued (controlled cylinder ⊕ banked disk) chain
  detects the local generator at every seam-collar point off `∂W` (the honest irreducible seam atom;
  `hbd` supplied by the constructed `hbd_ofTransfer` of `seam.toTransfer`). -/
  hdetAB : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
      (closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 2) diskDetectChain)
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1)
        (hbd_ofTransfer s t S hS φ hφ hφinj cd hseam d
          (CapstoneSeamTransferSeam.toTransfer s S hS φ hφ hφinj seam))) ≠ 0

/-- **The narrowed residual supplies the capstone `hasClass` field.** Fires `hasClass_ofTransfer`
with the banked disk detecting triple (`diskDetectChain`/`_hc`/`_hdet`), the transfer datum
`seam.toTransfer` (its `htransfer` discharged in §2), and the straddle detection. Its output is
exactly the type of `CapstoneAmbientSupplyWeldedMV.hasClass` (with `s := p'.1`, `t := p.1`). So the
deepest capstone atom reduces, for connected `s.M`, to inhabiting `CapstoneSeamTransferResidual` —
`{a fundamental cycle of M, the two co-adapted seam splits, the straddle detection}`, the literal
transfer eliminated. -/
def CapstoneSeamTransferResidual.toHasClass
    (R : CapstoneSeamTransferResidual s t S hS φ hφ hφinj cd hseam d) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  hasClass_ofTransfer s t S hS φ hφ hφinj cd hseam d R.z R.hz
    diskDetectChain diskDetectChain_hc diskDetectChain_hdet
    (CapstoneSeamTransferSeam.toTransfer s S hS φ hφ hφinj R.seam)
    R.hdetAB

end

end SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
