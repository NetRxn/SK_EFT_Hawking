/-
# Phase 5q.H (#212) — THE COLLAR-PAIR PRODUCER (`CollarPairBuild → CapstoneSeamCorrectorT`)

The **producer half** of the round-13 gate's 8-point frozen specification. The consumer half
(`CapstoneSeamCorrectorT` + its derived `toHasClass`) landed in `PinPlusTraceCapstoneCorrector`
(`ba271a11`); this module supplies the inspectable split data it is fed from, and PROVES the
producer — so the capstone `hasClass` is now reachable end-to-end from collar-pair data, with
nothing routed through the settled-dead `CapstoneSeamTransfer`.

## What is built

* **`CollarPairBuild`** (§2) — the frozen inspectable input: a fundamental cycle `{z, hz}`; the
  **#210 collar-pair split** (a shrunk core `K`, the shared 4-dimensional seam core `cCore`, the
  two co-adapted subdivision splits `hctrlC`/`hctrlH`, the two remainders supported off `K`
  (`houtC`/`houtH` — `U₂ = topface ∖ K`, never the refuted `Aᶜ`), and the collar-annulus weld
  `houtPair`); the subdivision **bridge** back to the frozen glued chain; the ambient **relative MV
  partition** (`near`/`away` with both relative-cycle corrections); the anti-fake tether
  **`hcoreHit`**; and the seam straddle-detection atom **`hq0det`**.
* **`CollarPairBuild.corrector`** (§3) — the corrector chain as a DEFINITION of the split data
  (`near` corrected by the subdivision/bridge prisms). It is never a field, so no independently
  supplied corrector can be smuggled in (gate spec 3 + 8).
* **`q0_eq_corrector_add_away`** — the central identity `q₀ z = corrector + away`, from which all
  five corrector facts are read off.
* **`correctorT_of_collarPair`** (§4) — THE PRODUCER, and **`hasClass_ofCollarPair`** — the
  composite whose conclusion is the exact `CapstoneAmbientSupply.hasClass` field type.

## Gate-spec compliance

Spec 1 (no `CapstoneSeamCollarPair` supply field — no such structure here); spec 2 (nothing routes
through `CapstoneSeamTransfer` / `hbd_ofTransfer` / `hasClass_ofTransferCorrector`); spec 3 (`p` is
DERIVED data, not a field); specs 4–5 (the split is inspectable: `K`, `cCore`, `μC`/`μH`, `outC`/
`outH`, `bdOut`, `bridge`, `near`/`away` are all DATA); spec 6 (`heS` derived from `hawayBd`, never
the dead transfer); spec 7 (`nonzero_of_genuine` derived from `hcoreHit` + `hKoffBd` + the glue);
spec 8 (`hasClass` derived, never stored).

**Anti-fake chain** (the tether the 2026-07-20 gate FAIL found missing):
`cCore → hctrlC/hctrlH → houtPair → qCtrl_boundary_eq → corrector`, with `hcoreHit` forcing
`K ≠ ∅` (an empty `K` makes `cCore ∈ C(Kᶜ)` automatic) and thence a genuine seam point at which
fact 3 gives a nonzero local class. The empty-`K` / zero-split fake the gate exhibited is closed.

## DEVIATION FROM THE DOSSIER — with an EQUIVALENCE CERTIFICATE

`codex_212_collarpair_design.md` routed `hp_det` through a `collarCorePrism` model chain plus a new
field `hnearModel` and a new theorem `collarCorePrism_hdet` derived from a field `hcCoreDet`
(detection of `cCore` inside `↥S`). **That leg is replaced here** by the single atom `hq0det` —
detection of the FROZEN glued chain `q₀ z` at seam points — and the five model-layer fields
(`csd`, `seamBase`, `seamBase_mid`, `hcCoreDet`, `nearCollar`/`hnearCollar`, `modelHomotopy`/
`modelOff`/`hnearModel`) are dropped.

The certificate is `corrector_relClassOf_eq`: because the mismatch `away` is supported off the
WHOLE overlap, at any seam point `x` the frozen chain and the derived corrector have the **same**
local class — an EQUALITY, not an implication. So the substituted obligation `hq0det` is
*equivalent* to the spec's `hp_det`, not merely sufficient for it. Two further reasons this is the
right substitution: (i) `hq0det` is *literally the existing in-tree atom*
`CapstoneSeamTransferResidual.hdetAB`, already accepted as "the honest irreducible seam atom", so
this reuses a vetted obligation rather than inventing one; (ii) the dossier's route needs a local
Künneth tower over the welded collar that does not exist in-tree, and whose base `↥S` carries no
manifold structure in this parameter row — see the residual note below.

## Deliberately NOT hypotheses

The dossier's `hφtop` / `hS_sphere` (its "upstream stop condition") and the `K ⊂ int A`
interiority pair `hKcyl`/`hKha` are **not** fields: the producer does not consume them, and a
producer proved from fewer inputs is strictly stronger. They remain genuine constraints on the
*inhabitation* wave (where the subtype-valued attaching maps `κC`/`κH` they type actually appear).
`houtC`/`houtH` ARE kept — they carry the #210 support signature (`U₂ = topface ∖ K`) that
distinguishes this shape from the refuted one — and are likewise inhabitation-side.

## The residual (what a future wave must inhabit)

`CollarPairBuild` is not inhabited here. Its genuinely geometric fields are exactly:
`hctrlC`, `hctrlH`, `houtPair`, `hbridge`, `hnearBd`, `hawayBd`, `hcoreHit`, `hq0det`.
The two hardest remain as the dossier scoped them: the shared `cCore` + `houtPair` collar-annulus
weld, and the canonical-disk `hbridge` (`diskDetectChain_subtype_boundary_split_freeSphere`
controls a subdivision, not the frozen chain).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCorrector
import SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
import SKEFTHawking.SingularSubdivisionToCover
import SKEFTHawking.SingularRelClassHomologous

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularSubdivision
open SKEFTHawking.SingularSubdivisionToCover
open SKEFTHawking.SingularExcision
open SKEFTHawking.SingularRelClassHomologous
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
open SKEFTHawking.PinPlusTraceDiskCorePair
open SKEFTHawking.PinPlusTraceCapstoneCorrector

namespace SKEFTHawking.PinPlusTraceCapstoneCollarPair

/-! ## §0. Char-2 shuffling helpers -/

/-- **The collar-pair seam cancellation** (char 2): the shared seam core appears once on each side
of the glue, so it cancels — `x + a + b + (x + c) = a + c + b`. The collar-pair analogue of
`transfer_cancel`, with the shared face already collapsed to a single term. -/
theorem collar_cancel {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (x a b c : V) :
    x + a + b + (x + c) = a + c + b := by
  rw [show x + a + b + (x + c) = x + x + (a + c + b) from by abel, ZModModule.add_self, zero_add]

/-- **The producer's char-2 bookkeeping**, isolated abstractly (the concrete carriers are
whnf-hostile). Given the bridge identity `q = Q + b + i` and the subdivision chain homotopy
`D + E = q + (n + a)`, the frozen chain `Q` is the corrector `n + (b + D) + (i + E)` plus `a`. -/
theorem char2_producer {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {q Q b i D E n a : V} (h1 : q = Q + b + i) (hh : D + E = q + (n + a)) :
    Q = n + (b + D) + (i + E) + a := by
  rw [show n + (b + D) + (i + E) + a = D + E + (n + a + b + i) from by abel, hh, h1,
    show Q + b + i + (n + a) + (n + a + b + i)
        = Q + (b + b) + (i + i) + (n + a + (n + a)) from by abel,
    ZModModule.add_self, ZModModule.add_self, ZModModule.add_self, add_zero, add_zero, add_zero]

section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §1. The frozen chains -/

/-- **The frozen glued 5-chain** `q₀ z` — the consumer's mismatch reference: the controlled cylinder
representative and the canonical disk chain, pushed into the trace carrier. -/
noncomputable def qZero (z : cycles (TopCat.of s.M) (2 + 2)) :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) :=
  closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
      (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
    + closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
      (3 + 2) diskDetectChain

/-- The `μC`-fold subdivision of the controlled cylinder representative. -/
noncomputable def ctrlCyl (z : cycles (TopCat.of s.M) (2 + 2)) (μC : ℕ) :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2) :=
  (⇑(singularSd (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2)))^[μC]
    (capstoneCylChainT s S hS φ hφ hφinj z)

/-- The `μH`-fold subdivision of the canonical disk detecting chain. -/
noncomputable def ctrlHandle (μH : ℕ) :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2) :=
  (⇑(singularSd (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)))^[μH]
    diskDetectChain

/-- The `μC`-fold subdivision of the cylinder's bottom face `z@⊥` (the source-manifold end). -/
noncomputable def ctrlBottom (z : cycles (TopCat.of s.M) (2 + 2)) (μC : ℕ) :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) :=
  (⇑(singularSd (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)))^[μC]
    (mapChain (slice (graphHom (TopCat.of s.M)) 0) (3 + 1)
      (z : SingularChain (TopCat.of s.M) (3 + 1)))

/-- The cylinder-side seam leg, typed at the cylinder END `.B` (rather than at `cyl M`) so every
cylinder-side sum is homogeneous — the `.B`/`cyl` defeq is real but not `rw`-transparent. -/
def seamLegB : C(TopCat.of ↥S, TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) :=
  ⟨φ, hφ⟩

/-- **The controlled glued 5-chain** `qCtrl` — the subdivision-controlled counterpart of `q₀`. -/
noncomputable def qCtrl (z : cycles (TopCat.of s.M) (2 + 2)) (μC μH : ℕ) :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) :=
  closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
      (3 + 2) (ctrlCyl s S hS φ hφ hφinj z μC)
    + closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
      (3 + 2) (ctrlHandle s S hS φ hφ hφinj μH)

/-- The seam point of an attaching-region parameter `a`, in the trace carrier. -/
noncomputable def seamPoint (a : ↥S) :
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier :=
  (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)

/-! ## §2. `CollarPairBuild` — the frozen inspectable split data -/

/-- **THE COLLAR-PAIR BUILD** — the producer's input. -/
structure CollarPairBuild where
  /-- a fundamental cycle of the closed source 4-manifold `M`. -/
  z : cycles (TopCat.of s.M) (2 + 2)
  /-- `z` represents THE fundamental class. -/
  hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
    = Homology.mk (TopCat.of s.M) (2 + 2) z
  /-- **the shrunk closed core** `K ⊂ int A` of the attaching region (#210 repair shape). -/
  K : Set ↥S
  /-- the core is chosen away from the boundary of the finished trace. -/
  hKoffBd : K ⊆ (seamPoint s S hS φ hφ hφinj ⁻¹'
    (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W))ᶜ
  /-- **the shared 4-dimensional seam core** on the attaching region. -/
  cCore : SingularChain (TopCat.of ↥S) (3 + 1)
  /-- the number of cylinder-side subdivisions. -/
  μC : ℕ
  /-- the number of handle-side subdivisions. -/
  μH : ℕ
  /-- the cylinder-side remainder (the un-attached top face, off `K`). -/
  outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
  /-- the handle-side remainder (the free boundary sphere, off `K`). -/
  outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
  /-- **the cylinder-side co-adaptation**: the subdivided controlled cylinder chain's boundary
  splits as the shared core (pushed along the attaching leg) + the off-`K` remainder + the
  bottom face. -/
  hctrlC : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
      (ctrlCyl s S hS φ hφ hφinj z μC)
    = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC + ctrlBottom s S hS φ hφ hφinj z μC
  /-- **the handle-side co-adaptation**: the subdivided canonical disk chain's boundary splits as
  the SAME shared core (pushed along the inclusion leg) + the off-`K` free-sphere remainder. -/
  hctrlH : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
      (ctrlHandle s S hS φ hφ hφinj μH)
    = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cCore + outH
  /-- the cylinder remainder is supported in the top face off the shrunk core (`U₂ = topface ∖ K`;
  the #210 engine-compatible support — never the dead `Aᶜ`). -/
  houtC : outC ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ φ '' K) (3 + 1)
  /-- the handle remainder is supported in the boundary sphere off the shrunk core. -/
  houtH : outH ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ Subtype.val '' K) (3 + 1)
  /-- the welded boundary-subtype chain the two remainders and the bottom face assemble into. -/
  bdOut : SingularChain
    (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1)
  /-- **the collar-annulus weld**: the two pushed remainders and the bottom face are exactly a
  `∂W`-chain. -/
  houtPair : closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) outC
      + closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
        (3 + 1) outH
      + closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) (ctrlBottom s S hS φ hφ hφinj z μC)
    = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) bdOut
  /-- the subdivision-prism 6-chain bridging the controlled glued chain to the frozen one. -/
  bridge : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 3)
  /-- the `∂W`-supported error of that bridge. -/
  bridgeBd : SingularChain
    (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 2)
  /-- **the bridge identity**: the controlled glued chain is the frozen one up to a boundary and a
  `∂W`-chain. -/
  hbridge : qCtrl s S hS φ hφ hφinj z μC μH
    = qZero s S hS φ hφ hφinj z
      + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) bridge
      + chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 2)
          bridgeBd
  /-- the ambient subdivision count of the relative MV partition. -/
  μW : ℕ
  /-- the collar-near piece of the partition. -/
  near : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)
  /-- the off-overlap piece of the partition. -/
  away : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)
  /-- **the partition**: the subdivided controlled glued chain splits into the two pieces. -/
  hpartition : ((⇑(singularSd
      (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)))^[μW])
      (qCtrl s S hS φ hφ hφinj z μC μH) = near + away
  /-- the off-overlap piece is supported off the seam overlap. -/
  hawayOff : away ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
        ∩ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)ᶜ (3 + 2)
  /-- the `∂W`-subtype witness for the near piece's boundary. -/
  nearBd : SingularChain
    (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1)
  /-- the `∂W`-subtype witness for the away piece's boundary. -/
  awayBd : SingularChain
    (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1)
  /-- **the near piece is a relative cycle** (the collar-overlap correction, not a generic split). -/
  hnearBd : chainBoundary
      (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) near
    = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) nearBd
  /-- **the away piece is a relative cycle**. -/
  hawayBd : chainBoundary
      (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) away
    = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) awayBd
  /-- **THE ANTI-FAKE TETHER (spec 7)**: genuine attachment forces the shared seam core to meet the
  shrunk core `K` — in particular `K ≠ ∅` and `cCore ≠ 0`. -/
  hcoreHit :
    mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
    cCore ∉ subspaceChains (X := TopCat.of ↥S) (K ᶜ) (3 + 1)
  /-- **THE SEAM STRADDLE-DETECTION ATOM**: the FROZEN glued chain `q₀ z` detects the local
  generator at every seam point off `∂W`. -/
  hq0det : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier),
      x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
      ∀ (hq : chainBoundary
          (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
          (qZero s S hS φ hφ hφinj z)
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            ({x}ᶜ) (3 + 1)),
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
      (qZero s S hS φ hφ hφinj z) hq ≠ 0

/-! ## §3. The derived chain algebra -/

variable {s t S hS φ hφ hφinj cd hseam d}

namespace CollarPairBuild

variable (R : CollarPairBuild s t S hS φ hφ hφinj cd hseam d)

omit [PreconnectedSpace s.M] in
/-- **The shared seam core cancels across the glue.** -/
theorem core_glue_eq :
    closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) (mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) R.cCore)
      = closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
        (3 + 1) (mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) R.cCore) :=
  closedEmbeddingChain_mapChain_glue_eq
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
    (seamLegB s S hS φ hφ hφinj) (seamLegHa s S hS φ hφ hφinj)
    (ContinuousMap.ext (fun a => (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a))
    (3 + 1) R.cCore

omit [PreconnectedSpace s.M] in
/-- **The controlled glued chain is a relative cycle**: its boundary is exactly the welded
`∂W`-chain `bdOut`. -/
theorem qCtrl_boundary_eq :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qCtrl s S hS φ hφ hφinj R.z R.μC R.μH)
      = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (3 + 1) R.bdOut := by
  rw [qCtrl, map_add, chainBoundary_closedEmbeddingChain, chainBoundary_closedEmbeddingChain,
    R.hctrlC, R.hctrlH, closedEmbeddingChain_add, closedEmbeddingChain_add,
    closedEmbeddingChain_add, R.core_glue_eq, ← R.houtPair]
  exact collar_cancel _ _ _ _

/-- The 6-chain correction: the bridge prism plus the ambient subdivision prism. -/
noncomputable def corr6 :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 3) :=
  R.bridge
    + iterHomotopy (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) R.μW
        (qCtrl s S hS φ hφ hφinj R.z R.μC R.μH)

/-- The `∂W`-supported 5-chain correction. -/
noncomputable def corrBd :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) :=
  chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 2)
      R.bridgeBd
    + iterHomotopy (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) R.μW
        (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
          (qCtrl s S hS φ hφ hφinj R.z R.μC R.μH))

/-- **THE CORRECTOR CHAIN, DERIVED** — never a `CollarPairBuild` field (round-13 gate spec 3+8).
It is the collar-near piece of the relative MV partition, corrected by the subdivision/bridge
prisms. Because it is a *definition* of the build's split data, no independently-supplied
corrector can be smuggled in. -/
noncomputable def corrector :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) :=
  R.near
    + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) R.corr6
    + R.corrBd

omit [PreconnectedSpace s.M] in
/-- **THE PRODUCER'S CENTRAL IDENTITY**: the frozen glued chain splits as the derived corrector
plus the off-overlap piece. Everything downstream (`hpS`, `heS`, `hagree`, `hp_det`) is read off
this one equation. -/
theorem q0_eq_corrector_add_away :
    qZero s S hS φ hφ hφinj R.z = R.corrector + R.away := by
  have hh := iterHomotopy_chainHomotopy
    (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) R.μW (3 + 1)
    (qCtrl s S hS φ hφ hφinj R.z R.μC R.μH)
  rw [R.hpartition] at hh
  rw [corrector, corr6, corrBd, map_add]
  exact char2_producer R.hbridge hh

omit [PreconnectedSpace s.M] in
/-- The mismatch between the frozen glued chain and the derived corrector is exactly the
off-overlap piece. -/
theorem mismatch_eq_away :
    qZero s S hS φ hφ hφinj R.z - R.corrector = R.away := by
  rw [R.q0_eq_corrector_add_away]; abel

omit [PreconnectedSpace s.M] in
/-- The `∂W`-supported 5-chain correction really is `∂W`-supported. -/
theorem corrBd_mem :
    R.corrBd ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 2) := by
  refine Submodule.add_mem _ ⟨R.bridgeBd, rfl⟩ (iterHomotopy_mem_subspaceChains ?_ R.μW)
  exact R.qCtrl_boundary_eq ▸ ⟨R.bdOut, rfl⟩

omit [PreconnectedSpace s.M] in
/-- **Corrector fact 1 (`hpS`)**: the derived corrector's boundary is a `∂W`-chain. -/
theorem corrector_hpS :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        R.corrector
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) := by
  rw [corrector, map_add, map_add, chainBoundary_chainBoundary_apply, R.hnearBd, add_zero]
  exact Submodule.add_mem _ ⟨R.nearBd, rfl⟩
    (chainBoundary_mem_subspaceChains _ (3 + 1) _ R.corrBd_mem)

omit [PreconnectedSpace s.M] in
/-- **Corrector fact 2 (`heS`)**: the mismatch's boundary is a `∂W`-chain — read off `hawayBd`,
never through the dead transfer (round-13 gate spec 2+6). -/
theorem corrector_heS :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qZero s S hS φ hφ hφinj R.z - R.corrector)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) := by
  rw [R.mismatch_eq_away, R.hawayBd]
  exact ⟨R.awayBd, rfl⟩

omit [PreconnectedSpace s.M] in
/-- **Corrector fact 4 (`hagree`)**: the mismatch is supported off the seam overlap. -/
theorem corrector_hagree :
    qZero s S hS φ hφ hφinj R.z - R.corrector
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
            ∩ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)ᶜ (3 + 2) :=
  R.mismatch_eq_away ▸ R.hawayOff

omit [PreconnectedSpace s.M] in
/-- The frozen glued chain is a relative cycle of `(W, ∂W)`. -/
theorem qZero_boundary_mem :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qZero s S hS φ hφ hφinj R.z)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) := by
  rw [R.q0_eq_corrector_add_away, map_add, R.hawayBd]
  exact Submodule.add_mem _ R.corrector_hpS ⟨R.awayBd, rfl⟩

omit [PreconnectedSpace s.M] in
/-- **Corrector fact 3 (`hp_det`) — THE EQUIVALENCE CERTIFICATE.** At a seam point `x` off `∂W`
the mismatch `away` is supported off `x` (it lives off the whole overlap), so the derived
corrector and the FROZEN glued chain have the *same* local class there. Detection of the corrector
is therefore not merely implied by, but EQUIVALENT to, the build's `hq0det` atom. -/
theorem corrector_relClassOf_eq
    (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
    (hxA : x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)
    (hxB : x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle) :
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
        (qZero s S hS φ hφ hφinj R.z)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) R.qZero_boundary_mem)
      = relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
        R.corrector
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) R.corrector_hpS) :=
  relClassOf_eq_of_congr (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr
      (show x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
          ∩ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle from ⟨hxA, hxB⟩)))
    3 R.q0_eq_corrector_add_away R.hawayOff _ _

omit [PreconnectedSpace s.M] in
/-- **Corrector fact 3 (`hp_det`)**: the derived corrector detects the local generator at every
seam point off `∂W`. -/
theorem corrector_hp_det
    (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
    (hxA : x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)
    (hxB : x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle) :
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
        R.corrector
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) R.corrector_hpS)
      ≠ 0 := by
  rw [← R.corrector_relClassOf_eq x hx hxA hxB]
  exact R.hq0det x hx hxA hxB _

omit [PreconnectedSpace s.M] in
/-- **The anti-fake tether bites: `K` is nonempty.** A supported-off-`K` core is automatic when
`K = ∅` (every chain lies in `C(univ)`), so `hcoreHit` rules the empty-`K` fake out. -/
theorem K_nonempty
    (hgen : mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (R.z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1)) :
    R.K.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  exact R.hcoreHit hgen (by rw [hempty, Set.compl_empty]; exact mem_subspaceChains_univ _ _)

omit [PreconnectedSpace s.M] in
/-- **Corrector fact 5 (`nonzero_of_genuine`) — the anti-fake guard (round-13 gate spec 7).**
Genuine attachment forces `K ≠ ∅`; any `a ∈ K` yields a seam point off `∂W` (by `hKoffBd`) sitting
in BOTH ends (by the surgery glue), where fact 3 gives a nonzero local class — impossible for the
zero chain. -/
theorem corrector_nonzero_of_genuine
    (hgen : mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (R.z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1)) :
    R.corrector ≠ 0 := by
  obtain ⟨a, ha⟩ := R.K_nonempty hgen
  intro hzero
  refine R.corrector_hp_det (seamPoint s S hS φ hφ hφinj a) (R.hKoffBd ha)
    ⟨φ a, (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a⟩ ⟨(a : D5), rfl⟩ ?_
  exact relClassOf_eq_zero_of_subspace (Set.empty_subset _) 3 R.corrector
    (by rw [hzero]; exact Submodule.zero_mem _) _

end CollarPairBuild

/-! ## §4. THE PRODUCER -/

/-- **THE PRODUCER** `correctorT_of_collarPair : CollarPairBuild → CapstoneSeamCorrectorT` —
the round-13 gate's frozen producer target. Every consumed field is DERIVED from the build's
inspectable split data. -/
noncomputable def correctorT_of_collarPair
    (R : CollarPairBuild s t S hS φ hφ hφinj cd hseam d) :
    CapstoneSeamCorrectorT s t S hS φ hφ hφinj cd hseam d where
  z := R.z
  hz := R.hz
  p := R.corrector
  hpS := R.corrector_hpS
  heS := R.corrector_heS
  hagree := R.corrector_hagree
  hp_det := fun x hx hxA hxB => R.corrector_hp_det x hx hxA hxB
  nonzero_of_genuine := fun hgen => R.corrector_nonzero_of_genuine hgen

/-- **THE CAPSTONE `hasClass`, FROM THE COLLAR-PAIR SPLIT.** The composite
`CollarPairBuild → CapstoneSeamCorrectorT → hasClass`. Its conclusion is the EXACT
`CapstoneAmbientSupply.hasClass` field type, so the downstream rows consume it as-is. This is the
#212 repair, end to end, with nothing routed through the settled-dead `CapstoneSeamTransfer`. -/
noncomputable def hasClass_ofCollarPair
    (R : CollarPairBuild s t S hS φ hφ hφinj cd hseam d) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  (correctorT_of_collarPair R).toHasClass

end

end SKEFTHawking.PinPlusTraceCapstoneCollarPair
