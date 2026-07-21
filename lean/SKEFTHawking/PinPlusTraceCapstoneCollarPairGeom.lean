/-
# Phase 5q.H (#212) — THE COLLAR-PAIR ROW, REDUCED (8 geometric fields → 6)

Work on the residual named at the end of `PinPlusTraceCapstoneCollarPair`: `CollarPairBuild` is not
inhabited, and its genuinely geometric fields are `hctrlC`, `hctrlH`, `houtPair`, `hbridge`,
`hnearBd`, `hawayBd`, `hcoreHit`, `hq0det`. This module **removes two of them** — including the one
the dossier's risk register ranked HIGHEST (`hbridge`, the canonical-disk subdivision bridge) — by
proving them from the rest, and packages the survivors as `CollarPairGeom` with a producer
`CollarPairGeom.toCollarPairBuild`.

## The lever: a UNIFIED subdivision count collapses the glued chain

`qCtrl` glues `Sd^μC` of the cylinder chain and `Sd^μH` of the disk chain along two closed
embeddings. With `μC = μH = μ` — a free normalization, nothing forces the two counts apart — the
new naturality square `mapChain_singularSd_iterate` (`SingularSubdivisionPushNatural`) pushes both
subdivisions *outside* the glue:

  `qCtrl_eq_singularSd_iterate_qZero : qCtrl z μ μ = Sdᵘ (q₀ z)`.

So the "controlled" glued chain is not a new chain at all — it is literally a subdivision of the
FROZEN one. Everything the dossier routed through a hand-built bridge prism is then the standard
subdivision chain homotopy.

## What is eliminated, and the two-way certificates

* **`hbridge` (+ its two data fields `bridge`, `bridgeBd`) — GONE**, replaced by the single soft
  field `hq0Bd : ∂(q₀ z) ∈ C(∂W)` ("the frozen glued chain is a relative cycle"). The certificate is
  `bridge_exists_iff_qZero_boundary_mem`: given the collar-pair splits (through their consequence
  `∂qCtrl = ∂W`-chain) and the unified count, an inhabitant of the bridge triple **exists if and
  only if** `hq0Bd` holds. Not "sufficient" — an `↔`.
* **`hawayBd` (+ its data field `awayBd`) — GONE**, derived in `exists_awayBd`: the partition's two
  halves cannot both fail to be relative cycles, because their sum `Sd^μW qCtrl` is one. The
  certificate is definitional: the derived statement is verbatim the `CollarPairBuild.hawayBd`
  field type, discharged in `toCollarPairBuild`.

The surviving geometric row is `hctrlC`, `hctrlH`, `houtPair`, `hq0Bd`, `hnearBd`, `hcoreHit`,
`hq0det` — and `hq0Bd` is itself a *consequence* of the splits whenever they are stated on the
UNSUBDIVIDED chains (`μ = 0`), discharged for free by `qZero_boundary_mem_of_splits` (§3) — which is
exactly the shape the vetted in-tree seam atom `CapstoneSeamTransferSeam` already uses. §5 makes
that structural rather than prose: **`CollarPairGeomUnsub`** carries exactly SIX geometric fields
(`hctrlC`, `hctrlH`, `houtPair`, `hnearBd`, `hcoreHit`, `hq0det`) and reaches `hasClass` through
`toCollarPairGeom → toCollarPairBuild → toHasClass`.

§6 records that `hq0det`'s `∀`-over-membership-proofs shape is cosmetic (`hq0det_of_witness`), so it
is *precisely* the vetted in-tree straddle atom, not a new obligation.

## Fences

Nothing here routes through `CapstoneSeamTransfer` / `hbd_ofTransfer` /
`hasClass_ofTransferCorrector` (round-13 gate spec 2); the `#210` support signature
(`houtC`/`houtH` at `U₂ = topface ∖ K`) is carried verbatim, so the settled-dead open-complement
split (`seam-transfer-open-support-uninhabitable`) is never re-entered. `hq0Bd` is deliberately NOT
taken from the in-tree `hbd_ofTransfer`, whose `hwOut` premise is exactly that refuted signature.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCollarPair
import SKEFTHawking.SingularSubdivisionPushNatural

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularSubdivision
open SKEFTHawking.SingularSubdivisionPushNatural
open SKEFTHawking.SingularExcision
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularSubdivisionToCover
open SKEFTHawking.SingularRelClassHomologous
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
open SKEFTHawking.PinPlusTraceDiskCorePair
open SKEFTHawking.PinPlusTraceCapstoneCorrector
open SKEFTHawking.PinPlusTraceCapstoneCollarPair

namespace SKEFTHawking.PinPlusTraceCapstoneCollarPairGeom

/-! ## §0. Char-2 shuffles, isolated abstractly (the concrete carriers are `rw`-hostile) -/

/-- `A = B + C ⟹ B = A + C` over `ZMod 2`. -/
theorem char2_left {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {A B C : V} (h : A = B + C) :
    B = A + C := by
  rw [h, add_assoc, ZModModule.add_self, add_zero]

/-- `X + Y = Z + W ⟹ W = Z + X + Y` over `ZMod 2`. -/
theorem char2_right {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {X Y Z W : V}
    (h : X + Y = Z + W) : W = Z + X + Y := by
  rw [add_assoc, h, ← add_assoc, ZModModule.add_self, zero_add]

section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §1. The unified-count collapse -/

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE COLLAPSE**: with a unified subdivision count the controlled glued chain is literally a
subdivision of the frozen one. Both closed-embedding pushforwards are plain pushforwards
(`closedEmbeddingChain_eq_mapChain`), and pushforward commutes with `Sdᵘ`
(`mapChain_singularSd_iterate`), so the two subdivisions migrate outside the glue and merge. -/
theorem qCtrl_eq_singularSd_iterate_qZero (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ) :
    qCtrl s S hS φ hφ hφinj z μ μ
      = (⇑(singularSd (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (3 + 2)))^[μ] (qZero s S hS φ hφ hφinj z) := by
  rw [qCtrl, qZero, ctrlCyl, ctrlHandle, closedEmbeddingChain_eq_mapChain,
    closedEmbeddingChain_eq_mapChain, closedEmbeddingChain_eq_mapChain,
    closedEmbeddingChain_eq_mapChain, mapChain_singularSd_iterate, mapChain_singularSd_iterate,
    ← singularSd_iterate_add]

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- At `μ = 0` the controlled cylinder chain is the cylinder chain. -/
theorem ctrlCyl_zero (z : cycles (TopCat.of s.M) (2 + 2)) :
    ctrlCyl s S hS φ hφ hφinj z 0 = capstoneCylChainT s S hS φ hφ hφinj z := rfl

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- At `μ = 0` the controlled disk chain is the canonical detecting chain. -/
theorem ctrlHandle_zero : ctrlHandle s S hS φ hφ hφinj 0 = diskDetectChain := rfl

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- At `μ = 0` the controlled bottom face is the bottom slice of `z`. -/
theorem ctrlBottom_zero (z : cycles (TopCat.of s.M) (2 + 2)) :
    ctrlBottom s S hS φ hφ hφinj z 0
      = mapChain (slice (graphHom (TopCat.of s.M)) 0) (3 + 1)
          (z : SingularChain (TopCat.of s.M) (3 + 1)) := rfl

/-! ## §2. `CollarPairGeom` — the reduced inspectable split data -/

/-- **THE REDUCED COLLAR-PAIR ROW.** `CollarPairBuild` with a UNIFIED subdivision count `μ`, the
bridge triple (`bridge`, `bridgeBd`, `hbridge`) traded for the single soft field `hq0Bd`, and the
`away`-side relative-cycle pair (`awayBd`, `hawayBd`) dropped outright. Every other field is
verbatim the `CollarPairBuild` field — including the `#210` support signature on `houtC`/`houtH`. -/
structure CollarPairGeom where
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
  /-- **the UNIFIED subdivision count** — one count for both sides of the glue. This is the
  normalization that makes the controlled glued chain a subdivision of the frozen one. -/
  μ : ℕ
  /-- the cylinder-side remainder (the un-attached top face, off `K`). -/
  outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
  /-- the handle-side remainder (the free boundary sphere, off `K`). -/
  outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
  /-- **the cylinder-side co-adaptation** (verbatim `CollarPairBuild.hctrlC` at `μC := μ`). -/
  hctrlC : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
      (ctrlCyl s S hS φ hφ hφinj z μ)
    = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC + ctrlBottom s S hS φ hφ hφinj z μ
  /-- **the handle-side co-adaptation** (verbatim `CollarPairBuild.hctrlH` at `μH := μ`). -/
  hctrlH : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
      (ctrlHandle s S hS φ hφ hφinj μ)
    = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cCore + outH
  /-- the cylinder remainder is supported in the top face off the shrunk core (`U₂ = topface ∖ K`). -/
  houtC : outC ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ φ '' K) (3 + 1)
  /-- the handle remainder is supported in the boundary sphere off the shrunk core. -/
  houtH : outH ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ Subtype.val '' K) (3 + 1)
  /-- the welded boundary-subtype chain the two remainders and the bottom face assemble into. -/
  bdOut : SingularChain
    (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1)
  /-- **the collar-annulus weld** (verbatim `CollarPairBuild.houtPair` at `μC := μ`). -/
  houtPair : closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) outC
      + closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
        (3 + 1) outH
      + closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) (ctrlBottom s S hS φ hφ hφinj z μ)
    = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) bdOut
  /-- **THE SOFT REPLACEMENT FOR `hbridge`**: the FROZEN glued chain is a relative cycle of
  `(W, ∂W)`. Certified equivalent to the dossier's bridge triple by
  `bridge_exists_iff_qZero_boundary_mem`, and discharged outright at `μ = 0` by
  `qZero_boundary_mem_of_splits`. -/
  hq0Bd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
      (qZero s S hS φ hφ hφinj z)
    ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)
  /-- the ambient subdivision count of the relative MV partition. -/
  μW : ℕ
  /-- the collar-near piece of the partition. -/
  near : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)
  /-- the off-overlap piece of the partition. -/
  away : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)
  /-- **the partition**: the subdivided controlled glued chain splits into the two pieces. -/
  hpartition : ((⇑(singularSd
      (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)))^[μW])
      (qCtrl s S hS φ hφ hφinj z μ μ) = near + away
  /-- the off-overlap piece is supported off the seam overlap. -/
  hawayOff : away ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
        ∩ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)ᶜ (3 + 2)
  /-- the `∂W`-subtype witness for the near piece's boundary. -/
  nearBd : SingularChain
    (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1)
  /-- **the near piece is a relative cycle** (the collar-overlap correction). The `away` mirror is
  NOT a field: it is forced (`away_boundary_mem`). -/
  hnearBd : chainBoundary
      (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) near
    = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) nearBd
  /-- **THE ANTI-FAKE TETHER**: genuine attachment forces the shared seam core to meet `K`. -/
  hcoreHit :
    mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
    cCore ∉ subspaceChains (X := TopCat.of ↥S) (K ᶜ) (3 + 1)
  /-- **THE SEAM STRADDLE-DETECTION ATOM** (verbatim `CollarPairBuild.hq0det`). -/
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

/-- **THE SIX-OBLIGATION ROW.** `CollarPairGeom` at `μ = 0`: the two co-adapted splits are stated on
the UNSUBDIVIDED chains — the shape the vetted in-tree seam atom `CapstoneSeamTransferSeam` already
uses — so `hq0Bd` disappears as a field (`qZero_boundary_mem_of_splits` proves it). Its geometric
obligations are exactly SIX: `hctrlC`, `hctrlH`, `houtPair`, `hnearBd`, `hcoreHit`, `hq0det`. This
structure is what makes the "six, down from eight" claim structural rather than prose. -/
structure CollarPairGeomUnsub where
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
  /-- the cylinder-side remainder (the un-attached top face, off `K`). -/
  outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
  /-- the handle-side remainder (the free boundary sphere, off `K`). -/
  outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
  /-- **GEOMETRIC 1 — the cylinder-side split**, on the unsubdivided controlled cylinder chain: its
  boundary is the shared core (pushed along the attaching leg) + the off-`K` top-face remainder +
  the bottom face. -/
  hctrlC : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
      (capstoneCylChainT s S hS φ hφ hφinj z)
    = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC
      + ctrlBottom s S hS φ hφ hφinj z 0
  /-- **GEOMETRIC 2 — the disk-side split**, on the canonical detecting chain itself: its boundary
  is the SAME shared core (pushed along the inclusion leg) + the off-`K` free-sphere remainder. -/
  hctrlH : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
      diskDetectChain
    = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cCore + outH
  /-- the cylinder remainder is supported in the top face off the shrunk core (`U₂ = topface ∖ K`). -/
  houtC : outC ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ φ '' K) (3 + 1)
  /-- the handle remainder is supported in the boundary sphere off the shrunk core. -/
  houtH : outH ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ Subtype.val '' K) (3 + 1)
  /-- the welded boundary-subtype chain the two remainders and the bottom face assemble into. -/
  bdOut : SingularChain
    (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1)
  /-- **GEOMETRIC 3 — the collar-annulus weld**: the two pushed remainders and the bottom face are
  exactly a `∂W`-chain. -/
  houtPair : closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) outC
      + closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
        (3 + 1) outH
      + closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) (ctrlBottom s S hS φ hφ hφinj z 0)
    = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) bdOut
  /-- the ambient subdivision count of the relative MV partition. -/
  μW : ℕ
  /-- the collar-near piece of the partition. -/
  near : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)
  /-- the off-overlap piece of the partition. -/
  away : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)
  /-- **the partition**: the subdivided FROZEN glued chain splits into the two pieces. -/
  hpartition : ((⇑(singularSd
      (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)))^[μW])
      (qZero s S hS φ hφ hφinj z) = near + away
  /-- the off-overlap piece is supported off the seam overlap. -/
  hawayOff : away ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
        ∩ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)ᶜ (3 + 2)
  /-- the `∂W`-subtype witness for the near piece's boundary. -/
  nearBd : SingularChain
    (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1)
  /-- **GEOMETRIC 4 — the near piece is a relative cycle** (the collar-overlap correction). -/
  hnearBd : chainBoundary
      (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) near
    = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) nearBd
  /-- **GEOMETRIC 5 — the anti-fake tether**: genuine attachment forces the shared seam core to
  meet `K`. -/
  hcoreHit :
    mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
    cCore ∉ subspaceChains (X := TopCat.of ↥S) (K ᶜ) (3 + 1)
  /-- **GEOMETRIC 6 — the seam straddle-detection atom**. -/
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

/-! ## §3. The two eliminations, as standalone certificates -/

variable {s t S hS φ hφ hφinj cd hseam d}

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE `hbridge` EQUIVALENCE CERTIFICATE.** Under the unified subdivision count, and given the
collar-pair splits' consequence `∂qCtrl = ∂W`-chain, the dossier's bridge triple
`(bridge, bridgeBd, hbridge)` is inhabitable **exactly when** the frozen glued chain is a relative
cycle of `(W, ∂W)`. So trading `hbridge` for `hq0Bd` neither weakens nor strengthens the row — it is
the same obligation, stated without the prism data. -/
theorem bridge_exists_iff_qZero_boundary_mem (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    (bdOut : SingularChain
      (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1))
    (hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qCtrl s S hS φ hφ hφinj z μ μ)
      = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (3 + 1) bdOut) :
    (∃ (bridge : SingularChain
          (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 3))
        (bridgeBd : SingularChain
          (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 2)),
        qCtrl s S hS φ hφ hφinj z μ μ
          = qZero s S hS φ hφ hφinj z
            + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
                (3 + 2) bridge
            + chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
                (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
                (3 + 2) bridgeBd)
      ↔ chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
            (qZero s S hS φ hφ hφinj z)
          ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
              (3 + 1) := by
  constructor
  · rintro ⟨bridge, bridgeBd, hbr⟩
    have h := congrArg (chainBoundary
      (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)) hbr
    rw [hbd, map_add, map_add, chainBoundary_chainBoundary_apply, add_zero] at h
    rw [char2_left h]
    exact Submodule.add_mem _ ⟨bdOut, rfl⟩
      (chainBoundary_mem_subspaceChains _ (3 + 1) _ ⟨bridgeBd, rfl⟩)
  · intro hq0
    obtain ⟨bridgeBd, hbb⟩ :
        ∃ b, chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
              (3 + 2) b
            = iterHomotopy (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
                (3 + 1) μ
                (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
                  (3 + 1) (qZero s S hS φ hφ hφinj z)) :=
      iterHomotopy_mem_subspaceChains hq0 μ
    refine ⟨iterHomotopy (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) μ
      (qZero s S hS φ hφ hφinj z), bridgeBd, ?_⟩
    have hh : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)
            (iterHomotopy (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) μ
              (qZero s S hS φ hφ hφinj z))
          + iterHomotopy (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) μ
              (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
                (3 + 1) (qZero s S hS φ hφ hφinj z))
        = qZero s S hS φ hφ hφinj z
          + (⇑(singularSd (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              (3 + 2)))^[μ] (qZero s S hS φ hφ hφinj z) :=
      iterHomotopy_chainHomotopy (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        μ (3 + 1) (qZero s S hS φ hφ hφinj z)
    rw [qCtrl_eq_singularSd_iterate_qZero, hbb]
    exact char2_right hh

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The collar-pair splits make the controlled glued chain a relative cycle**, standalone (no
structure). The shared seam core cancels across the glue
(`closedEmbeddingChain_mapChain_glue_eq`), leaving exactly the welded `∂W`-chain. -/
theorem qCtrl_boundary_eq_of_splits (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    {cCore : SingularChain (TopCat.of ↥S) (3 + 1)}
    {outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    {bdOut : SingularChain
      (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1)}
    (hctrlC : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
        (ctrlCyl s S hS φ hφ hφinj z μ)
      = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC
        + ctrlBottom s S hS φ hφ hφinj z μ)
    (hctrlH : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
        (ctrlHandle s S hS φ hφ hφinj μ)
      = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cCore + outH)
    (houtPair : closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 1) outC
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 1) outH
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 1) (ctrlBottom s S hS φ hφ hφinj z μ)
      = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (3 + 1) bdOut) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qCtrl s S hS φ hφ hφinj z μ μ)
      = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (3 + 1) bdOut := by
  have hglue := closedEmbeddingChain_mapChain_glue_eq
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
    (seamLegB s S hS φ hφ hφinj) (seamLegHa s S hS φ hφ hφinj)
    (ContinuousMap.ext (fun a => (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a))
    (3 + 1) cCore
  rw [qCtrl, map_add, chainBoundary_closedEmbeddingChain, chainBoundary_closedEmbeddingChain,
    hctrlC, hctrlH, closedEmbeddingChain_add, closedEmbeddingChain_add,
    closedEmbeddingChain_add, hglue, ← houtPair]
  exact collar_cancel _ _ _ _

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`hq0Bd` IS FREE AT `μ = 0`.** With the splits stated on the *unsubdivided* chains — the shape
the vetted in-tree seam atom `CapstoneSeamTransferSeam` already uses — the frozen glued chain's
relative-cycle property is a consequence, not an obligation. So `CollarPairGeom`'s independent
geometric row is `hctrlC`, `hctrlH`, `houtPair`, `hnearBd`, `hcoreHit`, `hq0det`: **six**. -/
theorem qZero_boundary_mem_of_splits (z : cycles (TopCat.of s.M) (2 + 2))
    {cCore : SingularChain (TopCat.of ↥S) (3 + 1)}
    {outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    {bdOut : SingularChain
      (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1)}
    (hctrlC : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
        (ctrlCyl s S hS φ hφ hφinj z 0)
      = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC
        + ctrlBottom s S hS φ hφ hφinj z 0)
    (hctrlH : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
        (ctrlHandle s S hS φ hφ hφinj 0)
      = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cCore + outH)
    (houtPair : closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 1) outC
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 1) outH
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 1) (ctrlBottom s S hS φ hφ hφinj z 0)
      = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (3 + 1) bdOut) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qZero s S hS φ hφ hφinj z)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) := by
  have hq : qCtrl s S hS φ hφ hφinj z 0 0 = qZero s S hS φ hφ hφinj z := by
    rw [qCtrl_eq_singularSd_iterate_qZero, Function.iterate_zero_apply]
  rw [← hq, qCtrl_boundary_eq_of_splits z 0 hctrlC hctrlH houtPair]
  exact ⟨bdOut, rfl⟩

/-! ## §4. The reduced row produces the frozen one -/

namespace CollarPairGeom

variable (R : CollarPairGeom s t S hS φ hφ hφinj cd hseam d)

omit [PreconnectedSpace s.M] in
/-- The controlled glued chain of a reduced row is a relative cycle of `(W, ∂W)`. -/
theorem qCtrl_boundary_eq :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qCtrl s S hS φ hφ hφinj R.z R.μ R.μ)
      = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (3 + 1) R.bdOut :=
  qCtrl_boundary_eq_of_splits R.z R.μ R.hctrlC R.hctrlH R.houtPair

omit [PreconnectedSpace s.M] in
/-- **THE `hawayBd` ELIMINATION.** The `away` half of the MV partition is forced to be a relative
cycle: its sum with `near` is `Sd^μW` of a relative cycle, and `near` is one by `hnearBd`. So the
dossier's `awayBd`/`hawayBd` pair carries no independent geometric content. -/
theorem away_boundary_mem :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) R.away
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) := by
  have hA : R.away
      = ((⇑(singularSd (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (3 + 2)))^[R.μW]) (qCtrl s S hS φ hφ hφinj R.z R.μ R.μ) + R.near :=
    char2_left (R.hpartition.trans (add_comm _ _))
  rw [hA, map_add, singularSd_iterate_chainBoundary, R.qCtrl_boundary_eq, R.hnearBd]
  exact Submodule.add_mem _
    (singularSd_iterate_mem_subspaceChains ⟨R.bdOut, rfl⟩ R.μW) ⟨R.nearBd, rfl⟩

omit [PreconnectedSpace s.M] in
/-- The `∂W`-subtype witness `away_boundary_mem` produces — exactly the dropped `awayBd` field. -/
theorem exists_awayBd :
    ∃ b, chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        R.away
      = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (3 + 1) b := by
  obtain ⟨b, hb⟩ := R.away_boundary_mem
  exact ⟨b, hb.symm⟩

omit [PreconnectedSpace s.M] in
/-- **THE `hbridge` ELIMINATION.** The bridge triple is produced from `hq0Bd` through the
equivalence certificate. -/
theorem exists_bridge :
    ∃ (bridge : SingularChain
        (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 3))
      (bridgeBd : SingularChain
        (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 2)),
      qCtrl s S hS φ hφ hφinj R.z R.μ R.μ
        = qZero s S hS φ hφ hφinj R.z
          + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              (3 + 2) bridge
          + chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
              (3 + 2) bridgeBd :=
  (bridge_exists_iff_qZero_boundary_mem R.z R.μ R.bdOut R.qCtrl_boundary_eq).mpr R.hq0Bd

/-- **THE REDUCTION PRODUCER** `CollarPairGeom → CollarPairBuild`. Sixteen fields pass through
verbatim; `μC`/`μH` are both `R.μ`; the bridge triple and the `away` relative-cycle pair are the
DERIVED witnesses. So the whole #212 chain — `CollarPairBuild → CapstoneSeamCorrectorT → hasClass`
— is now reachable from the reduced row. -/
noncomputable def toCollarPairBuild : CollarPairBuild s t S hS φ hφ hφinj cd hseam d where
  z := R.z
  hz := R.hz
  K := R.K
  hKoffBd := R.hKoffBd
  cCore := R.cCore
  μC := R.μ
  μH := R.μ
  outC := R.outC
  outH := R.outH
  hctrlC := R.hctrlC
  hctrlH := R.hctrlH
  houtC := R.houtC
  houtH := R.houtH
  bdOut := R.bdOut
  houtPair := R.houtPair
  bridge := R.exists_bridge.choose
  bridgeBd := R.exists_bridge.choose_spec.choose
  hbridge := R.exists_bridge.choose_spec.choose_spec
  μW := R.μW
  near := R.near
  away := R.away
  hpartition := R.hpartition
  hawayOff := R.hawayOff
  nearBd := R.nearBd
  awayBd := R.exists_awayBd.choose
  hnearBd := R.hnearBd
  hawayBd := R.exists_awayBd.choose_spec
  hcoreHit := R.hcoreHit
  hq0det := R.hq0det

/-- **THE CAPSTONE `hasClass`, FROM THE REDUCED COLLAR-PAIR ROW.** The composite
`CollarPairGeom → CollarPairBuild → CapstoneSeamCorrectorT → hasClass`, landing the exact
`CapstoneAmbientSupply.hasClass` field type. -/
noncomputable def toHasClass :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  hasClass_ofCollarPair R.toCollarPairBuild

end CollarPairGeom

/-! ## §5. The six-obligation row produces the reduced one -/

namespace CollarPairGeomUnsub

variable (R : CollarPairGeomUnsub s t S hS φ hφ hφinj cd hseam d)

/-- **THE SIX-OBLIGATION PRODUCER** `CollarPairGeomUnsub → CollarPairGeom`, at `μ := 0`. The
`hq0Bd` field is discharged by `qZero_boundary_mem_of_splits`; the partition is transported along
the `μ = 0` instance of the collapse (`qCtrl z 0 0 = q₀ z`). -/
noncomputable def toCollarPairGeom : CollarPairGeom s t S hS φ hφ hφinj cd hseam d where
  z := R.z
  hz := R.hz
  K := R.K
  hKoffBd := R.hKoffBd
  cCore := R.cCore
  μ := 0
  outC := R.outC
  outH := R.outH
  hctrlC := R.hctrlC
  hctrlH := R.hctrlH
  houtC := R.houtC
  houtH := R.houtH
  bdOut := R.bdOut
  houtPair := R.houtPair
  hq0Bd := qZero_boundary_mem_of_splits R.z R.hctrlC R.hctrlH R.houtPair
  μW := R.μW
  near := R.near
  away := R.away
  hpartition := by
    rw [qCtrl_eq_singularSd_iterate_qZero, Function.iterate_zero_apply]; exact R.hpartition
  hawayOff := R.hawayOff
  nearBd := R.nearBd
  hnearBd := R.hnearBd
  hcoreHit := R.hcoreHit
  hq0det := R.hq0det

/-- **THE CAPSTONE `hasClass`, FROM SIX GEOMETRIC OBLIGATIONS.** The full #212 chain
`CollarPairGeomUnsub → CollarPairGeom → CollarPairBuild → CapstoneSeamCorrectorT → hasClass`. -/
noncomputable def toHasClass :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  CollarPairGeom.toHasClass R.toCollarPairGeom

end CollarPairGeomUnsub

/-! ## §6. `hq0det` is the single-witness atom (COMPATIBILITY — not on the producer path)

`hq0det` quantifies over the `subspaceChains`-membership proof. That is cosmetic: the theorem below
shows one witness suffices, so `hq0det` is *exactly* the shape of the vetted in-tree straddle atom
`CapstoneSeamTransferSupply.CapstoneSeamTransferResidual.hdetAB` (which fixes its witness). Nothing
in `toHasClass` uses this — it is a statement about the row, recorded so the atom is not mistaken
for a new obligation. Note `hdetAB` itself is NOT invoked: its ambient structure carries the refuted
`∖ Set.range φ` remainder signature (`seam-transfer-open-support-uninhabitable`). -/

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`hq0det` from a single witness.** Detection at one membership proof gives detection at every
one (`subspaceChains` membership is a `Prop`), so the `∀ hq` form is no stronger. -/
theorem hq0det_of_witness (z : cycles (TopCat.of s.M) (2 + 2))
    (hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qZero s S hS φ hφ hφinj z)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    (h : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
        relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
            (qZero s S hS φ hφ hφinj z)
            (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) hbd) ≠ 0) :
    ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier),
      x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
      ∀ (hq : chainBoundary
          (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
          (qZero s S hS φ hφ hφinj z)
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            ({x}ᶜ) (3 + 1)),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
        (qZero s S hS φ hφ hφinj z) hq ≠ 0 :=
  fun x hx hxA hxB _ => h x hx hxA hxB

end

end SKEFTHawking.PinPlusTraceCapstoneCollarPairGeom
