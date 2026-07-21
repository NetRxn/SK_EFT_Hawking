/-
# Phase 5q.H (#212) — THE COLLAR-PAIR ROW, REDUCED AGAIN (6 geometric obligations → 5)

`PinPlusTraceCapstoneCollarPairGeom` cut the collar-pair row from eight geometric obligations to
six (`hctrlC`, `hctrlH`, `houtPair`, `hnearBd`, `hcoreHit`, `hq0det`), each elimination certified by
an `↔`. This module continues on the two the dossier ranked as *the real geometry*:

* **`hnearBd` — ELIMINATED (§2).** The relative-MV partition block of `CollarPairGeomUnsub`
  (`μW`, `near`, `away`, `hpartition`, `hawayOff`, `nearBd`, `hnearBd`) carries **no independent
  content**: the trivial partition `μW := 0`, `near := q₀ z`, `away := 0` satisfies `hpartition`
  (`Sd⁰ = id`, `+ 0`) and `hawayOff` (`0` is in every `subspaceChains`), and then `hnearBd` is
  *verbatim* `∂(q₀ z) ∈ C(∂W)` — which `qZero_boundary_mem_of_splits` already proves free from
  `hctrlC`/`hctrlH`/`houtPair`. The certificate is a genuine **two-way** one:
  `nonempty_collarPairGeomCore_iff` — `CollarPairGeomCore` (the row with the whole partition block
  deleted) is inhabited **iff** `CollarPairGeomUnsub` is, forgetting one way and the trivial
  partition the other. So the row's geometric obligations are exactly **FIVE**:
  `hctrlC`, `hctrlH`, `houtPair`, `hcoreHit`, `hq0det`.

  §1 records the companion fact that makes the elimination unsurprising: for *any* partition,
  `∂near ∈ C(∂W) ↔ ∂away ∈ C(∂W)` (`nearBd_mem_iff_awayBd_mem`) — the partition carries **one**
  relative-cycle obligation, dischargeable on either half, and the trivial partition discharges it
  on the half that is the whole chain.

* **`houtPair` — REDUCED, not eliminated (§3).** The collar-annulus weld is the deepest field in
  the row and it stays an obligation. What §3 does is factor it exactly:
  - `houtPair_exists_iff_weldSum_mem` — the existential over the `∂W`-subtype witness `bdOut` is
    pure bookkeeping: it holds **iff** the pushed sum lies in `C(∂W)` (`↔`).
  - `weldSum_eq_of_collarAnnulus` — if the two remainders share a **collar-annulus chain** `ann` on
    the attaching region (`outC = φ_# ann + outCbd`, `outH = ι_# ann + outHbd`), the annulus halves
    are *literally equal* after pushing (the glue identity `closedEmbeddingChain_mapChain_glue_eq`)
    and hence cancel in char 2. The weld sum collapses to the three genuine-boundary residuals.
  - `houtPair_iff_of_collarAnnulus` — so, **given** that refinement, `houtPair` holds **iff** the
    residual sum lies in `C(∂W)` (`↔`), and `houtPair_of_bdMem` / `houtPair_of_bdImageSubset`
    discharge it from three separate `∂W`-supports, the last stated purely **set-level**
    (`fromCyl '' Bd_C ⊆ ∂W`, …). Those three set-level containments are the sharply-named residual:
    the capstone's `∂W` has no set-level characterisation in tree, so they are where the remaining
    geometry actually lives.

* §4 `hctrlC_iff_topSplit_iterate` generalises `hctrlC_zero_iff_topSplit` from `μ = 0` to **every**
  `μ`: the cylinder-side co-adaptation is, at every subdivision count, *exactly* the subdivided
  top-face split `Sdᵘ(z@⊤) = φ_# cCore + outC`. That is the shape the in-tree open-cover
  subdivision engine produces, so it is the hook a future discharge of `hctrlC` will use.

* §5 shows the `μ = 0` normalisation is free on the **cylinder** side only: `hz` survives
  representative subdivision (`fundamentalClass_sdRep`) and the top slice commutes with it
  (`topSliceB_sdRep`), so the row's `hctrlC` on `Sdᵘ z` *is* `CollarPairGeom.hctrlC` at count `μ`
  on `z` (`hctrlC_sdRep_zero_iff_iterate`, an `↔`). No such move exists on the disk side —
  `diskDetectChain` is fixed — and none is claimed.

* **§6 is a NEW FENCE, not a route.** The in-tree `SurgeredEndDatum` carries exactly the three
  `∂W`-containments §3 asks for (`d.topFaceCovered`, `d.sphereFaceCovered`, the bottom face), which
  makes one instantiation of the collar-annulus refinement look free. It is settled-dead:
  `collarAnnulusOpen_toSeamTransferSeam` *constructs*, from the row's own `hctrlC`/`hctrlH` plus a
  refinement whose residuals sit at the OPEN-complement granularity, a verbatim
  `CapstoneSeamTransferSeam` — the shape refuted by `seam-transfer-open-support-uninhabitable` —
  and `not_collarAnnulusOpen_of_null` / `not_collarAnnulusOpen_row_of_null` turn it into `False`
  under the same null/non-bounding hypotheses. Scope: ONE direction only; a refinement at the
  coarser #210 shrunk-core granularity is NOT excluded, and §3 remains its live route.

## Fences

Nothing here touches `hcoreHit`. The registry fence
`collar-pair-maximal-core-reenters-refuted-support` stands: the *obvious* maximal-core shortcut
(`K = univ`) is closed because it re-enters `seam-transfer-open-support-uninhabitable`; that is a
one-direction result and is **not** a claim that every shortcut is closed. Nothing here routes
through `CapstoneSeamTransfer` / `hbd_ofTransfer`, and the `#210` shrunk-core support signature is
carried verbatim.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCollarPairGeom
import SKEFTHawking.PinPlusTraceSeamTransferNoGo

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
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.SingularRelativeEmpty
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
open SKEFTHawking.PinPlusTraceDiskCorePair
open SKEFTHawking.PinPlusTraceCapstoneCorrector
open SKEFTHawking.PinPlusTraceCapstoneCollarPair
open SKEFTHawking.PinPlusTraceCapstoneCollarPairGeom

namespace SKEFTHawking.PinPlusTraceCapstoneCollarPairCore

/-! ## §0. One more char-2 shuffle, isolated abstractly -/

/-- **The collar-annulus cancellation** (char 2): the shared annulus chain appears once on each side
of the glue, so `(A + a) + (A + b) + c = a + b + c`. Isolated on an abstract `ZMod 2`-module because
the concrete chain carriers are `rw`-hostile ("motive is not type correct"). -/
theorem char2_weld {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (A a b c : V) :
    A + a + (A + b) + c = a + b + c := by
  rw [show A + a + (A + b) + c = A + A + (a + b + c) from by abel, ZModModule.add_self, zero_add]

/-- **Absorbing a sub-split into the leading term**: `T = B + C` and `C = A + R` give
`T = B + A + R`. Isolated abstractly — rewriting the sub-split *inside* a concrete chain hypothesis
trips "motive is not type correct" on these carriers. -/
theorem split_absorb {V : Type} [AddCommGroup V] {T B C A R : V} (h1 : T = B + C)
    (h2 : C = A + R) : T = B + A + R := by
  rw [h1, h2, add_assoc]

section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

variable {s t S hS φ hφ hφinj cd hseam d}

/-! ## §1. The MV partition carries ONE relative-cycle obligation, on either half -/

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The partition's relative-cycle obligation is single and either-sided.** For any partition of
`Sd^μW (q₀ z)` into `near + away`, with the frozen glued chain a relative cycle, the near half is a
relative cycle **iff** the away half is: their boundaries differ by `Sd^μW ∂(q₀ z) ∈ C(∂W)`. This is
the two-sided strengthening of `CollarPairGeom.away_boundary_mem` (which proves only
`near ⟹ away`), and it is why deleting the whole partition block (§2) loses nothing. -/
theorem nearBd_mem_iff_awayBd_mem (z : cycles (TopCat.of s.M) (2 + 2)) (μW : ℕ)
    {near away : SingularChain
      (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)}
    (hpartition : ((⇑(singularSd
        (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)))^[μW])
        (qZero s S hS φ hφ hφinj z) = near + away)
    (hq0Bd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qZero s S hS φ hφ hφinj z)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)) :
    (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) near
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
      ↔ (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) away
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)) := by
  have hsum : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        near
      + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) away
      = ((⇑(singularSd (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (3 + 1)))^[μW])
          (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
            (qZero s S hS φ hφ hφinj z)) := by
    rw [← map_add, ← hpartition, singularSd_iterate_chainBoundary]
  have hmem := singularSd_iterate_mem_subspaceChains hq0Bd μW
  constructor
  · intro h
    rw [char2_left (hsum.symm.trans (add_comm _ _))]
    exact Submodule.add_mem _ hmem h
  · intro h
    rw [char2_left hsum.symm]
    exact Submodule.add_mem _ hmem h

/-! ## §2. `CollarPairGeomCore` — the FIVE-obligation row -/

variable (s t S hS φ hφ hφinj cd hseam d)

/-- **THE FIVE-OBLIGATION ROW.** `CollarPairGeomUnsub` with the entire relative-MV partition block
(`μW`, `near`, `away`, `hpartition`, `hawayOff`, `nearBd`, `hnearBd`) deleted. Every remaining field
is verbatim its `CollarPairGeomUnsub` counterpart. Its geometric obligations are exactly FIVE:
`hctrlC`, `hctrlH`, `houtPair`, `hcoreHit`, `hq0det`. Certified equivalent (as an inhabitation
problem) to `CollarPairGeomUnsub` by `nonempty_collarPairGeomCore_iff`. -/
structure CollarPairGeomCore where
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
  /-- **GEOMETRIC 1 — the top-face split** `z@⊤ = φ_# cCore + outC`. -/
  hctrlC : topSliceB s S hS φ hφ hφinj z
    = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC
  /-- **GEOMETRIC 2 — the disk-side split** on the canonical detecting chain. -/
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
  /-- **GEOMETRIC 3 — the collar-annulus weld**. -/
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
  /-- **GEOMETRIC 4 — the anti-fake tether**. -/
  hcoreHit :
    mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
    cCore ∉ subspaceChains (X := TopCat.of ↥S) (K ᶜ) (3 + 1)
  /-- **GEOMETRIC 5 — the seam straddle-detection atom**. -/
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

namespace CollarPairGeomCore

variable {s t S hS φ hφ hφinj cd hseam d}
variable (R : CollarPairGeomCore s t S hS φ hφ hφinj cd hseam d)

omit [PreconnectedSpace s.M] in
/-- The frozen glued chain of a five-obligation row is a relative cycle of `(W, ∂W)` — the `μ = 0`
instance of `qZero_boundary_mem_of_splits`, with `hctrlC` already in top-face form. -/
theorem qZero_boundary_mem :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qZero s S hS φ hφ hφinj R.z)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) :=
  qZero_boundary_mem_of_splits R.z
    ((hctrlC_zero_iff_topSplit R.z R.cCore R.outC).mpr R.hctrlC) R.hctrlH R.houtPair

/-- **THE `hnearBd` ELIMINATION** `CollarPairGeomCore → CollarPairGeomUnsub`, via the TRIVIAL
partition `μW := 0`, `near := q₀ z`, `away := 0`. `hpartition` is `Sd⁰ = id` plus `+ 0`; `hawayOff`
is `0 ∈ C(_)`; and `hnearBd` is then exactly `∂(q₀ z) ∈ C(∂W)`, which the splits already give. So
the partition block — including the field the dossier ranked as genuinely open — carries no
independent geometric content. -/
noncomputable def toCollarPairGeomUnsub : CollarPairGeomUnsub s t S hS φ hφ hφinj cd hseam d where
  z := R.z
  hz := R.hz
  K := R.K
  hKoffBd := R.hKoffBd
  cCore := R.cCore
  outC := R.outC
  outH := R.outH
  hctrlC := R.hctrlC
  hctrlH := R.hctrlH
  houtC := R.houtC
  houtH := R.houtH
  bdOut := R.bdOut
  houtPair := R.houtPair
  μW := 0
  near := qZero s S hS φ hφ hφinj R.z
  away := 0
  hpartition := by rw [Function.iterate_zero_apply, add_zero]
  hawayOff := Submodule.zero_mem _
  nearBd := R.qZero_boundary_mem.choose
  hnearBd := R.qZero_boundary_mem.choose_spec.symm
  hcoreHit := R.hcoreHit
  hq0det := R.hq0det

/-- **THE CAPSTONE `hasClass`, FROM FIVE GEOMETRIC OBLIGATIONS.** The full #212 chain
`CollarPairGeomCore → CollarPairGeomUnsub → CollarPairGeom → CollarPairBuild →
CapstoneSeamCorrectorT → hasClass`. -/
noncomputable def toHasClass :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  CollarPairGeomUnsub.toHasClass R.toCollarPairGeomUnsub

end CollarPairGeomCore

variable {s t S hS φ hφ hφinj cd hseam d}

/-- The forgetful direction: a six-obligation row has a five-obligation row underneath it (drop the
partition block). Together with `CollarPairGeomCore.toCollarPairGeomUnsub` this makes the reduction
an equivalence, not a strengthening. -/
noncomputable def CollarPairGeomCore.ofUnsub
    (R : CollarPairGeomUnsub s t S hS φ hφ hφinj cd hseam d) :
    CollarPairGeomCore s t S hS φ hφ hφinj cd hseam d where
  z := R.z
  hz := R.hz
  K := R.K
  hKoffBd := R.hKoffBd
  cCore := R.cCore
  outC := R.outC
  outH := R.outH
  hctrlC := R.hctrlC
  hctrlH := R.hctrlH
  houtC := R.houtC
  houtH := R.houtH
  bdOut := R.bdOut
  houtPair := R.houtPair
  hcoreHit := R.hcoreHit
  hq0det := R.hq0det

omit [PreconnectedSpace s.M] in
/-- **THE `hnearBd` EQUIVALENCE CERTIFICATE.** The five-obligation row is inhabited **iff** the
six-obligation row is: forgetting the partition block one way, the trivial partition the other. So
dropping `hnearBd` (and the rest of the MV block) neither weakens nor strengthens the #212 row — it
is the same inhabitation problem, and the collar-pair row's independent geometric obligations are
`hctrlC`, `hctrlH`, `houtPair`, `hcoreHit`, `hq0det`: **five**. -/
theorem nonempty_collarPairGeomCore_iff :
    Nonempty (CollarPairGeomCore s t S hS φ hφ hφinj cd hseam d)
      ↔ Nonempty (CollarPairGeomUnsub s t S hS φ hφ hφinj cd hseam d) :=
  ⟨fun ⟨R⟩ => ⟨R.toCollarPairGeomUnsub⟩, fun ⟨R⟩ => ⟨CollarPairGeomCore.ofUnsub R⟩⟩

/-! ## §3. `houtPair`, factored: the annulus cancels, three `∂W`-supports remain -/

/-- **The weld sum** — the left-hand side of `houtPair`: the two pushed remainders plus the pushed
bottom face. -/
noncomputable def weldSum (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    (outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1))
    (outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)) :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) :=
  closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
      (3 + 1) outC
    + closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
      (3 + 1) outH
    + closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
      (3 + 1) (ctrlBottom s S hS φ hφ hφinj z μ)

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The `bdOut` existential is bookkeeping.** `houtPair` is inhabitable (over its `∂W`-subtype
witness) **exactly when** the weld sum lies in `C(∂W)` — `subspaceChains` *is* the range of
`chainIncl`. An `↔`; it moves the field from an equation-with-witness to a support statement. -/
theorem houtPair_exists_iff_weldSum_mem (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    (outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1))
    (outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)) :
    (∃ bdOut : SingularChain
        (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1),
        weldSum z μ outC outH
          = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
              (3 + 1) bdOut)
      ↔ weldSum z μ outC outH
          ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
              (3 + 1) :=
  ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE COLLAR ANNULUS CANCELS.** If the two remainders share a collar-annulus chain `ann` on the
attaching region — `outC = φ_# ann + outCbd` on the cylinder end, `outH = ι_# ann + outHbd` on the
handle — then the two pushed annulus halves are *literally the same chain* in the trace carrier (the
glue identity `closedEmbeddingChain_mapChain_glue_eq`, exactly the one that cancels the seam core in
`qCtrl_boundary_eq_of_splits`), so in char 2 they cancel and the weld sum collapses to the three
genuine-boundary residuals. This is the structural content of "the collar-annulus weld". -/
theorem weldSum_eq_of_collarAnnulus (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    {outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    (ann : SingularChain (TopCat.of ↥S) (3 + 1))
    (outCbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1))
    (outHbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1))
    (hC : outC = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) ann + outCbd)
    (hH : outH = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) ann + outHbd) :
    weldSum z μ outC outH
      = weldSum z μ outCbd outHbd := by
  have hglue := closedEmbeddingChain_mapChain_glue_eq
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
    (seamLegB s S hS φ hφ hφinj) (seamLegHa s S hS φ hφ hφinj)
    (ContinuousMap.ext (fun a => (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a))
    (3 + 1) ann
  simp only [weldSum]
  rw [hC, hH, closedEmbeddingChain_add, closedEmbeddingChain_add, hglue]
  exact char2_weld _ _ _ _

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE `houtPair` FACTORISATION CERTIFICATE.** *Given* the collar-annulus refinement, `houtPair`
holds **iff** the three genuine-boundary residuals sum into `C(∂W)` — an `↔`. The annulus part of
the two remainders is therefore irrelevant to the weld: all the weld asks is that what is left after
the annulus cancels is a `∂W`-chain. -/
theorem houtPair_iff_of_collarAnnulus (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    {outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    (ann : SingularChain (TopCat.of ↥S) (3 + 1))
    (outCbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1))
    (outHbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1))
    (hC : outC = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) ann + outCbd)
    (hH : outH = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) ann + outHbd) :
    (∃ bdOut : SingularChain
        (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1),
        weldSum z μ outC outH
          = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
              (3 + 1) bdOut)
      ↔ weldSum z μ outCbd outHbd
          ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
              (3 + 1) := by
  rw [houtPair_exists_iff_weldSum_mem z μ outC outH,
    weldSum_eq_of_collarAnnulus z μ ann outCbd outHbd hC hH]

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`houtPair` from three `∂W`-supports.** With the annulus refinement in hand, the weld follows
from the three residuals being `∂W`-chains separately. -/
theorem houtPair_of_bdMem (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    {outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    (ann : SingularChain (TopCat.of ↥S) (3 + 1))
    (outCbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1))
    (outHbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1))
    (hC : outC = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) ann + outCbd)
    (hH : outH = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) ann + outHbd)
    (hbdC : closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) outCbd
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    (hbdH : closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
        (3 + 1) outHbd
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    (hbdBot : closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) (ctrlBottom s S hS φ hφ hφinj z μ)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)) :
    ∃ bdOut : SingularChain
      (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1),
      weldSum z μ outC outH
        = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
            (3 + 1) bdOut :=
  (houtPair_iff_of_collarAnnulus z μ ann outCbd outHbd hC hH).mpr
    (Submodule.add_mem _ (Submodule.add_mem _ hbdC hbdH) hbdBot)

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`houtPair` from three SET-LEVEL containments** — the sharply-named residual. Each residual is
supported in a set of its own piece whose image in the trace carrier lies inside `∂W`. Since the
capstone's `∂W` has no set-level characterisation in tree, these three containments are exactly
where the remaining collar-annulus geometry lives. -/
theorem houtPair_of_bdImageSubset (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    {outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    (ann : SingularChain (TopCat.of ↥S) (3 + 1))
    (outCbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1))
    (outHbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1))
    (hC : outC = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) ann + outCbd)
    (hH : outH = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) ann + outHbd)
    {BdC BdBot : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B}
    {BdH : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha}
    (hsC : outCbd ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) BdC (3 + 1))
    (hsH : outHbd ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) BdH (3 + 1))
    (hsBot : ctrlBottom s S hS φ hφ hφinj z μ ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) BdBot (3 + 1))
    (hiC : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl '' BdC
      ⊆ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
    (hiH : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle '' BdH
      ⊆ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
    (hiBot : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl '' BdBot
      ⊆ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) :
    ∃ bdOut : SingularChain
      (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1),
      weldSum z μ outC outH
        = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
            (3 + 1) bdOut :=
  houtPair_of_bdMem z μ ann outCbd outHbd hC hH
    (subspaceChains_mono hiC (3 + 1) (closedEmbeddingChain_mem_of_mem _ (3 + 1) _ hsC))
    (subspaceChains_mono hiH (3 + 1) (closedEmbeddingChain_mem_of_mem _ (3 + 1) _ hsH))
    (subspaceChains_mono hiBot (3 + 1) (closedEmbeddingChain_mem_of_mem _ (3 + 1) _ hsBot))

/-! ## §4. `hctrlC` is the subdivided top-face split, at EVERY count -/

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`hctrlC` unmasked at every subdivision count.** `ctrlCyl z μ` is `Sdᵘ` of a prism over the
cycle `z`, so its boundary is `Sdᵘ` of the two endpoint slices; the bottom one is `ctrlBottom z μ`
verbatim, and cancels. So `CollarPairGeom.hctrlC` at count `μ` is **exactly** the subdivided
top-face split `Sdᵘ(z@⊤) = φ_# cCore + outC`. This generalises `hctrlC_zero_iff_topSplit` off
`μ = 0` — and the right-hand side is precisely the shape the in-tree open-cover subdivision engine
produces, so this is the hook for a future discharge of `hctrlC`. An `↔`, both directions. -/
theorem hctrlC_iff_topSplit_iterate (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    (cCore : SingularChain (TopCat.of ↥S) (3 + 1))
    (outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)) :
    (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
        (ctrlCyl s S hS φ hφ hφinj z μ)
      = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC
        + ctrlBottom s S hS φ hφ hφinj z μ)
      ↔ ((⇑(singularSd (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)))^[μ])
            (topSliceB s S hS φ hφ hφinj z)
          = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC := by
  have hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
        (capstoneCylChainT s S hS φ hφ hφinj z)
      = topSliceB s S hS φ hφ hφinj z + ctrlBottom s S hS φ hφ hφinj z 0 :=
    chainBoundary_crossChain 3 (z : SingularChain (TopCat.of s.M) (3 + 1)) z.2
  have hiter : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
        (ctrlCyl s S hS φ hφ hφinj z μ)
      = ((⇑(singularSd (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)))^[μ])
          (topSliceB s S hS φ hφ hφinj z)
        + ctrlBottom s S hS φ hφ hφinj z μ := by
    rw [ctrlCyl, singularSd_iterate_chainBoundary, hbd, singularSd_iterate_add]
    rfl
  rw [hiter]
  exact add_left_inj _

/-! ## §5. The `μ = 0` normalisation is FREE on the cylinder side (and only there)

`CollarPairGeomUnsub` / `CollarPairGeomCore` fix the subdivision count at `0`, which looks like a
loss: the in-tree open-cover splitting engine only ever produces splits of a *subdivided* chain. §5
shows the loss is nil on the **cylinder** side, because the fundamental cycle `z` is itself a field
of the row and `hz` only pins its homology *class*: replacing `z` by `Sdᵘ z` keeps `hz`
(`fundamentalClass_sdRep`) and turns the `μ = 0` top-face obligation into the count-`μ` one
(`hctrlC_sdRep_zero_iff_iterate`, an `↔`) — because the top slice commutes with subdivision
(`topSliceB_sdRep`, the new naturality square).

⚠ **This does NOT extend to the disk side, and no claim is made that it does.** `hctrlH`'s chain is
`diskDetectChain`, a FIXED in-tree chain with no representative freedom, so at `μ = 0` it is not in
the engine's shape. That asymmetry — cylinder side free, disk side not — is the honest cost of the
`μ = 0` normalisation, and it is where a future discharge of `hctrlH` has to start (see
`PinPlusTraceSeamResidualNarrow` §3, whose split is stated at a subdivision count `μ` produced by
the engine). Nothing here says the disk side is impossible at `μ = 0`; it says it is not reachable
by the same representative-subdivision move. -/

/-- `Sdᵘ` of a fundamental cycle, packaged back up as a cycle. -/
noncomputable def sdRep (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ) :
    cycles (TopCat.of s.M) (2 + 2) :=
  ⟨((⇑(singularSd (TopCat.of s.M) (2 + 2)))^[μ]) (z : SingularChain (TopCat.of s.M) (2 + 2)),
    SingularConnSquareLHSExplicit.singularSd_iterate_mem_cycles (TopCat.of s.M) 3 μ _ z.2⟩

omit [PreconnectedSpace s.M] in
/-- **`hz` survives representative subdivision.** `Sdᵘ z` still represents THE fundamental class
(`homology_mk_singularSd_iterate`), so the `z`/`hz` pair of the row may be replaced by
`sdRep z μ`/this at will. -/
theorem fundamentalClass_sdRep (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z) :
    SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) (sdRep z μ) :=
  hz.trans (SingularConnSquareLHSExplicit.homology_mk_singularSd_iterate
    (TopCat.of s.M) 3 μ (z : SingularChain (TopCat.of s.M) (2 + 2)) z.2 _)

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The top slice commutes with representative subdivision** — the `slice`-instance of the
pushforward naturality square `mapChain_singularSd_iterate`. -/
theorem topSliceB_sdRep (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ) :
    topSliceB s S hS φ hφ hφinj (sdRep z μ)
      = ((⇑(singularSd (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)))^[μ])
          (topSliceB s S hS φ hφ hφinj z) :=
  mapChain_singularSd_iterate _ μ _

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE `μ = 0` NORMALISATION CERTIFICATE (cylinder side).** The five-obligation row's `hctrlC` on
the subdivided representative `Sdᵘ z` is *exactly* `CollarPairGeom.hctrlC` at count `μ` on `z` — an
`↔`. Together with `fundamentalClass_sdRep` (which keeps `hz`), this says the cylinder side of the
row loses nothing by fixing `μ = 0`: subdivide the representative instead of the chain. -/
theorem hctrlC_sdRep_zero_iff_iterate (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    (cCore : SingularChain (TopCat.of ↥S) (3 + 1))
    (outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)) :
    (topSliceB s S hS φ hφ hφinj (sdRep z μ)
        = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC)
      ↔ (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
            (ctrlCyl s S hS φ hφ hφinj z μ)
          = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC
            + ctrlBottom s S hS φ hφ hφinj z μ) := by
  rw [topSliceB_sdRep]
  exact (hctrlC_iff_topSplit_iterate z μ cCore outC).symm

/-! ## §6. ⛔ A FENCE: the OPEN-COMPLEMENT collar-annulus refinement is the refuted shape

§3 reduces `houtPair` to a collar-annulus refinement plus three `∂W`-supports. The in-tree data
makes one instantiation of those supports look free: `SurgeredEndDatum` carries exactly
`d.topFaceCovered` (`fromCyl '' (topface ∖ range φ) ⊆ ∂W`), `d.sphereFaceCovered`
(`fromHandle '' (sphere ∖ S) ⊆ ∂W`) and the bottom-face fact, and those are precisely the three
supports `hbd_ofTransfer` consumes. **That instantiation is settled-dead.**

`collarAnnulusOpen_toSeamTransferSeam` proves it by construction: a collar-annulus refinement whose
residuals sit at the OPEN-complement granularity (`outCbd ∈ C(topface ∖ range φ)`,
`outHbd ∈ C(sphere ∖ S)`) assembles — together with the row's own `hctrlC`/`hctrlH` — into a
*verbatim* `CapstoneSeamTransferSeam` at `cSeam := cCore + ann`, `cHa := diskDetectChain`. That
structure is the one refuted by `seam-transfer-open-support-uninhabitable`
(`isEmpty_capstoneSeamTransferSeam_of_null`), so `not_collarAnnulusOpen_of_null` turns the
refinement into `False` under the same null/non-bounding hypotheses.

⚠ **Scope — do not overstate.** What is proved is the ONE direction
`open-complement refinement ⟹ the refuted structure`. It is NOT proved that every collar-annulus
refinement is impossible: a refinement whose residuals sit at a *strictly coarser* granularity —
the closed-complement picture the #210 repair adopted (`topface ∖ φ '' K` for a shrunk core `K`) —
is not excluded by anything here, and `houtPair_of_bdMem` / `houtPair_of_bdImageSubset` (§3) remain
the live route for it. Cite this fence as "the free-looking `d.topFaceCovered` instantiation is
closed", never as "the collar-annulus refinement is closed". -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE STRUCTURAL FORCING.** A collar-annulus refinement of the two remainders at the
OPEN-complement granularity, on top of the five-obligation row's own `hctrlC`/`hctrlH`, *is* an
inhabitant of the refuted `CapstoneSeamTransferSeam` shape: the seam core absorbs the annulus
(`cSeam := cCore + ann`) and the two residuals are verbatim its `wOut`/`vOut` with verbatim its
`hwOut`/`hvOut` supports. So this refinement cannot be taken. -/
noncomputable def collarAnnulusOpen_toSeamTransferSeam (z : cycles (TopCat.of s.M) (2 + 2))
    {cCore ann : SingularChain (TopCat.of ↥S) (3 + 1)}
    {outC outCbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outH outHbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    (hctrlC : topSliceB s S hS φ hφ hφinj z
      = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC)
    (hctrlH : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
        diskDetectChain
      = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cCore + outH)
    (hCsplit : outC = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) ann + outCbd)
    (hHsplit : outH = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) ann + outHbd)
    (hCbd : outCbd ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1))
    (hHbd : outHbd ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1)) :
    CapstoneSeamTransferSeam s S hS φ hφ hφinj z diskDetectChain where
  cSeam := cCore + ann
  wOut := outCbd
  hsplit := by rw [map_add]; exact split_absorb hctrlC hCsplit
  hwOut := hCbd
  vOut := outHbd
  hsplitHa := by rw [map_add]; exact split_absorb hctrlH hHsplit
  hvOut := hHbd

/-- **THE FENCE, as a refutation.** Under the same null/non-bounding hypotheses that kill the
open-support seam-transfer shape (`isEmpty_capstoneSeamTransferSeam_of_null`), no collar-annulus
refinement at the open-complement granularity exists on top of the row's splits. This is the reason
`houtPair` cannot be discharged by routing its residuals through `d.topFaceCovered` /
`d.sphereFaceCovered`, even though those are sitting in the `SurgeredEndDatum`. -/
theorem not_collarAnnulusOpen_of_null (z : cycles (TopCat.of s.M) (2 + 2))
    (hA : ∀ w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1),
      w ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        (Set.range φ) (3 + 1) →
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 w = 0 →
      ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
        chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b = w)
    (hO : ∀ w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1),
      w ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 w = 0 →
      ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
        chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b = w)
    (hne : ¬ ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b
        = topSliceB s S hS φ hφ hφinj z)
    {cCore ann : SingularChain (TopCat.of ↥S) (3 + 1)}
    {outC outCbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outH outHbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    (hctrlC : topSliceB s S hS φ hφ hφinj z
      = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC)
    (hctrlH : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
        diskDetectChain
      = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cCore + outH)
    (hCsplit : outC = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) ann + outCbd)
    (hHsplit : outH = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) ann + outHbd)
    (hCbd : outCbd ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1))
    (hHbd : outHbd ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1)) : False :=
  (PinPlusTraceSeamTransferNoGo.isEmpty_capstoneSeamTransferSeam_of_null hA hO hne).false
    (collarAnnulusOpen_toSeamTransferSeam z hctrlC hctrlH hCsplit hHsplit hCbd hHbd)

/-- **THE FENCE AT THE ROW.** No inhabitant of the five-obligation row admits an open-complement
collar-annulus refinement of its two remainders (under the null/non-bounding hypotheses). Stated
directly on `CollarPairGeomCore` so the fence is citable where the temptation arises: `houtPair`'s
residuals must NOT be routed to `d.topFaceCovered` / `d.sphereFaceCovered`. -/
theorem not_collarAnnulusOpen_row_of_null
    (R : CollarPairGeomCore s t S hS φ hφ hφinj cd hseam d)
    (hA : ∀ w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1),
      w ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        (Set.range φ) (3 + 1) →
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 w = 0 →
      ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
        chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b = w)
    (hO : ∀ w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1),
      w ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) 3 w = 0 →
      ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
        chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b = w)
    (hne : ¬ ∃ b : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2),
      chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) b
        = topSliceB s S hS φ hφ hφinj R.z)
    {ann : SingularChain (TopCat.of ↥S) (3 + 1)}
    {outCbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outHbd : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    (hCsplit : R.outC = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) ann + outCbd)
    (hHsplit : R.outH = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) ann + outHbd)
    (hCbd : outCbd ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1))
    (hHbd : outHbd ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1)) : False :=
  not_collarAnnulusOpen_of_null R.z hA hO hne R.hctrlC R.hctrlH hCsplit hHsplit hCbd hHbd

end

end SKEFTHawking.PinPlusTraceCapstoneCollarPairCore
