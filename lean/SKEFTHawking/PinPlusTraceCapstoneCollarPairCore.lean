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

end

end SKEFTHawking.PinPlusTraceCapstoneCollarPairCore
