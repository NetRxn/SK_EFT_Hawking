/-
# Phase 5q.H (#212) — THE LOCAL-HOMOLOGY VERDICT ON `hdetAB`: NO ONE-PIECE CHAIN DETECTS AT A SEAM
POINT, EVEN UP TO HOMOLOGY.

`…CollarPairSeamDetect` §5 refuted the two *literal* one-sided congruence routes: the collar chain of
a `SeamCollarChainDatum`-style discharge of `hdetAB` cannot BE the pushed cylinder prism
(`collarChain_ne_cylPush`) and cannot BE the pushed disk chain (`collarChain_ne_diskPush`). Those are
support-level statements about two particular chains. This module replaces them with the structural
fact behind them — at the level of local homology, and universally over the collar chain.

## 1. The boundary-face vanishing, carried into the carrier (§1)

`SingularFaceLocalHomologyVanish` proves that a manifold-with-boundary has **zero** local homology at
a boundary-face point, in every degree. Both closed pieces of the trace carrier meet a seam point in
exactly that position:

* the cylinder piece `A = range fromCyl ≅ M × [0,1]` meets it at a **TOP-FACE** point — this is what
  `hφtop` says — so `cylPiece_localHomology_zero`;
* the handle piece `B = range fromHandle ≅ D⁵` meets it at a **BOUNDARY-SPHERE** point — the side
  condition `hsphere`, i.e. that the handle attaches along `∂D⁵`, the one genuinely geometric input
  the abstract `HandleAttachment` interface does not already carry — so
  `handlePiece_localHomology_zero`.

## 2. The verdict (§2–§3)

`relClassOf_eq_zero_of_cylSupported` / `relClassOf_eq_zero_of_handleSupported`: **any** 5-chain of
the carrier supported in **one** closed piece has local class `0` at a seam point. Consequently
(`relClassOf_eq_zero_of_cylHomologous` / `…_handleHomologous`, via
`SingularRelClassHomologous.relClassOf_eq_of_homologous`) so does any chain merely *homologous rel*
`{x}ᶜ` to a one-piece chain — `c = p + ∂w + e`, `p` in one piece, `e` off the point. The `w = 0` case
is precisely the congruence route (`SingularRelativeCoverMV.relClassOf_eq_of_congr`) that
`…SeamDetect` §5 attacked chain-by-chain; here it dies for **every** one-piece `p` at once, with no
reference to which chain `p` is.

`not_hdetAB_at_of_cylHomologous` / `not_hdetAB_at_of_handleHomologous` state the consequence in the
row's own localized shape — the per-parameter body of `hdetCore` in
`…SeamDetect.CollarPairCoreRow.ofSeamCoreLocal`: the detection obligation at a seam point is **FALSE**
as soon as `qGen z cHa` admits a one-piece representative there.

## 3. The binary-partition detection ban, KERNEL-CHECKED (§4)

`not_restrictsToRelGenOn_cylRange_at_seamCore`: for **every** class `αU` on the pair
`(range fromCyl, ∂W ∩ range fromCyl)` and **every** interior generator family `gen`, the
excision-pushforward fails `RestrictsToRelGenOn` on the cyl side at a core seam point. That is the
`hdetU` field of `PinPlusTraceCapstoneRelFund.CapstoneRelFundPartitionDatum` at `U = range fromCyl`,
so the datum is uninhabitable there. Engine:
`SingularFacePieceDetect.not_restrictsToRelGenOn_of_faceVanish` — the face companion of the banked
`SingularRelativeDisjointUnionLocal.restrictBd_excisionMap_eq_zero` (which kills a piece at a point
it MISSES; this kills it at a point it contains only in its own boundary face).

This is the `capstone-binary-partition-detection-uninhabitable` record's own **encode-on-settle**
condition met: *"the kernel-encodable core = `boundary-face local homology vanishes ⟹ hdetU(seam)
false`; formalizing the boundary-local-homology lemma is itself a task — when it lands, promote this
ban to `KERNEL_NOGO_REGISTRY`."* It has landed.

## 4. What this says about the LOCAL MAYER–VIETORIS route (read before building it)

The vanishing above is the *good* half of the local-MV picture: with both piece-local `H₅` zero, a
relative Mayer–Vietoris sequence for the pair `{A, B}` would have an INJECTIVE connecting map
`H₅(W, W∖x) → H₄(A ∩ B, (A∩B)∖x)`, turning `hdetAB` into detection of the seam-matching 4-chain in
the seam's own local `H₄`. **That sequence is not available for the pieces as they stand**: `A` and
`B` are CLOSED and a seam point is interior to neither, so `int A ∪ int B ≠ W` and the cover is not
excisive — exactly the gap the `capstone-binary-partition-detection-uninhabitable` record names
("genuine RELATIVE COVER-MV GLUING — W = A ∪ B **open** … which is NOT yet in-tree"). Nothing in this
module supplies it, and nothing here should be read as supplying it.

What this module *does* settle is the negative half, unconditionally: **the local class at a seam
point is irreducibly a two-piece quantity.** Neither closed piece contributes any of it — not the
cylinder, not the handle, not up to homology — so any discharge of `hdetAB` must exhibit genuine
seam-straddling content. That is the formal content of the `#156` wall analysis, previously carried
only as prose ("the closed piece's summand restricts through `H₅(sub U, sub U∖{x'})` at a
BOUNDARY-FACE point … which vanishes").

## Fences honored

* `collar-pair-closed-seam-attached-collar-bridge-is-FALSE` — no bridge, no collar retraction, no
  `sphere ∖ S` support; the only sets named are the two gluing ranges and single-point complements.
* `collar-pair-open-complement-annulus-is-refuted-shape` — nothing routes through
  `SurgeredEndDatum.topFaceCovered`; the surgered-end datum does not appear at all (these statements
  are independent of it).
* `collar-pair-maximal-core-reenters-refuted-support` — no core is chosen; `seamCore` is not used.
* `seam-transfer-open-support-uninhabitable` — nothing routes through `CapstoneSeamTransfer`,
  `hbd_ofTransfer` or `hasClass_ofTransferCorrector`.
* `collar-pair-coarse-core-does-not-relax-the-disk-side` — nothing is subdivided; `hctrlH` unused.
* `capstone-choose-representative-corrector-uninhabitable` — no representative is chosen at all: the
  results are universal over the chain.
* The shared-`cCore` co-adaptation is not built, referenced, or needed.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCollarPairSeamDetect
import SKEFTHawking.SingularFaceLocalHomologyVanish
import SKEFTHawking.SingularFacePieceDetect

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelClassHomologous
open SKEFTHawking.PinPlusTraceCapstoneCollarPair
open SKEFTHawking.PinPlusTraceCapstoneCollarPairMatch
open SKEFTHawking.SingularFaceLocalHomologyVanish
open SKEFTHawking.SingularFacePieceDetect
open SKEFTHawking.SingularExcisionIso (restr excisionMap)
open SKEFTHawking.SingularRelativeDisjointUnionFundClass (RestrictsToRelGenOn)
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCollarPairEnd
open SKEFTHawking.PinPlusTraceCapstoneCollarPairSeamDetect
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder (cylW)

namespace SKEFTHawking.PinPlusTraceCapstoneCollarPairSeamLocalHom

noncomputable section

variable {s : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)} [T2Space s.M]
  [CompactSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  {S : Set D5} {hS : IsClosed S} {φ : ↥S → s.M × Set.Icc (0 : ℝ) 1}
  {hφ : Continuous φ} {hφinj : Function.Injective φ}

/-! ## §1. Both closed pieces are FACE-FLAT at a seam point -/

omit [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- The seam point lies in the cylinder range (the gluing identification `glue`). -/
theorem seamPoint_mem_range_fromCyl (a : ↥S) :
    seamPoint s S hS φ hφ hφinj a
      ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl :=
  ⟨φ a, (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- The seam point lies in the handle range (by the definition of `seamPoint`). -/
theorem seamPoint_mem_range_fromHandle (a : ↥S) :
    seamPoint s S hS φ hφ hφinj a
      ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle :=
  ⟨(a : D5), rfl⟩

/-- **The cylinder piece of the carrier IS the cylinder** — `fromCyl` is a closed embedding, hence a
homeomorphism onto its range. -/
def cylPieceHomeo :
    cylW s.M ≃ₜ ↥(Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl) :=
  (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding.toHomeomorph

/-- **The handle piece of the carrier IS the disk** — `fromHandle` is a closed embedding. -/
def handlePieceHomeo :
    D5 ≃ₜ ↥(Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle) :=
  (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding.toHomeomorph

omit [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- Under the cylinder identification the attaching image `φ a` IS the seam point. -/
theorem cylPieceHomeo_phi (a : ↥S) :
    cylPieceHomeo (s := s) (S := S) (hS := hS) (φ := φ) (hφ := hφ) (hφinj := hφinj) (φ a)
      = (⟨seamPoint s S hS φ hφ hφinj a, seamPoint_mem_range_fromCyl a⟩ :
        ↥(Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)) :=
  Subtype.ext ((ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a)

/-- **THE CYLINDER PIECE IS FACE-FLAT AT EVERY SEAM POINT.** The intrinsic local homology of the
closed cylinder piece `A = range fromCyl ≅ M × [0,1]` vanishes at `seamPoint a`, in every degree: the
seam point is a **TOP-FACE** point of the cylinder (`hφtop`), and a manifold-with-boundary carries no
local homology at a boundary point
(`SingularFaceLocalHomologyVanish.cylTopFace_localHomology_zero`, transported along the closed
embedding `fromCyl` by `localHomology_zero_of_homeo`). -/
theorem cylPiece_localHomology_zero (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1) (a : ↥S) (k : ℕ)
    (β : RelativeHomology
      (({(⟨seamPoint s S hS φ hφ hφinj a, seamPoint_mem_range_fromCyl a⟩ :
          ↥(Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl))}ᶜ) :
        Set ↑(sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl))) (k + 2)) :
    β = 0 := by
  haveI : T1Space (cylW s.M) := inferInstance
  have hsymm : (cylPieceHomeo (s := s) (S := S) (hS := hS) (φ := φ) (hφ := hφ)
      (hφinj := hφinj)).symm (⟨seamPoint s S hS φ hφ hφinj a, seamPoint_mem_range_fromCyl a⟩ :
        ↥(Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)) = φ a := by
    rw [← cylPieceHomeo_phi a, Homeomorph.symm_apply_apply]
  refine localHomology_zero_of_homeo
    (X := sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl))
    (Y := TopCat.of (cylW s.M))
    (x := (⟨seamPoint s S hS φ hφ hφinj a, seamPoint_mem_range_fromCyl a⟩ :
      ↥(Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)))
    (cylPieceHomeo).symm (k + 2) ?_ β
  intro δ
  exact relativeHomology_zero_congr (B := (({φ a}ᶜ) : Set ↑(TopCat.of (cylW s.M))))
    (by rw [hsymm]) (k + 2)
    (fun ε => cylTopFace_localHomology_zero (m' := 2) (M := s.M) (φ a).1 (hφtop a) k ε) δ

omit [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- Under the handle identification the attaching parameter IS the seam point — by the definition of
`seamPoint`. -/
theorem handlePieceHomeo_param (a : ↥S) :
    handlePieceHomeo (s := s) (S := S) (hS := hS) (φ := φ) (hφ := hφ) (hφinj := hφinj) (a : D5)
      = (⟨seamPoint s S hS φ hφ hφinj a, seamPoint_mem_range_fromHandle a⟩ :
        ↥(Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)) :=
  rfl

omit [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE HANDLE PIECE IS FACE-FLAT AT EVERY SEAM POINT ON THE ATTACHING SPHERE.** The intrinsic
local homology of the closed handle piece `B = range fromHandle ≅ D⁵` vanishes at `seamPoint a`, in
every degree, once the attaching parameter lies on `∂D⁵`: a closed ball carries no local homology at
a boundary-sphere point (`SingularFaceLocalHomologyVanish.closedBall_faceLocalHomology_zero`).

`hsphere` is the one genuinely geometric side condition here — the abstract `HandleAttachment`
interface admits an arbitrary closed `S ⊆ D⁵`, while a *handle* attaches along the boundary sphere.
It is not free: at an interior parameter the same local homology is `ℤ/2` and NONZERO
(`SingularFaceLocalHomologyVanish.exists_ne_zero_closedBall_interiorLocalHomology`). -/
theorem handlePiece_localHomology_zero {a : ↥S}
    (hsphere : ‖((a : D5) : EuclideanSpace ℝ (Fin 5))‖ = 1) (k : ℕ)
    (β : RelativeHomology
      (({(⟨seamPoint s S hS φ hφ hφinj a, seamPoint_mem_range_fromHandle a⟩ :
          ↥(Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle))}ᶜ) :
        Set ↑(sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle))) (k + 2)) :
    β = 0 := by
  have hsymm : (handlePieceHomeo (s := s) (S := S) (hS := hS) (φ := φ) (hφ := hφ)
      (hφinj := hφinj)).symm (⟨seamPoint s S hS φ hφ hφinj a, seamPoint_mem_range_fromHandle a⟩ :
        ↥(Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)) = (a : D5) := by
    rw [← handlePieceHomeo_param a, Homeomorph.symm_apply_apply]
  refine localHomology_zero_of_homeo
    (X := sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle))
    (Y := TopCat.of D5)
    (x := (⟨seamPoint s S hS φ hφ hφinj a, seamPoint_mem_range_fromHandle a⟩ :
      ↥(Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)))
    (handlePieceHomeo).symm (k + 2) ?_ β
  intro δ
  exact relativeHomology_zero_congr (B := (({(a : D5)}ᶜ) : Set ↑(TopCat.of D5)))
    (by rw [hsymm]) (k + 2)
    (fun ε => closedBall_faceLocalHomology_zero (m := 3) (a : D5) hsphere k ε) δ

/-! ## §2. No one-piece chain detects at a seam point -/

/-- **NO CYLINDER-SUPPORTED 5-CHAIN HAS A NONZERO LOCAL CLASS AT A SEAM POINT.** Universal over the
chain: the cylinder side contributes nothing at all to seam detection. -/
theorem relClassOf_eq_zero_of_cylSupported (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1) (a : ↥S)
    (c : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2))
    (hcA : c ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl) (3 + 2))
    (hbd : chainBoundary
        (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) c
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1)) :
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      ({seamPoint s S hS φ hφ hφinj a}ᶜ) 3 c hbd = 0 :=
  relClassOf_eq_zero_of_subspace_of_faceVanish (seamPoint_mem_range_fromCyl a)
    (fun β => cylPiece_localHomology_zero hφtop a 3 β) c hcA hbd

omit [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **NO HANDLE-SUPPORTED 5-CHAIN HAS A NONZERO LOCAL CLASS AT A SEAM POINT** (attaching parameter on
`∂D⁵`). Universal over the chain: the disk side contributes nothing either. -/
theorem relClassOf_eq_zero_of_handleSupported {a : ↥S}
    (hsphere : ‖((a : D5) : EuclideanSpace ℝ (Fin 5))‖ = 1)
    (c : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2))
    (hcB : c ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle) (3 + 2))
    (hbd : chainBoundary
        (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) c
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1)) :
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      ({seamPoint s S hS φ hφ hφinj a}ᶜ) 3 c hbd = 0 :=
  relClassOf_eq_zero_of_subspace_of_faceVanish (seamPoint_mem_range_fromHandle a)
    (fun β => handlePiece_localHomology_zero hsphere 3 β) c hcB hbd

omit [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- The boundary bookkeeping of a homologous decomposition `c = p + ∂w + e`: the collar chain's own
boundary is again an off-the-point chain, so it has a local class to compare with. -/
theorem chainBoundary_mem_of_homologous
    {x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier}
    {c p e : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)}
    {w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 3)}
    (hcongr : c = p
      + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) w + e)
    (he : e ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      ({x}ᶜ) (3 + 2))
    (hbd : chainBoundary
        (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) c
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({x}ᶜ) (3 + 1)) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) p
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({x}ᶜ) (3 + 1) := by
  have hbde : chainBoundary
      (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) e
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            ({x}ᶜ) (3 + 1) :=
    chainBoundary_mem_subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) (3 + 1) e he
  have h1 : chainBoundary
      (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) c
      = chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) p
        + chainBoundary
            (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) e := by
    rw [hcongr, map_add, map_add, chainBoundary_chainBoundary_apply, add_zero]
  have hsum := Submodule.add_mem _ hbd hbde
  rw [h1, add_assoc, ZModModule.add_self, add_zero] at hsum
  exact hsum

/-- **A CYLINDER-SIDE REPRESENTATIVE FORCES THE LOCAL CLASS TO VANISH — UP TO HOMOLOGY.** If a
5-chain `c` of the carrier is homologous rel `{seamPoint a}ᶜ` to a **cylinder-supported** chain `p`
(`c = p + ∂w + e` with `e` supported off the seam point), its local class at the seam point is `0`.

Taking `w = 0` this is exactly the congruence route `relClassOf_eq_of_congr` a
`SeamCollarChainDatum` discharge of `hdetAB` uses — so that route is dead for **every** cylinder-side
collar chain at once, not merely for the pushed prism (`…SeamDetect.collarChain_ne_cylPush`, which
had to argue chain-by-chain). -/
theorem relClassOf_eq_zero_of_cylHomologous (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1) (a : ↥S)
    {c p e : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)}
    {w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 3)}
    (hcongr : c = p
      + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) w + e)
    (hp : p ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl) (3 + 2))
    (he : e ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 2))
    (hbd : chainBoundary
        (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) c
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1)) :
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      ({seamPoint s S hS φ hφ hφinj a}ᶜ) 3 c hbd = 0 := by
  have hbdp := chainBoundary_mem_of_homologous hcongr he hbd
  rw [relClassOf_eq_of_homologous (Set.Subset.refl _) 3 hcongr he hbd hbdp]
  exact relClassOf_eq_zero_of_cylSupported hφtop a p hp hbdp

omit [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **A HANDLE-SIDE REPRESENTATIVE FORCES THE LOCAL CLASS TO VANISH — UP TO HOMOLOGY.** The mirror of
`relClassOf_eq_zero_of_cylHomologous`, and the universal form of
`…SeamDetect.collarChain_ne_diskPush`. -/
theorem relClassOf_eq_zero_of_handleHomologous {a : ↥S}
    (hsphere : ‖((a : D5) : EuclideanSpace ℝ (Fin 5))‖ = 1)
    {c p e : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)}
    {w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 3)}
    (hcongr : c = p
      + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) w + e)
    (hp : p ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle) (3 + 2))
    (he : e ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 2))
    (hbd : chainBoundary
        (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) c
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1)) :
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      ({seamPoint s S hS φ hφ hφinj a}ᶜ) 3 c hbd = 0 := by
  have hbdp := chainBoundary_mem_of_homologous hcongr he hbd
  rw [relClassOf_eq_of_homologous (Set.Subset.refl _) 3 hcongr he hbd hbdp]
  exact relClassOf_eq_zero_of_handleSupported hsphere p hp hbdp

/-! ## §3. The row-facing verdict -/

/-- **THE ROW'S LOCALIZED DETECTION OBLIGATION IS FALSE AT A SEAM POINT WHERE THE GLUED CHAIN HAS A
CYLINDER-SIDE REPRESENTATIVE.** Stated in the exact per-parameter shape of `hdetCore` in
`…SeamDetect.CollarPairCoreRow.ofSeamCoreLocal`: if `qGen z cHa` is homologous rel
`{seamPoint a}ᶜ` to a cylinder-supported chain, then `∀ hq, relClassOf … ≠ 0` cannot hold at `a`. -/
theorem not_hdetAB_at_of_cylHomologous (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1) (a : ↥S)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    {p e : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)}
    {w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 3)}
    (hcongr : qGen s S hS φ hφ hφinj z cHa = p
      + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) w + e)
    (hp : p ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl) (3 + 2))
    (he : e ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 2))
    (hbd : chainBoundary
        (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qGen s S hS φ hφ hφinj z cHa)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1)) :
    ¬ (∀ (hq : chainBoundary
          (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
          (qGen s S hS φ hφ hφinj z cHa)
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1)),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        ({seamPoint s S hS φ hφ hφinj a}ᶜ) 3 (qGen s S hS φ hφ hφinj z cHa) hq ≠ 0) :=
  fun H => H hbd (relClassOf_eq_zero_of_cylHomologous hφtop a hcongr hp he hbd)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE ROW'S LOCALIZED DETECTION OBLIGATION IS FALSE AT A SEAM POINT WHERE THE GLUED CHAIN HAS A
HANDLE-SIDE REPRESENTATIVE** — the mirror of `not_hdetAB_at_of_cylHomologous`. Together the two say:
a discharge of `hdetAB` must produce, at every core seam point, a local class that NO one-piece chain
is homologous to. -/
theorem not_hdetAB_at_of_handleHomologous {a : ↥S}
    (hsphere : ‖((a : D5) : EuclideanSpace ℝ (Fin 5))‖ = 1)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    {p e : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2)}
    {w : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 3)}
    (hcongr : qGen s S hS φ hφ hφinj z cHa = p
      + chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) w + e)
    (hp : p ∈ subspaceChains
      (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle) (3 + 2))
    (he : e ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 2))
    (hbd : chainBoundary
        (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qGen s S hS φ hφ hφinj z cHa)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1)) :
    ¬ (∀ (hq : chainBoundary
          (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
          (qGen s S hS φ hφ hφinj z cHa)
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1)),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        ({seamPoint s S hS φ hφ hφinj a}ᶜ) 3 (qGen s S hS φ hφ hφinj z cHa) hq ≠ 0) :=
  fun H => H hbd (relClassOf_eq_zero_of_handleHomologous hsphere hcongr hp he hbd)

/-! ## §4. THE BINARY-PARTITION DETECTION BAN, KERNEL-CHECKED -/

section Partition

variable {t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)}
  {cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier}
  {hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd}
  {d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam}

/-- **NO CLASS ON THE CLOSED CYLINDER PIECE DETECTS AT A CORE SEAM POINT — the kernel-checked form of
the `capstone-binary-partition-detection-uninhabitable` ban.** For **every** relative class `αU` on
the pair `(range fromCyl, ∂W ∩ range fromCyl)` and **every** interior generator family `gen`, the
pushed-forward class fails `RestrictsToRelGenOn` on the cyl side: at a seam point of the canonical
core it must equal `(gen x hx).symm 1 ≠ 0`, but it restricts to `0` because the cylinder piece is
face-flat there (`cylPiece_localHomology_zero`).

This is exactly the `#156` wall analysis, no longer prose: *"at a seam point x (healed W-interior)
the closed piece's summand restricts through `H₅(sub U, sub U∖{x'})` at a BOUNDARY-FACE point — which
vanishes — so `restrictBd β x = 0 ≠ (gen x hx).symm 1` for EVERY `αU`."* The `hdetU` field of
`PinPlusTraceCapstoneRelFund.CapstoneRelFundPartitionDatum` is of exactly this shape with
`U := Set.range fromCyl`, so that datum is uninhabitable at `U` = the cyl range whenever the
canonical core is nonempty and the attaching map lands on the cylinder's top face.

The hypothesis `ha : a ∈ seamCore …` is what makes the seam point a `W`-INTERIOR point (`compl_seamCore`
is by construction the off-`∂W` condition, `seamPoint_notMem_bd_iff_mem_seamCore`) — i.e. a point at
which detection is actually demanded. -/
theorem not_restrictsToRelGenOn_cylRange_at_seamCore
    (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1)
    {a : ↥S} (ha : a ∈ seamCore s t S hS φ hφ hφinj cd hseam d)
    (gen : ∀ y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier,
      y ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) →
      (RelativeHomology (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        ({y}ᶜ) (3 + 2) ≃ₗ[ZMod 2] ZMod 2))
    (αU : RelativeHomology
      (restr (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)) (3 + 2)) :
    ¬ RestrictsToRelGenOn (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) gen
        (· ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)
        (excisionMap (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl) (3 + 2) αU) :=
  not_restrictsToRelGenOn_of_faceVanish (seamPoint_mem_range_fromCyl a)
    ((seamPoint_notMem_bd_iff_mem_seamCore (d := d) a).mpr ha) gen
    (fun β => cylPiece_localHomology_zero hφtop a 3 β) αU (seamPoint_mem_range_fromCyl a)

end Partition

end

end SKEFTHawking.PinPlusTraceCapstoneCollarPairSeamLocalHom
