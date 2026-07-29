/-
# Phase 5q.H (#212) — `CollarPairCoreRow.hdetAB` LOCALIZED; the ROW's vacuity attack COMPLETED; both one-sided congruence routes REFUTED.

**Headline (a localization plus two refutations; `hdetAB` is NOT discharged).**
`PinPlusTraceCapstoneCollarPairMatch` §6 reduced the collar-pair row to the two obligations `hbd`
and `hdetAB`; `PinPlusTraceCapstoneCollarPairSeamLocal` localized `hbd` to the canonical seam core
and left `hdetAB` explicitly untouched (:66–67). This module does to `hdetAB` what that one did to
`hbd`, and then says something new about both.

## 1. `hdetAB` is *exactly* a seam-core condition (§1–§2, an `↔`)

`hdetAB_iff_forall_seamCore`:

> the straddle-detection obligation over the whole trace carrier **iff** for every `a` in the
> canonical core `seamCore`, the glued 5-chain `qGen z cHa` has nonzero local class at the seam
> point `seamPoint a`.

Two facts make it an `↔`. The overlap zone `range fromCyl ∩ range fromHandle` is *exactly* the seam
(`mem_range_both_iff_exists_seamPoint`, the in-tree `range_fromCyl_inter_range_fromHandle` read in
the `seamPoint` idiom), and a seam point is off `∂W` *exactly* when its parameter is in the
canonical core (`seamPoint_notMem_bd_iff_mem_seamCore`, which is `compl_seamCore` by construction).
So the analytic set `∂W` — produced by the surgered-end datum through `ModelWithCorners.boundary` —
leaves the statement entirely, with **no loss and no gain**.

**Combined with `…SeamLocal.qGen_boundary_mem_iff_forall_seamCore`, BOTH obligations of
`CollarPairCoreRow` are now conditions indexed by `seamCore ⊆ ↥S` and nothing else.**
`CollarPairCoreRow.ofSeamCoreLocal` (§3) is the entry point in that shape: an inhabiter chooses `z`
and `cHa` and then discharges, at each core seam point, one support condition and one detection
condition. Neither hypothesis mentions the carrier or `∂W`.

## 2. The vacuity attack, run on the WHOLE row — and it succeeds (§4)

`…CollarPairMatch` §5 freed `hseamMatch` at `seamCore = ∅`; `…SeamLocal` §2 freed `hbd` there.
`hdetAB_of_seamCore_empty` frees the *other* obligation for the same reason (no overlap point off
`∂W` survives), and `nonempty_collarPairCoreRow_of_seamCore_empty` therefore builds the entire
two-obligation row outright, with **zero geometric input** — the disk triple is the banked canonical
one and a representing fundamental cycle always exists (`exists_fundCycle`).

**So `CollarPairCoreRow` is not by itself a certificate**: at `seamCore = ∅` its `toHasClass` would
fire on a row containing no geometry at all. This upgrades the standing instruction of
`…CollarPairMatch` :60–63 from advice to a proved necessity: an inhabiter MUST carry seam-core
nonemptiness (`CollarPairSeamRow.hseamHit`, guarded by
`…CollarPairMatch.qGen_ne_zero_of_seamCore_nonempty`) as a side condition. Nothing here suggests the
degenerate configuration is geometrically realizable — it is not excluded by the abstract
`SurgeredEndDatum` interface, which is precisely why the side condition is needed.

## 3. NEITHER GLUED PIECE CAN SERVE IN A CONGRUENCE ROUTE (§5) — the refutation

The one route the engine layer advertises for `hdetAB` is the collar decomposition
`qGen z cHa = p + e` of `SingularRelativeCoverMVSeam.SeamCollarChainDatum`: discard the away-error
`e` (supported off the point) and detect with the collar chain `p` (whose boundary is a `∂W`-chain),
via `relClassOf_eq_of_congr`. This module shows **neither glued piece can play either role** at a
core seam point:

* `cylPush_notMem_compl_seamPoint` — the pushed cylinder prism is *supported at every seam point*,
  so it can never be the away-error `e`. Engine: `crossChain_notMem_subspaceChains_compl_top` (§0).
* `cylPush_boundary_notMem_compl_seamPoint` — its boundary is not even a `{seamPoint a}ᶜ`-chain, so
  it can never be the collar chain `p` (`collarChain_ne_cylPush`).
* `collarChain_ne_diskPush` — and the disk piece cannot be `p` either, by the banked forcing
  theorem `…SeamLocal.diskBoundaryPush_notMem_bd_of_hbd`.

**Conclusion: the collar chain of any congruence-route discharge of `hdetAB` must be a genuinely
THIRD chain.** No "keep one side, discard the other" strategy exists.

§0's engine is the top-face companion of `…SeamLocal.fundCycle_notMem_subspaceChains_compl`, proved
for a general closed connected charted `M`: the prism `crossChain z` over a fundamental cycle is
supported at every point of the TOP face `M × {⊤}`. (Its boundary is the two endpoint slices; the
bottom slice lives in `M × {⊥}`, so mod 2 the top slice would have to miss the point, and pulling
back along the top-slice embedding would make `z` miss a point of `M`.) Reusable well beyond this
row, and it is what makes the cylinder-side refutation unconditional rather than `∂W`-dependent.

## 4. The disk side is forced POINTWISE (§5, sharper than the banked set-level fact)

`diskBoundary_notMem_compl_seamParam_of_hbd`: under `hbd` and `hφtop`, `∂cHa` has a simplex through
**every** core parameter `a`, not merely "somewhere in the core" as
`…SeamLocal.diskBoundary_notMem_sphereShrunk_of_hbd` gives. So the remaining
*adapted-fundamental-cycle* residual is a simultaneous mod-2 cancellation over the whole canonical
core, not a single one to arrange.

## What is NOT proved here (stated precisely, no overclaim)

* **`hdetAB` is NOT discharged.** After this module one named geometric residual remains: produce
  `z` and `cHa` such that, at every core seam point, the glued 5-chain `qGen z cHa` has nonzero
  local class. §5 says how it cannot be done (no one-sided congruence); it does not say how it can.
* **`hbd` is not discharged either** — it is unchanged from `…SeamLocal`.
* No claim that `seamCore = ∅` is realizable or unrealizable; §4 is a statement about what the row
  certifies, not about the geometry.
* No converse to §5 is claimed: "the collar chain is a third chain" is necessary, never sufficient.

## Fences honored

* `collar-pair-closed-seam-attached-collar-bridge-is-FALSE` — no bridge, no collar retraction, no
  `sphere ∖ S` support is constructed; the only sets named are the canonical `seamCore`, the two
  gluing faces (inherited), and single-point complements.
* `collar-pair-open-complement-annulus-is-refuted-shape` — nothing routes through
  `SurgeredEndDatum.topFaceCovered`; the datum enters only through the banked face lemmas.
* `collar-pair-maximal-core-reenters-refuted-support` — no core is chosen: `seamCore` is the
  canonical one, and it is only ever asked to be NONEMPTY (never `univ`).
* `seam-transfer-open-support-uninhabitable` — nothing routes through `CapstoneSeamTransfer`,
  `hbd_ofTransfer` or `hasClass_ofTransferCorrector`, and no new split structure of that shape is
  introduced; §5 in fact REFUTES the one-sided split at the seam. (`capstoneCylChainT` is the
  controlled cylinder representative, not part of the transfer datum.)
* `collar-pair-coarse-core-does-not-relax-the-disk-side` — nothing is subdivided and `hctrlH` is not
  revived; §5 strengthens the disk-side rigidity.
* `capstone-choose-representative-corrector-uninhabitable` — the cylinder side stays the CONTROLLED
  representative `capstoneCylChainT z` pinned by `hz`; the opaque `.choose` chain never appears.
* The shared-`cCore` co-adaptation is not built, referenced, or needed.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCollarPairSeamLocal

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularExcision
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeCrossProductRel
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlue
open SKEFTHawking.PinPlusTraceDiskCorePair
open SKEFTHawking.PinPlusTraceCapstoneCollarPair
open SKEFTHawking.PinPlusTraceCapstoneCollarPairGeom
open SKEFTHawking.PinPlusTraceCapstoneCollarPairCore
open SKEFTHawking.PinPlusTraceCapstoneCollarPairFace
open SKEFTHawking.PinPlusTraceCapstoneCollarPairEnd
open SKEFTHawking.PinPlusTraceCapstoneCollarPairMatch
open SKEFTHawking.PinPlusTraceCapstoneCollarPairSeamLocal

namespace SKEFTHawking.PinPlusTraceCapstoneCollarPairSeamDetect

noncomputable section

/-! ## §0. The prism is supported at every TOP-FACE point (generic engine) -/

section PrismTopSupport

variable {m' : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] [T1Space (cylW M)]

/-- **THE PRISM OVER A FUNDAMENTAL CYCLE IS SUPPORTED AT EVERY TOP-FACE POINT.** -/
theorem crossChain_notMem_subspaceChains_compl_top (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) (x : M) :
    crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2))
      ∉ subspaceChains (X := TopCat.of (cylW M))
          ({((x, ⊤) : cylW M)}ᶜ) (m' + 2 + 1) := by
  intro hmem
  have hbd : chainBoundary (TopCat.of (cylW M)) (m' + 2)
      (crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2)))
        ∈ subspaceChains (X := TopCat.of (cylW M)) ({((x, ⊤) : cylW M)}ᶜ) (m' + 2) :=
    chainBoundary_mem_subspaceChains (X := TopCat.of (cylW M)) ({((x, ⊤) : cylW M)}ᶜ)
      (m' + 2) _ hmem
  rw [chainBoundary_crossChain (m' + 1) (z : SingularChain (TopCat.of M) (m' + 2)) z.2] at hbd
  have hbot : mapChain (slice (graphHom (TopCat.of M)) 0) (m' + 2)
      (z : SingularChain (TopCat.of M) (m' + 2))
        ∈ subspaceChains (X := TopCat.of (cylW M)) ({((x, ⊤) : cylW M)}ᶜ) (m' + 2) :=
    mapChain_mem_subspaceChains (slice (graphHom (TopCat.of M)) 0)
      (fun y _ => by
        rw [slice_graphHom]
        intro hcon
        have h2 := congrArg (fun p : cylW M => ((p.2 : Set.Icc (0 : ℝ) 1) : ℝ))
          (Set.mem_singleton_iff.mp hcon)
        norm_num at h2)
      (m' + 2) _ (mem_subspaceChains_univ _ _)
  have htop : mapChain (slice (graphHom (TopCat.of M)) 1) (m' + 2)
      (z : SingularChain (TopCat.of M) (m' + 2))
        ∈ subspaceChains (X := TopCat.of (cylW M)) ({((x, ⊤) : cylW M)}ᶜ) (m' + 2) := by
    have hsum := Submodule.add_mem _ hbd hbot
    rwa [add_assoc, ZModModule.add_self, add_zero] at hsum
  have hjemb : Topology.IsEmbedding (⇑(slice (graphHom (TopCat.of M)) 1)) :=
    isEmbedding_prodMkLeft _
  have h3 := (closedEmbeddingChain_mem_iff_preimage hjemb (m' + 2)
      (z : SingularChain (TopCat.of M) (m' + 2))
      (A := ({((x, ⊤) : cylW M)}ᶜ))).mp
      (by
        rw [SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply.closedEmbeddingChain_eq_mapChain]
        exact htop)
  have hsub : (⇑(slice (graphHom (TopCat.of M)) 1)) ⁻¹' ({((x, ⊤) : cylW M)}ᶜ)
      ⊆ ({x}ᶜ : Set M) := by
    intro y hy
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hyx
    exact hy (by rw [hyx]; exact slice_graphHom (M := TopCat.of M) 1 x)
  exact fundCycle_notMem_subspaceChains_compl (m' := m') (M := M) z hz x
    (subspaceChains_mono hsub (m' + 2) h3)

end PrismTopSupport

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §1. THE OVERLAP ZONE IS THE CANONICAL CORE -/

variable {s t S hS φ hφ hφinj cd hseam d}

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE OVERLAP ZONE IS EXACTLY THE SEAM.** A carrier point lies in BOTH gluing ranges iff it is
the seam point of some attaching parameter — the in-tree
`HandleAttachment.range_fromCyl_inter_range_fromHandle` read in the `seamPoint` idiom. This is the
`hdetAB` quantifier's true index set: not the carrier, but `↥S`. -/
theorem mem_range_both_iff_exists_seamPoint
    (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) :
    (x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
        ∧ x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)
      ↔ ∃ a : ↥S, seamPoint s S hS φ hφ hφinj a = x := by
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
        ∩ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle := ⟨h1, h2⟩
    rw [(ktHandleAttachment s.M D5 S hS φ hφ hφinj).range_fromCyl_inter_range_fromHandle] at hx
    exact hx
  · rintro ⟨a, rfl⟩
    exact ⟨⟨φ a, (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a⟩, ⟨(a : D5), rfl⟩⟩

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **A SEAM POINT IS OFF `∂W` IFF ITS PARAMETER IS IN THE CANONICAL CORE** — by construction
(`seamCore` is the complement of `seamPoint ⁻¹' ∂W`), stated so that the localization below reads
without unfolding. -/
theorem seamPoint_notMem_bd_iff_mem_seamCore (a : ↥S) :
    seamPoint s S hS φ hφ hφinj a
        ∉ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W
      ↔ a ∈ seamCore s t S hS φ hφ hφinj cd hseam d := Iff.rfl

/-! ## §2. THE LOCALIZATION — `hdetAB` is a seam-core-point-by-point condition -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`CollarPairCoreRow.hdetAB`, FULLY LOCALIZED — the headline.** The two-obligation row's seam
straddle-detection obligation is *equivalent* to: at every seam point of the canonical core, the
glued 5-chain `qGen z cHa` has nonzero local class. Two facts make it an `↔`: the overlap zone is
exactly the seam (§1), and a seam point is off `∂W` exactly when its parameter is in the canonical
core (`compl_seamCore`). So the quantifier over the whole trace carrier — an analytic set produced
by the surgered-end datum through `ModelWithCorners.boundary` — collapses with **no loss and no
gain** to a quantifier over `seamCore ⊆ ↥S`.

Together with `…CollarPairSeamLocal.qGen_boundary_mem_iff_forall_seamCore` this makes **both**
obligations of `CollarPairCoreRow` conditions indexed by the canonical core and nothing else.

The relative-cycle proof is quantified over (`∀ hq`) exactly as in
`CollarPairCoreRow.ofSeamLocal`, so no proof term has to be threaded by hand. -/
theorem hdetAB_iff_forall_seamCore (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)) :
    (∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier),
        x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) →
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
        ∀ (hq : chainBoundary
            (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
            (qGen s S hS φ hφ hφinj z cHa)
          ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              ({x}ᶜ) (3 + 1)),
        relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
          (qGen s S hS φ hφ hφinj z cHa) hq ≠ 0)
      ↔ (∀ a ∈ seamCore s t S hS φ hφ hφinj cd hseam d,
        ∀ (hq : chainBoundary
            (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
            (qGen s S hS φ hφ hφinj z cHa)
          ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1)),
        relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({seamPoint s S hS φ hφ hφinj a}ᶜ) 3 (qGen s S hS φ hφ hφinj z cHa) hq ≠ 0) := by
  constructor
  · intro H a ha
    exact H (seamPoint s S hS φ hφ hφinj a) ha
      ⟨φ a, (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a⟩ ⟨(a : D5), rfl⟩
  · intro H x hx hxA hxB
    obtain ⟨a, rfl⟩ := (mem_range_both_iff_exists_seamPoint x).mp ⟨hxA, hxB⟩
    exact H a hx

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE VACUITY ATTACK ON `hdetAB` — it succeeds, at `seamCore = ∅` and there only.** With an
empty canonical core the straddle-detection obligation holds for EVERY fundamental cycle `z` and
EVERY disk chain `cHa`, with zero geometric input: there is simply no overlap point off `∂W` left
to detect at.

This is the `hdetAB`-side twin of `…CollarPairSeamLocal.hbd_of_seamCore_empty`, and together with it
it shows the vacuity is not confined to one obligation — see
`nonempty_collarPairCoreRow_of_seamCore_empty`, which builds the WHOLE two-obligation row for free
in that configuration. An inhabiter must therefore carry seam-core NONEMPTINESS
(`CollarPairSeamRow.hseamHit`) as a side condition; an inhabitation that lands in `seamCore = ∅`
certifies nothing. -/
theorem hdetAB_of_seamCore_empty (hempty : seamCore s t S hS φ hφ hφinj cd hseam d = ∅)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)) :
    ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier),
      x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
      ∀ (hq : chainBoundary
          (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
          (qGen s S hS φ hφ hφinj z cHa)
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            ({x}ᶜ) (3 + 1)),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
        (qGen s S hS φ hφ hφinj z cHa) hq ≠ 0 :=
  (hdetAB_iff_forall_seamCore (d := d) z cHa).mpr
    (fun a ha => absurd (hempty ▸ ha) (Set.notMem_empty a))

/-! ## §3. The fully seam-core-local entry point -/

/-- **BUILD THE TWO-OBLIGATION ROW FROM TWO SEAM-CORE-LOCAL CONDITIONS.** Sharpens
`…CollarPairSeamLocal.CollarPairCoreRow.ofSeamLocal`, which localized only `hbd`: here BOTH
obligations are quantified over the canonical core `seamCore ⊆ ↥S` and nothing else. Neither the
trace carrier nor the analytic set `∂W` appears in either hypothesis. This is the shape an
inhabitation attempt should target: choose `z` and `cHa`, then discharge two conditions at each core
seam point — the seam-match chain misses it (`hlocal`), and the glued 5-chain detects there
(`hdetCore`).

⚠ Carry seam-core NONEMPTINESS as a side condition: `nonempty_collarPairCoreRow_of_seamCore_empty`
builds this row outright when `seamCore = ∅`, so a row built with an empty core certifies nothing. -/
def CollarPairCoreRow.ofSeamCoreLocal (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1))
    (hdetHa : ∀ (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
        (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) ({y}ᶜ) 3 cHa
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) hcHa) ≠ 0)
    (hlocal : ∀ a ∈ seamCore s t S hS φ hφ hφinj cd hseam d,
      seamMatchGen s S hS φ hφ hφinj z cHa
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1))
    (hdetCore : ∀ a ∈ seamCore s t S hS φ hφ hφinj cd hseam d,
      ∀ (hq : chainBoundary
          (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
          (qGen s S hS φ hφ hφinj z cHa)
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1)),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        ({seamPoint s S hS φ hφ hφinj a}ᶜ) 3 (qGen s S hS φ hφ hφinj z cHa) hq ≠ 0) :
    CollarPairCoreRow s t S hS φ hφ hφinj cd hseam d :=
  SKEFTHawking.PinPlusTraceCapstoneCollarPairSeamLocal.CollarPairCoreRow.ofSeamLocal
    z hz cHa hcHa hdetHa hlocal ((hdetAB_iff_forall_seamCore (d := d) z cHa).mpr hdetCore)

/-! ## §4. THE FULL-ROW VACUITY ATTACK -/

omit [PreconnectedSpace s.M] in
/-- Every homology class has a representing cycle — `Homology.mk` is a quotient map. Used only to
supply the `z`/`hz` pair of the vacuity row below. -/
theorem exists_fundCycle :
    ∃ z : cycles (TopCat.of s.M) (2 + 2),
      SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
        = Homology.mk (TopCat.of s.M) (2 + 2) z := by
  -- v4.32: `fundamentalClass` is typed at the `def`-wrapped alias `Homology _ _`. Passing the
  -- submodule EXPLICITLY makes the unifier compare two fully-elaborated closed types through that
  -- alias, which blows the whnf budget. Passing `_` leaves a metavariable to assign after a single
  -- delta step — instant, and the idiom already used in `BocksteinIntegralLift`.
  -- (NEVER `set_option maxHeartbeats` here — Invariant #10; the budget is not the problem.)
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M))
  exact ⟨z, hz.symm⟩

omit [PreconnectedSpace s.M] in
/-- **THE VACUITY ATTACK, RUN ON THE WHOLE TWO-OBLIGATION ROW — and it succeeds.** When the
canonical core is EMPTY, `CollarPairCoreRow` is inhabited outright: `hbd` is free
(`…CollarPairSeamLocal.hbd_of_seamCore_empty`), `hdetAB` is free (`hdetAB_of_seamCore_empty`), the
disk triple is the banked canonical one, and a representing fundamental cycle always exists. **Zero
geometric input.**

This is strictly stronger than the per-obligation vacuity results of
`…CollarPairMatch` §5 and `…CollarPairSeamLocal` §2, which each freed ONE obligation: there is no
residual content anywhere in the row at `seamCore = ∅`. Consequently `CollarPairCoreRow` is **not by
itself a certificate** — `CollarPairCoreRow.toHasClass` would fire on this degenerate row too. The
seam-core NONEMPTINESS side condition (`CollarPairSeamRow.hseamHit`, guarded by
`…CollarPairMatch.qGen_ne_zero_of_seamCore_nonempty`) is what separates a genuine inhabitation from
this one, and by `…CollarPairSeamLocal` §3 the nonempty case is not free. -/
theorem nonempty_collarPairCoreRow_of_seamCore_empty
    (hempty : seamCore s t S hS φ hφ hφinj cd hseam d = ∅) :
    Nonempty (CollarPairCoreRow s t S hS φ hφ hφinj cd hseam d) := by
  obtain ⟨z, hz⟩ := exists_fundCycle (s := s)
  exact ⟨CollarPairCoreRow.ofSeamCoreLocal z hz diskDetectChain diskDetectChain_hc
    (fun y hy => diskDetectChain_hdet y hy)
    (fun a ha => absurd (hempty ▸ ha) (Set.notMem_empty a))
    (fun a ha => absurd (hempty ▸ ha) (Set.notMem_empty a))⟩

/-! ## §5. FORCING — the cylinder piece is pinned to every seam point -/

/-- **THE PUSHED TOP SLICE IS SUPPORTED AT EVERY SEAM POINT.** For any fundamental cycle `z` and any
attaching parameter `a` (with `hφtop`), `fromCyl_#(z@⊤)` has a simplex through the seam point
`seamPoint a`. This drops the `a ∈ seamCore` hypothesis of
`…CollarPairSeamLocal.topSlicePush_notMem_bd_of_mem_seamCore` and replaces the analytic `∂W` by the
single-point complement: the obstruction is not about the boundary at all, it is that a fundamental
cycle is supported at `(φ a).1` (`fundCycle_notMem_subspaceChains_compl`). -/
theorem topSlicePush_notMem_compl_seamPoint (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z) (a : ↥S) :
    closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) (topSliceB s S hS φ hφ hφinj z)
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1) := by
  intro h
  have h1 := (closedEmbeddingChain_mem_iff_preimage _ _ _).mp h
  have hsub : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
      ({seamPoint s S hS φ hφ hφinj a}ᶜ)
      ⊆ ({φ a}ᶜ : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) := by
    intro y hy
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hy
    simp only [Set.mem_compl_iff]
    intro hya
    exact hy (by rw [hya]; exact (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a)
  have h2 := subspaceChains_mono hsub (3 + 1) h1
  have h3 := (closedEmbeddingChain_mem_iff_preimage (isEmbedding_sliceOne (s := s)) (3 + 1)
      (z : SingularChain (TopCat.of s.M) (3 + 1))
      (A := ({φ a}ᶜ : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B))).mp
      (by
        rw [SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply.closedEmbeddingChain_eq_mapChain]
        exact h2)
  refine fundCycle_notMem_subspaceChains_compl (m' := 2) (M := s.M) z hz (φ a).1
    (subspaceChains_mono ?_ (2 + 2) h3)
  intro y hy
  simp only [Set.mem_preimage] at hy
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hya
  exact hy (by rw [hya, slice_graphHom]; exact Prod.ext rfl (phi_snd_eq_top hφtop a).symm)

/-- **THE CYLINDER 5-CHAIN IS SUPPORTED AT EVERY SEAM POINT.** The pushed prism
`fromCyl_#(capstoneCylChainT z)` always has a simplex through `seamPoint a` — the seam point is a
TOP-FACE point of the cylinder, and the prism over a fundamental cycle is supported at every
top-face point (`crossChain_notMem_subspaceChains_compl_top`).

Consequence for `hdetAB`: **the cylinder piece can never be the away-error of a congruence route.**
`relClassOf_eq_of_congr` discards a summand only when it is supported off the point; the cylinder
piece never is. -/
theorem cylPush_notMem_compl_seamPoint (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z) (a : ↥S) :
    closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 2) := by
  intro h
  have h1 := (closedEmbeddingChain_mem_iff_preimage _ _ _).mp h
  have hsub : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
      ({seamPoint s S hS φ hφ hφinj a}ᶜ)
      ⊆ ({((φ a).1, ⊤)}ᶜ : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) := by
    intro y hy
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hy
    simp only [Set.mem_compl_iff]
    intro hya
    refine hy ?_
    rw [hya, show ((φ a).1, (⊤ : Set.Icc (0 : ℝ) 1)) = φ a from
      Prod.ext rfl (phi_snd_eq_top hφtop a).symm]
    exact (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a
  exact crossChain_notMem_subspaceChains_compl_top (m' := 2) (M := s.M) z hz (φ a).1
    (subspaceChains_mono hsub (3 + 2) h1)

/-- **THE CYLINDER PIECE IS NEVER AN ALMOST-CYCLE AT A SEAM POINT.** Its boundary is the pushed top
slice plus the pushed bottom slice; the bottom slice lies in the source end (disjoint from the
seam), so the boundary avoids `seamPoint a` iff the pushed top slice does — which it never does.

Consequence for `hdetAB`: **the cylinder piece can never be the collar chain of a congruence
route** either. A `SeamCollarChainDatum`'s collar chain `p` must satisfy `∂p ∈ C(∂W)`, and at a core
seam point `∂W ⊆ {seamPoint a}ᶜ`. -/
theorem cylPush_boundary_notMem_compl_seamPoint (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z) (a : ↥S) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1) := by
  intro h
  have hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
        (capstoneCylChainT s S hS φ hφ hφinj z)
      = topSliceB s S hS φ hφ hφinj z + ctrlBottom s S hS φ hφ hφinj z 0 :=
    chainBoundary_crossChain 3 (z : SingularChain (TopCat.of s.M) (3 + 1)) z.2
  rw [chainBoundary_closedEmbeddingChain, hbd, closedEmbeddingChain_add] at h
  have hbotsub : (Set.univ ×ˢ ({⊥} : Set (Set.Icc (0 : ℝ) 1)))
      ⊆ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
        ({seamPoint s S hS φ hφ hφinj a}ᶜ) := by
    intro y hy
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    have hya : y = φ a :=
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl_injective
        (hcon.trans ((ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a).symm)
    have h2 : ((y.2 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := by rw [hy.2]; rfl
    rw [hya] at h2
    rw [hφtop a] at h2
    norm_num at h2
  have hbot : closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
      (3 + 1) (ctrlBottom s S hS φ hφ hφinj z 0)
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1) :=
    (closedEmbeddingChain_mem_iff_preimage _ _ _).mpr
      (subspaceChains_mono hbotsub (3 + 1)
        (ctrlBottom_zero_mem_bottomFace (s := s) (S := S) (hS := hS) (φ := φ) (hφ := hφ)
          (hφinj := hφinj) z))
  have hsum := Submodule.add_mem _ h hbot
  rw [add_assoc, ZModModule.add_self, add_zero] at hsum
  exact topSlicePush_notMem_compl_seamPoint hφtop z hz a hsum

/-- **THE COLLAR CHAIN OF ANY CONGRUENCE ROUTE IS NOT THE CYLINDER PIECE.** Stated at the level a
`SeamCollarChainDatum` uses it: any chain `p` whose boundary is a `∂W`-chain differs from the pushed
cylinder prism, once the canonical core has a point. So `hdetAB` at a core seam point cannot be
discharged by "keep the cylinder side, discard the disk side". -/
theorem collarChain_ne_cylPush (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    {a : ↥S} (ha : a ∈ seamCore s t S hS φ hφ hφinj cd hseam d)
    (p : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2))
    (hpBd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) p
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)) :
    p ≠ closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
      (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z) := by
  intro hpeq
  refine cylPush_boundary_notMem_compl_seamPoint (hS := hS) (hφ := hφ) (hφinj := hφinj)
    hφtop z hz a ?_
  rw [← hpeq]
  exact subspaceChains_mono (Set.subset_compl_singleton_iff.mpr
    ((seamPoint_notMem_bd_iff_mem_seamCore (d := d) a).mpr ha)) (3 + 1) hpBd

/-- **THE COLLAR CHAIN OF ANY CONGRUENCE ROUTE IS NOT THE DISK PIECE EITHER.** The mirror statement,
from the banked forcing theorem `…CollarPairSeamLocal.diskBoundaryPush_notMem_bd_of_hbd`: under the
row's own `hbd` and a nonempty canonical core the pushed disk chain's boundary is not a `∂W`-chain.

Together with `collarChain_ne_cylPush` this is the sharp structural statement about `hdetAB`: in a
`SeamCollarChainDatum`-style discharge `qGen z cHa = p + e`, the collar chain `p` must be a
genuinely THIRD chain — neither glued piece will serve. -/
theorem collarChain_ne_diskPush (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qGen s S hS φ hφ hφinj z cHa)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    (hne : (seamCore s t S hS φ hφ hφinj cd hseam d).Nonempty)
    (p : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2))
    (hpBd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) p
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)) :
    p ≠ closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
      (3 + 2) cHa := by
  obtain ⟨a, ha⟩ := hne
  intro hpeq
  refine diskBoundaryPush_notMem_bd_of_hbd (d := d) hφtop z hz cHa hbd ha ?_
  rw [← chainBoundary_closedEmbeddingChain, ← hpeq]
  exact hpBd

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`hdetAB` FORCES SUPPORT AT THE POINT** — the elementary necessary condition: a chain whose
local class at `x` is nonzero cannot be a `{x}ᶜ`-chain (`relClassOf_eq_zero_of_subspace`). Recorded
because it is what the two forcing theorems above are measured against. -/
theorem qGen_notMem_compl_of_relClassOf_ne_zero (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    {x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier}
    (hq : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qGen s S hS φ hφ hφinj z cHa)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({x}ᶜ) (3 + 1))
    (hdet : relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      ({x}ᶜ) 3 (qGen s S hS φ hφ hφinj z cHa) hq ≠ 0) :
    qGen s S hS φ hφ hφinj z cHa
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({x}ᶜ) (3 + 2) :=
  fun hc => hdet (relClassOf_eq_zero_of_subspace (Set.Subset.refl _) 3 _ hc hq)

/-- **THE SUPPORT CONDITION IS AUTOMATIC WHEN THE DISK CHAIN AVOIDS THE ATTACHING PARAMETER.** If
`cHa` misses `a ∈ D⁵`, the disk term dies at `seamPoint a` and the surviving cylinder term is
supported there (`cylPush_notMem_compl_seamPoint`), so the glued chain is too. So `hdetAB`'s
necessary support condition costs nothing in that regime — and, dually, the glued chain can only
MISS a seam point through genuine mod-2 cancellation of the prism against the disk chain. This is
the 5-chain-level twin of the boundary-level forcing in `…CollarPairSeamLocal` §3. -/
theorem qGen_notMem_compl_seamPoint_of_disk_avoids (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (a : ↥S)
    (hAvoid : cHa ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({(a : D5)}ᶜ) (3 + 2)) :
    qGen s S hS φ hφ hφinj z cHa
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 2) := by
  intro h
  refine cylPush_notMem_compl_seamPoint (hS := hS) (hφ := hφ) (hφinj := hφinj) hφtop z hz a ?_
  have hsub : ({(a : D5)}ᶜ : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ⊆ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle ⁻¹'
        ({seamPoint s S hS φ hφ hφinj a}ᶜ) := by
    intro q hq
    simp only [Set.mem_compl_iff] at hq
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun hcon => hq ((ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle_injective hcon)
  have hH : closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
      (3 + 2) cHa
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 2) :=
    (closedEmbeddingChain_mem_iff_preimage _ _ _).mpr (subspaceChains_mono hsub (3 + 2) hAvoid)
  have hsum := Submodule.add_mem _ h hH
  rw [qGen, add_assoc, ZModModule.add_self, add_zero] at hsum
  exact hsum

/-- **THE DISK BOUNDARY MUST PASS THROUGH *EVERY* CORE SEAM PARAMETER — pointwise.** Under the row's
own `hbd` and `hφtop`, for each `a` in the canonical core the disk chain's boundary `∂cHa` has a
simplex through the point `a ∈ D⁵` itself.

This is strictly sharper than the banked set-level
`…CollarPairSeamLocal.diskBoundary_notMem_sphereShrunk_of_hbd` ("`∂cHa` cannot be confined to
`S⁴ ∖ seamCore`", one witness): here EVERY core parameter is hit. The proof is `∂W`-free after the
first step — `hbd` puts the seam-match chain off `seamPoint a` (`ha` says `∂W` misses that point),
the pushed top slice is never off it (`topSlicePush_notMem_compl_seamPoint`), so mod 2 the pushed
disk boundary cannot be off it either.

The design consequence: the "adapted fundamental cycle" residual is not a single cancellation to
arrange, it is a cancellation at every point of the canonical core simultaneously. -/
theorem diskBoundary_notMem_compl_seamParam_of_hbd (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qGen s S hS φ hφ hφinj z cHa)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    {a : ↥S} (ha : a ∈ seamCore s t S hS φ hφ hφinj cd hseam d) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          ({(a : D5)}ᶜ) (3 + 1) := by
  intro hC
  have hsub : ({(a : D5)}ᶜ : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ⊆ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle ⁻¹'
        ({seamPoint s S hS φ hφ hφinj a}ᶜ) := by
    intro q hq
    simp only [Set.mem_compl_iff] at hq
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun hcon => hq ((ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle_injective hcon)
  have hH := (closedEmbeddingChain_mem_iff_preimage
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding (3 + 1)
    (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa)).mpr
    (subspaceChains_mono hsub (3 + 1) hC)
  have hsm2 := subspaceChains_mono (Set.subset_compl_singleton_iff.mpr
      ((seamPoint_notMem_bd_iff_mem_seamCore (d := d) a).mpr ha)) (3 + 1)
    ((qGen_boundary_mem_iff_seamMatchGen_mem t cd hseam d z cHa).mp hbd)
  have hsum := Submodule.add_mem _ hsm2 hH
  rw [seamMatchGen, add_assoc, ZModModule.add_self, add_zero] at hsum
  exact topSlicePush_notMem_compl_seamPoint (hS := hS) (hφ := hφ) (hφinj := hφinj)
    hφtop z hz a hsum

end

end SKEFTHawking.PinPlusTraceCapstoneCollarPairSeamDetect
