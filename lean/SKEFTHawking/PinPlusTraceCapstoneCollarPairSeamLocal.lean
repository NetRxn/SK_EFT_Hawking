/-
# Phase 5q.H (#212) — `CollarPairCoreRow.hbd` LOCALIZED, and the disk side FORCED.

**Headline (a sharpening plus a forcing theorem; `hbd` is NOT discharged).**
`PinPlusTraceCapstoneCollarPairMatch` §6 reduced the collar-pair row to the two obligations
`hbd` (the glued 5-chain `qGen z cHa` is a relative cycle) and `hdetAB` (seam straddle-detection),
and freed the disk chain `cHa`. This module does two things to `hbd`, and **nothing** to `hdetAB`.

## 1. `hbd` is *exactly* a seam-local condition (§1–§2, an `↔`)

`qGen_boundary_mem_iff_forall_seamCore`:

> `∂(qGen z cHa) ∈ C(∂W)` **iff** for every `a` in the canonical core `seamCore`, the seam-match
> chain `seamMatchGen z cHa = fromCyl_#(z@⊤) + fromHandle_#(∂cHa)` has **no simplex through the
> seam point `seamPoint a`**.

The `∂W` side of the obligation — an analytic set produced by the surgered-end datum through
`ModelWithCorners.boundary` — is replaced with no loss by a condition naming only the seam points
that the canonical core singles out. Two facts make it an `↔` and not merely a sufficient
condition: `bd_subset_compl_seamCoreImage` (`∂W` misses every core seam point — this is what
`seamCore` *is*, by `compl_seamCore`) and `seamSupport_diff_seamCoreImage_subset_bd` (off the core,
BOTH gluing faces are inside `∂W` — the two shrunk-face lemmas at `K := seamCore`). The chain is
confined to the two gluing faces by `seamMatchGen_mem_seamSupport`, which is where `hcHa` is used.

**No split, no support Prop, no transfer.** The reduction is a statement about the SUM
`fromCyl_#(z@⊤) + fromHandle_#(∂cHa)` after mod-2 cancellation; it never asks for the sum to be
decomposed into an attached and an un-attached piece. That is deliberate — the split shape is the
refuted one (fence `seam-transfer-open-support-uninhabitable`), and it is not reconstructed here.

## 2. The disk side is FORCED to reach the core (§3) — the non-vacuity certificate

`topSlicePush_notMem_bd_of_mem_seamCore`: if the core is inhabited (`a ∈ seamCore`) and `hφtop`
holds, the **cylinder term alone is never a `∂W`-chain**, for any fundamental cycle `z`. Hence
(`diskBoundaryPush_notMem_bd_of_hbd`, `diskBoundary_notMem_sphereShrunk_of_hbd`) in *any*
inhabitation of the two-obligation row with a nonempty core, `∂cHa` must genuinely enter
`seamCore`: it can never be confined to `S⁴ ∖ seamCore`. So §6's "`cHa` is DATA" is not an optional
convenience — **mod-2 cancellation across the seam is mandatory**, and any inhabitation attempt
that keeps the two terms separately inside `∂W` is dead before it starts.

The engine of the forcing step is `fundCycle_notMem_subspaceChains_compl`, proved here for a general
closed charted `M`: **a fundamental cycle is supported at every point** — if `z` misses `x` then the
prism `crossChain z` misses the interior cylinder point `(x, 1/2)`, and its local class there
vanishes, contradicting `crossChain_relClassOf_ne_zero`. Reusable well beyond this row.

## 3. Vacuity attack (NEW-PROP DISCIPLINE — recorded outcome)

The one new Prop-shaped object here is the localized condition
`∀ a ∈ seamCore, seamMatchGen z cHa ∈ C({seamPoint a}ᶜ)`. Attacked with zero geometric input:

* **The attack SUCCEEDS at `seamCore = ∅`, and only there.** `hbd_of_seamCore_empty` discharges
  `hbd` for EVERY `z` and EVERY `cHa` with a sphere-supported boundary when the core is empty —
  strictly generalizing `PinPlusTraceCapstoneCollarPairMatch.seamMatch_mem_of_seamCore_empty`
  (which was stated only at the frozen `cHa := diskDetectChain`).
* **That degenerate configuration is exactly what `CollarPairSeamRow.hseamHit` excludes**, and §3
  above certifies the non-degenerate case has real content: with `seamCore` nonempty the condition
  is *not* satisfiable by either term separately. So an inhabiter must carry `hseamHit` (seamCore
  nonempty) as a side condition — as `…CollarPairMatch` :60–63 instructs — and then the localized
  condition is a genuine mod-2 matching demand, not a free lunch.

## What is NOT proved here (stated precisely, no overclaim)

* **`hbd` is not discharged.** What remains after this module is one named geometric residual:
  produce a fundamental cycle `z` of `M` and a disk chain `cHa` (sphere-supported boundary,
  interior-detecting) whose seam-match chain cancels mod 2 over every core seam point. That is an
  *adapted-fundamental-cycle* construction, and it is not attempted here.
* **`hdetAB` is untouched.** The seam straddle-detection atom is not weakened, localized, or
  discharged by anything in this file.
* No converse to §3 is claimed: "the disk boundary reaches the core" is necessary, never sufficient.

`CollarPairCoreRow.ofSeamLocal` (§4) is the inhabiter's entry point: it builds the row from the
localized condition in place of `hbd`, quantifying `hdetAB` over the relative-cycle proof so no
proof term has to be threaded by hand.

## Fences honored

* `collar-pair-closed-seam-attached-collar-bridge-is-FALSE` — no bridge, no collar retraction, no
  `sphere ∖ S` support is constructed; the only sets named are the two gluing faces and the
  canonical `seamCore`.
* `collar-pair-open-complement-annulus-is-refuted-shape` — nothing routes through
  `SurgeredEndDatum.topFaceCovered`; the datum enters only through the free/shrunk face lemmas.
* `collar-pair-maximal-core-reenters-refuted-support` — no core is chosen: `seamCore` is the
  canonical one, and it is only ever asked to be NONEMPTY (never `univ`).
* `seam-transfer-open-support-uninhabitable` — nothing routes through `CapstoneSeamTransfer`,
  `hbd_ofTransfer` or `hasClass_ofTransferCorrector`, and **no new split structure of that shape is
  introduced**: the localization is stated on the summed chain.
* `collar-pair-coarse-core-does-not-relax-the-disk-side` — nothing is subdivided and `hctrlH` is not
  revived; §3 in fact *strengthens* the disk-side rigidity by showing the freedom §6 grants is
  compulsory.
* `capstone-choose-representative-corrector-uninhabitable` — the cylinder side stays the CONTROLLED
  representative `capstoneCylChainT z` pinned by `hz`; the opaque `.choose` chain never appears.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCrossProductRel
import SKEFTHawking.PinPlusTraceCapstoneCollarPairMatch

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

namespace SKEFTHawking.PinPlusTraceCapstoneCollarPairSeamLocal

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §1. The two gluing faces, and what lies off the canonical core -/

/-- **THE TWO GLUING FACES.** The pushed cylinder top face `fromCyl(M × {⊤})` together with the
pushed disk boundary sphere `fromHandle(S⁴)` — the only part of the trace carrier the seam-match
chain can reach. Everything in this set except the core seam points is inside `∂W`
(`seamSupport_diff_seamCoreImage_subset_bd`), which is what makes the localization an `↔`. -/
def seamSupport : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier :=
  (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ''
      (Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1)))
    ∪ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle ''
        {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}

variable {s t S hS φ hφ hφinj cd hseam d}

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE SEAM-MATCH CHAIN IS CONFINED TO THE TWO GLUING FACES**, at a FREE disk chain: the
cylinder term is the top slice of a cycle (`topSliceB_mem_topFace`) and the handle term is
sphere-supported (that is precisely the row's `hcHa`). This is the only place `hcHa` is used in the
localization, and it is what lets the `↔` run backwards. -/
theorem seamMatchGen_mem_seamSupport (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1)) :
    seamMatchGen s S hS φ hφ hφinj z cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (seamSupport s S hS φ hφ hφinj) (3 + 1) := by
  refine Submodule.add_mem _ ((closedEmbeddingChain_mem_iff_preimage _ _ _).mpr ?_)
    ((closedEmbeddingChain_mem_iff_preimage _ _ _).mpr ?_)
  · exact subspaceChains_mono (fun p hp => Or.inl ⟨p, hp, rfl⟩) (3 + 1)
      (topSliceB_mem_topFace (s := s) (S := S) (hS := hS) (φ := φ) (hφ := hφ) (hφinj := hφinj) z)
  · exact subspaceChains_mono (fun q hq => Or.inr ⟨q, hq, rfl⟩) (3 + 1) hcHa

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **OFF THE CANONICAL CORE, BOTH GLUING FACES ARE INSIDE `∂W`.** The two shrunk-face lemmas
(`topFaceShrunk_subset_fromCyl_preimage_bd`, `sphereShrunk_subset_fromHandle_preimage_bd`) fired at
the canonical `K := seamCore`, whose annulus hypothesis is the banked `hseamAnn_seamCore`. Both
`fromCyl` and `fromHandle` are injective, so removing the single set `seamPoint '' seamCore` from
the union removes exactly `φ '' seamCore` from the top face and `seamCore` from the sphere. -/
theorem seamSupport_diff_seamCoreImage_subset_bd :
    seamSupport s S hS φ hφ hφinj
        \ seamPoint s S hS φ hφ hφinj '' seamCore s t S hS φ hφ hφinj cd hseam d
      ⊆ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W := by
  rintro x ⟨hxU, hxK⟩
  rcases hxU with ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩
  · refine topFaceShrunk_subset_fromCyl_preimage_bd (d := d)
      (K := seamCore s t S hS φ hφ hφinj cd hseam d)
      (fun a ha => hseamAnn_seamCore (d := d) a ha) ⟨hp, ?_⟩
    rintro ⟨a, ha, rfl⟩
    exact hxK ⟨a, ha, ((ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a).symm⟩
  · refine sphereShrunk_subset_fromHandle_preimage_bd (d := d)
      (K := seamCore s t S hS φ hφ hφinj cd hseam d)
      (fun a ha => hseamAnn_seamCore (d := d) a ha) ⟨hq, ?_⟩
    rintro ⟨a, ha, rfl⟩
    exact hxK ⟨a, ha, rfl⟩

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`∂W` MISSES EVERY CORE SEAM POINT** — the converse containment, and near-definitional: it is
`compl_seamCore` read forwards (`seamCore` is by construction the complement of
`seamPoint ⁻¹' ∂W`). Stated separately because it is the forward leg of the localization `↔`, and
because it is the reason the localized condition is *weaker-looking but not weaker*. -/
theorem bd_subset_compl_seamCoreImage :
    ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W
      ⊆ (seamPoint s S hS φ hφ hφinj '' seamCore s t S hS φ hφ hφinj cd hseam d)ᶜ := by
  rintro x hx ⟨a, ha, rfl⟩
  have hc : a ∈ (seamCore s t S hS φ hφ hφinj cd hseam d)ᶜ := by
    rw [compl_seamCore]; exact hx
  exact hc ha

/-! ## §2. THE LOCALIZATION — `hbd` is a seam-point-by-seam-point condition -/

/-- **AVOIDING AN IMAGE IS AVOIDING EACH POINT OF IT.** A chain lies in `C((f '' K)ᶜ)` iff it lies
in `C({f a}ᶜ)` for every `a ∈ K` — chains have finite support and membership is per-simplex, so an
arbitrary intersection of complements poses no problem. General; no geometry. -/
theorem mem_subspaceChains_compl_image_iff {X : TopCat} {ι : Type} (f : ι → ↑X) (K : Set ι)
    (n : ℕ) (c : SingularChain X n) :
    c ∈ subspaceChains (X := X) ((f '' K)ᶜ) n
      ↔ ∀ a ∈ K, c ∈ subspaceChains (X := X) ({f a}ᶜ) n := by
  refine ⟨fun h a ha => subspaceChains_mono ?_ n h, fun h => mem_subspaceChains_of_support ?_⟩
  · exact Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr ⟨a, ha, rfl⟩)
  · intro τ hτ y hy
    rintro ⟨a, ha, hfa⟩
    exact range_of_mem_subspaceChains (h a ha) hτ hy hfa.symm

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE LOCALIZATION `↔`.** The seam-match chain is a `∂W`-chain **iff** it avoids the image of
the canonical core. Forward: `∂W` misses the core (`bd_subset_compl_seamCoreImage`). Backward: the
chain is confined to the two gluing faces, and off the core those faces are inside `∂W`. So the
analytic set `∂W` may be traded for a purely seam-local one with **no loss and no gain** — the
`hbd`-side analogue of the §2 bottom-face `↔` in `…CollarPairMatch`. -/
theorem seamMatchGen_mem_bd_iff_avoids_seamCoreImage (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1)) :
    (seamMatchGen s S hS φ hφ hφinj z cHa
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
      ↔ (seamMatchGen s S hS φ hφ hφinj z cHa
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (seamPoint s S hS φ hφ hφinj '' seamCore s t S hS φ hφ hφinj cd hseam d)ᶜ (3 + 1)) := by
  refine ⟨fun h => subspaceChains_mono (bd_subset_compl_seamCoreImage (d := d)) (3 + 1) h,
    fun h => ?_⟩
  have hinf : seamMatchGen s S hS φ hφ hφinj z cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (seamSupport s S hS φ hφ hφinj
          ∩ (seamPoint s S hS φ hφ hφinj '' seamCore s t S hS φ hφ hφinj cd hseam d)ᶜ) (3 + 1) := by
    rw [← SingularMayerVietoris.subspaceChains_inf]
    exact ⟨seamMatchGen_mem_seamSupport z cHa hcHa, h⟩
  exact subspaceChains_mono
    (fun x hx => seamSupport_diff_seamCoreImage_subset_bd (d := d) ⟨hx.1, hx.2⟩) (3 + 1) hinf

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`CollarPairCoreRow.hbd`, FULLY LOCALIZED — the headline.** The two-obligation row's
relative-cycle obligation is *equivalent* to: at every seam point of the canonical core, the
seam-match chain `fromCyl_#(z@⊤) + fromHandle_#(∂cHa)` has no surviving simplex. Composes the free
bottom face (`qGen_boundary_mem_iff_seamMatchGen_mem`), the localization `↔`, and the pointwise
reading. **One named geometric residual, purely local to the seam** — and by §3 it is a genuine
mod-2 cancellation demand whenever the core is nonempty. -/
theorem qGen_boundary_mem_iff_forall_seamCore (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1)) :
    (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
          (qGen s S hS φ hφ hφinj z cHa)
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
      ↔ ∀ a ∈ seamCore s t S hS φ hφ hφinj cd hseam d,
          seamMatchGen s S hS φ hφ hφinj z cHa
            ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
                ({seamPoint s S hS φ hφ hφinj a}ᶜ) (3 + 1) := by
  rw [qGen_boundary_mem_iff_seamMatchGen_mem t cd hseam d z cHa,
    seamMatchGen_mem_bd_iff_avoids_seamCoreImage (d := d) z cHa hcHa,
    mem_subspaceChains_compl_image_iff]

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE VACUITY ATTACK ON THE LOCALIZED OBLIGATION — it succeeds, at `seamCore = ∅` and there
only.** With an empty canonical core, `hbd` holds for EVERY fundamental cycle `z` and EVERY disk
chain `cHa` with sphere-supported boundary, with zero geometric input. This strictly generalizes
`…CollarPairMatch.seamMatch_mem_of_seamCore_empty`, which was stated only at the frozen
`cHa := diskDetectChain`; freeing the disk chain does not narrow the degenerate discharge.

The verdict is the good one, and it is the *same* verdict §5 of `…CollarPairMatch` reached: the
degenerate configuration is exactly the one `CollarPairSeamRow.hseamHit` rules out, and §3 below
shows the non-degenerate case carries real content (the two terms can never separately satisfy the
obligation). An inhabiter must therefore carry seam-core nonemptiness as a side condition; an
inhabitation that lands in `seamCore = ∅` proves nothing. -/
theorem hbd_of_seamCore_empty (hempty : seamCore s t S hS φ hφ hφinj cd hseam d = ∅)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1)) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qGen s S hS φ hφ hφinj z cHa)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) :=
  (qGen_boundary_mem_iff_forall_seamCore (d := d) z cHa hcHa).mpr
    (fun a ha => absurd (hempty ▸ ha) (Set.notMem_empty a))

/-! ## §3. FORCING — the cylinder side alone never suffices, so the disk side must reach the core -/

section FundCycleSupport

variable {m' : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] [T1Space (cylW M)]

/-- **A FUNDAMENTAL CYCLE IS SUPPORTED AT EVERY POINT.** No representative of `[M]` can be a chain
in `M ∖ {x}`. Proof without any local-homology bridge: if `z` misses `x`, its prism
`crossChain z` misses the *interior* cylinder point `(x, 1/2)` (`crossChain_mem_subspaceChains`,
whose `crossSubspace` is `M×{⊥,⊤} ∪ (M ∖ {x})×I`), so the prism's local class there vanishes
(`relClassOf_eq_zero_of_subspace`) — contradicting `crossChain_relClassOf_ne_zero`.

General (any closed connected charted `M`); the file's own use is at `m' = 2`. -/
theorem fundCycle_notMem_subspaceChains_compl (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) (x : M) :
    (z : SingularChain (TopCat.of M) (m' + 2))
      ∉ subspaceChains (X := TopCat.of M) ({x}ᶜ) (m' + 2) := by
  intro hzc
  set ymid : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩ with hymid
  set y : ↑(TopCat.of (cylW M)) := (x, ymid) with hydef
  have hbdI : ymid ∉ ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff, Set.Icc.coe_bot,
      Set.Icc.coe_top, hymid, not_or]
    norm_num
  have hbdI' : ymid ∉ boundaryI := by
    simp only [boundaryI, Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff, hymid, not_or]
    norm_num
  have hyb : y ∉ (cylModel m').boundary (cylW M) := by
    rw [cyl_boundary_eq]
    exact fun h => hbdI h.2
  have hsub : crossSubspace (TopCat.of M) ({x}ᶜ) ⊆ ({y}ᶜ : Set ↑(cyl (TopCat.of M))) := by
    rintro p (⟨-, hp⟩ | ⟨hp, -⟩) rfl
    · exact hbdI' hp
    · exact hp rfl
  have hmem : crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2))
      ∈ subspaceChains (X := TopCat.of (cylW M)) ({y}ᶜ) (m' + 1 + 1 + 1) :=
    subspaceChains_mono hsub (m' + 1 + 1 + 1)
      (crossChain_mem_subspaceChains (X := TopCat.of M) ({x}ᶜ) (m' + 2) hzc)
  exact crossChain_relClassOf_ne_zero (m' := m') (M := M) z hz y hyb
    (relClassOf_eq_zero_of_subspace (Set.Subset.refl _) (m' + 1) _ hmem _)

end FundCycleSupport

omit [T2Space s.M] [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- The top-slice map `x ↦ (x, ⊤)` is a topological embedding — what lets `mapChain` be inverted
along it (`closedEmbeddingChain_eq_mapChain` + `closedEmbeddingChain_mem_iff_preimage`), i.e. what
lets a support statement about `z@⊤` be read back as one about `z`. -/
theorem isEmbedding_sliceOne :
    Topology.IsEmbedding (⇑(slice (graphHom (TopCat.of s.M)) 1)) :=
  isEmbedding_prodMkLeft _

/-- **THE CYLINDER TERM ALONE IS NEVER A `∂W`-CHAIN** (given a nonempty canonical core and
`hφtop`). If it were, then intersecting with the top face and using
`topFaceSeamCore_eq_topFace_inter_preimage` would put `z@⊤` inside `M × {⊤} ∖ φ '' seamCore`; pulling
back along the top-slice embedding would put `z` off the point `(φ a).1` — impossible for a
fundamental cycle (`fundCycle_notMem_subspaceChains_compl`).

**This is the non-vacuity certificate for the localized obligation.** It says the seam-match chain
can only be a `∂W`-chain through genuine mod-2 cancellation *between* its two terms, never by each
term being one separately. Every "keep the two sides apart" inhabitation strategy is dead. -/
theorem topSlicePush_notMem_bd_of_mem_seamCore (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    {a : ↥S} (ha : a ∈ seamCore s t S hS φ hφ hφinj cd hseam d) :
    closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
        (3 + 1) (topSliceB s S hS φ hφ hφinj z)
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) := by
  intro h
  have h1 := (closedEmbeddingChain_mem_iff_preimage _ _ _).mp h
  have h2 : topSliceB s S hS φ hφ hφinj z
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1)))
            ∩ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
              (((𝓡 4).prod (𝓡∂ 1)).boundary
                (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1) := by
    rw [← SingularMayerVietoris.subspaceChains_inf]
    exact ⟨topSliceB_mem_topFace (s := s) (S := S) (hS := hS) (φ := φ) (hφ := hφ)
      (hφinj := hφinj) z, h1⟩
  have h2' := subspaceChains_mono
    (topFaceSeamCore_eq_topFace_inter_preimage (d := d) hφtop).ge (3 + 1) h2
  have h3 := (closedEmbeddingChain_mem_iff_preimage (isEmbedding_sliceOne (s := s)) (3 + 1)
    (z : SingularChain (TopCat.of s.M) (3 + 1))
    (A := (Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1)))
      \ φ '' seamCore s t S hS φ hφ hφinj cd hseam d)).mp
      (by
        rw [SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply.closedEmbeddingChain_eq_mapChain]
        exact h2')
  refine fundCycle_notMem_subspaceChains_compl (m' := 2) (M := s.M) z hz (φ a).1
    (subspaceChains_mono ?_ (2 + 2) h3)
  rintro p hp rfl
  exact hp.2 ⟨a, ha, Prod.ext rfl (phi_snd_eq_top hφtop a)⟩

/-- **THE HANDLE TERM IS FORCED OFF `∂W` TOO.** Under `hbd` with a nonempty core, the pushed disk
boundary cannot be a `∂W`-chain either: mod 2, if both the sum and the handle term were `∂W`-chains
so would be the cylinder term, contradicting `topSlicePush_notMem_bd_of_mem_seamCore`. -/
theorem diskBoundaryPush_notMem_bd_of_hbd (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qGen s S hS φ hφ hφinj z cHa)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    {a : ↥S} (ha : a ∈ seamCore s t S hS φ hφ hφinj cd hseam d) :
    closedEmbeddingChain
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
        (3 + 1) (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
          cHa)
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) := by
  intro hH
  have hsum := (qGen_boundary_mem_iff_seamMatchGen_mem t cd hseam d z cHa).mp hbd
  have hcyl := Submodule.add_mem _ hsum hH
  rw [seamMatchGen, add_assoc, ZModModule.add_self, add_zero] at hcyl
  exact topSlicePush_notMem_bd_of_mem_seamCore (d := d) hφtop z hz ha hcyl

/-- **THE DISK CHAIN'S BOUNDARY MUST REACH INTO THE CANONICAL CORE** — the sharp form. In any
inhabitation of `CollarPairCoreRow` with a nonempty canonical core (i.e. carrying `hseamHit` as
`…CollarPairMatch` :60–63 requires), `∂cHa` can NEVER be confined to `S⁴ ∖ seamCore`.

So the disk-side freedom that `…CollarPairMatch` §6 unlocked ("`cHa` is DATA, not the frozen
`diskDetectChain`") is not a convenience — it is **compulsory**: the disk chain has to be adapted to
the cylinder side over the core, and nothing supported away from the core can work. -/
theorem diskBoundary_notMem_sphereShrunk_of_hbd (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1)
    (z : cycles (TopCat.of s.M) (2 + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z)
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qGen s S hS φ hφ hφinj z cHa)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    (hne : (seamCore s t S hS φ hφ hφinj cd hseam d).Nonempty) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          ({v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}
            \ Subtype.val '' seamCore s t S hS φ hφ hφinj cd hseam d) (3 + 1) := by
  obtain ⟨a, ha⟩ := hne
  intro hC
  exact diskBoundaryPush_notMem_bd_of_hbd (d := d) hφtop z hz cHa hbd ha
    ((closedEmbeddingChain_mem_iff_preimage _ _ _).mpr
      (subspaceChains_mono (sphereShrunk_subset_fromHandle_preimage_bd (d := d)
        (fun b hb => hseamAnn_seamCore (d := d) b hb)) (3 + 1) hC))

/-! ## §4. The inhabiter's entry point -/

/-- **BUILD THE TWO-OBLIGATION ROW FROM THE LOCALIZED CONDITION.** Identical to
`CollarPairCoreRow` except that `hbd` is replaced by its `↔`-equivalent seam-local form `hlocal`,
and `hdetAB` is quantified over the relative-cycle proof (so no proof term has to be threaded by
hand — proofs are irrelevant, so this loses nothing). This is the shape an inhabitation attempt
should target: choose `z` and `cHa`, then show the seam-match chain misses each core seam point.

⚠ Carry seam-core NONEMPTINESS as a side condition. `hbd_of_seamCore_empty` discharges `hlocal`
vacuously when `seamCore = ∅`, so a row built this way with an empty core certifies nothing;
`…CollarPairMatch.qGen_ne_zero_of_seamCore_nonempty` is the guard, and §3 here is the reason the
nonempty case is not free. -/
def CollarPairCoreRow.ofSeamLocal (z : cycles (TopCat.of s.M) (2 + 2))
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
    (hdetAB : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier),
        x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) →
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
        x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
        ∀ (hq : chainBoundary
            (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
            (qGen s S hS φ hφ hφinj z cHa)
          ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
              ({x}ᶜ) (3 + 1)),
        relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
          (qGen s S hS φ hφ hφinj z cHa) hq ≠ 0) :
    CollarPairCoreRow s t S hS φ hφ hφinj cd hseam d where
  z := z
  hz := hz
  cHa := cHa
  hcHa := hcHa
  hdetHa := hdetHa
  hbd := (qGen_boundary_mem_iff_forall_seamCore (d := d) z cHa hcHa).mpr hlocal
  hdetAB := fun x hx hxA hxB => hdetAB x hx hxA hxB _

end

end SKEFTHawking.PinPlusTraceCapstoneCollarPairSeamLocal
