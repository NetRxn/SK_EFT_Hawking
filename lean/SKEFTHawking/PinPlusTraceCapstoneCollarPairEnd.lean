/-
# Phase 5q.H (#212) — `houtPair` DISCHARGED, AND `range eM'` SHOWN TO BE PINNED

`PinPlusTraceCapstoneCollarPairFace` reduced the collar-pair row's deepest obligation to ONE set-level
containment `hseamAnn` ("the surgered end swallows the seam annulus between the shrunk core `K` and
the edge of the attaching region"), and — the load-bearing observation this module cashes in — proved
in `K_eq_compl_seamPreimage` that a face row's core is **not free data**: `hKoffBd` and `hseamAnn`
*pin* it to `K = (seamPoint ⁻¹' ∂W)ᶜ`. Two things follow, and this module proves both.

* **§1 — the datum has NO degrees of freedom left to spend.** The lead question on this row was
  whether `range eM'` is a free construction choice (in which case `hseamAnn` is a construction task)
  or is pinned upstream (in which case it is not). It is **pinned, rigidly**:
  - `range_eM'_eq_bd_diff_source` — `d.bdry` is an *equality*, so with `d.disj`,
    `range d.eM' = ∂W ∖ range ktSourceEnd` exactly. `range_eM'_subset_bd` reads off the cap.
  - `bd_datum_indep` — `∂W` is **`rfl`-equal** for any two surgered-end data over the same `S`/`φ`/
    `cd`/`hseam`: `d` enters `ambientTraceBordism_capstone_ofSurgeredEnd` only through the end maps,
    never through the atlas the model boundary is read from.
  - hence `range_eM'_datum_indep` — **any two surgered-end data have the SAME `eM'` range**, and
    `seamPreimage_datum_indep` — `hseamAnn` holds for one datum iff it holds for all of them.

  So "build a datum whose `eM'` covers the seam annulus" is **not a move**. Enlarging `range eM'` past
  `∂W ∖ range ktSourceEnd` contradicts `bdry`; shrinking it contradicts `bdry`. This is a **route
  fact**, not a refutation: it does not say `hseamAnn` is false, it says no *datum-level* choice can
  bear on it. What it bears on is the chart-determined `∂W` — the `SingularSurgeryBoundaryFloor`
  territory that is chart-choice-dependent at `k = 0`.

* **§2–§5 — `houtPair` IS DISCHARGED, and the row drops to FOUR obligations.** If the core is forced
  anyway, stop carrying it. `seamCore := (seamPoint ⁻¹' ∂W)ᶜ` is the canonical core; at it both
  redundant fields collapse to tautologies — `hKoffBd_seamCore` is `subset_rfl` and
  `hseamAnn_seamCore` is `not_not.mp`. Therefore `houtPair_of_seamCoreSupport` produces the weld
  **from the two remainder supports alone, with no seam hypothesis of any kind** (and, inherited from
  `houtPair_of_seamAnnulusCovered`, with the trivial annulus `ann := 0`).

  `CollarPairGeomEnd` is the resulting row. Its geometric obligations are exactly **FOUR** —
  `hctrlC`, `hctrlH`, `hcoreHit`, `hq0det` — with `K`, `hKoffBd`, `bdOut` and `houtPair` all gone.
  `nonempty_collarPairGeomEnd_iff_face` certifies the trade is **content-free in both directions**
  (`↔`, both constructive), so the drop from the face row's five is real and not a reshuffle;
  `nonempty_collarPairGeomCore_of_end` chains it to the five-obligation row and thence to the
  capstone.

  §2's `topFaceSeamCore_eq_topFace_inter_preimage` restates the predecessor's tightness result
  row-free: an `End` row's `houtC` demands exactly the maximal-granularity top-face support
  `topface ∩ fromCyl ⁻¹' ∂W`. That is where the geometry now lives — in a support constraint on the
  chosen remainder chain, in the same "constraint on chosen data" category as the face row's `houtC`
  (which, by the forcing theorem, was already this very set). **Nothing moved; two redundant fields
  were deleted.**

⚠ **Counting discipline.** `houtC` / `houtH` are constraints on *chosen data* (`outC`, `outH`), not
geometric obligations — the convention `CollarPairGeomCore` itself uses when it calls its own count
FIVE while carrying `houtC`/`houtH` as fields. This module keeps that convention exactly.

⚠ **`CollarPairGeomEnd → CollarPairGeomCore` is SUFFICIENT, not equivalent** — same posture as
`CollarPairGeomFace`. `CollarPairGeomCore` may choose any `K ⊆ seamCore`, giving a *weaker* `houtC`
than the canonical core's, and `houtPair` does not recover the containment. The certified `↔` is with
`CollarPairGeomFace`, which is the live producer lane.

## Fences

* `collar-pair-open-complement-annulus-is-refuted-shape` — untouched. No collar-annulus refinement
  appears here at any granularity; the weld comes from `houtPair_of_seamAnnulusCovered` with
  `ann := 0` at the shrunk-core granularity. Nothing routes through `CapstoneSeamTransfer`.
* `collar-pair-maximal-core-reenters-refuted-support` — **not re-entered.** That fence closes
  `K = univ`. `seamCore` is not `univ` by fiat; it is `univ` exactly when no seam point meets `∂W`,
  and `CollarPairGeomFace.exists_seamPoint_mem_bd_of_null` already shows that configuration is
  *unsatisfiable* under the null / non-bounding hypotheses. An `End` row therefore lives in the live
  band `seamCore ⊊ univ` for exactly the same reason a face row does — it inherits the constraint
  rather than assuming its way around it.
* `collar-pair-face-row-forces-seam-to-meet-boundary` — this module is the positive use of that
  forcing, not a contradiction of it: the price it names (the seam must meet `∂W`) is precisely what
  makes `seamCore` a *proper* subset and the canonical-core row non-degenerate.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCollarPairFace

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
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
open SKEFTHawking.PinPlusTraceDiskCorePair
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
open SKEFTHawking.PinPlusTraceCapstoneCollarPair
open SKEFTHawking.PinPlusTraceCapstoneCollarPairGeom
open SKEFTHawking.PinPlusTraceCapstoneCollarPairCore
open SKEFTHawking.PinPlusTraceCapstoneCollarPairFace

namespace SKEFTHawking.PinPlusTraceCapstoneCollarPairEnd

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

variable {s t S hS φ hφ hφinj cd hseam d}

/-! ## §1. `range eM'` is PINNED, not a construction choice -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE SURGERED END IS DETERMINED BY `∂W`.** `d.bdry` is an *equality*, so `range eM'` is not
merely contained in `∂W` — together with `d.disj` it is exactly `∂W` minus the source end. -/
theorem range_eM'_eq_bd_diff_source :
    Set.range d.eM'
      = ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W
        \ Set.range (ktSourceEnd s.M D5 S hS φ hφ hφinj) := by
  ext x
  rw [capstone_boundary_eq]
  exact ⟨fun h => ⟨Or.inr h, fun hs => Set.disjoint_right.mp d.disj h hs⟩,
    fun h => h.1.resolve_left h.2⟩

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`range eM'` CANNOT BE ENLARGED.** It is capped by `∂W`. -/
theorem range_eM'_subset_bd :
    Set.range d.eM'
      ⊆ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W := by
  rw [range_eM'_eq_bd_diff_source (d := d)]
  exact Set.diff_subset

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`∂W` DOES NOT DEPEND ON THE SURGERED-END DATUM.** The capstone's carrier and its charted-space
structure are assembled from the attaching data `S`/`φ` and the seam-collar datum `cd`/`hseam` alone;
`d` enters `ambientTraceBordism_capstone_ofSurgeredEnd` only through the *end maps*, never through the
atlas. So the model boundary read off that atlas is literally the same set for every `d` — `rfl`. -/
theorem bd_datum_indep (d₁ d₂ : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam) :
    ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d₁).W
      = ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d₂).W := rfl

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **⛔ `range eM'` IS NOT A FREE CONSTRUCTION CHOICE — IT IS UNIQUELY DETERMINED.** Any two
surgered-end data over the *same* attaching + seam-collar data have the SAME surgered-end range.
`bdry` pins it from above (`range eM' ⊆ ∂W`) and from below (`∂W ∖ range ktSourceEnd ⊆ range eM'`),
and `∂W` is datum-independent (`bd_datum_indep`). So "choose a bigger `eM'`" is not a move: enlarging
the range past `∂W ∖ range ktSourceEnd` contradicts `bdry`, shrinking it contradicts `bdry` too.

⚠ **Scope.** This is a *route fact*, not a refutation: it says the seam-annulus residual cannot be
discharged by picking a better datum, because there is nothing to pick. It says nothing about whether
the residual is TRUE — that is a question about the constructed atlas, and the honest reading of
`SingularSurgeryBoundaryFloor` is that it is chart-choice-dependent at `k = 0`. It also does not
assert that a `SurgeredEndDatum` exists; it constrains every one that does. -/
theorem range_eM'_datum_indep (d₁ d₂ : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam) :
    Set.range d₁.eM' = Set.range d₂.eM' := by
  rw [range_eM'_eq_bd_diff_source (d := d₁), range_eM'_eq_bd_diff_source (d := d₂),
    bd_datum_indep (s := s) (t := t) d₁ d₂]
  rfl

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE SEAM-ANNULUS RESIDUAL IS DATUM-INVARIANT.** Since `∂W` is the same set for every
surgered-end datum, so is the seam's boundary-preimage: the residual `hseamAnn` (equivalently, by
`seamAnnulusCovered_iff_eM'`, "`range eM'` swallows the seam annulus") holds for one datum iff it
holds for every datum. Combined with `range_eM'_datum_indep`, this closes the "just build a datum
whose `eM'` covers the seam" line: there is no datum-level degree of freedom to spend. -/
theorem seamPreimage_datum_indep (d₁ d₂ : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam) :
    seamPoint s S hS φ hφ hφinj ⁻¹'
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d₁).W)
      = seamPoint s S hS φ hφ hφinj ⁻¹'
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d₂).W) := by
  rw [bd_datum_indep (s := s) (t := t) d₁ d₂]

/-! ## §2. The canonical core, and the two fields it discharges -/

variable (s t S hS φ hφ hφinj cd hseam d)

/-- **THE CANONICAL (FORCED) CORE** — the seam points that do *not* meet `∂W`. By
`CollarPairGeomFace.K_eq_compl_seamPreimage` this is not one admissible core among many: it is the
*only* core a face row can have, so promoting it from chosen data to a definition loses nothing. By
`seamPreimage_datum_indep` it does not depend on the surgered-end datum either. -/
def seamCore : Set ↥S :=
  (seamPoint s S hS φ hφ hφinj ⁻¹'
    (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W))ᶜ

variable {s t S hS φ hφ hφinj cd hseam d}

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`hseamAnn` IS A TAUTOLOGY AT THE CANONICAL CORE.** `a ∉ seamCore` unfolds to
`¬¬(seamPoint a ∈ ∂W)`, so the seam-annulus residual — the field the whole coarse route was reduced
to — discharges by `not_not.mp`. Nothing is being smuggled: the content did not vanish, it was never
in this field once the core was known to be forced. It now lives in the `houtC` support
(`topFaceSeamCore_eq_topFace_inter_preimage`), exactly where the face row already carried it. -/
theorem hseamAnn_seamCore (a : ↥S) (ha : a ∉ seamCore s t S hS φ hφ hφinj cd hseam d) :
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)
      ∈ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W :=
  not_not.mp ha

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`hKoffBd` IS A TAUTOLOGY AT THE CANONICAL CORE.** -/
theorem hKoffBd_seamCore :
    seamCore s t S hS φ hφ hφinj cd hseam d ⊆ (seamPoint s S hS φ hφ hφinj ⁻¹'
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W))ᶜ :=
  subset_rfl

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- The complement of the canonical core is the seam's boundary-preimage — by construction. -/
theorem compl_seamCore :
    (seamCore s t S hS φ hφ hφinj cd hseam d)ᶜ
      = seamPoint s S hS φ hφ hφinj ⁻¹'
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) :=
  compl_compl _

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE CANONICAL CORE'S SUPPORT SATURATES THE MAXIMAL BAND — row-free.**
`topFaceShrunk_eq_topFace_inter_preimage` with the *forced* core substituted in, so no
`CollarPairGeomFace` is needed to state it. This is what an `End` row's `houtC` actually demands: the
cylinder remainder must live in exactly the maximal-granularity top-face support. -/
theorem topFaceSeamCore_eq_topFace_inter_preimage (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1) :
    (Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ φ '' seamCore s t S hS φ hφ hφinj cd hseam d
      = (Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1)))
        ∩ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) := by
  rw [topFace_inter_fromCyl_preimage_bd (d := d) hφtop]
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · rcases hy with ⟨hytop, hyK⟩
    by_cases hyφ : y ∈ Set.range φ
    · obtain ⟨a, rfl⟩ := hyφ
      have haK : a ∈ (seamCore s t S hS φ hφ hφinj cd hseam d)ᶜ :=
        fun h => hyK (Set.mem_image_of_mem _ h)
      rw [compl_seamCore] at haK
      exact Set.mem_union_right _ ⟨a, (seamPoint_mem_bd_iff (d := d) hφtop a).mp haK, rfl⟩
    · exact Set.mem_union_left _ ⟨hytop, hyφ⟩
  · rintro y (⟨hytop, hyφ⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨hytop, fun hy => hyφ (Set.image_subset_range φ _ hy)⟩
    · refine ⟨⟨Set.mem_univ _, phi_snd_eq_top hφtop a⟩, fun hy => ?_⟩
      obtain ⟨b, hbK, hba⟩ := hy
      have hab : a = b := hφinj hba.symm
      have haK : a ∈ (seamCore s t S hS φ hφ hφinj cd hseam d)ᶜ := by
        rw [compl_seamCore]
        exact (seamPoint_mem_bd_iff (d := d) hφtop a).mpr ha
      exact haK (hab ▸ hbK)

/-! ## §3. `houtPair`, with NO seam hypothesis at all -/

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`houtPair` FROM THE TWO SUPPORTS ALONE — no seam hypothesis of any kind.** The `μ = 0` weld,
with the trivial annulus `ann := 0` (inherited from `houtPair_of_seamAnnulusCovered`), produced from
nothing but the remainder supports at the canonical core. This is the discharge of `#212`'s first
target: `houtPair` is no longer an obligation on this lane. -/
theorem houtPair_of_seamCoreSupport (z : cycles (TopCat.of s.M) (2 + 2))
    {outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    (houtC : outC ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1)))
        \ φ '' seamCore s t S hS φ hφ hφinj cd hseam d) (3 + 1))
    (houtH : outH ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1}
        \ Subtype.val '' seamCore s t S hS φ hφ hφinj cd hseam d) (3 + 1)) :
    ∃ bdOut : SingularChain
      (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1),
      weldSum z 0 outC outH
        = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
            (3 + 1) bdOut :=
  houtPair_of_seamAnnulusCovered (d := d) z houtC houtH hseamAnn_seamCore

/-! ## §4. `CollarPairGeomEnd` — the FOUR-obligation row -/

variable (s t S hS φ hφ hφinj cd hseam d)

/-- **THE FOUR-OBLIGATION ROW.** `CollarPairGeomFace` with its core promoted to the canonical
`seamCore` and the two fields that promotion makes redundant (`K`'s companion `hKoffBd`, and
`hseamAnn`) deleted; `bdOut`/`houtPair` were already gone at the face stage. Every remaining field is
verbatim its face-row counterpart with `K := seamCore` substituted.

Its geometric obligations are exactly **FOUR**: `hctrlC`, `hctrlH`, `hcoreHit`, `hq0det`.
Certified equivalent (as an inhabitation problem) to `CollarPairGeomFace` by
`nonempty_collarPairGeomEnd_iff_face`, hence a producer for `CollarPairGeomCore`. -/
structure CollarPairGeomEnd where
  /-- a fundamental cycle of the closed source 4-manifold `M`. -/
  z : cycles (TopCat.of s.M) (2 + 2)
  /-- `z` represents THE fundamental class. -/
  hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
    = Homology.mk (TopCat.of s.M) (2 + 2) z
  /-- **the shared 4-dimensional seam core** on the attaching region. -/
  cCore : SingularChain (TopCat.of ↥S) (3 + 1)
  /-- the cylinder-side remainder. -/
  outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
  /-- the handle-side remainder. -/
  outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
  /-- **GEOMETRIC 1 — the top-face split** `z@⊤ = φ_# cCore + outC`. -/
  hctrlC : topSliceB s S hS φ hφ hφinj z
    = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC
  /-- **GEOMETRIC 2 — the disk-side split** on the canonical detecting chain. -/
  hctrlH : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
      diskDetectChain
    = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cCore + outH
  /-- the cylinder remainder is supported in the top face off the CANONICAL core. -/
  houtC : outC ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1)))
        \ φ '' seamCore s t S hS φ hφ hφinj cd hseam d) (3 + 1)
  /-- the handle remainder is supported in the boundary sphere off the CANONICAL core. -/
  houtH : outH ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1}
        \ Subtype.val '' seamCore s t S hS φ hφ hφinj cd hseam d) (3 + 1)
  /-- **GEOMETRIC 3 — the anti-fake tether** (was GEOMETRIC 4). -/
  hcoreHit :
    mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
    cCore ∉ subspaceChains (X := TopCat.of ↥S)
      ((seamCore s t S hS φ hφ hφinj cd hseam d)ᶜ) (3 + 1)
  /-- **GEOMETRIC 4 — the seam straddle-detection atom** (was GEOMETRIC 5). -/
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

namespace CollarPairGeomEnd

variable {s t S hS φ hφ hφinj cd hseam d}
variable (E : CollarPairGeomEnd s t S hS φ hφ hφinj cd hseam d)

omit [PreconnectedSpace s.M] in
/-- **THE END ROW PRODUCES THE FACE ROW** — `K := seamCore`, and both `hKoffBd` and `hseamAnn` are
tautologies at it. -/
def toCollarPairGeomFace : CollarPairGeomFace s t S hS φ hφ hφinj cd hseam d where
  z := E.z
  hz := E.hz
  K := seamCore s t S hS φ hφ hφinj cd hseam d
  hKoffBd := hKoffBd_seamCore
  cCore := E.cCore
  outC := E.outC
  outH := E.outH
  hctrlC := E.hctrlC
  hctrlH := E.hctrlH
  houtC := E.houtC
  houtH := E.houtH
  hseamAnn := fun a ha => hseamAnn_seamCore a ha
  hcoreHit := E.hcoreHit
  hq0det := E.hq0det

end CollarPairGeomEnd

namespace CollarPairGeomEnd

variable {s t S hS φ hφ hφinj cd hseam d}
variable (F : CollarPairGeomFace s t S hS φ hφ hφinj cd hseam d)

omit [PreconnectedSpace s.M] in
/-- **THE FACE ROW PRODUCES THE END ROW** — the converse direction. -/
def ofFace : CollarPairGeomEnd s t S hS φ hφ hφinj cd hseam d where
  z := F.z
  hz := F.hz
  cCore := F.cCore
  outC := F.outC
  outH := F.outH
  hctrlC := F.hctrlC
  hctrlH := F.hctrlH
  houtC := by
    have h := F.houtC
    rwa [F.K_eq_compl_seamPreimage] at h
  houtH := by
    have h := F.houtH
    rwa [F.K_eq_compl_seamPreimage] at h
  hcoreHit := by
    have h := F.hcoreHit
    rwa [F.K_eq_compl_seamPreimage] at h
  hq0det := F.hq0det

end CollarPairGeomEnd

/-! ## §5. The equivalence certificate, and the production statement -/

variable {s t S hS φ hφ hφinj cd hseam d}

omit [PreconnectedSpace s.M] in
/-- **THE REDUCTION IS CONTENT-FREE** — an `↔`, both directions constructive, so the drop from the
face row's FIVE obligations to the end row's FOUR is a genuine reduction and not a reshuffle.
Forward: substitute `K := seamCore`; both deleted fields are tautologies. Backward: rewrite the face
row's own fields along `K_eq_compl_seamPreimage`, which says its `K` *was* `seamCore` all along. -/
theorem nonempty_collarPairGeomEnd_iff_face :
    Nonempty (CollarPairGeomEnd s t S hS φ hφ hφinj cd hseam d)
      ↔ Nonempty (CollarPairGeomFace s t S hS φ hφ hφinj cd hseam d) :=
  ⟨fun h => ⟨h.some.toCollarPairGeomFace⟩, fun h => ⟨CollarPairGeomEnd.ofFace h.some⟩⟩

omit [PreconnectedSpace s.M] in
/-- **THE PRODUCTION STATEMENT.** Inhabiting the four-obligation row inhabits the five-obligation row
(through the face row), hence — via `CollarPairGeomCore.toHasClass` — the capstone's relative
fundamental class. As with the face row, only this direction is claimed. -/
theorem nonempty_collarPairGeomCore_of_end
    (h : Nonempty (CollarPairGeomEnd s t S hS φ hφ hφinj cd hseam d)) :
    Nonempty (CollarPairGeomCore s t S hS φ hφ hφinj cd hseam d) :=
  nonempty_collarPairGeomCore_of_face (nonempty_collarPairGeomEnd_iff_face.mp h)

end

end SKEFTHawking.PinPlusTraceCapstoneCollarPairEnd
