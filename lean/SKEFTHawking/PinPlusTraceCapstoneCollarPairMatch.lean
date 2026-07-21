/-
# Phase 5q.H (#212) — THE ROW COLLAPSES: 4 → 3 → 2, and the disk chain stops being frozen.

**Headline (a premise correction, not a discharge).** The collar-pair row's cylinder/handle split
block — `cCore`, `outC`, `outH`, `hctrlC`, `hctrlH`, `houtC`, `houtH` (and, upstream, `bdOut` /
`houtPair` / the bridge triple / the whole relative-MV partition) — is consumed downstream through
**exactly one** consequence: that the frozen glued chain `q₀ z` is a **relative cycle**,
`∂(q₀ z) ∈ C(∂W)`. Nothing else about the split ever reaches the capstone. In particular the
**exact shared-`cCore` co-adaptation** — the item the `#212` codex dossier ranked hardest
("Shared `cCore`, `houtPair`, canonical-chain `hbridge`, 450–800 LOC, Opus, hardest") and the residue
that `PinPlusTraceCapstoneCollarPairHandle` left sitting on `hctrlC` — **is not an obligation of the
row at all.**

So this module replaces the four-obligation `CollarPairGeomEnd` row by a **three-obligation** one:

| End row (4) | this row (3) |
|---|---|
| `hctrlC` + `hctrlH` (+ the `houtC`/`houtH` support constraints) | `hseamMatch` — ONE chain membership |
| `hcoreHit` (chain-quantified anti-fake tether) | `hseamHit` — ONE set-level nonemptiness |
| `hq0det` | `hq0det` (verbatim) |

## What is proved

* **§1 `qZero_boundary_eq_seamMatch_add_botPush`** — `∂(q₀ z)` computed: the cylinder chain is a
  prism over `z`, so its boundary is the two endpoint slices, and the bottom slice is the *source
  end*, already inside `∂W` for free (`botPush_mem_bd`). What is left is
  `seamMatch z := fromCyl_# (z@⊤) + fromHandle_# (∂ diskDetectChain)`.
* **§2 `qZero_boundary_mem_iff_seamMatch_mem` — THE EQUIVALENCE CERTIFICATE (`↔`).**
  `∂(q₀ z) ∈ C(∂W) ↔ seamMatch z ∈ C(∂W)`. So the row's field may be stated at the sharper
  `seamMatch` granularity with **no loss and no gain**: the bottom face is genuinely free.
* **§3 `CollarPairSeamRow`** — the three-obligation row, and `toCorrectorT` / `toHasClass`: the
  capstone's relative fundamental class from `{hseamMatch, hseamHit, hq0det}` and nothing else.
  The corrector is `p := q₀ z` — a **definition** of the row's own `z` (round-13 gate spec 3/8), at
  which the gate's `heS` and `hagree` are *identically zero mismatches*. That is the content of the
  correction: the corrector degree of freedom buys nothing; the row's real demand is that `q₀ z` is
  already a relative cycle.
* **§4 `CollarPairGeomEnd.toSeamRow`** — the 4 → 3 production, and
  `nonempty_collarPairSeamRow_of_end`; plus `CollarPairBuild.toSeamRow`, which shows even the
  original frozen eight-field build factors through the three-obligation row — the collapse is not
  an artifact of the `End` row's canonical core.
* **§5 the vacuity attack, run on the new row.** `seamMatch_mem_of_seamCore_empty`: if the canonical
  core is EMPTY — every seam point already inside `∂W` — then `hseamMatch` holds for **every** `z`
  with zero geometric input. The attack succeeds, and its target is *precisely* the configuration
  the row's own `hseamHit` excludes: the two obligations are in genuine tension, neither can be
  traded for the other, and the row is not inhabitable by degenerating the seam.
  `seamMatch_mem_datum_indep` — no surgered-end-datum shopping (`∂W` is `rfl`-equal across data).
  `seamCore_nonempty_iff_exists_offRange_eM'` — under `hφtop`, `hseamHit` says exactly *the surgered
  end does not swallow the whole seam*, a boundary-floor fact, not a datum choice.
* **§6 `CollarPairCoreRow` — TWO obligations, and the disk chain is FREE.** Firing the underlying
  engine `capstone_hasClass_ofCoreChains` directly (rather than through `CapstoneSeamCorrectorT`)
  removes two things at once. (a) The anti-fake field `hseamHit` has no premise, because no corrector
  is supplied at all — and nothing is evaded: the guard survives as the *theorem*
  `qGen_ne_zero_of_seamCore_nonempty`, which forces the glued chain nonzero under exactly the
  hypothesis `hseamHit` asserts. (b) **`cHa` becomes DATA.** The disk-side rigidity recorded in
  `collar-pair-coarse-core-does-not-relax-the-disk-side` ("`diskDetectChain` is fixed") is an artifact
  of the corrector interface, whose `heS`/`hagree` name `diskDetectChain` literally; the engine is
  general in *both* piece chains, needing only a disk detecting triple. `CollarPairSeamRow.toCoreRow`
  is the 3 → 2 production at `cHa := diskDetectChain`.

  **Which row to aim at.** `CollarPairCoreRow` is the terminal inhabitation target — but an inhabiter
  should carry `hseamHit` as a *side condition* (not a field), because §5 shows the degenerate
  `seamCore = ∅` configuration discharges the relative-cycle obligation for free; `hseamHit` is what
  certifies the inhabitation is not that one.

## Direction of strength — stated precisely (no overclaim)

The `End → Seam` production is **one-way by design**: the seam row's hypotheses are strictly
*weaker*, so the producer theorem is strictly *stronger* and the inhabitation problem strictly
*easier*. **`hctrlC` is NOT discharged here.** What is proved is that the row no longer asks for it:
any inhabitation effort should target `hseamMatch`, and the exact-sharing rigidity should not be
built. The one place an honest `↔` is available — the bottom-face drop — is supplied as one
(§2). No converse `Seam → End` is claimed: recovering a split block from a relative-cycle statement
would require constructing `cCore`/`outC`/`outH`, which the open-cover engine does not give at the
closed-`S` granularity (fence `collar-pair-closed-seam-attached-collar-bridge-is-FALSE`).

## Fences honored

* `collar-pair-closed-seam-attached-collar-bridge-is-false` — no bridge, no collar retraction, no
  `sphere ∖ S` support appears; this module *removes* the demand rather than supplying it.
* `collar-pair-open-complement-annulus-is-refuted-shape` — nothing routes through
  `SurgeredEndDatum.topFaceCovered` to build a `CapstoneSeamTransferSeam`; the only use of the
  surgered-end datum is the *free* bottom-face containment `capstone_boundary_eq`.
* `collar-pair-maximal-core-reenters-refuted-support` — no core is chosen at all here; `hseamHit`
  speaks only of the canonical `seamCore`, and asks for it to be NONEMPTY (never `univ`).
* `seam-transfer-open-support-uninhabitable` — nothing routes through `CapstoneSeamTransfer`,
  `hbd_ofTransfer` or `hasClass_ofTransferCorrector`; the consumers are `CapstoneSeamCorrectorT`
  (§3) and `capstone_hasClass_ofCoreChains` (§6).
* `collar-pair-coarse-core-does-not-relax-the-disk-side` — **not re-attempted, and not contradicted.**
  That fence rules out the representative-subdivision dodge *for `hctrlH`*, whose disk chain is
  frozen by the corrector interface. §6 does not subdivide anything and does not revive `hctrlH`; it
  observes that the ENGINE never demanded the canonical chain in the first place. The fence's scope
  ("`diskDetectChain` is fixed") is about the row as then stated, not about
  `capstone_hasClass_ofCoreChains`.
* `capstone-choose-representative-corrector-uninhabitable` — the cylinder side stays the CONTROLLED
  representative `capstoneCylChainT z` pinned by `hz`, never the opaque `.choose`-based
  `capstoneCylChain`. (That is the one place where freedom is *not* available and must not be taken.)

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCollarPairEnd

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
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlue
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
open SKEFTHawking.PinPlusTraceDiskCorePair
open SKEFTHawking.PinPlusTraceCapstoneCorrector
open SKEFTHawking.PinPlusTraceCapstoneCollarPair
open SKEFTHawking.PinPlusTraceCapstoneCollarPairGeom
open SKEFTHawking.PinPlusTraceCapstoneCollarPairCore
open SKEFTHawking.PinPlusTraceCapstoneCollarPairFace
open SKEFTHawking.PinPlusTraceCapstoneCollarPairEnd

namespace SKEFTHawking.PinPlusTraceCapstoneCollarPairMatch

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §1. `∂(q₀ z)`, computed: the seam-match term plus a free bottom face -/

/-- **THE SEAM-MATCH CHAIN.** The top slice of the fundamental cycle and the boundary of the
canonical disk-detecting chain, both pushed into the trace carrier. This is *all* of `∂(q₀ z)` that
is not already inside `∂W`. -/
def seamMatch (z : cycles (TopCat.of s.M) (2 + 2)) :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) :=
  closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
      (3 + 1) (topSliceB s S hS φ hφ hφinj z)
    + closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
      (3 + 1) (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
        diskDetectChain)

/-- The pushed bottom face of the cylinder — the source end of the trace. -/
def botPush (z : cycles (TopCat.of s.M) (2 + 2)) :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) :=
  closedEmbeddingChain
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
    (3 + 1) (ctrlBottom s S hS φ hφ hφinj z 0)

variable {s t S hS φ hφ hφinj cd hseam d}

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE BOTTOM FACE IS FREE.** `z@⊥` lives in `M × {⊥}`, which `fromCyl` sends into
`range ktSourceEnd ⊆ ∂W`. No datum field and no seam hypothesis is used. -/
theorem botPush_mem_bd (z : cycles (TopCat.of s.M) (2 + 2)) :
    botPush s S hS φ hφ hφinj z
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) :=
  (closedEmbeddingChain_mem_iff_preimage _ _ _).mpr
    (subspaceChains_mono (bottomFace_subset_fromCyl_preimage_bd (d := d)) (3 + 1)
      (ctrlBottom_zero_mem_bottomFace (s := s) (S := S) (hS := hS) (φ := φ) (hφ := hφ)
        (hφinj := hφinj) z))

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`∂(q₀ z)` COMPUTED.** The controlled cylinder representative is a prism over the cycle `z`, so
its boundary is exactly the two endpoint slices (`chainBoundary_crossChain`); pushing through the two
closed embeddings and adding the disk term gives the seam-match chain plus the bottom face. -/
theorem qZero_boundary_eq_seamMatch_add_botPush (z : cycles (TopCat.of s.M) (2 + 2)) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qZero s S hS φ hφ hφinj z)
      = seamMatch s S hS φ hφ hφinj z + botPush s S hS φ hφ hφinj z := by
  have hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
        (capstoneCylChainT s S hS φ hφ hφinj z)
      = topSliceB s S hS φ hφ hφinj z + ctrlBottom s S hS φ hφ hφinj z 0 :=
    chainBoundary_crossChain 3 (z : SingularChain (TopCat.of s.M) (3 + 1)) z.2
  rw [qZero, map_add, chainBoundary_closedEmbeddingChain, chainBoundary_closedEmbeddingChain, hbd,
    closedEmbeddingChain_add, seamMatch, botPush]
  abel

/-! ## §2. THE EQUIVALENCE CERTIFICATE -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE `↔`.** The frozen glued chain is a relative cycle **iff** the seam-match chain is a
`∂W`-chain. The bottom face is free in both directions, so sharpening the row's obligation from
`∂(q₀ z) ∈ C(∂W)` to `seamMatch z ∈ C(∂W)` is a genuine equivalence — no content is moved. -/
theorem qZero_boundary_mem_iff_seamMatch_mem (z : cycles (TopCat.of s.M) (2 + 2)) :
    (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qZero s S hS φ hφ hφinj z)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
      ↔ (seamMatch s S hS φ hφ hφinj z
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)) := by
  rw [qZero_boundary_eq_seamMatch_add_botPush (s := s) z]
  refine ⟨fun h => ?_, fun h => Submodule.add_mem _ h (botPush_mem_bd (d := d) z)⟩
  have := Submodule.add_mem _ h (botPush_mem_bd (d := d) z)
  rwa [add_assoc, ZModModule.add_self, add_zero] at this

/-! ## §3. `CollarPairSeamRow` — the THREE-obligation row -/

variable (s t S hS φ hφ hφinj cd hseam d)

/-- **THE THREE-OBLIGATION ROW.** The whole `#212` collar-pair apparatus, reduced to what the
capstone actually consumes.

Geometric obligations, exactly **THREE**:
* `hseamMatch` — the seam match: `fromCyl_#(z@⊤) + fromHandle_#(∂ diskDetectChain)` is a `∂W`-chain
  (equivalently, by `qZero_boundary_mem_iff_seamMatch_mem`, the frozen glued chain is a relative
  cycle). This ONE membership replaces the End row's `hctrlC` + `hctrlH` **and** their `houtC` /
  `houtH` support constraints; no shared `cCore` and no co-adaptation is asked for.
* `hseamHit` — genuine attachment forces the canonical core to be nonempty, i.e. **some** seam point
  misses `∂W`. This replaces the End row's chain-quantified `hcoreHit`, of which it is the only
  consequence ever used.
* `hq0det` — the seam straddle-detection atom, verbatim from the End row.

Note `hseamHit` is not vacuously true and not provable in this parameter row: at `S = ∅` the seam is
empty and `seamCore = ∅`, so a genuinely attached handle is a real hypothesis on `(S, φ)`. -/
structure CollarPairSeamRow where
  /-- a fundamental cycle of the closed source 4-manifold `M`. -/
  z : cycles (TopCat.of s.M) (2 + 2)
  /-- `z` represents THE fundamental class. -/
  hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
    = Homology.mk (TopCat.of s.M) (2 + 2) z
  /-- **GEOMETRIC 1 — the seam match.** -/
  hseamMatch : seamMatch s S hS φ hφ hφinj z
    ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)
  /-- **GEOMETRIC 2 — the anti-fake tether, at set level.** -/
  hseamHit :
    mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
    (seamCore s t S hS φ hφ hφinj cd hseam d).Nonempty
  /-- **GEOMETRIC 3 — the seam straddle-detection atom.** -/
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

namespace CollarPairSeamRow

variable {s t S hS φ hφ hφinj cd hseam d}
variable (R : CollarPairSeamRow s t S hS φ hφ hφinj cd hseam d)

omit [PreconnectedSpace s.M] in
/-- The frozen glued chain of a seam row is a relative cycle — the `↔` of §2, read forwards. -/
theorem qZero_boundary_mem :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qZero s S hS φ hφ hφinj R.z)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) :=
  (qZero_boundary_mem_iff_seamMatch_mem (d := d) R.z).mpr R.hseamMatch

omit [PreconnectedSpace s.M] in
/-- **The tether bites.** Genuine attachment gives a seam point of the trace carrier that lies off
`∂W` and inside BOTH ends — the exact configuration `hq0det` speaks about. -/
theorem exists_seamPoint_offBd
    (hgen : mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (R.z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1)) :
    ∃ x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier,
      x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ∧ x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
        ∧ x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle := by
  obtain ⟨a, ha⟩ := R.hseamHit hgen
  exact ⟨seamPoint s S hS φ hφ hφinj a, ha,
    ⟨φ a, (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a⟩, ⟨(a : D5), rfl⟩⟩

omit [PreconnectedSpace s.M] in
/-- **The frozen glued chain is nonzero under genuine attachment** — the round-13 gate's spec-7
anti-fake guard, at `p := q₀ z`. -/
theorem qZero_ne_zero_of_genuine
    (hgen : mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (R.z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1)) :
    qZero s S hS φ hφ hφinj R.z ≠ 0 := by
  obtain ⟨x, hx, hxA, hxB⟩ := R.exists_seamPoint_offBd hgen
  intro hzero
  refine R.hq0det x hx hxA hxB
    (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) R.qZero_boundary_mem) ?_
  exact relClassOf_eq_zero_of_subspace (Set.empty_subset _) 3 (qZero s S hS φ hφ hφinj R.z)
    (by rw [hzero]; exact Submodule.zero_mem _) _

/-- **THE PRODUCER** `CollarPairSeamRow → CapstoneSeamCorrectorT`, with the corrector taken to be
the frozen glued chain itself. `p` is a DEFINITION of the row's `z` (gate spec 3/8) — nothing is
supplied independently — and at this `p` the gate's mismatch facts `heS`/`hagree` are the zero
chain, which is the whole content of the correction this module records: **the corrector degree of
freedom buys nothing**; what the capstone needs is that `q₀ z` is already a relative cycle. -/
def toCorrectorT : CapstoneSeamCorrectorT s t S hS φ hφ hφinj cd hseam d where
  z := R.z
  hz := R.hz
  p := qZero s S hS φ hφ hφinj R.z
  hpS := R.qZero_boundary_mem
  heS := by
    rw [qZero, sub_self, map_zero]
    exact Submodule.zero_mem _
  hagree := by
    rw [qZero, sub_self]
    exact Submodule.zero_mem _
  hp_det := fun x hx hxA hxB => R.hq0det x hx hxA hxB _
  nonzero_of_genuine := fun hgen => R.qZero_ne_zero_of_genuine hgen

/-- **THE CAPSTONE `hasClass`, FROM THREE GEOMETRIC OBLIGATIONS.** The `#212` chain, terminal form:
`CollarPairSeamRow → CapstoneSeamCorrectorT → hasClass`. The conclusion is the EXACT
`CapstoneAmbientSupply.hasClass` field type, so the downstream rows consume it unchanged. -/
def toHasClass :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  R.toCorrectorT.toHasClass

end CollarPairSeamRow

/-! ## §4. The 4 → 3 production -/

variable {s t S hS φ hφ hφinj cd hseam d}

omit [PreconnectedSpace s.M] in
/-- **`hseamHit` FROM `hcoreHit`.** An End row's chain-quantified tether has exactly one consequence
the capstone uses: the canonical core is nonempty. (If `seamCore = ∅` its complement is `univ`, and
every chain — in particular `cCore` — lies in `C(univ)`, contradicting `hcoreHit`.) -/
theorem seamCore_nonempty_of_end (E : CollarPairGeomEnd s t S hS φ hφ hφinj cd hseam d)
    (hgen : mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (E.z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1)) :
    (seamCore s t S hS φ hφ hφinj cd hseam d).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  exact E.hcoreHit hgen (by rw [hempty, Set.compl_empty]; exact mem_subspaceChains_univ _ _)

omit [PreconnectedSpace s.M] in
/-- **THE END ROW PRODUCES THE SEAM ROW** — the 4 → 3 reduction. `hseamMatch` is the End row's own
relative-cycle consequence read through the §2 `↔`; `hseamHit` is `seamCore_nonempty_of_end`;
`hq0det` passes through verbatim.

⚠ **One-way by design.** The seam row's hypotheses are strictly weaker, so no converse is claimed
(and none is expected: recovering a split block would need `cCore`/`outC`/`outH` at the closed-`S`
granularity the refuted bridge asked for). `hctrlC` is not discharged — it is shown unnecessary. -/
def CollarPairGeomEnd.toSeamRow (E : CollarPairGeomEnd s t S hS φ hφ hφinj cd hseam d) :
    CollarPairSeamRow s t S hS φ hφ hφinj cd hseam d where
  z := E.z
  hz := E.hz
  hseamMatch := (qZero_boundary_mem_iff_seamMatch_mem (d := d) E.z).mp
    E.toCollarPairGeomFace.toCollarPairGeomCore.qZero_boundary_mem
  hseamHit := fun hgen => seamCore_nonempty_of_end E hgen
  hq0det := E.hq0det

omit [PreconnectedSpace s.M] in
/-- **THE PRODUCTION STATEMENT.** Inhabiting the four-obligation row inhabits the three-obligation
one. Together with `CollarPairSeamRow.toHasClass` this is the `#212` lane's shortest end-to-end
route: the capstone's relative fundamental class rests on `hseamMatch`, `hseamHit`, `hq0det` — and
nothing else. -/
theorem nonempty_collarPairSeamRow_of_end
    (h : Nonempty (CollarPairGeomEnd s t S hS φ hφ hφinj cd hseam d)) :
    Nonempty (CollarPairSeamRow s t S hS φ hφ hφinj cd hseam d) :=
  ⟨CollarPairGeomEnd.toSeamRow h.some⟩

omit [PreconnectedSpace s.M] in
/-- **THE FROZEN EIGHT-FIELD BUILD ALSO PRODUCES THE SEAM ROW.** Entering one level further left:
even the original `CollarPairBuild` — free subdivision counts, chosen core `K`, split chains,
`bdOut`/`houtPair`, the bridge triple and the full relative-MV partition — factors through the
three-obligation row. Its `K.Nonempty` (from `hcoreHit`) lands inside `seamCore` by its own
`hKoffBd`. So the collapse is not an artifact of the `End` row's canonical core: **every row in the
`#212` tower is subsumed.** -/
def CollarPairBuild.toSeamRow (R : CollarPairBuild s t S hS φ hφ hφinj cd hseam d) :
    CollarPairSeamRow s t S hS φ hφ hφinj cd hseam d where
  z := R.z
  hz := R.hz
  hseamMatch := (qZero_boundary_mem_iff_seamMatch_mem (d := d) R.z).mp R.qZero_boundary_mem
  hseamHit := fun hgen => (R.K_nonempty hgen).imp (fun _ ha => R.hKoffBd ha)
  hq0det := R.hq0det

/-! ## §5. The vacuity attack, run on the new row -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- The top slice of a fundamental cycle lives in the cylinder's top face — the `⊤`-mirror of
`ctrlBottom_zero_mem_bottomFace`. -/
theorem topSliceB_mem_topFace (z : cycles (TopCat.of s.M) (2 + 2)) :
    topSliceB s S hS φ hφ hφinj z
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        (Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) (3 + 1) := by
  rw [topSliceB]
  exact mapChain_mem_subspaceChains (slice (graphHom (TopCat.of s.M)) 1)
    (fun x _ => by rw [slice_graphHom]; exact ⟨Set.mem_univ x, rfl⟩) (3 + 1) _
    (mem_subspaceChains_univ _ _)

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE VACUITY ATTACK SUCCEEDS — in exactly one configuration, and the tether excludes it.**
If the canonical core is EMPTY — i.e. every seam point already lies in `∂W` — then `hseamMatch`
holds for *every* fundamental cycle `z`, with zero geometric input: the whole top face and the whole
boundary sphere are then inside the `∂W`-preimages, and the two terms are separately `∂W`-chains.

This is the roadmap-§3 vacuity attack run against the new row, and its verdict is the good one: the
degenerate discharge exists, and it is *precisely* the configuration the row's own second obligation
`hseamHit` rules out. So the two obligations are in genuine tension — `hseamMatch` carries content
exactly when `hseamHit` does — and neither can be traded for the other. Note also what is NOT needed
here: no `hφtop`, no shrunk core, no split. -/
theorem seamMatch_mem_of_seamCore_empty
    (hempty : seamCore s t S hS φ hφ hφinj cd hseam d = ∅)
    (z : cycles (TopCat.of s.M) (2 + 2)) :
    seamMatch s S hS φ hφ hφinj z
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1) := by
  have hseamAnn : ∀ a : ↥S, a ∉ (∅ : Set ↥S) →
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)
        ∈ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W :=
    fun a _ => hseamAnn_seamCore (d := d) a (by rw [hempty]; exact Set.notMem_empty a)
  have htop := topFaceShrunk_subset_fromCyl_preimage_bd (d := d) hseamAnn
  have hsph := sphereShrunk_subset_fromHandle_preimage_bd (d := d) hseamAnn
  rw [Set.image_empty, Set.diff_empty] at htop
  rw [Set.image_empty, Set.diff_empty] at hsph
  refine Submodule.add_mem _ ((closedEmbeddingChain_mem_iff_preimage _ _ _).mpr ?_)
    ((closedEmbeddingChain_mem_iff_preimage _ _ _).mpr ?_)
  · exact subspaceChains_mono htop (3 + 1) (topSliceB_mem_topFace (s := s) (S := S) (hS := hS) (φ := φ) (hφ := hφ) (hφinj := hφinj) z)
  · exact subspaceChains_mono hsph (3 + 1) diskDetectChain_hc

variable (s t S hS φ hφ hφinj cd hseam)

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **NO DATUM SHOPPING.** `seamMatch` does not mention the surgered-end datum, and `∂W` is
`rfl`-equal across data (`bd_datum_indep`), so the `hseamMatch` obligation holds for one datum iff it
holds for all of them — the same rigidity `seamPreimage_datum_indep` records for the core. -/
theorem seamMatch_mem_datum_indep (d₁ d₂ : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)
    (z : cycles (TopCat.of s.M) (2 + 2)) :
    (seamMatch s S hS φ hφ hφinj z
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d₁).W) (3 + 1))
      ↔ (seamMatch s S hS φ hφ hφinj z
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d₂).W) (3 + 1)) := by
  rw [bd_datum_indep (s := s) (t := t) d₁ d₂]

variable {s t S hS φ hφ hφinj cd hseam}

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **WHERE `hseamHit` ACTUALLY LIVES.** With the attaching map landing in the top face, a seam point
never meets the source end, so the canonical core is nonempty **iff the surgered end fails to swallow
the whole seam**. That is a statement about the chart-determined `∂W` / `range eM'` — boundary-floor
territory — and by `seamPreimage_datum_indep` it is not a datum-level choice. -/
theorem seamCore_nonempty_iff_exists_offRange_eM' (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1) :
    (seamCore s t S hS φ hφ hφinj cd hseam d).Nonempty
      ↔ ∃ a : ↥S, seamPoint s S hS φ hφ hφinj a ∉ Set.range d.eM' := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun h => ha ((seamPoint_mem_bd_iff (d := d) hφtop a).mpr h)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun h => ha ((seamPoint_mem_bd_iff (d := d) hφtop a).mp h)⟩

/-! ## §6. TWO obligations — and the disk chain is NOT fixed -/

variable (s S hS φ hφ hφinj)

/-- **THE GLUED 5-CHAIN OVER A FREE DISK CHAIN.** The controlled cylinder representative (still
pinned to the fundamental class through `hz`, which is what supplies the cylinder-side detection)
glued to an ARBITRARY disk chain. At `cHa := diskDetectChain` this is `qZero`, definitionally. -/
def qGen (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)) :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 2) :=
  closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
      (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
    + closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
      (3 + 2) cHa

/-- **THE SEAM-MATCH CHAIN AT A FREE DISK CHAIN.** `seamMatch` is this at `cHa := diskDetectChain`
(definitionally). -/
def seamMatchGen (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)) :
    SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1) :=
  closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
      (3 + 1) (topSliceB s S hS φ hφ hφinj z)
    + closedEmbeddingChain
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
      (3 + 1) (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa)

variable (t cd hseam d)

variable {s S hS φ hφ hφinj} in
omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`∂(qGen)` COMPUTED, at a free disk chain** — the §1 identity with `diskDetectChain` replaced by
an arbitrary `cHa`. -/
theorem qGen_boundary_eq_seamMatchGen_add_botPush (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qGen s S hS φ hφ hφinj z cHa)
      = seamMatchGen s S hS φ hφ hφinj z cHa + botPush s S hS φ hφ hφinj z := by
  have hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
        (capstoneCylChainT s S hS φ hφ hφinj z)
      = topSliceB s S hS φ hφ hφinj z + ctrlBottom s S hS φ hφ hφinj z 0 :=
    chainBoundary_crossChain 3 (z : SingularChain (TopCat.of s.M) (3 + 1)) z.2
  rw [qGen, map_add, chainBoundary_closedEmbeddingChain, chainBoundary_closedEmbeddingChain, hbd,
    closedEmbeddingChain_add, seamMatchGen, botPush]
  abel

variable {s S hS φ hφ hφinj} in
omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE `↔` FOR THE TWO-OBLIGATION ROW'S `hbd`.** `qGen z cHa` is a relative cycle **iff** the
free-disk seam-match chain is a `∂W`-chain — the bottom face is free at every `cHa`. This is the form
an inhabiter should target: one membership, with the disk chain still to choose. -/
theorem qGen_boundary_mem_iff_seamMatchGen_mem (z : cycles (TopCat.of s.M) (2 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)) :
    (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (qGen s S hS φ hφ hφinj z cHa)
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
      ↔ (seamMatchGen s S hS φ hφ hφinj z cHa
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)) := by
  rw [qGen_boundary_eq_seamMatchGen_add_botPush z cHa]
  refine ⟨fun h => ?_, fun h => Submodule.add_mem _ h (botPush_mem_bd (d := d) z)⟩
  have := Submodule.add_mem _ h (botPush_mem_bd (d := d) z)
  rwa [add_assoc, ZModModule.add_self, add_zero] at this

/-- **THE TWO-OBLIGATION ROW — and the disk side is FREE.**

Two independent things happen here relative to `CollarPairSeamRow`:

1. **The anti-fake field disappears** — legitimately. `hseamHit` was needed only because the
   `CapstoneSeamCorrectorT` interface stores a corrector `p` and must guard against `p = 0`
   (round-13 gate spec 7). Firing the underlying engine `capstone_hasClass_ofCoreChains` directly
   supplies **no corrector at all**, so the guard has no premise. Nothing is evaded: the guard
   survives as a *theorem* about this row — `qGen_ne_zero_of_seamCore_nonempty` — rather than as a
   carried hypothesis.
2. **`cHa` is DATA, not the frozen `diskDetectChain`.** The disk-side rigidity recorded in
   `collar-pair-coarse-core-does-not-relax-the-disk-side` ("`diskDetectChain` is fixed") is an
   artifact of the *corrector interface*, whose `heS`/`hagree` fields name `diskDetectChain`
   literally. The engine underneath is general in both piece chains: any chain with a disk detecting
   triple (`hcHa` boundary-in-`∂D⁵`, `hdetHa` detection at every interior point) will do. An
   inhabiter may therefore adapt the disk chain to the cylinder side — a degree of freedom the row
   did not previously have.

Geometric obligations, exactly **TWO**: `hbd` (the glued chain is a relative cycle) and `hdetAB`
(seam straddle-detection). Nothing else. -/
structure CollarPairCoreRow where
  /-- a fundamental cycle of the closed source 4-manifold `M`. -/
  z : cycles (TopCat.of s.M) (2 + 2)
  /-- `z` represents THE fundamental class — the pin that supplies the cylinder-side detection. -/
  hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
    = Homology.mk (TopCat.of s.M) (2 + 2) z
  /-- **the disk-side chain — free data, no longer the frozen canonical one.** -/
  cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)
  /-- its boundary lies on the disk's boundary sphere `∂D⁵`. -/
  hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
    ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
        {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1)
  /-- it detects the local generator at every disk-interior point. -/
  hdetHa : ∀ (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}),
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) ({y}ᶜ) 3 cHa
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) hcHa) ≠ 0
  /-- **GEOMETRIC 1 — the glued chain is a relative cycle.** -/
  hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
      (qGen s S hS φ hφ hφinj z cHa)
    ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1)
  /-- **GEOMETRIC 2 — the seam straddle-detection atom.** -/
  hdetAB : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
      (qGen s S hS φ hφ hφinj z cHa)
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) hbd) ≠ 0

namespace CollarPairCoreRow

variable {s t S hS φ hφ hφinj cd hseam d}
variable (R : CollarPairCoreRow s t S hS φ hφ hφinj cd hseam d)

/-- **THE CAPSTONE `hasClass`, FROM TWO GEOMETRIC OBLIGATIONS.** The engine
`capstone_hasClass_ofCoreChains` fired directly: the controlled cylinder triple at `hz`, the row's
own disk triple, the two free boundary-absorbs, and the row's two obligations. No corrector, no
split, no bridge, no partition. -/
def toHasClass :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  capstone_hasClass_ofCoreChains s t S hS φ hφ hφinj cd hseam d
    (capstoneCylChainT s S hS φ hφ hφinj R.z) R.cHa R.hbd
    (capstone_habsorbB s t S hS φ hφ hφinj cd hseam d)
    (capstoneCylT_hc s S hS φ hφ hφinj R.z)
    (capstoneCylT_hdet s S hS φ hφ hφinj R.z R.hz)
    (capstone_habsorbHa s t S hS φ hφ hφinj cd hseam d)
    R.hcHa R.hdetHa R.hdetAB

omit [PreconnectedSpace s.M] in
/-- **THE ROUND-13 ANTI-FAKE GUARD, AS A THEOREM.** Nothing was evaded by dropping the corrector
interface's `nonzero_of_genuine` field: whenever the canonical core is nonempty — i.e. exactly under
`CollarPairSeamRow.hseamHit` — this row's glued chain is forced nonzero by its own detection
obligation. The guard is a *consequence* of the two obligations, never an extra assumption. -/
theorem qGen_ne_zero_of_seamCore_nonempty
    (h : (seamCore s t S hS φ hφ hφinj cd hseam d).Nonempty) :
    qGen s S hS φ hφ hφinj R.z R.cHa ≠ 0 := by
  obtain ⟨a, ha⟩ := h
  intro hzero
  refine R.hdetAB (seamPoint s S hS φ hφ hφinj a) ha
    ⟨φ a, (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a⟩ ⟨(a : D5), rfl⟩ ?_
  exact relClassOf_eq_zero_of_subspace (Set.empty_subset _) 3 (qGen s S hS φ hφ hφinj R.z R.cHa)
    (by rw [hzero]; exact Submodule.zero_mem _) _

end CollarPairCoreRow

variable {s t S hS φ hφ hφinj cd hseam d}

/-- **THE 3 → 2 PRODUCTION.** A seam row is a core row at the canonical disk chain: `qGen` at
`cHa := diskDetectChain` is `qZero` definitionally, the disk triple is the banked
`diskDetectChain_hc`/`_hdet`, and the seam row's two remaining obligations are the core row's two.
`hseamHit` is simply not needed by this route. -/
def CollarPairSeamRow.toCoreRow (R : CollarPairSeamRow s t S hS φ hφ hφinj cd hseam d) :
    CollarPairCoreRow s t S hS φ hφ hφinj cd hseam d where
  z := R.z
  hz := R.hz
  cHa := diskDetectChain
  hcHa := diskDetectChain_hc
  hdetHa := fun y hy => diskDetectChain_hdet y hy
  hbd := R.qZero_boundary_mem
  hdetAB := fun x hx hxA hxB => R.hq0det x hx hxA hxB _

omit [PreconnectedSpace s.M] in
/-- The 3 → 2 production at the level of inhabitation. -/
theorem nonempty_collarPairCoreRow_of_seamRow
    (h : Nonempty (CollarPairSeamRow s t S hS φ hφ hφinj cd hseam d)) :
    Nonempty (CollarPairCoreRow s t S hS φ hφ hφinj cd hseam d) :=
  ⟨CollarPairSeamRow.toCoreRow h.some⟩

end

end SKEFTHawking.PinPlusTraceCapstoneCollarPairMatch
