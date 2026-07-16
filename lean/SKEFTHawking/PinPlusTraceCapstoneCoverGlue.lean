/-
# Phase 5q.H close-out — THE CAPSTONE `hasClass` FROM THE RELATIVE COVER-MV GLUE (the honest route)

The binary-partition route to the capstone's `[W,∂W]` existence witness is ROUTE-BANNED
(`capstone-binary-partition-detection-uninhabitable`, SETTLED_FORKS 2026-07-16): a complementary set
partition of the CONNECTED capstone always leaves seam points on the closed piece's frontier, where
the piece's boundary-face local homology kills the detection for EVERY class. The live route is the
**relative cover-MV gluing** (`SingularRelativeCoverMV.lean`): the class is glued at the CHAIN level
from two core-supported chains whose seam boundary terms cancel mod 2 in the sum — the Mayer–Vietoris
connecting-map bookkeeping, where "the two pieces agree on the overlap" genuinely lives.

**Why this evades the ban (categorically different route).** The banned engine pushed per-piece PAIR
classes `H₅(piece, ∂W∩piece)` into the ambient and demanded detection on ALL of a closed piece —
false at the frontier. Here no per-piece pair class exists at all (for a proper piece of a connected
`W` that group is degenerate — see the gluing module's header); the glue datum carries CHAINS, the
one-sided detections are demanded only OFF the other core (`x ∉ CB` keeps `x` away from `CA`'s
frontier when the cores overlap on a collar block), and the overlap zone carries its own straddle
detection, dischargeable from a collar product chain via `relClassOf_eq_of_congr`.

**The supplier (§1).** `capstone_hasClass_of_glueData` fires the generic
`RelCoverGlueData.hasRelFundClass_of_glueData` at `X := TopCat.of W`, `S := ∂W`,
`gen := interiorGenFamily … εtrace`, `m := 3` — producing the EXACT
`CapstoneAmbientSupply.hasClass` field type (equivalently the `hasClass` argument of
`TraceRelFundLeaves.ofCapstone`). **The datum row (§2).** `CapstoneRelFundCoverDatum` bundles the
glue datum (cores, chains, seam-cancellation) with the three per-zone local nonvanishing facts —
each an honest local fact about a concrete chain (the cyl-side chain's local class off the handle
core, the handle-side chain's off the cyl core, the glued chain's on the overlap), never a
completeness Prop and never a detection at a closed piece's frontier. `.toHasClass` assembles it.

**Fences.** THE COLLAR FORK is respected: no general collar theorem — the intended cores are the
constructed carrier's own `range fromCyl`/`range fromHandle` (closed by
`isClosedEmbedding_fromCyl/fromHandle`, covering by `range_fromCyl_union_range_fromHandle`), and the
overlap chain is whatever concrete collar chain the SeamCollarDatum-side construction supplies BY
CONSTRUCTION. `εtrace` is the canonical `finAddEquivProd`. The sealed `capstoneB` term is never
re-elaborated with explicit heavy arguments; all statements copy the partition file's guarded
spelling.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryTraceCapstone
import SKEFTHawking.PinPlusTraceRelFundReduce
import SKEFTHawking.PinPlusTraceCapstoneInhabit
import SKEFTHawking.SingularRelativeCoverMV
import SKEFTHawking.SingularSurgeryCoreDetect

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit

namespace SKEFTHawking.PinPlusTraceCapstoneCoverGlue

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §1. The capstone `hasClass` supplier from a cover-glue datum. -/

/-- **The capstone `hasClass` per-atom supplier — the relative cover-MV glue.** Fires the generic
chain-level glue (`RelCoverGlueData.hasRelFundClass_of_glueData`) at `X := TopCat.of W`,
`S := ∂W`, `gen := interiorGenFamily … εtrace`, `m := 3` — producing the exact
`CapstoneAmbientSupply.hasClass` field (equivalently the `hasClass` argument of
`TraceRelFundLeaves.ofCapstone`). The inputs are the glue datum `D` (two closed cores covering `W`,
two core-supported chains, the mod-2 seam-cancellation) and the three per-zone local nonvanishing
facts. No detection is ever demanded at a closed piece's frontier: the one-sided zones carry
`x ∉ other core`, and the overlap zone's straddle detection reduces to a collar product chain via
`relClassOf_eq_of_congr` — the honest chain-level "agreement on the overlap". -/
def capstone_hasClass_of_glueData
    (D : RelCoverGlueData
      (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 3)
    (hdetA : ∀ (x : ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
      (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
      (hxB : x ∉ D.CB),
      relClassOf ({x}ᶜ) 3 D.cA (D.hbdA_local hx hxB) ≠ 0)
    (hdetB : ∀ (x : ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
      (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
      (hxA : x ∉ D.CA),
      relClassOf ({x}ᶜ) 3 D.cB (D.hbdB_local hx hxA) ≠ 0)
    (hdetAB : ∀ (x : ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
      (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
      x ∈ D.CA → x ∈ D.CB →
      relClassOf ({x}ᶜ) 3 (D.cA + D.cB)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) D.hbd) ≠ 0) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
  D.hasRelFundClass_of_glueData
    (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      ((𝓡 4).prod (𝓡∂ 1)) εtrace) hdetA hdetB hdetAB

/-! ## §2. The cover-glue datum row — the honest reduction of the deepest atom. -/

/-- **The capstone cover-glue detection row** — the honest named sub-reduction of the deepest
`CapstoneAmbientSupply` atom via the relative cover-MV glue, bundled as one geometric object (the
arm's datum discipline). Carries the chain-level glue datum `D` (two closed cores covering `W`, two
core-supported chains, the mod-2 seam-cancellation — the MV "agreement on the overlap") and the
three per-zone local nonvanishing facts. Each field is a genuine geometric residual about a concrete
chain; none is a completeness Prop, and no field demands detection at a closed piece's frontier (the
structural falsity that killed the partition route). `toHasClass` fires the glue to supply the exact
`CapstoneAmbientSupply.hasClass` field — so the deepest atom is replaced by this transparent row. -/
structure CapstoneRelFundCoverDatum where
  /-- the chain-level cover-glue datum: cores `CA`/`CB` (intended: `range fromCyl`/`range
  fromHandle`), core-supported chains `cA`/`cB`, and the seam-cancellation `hbd`. -/
  D : RelCoverGlueData
    (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
    (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 3
  /-- the cyl-side chain's local class is nonzero at every interior point off the handle core. -/
  hdetA : ∀ (x : ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
    (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
    (hxB : x ∉ D.CB),
    relClassOf ({x}ᶜ) 3 D.cA (D.hbdA_local hx hxB) ≠ 0
  /-- the handle-side chain's local class is nonzero at every interior point off the cyl core. -/
  hdetB : ∀ (x : ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
    (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
    (hxA : x ∉ D.CA),
    relClassOf ({x}ᶜ) 3 D.cB (D.hbdB_local hx hxA) ≠ 0
  /-- the glued chain's local class is nonzero on the overlap zone (the straddle detection —
  dischargeable from a collar product chain via `relClassOf_eq_of_congr`). -/
  hdetAB : ∀ (x : ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
    (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
    x ∈ D.CA → x ∈ D.CB →
    relClassOf ({x}ᶜ) 3 (D.cA + D.cB)
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) D.hbd) ≠ 0

/-- **The cover-glue datum row supplies the capstone `hasClass` field.** Projects the row and fires
`capstone_hasClass_of_glueData` — producing the exact type of `CapstoneAmbientSupply.hasClass` (and
of the `hasClass` argument of `TraceRelFundLeaves.ofCapstone`), so the datum drops in directly as
the `hasClass` atom. -/
def CapstoneRelFundCoverDatum.toHasClass
    (R : CapstoneRelFundCoverDatum s t S hS φ hφ hφinj cd hseam d) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  capstone_hasClass_of_glueData s t S hS φ hφ hφinj cd hseam d R.D R.hdetA R.hdetB R.hdetAB

/-! ## §3. The capstone `hasClass` from the two core chains — the one-sided detections discharged.

The final narrowing of this arm: firing the handle-attachment-level two-core assembly
(`SingularSurgeryCoreDetect.hasRelFundClass_of_coreChains`) at the capstone's boundary set and
canonical interior generator family. The capstone's `hasClass` atom is thereby reduced to exactly
FOUR named geometric residuals on the two piece chains: the two boundary-absorb facts (`∂W ∪` the
other core absorbs each piece's boundary support — boundary bookkeeping from the `SurgeredEndDatum`
decomposition), the two piece supports/intrinsic detections (the cylinder side SUPPLIED by
`exists_cylinder_detecting_chain` for connected `s.M`; the `D⁵` side the open disk-chain atom), the
mod-2 seam-cancellation `hbd` (the degree-4 overlap agreement, chain level), and the overlap-zone
straddle detection `hdetAB` (dischargeable from a collar product chain via
`relClassOf_eq_of_congr`). The one-sided detection fields of the datum row are DISCHARGED. -/

/-- **The capstone `hasClass` from the two core chains.** The exact
`CapstoneAmbientSupply.hasClass` field type, produced from the two piece chains and the four named
residual atoms — the cover-glue route with both one-sided detections discharged by the core
suppliers. -/
def capstone_hasClass_ofCoreChains
    (cCyl : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 2))
    (cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2))
    (hbd : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
        (closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
            (3 + 2) cCyl
          + closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
            (3 + 2) cHa)
      ∈ subspaceChains
          (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (3 + 1))
    {BdB : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B}
    (habsorbB : ∀ y ∈ BdB, (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl y
      ∈ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ∪ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)
    (hcCyl : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1) cCyl
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) BdB (3 + 1))
    (hdetCyl : ∀ (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (hy : y ∉ BdB),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) ({y}ᶜ) 3 cCyl
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) hcCyl) ≠ 0)
    {BdHa : Set (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha}
    (habsorbHa : ∀ y ∈ BdHa, (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle y
      ∈ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ∪ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)
    (hcHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) BdHa (3 + 1))
    (hdetHa : ∀ (y : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (hy : y ∉ BdHa),
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) ({y}ᶜ) 3 cHa
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1) hcHa) ≠ 0)
    (hdetAB : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
      relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
        (closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
            (3 + 2) cCyl
          + closedEmbeddingChain
            (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
            (3 + 2) cHa)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1) hbd) ≠ 0) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
  SKEFTHawking.SingularSurgeryCoreDetect.hasRelFundClass_of_coreChains
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj)
    (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 3
    (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      ((𝓡 4).prod (𝓡∂ 1)) εtrace)
    cCyl cHa hbd habsorbB hcCyl hdetCyl habsorbHa hcHa hdetHa hdetAB

end

end SKEFTHawking.PinPlusTraceCapstoneCoverGlue
