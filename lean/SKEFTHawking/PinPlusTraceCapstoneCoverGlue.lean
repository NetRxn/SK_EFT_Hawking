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

end

end SKEFTHawking.PinPlusTraceCapstoneCoverGlue
