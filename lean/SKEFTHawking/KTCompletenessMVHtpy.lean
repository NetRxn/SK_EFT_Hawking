/-
# Phase 5q.H close-out — THE HOMOTOPY-RELAXATION ASSEMBLY: the finiteness-form MV datum.

**The relaxation (lead-endorsed architectural finding).** `CapstoneMVTransferRow`/`.ofPieces`
(`PinPlusTraceCapstoneMVPieces.lean`) discharge the four capstone cohomology finite-dimensionality
atoms from FOUR homeomorphisms of the constructed pieces onto standard comparison spaces — in
particular `eA : ↥(sub coverA) ≃ₜ (ktHandleAttachment …).B` and
`eB : ↥(sub coverB) ≃ₜ (ktHandleAttachment …).Ha`. Those two homeomorphism demands are
mathematically **over-strong**: the collar-thickened pieces `coverA = range fromCyl ∪ cd.seamNbhd`
and `coverB = range fromHandle ∪ cd.seamNbhd` PROPERLY contain the opposite half-collar sliver
(`cd.seamNbhd \ range fromCyl` is the handle-side of the collar), so they are homotopy-equivalent to
the closed ends — NOT homeomorphic to them. Since the pieces are not homeomorphic to `B`/`Ha`,
`.ofPieces` can never be instantiated for the real cover.

But the `CapstoneCohomologyMVDatum` fields `hA`/`hB` only ask for
`∀ n, FiniteDimensional (Homology (sub coverA) n)` — **finiteness**, which is a HOMOTOPY invariant
(`SingularHomologyFiniteTransfer.finiteDimensional_homology_of_homotopyEquiv`). This module supplies
the datum in that honest finiteness form: it takes `hA`/`hB` as the homotopy-invariant piece
finiteness (the correct, achievable form) and discharges the remaining two atoms GENERICALLY —
`hAB` through the banked collar overlap homeomorphism `eAB` and the overlap finiteness `hYAB`, and
`hBd` through the banked boundary two-closed-ends split `capstone_boundary_hBd` — for ARBITRARY
attachment data `(s, t, S, φ, cd, hseam, d)`.

## §-map
* **§1 — the overlap atom** `capstone_hAB`: `H_*(coverA ∩ coverB) < ∞` from the overlap finiteness
  `hYAB` transported across the banked collar homeo `eAB` (`≃ₜ WeldedCollarModel cd.A`).
* **§2 — the finiteness-form datum** `mvDatumOfPieceFiniteness`: the `CapstoneCohomologyMVDatum`
  built from the collar-thickened cover `coverA`/`coverB`/`hcov`, the homotopy-invariant piece
  finiteness `hA`/`hB`, and the overlap finiteness `hYAB` — with `hAB` (§1) and `hBd`
  (`capstone_boundary_hBd`, banked) discharged internally. The two homeomorphism demands `eA`/`eB`
  of `.ofPieces` are GONE, replaced by the weaker, geometrically-true finiteness demands `hA`/`hB`.
* **§3 — the four finite-dimensionality atoms** `findimAbs14/23_of_pieceFiniteness`,
  `findimRel14/23_of_pieceFiniteness`: the four `CapstoneAmbientSupply` cohomology
  finite-dimensionality atoms, generic over the attachment data, from exactly the piece finiteness
  `hA`/`hB` + the overlap finiteness `hYAB`.

**The residual floor.** After this module the four numeric atoms reduce to exactly three genuine
inputs: `hA`, `hB` (the piece finiteness — the homotopy-invariant relaxation of the false
homeomorphisms `eA`/`eB`) and `hYAB` (the overlap `WeldedCollarModel cd.A` finiteness, a genuine
geometric input since `cd.A` is an arbitrary charted 4-manifold). `hAB`, `hBd` are fully discharged.

**Fences.** THE COLLAR FORK is respected: the cover is `KTCompletenessMVCover`'s
`coverA`/`coverB` (the constructed handle-attachment's own `range fromCyl`/`range fromHandle`
structure, thickened by the GIVEN `cd.seamNbhd`), never a general collar theorem. Leaf-additive; no
existing module edited. The sealed heavy carrier term appears only in field/binder TYPES, never
re-elaborated inside a constructed term.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.KTCompletenessMVCover
import SKEFTHawking.KTCompletenessTransfer

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularHomologyFiniteTransfer
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCohomologyMV
open SKEFTHawking.PinPlusTraceCapstoneMVPieces
open SKEFTHawking.KTCompletenessMVCover
open SKEFTHawking.KTCompletenessTransfer

namespace SKEFTHawking.KTCompletenessMVHtpy

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M] [T2Space t.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §1. The overlap atom — `H_*(coverA ∩ coverB)` finiteness through the collar homeo. -/

omit [T2Space t.M] in
/-- **The overlap finiteness `hAB`, discharged through the collar homeomorphism.** The overlap
`coverA ∩ coverB` is the open seam collar (`coverA_inter_coverB`), presented as
`WeldedCollarModel cd.A` by the banked collar homeo `eAB`. So its all-degree homology finiteness
transfers from the overlap finiteness `hYAB` (the `WeldedCollarModel cd.A` finiteness — a genuine
geometric input, `cd.A` being an arbitrary charted 4-manifold). This is the `hAB` field of
`CapstoneCohomologyMVDatum`, discharged generically over the attachment data given `hYAB`. -/
theorem capstone_hAB
    (hYAB : ∀ n, FiniteDimensional (ZMod 2) (Homology (TopCat.of (WeldedCollarModel cd.A)) n))
    (n : ℕ) :
    FiniteDimensional (ZMod 2)
      (Homology (sub (coverA s t S hS φ hφ hφinj cd hseam d
        ∩ coverB s t S hS φ hφ hφinj cd hseam d)) n) :=
  finiteDimensional_homology_of_homeomorph (eAB s t S hS φ hφ hφinj cd hseam d) n (hYAB n)

/-! ## §2. The finiteness-form MV datum — the homotopy-invariant relaxation of `.ofPieces`. -/

/-- **The capstone cohomology MV datum, in the finiteness form.** Built from the collar-thickened
cover `coverA`/`coverB` (`KTCompletenessMVCover`) and its banked interior-cover `hcov`, with:
* `hA`/`hB` — the piece finiteness, taken as inputs. These are the HOMOTOPY-INVARIANT relaxation of
  the over-strong homeomorphism demands `eA`/`eB` of `CapstoneMVTransferRow.ofPieces` (which are
  geometrically false: the thickened pieces properly contain the opposite half-collar, so they are
  homotopy-equivalent — not homeomorphic — to the closed ends `B`/`Ha`);
* `hAB` — discharged from the overlap finiteness `hYAB` through the collar homeo (`capstone_hAB`, §1);
* `hBd` — discharged from the boundary two-closed-ends split (`capstone_boundary_hBd`, banked).

Generic over the attachment data. The whole datum — hence the four finite-dimensionality atoms
(§3) — now reduces to exactly `hA`, `hB` (piece finiteness) and `hYAB` (overlap finiteness). -/
def mvDatumOfPieceFiniteness
    (hA : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (sub (coverA s t S hS φ hφ hφinj cd hseam d)) n))
    (hB : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (sub (coverB s t S hS φ hφ hφinj cd hseam d)) n))
    (hYAB : ∀ n, FiniteDimensional (ZMod 2) (Homology (TopCat.of (WeldedCollarModel cd.A)) n)) :
    CapstoneCohomologyMVDatum s t S hS φ hφ hφinj cd hseam d where
  A := coverA s t S hS φ hφ hφinj cd hseam d
  B := coverB s t S hS φ hφ hφinj cd hseam d
  hcov := hcov s t S hS φ hφ hφinj cd hseam d
  hA := hA
  hB := hB
  hAB := capstone_hAB s t S hS φ hφ hφinj cd hseam d hYAB
  hBd := capstone_boundary_hBd s t S hS φ hφ hφinj cd hseam d

/-! ## §3. The four capstone cohomology finite-dimensionality atoms, from piece finiteness. -/

/-- **`findimAbs14` generic, from piece finiteness** — `H¹(W)` finite-dim for arbitrary attachment
data, from exactly the piece finiteness `hA`/`hB` and the overlap finiteness `hYAB`. -/
theorem findimAbs14_of_pieceFiniteness
    (hA : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (sub (coverA s t S hS φ hφ hφinj cd hseam d)) n))
    (hB : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (sub (coverB s t S hS φ hφ hφinj cd hseam d)) n))
    (hYAB : ∀ n, FiniteDimensional (ZMod 2) (Homology (TopCat.of (WeldedCollarModel cd.A)) n)) :
    FiniteDimensional (ZMod 2)
      (Cohomology (TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 1) :=
  (mvDatumOfPieceFiniteness s t S hS φ hφ hφinj cd hseam d hA hB hYAB).toFindimAbs14

/-- **`findimAbs23` generic, from piece finiteness** — `H²(W)` finite-dim for arbitrary attachment
data. -/
theorem findimAbs23_of_pieceFiniteness
    (hA : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (sub (coverA s t S hS φ hφ hφinj cd hseam d)) n))
    (hB : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (sub (coverB s t S hS φ hφ hφinj cd hseam d)) n))
    (hYAB : ∀ n, FiniteDimensional (ZMod 2) (Homology (TopCat.of (WeldedCollarModel cd.A)) n)) :
    FiniteDimensional (ZMod 2)
      (Cohomology (TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 2) :=
  (mvDatumOfPieceFiniteness s t S hS φ hφ hφinj cd hseam d hA hB hYAB).toFindimAbs23

/-- **`findimRel14` generic, from piece finiteness** — `H⁴(W,∂W)` finite-dim for arbitrary
attachment data. -/
theorem findimRel14_of_pieceFiniteness
    (hA : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (sub (coverA s t S hS φ hφ hφinj cd hseam d)) n))
    (hB : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (sub (coverB s t S hS φ hφ hφinj cd hseam d)) n))
    (hYAB : ∀ n, FiniteDimensional (ZMod 2) (Homology (TopCat.of (WeldedCollarModel cd.A)) n)) :
    FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 4) :=
  (mvDatumOfPieceFiniteness s t S hS φ hφ hφinj cd hseam d hA hB hYAB).toFindimRel14

/-- **`findimRel23` generic, from piece finiteness** — `H³(W,∂W)` finite-dim for arbitrary
attachment data. -/
theorem findimRel23_of_pieceFiniteness
    (hA : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (sub (coverA s t S hS φ hφ hφinj cd hseam d)) n))
    (hB : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (sub (coverB s t S hS φ hφ hφinj cd hseam d)) n))
    (hYAB : ∀ n, FiniteDimensional (ZMod 2) (Homology (TopCat.of (WeldedCollarModel cd.A)) n)) :
    FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 3) :=
  (mvDatumOfPieceFiniteness s t S hS φ hφ hφinj cd hseam d hA hB hYAB).toFindimRel23

end

end SKEFTHawking.KTCompletenessMVHtpy
