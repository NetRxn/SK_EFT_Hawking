/-
# Phase 5q.H W-D arm 4 — THE TRACE [W,∂W] REDUCED TO ITS EXISTENCE ATOM (residual-2's deepest field)

**Dimension discipline.** `W` = the 5-dimensional surgery trace bordism (`B ⊔_φ Ha`, the glued
adjunction carrier); `∂W = {M, M′}` are the 4-manifold ends; the membrane `Q` is 3-dimensional (not this
module's object). This module works the *deepest* field of the trace-W admissibility leaf row
(`TraceWAdmLeaves`, `PinPlusTraceWAdmPinned.lean`): the relative fundamental class
`relFund : RelFundClassDatum (X := TopCat.of b.W) (m := 3) (∂W)` — the Poincaré–Lefschetz duality of the
trace cobordism.

**The reduction (THE COLLAR FORK, explicit-collar specialization).** The binding ruling is that a
CONSTRUCTED `W` carries its `[W,∂W]` data BY CONSTRUCTION (the provider pattern); the general
collar-neighbourhood theorem is a deferred non-critical slice, NOT attempted here. The carrier-agnostic
`PoincareLefschetzRelFundClassGeom.relFundClassDatumOf` is exactly the provider hook: for ANY charted
`W` with the trace's tangent model `(𝓡 4).prod (𝓡∂ 1)` (`= cylModel 2` definitionally, so the canonical
interior-chart identification `ε : E⁴ × E¹ ≃L E⁵` is the reused `EuclideanSpace.finAddEquivProd`), it
assembles the full `RelFundClassDatum` from the CANONICAL interior generator family
(`interiorGenFamily`) plus a single **existence witness** `HasRelFundClass` (the relative Hatcher-3.27(b)
MV-cover existence obligation). The generator family is no longer a carried field — it is constructed
from the model + `ε` — so the whole datum reduces to exactly the existence atom, plus the per-object
`T1Space b.W` separation certificate (bordism carriers are NOT T1 in general — `KernelNoGos` — so it is
carried, exactly as `TraceMembraneLeaves` carries the `T2Space` certificate `hWT2`).

`TraceRelFundLeaves b` bundles those two atoms; `toRelFundClassDatum` discharges the full
`RelFundClassDatum` from them; `TraceWAdmLeaves.ofRelFundLeaves` rebuilds the residual-2 leaf row with
its deepest field `relFund` supplied by the reduced row — so the trace-W admissibility seam visibly
narrows: its Poincaré–Lefschetz field bottoms out in {a T1 certificate, the class-existence witness},
with the interior generators canonically constructed. Neither atom is a completeness/bounding Prop: the
existence witness is the honest relative-Hatcher MV residual, and the T1 certificate is a separation
fact about the constructed carrier.

**Fences respected.** No general collar theorem is attempted (the ruled-out fork of THE COLLAR FORK).
`ε` is the canonical `finAddEquivProd` (no free basis gauge). The reduction is carrier-agnostic through
`relFundClassDatumOf`, so it never assumes the trace carrier is a cylinder — it only reuses the cylinder
model's canonical interior-chart identification, which the trace shares by tangent-model equality.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceWAdmPinned
import SKEFTHawking.PoincareLefschetzRelFundClassGeom

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2

namespace SKEFTHawking.PinPlusTraceRelFundReduce

noncomputable section

variable {s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)}

/-- **The canonical trace interior-chart linear equiv** `E⁴ × E¹ ≃L E⁵` — the `ε` the interior
generator family consumes for the 5-dim trace model `(𝓡 4).prod (𝓡∂ 1)` (whose vector space is
`EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)`). This is `EuclideanSpace.finAddEquivProd`
inverted — canonical, no free basis choice. `Fin (4 + 1) = Fin (3 + 2)` definitionally (both `Fin 5`,
the trace top degree). -/
def εtrace : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
    EuclideanSpace ℝ (Fin (3 + 2)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 4) (m := 1)).symm

/-- **The trace relative-fundamental-class leaf row.** Bundles the two atoms the carrier-agnostic
provider `relFundClassDatumOf` reduces `[W,∂W]` to: the per-object `T1Space b.W` separation certificate
(bordism carriers are NOT T1 in general — carried, like `TraceMembraneLeaves.hWT2`), and the single
existence witness `hasClass : HasRelFundClass (∂W) (interiorGenFamily …)` — the relative Hatcher-3.27(b)
MV-cover existence obligation for the CANONICAL interior generator family. The generator family is
constructed (from the trace model + the canonical `εtrace`), not a carried field. Neither field is a
completeness Prop. -/
structure TraceRelFundLeaves (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) s t) where
  /-- **per-object certificate**: the trace carrier `W = b.W` is T1 (separation for the local-homology
  interior-chart machinery; bordism carriers are not T1 in general, so this is carried). -/
  hWT1 : T1Space b.W
  /-- **the class-existence atom**: `[W,∂W]` exists restricting to the canonical interior generator
  family (the relative Hatcher-3.27(b) MV-cover existence obligation of the trace pair). -/
  hasClass :
    letI := hWT1
    HasRelFundClass (X := TopCat.of b.W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary b.W)
      (interiorGenFamily (W := b.W) ((𝓡 4).prod (𝓡∂ 1)) εtrace)

/-- **The trace relFund leaf row discharges the full `RelFundClassDatum`.** Feeds the reduced row
through the carrier-agnostic provider `relFundClassDatumOf` (canonical `εtrace`): the class is
`hasClass.choose`, the generator family is the constructed `interiorGenFamily`, and the restriction is
`hasClass.choose_spec`. This is the kernel-checked reduction — `relFund` inhabited from exactly {T1
certificate, existence witness}. -/
def TraceRelFundLeaves.toRelFundClassDatum {b : Bordism ((𝓡 4).prod (𝓡∂ 1)) s t}
    (d : TraceRelFundLeaves b) :
    RelFundClassDatum (X := TopCat.of b.W) (m := 3) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) :=
  letI := d.hWT1
  relFundClassDatumOf (W := b.W) ((𝓡 4).prod (𝓡∂ 1)) εtrace d.hasClass

/-- **The residual-2 leaf row rebuilt with its deepest field reduced.** Assembles a full
`TraceWAdmLeaves b` with the relative fundamental-class field `relFund` supplied by the reduced row
`rf` (`= rf.toRelFundClassDatum`), and the remaining finiteness / Lefschetz-non-degeneracy / Betti /
Wu-vanishing atoms as before. This is the visible seam narrowing: the trace-W admissibility's Poincaré–
Lefschetz field no longer floats as a raw `RelFundClassDatum` — it bottoms out in the T1 certificate +
the class-existence witness of `TraceRelFundLeaves`, with the interior generators canonically
constructed. The numerics fields (`findim…`, `dimeq…`) are the compact-manifold Betti atoms; the
`nondeg…`/`hwu` are the Poincaré–Lefschetz non-degeneracies and the pin⁺ spin condition, now stated
against the reduced datum's `mu`. -/
def TraceWAdmLeaves.ofRelFundLeaves {b : Bordism ((𝓡 4).prod (𝓡∂ 1)) s t}
    (rf : TraceRelFundLeaves b)
    (findimAbs14 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of b.W) 1))
    (findimRel14 : FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4))
    (nondeg14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of b.W) (S := ((𝓡 4).prod (𝓡∂ 1)).boundary b.W)).compr₂
        rf.toRelFundClassDatum.mu))
    (dimeq14 : Module.finrank (ZMod 2) (Cohomology (TopCat.of b.W) 1)
             = Module.finrank (ZMod 2)
               (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4))
    (findimAbs23 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of b.W) 2))
    (findimRel23 : FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 3))
    (nondeg23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of b.W) (S := ((𝓡 4).prod (𝓡∂ 1)).boundary b.W)).compr₂
        rf.toRelFundClassDatum.mu))
    (dimeq23 : Module.finrank (ZMod 2) (Cohomology (TopCat.of b.W) 2)
             = Module.finrank (ZMod 2)
               (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 3))
    (hwu : wuW2
        (LefschetzWuDatum.ofRelFund14 rf.toRelFundClassDatum findimAbs14 findimRel14 nondeg14 dimeq14)
        (LefschetzWuDatum.ofRelFund23 rf.toRelFundClassDatum findimAbs23 findimRel23 nondeg23 dimeq23)
      = 0) :
    TraceWAdmLeaves b where
  relFund := rf.toRelFundClassDatum
  findimAbs14 := findimAbs14
  findimRel14 := findimRel14
  nondeg14 := nondeg14
  dimeq14 := dimeq14
  findimAbs23 := findimAbs23
  findimRel23 := findimRel23
  nondeg23 := nondeg23
  dimeq23 := dimeq23
  hwu := hwu

/-- **The KRS-consumer W-admissibility datum from the reduced relFund row.** The headline seam
narrowing: the pinned `WAdmPinned b` the weld consumers (`borTetheredOfWeld`,
`ambientSurgeryDatum_of_weld`, `dataBordant_of_traceBor`) require on top of the packaged
`surgeryTraceBordism` is produced from the reduced relative-fundamental-class row `rf`
(`TraceRelFundLeaves` — T1 certificate + class-existence witness, canonical interior generators) plus
the compact-manifold Betti/non-degeneracy/spin numerics. Composes `ofRelFundLeaves` with the residual-2
opener's `TraceWAdmLeaves.toWAdmPinned`. The trace-W admissibility's deepest input `[W,∂W]` no longer
enters as a raw datum — it enters as the existence atom of `TraceRelFundLeaves`. -/
def traceWAdmPinned_ofRelFundLeaves {b : Bordism ((𝓡 4).prod (𝓡∂ 1)) s t}
    (rf : TraceRelFundLeaves b)
    (findimAbs14 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of b.W) 1))
    (findimRel14 : FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4))
    (nondeg14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of b.W) (S := ((𝓡 4).prod (𝓡∂ 1)).boundary b.W)).compr₂
        rf.toRelFundClassDatum.mu))
    (dimeq14 : Module.finrank (ZMod 2) (Cohomology (TopCat.of b.W) 1)
             = Module.finrank (ZMod 2)
               (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4))
    (findimAbs23 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of b.W) 2))
    (findimRel23 : FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 3))
    (nondeg23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of b.W) (S := ((𝓡 4).prod (𝓡∂ 1)).boundary b.W)).compr₂
        rf.toRelFundClassDatum.mu))
    (dimeq23 : Module.finrank (ZMod 2) (Cohomology (TopCat.of b.W) 2)
             = Module.finrank (ZMod 2)
               (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 3))
    (hwu : wuW2
        (LefschetzWuDatum.ofRelFund14 rf.toRelFundClassDatum findimAbs14 findimRel14 nondeg14 dimeq14)
        (LefschetzWuDatum.ofRelFund23 rf.toRelFundClassDatum findimAbs23 findimRel23 nondeg23 dimeq23)
      = 0) :
    WAdmPinned b :=
  (TraceWAdmLeaves.ofRelFundLeaves rf findimAbs14 findimRel14 nondeg14 dimeq14
    findimAbs23 findimRel23 nondeg23 dimeq23 hwu).toWAdmPinned

end

end SKEFTHawking.PinPlusTraceRelFundReduce
