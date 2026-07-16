/-
# Phase 5q.H W-A arm 4 — THE TRACE-W ADMISSIBILITY OPENER (surgery-foundation wave-4 residual 2)

**Dimension discipline.** `W` = the 5-dimensional surgery trace bordism (`B ⊔_φ Ha`, the adjunction
space of `SingularSurgeryFoundation.lean`); `∂W = M ⊔ M′` are 4-manifolds; the surgered membrane
`Σ/Q` is 3-dimensional; the handle `Ha` models `D⁵` on `KTModel = E⁴ × H¹`, the attaching sphere
`S ⊆ D⁵`. This file supplies the *W-admissibility* datum `WAdmPinned` on the trace pair `(W, ∂W)`
that the KRS-supply consumption chain (`borTetheredOfWeld`, `ambientSurgeryDatum_of_weld`,
`dataBordant_of_traceBor`) needs on top of the already-packaged `surgeryTraceBordism`.

**The generic reduction (§1).** Until now a `WAdmPinned b` was produced only for cylinders
(`CylinderWAdmPinned`, `PinPlusCharPairWProviderTransport`) and their disjoint sums
(`WAdmPinned.add`, `sumRelFundClass`). The disjoint-union `SumRelFundClass` machinery assembles the
relative fundamental class of a **disjoint** union `A ⊔ B`; the trace carrier is a **glued**
adjunction space `B ⊔_φ Ha`, so `add` does not reach it. `WAdmPinned.ofRelFund` is the honest
carrier-agnostic constructor: it takes the Poincaré–Lefschetz **leaf row** for ANY bordism `b` —
one relative fundamental-class datum `[W,∂W]`, the two absolute/relative finite-dimensionalities per
degree pair, the two Lefschetz non-degeneracies, the two Betti equalities, and the Wu vanishing
`w₂(W)=0` — and assembles `WAdmPinned b` via the substrate `ofRelFund14/23` + their pins
(`ofRelFund14_pinned/ofRelFund23_pinned`). Each hypothesis is a genuine geometric atom (a rel-fund
class, a finiteness, a duality non-degeneracy, a Betti identity, a spin condition), NOT a
completeness/bounding Prop. It reuses the pinned certificates verbatim, so no free-`sqOp` gauge is
introduced (`wadm_sqop_gauge_w2_filter_vacuous` fence respected: the pins are the substrate ones).

**The trace leaf-row (§2).** `TraceWAdmLeaves b` bundles exactly the §1 hypotheses for a bordism
`b` (here instantiated at the trace carrier); `TraceWAdmLeaves.toWAdmPinned` discharges
`WAdmPinned b` from it. This is the "strictly-smaller named leaf row" the opener reduces the trace
pair to: the deep residual is the single relative fundamental class of the surgery trace (the
Poincaré–Lefschetz duality of the trace cobordism) plus the pin⁺ spin condition `w₂ = 0`; the
finiteness/Betti atoms are the compact-manifold numerics. None is a new deep arc dissolved here —
they are the honest geometric content, left as typed leaves for the downstream duality tower.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusWAdmPinnedCore

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.PinPlusCharPairData

namespace SKEFTHawking.PinPlusWAdmPinned

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-! ## §1. The carrier-agnostic `ofRelFund` constructor for `WAdmPinned`.

For ANY bordism `b : Bordism (I.prod (𝓡∂ 1)) s t` (carrier `W = b.W`, boundary `∂W`), a pinned
W-admissibility datum is assembled from the Poincaré–Lefschetz leaf row of the pair `(W, ∂W)`. This
is the trace-reaching generalisation of the cylinder/disjoint-union constructors: it is agnostic to
the carrier's homeomorphism type, so it applies verbatim to the glued surgery-trace carrier. -/

/-- **The carrier-agnostic pinned W-admissibility constructor.** Given a bordism `b` and the leaf
row for the pair `(b.W, ∂b.W)` — one relative fundamental-class datum `D` (`[W,∂W]`), the `(1,4)`
and `(2,3)` absolute/relative finite-dimensionalities, Lefschetz non-degeneracies and Betti
equalities, and the Wu vanishing `wuW2 = 0` — produces `WAdmPinned b`. The two Lefschetz–Wu data
are the substrate `ofRelFund14/23` assemblies (so `cup := relCupH14/23`, `sqOp := relSq1/2`,
`μ := D.mu` are all pinned to the substrate), and their pins are the generic non-vacuity
certificates `ofRelFund14_pinned/ofRelFund23_pinned`. -/
def WAdmPinned.ofRelFund {s t : SingularManifold PUnit k I}
    (b : Bordism (I.prod (𝓡∂ 1)) s t)
    (D : RelFundClassDatum (X := TopCat.of b.W) (m := 3) ((I.prod (𝓡∂ 1)).boundary b.W))
    (findimAbs14 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of b.W) 1))
    (findimRel14 : FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 4))
    (nondeg14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of b.W) (S := (I.prod (𝓡∂ 1)).boundary b.W)).compr₂ D.mu))
    (dimeq14 : Module.finrank (ZMod 2) (Cohomology (TopCat.of b.W) 1)
             = Module.finrank (ZMod 2)
               (RelativeCohomology (X := TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 4))
    (findimAbs23 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of b.W) 2))
    (findimRel23 : FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 3))
    (nondeg23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of b.W) (S := (I.prod (𝓡∂ 1)).boundary b.W)).compr₂ D.mu))
    (dimeq23 : Module.finrank (ZMod 2) (Cohomology (TopCat.of b.W) 2)
             = Module.finrank (ZMod 2)
               (RelativeCohomology (X := TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 3))
    (hwu : wuW2 (LefschetzWuDatum.ofRelFund14 D findimAbs14 findimRel14 nondeg14 dimeq14)
                (LefschetzWuDatum.ofRelFund23 D findimAbs23 findimRel23 nondeg23 dimeq23) = 0) :
    WAdmPinned b where
  wadm :=
    { P14 := LefschetzWuDatum.ofRelFund14 D findimAbs14 findimRel14 nondeg14 dimeq14
      P23 := LefschetzWuDatum.ofRelFund23 D findimAbs23 findimRel23 nondeg23 dimeq23
      hwu := hwu }
  pin14 := ofRelFund14_pinned D findimAbs14 findimRel14 nondeg14 dimeq14
  pin23 := ofRelFund23_pinned D findimAbs23 findimRel23 nondeg23 dimeq23

/-! ## §2. The trace leaf-row bundle `TraceWAdmLeaves` and its discharge.

`TraceWAdmLeaves b` bundles exactly the §1 leaf row into a single named type — the "strictly-smaller
named leaf row" the trace opener reduces the W-admissibility obligation to. It mirrors the
`CylWAdmData`/`CylinderWAdmPinned` residual-set idiom (one structure whose fields are the honest
open geometric atoms, all derived data below). For the surgery-trace pair the deep residual is the
single relative fundamental-class field `relFund` (the Poincaré–Lefschetz duality of the trace
cobordism `W = B ⊔_φ Ha`); the finiteness/Betti fields are the compact-manifold numerics; `hwu` is
the pin⁺ spin condition `w₂(W)=0`. No field is a completeness/bounding Prop. -/

/-- **The trace-pair W-admissibility leaf row.** Bundles the Poincaré–Lefschetz atoms that
`WAdmPinned.ofRelFund` consumes for a bordism `b` (here the 5-dim surgery-trace carrier `W = b.W`,
`∂W = M ⊔ M′`): the relative fundamental class `[W,∂W]` (`relFund`), the `(1,4)`/`(2,3)` absolute and
relative finite-dimensionalities, the two Lefschetz non-degeneracies, the two Betti equalities, and
the Wu vanishing `wuW2 = 0`. Each field is a genuine geometric atom. -/
structure TraceWAdmLeaves {s t : SingularManifold PUnit k I}
    (b : Bordism (I.prod (𝓡∂ 1)) s t) where
  /-- The relative fundamental class `[W,∂W]` of the trace pair (the deep PL-duality residual). -/
  relFund : RelFundClassDatum (X := TopCat.of b.W) (m := 3) ((I.prod (𝓡∂ 1)).boundary b.W)
  /-- `H¹(W;ℤ/2)` finite-dimensional. -/
  findimAbs14 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of b.W) 1)
  /-- `H⁴(W,∂W;ℤ/2)` finite-dimensional. -/
  findimRel14 : FiniteDimensional (ZMod 2)
    (RelativeCohomology (X := TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 4)
  /-- `(1,4)` Lefschetz non-degeneracy (Poincaré–Lefschetz duality of the trace). -/
  nondeg14 : Function.Injective
    ⇑((relCupH14 (X := TopCat.of b.W) (S := (I.prod (𝓡∂ 1)).boundary b.W)).compr₂ relFund.mu)
  /-- `(1,4)` Betti equality `dim H¹(W) = dim H⁴(W,∂W)`. -/
  dimeq14 : Module.finrank (ZMod 2) (Cohomology (TopCat.of b.W) 1)
          = Module.finrank (ZMod 2)
            (RelativeCohomology (X := TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 4)
  /-- `H²(W;ℤ/2)` finite-dimensional. -/
  findimAbs23 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of b.W) 2)
  /-- `H³(W,∂W;ℤ/2)` finite-dimensional. -/
  findimRel23 : FiniteDimensional (ZMod 2)
    (RelativeCohomology (X := TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 3)
  /-- `(2,3)` Lefschetz non-degeneracy. -/
  nondeg23 : Function.Injective
    ⇑((relCupH23 (X := TopCat.of b.W) (S := (I.prod (𝓡∂ 1)).boundary b.W)).compr₂ relFund.mu)
  /-- `(2,3)` Betti equality `dim H²(W) = dim H³(W,∂W)`. -/
  dimeq23 : Module.finrank (ZMod 2) (Cohomology (TopCat.of b.W) 2)
          = Module.finrank (ZMod 2)
            (RelativeCohomology (X := TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 3)
  /-- The Wu obstruction vanishes `wuW2 P14 P23 = 0` (`w₂(W) = 0`, the pin⁺ spin condition). -/
  hwu : wuW2 (LefschetzWuDatum.ofRelFund14 relFund findimAbs14 findimRel14 nondeg14 dimeq14)
             (LefschetzWuDatum.ofRelFund23 relFund findimAbs23 findimRel23 nondeg23 dimeq23) = 0

/-- **The trace leaf-row discharges `WAdmPinned`.** Feeding `TraceWAdmLeaves b` through the
carrier-agnostic `WAdmPinned.ofRelFund` produces the pinned W-admissibility datum on `b`. This is
the opener's headline: `WAdmPinned` on the trace pair is inhabited from — and only from — the named
geometric leaf row. -/
def TraceWAdmLeaves.toWAdmPinned {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} (d : TraceWAdmLeaves b) : WAdmPinned b :=
  WAdmPinned.ofRelFund b d.relFund d.findimAbs14 d.findimRel14 d.nondeg14 d.dimeq14
    d.findimAbs23 d.findimRel23 d.nondeg23 d.dimeq23 d.hwu

end

/-! ## §3. The consumer-grade specialization (`I := 𝓡 4`, `k := 0`).

The KRS-supply consumers (`borTetheredOfWeld`, `ambientSurgeryDatum_of_weld`, `dataBordant_of_traceBor`)
take `WAdmPinned b` on a trace bordism `b : Bordism ((𝓡 4).prod (𝓡∂ 1)) s t` between closed singular
`𝓡 4`-manifolds at `k = 0` (the C⁰ collapse — all smoothness fields free). This section pins the opener
at that exact grade, confirming the `EuclideanSpace ℝ (Fin (2+2)) = EuclideanSpace ℝ (Fin 4)` model
instantiation and giving the consumers a directly-applicable hook. -/

noncomputable section

/-- **The trace opener at the KRS-consumer grade.** For a surgery-trace bordism `b` between closed
singular `𝓡 4`-manifolds (`k = 0`), the trace leaf row discharges the pinned W-admissibility datum
`WAdmPinned b`. `W = b.W` is the 5-dim trace carrier `B ⊔_φ Ha`; `∂W = M ⊔ M′` are 4-manifolds. This
is the datum both weld consumers require on top of the packaged `surgeryTraceBordism`. -/
def traceWAdmPinned {s t : SingularManifold PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)}
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) s t) (d : TraceWAdmLeaves b) : WAdmPinned b :=
  d.toWAdmPinned

end

end SKEFTHawking.PinPlusWAdmPinned
