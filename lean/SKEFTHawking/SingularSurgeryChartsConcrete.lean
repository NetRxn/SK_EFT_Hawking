/-
# Phase 5q.H W-D — SURGERY WAVE 6: THE ChartedSpace FLOOR (the concrete cylinder end)

Wave 5 (`SingularSurgeryDatumC0.lean`) made the whole smoothness/weld stack FREE at `k = 0`:
`SmoothSurgeryChartDatum.ofC0` builds a Wave-3 `SmoothSurgeryChartDatum` from a bare Wave-2
`SurgeryChartDatum` (the `ChartedSpace` floor) plus a tangent model `J`. So feeding the Pin⁺ consumer's
`AmbientSurgeryDatum.b` (a `Bordism ((𝓡 4).prod (𝓡∂ 1)) …`) reduces to supplying a **concrete
`SurgeryChartDatum`** at the KT surgery-trace models: chart model
`H' = ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanHalfSpace 1)`, cylinder end `B = M × I`, handle end
`Ha = D² × D³`, and the welded seam collar — plus `J = (𝓡 4).prod (𝓡∂ 1)`.

This module ships the **honestly-complete floor** of that datum and names the irreducible residual
sharply.

## What lands GREEN here

* **§1 — the concrete cylinder chart `KTModel`-charts `M × I`.** For any source manifold `M` charted on
  `EuclideanSpace ℝ (Fin 4)` (every `SingularManifold.{0} X 0 (𝓡 4)`'s carrier is one), the cylinder
  `M × Set.Icc 0 1` is `H'`-charted **for free** by Mathlib's product-charted-space instance
  (`prodChartedSpace`) over `M`'s charts × the interval's boundary-model charts
  (`ChartedSpace (EuclideanHalfSpace 1) (Set.Icc 0 1)`). This is exactly the charted structure
  `reflCylinder`'s `W` carries; `chartB` is DONE, concretely, with zero geometric input.

* **§2 — the `k = 0` boundary-smoothness collapse.** In the continuous category the bordism's boundary
  map obligation `he_smooth : ContMDiff I J 0 e` is **just continuity** (`contMDiff_zero_iff`). So the
  Wave-3 boundary input `he_smooth` carries no smoothness content for the Pin⁺ (`k = 0`) consumer either
  — a `Continuous e` suffices. This sharpens the residual: only `he_inj` (injectivity) and `he_boundary`
  (range `= ∂W`) remain genuine.

## THE Ha DESIGN CALL — the document of record (D⁵ dominates)

The handle `Ha = D² × D³` (a 2-handle of the 5-dimensional trace) charts *naturally* over the corner
model `ModelProd (ModelProd E¹ H¹) (ModelProd E² H¹)` — TWO half-space factors, a corner. `H'` has a
single half-space factor. At `k = 0` `IsManifold` ignores the corner (Wave 5's finding), but the
`ChartedSpace` model `H'` must still match on the nose, so the product route needs a *corner-straightening*
model homeomorphism (quadrant `≃ₜ` half-plane) — bespoke and awkward.

The **cheapest honest** presentation is therefore **`Ha = D⁵`** (a 2-handle is a 5-ball abstractly): a
closed 5-ball built with the same collar atlas as `DiskManifoldSmooth`'s `D³` is modelled on
`(𝓡 4).prod (𝓡∂ 1)` — model space **exactly `H'`, a single boundary face, NO corner and NO
re-association.** The attaching region is a thickened `S¹ ⊆ ∂D⁵`. This is the design of record; the
concrete `D⁵` collar atlas is the sharply-named residual below (a `ChartedSpace H' D⁵`, the direct
5-dimensional analogue of `DiskChart`/`DiskManifoldSmooth`'s `D³` construction).

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryDatumC0
import SKEFTHawking.PinPlusKTSurgeryTraceConsumers

namespace SKEFTHawking.SurgeryFoundation

open Topology TopologicalSpace
open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTSurgeryTraceConsumers

/-! ## §1. The concrete cylinder chart — `chartB` for `B = M × I`, at the KT model, for free. -/

/-- **The KT surgery-trace chart model** `H' = ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanHalfSpace 1)`
— the model space of `J = (𝓡 4).prod (𝓡∂ 1)`, the tangent model of the Pin⁺ surgery-trace bordism. -/
abbrev KTModel : Type := ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanHalfSpace 1)

/-- **The cylinder end `M × I` is `H'`-charted, concretely and for free.** For any `M` charted on
`EuclideanSpace ℝ (Fin 4)` (every closed source 4-manifold), the cylinder `M × Set.Icc 0 1` carries a
`ChartedSpace KTModel` structure by Mathlib's product-charted-space instance: `M`'s charts × the
interval's boundary-model charts (`ChartedSpace (EuclideanHalfSpace 1) (Set.Icc 0 1)`). This is the
`chartB` field of the KT surgery-trace `SurgeryChartDatum` — delivered with zero geometric input. -/
@[reducible] noncomputable def cylinderChartedSpace (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] :
    ChartedSpace KTModel (M × Set.Icc (0 : ℝ) 1) :=
  inferInstance

/-! ## §2. The `k = 0` boundary-smoothness collapse — the boundary map's smoothness is free.

The bordism's boundary-map field `he_smooth : ContMDiff I J 0 e` demands only continuity in the
continuous category (`contMDiff_zero_iff`). So the Pin⁺ (`k = 0`) consumer's boundary input reduces to a
`Continuous e`; only `he_inj`/`he_boundary` carry genuine content. -/

/-- **At `k = 0` the boundary map's smoothness obligation is continuity.** A restatement of Mathlib's
`contMDiff_zero_iff` at the surgery-trace boundary shape: for a map between charted spaces, `ContMDiff`
at order `0` is exactly `Continuous`. This discharges the `he_smooth` field of the surgery-trace bordism
from a bare continuity hypothesis (the Pin⁺ consumer runs at `k = 0`). -/
theorem contMDiff_zero_iff_continuous
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    (J : ModelWithCorners ℝ E' H')
    {M M' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
    (f : M → M') : ContMDiff I J 0 f ↔ Continuous f :=
  contMDiff_zero_iff

/-! ## §3. The concrete surgery-chart datum — cylinder end baked in, handle + collar as named inputs.

The KT surgery-trace `HandleAttachment` with the cylinder end `B = M × I` fixed concretely (its
`TopologicalSpace`/`CompactSpace`/`T2Space` free from `M`'s + the interval's), and the
`SurgeryChartDatum` whose `chartB` is `cylinderChartedSpace` (§1). The handle `Ha` (its atlas), the
attaching data `S`/`φ`, and the welded seam collar `seamNbhd`/`chartSeam` remain the named geometric
inputs (the Ha-atlas + collar-weld residuals; see the header's design of record). -/

/-- **The KT surgery-trace handle-attachment with cylinder end `B = M × I`.** `M` is the (compact
Hausdorff) source 4-manifold; the interval `Set.Icc 0 1` supplies the collar direction. The handle `Ha`,
attaching region `S`, and attaching map `φ : S → M × I` are the geometric inputs a surgery presentation
supplies; `B`'s compactness/Hausdorffness are free. -/
def ktHandleAttachment
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (Ha : Type) [TopologicalSpace Ha] [CompactSpace Ha] [T2Space Ha]
    (S : Set Ha) (hS : IsClosed S) (φ : ↥S → M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ) : HandleAttachment where
  B := M × Set.Icc (0 : ℝ) 1
  Ha := Ha
  S := S
  hS := hS
  φ := φ
  hφ := hφ
  hφinj := hφinj

/-- **The KT surgery-trace `SurgeryChartDatum` — the Wave-2 `ChartedSpace` floor, with `chartB`
concrete.** The cylinder end's chart is `cylinderChartedSpace M` (§1, free); the handle's chart
`chartHa` and the welded seam collar `seamNbhd`/`chartSeam` are the named geometric inputs. Its chart
model is `H' = KTModel`, so `SmoothSurgeryChartDatum.ofC0 · (E⁴ × E¹) ((𝓡 4).prod (𝓡∂ 1))` pins the
Pin⁺ tangent model. -/
noncomputable def ktSurgeryChartDatum
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (Ha : Type) [TopologicalSpace Ha] [CompactSpace Ha] [T2Space Ha]
    [ChartedSpace KTModel Ha]
    (S : Set Ha) (hS : IsClosed S) (φ : ↥S → M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (seamNbhd : Opens (ktHandleAttachment M Ha S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment M Ha S hS φ hφ hφinj).seamRegion ⊆ seamNbhd)
    [chartSeam : ChartedSpace KTModel seamNbhd] : SurgeryChartDatum where
  toHandleAttachment := ktHandleAttachment M Ha S hS φ hφ hφinj
  H' := KTModel
  chartB := cylinderChartedSpace M
  chartHa := ‹ChartedSpace KTModel Ha›
  seamNbhd := seamNbhd
  hseam := hseam
  chartSeam := chartSeam

/-- **The KT surgery-trace `SmoothSurgeryChartDatum` at the Pin⁺ tangent model.** `ktSurgeryChartDatum`
(§3, `chartB` concrete) pushed through Wave-5's `SmoothSurgeryChartDatum.ofC0` with tangent model
`J = (𝓡 4).prod (𝓡∂ 1)` and smoothness order `k = 0` — the whole smoothness/weld stack is free (Wave 5).
This is the datum the Pin⁺ ambient consumer's `b` field is built from. -/
noncomputable def ktSmoothSurgeryChartDatum
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (Ha : Type) [TopologicalSpace Ha] [CompactSpace Ha] [T2Space Ha]
    [ChartedSpace KTModel Ha]
    (S : Set Ha) (hS : IsClosed S) (φ : ↥S → M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (seamNbhd : Opens (ktHandleAttachment M Ha S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment M Ha S hS φ hφ hφinj).seamRegion ⊆ seamNbhd)
    [chartSeam : ChartedSpace KTModel seamNbhd] : SmoothSurgeryChartDatum :=
  SmoothSurgeryChartDatum.ofC0 (ktSurgeryChartDatum M Ha S hS φ hφ hφinj seamNbhd hseam)
    (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)) ((𝓡 4).prod (𝓡∂ 1))

/-! ## §4. The win-shape, cashed — the concrete ambient trace bordism (honest conditional).

The Pin⁺ consumer's `AmbientSurgeryDatum.b : Bordism ((𝓡 4).prod (𝓡∂ 1)) …` EXISTS once the residual
geometric inputs are supplied: the source manifold `s` (its cylinder end + chart are baked in), the
handle end `Ha` with its atlas, the attaching data `S`/`φ`, the welded seam collar, and the boundary
identification (`Continuous` suffices for smoothness by §2; only injectivity + the range-`= ∂W` condition
carry content). Everything the `ChartedSpace` floor could resolve for free is resolved; the named inputs
are exactly the header's sharply-named residuals. -/

/-- **The concrete ambient trace bordism (honest conditional).** Given a source closed 4-manifold `s`
(Hausdorff), a handle end `Ha` with its `H'`-atlas, the attaching region `S`/map `φ : S → s.M × I`, the
welded seam collar `seamNbhd`/`chartSeam`, and a boundary identification `e` that is continuous,
injective, and hits exactly `∂W` — the surgery-trace `Bordism ((𝓡 4).prod (𝓡∂ 1)) s t` is produced. The
cylinder end's chart (`chartB`) and the whole `k = 0` smoothness/weld stack are supplied concretely
(§1–§3, Wave 5); the boundary map's smoothness is discharged from continuity (§2). This is the mission's
win-shape: feeding the Pin⁺ consumer's `b` bottoms out in exactly {handle atlas, attaching map, seam
collar, boundary injectivity + range}. -/
noncomputable def ambientTraceBordism_concrete
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (Ha : Type) [TopologicalSpace Ha] [CompactSpace Ha] [T2Space Ha]
    [ChartedSpace KTModel Ha]
    (S : Set Ha) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (seamNbhd : Opens (ktHandleAttachment s.M Ha S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M Ha S hS φ hφ hφinj).seamRegion ⊆ seamNbhd)
    [chartSeam : ChartedSpace KTModel seamNbhd]
    (e : s.M ⊕ t.M → (ktHandleAttachment s.M Ha S hS φ hφ hφinj).carrier)
    (he_cont : Continuous e)
    (he_inj : Function.Injective e)
    (he_boundary :
      letI : ChartedSpace KTModel (ktHandleAttachment s.M Ha S hS φ hφ hφinj).carrier :=
        (ktSurgeryChartDatum s.M Ha S hS φ hφ hφinj seamNbhd hseam).carrierChartedSpace
      Set.range e =
        ((𝓡 4).prod (𝓡∂ 1)).boundary (ktHandleAttachment s.M Ha S hS φ hφ hφinj).carrier) :
    Bordism ((𝓡 4).prod (𝓡∂ 1)) s t := by
  letI : ChartedSpace KTModel (ktHandleAttachment s.M Ha S hS φ hφ hφinj).carrier :=
    (ktSurgeryChartDatum s.M Ha S hS φ hφ hφinj seamNbhd hseam).carrierChartedSpace
  haveI : FiniteDimensional ℝ
      (ktSmoothSurgeryChartDatum s.M Ha S hS φ hφ hφinj seamNbhd hseam).E' :=
    (inferInstance : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)))
  have he_smooth : ContMDiff (𝓡 4) ((𝓡 4).prod (𝓡∂ 1)) 0 e := contMDiff_zero_iff.mpr he_cont
  exact ambientTraceBordism (ktSmoothSurgeryChartDatum s.M Ha S hS φ hφ hφinj seamNbhd hseam)
    s t e he_smooth he_inj he_boundary

end SKEFTHawking.SurgeryFoundation
