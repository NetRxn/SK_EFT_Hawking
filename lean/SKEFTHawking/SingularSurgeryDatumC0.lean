/-
# Phase 5q.H W-D — SURGERY WAVE 5: the C⁰ model-pinned `SmoothSurgeryChartDatum`

Wave 4 (`SingularSurgeryWeld.lean` + `PinPlusKTSurgeryTraceConsumers.lean`) reduced BOTH convergence
consumers' trace bordism to residual 1: a CONCRETE `SmoothSurgeryChartDatum` (Wave 3's smoothness-
enriched surgery datum) at the KT surgery-trace models — `J = (𝓡 4).prod (𝓡∂ 1)`, smoothness order
`k = 0` (the continuous category — the setting the Pin⁺ `AmbientSurgeryDatum.b` lives in), the 2-handle
`Ha = D² × D³`, cylinder `B = M × I`. This module instantiates that datum's smoothness/weld field stack
**as far as honest**, and the finding is decisive:

## THE k = 0 FINDING — the entire smoothness/weld stack is FREE in the continuous category

`SmoothSurgeryChartDatum` (Wave 3) enriches the Wave-2 `SurgeryChartDatum` (the pure `ChartedSpace`
floor) with FOUR smoothness fields: `mfdB`, `mfdHa`, `mfdSeam` (`IsManifold J k` on the two ends + the
seam collar) and `smoothWeld` (the seam↔interior chart transitions lie in `contDiffGroupoid k J` — the
"sole genuinely-geometric input", Wave 3's own words). At `k = 0` **all four collapse to nothing**:

* **`IsManifold J 0 X` is a registered instance for ANY `ChartedSpace H' X`** (`IsManifold.
  instOfNatWithTopENat`). So `mfdB`/`mfdHa`/`mfdSeam` are synthesized by instance resolution from the
  Wave-2 datum's `chartB`/`chartHa`/`chartSeam` alone — no smoothness content whatsoever.
* **`contDiffGroupoid 0 J = continuousGroupoid H'`** (`contDiffGroupoid_zero_eq`), and EVERY
  `OpenPartialHomeomorph H' H'` lies in `continuousGroupoid H'` (its pregroupoid property is `True`).
  So `smoothWeld` — for ANY of the seam↔interior transitions, without touching the collar geometry —
  is discharged by `mem_contDiffGroupoid_zero` below.

**Consequence (the mission's win-shape, cashed):** at `k = 0` a `SmoothSurgeryChartDatum` requires NO
geometric weld input beyond a `SurgeryChartDatum` (Wave-2's `ChartedSpace` atlas) plus a choice of
tangent model `J`. `SmoothSurgeryChartDatum.ofC0` builds it generically; the caller pins
`J = (𝓡 4).prod (𝓡∂ 1)` at consumer time. The `smoothWeld` field — Wave 3's stated "sole geometric
input" — carries ZERO content in the continuous category.

## THE CORNER DESIGN CALL — it EVAPORATES at k = 0 (document of record)

The a-priori worry (mission brief): `Ha = D² × D³` has corners at `∂D² × ∂D³`, so the honest smooth
model might need corner-smoothing or a corner-free re-presentation (e.g. the closed 5-ball `D⁵` — a
2-handle IS a 5-ball abstractly). **This concern is void at `k = 0`.** The corner obstruction is
purely a *smoothness-of-transition* phenomenon; `IsManifold J 0` ignores transition smoothness entirely
(every continuous transition qualifies). So `D² × D³` needs no corner model, no smoothing, and no
diffeomorphic 5-ball substitute: whatever `ChartedSpace H'` the Wave-2 datum equips `Ha` with (corners
and all) is already a `C⁰` manifold-with-corners for free. The corner design call is therefore made by
NOT making it — the cheapest honest presentation is the literal product, taken at `k = 0`.

## The post-wave residual (restated)

Feeding the consumers' `SmoothSurgeryChartDatum` now reduces to supplying a **`SurgeryChartDatum`** —
Wave 2's `ChartedSpace` floor: the two ends `B = M × I`, `Ha = D² × D³` as `ChartedSpace H'` over the KT
model `H' = ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanHalfSpace 1)`, and the seam collar's
`chartSeam` (Wave 2's named collar-neighborhood residual) — plus the tangent model `J`. The
smoothness/weld obstruction that Wave 3 isolated is DISCHARGED for the `k = 0` (Pin⁺ ambient) consumer.
(The generic-`k` `HandleTradeCobordism` consumer, whose tangential data fixes `k` abstractly, still
carries the genuine collar-weld smoothness at `k > 0`; only the `k = 0` datum is free.)

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryManifold

namespace SKEFTHawking.SurgeryFoundation

open Topology TopologicalSpace
open scoped Manifold

/-! ## §1. The reusable C⁰ groupoid fact — every change of coordinates is `C⁰`-smooth. -/

/-- **Every `OpenPartialHomeomorph H' H'` lies in `contDiffGroupoid 0 J`.** At smoothness order `0`
the smooth groupoid is the *continuous* groupoid (`contDiffGroupoid_zero_eq`), whose pregroupoid
property is `True`, so any change of coordinates qualifies. This is the reusable Mathlib-grade fact
behind the k = 0 collapse of the surgery `smoothWeld`. -/
theorem mem_contDiffGroupoid_zero {H' : Type*} [TopologicalSpace H']
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (J : ModelWithCorners ℝ E' H') (e : OpenPartialHomeomorph H' H') :
    e ∈ contDiffGroupoid 0 J := by
  rw [contDiffGroupoid_zero_eq]
  exact mem_groupoid_of_pregroupoid.mpr ⟨trivial, trivial⟩

/-! ## §2. The generic C⁰ constructor — `SurgeryChartDatum` + tangent model ⟹ `SmoothSurgeryChartDatum`.

Generic-output (the mission's "keep the datum generic, pin at the caller"): any Wave-2 `SurgeryChartDatum`
extends to a Wave-3 `SmoothSurgeryChartDatum` at `k = 0` for ANY tangent model `J` over its chart model
`H'`. The four smoothness fields are the k = 0 collapse: `mfdB`/`mfdHa`/`mfdSeam` from the datum's own
charts (the `IsManifold _ 0` instance), `smoothWeld` from `mem_contDiffGroupoid_zero`. -/

/-- **The C⁰ smoothness-enriched surgery datum** — Wave-2 `SurgeryChartDatum` `D₀` + a tangent model `J`
over its chart model `D₀.H'`, at smoothness order `0`. Discharges all four of Wave 3's smoothness fields
in the continuous category (see the module header — the k = 0 finding). The caller pins `J`
(`= (𝓡 4).prod (𝓡∂ 1)` for the KT surgery trace); the datum stays generic. -/
noncomputable def SmoothSurgeryChartDatum.ofC0
    (D₀ : SurgeryChartDatum)
    (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (J : ModelWithCorners ℝ E' D₀.H') :
    SmoothSurgeryChartDatum where
  toSurgeryChartDatum := D₀
  E' := E'
  J := J
  k := 0
  mfdB := inferInstance
  mfdHa := inferInstance
  mfdSeam := inferInstance
  smoothWeld := fun _ _ _ _ _ _ => mem_contDiffGroupoid_zero J _

/-! ## §3. The constructor's projections — what the caller reasons with. -/

@[simp] theorem SmoothSurgeryChartDatum.ofC0_toSurgeryChartDatum
    (D₀ : SurgeryChartDatum) (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (J : ModelWithCorners ℝ E' D₀.H') :
    (SmoothSurgeryChartDatum.ofC0 D₀ E' J).toSurgeryChartDatum = D₀ := rfl

@[simp] theorem SmoothSurgeryChartDatum.ofC0_k
    (D₀ : SurgeryChartDatum) (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (J : ModelWithCorners ℝ E' D₀.H') :
    (SmoothSurgeryChartDatum.ofC0 D₀ E' J).k = 0 := rfl

@[simp] theorem SmoothSurgeryChartDatum.ofC0_J
    (D₀ : SurgeryChartDatum) (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (J : ModelWithCorners ℝ E' D₀.H') :
    (SmoothSurgeryChartDatum.ofC0 D₀ E' J).J = J := rfl

end SKEFTHawking.SurgeryFoundation
