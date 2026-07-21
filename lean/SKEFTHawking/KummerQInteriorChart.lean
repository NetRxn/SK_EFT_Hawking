/-
# Phase 5q.H — K6′b Leg 10b: CHART FAMILY 2/3 — the Q-interior charts on the flat model `𝓔³ × ℝ`

`Q = T⁴°/τ` is charted on the manifold-**with-boundary** model `Model = ModelProd 𝓔³
(EuclideanHalfSpace 1)` (`KummerQuotientManifold.instChartedSpaceFreeQuotient`). The weld atlas needs
its **interior** `interiorQ = Q ∖ ∂Q` charted on the boundaryless `𝓔³ × ℝ`.

**Why this side is not symmetric with the E side.** On the E side the atlas's three *interior*
charts already cover `interiorE`, so the collar charts are never touched. On the Q side they do
**not**: the `Q` atlas's interior charts live over the round-`5/8`-ball complement `interiorSet`,
while `interiorQ` reaches all the way down to chart-radius `> 1/2`. Points of the collar band
`1/2 < r < 5/8` are covered only by a **collar** chart. So the positivity of the half-space height
cannot come from a target inclusion here; it must come from the geometry:

> `KummerShellChart.shellCollarChart` has height `‖v‖ − 1/2`, so a collar chart has **positive**
> height exactly at the points of chart-radius `> 1/2` — i.e. exactly off the boundary sphere
> `chartSphere c`. And `q ∈ interiorQ` says precisely that no representative sits on any
> `chartSphere c` (§2).

That is the honest content of this module: `posHt_chartAt_of_mem_interiorQ` (§3), the pointwise
positive-height law for the *dispatched* `Q`-chart, valid on both branches of the dispatch.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.HalfSpaceInteriorFlatten
import SKEFTHawking.KummerWeldQInterior
import SKEFTHawking.KummerQuotientManifold

namespace SKEFTHawking.KummerQInteriorChart

open Set Topology
open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerShellChart
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerChartedSpace (qmk_localOpenPartialHomeomorph
  mem_qmk_localOpenPartialHomeomorph_source)
open SKEFTHawking.KummerBoundaryChart
open SKEFTHawking.KummerWeldQInterior (interiorQ isOpen_interiorQ)
open SKEFTHawking.HalfSpaceInteriorFlatten

noncomputable section

/-! ## §1. The interior branch: `interiorReshape` lands in the half-space interior -/

/-- `interiorReshape`'s target **is** the interior region — its fourth coordinate is an
exponential. -/
theorem posHt_interiorReshape : PosHt interiorReshape :=
  posHt_of_target_subset (fun _ hq => hq)

theorem posHt_interiorChartR (x : ↥interiorOpens) : PosHt (interiorChartR x) :=
  posHt_lift isOpenEmbedding_interiorIncl (posHt_trans _ posHt_interiorReshape)

/-! ## §2. The collar branch: height `= ‖v‖ − 1/2`, positive off the boundary sphere -/

/-- **The collar chart's half-space height is the shell radius above `1/2`.** -/
theorem height_bdyChartAt {y : ↥puncturedTorus} (h : (y : TorusFour) ∉ interiorSet) :
    height (bdyChartAt h y) = ‖(chosenShell h : EuclideanSpace ℝ (Fin 4))‖ - 1 / 2 := by
  have key : bdyChartAt h y
      = innerCollarChart (chosenC h) (shellDir (shellIncl (chosenShell h)))
          ⟨(y : TorusFour), mem_collarSet_chosenC h⟩ :=
    (innerCollarChart (chosenC h) (shellDir (shellIncl (chosenShell h)))).lift_openEmbedding_apply
      (isOpenEmbedding_collarIncl (chosenC_mem h))
      (x := ⟨(y : TorusFour), mem_collarSet_chosenC h⟩)
  rw [key]
  rfl

/-- A point of `T⁴°` whose `Q`-image misses `∂Q` is not on any boundary sphere. -/
theorem notMem_chartSphere_of_interiorQ {y : ↥puncturedTorus} (hy : qmk y ∈ interiorQ)
    {c : TorusFour} (hc : c ∈ fixedSet) : (y : TorusFour) ∉ chartSphere c := fun hmem =>
  hy (Set.mem_biUnion hc ⟨y, hmem, rfl⟩)

/-- **The collar height is strictly positive off the boundary sphere.** If the shell radius were
exactly `1/2` the point would be the centered-chart image of a radius-`1/2` vector, i.e. a point of
`chartSphere (chosenC h)` — which `interiorQ` forbids. -/
theorem height_bdyChartAt_pos {y : ↥puncturedTorus} (h : (y : TorusFour) ∉ interiorSet)
    (hy : qmk y ∈ interiorQ) : 0 < height (bdyChartAt h y) := by
  rw [height_bdyChartAt h]
  have hlow : (1 : ℝ) / 2 ≤ ‖(chosenShell h : EuclideanSpace ℝ (Fin 4))‖ := (chosenShell h).2.1
  rcases lt_or_eq_of_le hlow with hlt | heq
  · linarith
  · exfalso
    refine notMem_chartSphere_of_interiorQ hy (chosenC_mem h) ?_
    have himg : centeredChartParamE4 (chosenC h) (chosenShell h : EuclideanSpace ℝ (Fin 4))
        = (y : TorusFour) := by
      have := (collarHomeo (chosenC h)).apply_symm_apply
        (⟨(y : TorusFour), mem_collarSet_chosenC h⟩ : ↥(collarSet (chosenC h)))
      exact congrArg Subtype.val this
    refine ⟨ofE4 (chosenShell h : EuclideanSpace ℝ (Fin 4)), ?_, himg⟩
    show sqNorm (ofE4 (chosenShell h : EuclideanSpace ℝ (Fin 4))) = excisionRadius ^ 2
    rw [sqNorm_ofE4, ← heq]
    norm_num [show excisionRadius = (1 : ℝ) / 2 from rfl]

/-! ## §3. The dispatched `Q`-chart has positive height on `interiorQ` -/

open Classical in
/-- **THE Q-SIDE POSITIVE-HEIGHT LAW.** At every point of `interiorQ` the dispatched half-space
chart of `Q` sends the point strictly inside the half space — on the interior branch because
`interiorReshape`'s fourth coordinate is an exponential, on the collar branch because the point's
shell radius exceeds `1/2` (§2). This is the Q-side replacement for the E-side's global `PosHt`. -/
theorem posHt_chartAt_of_mem_interiorQ {q : FreeQuotient} (hq : q ∈ interiorQ) :
    0 < height (chartAt HModel q q) := by
  have hout : qmk (Quotient.out q) = q := Quotient.out_eq q
  have hsymm : (qmk_localOpenPartialHomeomorph (Quotient.out q)).symm q = Quotient.out q := by
    have h2 := (qmk_localOpenPartialHomeomorph (Quotient.out q)).left_inv
      (mem_qmk_localOpenPartialHomeomorph_source (Quotient.out q))
    rw [SKEFTHawking.KummerChartedSpace.qmk_localOpenPartialHomeomorph_apply, hout] at h2
    exact h2
  by_cases h : ((Quotient.out q : ↥puncturedTorus) : TorusFour) ∈ interiorSet
  · show 0 < height (dite _ (fun h => qmkInteriorChart (Quotient.out q) h)
      (fun h => qmkBoundaryChart (Quotient.out q) h) q)
    rw [dif_pos h]
    show 0 < height (interiorChartR ⟨_, h⟩
      ((qmk_localOpenPartialHomeomorph (Quotient.out q)).symm q))
    rw [hsymm]
    refine posHt_interiorChartR ⟨_, h⟩ _ ?_
    have := mem_interiorChartR_source
      (⟨((Quotient.out q : ↥puncturedTorus) : TorusFour), h⟩ : ↥interiorOpens)
    exact this
  · show 0 < height (dite _ (fun h => qmkInteriorChart (Quotient.out q) h)
      (fun h => qmkBoundaryChart (Quotient.out q) h) q)
    rw [dif_neg h]
    show 0 < height (bdyChartAt h ((qmk_localOpenPartialHomeomorph (Quotient.out q)).symm q))
    rw [hsymm]
    exact height_bdyChartAt_pos h (by rw [hout]; exact hq)

/-! ## §4. The flat charted space on `↥interiorQ` -/

/-- The open inclusion `↥interiorQ ↪ Q` as an `OpenPartialHomeomorph`. The `Nonempty` witness (only
needed for the junk value of the inverse off the range) is the very point the chart is built at — no
separate "some point of `Q` misses `∂Q`" geometric argument is required. -/
def interiorQIncl (y : ↥interiorQ) : OpenPartialHomeomorph (↥interiorQ) FreeQuotient :=
  haveI : Nonempty ↥interiorQ := ⟨y⟩
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph Subtype.val
    isOpen_interiorQ.isOpenEmbedding_subtypeVal

@[simp] theorem interiorQIncl_source (y : ↥interiorQ) : (interiorQIncl y).source = Set.univ := rfl

/-- **The flat Q-interior chart at `y`** — the dispatched half-space chart of `Q` at `y`, flattened
and restricted to `↥interiorQ`. -/
def qIntChart (y : ↥interiorQ) : OpenPartialHomeomorph (↥interiorQ) FModel :=
  (interiorQIncl y).trans (flatChart (chartAt HModel (y : FreeQuotient)))

theorem mem_qIntChart_source (y : ↥interiorQ) : y ∈ (qIntChart y).source := by
  rw [qIntChart, OpenPartialHomeomorph.trans_source]
  exact ⟨Set.mem_univ _,
    mem_flatChart_source (mem_chart_source HModel (y : FreeQuotient))
      (posHt_chartAt_of_mem_interiorQ y.2)⟩

/-- **CHART FAMILY 2/3 (interior half) — `↥interiorQ` is a charted space on the flat model
`𝓔³ × ℝ`.** The atlas is the flattening of the `Q` half-space atlas at each interior point; the
positivity that keeps each source intact is `posHt_chartAt_of_mem_interiorQ`. -/
noncomputable instance instChartedSpaceInteriorQ : ChartedSpace FModel (↥interiorQ) where
  atlas := Set.range qIntChart
  chartAt := qIntChart
  mem_chart_source := mem_qIntChart_source
  chart_mem_atlas y := Set.mem_range_self y

end

end SKEFTHawking.KummerQInteriorChart
