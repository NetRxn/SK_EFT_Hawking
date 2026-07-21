/-
# Phase 5q.H — K6′b Leg 10a: CHART FAMILY 1/3 — the E-interior charts on the flat model `𝓔³ × ℝ`

`ResE` is charted on the manifold-**with-boundary** model `Model = ModelProd 𝓔³ (EuclideanHalfSpace
1)` (`KummerResolutionPieceBoundary.instChartedSpaceResE`). The weld atlas needs its **interior**
`interiorE = {fiberNorm < 1}` charted on the boundaryless `𝓔³ × ℝ`. This module supplies that, by
composing the three *interior* charts of the E-side atlas with the flattening of
`HalfSpaceInteriorFlatten`.

**Why the three interior charts suffice.** `interiorE` is exactly the fiber-radius-`< 1` locus, and
the fiber interior chart `DiskChartGeneric.diskInteriorChart 1` is defined on exactly that locus
(`‖w‖ < 1`, including the fiber centre). So the base dispatch of
`KummerResolutionPieceBoundary.exists_chart` — off the base equator use `interiorChart` /
`interiorChart1`, on it use `annulusInteriorChart` — always has its interior branch available on
`interiorE`; the collar charts are never needed (§3).

**Why the height is positive there.** The fiber interior chart's half-space coordinate is
`w_last + 2 ≥ 2 − ‖w‖ > 1`, and the model reshape `𝓔² × (𝓔¹ × HS¹) → 𝓔³ × HS¹` carries the fiber's
half-space factor across untouched. So all three interior charts satisfy
`HalfSpaceInteriorFlatten.PosHt` **globally**, not merely on the interior (§2) — flattening them
therefore does not shrink their sources at all.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.HalfSpaceInteriorFlatten
import SKEFTHawking.KummerWeldOpenPieces
import SKEFTHawking.KummerResolutionPieceBoundary

namespace SKEFTHawking.KummerEInteriorChart

open Set Topology
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeldFiberFlow
open SKEFTHawking.KummerWeldOpenPieces (interiorE isOpen_interiorE)
open SKEFTHawking.HalfSpaceInteriorFlatten
open SKEFTHawking.KummerResolutionPieceBoundary
open SKEFTHawking.DiskChartGeneric (NDisk diskInteriorChart)

noncomputable section

/-! ## §1. The height coordinate of the banked disk interior chart -/

/-- The half-space coordinate of the fiber-level model `ModelProd 𝓔¹ HalfSpace¹`. -/
def fiberHt {n : ℕ} (p : ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)) : ℝ :=
  p.2.val.ofLp 0

/-- **The disk interior chart's half-space coordinate is the translated last coordinate.** -/
theorem fiberHt_diskInteriorChart {n : ℕ} (v : NDisk n) :
    fiberHt (diskInteriorChart n v) = (v : EuclideanSpace ℝ (Fin (n + 1))).ofLp (Fin.last n) + 2 := by
  simp only [fiberHt]; rfl

/-- **The disk interior chart lands strictly inside the half-space** — `|v_last| ≤ ‖v‖ ≤ 1`, so the
translated coordinate is `≥ 1 > 0`. This is the fact that makes the E-interior charts flattenable. -/
theorem fiberHt_diskInteriorChart_pos {n : ℕ} (v : NDisk n) : 0 < fiberHt (diskInteriorChart n v) := by
  rw [fiberHt_diskInteriorChart]
  have h1 : ‖(v : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := mem_closedBall_zero_iff.mp v.2
  have h2 : ‖(v : EuclideanSpace ℝ (Fin (n + 1))).ofLp (Fin.last n)‖
      ≤ ‖(v : EuclideanSpace ℝ (Fin (n + 1)))‖ := PiLp.norm_apply_le _ _
  rw [Real.norm_eq_abs] at h2
  have h3 := (abs_le.mp (h2.trans h1)).1
  linarith

/-- The fiber interior chart of the E-side (the banked disk chart through the `Disk ≃ₜ NDisk 1`
bridge) has strictly positive half-space coordinate, at **every** point of `Disk`. -/
theorem fiberHt_fiberInteriorChart_pos (w : Disk) : 0 < fiberHt (fiberInteriorChart w) :=
  fiberHt_diskInteriorChart_pos _

/-! ## §2. `PosHt` for the three E-side interior charts -/

/-- **The reshape carries the fiber's half-space factor across untouched**: the `Model` height of a
reshaped point is the fiber-level height. -/
theorem height_reshapeModel
    (q : EuclideanSpace ℝ (Fin 2) × ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)) :
    height (reshapeModel q) = fiberHt q.2 := rfl

/-- **The generic `PosHt` for a `(base × fiber-interior) ≫ reshape` chart.** Both E-side interior
chart shapes — `resChartInteriorChart` (base `baseDiskChart`) and `baseFiberInteriorChart` (base
`toE2Homeo`) — are of this form, so this single lemma discharges both. -/
theorem posHt_prod_reshape {B : Type*} [TopologicalSpace B]
    (a : OpenPartialHomeomorph B (EuclideanSpace ℝ (Fin 2)))
    (b : OpenPartialHomeomorph Disk (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (hb : ∀ w, 0 < fiberHt (b w)) :
    PosHt ((a.prod b).trans reshapeModel.toOpenPartialHomeomorph) := by
  intro x _
  show 0 < height (reshapeModel (a x.1, b x.2))
  rw [height_reshapeModel]
  exact hb x.2

theorem posHt_resChartInteriorChart : PosHt resChartInteriorChart :=
  posHt_prod_reshape baseDiskChart fiberInteriorChart fiberHt_fiberInteriorChart_pos

theorem posHt_interiorChartInner : PosHt interiorChartInner :=
  posHt_trans _ posHt_resChartInteriorChart

theorem posHt_interiorChart : PosHt interiorChart :=
  posHt_lift isOpenEmbedding_chart0_baseInterior posHt_interiorChartInner

theorem posHt_interiorChart1 : PosHt interiorChart1 :=
  posHt_lift isOpenEmbedding_chart1_baseInterior posHt_interiorChartInner

theorem posHt_baseFiberInteriorChart : PosHt baseFiberInteriorChart :=
  posHt_prod_reshape toE2Homeo.toOpenPartialHomeomorph fiberInteriorChart
    fiberHt_fiberInteriorChart_pos

theorem posHt_annulusInteriorChart : PosHt annulusInteriorChart :=
  posHt_trans _ posHt_baseFiberInteriorChart

/-! ## §3. The three interior charts cover `interiorE` -/

/-- **The E-side interior atlas** — the three `Model`-valued interior charts of `ResE`. -/
def atlasEInt : Set (OpenPartialHomeomorph ResE HModel) :=
  {interiorChart, interiorChart1, annulusInteriorChart}

theorem posHt_of_mem_atlasEInt {c : OpenPartialHomeomorph ResE HModel} (hc : c ∈ atlasEInt) :
    PosHt c := by
  rcases hc with rfl | rfl | rfl
  · exact posHt_interiorChart
  · exact posHt_interiorChart1
  · exact posHt_annulusInteriorChart

/-- **THE INTERIOR COVERING.** Every point of `interiorE` lies in the source of one of the three
interior charts — the collar charts are never needed. The fiber-radius hypothesis `fiberNorm x < 1`
is exactly the source condition of the fiber interior chart. -/
theorem exists_interiorChart {x : ResE} (hx : x ∈ interiorE) :
    ∃ c ∈ atlasEInt, x ∈ c.source := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  cases a with
  | inl p =>
    have hw : ‖(p.2 : ℂ)‖ < 1 := hx
    by_cases hz : ‖(p.1 : ℂ)‖ < 1
    · exact ⟨interiorChart, Set.mem_insert _ _, mem_interiorChart_source hz hw⟩
    · have hz1 : 1 / 2 < ‖(p.1 : ℂ)‖ := lt_of_lt_of_le (by norm_num) (not_lt.mp hz)
      exact ⟨annulusInteriorChart,
        Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl),
        mem_annulusInteriorChart_source_chart0 hz1 hw⟩
  | inr q =>
    have hw : ‖(q.2 : ℂ)‖ < 1 := hx
    by_cases hz : ‖(q.1 : ℂ)‖ < 1
    · exact ⟨interiorChart1, Set.mem_insert_of_mem _ (Set.mem_insert _ _),
        mem_interiorChart1_source hz hw⟩
    · have hz1 : 1 / 2 < ‖(q.1 : ℂ)‖ := lt_of_lt_of_le (by norm_num) (not_lt.mp hz)
      exact ⟨annulusInteriorChart,
        Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl),
        mem_annulusInteriorChart_source_chart1 hz1 hw⟩

/-! ## §4. The flat charted space on `↥interiorE` -/

instance instNonemptyInteriorE : Nonempty ↥interiorE :=
  ⟨⟨chart0 (⟨0, by simp⟩, ⟨0, by simp⟩), by
    show fiberNorm (chart0 (⟨0, by simp⟩, ⟨0, by simp⟩)) < 1
    rw [fiberNorm_chart0]
    simp⟩⟩

/-- The open inclusion `↥interiorE ↪ ResE` as an `OpenPartialHomeomorph`. -/
def interiorEIncl : OpenPartialHomeomorph (↥interiorE) ResE :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph Subtype.val
    isOpen_interiorE.isOpenEmbedding_subtypeVal

@[simp] theorem interiorEIncl_source : interiorEIncl.source = Set.univ := rfl

@[simp] theorem interiorEIncl_apply (y : ↥interiorE) : interiorEIncl y = (y : ResE) := rfl

/-- **The flat E-interior chart** `↥interiorE → 𝓔³ × ℝ` induced by a `Model`-valued chart of
`ResE`. -/
def eIntChart (c : OpenPartialHomeomorph ResE HModel) : OpenPartialHomeomorph (↥interiorE) FModel :=
  interiorEIncl.trans (flatChart c)

/-- A point of `interiorE` lying in a `PosHt` chart's source lies in the flat chart's source. -/
theorem mem_eIntChart_source {c : OpenPartialHomeomorph ResE HModel} (hc : PosHt c)
    {y : ↥interiorE} (hy : (y : ResE) ∈ c.source) : y ∈ (eIntChart c).source := by
  rw [eIntChart, OpenPartialHomeomorph.trans_source]
  exact ⟨Set.mem_univ _, mem_flatChart_source hy (hc _ hy)⟩

/-- Every point of `↥interiorE` lies in the source of the flat chart of one of the three interior
charts. -/
theorem exists_eIntChart (y : ↥interiorE) :
    ∃ c ∈ atlasEInt, y ∈ (eIntChart c).source := by
  obtain ⟨c, hc, hyc⟩ := exists_interiorChart y.2
  exact ⟨c, hc, mem_eIntChart_source (posHt_of_mem_atlasEInt hc) hyc⟩

open Classical in
/-- **CHART FAMILY 1/3 (interior half) — `↥interiorE` is a charted space on the flat model
`𝓔³ × ℝ`.** The atlas is the three flattened interior charts of the E-side half-space atlas;
`chartAt` dispatches to a covering one. This is the boundaryless replacement of
`instChartedSpaceResE` on the E-piece's interior, and the input the weld atlas's family 1/3
needs. -/
noncomputable instance instChartedSpaceInteriorE : ChartedSpace FModel (↥interiorE) where
  atlas := eIntChart '' atlasEInt
  chartAt y := eIntChart (Classical.choose (exists_eIntChart y))
  mem_chart_source y := (Classical.choose_spec (exists_eIntChart y)).2
  chart_mem_atlas y :=
    ⟨Classical.choose (exists_eIntChart y), (Classical.choose_spec (exists_eIntChart y)).1, rfl⟩

end

end SKEFTHawking.KummerEInteriorChart
