/-
# Phase 5q.H — K4′′ packaging: the boundary charts of `T⁴°` (manifold-with-boundary)

This module assembles deliverable (1) of the K4′′ certificate (see `KummerShellChart.lean` §C): the
**16 boundary collar charts** of the punctured torus `T⁴° = ↥puncturedTorus`, each an
`OpenPartialHomeomorph (↥puncturedTorus) ((𝓡 3).prod (𝓡∂ 1))` charting a neighborhood of a boundary
sphere onto the half-space model.

The construction is **purely compositional** (the predecessor's key point in §C): the boundary chart is
```
  shellCollarChart u₀ ∘ (↥shellSetE4 ↪ ExtShell) ∘ (collarHomeo c).symm
```
lifted along the open embedding `↥(collarSet c) ↪ ↥puncturedTorus` via
`OpenPartialHomeomorph.lift_openEmbedding` — every source/target/continuity/openness obligation is
discharged by the `OpenPartialHomeomorph` combinators (`.trans`, `Homeomorph.toOpenPartialHomeomorph`,
`IsOpenEmbedding.toOpenPartialHomeomorph`, `lift_openEmbedding`). No bespoke junk-value or subtype
open-map argument remains.

The single genuine geometric obligation is that the collar `collarSet c` — which includes the boundary
sphere `‖w‖ = 1/2`, so it is **not** open in `T⁴` — is nonetheless **relatively open in
`puncturedTorus`** (`collarSet_relopen`): on the punctured side, membership in the collar coincides with
membership in the open extended-chart ball `(centeredChartParamE4 c).target`. This mirrors
`shellImage_mem_puncturedTorus`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerShellChart

open Metric Set
open scoped Manifold

namespace SKEFTHawking.KummerBoundaryChart

open SKEFTHawking.KummerShellChart
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerK3Base
open SKEFTHawking.DiskChartGeneric (NSphere)

noncomputable section

/-- The half-space boundary model `(𝓡 3).prod (𝓡∂ 1) = ModelProd (E³) (HalfSpace¹)`. -/
abbrev Model : Type := ModelProd (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 1)

/-! ### §1. The collar is relatively open in `puncturedTorus` -/

/-- On the punctured side, membership in `collarSet c` coincides with membership in the open
extended-chart ball image `(centeredChartParamE4 c).target`. Forward: `shellSetE4 ⊆ {‖w‖ < 3/4}`.
Backward: a chart-ball preimage with `‖w‖ < 1/2` would land in `chartBall c ⊆ excisedBalls`, contradicting
`y ∈ puncturedTorus`. -/
theorem mem_collarSet_iff_of_punctured {c : TorusFour} (hc : c ∈ fixedSet) (y : ↥puncturedTorus) :
    (y : TorusFour) ∈ collarSet c ↔ (y : TorusFour) ∈ (centeredChartParamE4 c).target := by
  constructor
  · rintro ⟨w, hw, heq⟩
    exact ⟨w, hw.2, heq⟩
  · rintro ⟨w, hw, hwy⟩
    by_cases h : ‖w‖ < (1 : ℝ) / 2
    · exfalso
      have hmem : (y : TorusFour) ∈ chartBall c := by
        rw [← hwy]
        refine ⟨ofE4 w, ?_, rfl⟩
        rw [Set.mem_setOf_eq, sqNorm_ofE4, show excisionRadius = (1 : ℝ) / 2 from rfl]
        nlinarith [norm_nonneg w, h]
      have hexc : (y : TorusFour) ∈ excisedBalls := Set.mem_biUnion hc hmem
      exact (y.2) hexc
    · exact ⟨w, ⟨not_lt.mp h, hw⟩, hwy⟩

/-- **The collar is relatively open in `puncturedTorus`.** Although `collarSet c` contains the boundary
sphere `‖w‖ = 1/2` and so is not open in `T⁴`, its trace on `puncturedTorus` equals the trace of the open
ball `(centeredChartParamE4 c).target`. -/
theorem collarSet_relopen {c : TorusFour} (hc : c ∈ fixedSet) :
    IsOpen (Subtype.val ⁻¹' (collarSet c) : Set ↥puncturedTorus) := by
  have hset : (Subtype.val ⁻¹' (collarSet c) : Set ↥puncturedTorus)
      = Subtype.val ⁻¹' (centeredChartParamE4 c).target := by
    ext y
    simp only [Set.mem_preimage]
    exact mem_collarSet_iff_of_punctured hc y
  rw [hset]
  exact (centeredChartParamE4 c).open_target.preimage continuous_subtype_val

/-! ### §2. The two open embeddings feeding the composition -/

/-- The inclusion `↥(collarSet c) ↪ ↥puncturedTorus` is an open embedding (relative openness). -/
theorem isOpenEmbedding_collarIncl {c : TorusFour} (hc : c ∈ fixedSet) :
    Topology.IsOpenEmbedding (Set.inclusion (collarSet_subset_puncturedTorus hc)) :=
  Topology.IsOpenEmbedding.inclusion (collarSet_subset_puncturedTorus hc) (collarSet_relopen hc)

/-- The inclusion `↥shellSetE4 ↪ ExtShell` (a shell-band point is a shell point). -/
def shellIncl : ↥shellSetE4 → ExtShell := Set.inclusion (fun _ hw => hw.1)

/-- `shellSetE4` is open in `ExtShell` (its trace is `{‖v‖ < 3/4}`; the `1/2 ≤ ‖v‖` half is automatic). -/
theorem isOpen_shellSetE4_in_ExtShell : IsOpen (Subtype.val ⁻¹' shellSetE4 : Set ExtShell) := by
  have hset : (Subtype.val ⁻¹' shellSetE4 : Set ExtShell)
      = {v : ExtShell | ‖(v : EuclideanSpace ℝ (Fin 4))‖ < 3 / 4} := by
    ext v
    simp only [Set.mem_preimage, shellSetE4, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨v.2, h⟩⟩
  rw [hset]
  exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

/-- The inclusion `↥shellSetE4 ↪ ExtShell` is an open embedding. -/
theorem isOpenEmbedding_shellIncl :
    Topology.IsOpenEmbedding shellIncl :=
  Topology.IsOpenEmbedding.inclusion (fun _ hw => hw.1) isOpen_shellSetE4_in_ExtShell

/-- `shellSetE4` is nonempty (witness `‖·‖ = 3/5 ∈ [1/2, 3/4)`) — needed to convert the shell open
embedding into an `OpenPartialHomeomorph` (its inverse needs a junk value off the range). -/
instance instNonemptyShellSetE4 : Nonempty ↥shellSetE4 :=
  ⟨⟨EuclideanSpace.single (0 : Fin 4) (3 / 5 : ℝ), by
    have hn : ‖EuclideanSpace.single (0 : Fin 4) (3 / 5 : ℝ)‖ = 3 / 5 := by
      rw [PiLp.norm_single, Real.norm_eq_abs]; norm_num
    rw [show shellSetE4 = {w | (1 : ℝ) / 2 ≤ ‖w‖ ∧ ‖w‖ < 3 / 4} from rfl, Set.mem_setOf_eq, hn]
    norm_num⟩⟩

/-! ### §3. The boundary collar chart (compositional) -/

/-- **The inner boundary chart** `↥(collarSet c) → Model`: `shellCollarChart u₀ ∘ (↥shellSetE4 ↪
ExtShell) ∘ (collarHomeo c).symm`, all as `OpenPartialHomeomorph`s composed by `.trans`. -/
def innerCollarChart (c : TorusFour) (u₀ : NSphere 3) :
    OpenPartialHomeomorph (↥(collarSet c)) Model :=
  ((collarHomeo c).symm.toOpenPartialHomeomorph).trans
    ((Topology.IsOpenEmbedding.toOpenPartialHomeomorph shellIncl isOpenEmbedding_shellIncl).trans
      (shellCollarChart u₀))

/-- **The boundary collar chart at `(c, u₀)`** — the `OpenPartialHomeomorph (↥puncturedTorus) Model`
charting the punctured-torus collar of the boundary sphere `chartSphere c` onto the half-space model.
Built by lifting `innerCollarChart` along the open embedding `↥(collarSet c) ↪ ↥puncturedTorus`; its
source is the relatively-open collar and its `IsOpenMap` obligation is discharged compositionally. -/
def boundaryChart (c : TorusFour) (u₀ : NSphere 3) (hc : c ∈ fixedSet) :
    OpenPartialHomeomorph (↥puncturedTorus) Model :=
  (innerCollarChart c u₀).lift_openEmbedding (isOpenEmbedding_collarIncl hc)

/-! ### §4. The interior reshaping `𝔼¹×𝔼¹×𝔼¹×𝔼¹ → 𝔼³ × HalfSpace¹` (into the interior) -/

/-- The ambient product chart model of `T⁴` (the four `Circle` factors), on which the interior of
`T⁴°` is charted (`KummerChartedSpace.interior_chartedSpace`). -/
abbrev PModel : Type := ModelProd (EuclideanSpace ℝ (Fin 1))
  (ModelProd (EuclideanSpace ℝ (Fin 1))
    (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))))

/-- Round-trip: rebuilding `E³` from its three coordinates. -/
theorem toLp_ofLp_fin_three (v : EuclideanSpace ℝ (Fin 3)) :
    (WithLp.toLp 2 ![v.ofLp 0, v.ofLp 1, v.ofLp 2] : EuclideanSpace ℝ (Fin 3)) = v := by
  ext i
  fin_cases i <;> simp

/-- **The interior reshaping** `PModel → Model`: the first three ambient coordinates combine into the
`𝔼³` factor, the fourth maps by `Real.exp` into the strictly-positive ray — the interior of the
half-space. An `OpenPartialHomeomorph` (source `univ`, target `{q | 0 < q.2.val.ofLp 0}` = the interior
region), so composing an ambient product chart with it charts an interior point of `T⁴°` into the
interior of the half-space model, coexisting with the boundary collar charts of §3. -/
def interiorReshape : OpenPartialHomeomorph PModel Model where
  source := Set.univ
  target := {q : Model | 0 < q.2.val.ofLp 0}
  toFun p := (WithLp.toLp 2 ![p.1.ofLp 0, p.2.1.ofLp 0, p.2.2.1.ofLp 0],
    ⟨WithLp.toLp 2 (fun _ : Fin 1 => Real.exp (p.2.2.2.ofLp 0)), by simp; positivity⟩)
  invFun q := (WithLp.toLp 2 (fun _ : Fin 1 => q.1.ofLp 0),
    (WithLp.toLp 2 (fun _ : Fin 1 => q.1.ofLp 1),
      (WithLp.toLp 2 (fun _ : Fin 1 => q.1.ofLp 2),
        WithLp.toLp 2 (fun _ : Fin 1 => Real.log (q.2.val.ofLp 0)))))
  map_source' p _ := by
    show (0 : ℝ) < (WithLp.toLp 2 (fun _ : Fin 1 => Real.exp (p.2.2.2.ofLp 0))).ofLp 0
    simp; positivity
  map_target' _ _ := Set.mem_univ _
  left_inv' p _ := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
      simp [DiskChartGeneric.toLp_ofLp_fin_one]
  right_inv' q hq := by
    have hpos : (0 : ℝ) < q.2.val.ofLp 0 := hq
    refine Prod.ext ?_ ?_
    · show (WithLp.toLp 2 ![q.1.ofLp 0, q.1.ofLp 1, q.1.ofLp 2] : EuclideanSpace ℝ (Fin 3)) = q.1
      · simp [toLp_ofLp_fin_three]
    · apply Subtype.ext
      show WithLp.toLp 2 (fun _ : Fin 1 =>
        Real.exp ((WithLp.toLp 2 (fun _ : Fin 1 => Real.log (q.2.val.ofLp 0))).ofLp 0)) = q.2.val
      rw [show (WithLp.toLp 2 (fun _ : Fin 1 => Real.log (q.2.val.ofLp 0))).ofLp 0
          = Real.log (q.2.val.ofLp 0) from by simp, Real.exp_log hpos]
      exact DiskChartGeneric.toLp_ofLp_fin_one _
  open_source := isOpen_univ
  open_target := by
    apply isOpen_lt continuous_const
    exact (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
      (continuous_subtype_val.comp continuous_snd)
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.prodMk
    · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => ?_))
      fin_cases i <;> simp <;> fun_prop
    · apply Continuous.subtype_mk
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun _ => ?_))
      fun_prop
  continuousOn_invFun := by
    refine ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ ?_))
    · apply Continuous.continuousOn
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun _ => ?_)); fun_prop
    · apply Continuous.continuousOn
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun _ => ?_)); fun_prop
    · apply Continuous.continuousOn
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun _ => ?_)); fun_prop
    · apply (PiLp.continuous_toLp 2 _).comp_continuousOn
      apply continuousOn_pi.mpr
      intro _
      apply Real.continuousOn_log.comp
      · exact ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
          (continuous_subtype_val.comp continuous_snd)).continuousOn
      · intro q hq
        exact ne_of_gt hq

/-! ### §5. The interior charts (the ambient product charts reshaped into the interior) -/

open SKEFTHawking.KummerChartedSpace

/-- The inclusion `↥openPunctured ↪ ↥puncturedTorus` is an open embedding (`openPunctured` is open in
`T⁴` and contained in `T⁴°`). -/
theorem isOpenEmbedding_openPuncturedIncl :
    Topology.IsOpenEmbedding
      (Set.inclusion openPunctured_subset_puncturedTorus :
        ↥openPunctured → ↥puncturedTorus) :=
  Topology.IsOpenEmbedding.inclusion openPunctured_subset_puncturedTorus
    (isOpen_openPuncturedSet.preimage continuous_subtype_val)

/-- **The interior chart at an interior point `x`** — the ambient `T⁴` product chart at `x` reshaped
into the interior of the half-space model by `interiorReshape`, then lifted along the open embedding
`↥openPunctured ↪ ↥puncturedTorus`. An `OpenPartialHomeomorph (↥puncturedTorus) Model` whose image lies
in the interior region `{q | 0 < q.2.val.ofLp 0}`. -/
def interiorChart (x : ↥openPunctured) : OpenPartialHomeomorph (↥puncturedTorus) Model :=
  ((chartAt PModel x).trans interiorReshape).lift_openEmbedding isOpenEmbedding_openPuncturedIncl

/-! ### §6. The covering — the round-ball interior region ∪ the 16 collars ⊇ `T⁴°`

`KummerChartedSpace.openPunctured` excises the **metric** closed balls (radius `1/2`), which is too
much: a point with all four chart coordinates `≈ 1/2` has metric distance `≈ 0.495 < 1/2` (so it is
outside `openPunctured`) yet round chart-radius `≈ 1.0 > 3/4` (so it is outside every collar) — a genuine
coverage gap. The instance therefore uses a **round-ball** interior region `interiorSet` (the complement
of the round CLOSED balls of chart-radius `5/8 ∈ (1/2, 3/4)`), which overlaps the collar band `[1/2, 3/4)`
on `[1/2, 5/8]` and so, together with the collars, covers all of `T⁴°`. -/

/-- The round CLOSED ball of chart-radius `5/8` at `c` — the continuous image of a Euclidean closed
ball, hence compact and closed. -/
def chartClosedBall58 (c : TorusFour) : Set TorusFour :=
  (fun w : EuclideanSpace ℝ (Fin 4) => centeredChartParam c (ofE4 w)) ''
    Metric.closedBall 0 (5 / 8)

theorem isClosed_chartClosedBall58 (c : TorusFour) : IsClosed (chartClosedBall58 c) :=
  ((isCompact_closedBall 0 (5 / 8)).image
    ((continuous_centeredChartParam c).comp continuous_ofE4)).isClosed

/-- **The round-ball interior region** `T⁴ ∖ (16 round closed balls of radius 5/8)`. Open, contained in
`T⁴°`, and (with the collars) covers `T⁴°`. -/
def interiorSet : Set TorusFour := (⋃ c ∈ fixedFinset, chartClosedBall58 c)ᶜ

theorem isOpen_interiorSet : IsOpen interiorSet :=
  (fixedFinset.finite_toSet.isClosed_biUnion fun c _ => isClosed_chartClosedBall58 c).isOpen_compl

/-- The round-ball interior region as an `Opens TorusFour` (the open-submanifold carrier of the
interior charts used by the instance). -/
def interiorOpens : TopologicalSpace.Opens TorusFour := ⟨interiorSet, isOpen_interiorSet⟩

theorem interiorSet_subset_puncturedTorus : interiorSet ⊆ puncturedTorus := by
  intro y hy
  rw [puncturedTorus, Set.mem_compl_iff, excisedBalls, Set.mem_iUnion₂]
  rintro ⟨c, hc, t, ht, rfl⟩
  refine hy ?_
  rw [Set.mem_iUnion₂]
  refine ⟨c, (mem_fixedFinset c).mpr hc, toE4 t, ?_, by simp only [ofE4_toE4]⟩
  rw [Metric.mem_closedBall, dist_zero_right, norm_toE4]
  rw [Set.mem_setOf_eq, show excisionRadius = (1 : ℝ) / 2 from rfl] at ht
  have : Real.sqrt (sqNorm t) < 1 / 2 := by
    rw [show (1 : ℝ) / 2 = Real.sqrt ((1 / 2) ^ 2) from by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (sqNorm_nonneg t) ht
  linarith

/-- **The covering.** Every point of `T⁴°` is either in the round-ball interior region or in one of the
16 collars — the antidote to the metric-ball gap above. -/
theorem punctured_covered {y : TorusFour} (hy : y ∈ puncturedTorus) :
    y ∈ interiorSet ∨ ∃ c ∈ fixedFinset, y ∈ collarSet c := by
  by_cases h : y ∈ interiorSet
  · exact Or.inl h
  · right
    simp only [interiorSet, Set.mem_compl_iff, not_not, Set.mem_iUnion₂] at h
    obtain ⟨c, hcF, w, hw, rfl⟩ := h
    have hw58 : ‖w‖ ≤ 5 / 8 := by rwa [Metric.mem_closedBall, dist_zero_right] at hw
    have hc : c ∈ fixedSet := (mem_fixedFinset c).mp hcF
    refine ⟨c, hcF, w, ⟨?_, by linarith⟩, rfl⟩
    by_contra hlt
    rw [not_le] at hlt
    refine (Set.mem_compl_iff _ _ |>.mp hy) ?_
    rw [excisedBalls, Set.mem_iUnion₂]
    refine ⟨c, hc, ofE4 w, ?_, rfl⟩
    rw [Set.mem_setOf_eq, sqNorm_ofE4, show excisionRadius = (1 : ℝ) / 2 from rfl]
    nlinarith [norm_nonneg w, hlt]

/-! ### §7. The manifold-with-boundary `ChartedSpace` on `T⁴°` -/

/-- The inclusion `↥interiorOpens ↪ ↥puncturedTorus` is an open embedding. -/
theorem isOpenEmbedding_interiorIncl :
    Topology.IsOpenEmbedding (Set.inclusion interiorSet_subset_puncturedTorus :
      ↥interiorOpens → ↥puncturedTorus) :=
  Topology.IsOpenEmbedding.inclusion interiorSet_subset_puncturedTorus
    (isOpen_interiorSet.preimage continuous_subtype_val)

/-- **The interior chart on the round-ball interior region** — the ambient product chart at `x`
reshaped into the interior of the half-space model and lifted to `↥puncturedTorus`. -/
def interiorChartR (x : ↥interiorOpens) : OpenPartialHomeomorph (↥puncturedTorus) Model :=
  ((chartAt PModel x).trans interiorReshape).lift_openEmbedding isOpenEmbedding_interiorIncl

/-- For a non-interior point of `T⁴°`, the covering supplies a collar containing it. -/
theorem exists_collar {y : ↥puncturedTorus} (h : (y : TorusFour) ∉ interiorSet) :
    ∃ c ∈ fixedFinset, (y : TorusFour) ∈ collarSet c :=
  (punctured_covered y.2).resolve_left h

/-- The chosen collar fixed point for a non-interior point. -/
noncomputable def chosenC {y : ↥puncturedTorus} (h : (y : TorusFour) ∉ interiorSet) : TorusFour :=
  (exists_collar h).choose

theorem chosenC_mem {y : ↥puncturedTorus} (h : (y : TorusFour) ∉ interiorSet) :
    chosenC h ∈ fixedSet :=
  (mem_fixedFinset _).mp (exists_collar h).choose_spec.1

theorem mem_collarSet_chosenC {y : ↥puncturedTorus} (h : (y : TorusFour) ∉ interiorSet) :
    (y : TorusFour) ∈ collarSet (chosenC h) :=
  (exists_collar h).choose_spec.2

/-- The collar preimage of `y` as a shell point (via the collar homeomorphism's inverse). -/
noncomputable def chosenShell {y : ↥puncturedTorus} (h : (y : TorusFour) ∉ interiorSet) :
    ↥shellSetE4 :=
  (collarHomeo (chosenC h)).symm ⟨(y : TorusFour), mem_collarSet_chosenC h⟩

/-- The collar chart selected for a non-interior point `y`, with base direction the shell direction of
`y`'s collar preimage (so `y` lands in the base chart's source). -/
noncomputable def bdyChartAt {y : ↥puncturedTorus} (h : (y : TorusFour) ∉ interiorSet) :
    OpenPartialHomeomorph (↥puncturedTorus) Model :=
  boundaryChart (chosenC h) (shellDir (shellIncl (chosenShell h))) (chosenC_mem h)

/-- An interior point lies in the source of its interior chart. -/
theorem mem_interiorChartR_source (x : ↥interiorOpens) :
    (⟨(x : TorusFour), interiorSet_subset_puncturedTorus x.2⟩ : ↥puncturedTorus)
      ∈ (interiorChartR x).source := by
  rw [interiorChartR, OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨x, ?_, rfl⟩
  rw [OpenPartialHomeomorph.trans_source]
  exact ⟨mem_chart_source PModel x, Set.mem_univ _⟩

/-- A non-interior (collar) point lies in the source of its selected collar chart — its shell direction
is the base point of the sphere chart, which contains its own base. -/
theorem mem_bdyChartAt_source {y : ↥puncturedTorus} (h : (y : TorusFour) ∉ interiorSet) :
    y ∈ (bdyChartAt h).source := by
  simp only [bdyChartAt, boundaryChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨⟨(y : TorusFour), mem_collarSet_chosenC h⟩, ?_, rfl⟩
  simp only [innerCollarChart, OpenPartialHomeomorph.trans_source]
  refine ⟨Set.mem_univ _, Set.mem_univ _, ?_⟩
  rw [Set.mem_preimage]
  exact mem_chart_source _ _

open Classical in
/-- **`T⁴° = ↥puncturedTorus` is a charted space on the manifold-with-boundary model
`(𝓡 3).prod (𝓡∂ 1)`** — the K4′′ certificate. The atlas is the round-ball interior charts
(`interiorChartR`, ambient product charts reshaped into the half-space interior) together with the 16
boundary collar chart families (`boundaryChart`). `chartAt` dispatches on membership in the round-ball
interior region; every point is covered (`punctured_covered`). -/
noncomputable instance instChartedSpacePuncturedTorus :
    ChartedSpace Model (↥puncturedTorus) where
  atlas := Set.range interiorChartR ∪
    ⋃ (c : TorusFour) (u₀ : NSphere 3) (_ : c ∈ fixedSet), {boundaryChart c u₀ ‹_›}
  chartAt y :=
    if h : (y : TorusFour) ∈ interiorSet then interiorChartR ⟨(y : TorusFour), h⟩
    else bdyChartAt h
  mem_chart_source y := by
    by_cases h : (y : TorusFour) ∈ interiorSet
    · rw [dif_pos h]; exact mem_interiorChartR_source ⟨(y : TorusFour), h⟩
    · rw [dif_neg h]; exact mem_bdyChartAt_source h
  chart_mem_atlas y := by
    by_cases h : (y : TorusFour) ∈ interiorSet
    · rw [dif_pos h]; exact Or.inl (Set.mem_range_self _)
    · rw [dif_neg h]
      refine Or.inr ?_
      simp only [Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨chosenC h, shellDir (shellIncl (chosenShell h)), chosenC_mem h, rfl⟩

end

end SKEFTHawking.KummerBoundaryChart
