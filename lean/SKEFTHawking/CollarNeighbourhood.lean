/-
Copyright (c) 2026 SK-EFT Hawking project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# The boundary of an `I.prod (𝓡∂ 1)`-manifold, towards the collar neighbourhood theorem

Mathlib's `Mathlib/Geometry/Manifold/Bordism.lean` records that bordism is an equivalence relation
with the parenthetical "*transitivity follows from the collar neighbourhood theorem*", and
`Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean` lists "`boundary M` is a submanifold"
as an open TODO. This file builds, from the bottom up, the substrate for both — for the model that
bordism actually uses: a manifold `W` modelled on `I.prod (𝓡∂ 1)` with `I` boundaryless (`W` is
one dimension up from its ends, with a single half-line direction transverse to the boundary).

Everything is stated at a **free regularity** `n : WithTop ℕ∞` (with the hypothesis `n ≠ 0` where
Mathlib's chart-independence of the boundary requires it); nothing here is special to `n = ∞`, and
nothing here mentions the bordism stack it is meant to feed. It is written to be upstreamable: the
only project-specific thing about it is the enclosing namespace.

## Main definitions

* `SKEFTHawking.Collar.boundarySlice`: the slice of an ambient chart of `W` along `∂W`, as an
  `OpenPartialHomeomorph (∂W) H`.
* `SKEFTHawking.Collar.boundaryChartedSpace`: `∂W` as a charted space over `H`.
* `SKEFTHawking.Collar.hyperplaneIncl`: the inclusion of the boundary's model space as the boundary
  hyperplane of the ambient model space.

## Main results

General `ModelWithCorners` API, for an arbitrary model with corners `J` on an arbitrary charted
space — the missing glue turning Mathlib's chart-independence lemmas, which are phrased against the
*chart's* extended target, into statements about the *model range*:

* `mem_interior_extend_target_iff`, `mem_frontier_range_iff_notMem_interior`
* `isInteriorPoint_iff_mem_interior_range_of_mem_atlas`
* `isBoundaryPoint_iff_mem_frontier_range_of_mem_atlas`

For the model `I.prod (𝓡∂ 1)` with `I` boundaryless:

* `range_prodHalf`, `interior_range_prodHalf`, `frontier_range_prodHalf`: the range, its interior
  and its frontier are the closed, open and degenerate half spaces cut out by the last coordinate.
* `isBoundaryPoint_prodHalf_iff`, `isInteriorPoint_prodHalf_iff`: boundary and interior points are
  detected by the last coordinate of the preferred extended chart.
* `isBoundaryPoint_prodHalf_iff_of_mem_atlas`, `isInteriorPoint_prodHalf_iff_of_mem_atlas`: the
  same detection, in *any* atlas chart. This is what makes `∂W` a well-defined slice of every
  chart, and hence the starting point of the collar construction.
* `boundaryless_boundaryChartedSpace`: the resulting charted space has no boundary of its own.
* `contDiffOn_boundarySlice_trans`: the transition between two boundary slices is the ambient
  transition restricted to the boundary hyperplane, hence `C^n`.
* `isManifold_boundary`: **`∂W` is a `C^n` manifold modelled on `I`** — the "boundary is a
  submanifold" prerequisite, for the model bordism uses.
* `isClosed_boundary_prodHalf`, `compactSpace_boundary`: `∂W` is closed, and compact when `W` is.
  Compactness of `∂W` is what makes the local collars uniform.

## TODO — the collar itself, and the state of Mathlib underneath it

What remains is the classical globalisation: an inward-pointing vector field near `∂W` built from
a partition of unity over boundary charts, and its uniform-time flow. Two independent gaps in the
current Mathlib sit under that step; both are upstreamable in their own right.

1. **Flow from the boundary.** `exists_isMIntegralCurveAt_of_contMDiffAt` requires
   `I.IsInteriorPoint x₀`, and *every* global / uniform-time result in
   `Mathlib/Geometry/Manifold/IntegralCurve/UniformTime.lean` carries `[BoundarylessManifold I M]`.
   Flowing out of a boundary point is Mathlib's own recorded TODO in
   `Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean` ("the case where the integral curve
   may venture to the boundary of the manifold. See Theorem 9.34, Lee. May require submanifolds").
   Closing it needs Picard–Lindelöf on `Ici 0` in the model half space, then the manifold-level
   statement.

2. **Partitions of unity at finite regularity.** Mathlib's are `C^∞`-only:
   `SmoothPartitionOfUnity` is valued in `C^∞⟮I, M; 𝓘(ℝ), ℝ⟯` and
   `SmoothPartitionOfUnity.exists_isSubordinate` proceeds through
   `BumpCovering.exists_isSubordinate_of_prop (ContMDiff I 𝓘(ℝ) ∞)`; the smoothness of a
   `SmoothBumpFunction` on `M` lives under `variable [IsManifold I ∞ M]`. Nothing about
   *boundarylessness* is assumed — partitions of unity work fine on manifolds with boundary, and
   only need `[FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]` — but a `C^k` partition
   of unity for finite `k` does not exist in the library and would have to be built (the standard
   bump is `C^∞` in a chart, so it is a `C^k` function on a `C^k` manifold; that generalisation is
   the missing piece).

Neither gap is about boundary *detection*, which is what this file supplies.
-/

open Set Function
open scoped Topology Manifold

namespace SKEFTHawking.Collar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-! ### General `ModelWithCorners` API: interior/frontier of a chart target vs. of the model range

These two lemmas are stated for an arbitrary model with corners; they are the missing glue that
turns Mathlib's chart-independence lemmas (`ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`,
`ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas`), which are phrased in terms of the *chart's*
extended target, into statements about the *model range* — the form in which the model range is
computable. -/

section GeneralModel

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

omit [ChartedSpace H' M] in
/-- For a chart `f` and a point `x` of its source, the extended chart image `J (f x)` lies in the
interior of the extended target iff it lies in the interior of the model range. -/
theorem mem_interior_extend_target_iff {f : OpenPartialHomeomorph M H'} {x : M}
    (hx : x ∈ f.source) :
    f.extend J x ∈ interior (f.extend J).target ↔ f.extend J x ∈ interior (range J) :=
  ⟨fun h ↦ OpenPartialHomeomorph.interior_extend_target_subset_interior_range _ h,
    fun h ↦ f.mem_interior_extend_target (f.map_source hx) h⟩

/-- A point of the model range lies in the frontier of the range exactly when it is not an
interior point of the range (the range of a model with corners is closed). -/
theorem mem_frontier_range_iff_notMem_interior (y : H') :
    J y ∈ frontier (range J) ↔ J y ∉ interior (range J) := by
  rw [J.isClosed_range.frontier_eq, mem_diff]
  simp

/-- Chart-independent detection of interior points, phrased against the **model range**. -/
theorem isInteriorPoint_iff_mem_interior_range_of_mem_atlas {n : WithTop ℕ∞} [IsManifold J n M]
    (hn : n ≠ 0) {f : OpenPartialHomeomorph M H'} (hf : f ∈ atlas H' M) {x : M}
    (hx : x ∈ f.source) :
    J.IsInteriorPoint x ↔ J (f x) ∈ interior (range J) :=
  (J.isInteriorPoint_iff_of_mem_atlas hn hf hx).trans (mem_interior_extend_target_iff hx)

/-- Chart-independent detection of boundary points, phrased against the **model range**. -/
theorem isBoundaryPoint_iff_mem_frontier_range_of_mem_atlas {n : WithTop ℕ∞} [IsManifold J n M]
    (hn : n ≠ 0) {f : OpenPartialHomeomorph M H'} (hf : f ∈ atlas H' M) {x : M}
    (hx : x ∈ f.source) :
    J.IsBoundaryPoint x ↔ J (f x) ∈ frontier (range J) := by
  rw [mem_frontier_range_iff_notMem_interior,
    ← isInteriorPoint_iff_mem_interior_range_of_mem_atlas hn hf hx,
    J.isBoundaryPoint_iff_not_isInteriorPoint]

end GeneralModel

/-! ### The model `I.prod (𝓡∂ 1)` -/

section ModelRange

variable (I : ModelWithCorners ℝ E H) [I.Boundaryless]

/-- The range of the "one more half-line" model `I.prod (𝓡∂ 1)` is the closed half space
cut out by the sign of the last coordinate. -/
theorem range_prodHalf :
    range (I.prod (𝓡∂ 1)) = {p : E × EuclideanSpace ℝ (Fin 1) | 0 ≤ p.2 0} := by
  rw [ModelWithCorners.range_prod, I.range_eq_univ, range_modelWithCornersEuclideanHalfSpace]
  ext p; simp

/-- The interior of the range of `I.prod (𝓡∂ 1)` is the open half space. -/
theorem interior_range_prodHalf :
    interior (range (I.prod (𝓡∂ 1))) = {p : E × EuclideanSpace ℝ (Fin 1) | 0 < p.2 0} := by
  rw [ModelWithCorners.range_prod, I.range_eq_univ, interior_prod_eq, interior_univ,
    interior_range_modelWithCornersEuclideanHalfSpace]
  ext p; simp

/-- The frontier of the range of `I.prod (𝓡∂ 1)` is the hyperplane `last coordinate = 0`. -/
theorem frontier_range_prodHalf :
    frontier (range (I.prod (𝓡∂ 1))) = {p : E × EuclideanSpace ℝ (Fin 1) | p.2 0 = 0} := by
  rw [ModelWithCorners.range_prod, I.range_eq_univ, frontier_prod_eq, frontier_univ, closure_univ,
    frontier_range_modelWithCornersEuclideanHalfSpace]
  ext p; simp [eq_comm]

end ModelRange

/-! ### Boundary and interior points, detected by the last model coordinate -/

section BoundaryPoints

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {W : Type*} [TopologicalSpace W] [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]

/-- A point of an `I.prod (𝓡∂ 1)`-manifold is a boundary point exactly when the preferred
extended chart sends it to the hyperplane `last coordinate = 0`. -/
theorem isBoundaryPoint_prodHalf_iff (x : W) :
    (I.prod (𝓡∂ 1)).IsBoundaryPoint x ↔ (extChartAt (I.prod (𝓡∂ 1)) x x).2 0 = 0 := by
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_prodHalf]; rfl

/-- A point of an `I.prod (𝓡∂ 1)`-manifold is an interior point exactly when the preferred
extended chart sends it strictly inside the half space. -/
theorem isInteriorPoint_prodHalf_iff (x : W) :
    (I.prod (𝓡∂ 1)).IsInteriorPoint x ↔ 0 < (extChartAt (I.prod (𝓡∂ 1)) x x).2 0 := by
  rw [ModelWithCorners.IsInteriorPoint, interior_range_prodHalf]; rfl

/-- **Chart-independent boundary detection.** In a `C^n` manifold (`n ≠ 0`) modelled on
`I.prod (𝓡∂ 1)`, a point in the source of *any* atlas chart `e` is a boundary point exactly when
the last coordinate of `e x` vanishes. This is the fact that makes the boundary a well-defined
slice of every chart, and hence the starting point of the collar construction. -/
theorem isBoundaryPoint_prodHalf_iff_of_mem_atlas {n : WithTop ℕ∞}
    [IsManifold (I.prod (𝓡∂ 1)) n W] (hn : n ≠ 0)
    {e : OpenPartialHomeomorph W (ModelProd H (EuclideanHalfSpace 1))}
    (he : e ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W) {x : W} (hx : x ∈ e.source) :
    (I.prod (𝓡∂ 1)).IsBoundaryPoint x ↔ (e x).2.1 0 = 0 := by
  rw [isBoundaryPoint_iff_mem_frontier_range_of_mem_atlas hn he hx, frontier_range_prodHalf]
  rfl

/-- **Chart-independent interior detection**, the companion of
`isBoundaryPoint_prodHalf_iff_of_mem_atlas`. -/
theorem isInteriorPoint_prodHalf_iff_of_mem_atlas {n : WithTop ℕ∞}
    [IsManifold (I.prod (𝓡∂ 1)) n W] (hn : n ≠ 0)
    {e : OpenPartialHomeomorph W (ModelProd H (EuclideanHalfSpace 1))}
    (he : e ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W) {x : W} (hx : x ∈ e.source) :
    (I.prod (𝓡∂ 1)).IsInteriorPoint x ↔ 0 < (e x).2.1 0 := by
  rw [isInteriorPoint_iff_mem_interior_range_of_mem_atlas hn he hx, interior_range_prodHalf]
  rfl

end BoundaryPoints

/-! ### The boundary as a charted space over `H` -/

section BoundaryChart

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {W : Type*} [TopologicalSpace W] [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]

/-- A point of `EuclideanHalfSpace 1` is the origin as soon as its single coordinate vanishes. -/
theorem euclideanHalfSpace_one_eq_zero {y : EuclideanHalfSpace 1} (hy : y.1 0 = 0) :
    y = (0 : EuclideanHalfSpace 1) := by
  ext i; fin_cases i; simpa using hy

variable {n : WithTop ℕ∞} [IsManifold (I.prod (𝓡∂ 1)) n W]

/-- On the boundary, every atlas chart has vanishing last coordinate. -/
theorem chart_snd_eq_zero_of_mem_boundary (hn : n ≠ 0)
    {e : OpenPartialHomeomorph W (ModelProd H (EuclideanHalfSpace 1))}
    (he : e ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W) {x : W} (hx : x ∈ e.source)
    (hb : x ∈ (I.prod (𝓡∂ 1)).boundary W) :
    (e x).2 = (0 : EuclideanHalfSpace 1) :=
  euclideanHalfSpace_one_eq_zero
    ((isBoundaryPoint_prodHalf_iff_of_mem_atlas hn he hx).mp hb)

/-- On the boundary, an ambient chart is recovered from its `H`-component alone. -/
theorem chart_apply_eq_of_mem_boundary (hn : n ≠ 0)
    {e : OpenPartialHomeomorph W (ModelProd H (EuclideanHalfSpace 1))}
    (he : e ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W) {x : W} (hx : x ∈ e.source)
    (hb : x ∈ (I.prod (𝓡∂ 1)).boundary W) :
    (((e x).1, 0) : ModelProd H (EuclideanHalfSpace 1)) = e x :=
  Prod.ext rfl (chart_snd_eq_zero_of_mem_boundary hn he hx hb).symm

/-- Conversely, a chart preimage of a point with vanishing last coordinate is a boundary point. -/
theorem mem_boundary_of_chart_snd_eq_zero (hn : n ≠ 0)
    {e : OpenPartialHomeomorph W (ModelProd H (EuclideanHalfSpace 1))}
    (he : e ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W) {h : H}
    (hb : ((h, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target) :
    e.symm (h, 0) ∈ (I.prod (𝓡∂ 1)).boundary W := by
  have hs := e.map_target hb
  have hr := e.right_inv hb
  exact (isBoundaryPoint_prodHalf_iff_of_mem_atlas hn he hs).mpr (by rw [hr]; rfl)

open scoped Classical in
/-- **The boundary slice of an ambient chart**, as an open partial homeomorphism from the boundary
of `W` to the model space `H` of the boundary.

`e` is an ambient chart of `W` (modelled on `H × EuclideanHalfSpace 1`) and `y₀` is a base point of
the boundary, used only as the junk value of the inverse outside the target (a `PartialEquiv`
demands a total inverse, and the boundary can be empty). -/
noncomputable def boundarySlice (hn : n ≠ 0)
    (e : OpenPartialHomeomorph W (ModelProd H (EuclideanHalfSpace 1)))
    (he : e ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W)
    (y₀ : (I.prod (𝓡∂ 1)).boundary W) :
    OpenPartialHomeomorph ((I.prod (𝓡∂ 1)).boundary W) H where
  toFun y := (e y.1).1
  invFun h :=
    ⟨if ((h, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target then e.symm (h, 0) else y₀.1, by
      split_ifs with hb
      · exact mem_boundary_of_chart_snd_eq_zero hn he hb
      · exact y₀.2⟩
  source := Subtype.val ⁻¹' e.source
  target := {h : H | ((h, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target}
  map_source' x hx := by
    show (((e x.1).1, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target
    rw [chart_apply_eq_of_mem_boundary hn he hx x.2]
    exact e.map_source hx
  map_target' h hb := by
    have hb' : ((h, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target := hb
    show (if ((h, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target then e.symm (h, 0) else y₀.1)
      ∈ e.source
    rw [if_pos hb']
    exact e.map_target hb'
  left_inv' x hx := by
    have hb : (((e x.1).1, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target := by
      rw [chart_apply_eq_of_mem_boundary hn he hx x.2]; exact e.map_source hx
    apply Subtype.ext
    show (if (((e x.1).1, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target then
      e.symm ((e x.1).1, 0) else y₀.1) = x.1
    rw [if_pos hb, chart_apply_eq_of_mem_boundary hn he hx x.2, e.left_inv hx]
  right_inv' h hb := by
    have hb' : ((h, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target := hb
    show (e (if ((h, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target then
      e.symm (h, 0) else y₀.1)).1 = h
    rw [if_pos hb', e.right_inv hb']
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage (by fun_prop)
  continuousOn_toFun :=
    ContinuousOn.fst (e.continuousOn.comp continuous_subtype_val.continuousOn fun _ hz => hz)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr
      (e.continuousOn_symm.comp (by fun_prop) fun _ hh => hh) fun h hh => ?_
    exact if_pos (show ((h, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target from hh)

@[simp] theorem boundarySlice_source (hn : n ≠ 0)
    {e : OpenPartialHomeomorph W (ModelProd H (EuclideanHalfSpace 1))}
    (he : e ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W)
    (y₀ : (I.prod (𝓡∂ 1)).boundary W) :
    (boundarySlice hn e he y₀).source = Subtype.val ⁻¹' e.source := rfl

@[simp] theorem boundarySlice_target (hn : n ≠ 0)
    {e : OpenPartialHomeomorph W (ModelProd H (EuclideanHalfSpace 1))}
    (he : e ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W)
    (y₀ : (I.prod (𝓡∂ 1)).boundary W) :
    (boundarySlice hn e he y₀).target =
      {h : H | ((h, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target} := rfl

@[simp] theorem boundarySlice_apply (hn : n ≠ 0)
    {e : OpenPartialHomeomorph W (ModelProd H (EuclideanHalfSpace 1))}
    (he : e ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W)
    (y₀ y : (I.prod (𝓡∂ 1)).boundary W) :
    boundarySlice hn e he y₀ y = (e y.1).1 := rfl

theorem boundarySlice_symm_apply (hn : n ≠ 0)
    {e : OpenPartialHomeomorph W (ModelProd H (EuclideanHalfSpace 1))}
    (he : e ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W)
    (y₀ : (I.prod (𝓡∂ 1)).boundary W) {h : H}
    (hh : ((h, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target) :
    ((boundarySlice hn e he y₀).symm h : W) = e.symm (h, 0) := if_pos hh

variable (I W) in
/-- **The boundary of a `C^n` manifold modelled on `I.prod (𝓡∂ 1)` is a charted space over `H`.**

This is one half of "the boundary is a submanifold", which Mathlib lists as an open TODO in
`Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean`, and the first prerequisite of the
collar neighbourhood theorem (`Mathlib/Geometry/Manifold/Bordism.lean`: "transitivity follows
from the collar neighbourhood theorem").

It is a `def` rather than an `instance` because it depends on the hypothesis `n ≠ 0`: at `n = 0`
the chart-independence of the boundary is not available (Mathlib proves it only for `C^1` and
above), so the construction genuinely needs the regularity. -/
@[reducible] noncomputable def boundaryChartedSpace (hn : n ≠ 0) :
    ChartedSpace H ((I.prod (𝓡∂ 1)).boundary W) where
  atlas := range fun x : (I.prod (𝓡∂ 1)).boundary W =>
    boundarySlice hn (chartAt (ModelProd H (EuclideanHalfSpace 1)) x.1) (chart_mem_atlas _ _) x
  chartAt x :=
    boundarySlice hn (chartAt (ModelProd H (EuclideanHalfSpace 1)) x.1) (chart_mem_atlas _ _) x
  mem_chart_source x := mem_chart_source _ x.1
  chart_mem_atlas x := mem_range_self x

/-- The boundary, charted over `H` via `boundaryChartedSpace`, is a **boundaryless** charted
space — it has no corners of its own. -/
theorem boundaryless_boundaryChartedSpace (hn : n ≠ 0) :
    letI := boundaryChartedSpace I W hn
    I.boundary ((I.prod (𝓡∂ 1)).boundary W) = ∅ := by
  letI := boundaryChartedSpace I W hn
  exact ModelWithCorners.Boundaryless.boundary_eq_empty

end BoundaryChart

/-! ### The boundary slices are `C^n`-compatible -/

section BoundaryManifold

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {W : Type*} [TopologicalSpace W] [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]
  {n : WithTop ℕ∞} [IsManifold (I.prod (𝓡∂ 1)) n W]

/-- The inverse of the half-line model sends the origin to the origin. -/
@[simp] theorem modelWithCornersEuclideanHalfSpace_one_symm_zero :
    (𝓡∂ 1).symm (0 : EuclideanSpace ℝ (Fin 1)) = (0 : EuclideanHalfSpace 1) := by
  simp [modelWithCornersEuclideanHalfSpace]; rfl

omit [I.Boundaryless] in
/-- The inverse of the bordism model on the boundary hyperplane. -/
theorem prodHalf_symm_zero (v : E) :
    (I.prod (𝓡∂ 1)).symm ((v, 0) : E × EuclideanSpace ℝ (Fin 1)) =
      ((I.symm v, 0) : ModelProd H (EuclideanHalfSpace 1)) := by
  simp

/-- The inclusion of the model space of the boundary as the boundary hyperplane of the ambient
model space. -/
def hyperplaneIncl (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E → E × EuclideanSpace ℝ (Fin 1) := fun v => (v, 0)

theorem contDiff_hyperplaneIncl {m : WithTop ℕ∞} : ContDiff ℝ m (hyperplaneIncl E) :=
  contDiff_id.prodMk contDiff_const

/-- The boundary hyperplane lands in the model range. -/
theorem hyperplaneIncl_mem_range (I : ModelWithCorners ℝ E H) [I.Boundaryless] (v : E) :
    hyperplaneIncl E v ∈ range (I.prod (𝓡∂ 1)) := by
  rw [range_prodHalf]
  simp [hyperplaneIncl]

/-- **The boundary slices are `C^n`-compatible**: the transition between two boundary slices is
the ambient transition restricted to the boundary hyperplane, hence `C^n`. -/
theorem contDiffOn_boundarySlice_trans (hn : n ≠ 0)
    {e e' : OpenPartialHomeomorph W (ModelProd H (EuclideanHalfSpace 1))}
    (he : e ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W)
    (he' : e' ∈ atlas (ModelProd H (EuclideanHalfSpace 1)) W)
    (y₀ y₀' : (I.prod (𝓡∂ 1)).boundary W) :
    ContDiffOn ℝ n
      (I ∘ ((boundarySlice hn e he y₀).symm ≫ₕ boundarySlice hn e' he' y₀') ∘ I.symm)
      (I.symm ⁻¹' ((boundarySlice hn e he y₀).symm ≫ₕ boundarySlice hn e' he' y₀').source ∩
        range I) := by
  have hcomp : e.symm ≫ₕ e' ∈ contDiffGroupoid n (I.prod (𝓡∂ 1)) :=
    HasGroupoid.compatible he he'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hcomp
  have hamb := hcomp.1
  have key : ∀ v ∈ I.symm ⁻¹'
      ((boundarySlice hn e he y₀).symm ≫ₕ boundarySlice hn e' he' y₀').source ∩ range I,
      ((I.symm v, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e.target ∧
        e.symm ((I.symm v, 0) : ModelProd H (EuclideanHalfSpace 1)) ∈ e'.source := by
    rintro v ⟨hv, -⟩
    simp only [mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, boundarySlice_target, mem_inter_iff,
      mem_setOf_eq] at hv
    obtain ⟨hv1, hv2⟩ := hv
    refine ⟨hv1, ?_⟩
    rw [← boundarySlice_symm_apply hn he y₀ hv1]
    exact hv2
  have hmaps : MapsTo (hyperplaneIncl E)
      (I.symm ⁻¹' ((boundarySlice hn e he y₀).symm ≫ₕ boundarySlice hn e' he' y₀').source ∩
        range I)
      ((I.prod (𝓡∂ 1)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range (I.prod (𝓡∂ 1))) := by
    intro v hv
    obtain ⟨h1, h2⟩ := key v hv
    refine ⟨?_, hyperplaneIncl_mem_range I v⟩
    simp only [mem_preimage, hyperplaneIncl, prodHalf_symm_zero,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, mem_inter_iff]
    exact ⟨h1, h2⟩
  refine ContDiffOn.congr
    (contDiff_fst.comp_contDiffOn (hamb.comp contDiff_hyperplaneIncl.contDiffOn hmaps)) ?_
  intro v hv
  obtain ⟨h1, -⟩ := key v hv
  simp only [Function.comp_apply, hyperplaneIncl, prodHalf_symm_zero,
    OpenPartialHomeomorph.coe_trans, boundarySlice_apply, modelWithCorners_prod_coe]
  rw [boundarySlice_symm_apply hn he y₀ h1]
  rfl

variable (I W) in
/-- **The boundary of a `C^n` manifold modelled on `I.prod (𝓡∂ 1)` is itself a `C^n` manifold**,
modelled on `I` — one dimension down, and boundaryless.

Together with `boundaryChartedSpace` and `boundaryless_boundaryChartedSpace` this is the
"boundary is a submanifold" prerequisite of the collar neighbourhood theorem, for the model that
bordism uses. Mathlib lists it as an open TODO in
`Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean`.

The regularity `n` is free; the hypothesis `n ≠ 0` is genuinely load-bearing, since the
chart-independence of the boundary that makes the slices well-defined is only available from
`C^1` up. -/
theorem isManifold_boundary (hn : n ≠ 0) :
    letI := boundaryChartedSpace I W hn
    IsManifold I n ((I.prod (𝓡∂ 1)).boundary W) := by
  letI := boundaryChartedSpace I W hn
  refine isManifold_of_contDiffOn I n _ ?_
  rintro f f' ⟨x, rfl⟩ ⟨x', rfl⟩
  exact contDiffOn_boundarySlice_trans hn _ _ x x'

omit [I.Boundaryless] in
/-- The boundary is a closed subset of `W`. (A re-export of
`ModelWithCorners.isClosed_boundary` at the bordism model, recorded here because the collar
construction uses it twice: to get compactness of `∂W`, and as the closed set a subordinate
partition of unity is built over.) -/
theorem isClosed_boundary_prodHalf (hn : n ≠ 0) :
    IsClosed ((I.prod (𝓡∂ 1)).boundary W) :=
  ModelWithCorners.isClosed_boundary hn

omit [I.Boundaryless] in
/-- **The boundary of a compact bordism-model manifold is compact.** This is where the compactness
hypothesis of the collar neighbourhood theorem enters: it is what turns the pointwise local
collars into a *uniform* one. -/
theorem compactSpace_boundary [CompactSpace W] (hn : n ≠ 0) :
    CompactSpace ((I.prod (𝓡∂ 1)).boundary W) :=
  isCompact_iff_compactSpace.mp (isClosed_boundary_prodHalf hn).isCompact

end BoundaryManifold

end SKEFTHawking.Collar
