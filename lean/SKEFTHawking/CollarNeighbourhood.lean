/-
Copyright (c) 2026 SK-EFT Hawking project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Towards the collar neighbourhood theorem: the boundary of an `I.prod (𝓡∂ 1)`-manifold

Placeholder header; filled in once the section content settles.
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

end SKEFTHawking.Collar
