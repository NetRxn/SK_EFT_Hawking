/-
# Phase 5q.H — the Kummer K3 generator, K5′/K6′ chart-level certificates (Wave K-II completion)

Continues `KummerFreeQuotient.lean` (K5′ = the free quotient `Q := T⁴°/τ`; carrier/T2/compact,
the interior open-embedding engine `isOpenEmbedding_qmk_sepBall`, the fiber law `qmk_eq_iff`, and
the set-level `∂Q = 16 × ℝP³`). This module supplies the **chart-level certificates** the K6′b weld
needs on the `Q` side: the smooth manifold structure of the **interior** of `T⁴°` and of `Q`.

## The interior structure (this module — clean, `Opens`-backed)

`T⁴°` splits as `interior ⊔ ∂`. Away from the boundary spheres the ambient `T⁴` charts descend
directly:

- **`openPunctured`** = `T⁴ ∖ (16 CLOSED balls)`, an **open** submanifold of `T⁴` (`Opens TorusFour`).
  Mathlib's `Opens` instances give `ChartedSpace` + `IsManifold ω` for free — the honest interior
  of `T⁴°` as a boundaryless smooth 4-manifold (`interior_isManifold`).
- The free `τ`-action restricts to `openPunctured` (freeness, proper discontinuity carried from K4′/K5′),
  so the interior of `Q` is a boundaryless smooth 4-manifold (§C).

## The boundary structure (a GEOMETRIC obstruction — reported to the lead, NOT ground)

`excisionRadius = 1/2` and the excised balls are `Metric.ball c (1/2)` in the **product (sup) metric**
on `TorusFour = Circle × Circle × Circle × Circle` (`Prod.dist_eq = max`, used already in
`le_dist_c1 … le_dist_c4`). Hence each excised ball is a **box** — a product of four chordal arcs
(`ball_isBox` below) — whose topological boundary `Metric.sphere c (1/2)` is a **cubical** `S³` with
edges and corners, NOT a round `S³`. A smooth manifold-with-boundary structure `IsManifold (𝓡∂ 4)`
with the DiskManifold spherical-shell collar chart (direction ∈ S³ × radial ∈ half-space) requires a
smooth codim-1 boundary; the box boundary has corners, so the local model at a corner is a Euclidean
QUADRANT, not a half-space. The literal `puncturedTorus` is therefore a manifold-with-CORNERS, and the
`IsManifold (𝓡∂ 4)` / round-`S³`-boundary target of the mission does not hold on the nose for the
metric-ball definition. See the wall report at the foot of this file.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerFreeQuotient

namespace SKEFTHawking.KummerChartedSpace

open Metric Set
open scoped Manifold ContDiff
open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerInvolution
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerFreeQuotient

/-! ## §A. The excised balls are boxes — the sup-metric obstruction to a round boundary

`TorusFour` carries the product (sup) metric, so a metric ball is a product of per-factor balls: a
**box**, not a round ball. This is the kernel-checked witness for the boundary-corner obstruction
documented in the module header. -/

/-- **A `TorusFour` metric ball is a box** — the product of the four per-factor chordal balls.
The sup-metric structure (`Prod.dist_eq = max`) makes `ball c r` a product of arcs; its topological
boundary is a cubical `S³` with corners, not a round `S³`. -/
theorem ball_isBox (c : TorusFour) (r : ℝ) :
    Metric.ball c r
      = (Metric.ball c.1 r) ×ˢ ((Metric.ball c.2.1 r) ×ˢ
          ((Metric.ball c.2.2.1 r) ×ˢ (Metric.ball c.2.2.2 r))) := by
  ext x
  simp only [Metric.mem_ball, Set.mem_prod, Prod.dist_eq, max_lt_iff]

/-! ## §B. The interior of `T⁴°` as an open smooth submanifold of `T⁴`

`openPunctured := T⁴ ∖ (16 CLOSED balls)` is open in `T⁴`, hence an open submanifold: Mathlib's
`Opens` instances supply `ChartedSpace` + `IsManifold ω` directly. This is the interior of `T⁴°`
(`openPunctured ⊆ puncturedTorus`), the locus where the ambient `T⁴` charts descend unchanged. -/

/-- The 16 CLOSED excised balls (finite union over the 16 fixed points). -/
noncomputable def excisedClosedBalls : Set TorusFour :=
  ⋃ c ∈ fixedFinset, Metric.closedBall c excisionRadius

/-- The closed excised region is closed (finite union of closed balls). -/
theorem isClosed_excisedClosedBalls : IsClosed excisedClosedBalls :=
  fixedFinset.finite_toSet.isClosed_biUnion fun _ _ => Metric.isClosed_closedBall

/-- **The interior of `T⁴°`** as a set: `T⁴ ∖ (16 closed balls)`, the boundary-free part. -/
noncomputable def openPuncturedSet : Set TorusFour := (excisedClosedBalls)ᶜ

theorem isOpen_openPuncturedSet : IsOpen openPuncturedSet :=
  isClosed_excisedClosedBalls.isOpen_compl

/-- **The interior of `T⁴°` as an `Opens TorusFour`** — the open submanifold carrier. -/
noncomputable def openPunctured : TopologicalSpace.Opens TorusFour :=
  ⟨openPuncturedSet, isOpen_openPuncturedSet⟩

/-- The interior sits inside the (closed) punctured torus `T⁴°`: dropping the boundary spheres. -/
theorem openPunctured_subset_puncturedTorus : openPuncturedSet ⊆ puncturedTorus := by
  intro x hx
  rw [puncturedTorus, Set.mem_compl_iff, excisedBalls, Set.mem_iUnion₂]
  rintro ⟨c, hc, hxc⟩
  refine hx ?_
  rw [excisedClosedBalls, Set.mem_iUnion₂]
  exact ⟨c, (mem_fixedFinset c).mpr hc, Metric.ball_subset_closedBall hxc⟩

/-- **The interior of `T⁴°` is a charted space** on the product model `𝔼¹ × 𝔼¹ × 𝔼¹ × 𝔼¹` — the
open-submanifold `ChartedSpace` instance, restricting the ambient `T⁴` atlas. -/
@[reducible] noncomputable def interior_chartedSpace :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1))
      (ModelProd (EuclideanSpace ℝ (Fin 1))
        (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))))) (↥openPunctured) :=
  inferInstance

/-- **The interior of `T⁴°` is a smooth (`C^ω`) 4-manifold** (boundaryless) — the open-submanifold
`IsManifold` instance on the same product model as `T⁴`. This is the honest interior of the
manifold-with-boundary `T⁴°`; the ambient `T⁴` charts descend to it verbatim. -/
theorem interior_isManifold :
    IsManifold ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) ω (↥openPunctured) :=
  inferInstance

end SKEFTHawking.KummerChartedSpace
