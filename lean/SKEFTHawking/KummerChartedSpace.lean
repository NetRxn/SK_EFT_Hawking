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

/-! ## §C. The descent primitive — `qmk` is a local homeomorphism (the covering structure of `Q`)

The mission's interior-chart descent engine (`isOpenEmbedding_qmk_sepBall`) packages into the
`RP4PointSet` `toRP4_localOpenPartialHomeomorph` shape: on each separating ball `qmk` is an
`OpenPartialHomeomorph`, so `qmk : ↥T⁴° ↠ Q` is a **local homeomorphism** (a 2-to-1 covering map).
This is PURELY TOPOLOGICAL — it holds on the WHOLE of `↥T⁴°` (freeness of `τ` holds on the boundary
spheres too), independent of the smooth-boundary question. It is the topological backbone for the
chart descent on both the interior and the boundary of `Q`: `Q` is locally homeomorphic to `T⁴°`
everywhere, so `Q` is a topological 4-manifold-with-boundary wherever `T⁴°` is. -/

/-- **The local `OpenPartialHomeomorph` of `qmk` at `x`** — the separating-ball open embedding
`isOpenEmbedding_qmk_sepBall` packaged as an `OpenPartialHomeomorph ↥T⁴° Q` (the
`toRP4_localOpenPartialHomeomorph` analogue; the reusable interior/boundary chart-descent primitive).
Source `= ball x (sepRadius x)`; `qmk`-image as target; local inverse the `InjOn` section. -/
noncomputable def qmk_localOpenPartialHomeomorph (x : ↥puncturedTorus) :
    OpenPartialHomeomorph (↥puncturedTorus) FreeQuotient := by
  refine OpenPartialHomeomorph.ofContinuousOpenRestrict
    (Set.InjOn.toPartialEquiv qmk (Metric.ball x (sepRadius x)) (qmk_injOn_sepBall x)) ?_ ?_ ?_
  · exact continuous_quotient_mk'.continuousOn
  · exact isOpenMap_qmk.restrict Metric.isOpen_ball
  · exact Metric.isOpen_ball

/-- The source of the local `OpenPartialHomeomorph` at `x` is the separating ball. -/
@[simp] theorem qmk_localOpenPartialHomeomorph_source (x : ↥puncturedTorus) :
    (qmk_localOpenPartialHomeomorph x).source = Metric.ball x (sepRadius x) := rfl

/-- The local `OpenPartialHomeomorph` at `x` agrees with `qmk` on its source. -/
@[simp] theorem qmk_localOpenPartialHomeomorph_apply (x y : ↥puncturedTorus) :
    (qmk_localOpenPartialHomeomorph x) y = qmk y := rfl

/-- Every `x` lies in the source of its own local `OpenPartialHomeomorph` (center of the ball). -/
theorem mem_qmk_localOpenPartialHomeomorph_source (x : ↥puncturedTorus) :
    x ∈ (qmk_localOpenPartialHomeomorph x).source :=
  Metric.mem_ball_self (sepRadius_pos x)

/-- **`qmk : ↥T⁴° ↠ Q` is a local homeomorphism** — the 2-to-1 covering structure of the free
quotient (the `toRP4_isLocalHomeomorph` analogue, one dimension up). Every point of `T⁴°` — interior
OR boundary — has a neighborhood mapped homeomorphically onto its `qmk`-image, so `Q` is locally
homeomorphic to `T⁴°` everywhere. Purely topological (freeness on the whole `T⁴°`), so it is the
chart-descent backbone that survives the boundary-corner question. -/
theorem qmk_isLocalHomeomorph : IsLocalHomeomorph qmk :=
  IsLocalHomeomorph.mk qmk fun x =>
    ⟨qmk_localOpenPartialHomeomorph x, mem_qmk_localOpenPartialHomeomorph_source x, fun _ _ => rfl⟩

/-! ## §D. WALL REPORT — the smooth-boundary target needs an architecture decision (for the lead)

**What lands here (decision-independent, GREEN):**
- `interior_isManifold` — the interior of `T⁴°` is a boundaryless smooth `C^ω` 4-manifold (§B).
- `qmk_isLocalHomeomorph` — `Q` is locally homeomorphic to `T⁴°` EVERYWHERE, so `Q` is a topological
  4-manifold-with-boundary wherever `T⁴°` is; and interior points of `Q` descend the `T⁴°` charts
  through `qmk_localOpenPartialHomeomorph` (§C). This is the topological backbone of the K6′b weld.

**The wall (`ball_isBox`, §A):** `excisedBalls` are `Metric.ball c (1/2)` in the product (sup)
metric, hence BOXES. So `Metric.sphere c (1/2)` (= `boundarySphere c`, the pinned "S³") is a CUBICAL
`S³` with edges/corners, not a round `S³`. Consequences:
  1. A smooth `IsManifold (𝓡∂ 4)` / `((𝓡 3).prod (𝓡∂ 1))` structure with the banked DiskManifold
     spherical-shell collar chart (direction ∈ S³ × radial ∈ half-space) does NOT apply on the nose:
     near a corner the local model is a Euclidean QUADRANT, not a half-space. The literal
     `puncturedTorus` is a manifold-with-CORNERS, not -with-boundary.
  2. The `centeredChartParam c` centered charts do NOT carry the box boundary to a round Euclidean
     sphere (`centeredChartParam` uses `Circle.exp` = arc-length, an isometry of the chart line but
     NOT of the chordal `Circle` metric), so "transport to the standard ℝ⁴-minus-ball model" — the
     mission's collar-chart plan — is not literal.

**Recommended fix (lead decision; a statement change to K4′, so out of this worker's scope):**
Redefine the 16 excised balls as the `centeredChartParam c`-images of ROUND Euclidean balls
`{t : ℝ⁴ | ‖t‖ < ρ}` (a "coordinate ball" in the τ = −id centered chart) instead of the sup-metric
`Metric.ball c (1/2)`. Then (a) the boundary is a round `S³` in the chart, the DiskManifold collar
chart applies, and the smooth `IsManifold (𝓡∂ 4)` target is reachable; (b) the `τ = −id` normal form
(`centeredChartParam_involution`) makes the boundary quotient exactly `S³/±1 = ℝP³` on the nose,
matching K6′a's `∂E ≅ ℝP³` weld presentation (Design Risk #2). The `qmk_isLocalHomeomorph` /
`interior_isManifold` bricks here carry over verbatim; only the excised-region definition and the
disjointness/`sphere_subset` lemmas (currently metric) need re-deriving in chart coordinates.

Until that decision, the smooth manifold-with-boundary ChartedSpace on the FULL `T⁴°`/`Q` (both
`IsManifold` AND a Euclidean-model ChartedSpace instance at the corner/boundary points) is blocked;
the interior smooth structure and the topological covering structure above are the maximal clean
prefix. -/

end SKEFTHawking.KummerChartedSpace
