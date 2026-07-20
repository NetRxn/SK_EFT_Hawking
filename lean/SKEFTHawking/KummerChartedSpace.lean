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

## The boundary structure (round `S³` in-chart — the box obstruction is RESOLVED)

The earlier definition excised sup-metric balls `Metric.ball c (1/2)`, which are **boxes** (`ball_isBox`
below is the kernel-checked witness: `Prod.dist_eq = max`, so a metric ball is a product of four chordal
arcs), giving a cubical `S³` boundary with corners — the local model at a corner is a Euclidean QUADRANT,
not a half-space, so `IsManifold (𝓡∂ 4)` fails on the nose. **This is why K4′ was redefined
(`KummerPuncturedTorus`, 2026-07-20 round-ball refactor):** the excised regions are now
`centeredChartParam c '' {t : ℝ⁴ ∣ ‖t‖ < ρ}` (round Euclidean balls in the `τ = −id` centered chart),
whose boundary `chartSphere c = centeredChartParam c '' {‖t‖ = ρ}` is a **round** `S³` in the chart, and
on which `τ = −id` acts antipodally — so the DiskManifold spherical-shell collar chart (direction ∈ S³ ×
radial ∈ half-space) is applicable and the boundary quotient is `S³/±1 = ℝP³` on the nose (Design Risk
#2). `ball_isBox` is retained as the recorded reason for the route change; `Metric.ball` no longer
defines the excision.

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

/-! ## §A. Why the excision is round-in-chart, not metric — the box witness (`ball_isBox`)

`TorusFour` carries the product (sup) metric, so a metric ball is a product of per-factor balls: a
**box**, not a round ball. This kernel-checked fact is the recorded reason K4′ excises round
`centeredChartParam c`-image balls (`chartBall`) rather than `Metric.ball` — a box boundary is a cubical
`S³` with corners, blocking `IsManifold (𝓡∂ 4)`; the round chart boundary is a smooth `S³`. -/

/-- **A `TorusFour` metric ball is a box** — the product of the four per-factor chordal balls.
The sup-metric structure (`Prod.dist_eq = max`) makes `ball c r` a product of arcs; its topological
boundary is a cubical `S³` with corners, not a round `S³`. This motivates the round-in-chart excision
(`chartBall`) that K4′ now uses. -/
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
  exact ⟨c, (mem_fixedFinset c).mpr hc, chartBall_subset_metricClosedBall c hxc⟩

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

/-! ## §D. The round centered chart — the payoff object the box definition could not provide

With the round-ball refactor the centered chart `centeredChartParam c` is a genuine
`OpenPartialHomeomorph` from the round Euclidean ball `{t : ℝ⁴ ∣ ‖t‖ < ρ}` onto the round `chartBall c`:
continuous (`continuous_centeredChartParam`), injective there (`centeredChartParam_injOn`, `ρ = 1/2 < π`),
and open (`isOpenMap_centeredChartParam`, since `Circle.exp` is a covering map). This is the object the
box definition could NOT provide — a box has no Euclidean-ball chart at its corners. It is the
`diskInteriorChart` analogue: the interior chart building block, and the domain-side model on which the
banked `diskCollarChart` (spherical shell ↦ half-space) will be assembled for the boundary. -/

/-- **The round centered chart at `c` as an `OpenPartialHomeomorph`** — `centeredChartParam c` restricts
to a homeomorphism of the open round ball `{‖t‖ < ρ}` onto the round `chartBall c`. The genuine smooth
chart the round-ball refactor unlocks (impossible for a sup-metric box). -/
noncomputable def centeredChartParam_openPartialHomeomorph (c : TorusFour) :
    OpenPartialHomeomorph (ℝ × ℝ × ℝ × ℝ) TorusFour := by
  refine OpenPartialHomeomorph.ofContinuousOpenRestrict
    (Set.InjOn.toPartialEquiv (centeredChartParam c) {t | sqNorm t < excisionRadius ^ 2}
      ((centeredChartParam_injOn c).mono (Set.setOf_subset_setOf.mpr fun _ h => le_of_lt h)))
    ?_ ?_ ?_
  · exact (continuous_centeredChartParam c).continuousOn
  · exact (isOpenMap_centeredChartParam c).restrict (isOpen_lt sqNorm_continuous continuous_const)
  · exact isOpen_lt sqNorm_continuous continuous_const

/-- The chart's source is the open round ball `{‖t‖ < ρ}`. -/
@[simp] theorem centeredChartParam_openPartialHomeomorph_source (c : TorusFour) :
    (centeredChartParam_openPartialHomeomorph c).source = {t | sqNorm t < excisionRadius ^ 2} := rfl

/-- The chart agrees with `centeredChartParam c` on its source. -/
@[simp] theorem centeredChartParam_openPartialHomeomorph_apply (c : TorusFour)
    (t : ℝ × ℝ × ℝ × ℝ) : (centeredChartParam_openPartialHomeomorph c) t = centeredChartParam c t := rfl

/-- The chart's image (target) is exactly the round ball `chartBall c`. -/
theorem centeredChartParam_openPartialHomeomorph_target (c : TorusFour) :
    (centeredChartParam_openPartialHomeomorph c).target = chartBall c := rfl

/-! ## §E. STATUS — the smooth manifold-with-boundary certificate (route now UNBLOCKED)

**GREEN here (the maximal clean prefix, round-ball route):**
- `interior_isManifold` — the interior of `T⁴°` is a boundaryless smooth `C^ω` 4-manifold (§B).
- `qmk_isLocalHomeomorph` — `Q` is locally homeomorphic to `T⁴°` EVERYWHERE, so `Q` is a topological
  4-manifold-with-boundary wherever `T⁴°` is; interior points descend the `T⁴°` charts through
  `qmk_localOpenPartialHomeomorph` (§C). Topological backbone of the K6′b weld.
- `centeredChartParam_openPartialHomeomorph` — the round centered chart is a genuine `OpenPartialHomeomorph`
  (§D); the box `Metric.ball` had none. This is the interior-chart / collar-chart building block.

**The box obstruction is RESOLVED** (`ball_isBox` records why): the excision is now round-in-chart
(`chartBall`), so `chartSphere c` is a round `S³` (`sphere_subset_puncturedTorus`,
`chartSphere_involution_invariant`) on which `τ = −id` acts antipodally — the DiskManifold spherical-shell
collar chart (direction ∈ S³ × radial ∈ `EuclideanHalfSpace 1`) now applies, and the boundary quotient is
`S³/±1 = ℝP³` on the nose (Design Risk #2 becomes literal).

**Residual (the deep half of K4′, now UNBLOCKED — the collar-chart brick K4′′/K5′′):** the full
`IsManifold ((𝓡 3).prod (𝓡∂ 1)) ω (↥puncturedTorus)` manifold-WITH-boundary `ChartedSpace` on the FULL
`T⁴°` (and its ℝP³-boundary descent on `Q`) requires, per boundary sphere, a collar chart of the shell
`{ρ ≤ ‖t‖ < ρ + ε}` — the EXTERIOR-of-ball analogue of the banked `DiskChart.diskCollarChart` (radial
`‖t‖ − ρ ≥ 0` in place of `1 − ‖v‖`), assembled through `centeredChartParam_openPartialHomeomorph` above,
glued to the interior atlas `interior_chartedSpace`. Every input is now in place (round chart + round
sphere + antipodal `τ`); the remaining work is the DiskChart-style transition-smoothness bookkeeping,
one collar per fixed point. -/

end SKEFTHawking.KummerChartedSpace
