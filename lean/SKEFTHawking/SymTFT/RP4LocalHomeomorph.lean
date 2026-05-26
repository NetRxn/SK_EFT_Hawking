/-
# Phase 6r-prime M3 Layer B segment B-4a — IsLocalHomeomorph S4.toRP4

This module ships the substantive **`IsLocalHomeomorph S4.toRP4`**
instance for the antipodal-quotient map `S⁴ → RP⁴`. The construction
consumes all the M3 Layer B substrate accumulated in `RP4Smooth.lean`:

- **B-1**: `antipodal_disjoint_open_balls` (parallelogram identity).
- **B-2**: `S4.toRP4_isQuotientMap`, `S4.toRP4_isOpenMap`.
- **B-3**: `S4.toRP4_injOn_ball`.

For each point `a : S⁴`, we construct an `OpenPartialHomeomorph S⁴ RP⁴`
with source `Subtype.val ⁻¹' Metric.ball a 1` (open in `S⁴`), target the
toRP4-image of source (open in `RP⁴` via B-2 `IsOpenMap`), and the
forward/inverse maps via `Set.InjOn.toPartialEquiv` (using B-3 injectivity).

The result `IsLocalHomeomorph S4.toRP4` is the **load-bearing prerequisite
for `IsCoveringMap S4.toRP4` and downstream `ChartedSpace` + `IsManifold`
instances on `RP4`** (M3 Layer B segments B-4b/B-4c).

## Substantive content

- The local-section-via-`InjOn` construction is real geometric content.
- The continuous-inverse-via-open-map argument is real topological
  content: a continuous open bijection between Hausdorff spaces is a
  homeomorphism (specialized here to the restriction to ball ∩ S⁴).
- No new axioms; consumes B-1+B-2+B-3 substrate only.

## Phase 6r-prime M3 Layer B-4a ship

Closes the first substantive step toward full B-4. Subsequent steps
(B-4b: chart atlas with stereographic projection; B-4c: `ChartedSpace
(EuclideanSpace ℝ (Fin 4)) RP4`; B-4d: `IsManifold (𝓡 4) ω RP4`) follow
on this `IsLocalHomeomorph` foundation.

## References

- Mathlib `Mathlib.Topology.IsLocalHomeomorph` (`IsLocalHomeomorph.mk`).
- Mathlib `Mathlib.Topology.OpenPartialHomeomorph.Basic`
  (`OpenPartialHomeomorph.ofContinuousOpenRestrict`).
- Mathlib `Mathlib.Logic.Equiv.PartialEquiv` (`Set.InjOn.toPartialEquiv`).
- Hatcher, *Algebraic Topology*, §1.3.
-/
import SKEFTHawking.SymTFT.RP4Smooth
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace SKEFTHawking.SymTFT

open Metric Topology

universe u

/-! ## §1. Local OpenPartialHomeomorph at each point of S⁴

For each `a : S⁴`, we construct an `OpenPartialHomeomorph S4 RP4` whose
source is the radius-1 ball around `a` (intersected with `S⁴`). -/

/-- `S4` is non-empty (the north-pole basis vector witnesses). Required for
`Set.InjOn.toPartialEquiv`. -/
instance S4.instNonempty : Nonempty S4 := by
  refine ⟨EuclideanSpace.single (0 : Fin 5) (1 : ℝ), ?_⟩
  simp [Metric.mem_sphere, EuclideanSpace.norm_single]

/-- **The local PartialEquiv at `a : S⁴`** for the antipodal quotient map.
Source: ball(a, 1) ∩ S⁴. Target: `toRP4 '' source`. Inverse: local
section via `Set.InjOn.toPartialEquiv` (using B-3 injectivity). -/
noncomputable def S4.toRP4_localPartialEquiv (a : S4) : PartialEquiv S4 RP4 :=
  Set.InjOn.toPartialEquiv S4.toRP4
    ((Subtype.val ⁻¹' Metric.ball (a : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)
    (S4.toRP4_injOn_ball a)

/-- **The local OpenPartialHomeomorph at `a : S⁴`** for the antipodal
quotient map. Combines:
- B-2's `S4.toRP4_isOpenMap` for openness of the target.
- B-3's `S4.toRP4_injOn_ball` for injectivity.
- Continuity of `S4.toRP4` (it's a quotient map / continuous by
  construction in `RP4.lean`). -/
noncomputable def S4.toRP4_localOpenPartialHomeomorph (a : S4) :
    OpenPartialHomeomorph S4 RP4 := by
  refine OpenPartialHomeomorph.ofContinuousOpenRestrict
    (S4.toRP4_localPartialEquiv a) ?_ ?_ ?_
  · -- ContinuousOn S4.toRP4 (ball(a, 1) ∩ S4)
    show ContinuousOn S4.toRP4 _
    exact (continuous_quotient_mk' (s := antipodalSetoidS4)).continuousOn
  · -- IsOpenMap on source.restrict via IsOpenMap.restrict
    have hopen_source : IsOpen
        ((Subtype.val ⁻¹' Metric.ball (a : EuclideanSpace ℝ (Fin 5)) 1) : Set S4) :=
      Metric.isOpen_ball.preimage continuous_subtype_val
    show IsOpenMap (_ : _ → RP4)
    exact S4.toRP4_isOpenMap.restrict hopen_source
  · -- IsOpen source: standard induced topology on subtype
    show IsOpen _
    exact Metric.isOpen_ball.preimage continuous_subtype_val

/-! ## §2. Source equation + membership

Verifies the OpenPartialHomeomorph's source matches the original ball
specification, which the IsLocalHomeomorph constructor needs. -/

/-- The source of the local OpenPartialHomeomorph at `a` is the ball around `a`. -/
@[simp]
lemma S4.toRP4_localOpenPartialHomeomorph_source (a : S4) :
    (S4.toRP4_localOpenPartialHomeomorph a).source =
      ((Subtype.val ⁻¹' Metric.ball (a : EuclideanSpace ℝ (Fin 5)) 1) : Set S4) :=
  rfl

/-- The local OpenPartialHomeomorph at `a` agrees with `S4.toRP4` on the source. -/
@[simp]
lemma S4.toRP4_localOpenPartialHomeomorph_apply (a : S4) (x : S4) :
    (S4.toRP4_localOpenPartialHomeomorph a) x = S4.toRP4 x :=
  rfl

/-- Every point `a : S⁴` lies in the source of its own local
OpenPartialHomeomorph (the ball of radius 1 around itself contains the
center). -/
lemma S4.mem_toRP4_localOpenPartialHomeomorph_source (a : S4) :
    a ∈ (S4.toRP4_localOpenPartialHomeomorph a).source := by
  show (a : EuclideanSpace ℝ (Fin 5)) ∈ Metric.ball (a : EuclideanSpace ℝ (Fin 5)) 1
  exact Metric.mem_ball_self one_pos

/-! ## §3. `IsLocalHomeomorph S4.toRP4`

The substantive Phase 6r-prime M3 Layer B-4a headline: the antipodal
quotient map `S⁴ → RP⁴` is a local homeomorphism. -/

/-- **`S4.toRP4_isLocalHomeomorph`** — the antipodal quotient map
`S⁴ → RP⁴` is a local homeomorphism. The per-point chart is
`S4.toRP4_localOpenPartialHomeomorph a` whose source is the radius-1 ball
around `a` (intersected with `S⁴`), and where every point lies in its
own chart's source.

**Substantive content**: combines B-1 (parallelogram identity for
antipodal disjointness), B-2 (`IsOpenMap S4.toRP4`), and B-3
(`S4.toRP4_injOn_ball`). The construction uses
`OpenPartialHomeomorph.ofContinuousOpenRestrict` to lift the per-point
`Set.InjOn` data to a smooth-manifold-compatible chart.

Closes Phase 6r-prime M3 Layer B segment B-4a. The chart atlas
(`ChartedSpace`) + smooth-structure (`IsManifold`) follow-on layer B-4b/c
consumes this `IsLocalHomeomorph` foundation. -/
theorem S4.toRP4_isLocalHomeomorph : IsLocalHomeomorph S4.toRP4 :=
  IsLocalHomeomorph.mk S4.toRP4 fun x => ⟨S4.toRP4_localOpenPartialHomeomorph x,
    S4.mem_toRP4_localOpenPartialHomeomorph_source x,
    fun _ _ => rfl⟩

end SKEFTHawking.SymTFT
