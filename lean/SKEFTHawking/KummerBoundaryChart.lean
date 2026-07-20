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

end

end SKEFTHawking.KummerBoundaryChart
