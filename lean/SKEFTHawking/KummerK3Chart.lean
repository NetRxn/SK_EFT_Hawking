/-
# Phase 5q.H — K6′b Leg 11: `KummerK3` IS A CHARTED SPACE ON THE FLAT MODEL `𝓔³ × ℝ`

The three weld chart families are now all available on the boundaryless model `𝓔³ × ℝ`:

| family | source region | charts |
|---|---|---|
| 1/3 E-interior | `weldMk '' (inr '' (univ ×ˢ interiorE))` | `KummerEInteriorChart.instChartedSpaceInteriorE` pushed along `isOpenEmbedding_eInteriorCopy` |
| 2/3 Q-interior | `range qInteriorPiece` | `KummerQInteriorChart.instChartedSpaceInteriorQ` pushed along `isOpenEmbedding_qInteriorPiece` |
| 3/3 seam | `seamNbhd` | `KummerSeamChart.seamChart` (already `K3`-valued) |

and `KummerSeamOpenNbhd.isOpen_cover_three_families` says the three regions cover `K3`. This module
does the assembly.

**The one missing set identity** is that the *global* seam neighbourhood is the union of the
*per-component* ones (`seamNbhd_eq_iUnion`, §1) — the global carrier takes all sixteen Q-collars
together with the E-collar of *every* copy, the per-component carrier takes the `c`-th of each; the
`univ = ⋃ {c}` split on the E index is the whole content.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerEInteriorChart
import SKEFTHawking.KummerQInteriorChart
import SKEFTHawking.KummerSeamChart

namespace SKEFTHawking.KummerK3Chart

open Set Topology
open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerWeldOpenPieces (interiorE eInteriorCopy isOpenEmbedding_eInteriorCopy)
open SKEFTHawking.KummerWeldQInterior (interiorQ qInteriorPiece isOpenEmbedding_qInteriorPiece)
open SKEFTHawking.KummerSeamOpenNbhd
open SKEFTHawking.KummerSeamComponentOpen (seamCompCarrier seamCompNbhd)
open SKEFTHawking.KummerSeamChart (openParam seamParam seamChart mem_seamChart_source
  range_seamParam)
open SKEFTHawking.HalfSpaceInteriorFlatten (FModel)

noncomputable section

/-! ## §1. The global seam neighbourhood is the union of the per-component ones -/

/-- The global seam carrier is the union of the sixteen per-component carriers: the Q-side is a
`⋃ c` on the nose, and the E-side splits `univ = ⋃ c, {c}` on the copy index. -/
theorem seamNbhdCarrier_eq_iUnion : seamNbhdCarrier = ⋃ c : EIndex, seamCompCarrier c := by
  ext a
  constructor
  · rintro (⟨q, hq, rfl⟩ | ⟨p, hp, rfl⟩)
    · obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hq
      exact Set.mem_iUnion.mpr ⟨c, Or.inl ⟨q, hc, rfl⟩⟩
    · exact Set.mem_iUnion.mpr ⟨p.1, Or.inr ⟨p, ⟨rfl, hp.2⟩, rfl⟩⟩
  · intro h
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp h
    rcases hc with ⟨q, hq, rfl⟩ | ⟨p, hp, rfl⟩
    · exact Or.inl ⟨q, Set.mem_iUnion.mpr ⟨c, hq⟩, rfl⟩
    · exact Or.inr ⟨p, ⟨Set.mem_univ _, hp.2⟩, rfl⟩

/-- **The global seam neighbourhood is the union of the per-component seam neighbourhoods.** -/
theorem seamNbhd_eq_iUnion : seamNbhd = ⋃ c : EIndex, seamCompNbhd c := by
  rw [seamNbhd, seamNbhdCarrier_eq_iUnion, Set.image_iUnion]
  rfl

/-! ## §2. The three flat chart families of `K3` -/

/-- **Chart family 1/3** — a flat chart of `↥interiorE` pushed forward along the open embedding
`eInteriorCopy c : ↥interiorE ↪ K3`. -/
def eFamChart (c : EIndex) (y : ↥interiorE) : OpenPartialHomeomorph KummerK3 FModel :=
  (chartAt FModel y).lift_openEmbedding (isOpenEmbedding_eInteriorCopy c)

theorem mem_eFamChart_source (c : EIndex) (y : ↥interiorE) :
    eInteriorCopy c y ∈ (eFamChart c y).source := by
  rw [eFamChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨y, mem_chart_source FModel y, rfl⟩

/-- **Chart family 2/3** — a flat chart of `↥interiorQ` pushed forward along the open embedding
`qInteriorPiece : ↥interiorQ ↪ K3`. -/
def qFamChart (y : ↥interiorQ) : OpenPartialHomeomorph KummerK3 FModel :=
  (chartAt FModel y).lift_openEmbedding isOpenEmbedding_qInteriorPiece

theorem mem_qFamChart_source (y : ↥interiorQ) :
    qInteriorPiece y ∈ (qFamChart y).source := by
  rw [qFamChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨y, mem_chart_source FModel y, rfl⟩

/-- **THE WELD ATLAS** on the flat model `𝓔³ × ℝ`: the two pushed-forward interior families plus
the seam family. -/
def atlasK3 : Set (OpenPartialHomeomorph KummerK3 FModel) :=
  (⋃ c : EIndex, Set.range (eFamChart c)) ∪ Set.range qFamChart
    ∪ ⋃ c : EIndex, Set.range (seamChart c)

/-! ## §3. The covering dispatch -/

/-- **EVERY POINT OF `K3` LIES IN THE SOURCE OF A WELD-ATLAS CHART.** The three-family open cover
(`isOpen_cover_three_families`) supplies the case split; each case's chart is the corresponding
family's chart at a preimage of the point. -/
theorem exists_chartK3 (y : KummerK3) : ∃ ch ∈ atlasK3, y ∈ ch.source := by
  have hcov := (isOpen_cover_three_families).2.2.2
  have hy : y ∈ Set.range qInteriorPiece
      ∪ weldMk '' (Sum.inr '' ((Set.univ : Set EIndex) ×ˢ interiorE))
      ∪ seamNbhd := by rw [hcov]; exact Set.mem_univ y
  rcases hy with (hq | he) | hs
  · obtain ⟨q, rfl⟩ := hq
    exact ⟨qFamChart q, Or.inl (Or.inr (Set.mem_range_self q)), mem_qFamChart_source q⟩
  · obtain ⟨_, ⟨⟨c, x⟩, ⟨-, hx⟩, rfl⟩, rfl⟩ := he
    refine ⟨eFamChart c ⟨x, hx⟩,
      Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨c, Set.mem_range_self _⟩)), ?_⟩
    exact mem_eFamChart_source c ⟨x, hx⟩
  · rw [seamNbhd_eq_iUnion] at hs
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hs
    rw [← range_seamParam] at hc
    obtain ⟨p, rfl⟩ := hc
    exact ⟨seamChart c p.1, Or.inr (Set.mem_iUnion.mpr ⟨c, Set.mem_range_self _⟩),
      mem_seamChart_source c p⟩

/-! ## §4. The charted space -/

open Classical in
/-- **`KummerK3` IS A CHARTED SPACE ON THE FLAT MODEL `𝓔³ × ℝ`** — the topological half of the
K6′b weld atlas, on exactly the model that `ManifoldModelTransport.isManifold_R4_of_prodReal`
carries to `𝓡 4`. `chartAt` dispatches each point through `exists_chartK3` to one of the three
families. -/
noncomputable instance instChartedSpaceKummerK3 : ChartedSpace FModel KummerK3 where
  atlas := atlasK3
  chartAt y := Classical.choose (exists_chartK3 y)
  mem_chart_source y := (Classical.choose_spec (exists_chartK3 y)).2
  chart_mem_atlas y := (Classical.choose_spec (exists_chartK3 y)).1

end

end SKEFTHawking.KummerK3Chart
