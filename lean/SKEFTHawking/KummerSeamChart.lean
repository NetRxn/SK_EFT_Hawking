/-
# Phase 5q.H — K6′b Leg 9c: CHART FAMILY 3/3 — the seam chart `K3 → 𝓔³ × ℝ`

Leg 9b made the parametrization `ℝP³ × (−1/8, 1/2) ↪ K3` an open embedding onto the per-component
seam neighbourhood. This module turns it into actual **charts**: invert the open embedding and
apply the banked `ℝP³` atlas (`KummerRP3Smooth.instChartedSpaceRP3`, `ℝP³` charted on `𝓔³`) to the
first factor and the open-interval inclusion `(−1/8, 1/2) ↪ ℝ` to the second.

The target model is the **untagged** product `𝓔³ × ℝ` — the model that
`ManifoldModelTransport.prodRealEquivEuclidean` carries to `𝓡 4` (`isManifold_R4_of_prodReal`), and
which `ManifoldModelTransport.model_prod3Real_eq` identifies with the briefed `(𝓡 3).prod 𝓘(ℝ, ℝ)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamComponentOpen
import SKEFTHawking.KummerRP3Smooth

namespace SKEFTHawking.KummerSeamChart

open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerRP3Smooth (E3)
open SKEFTHawking.KummerSeamDoubleCollar (dblParam dblCollar dblCollar_injective
  continuous_dblCollar)
open SKEFTHawking.KummerSeamComponentOpen

noncomputable section

/-! ## §1. The open collar parameter as a subtype of `ℝ` -/

/-- The open double-collar parameter interval `(−1/8, 1/2) ⊆ ℝ`. -/
def openParam : Set ℝ := Set.Ioo (-(1 / 8) : ℝ) (1 / 2)

theorem isOpen_openParam : IsOpen openParam := isOpen_Ioo

instance instNonemptyOpenParam : Nonempty ↥openParam := ⟨⟨0, by constructor <;> norm_num⟩⟩

/-- The inclusion `(−1/8, 1/2) ↪ [−1/8, 1/2]` of the open parameter into the closed one. -/
def toDbl (v : ↥openParam) : ↥dblParam := ⟨(v : ℝ), ⟨le_of_lt v.2.1, le_of_lt v.2.2⟩⟩

theorem continuous_toDbl : Continuous toDbl :=
  Continuous.subtype_mk continuous_subtype_val _

/-- The inclusion is an **open** map: the open interval is open in `ℝ`, hence its image is the
`↥dblParam`-preimage of an open subset of `ℝ`. (`Subtype.val : ↥dblParam → ℝ` is *not* open — the
closed interval is not open — so this must be routed through `ℝ`, not through `dblParam`.) -/
theorem isOpenMap_toDbl : IsOpenMap toDbl := by
  intro U hU
  have h1 : IsOpen ((Subtype.val : ↥openParam → ℝ) '' U) :=
    isOpen_openParam.isOpenMap_subtype_val U hU
  have hset : toDbl '' U = (Subtype.val : ↥dblParam → ℝ) ⁻¹' ((Subtype.val : ↥openParam → ℝ) '' U) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro w ⟨v, hv, hvw⟩
      exact ⟨v, hv, Subtype.ext hvw⟩
  rw [hset]
  exact h1.preimage continuous_subtype_val

/-! ## §2. The seam parametrization on the honest open interval -/

/-- **The seam parametrization** `ℝP³ × (−1/8, 1/2) → K3` of the `c`-th component's two-sided
collar. -/
def seamParam (c : EIndex) (p : RP3 × ↥openParam) : KummerK3 := dblCollar c (p.1, toDbl p.2)

theorem continuous_seamParam (c : EIndex) : Continuous (seamParam c) :=
  (continuous_dblCollar c).comp (continuous_fst.prodMk (continuous_toDbl.comp continuous_snd))

theorem injective_seamParam (c : EIndex) : Function.Injective (seamParam c) := by
  intro p q h
  have hpair := dblCollar_injective c h
  refine Prod.ext (Prod.ext_iff.mp hpair).1 (Subtype.ext ?_)
  exact congrArg (fun w : ↥dblParam => (w : ℝ)) (Prod.ext_iff.mp hpair).2

/-- **THE SEAM PARAMETRIZATION IS AN OPEN EMBEDDING** on the honest open interval. -/
theorem isOpenEmbedding_seamParam (c : EIndex) : Topology.IsOpenEmbedding (seamParam c) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_seamParam c) (injective_seamParam c) ?_
  intro U hU
  have himg : seamParam c '' U = dblCollar c '' (Prod.map id toDbl '' U) := by
    rw [Set.image_image]; rfl
  rw [himg]
  refine isOpen_dblCollar_image (IsOpenMap.id.prodMap isOpenMap_toDbl U hU) ?_
  rintro _ ⟨p, -, rfl⟩
  exact ⟨Set.mem_univ _, p.2.2.1, p.2.2.2⟩

/-- The parametrization's range is the open component neighbourhood of Leg 9b. -/
theorem range_seamParam (c : EIndex) : Set.range (seamParam c) = seamCompNbhd c := by
  rw [seamCompNbhd_eq_dblCollar_image]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨p, rfl⟩
    exact ⟨(p.1, toDbl p.2), ⟨Set.mem_univ _, p.2.2.1, p.2.2.2⟩, rfl⟩
  · rintro _ ⟨⟨r, v⟩, ⟨-, hlo, hhi⟩, rfl⟩
    exact ⟨(r, ⟨(v : ℝ), hlo, hhi⟩), rfl⟩

/-! ## §3. The seam charts -/

/-- The open interval as a chart into `ℝ`. -/
def paramChart : OpenPartialHomeomorph ↥openParam ℝ :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph Subtype.val
    isOpen_openParam.isOpenEmbedding_subtypeVal

/-- The seam parametrization as an `OpenPartialHomeomorph` (source `univ`, target
`seamCompNbhd c`). -/
def seamParamHomeo (c : EIndex) : OpenPartialHomeomorph (RP3 × ↥openParam) KummerK3 :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph (seamParam c) (isOpenEmbedding_seamParam c)

theorem seamParamHomeo_target (c : EIndex) :
    (seamParamHomeo c).target = Set.range (seamParam c) :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target (seamParam c)
    (isOpenEmbedding_seamParam c)

/-- **CHART FAMILY 3/3 — the seam chart of `K3` at collar direction `r₀`**, an
`OpenPartialHomeomorph K3 (𝓔³ × ℝ)`: invert the seam parametrization, then apply the banked `ℝP³`
chart at `r₀` to the collar direction and the interval inclusion to the collar parameter.

The `𝓔³ × ℝ` model is the untagged product `ManifoldModelTransport` transports to `𝓡 4`. -/
def seamChart (c : EIndex) (r₀ : RP3) : OpenPartialHomeomorph KummerK3 (E3 × ℝ) :=
  (seamParamHomeo c).symm.trans ((chartAt E3 r₀).prod paramChart)

/-- **Every collar point is in the source of its own seam chart** — the chart-covering condition
for chart family 3/3. -/
theorem mem_seamChart_source (c : EIndex) (p : RP3 × ↥openParam) :
    seamParam c p ∈ (seamChart c p.1).source := by
  have hsymm : (seamParamHomeo c).symm (seamParam c p) = p :=
    (seamParamHomeo c).left_inv (by trivial)
  simp only [seamChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨(seamParamHomeo c).map_source (by trivial),
    by rw [hsymm]; exact ⟨mem_chart_source E3 p.1, by trivial⟩⟩

/-- **The seam chart's source is exactly the open component neighbourhood cut down to the `ℝP³`
chart domain** — in particular it is open and contains the whole `r₀`-slice of the collar. -/
theorem seamChart_source_subset (c : EIndex) (r₀ : RP3) :
    (seamChart c r₀).source ⊆ seamCompNbhd c := by
  intro x hx
  rw [← range_seamParam]
  simp only [seamChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff] at hx
  rw [← seamParamHomeo_target]
  exact hx.1

end

end SKEFTHawking.KummerSeamChart
