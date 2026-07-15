/-
# Phase 5q.H W-D — THE SURGERY FOUNDATION, WAVE 3: SmoothWeld → IsManifold, the surgered
# boundary, and the Bordism packaging

Wave-3 companion to `SingularSurgeryFoundation.lean` (opener) + `SingularSurgeryCharts.lean` (wave 2).
Wave 2 delivered `carrierChartedSpace : ChartedSpace H' W` via the `chartedSpaceOfOpensCover` keystone,
and isolated ALL remaining `Bordism` content to (Target 2) `IsManifold J k W`, (Target 3) the boundary
map, and (Target 4) the `Bordism` packaging. This module delivers them at the honest grain.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryCharts
import SKEFTHawking.BordismGroup

namespace SKEFTHawking.SurgeryFoundation

open Topology TopologicalSpace
open scoped Manifold

/-! ## §1. The reusable keystone — assemble `HasGroupoid` from the open cover.

Wave 2's `chartedSpaceOfOpensCover` assembled a `ChartedSpace` from an open cover of charted open
subsets; its atlas member at `w` is the region chart transported through the open inclusion. Here we
prove the `HasGroupoid`/`IsManifold` layer on top: the assembled atlas lies in a groupoid `G` as soon
as every pairwise **region-bridged transition** does. That single hypothesis absorbs both the
same-region transitions (the regions' own smoothness) and the cross-region ones (empty-source for
disjoint regions; the collar weld for the seam). This is the mechanism `IsManifold J k W` is built by. -/

variable {H' W : Type*} [TopologicalSpace H'] [TopologicalSpace W] {ι : Type*}

/-- **The region bridge** `↥(U i) ⇢ ↥(U j)` — the open-embedding transition `incl i ≫ incl j⁻¹`
between two covering regions, defined on the overlap `U i ∩ U j`. For `i = j` it is (eqOnSource) the
identity; for disjoint regions it has empty source. -/
noncomputable def regionBridge (U : ι → Opens W) (i j : ι)
    (hi : Nonempty ↥(U i)) (hj : Nonempty ↥(U j)) :
    OpenPartialHomeomorph ↥(U i) ↥(U j) :=
  ((U i).openPartialHomeomorphSubtypeCoe hi).trans
    ((U j).openPartialHomeomorphSubtypeCoe hj).symm

/-- **The region-bridged transition** `H' ⇢ H'` — the composite `(chartAt p)⁻¹ ≫ regionBridge ≫
chartAt p'` that every pairwise transition of the assembled atlas equals. Its membership in `G` is the
single hypothesis of the keystone. -/
noncomputable def bridgeTransition (U : ι → Opens W) (cs : ∀ i, ChartedSpace H' (U i))
    (i j : ι) (p : ↥(U i)) (p' : ↥(U j)) : OpenPartialHomeomorph H' H' :=
  letI := cs i; letI := cs j
  (chartAt H' p).symm ≫ₕ (regionBridge U i j ⟨p⟩ ⟨p'⟩ ≫ₕ chartAt H' p')

/-- **The chart-transition reduction** (pure `OpenPartialHomeomorph` algebra). The transition between
two transported region charts `(incl i)⁻¹ ≫ chartAt p` and `(incl j)⁻¹ ≫ chartAt p'` equals the
`bridgeTransition`. All steps are equalities (`trans_symm_eq_symm_trans_symm`, `symm_symm`,
`trans_assoc`). -/
theorem chartTrans_eq_bridge (U : ι → Opens W) (cs : ∀ i, ChartedSpace H' (U i))
    (i j : ι) (p : ↥(U i)) (p' : ↥(U j)) (hi : Nonempty ↥(U i)) (hj : Nonempty ↥(U j)) :
    letI := cs i; letI := cs j
    (((U i).openPartialHomeomorphSubtypeCoe hi).symm ≫ₕ chartAt H' p).symm ≫ₕ
        (((U j).openPartialHomeomorphSubtypeCoe hj).symm ≫ₕ chartAt H' p')
      = bridgeTransition U cs i j p p' := by
  letI := cs i; letI := cs j
  simp only [bridgeTransition, regionBridge, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]

/-- **Key reduction: the assembled atlas transition IS a `bridgeTransition`.** For the
`chartedSpaceOfOpensCover` atlas, `(chart w)⁻¹ ≫ chart w'` reduces — by pure `OpenPartialHomeomorph`
trans/symm algebra — to `bridgeTransition` at the two regions. This is the whole reason the single
`bridgeTransition ∈ G` hypothesis suffices. -/
theorem hasGroupoid_of_opensCover
    (U : ι → Opens W) (hcover : ∀ w : W, ∃ i, w ∈ U i)
    (cs : ∀ i, ChartedSpace H' (U i)) (G : StructureGroupoid H')
    (hbridge : ∀ (i j : ι) (p : ↥(U i)) (p' : ↥(U j)),
      bridgeTransition U cs i j p p' ∈ G) :
    @HasGroupoid H' _ W _ (chartedSpaceOfOpensCover U hcover cs) G := by
  letI := chartedSpaceOfOpensCover U hcover cs
  refine ⟨?_⟩
  intro e e' he he'
  obtain ⟨w, hw⟩ := he
  obtain ⟨w', hw'⟩ := he'
  rw [← hw, ← hw', chartTrans_eq_bridge]
  exact hbridge _ _ _ _

/-! ### §1.1. Discharging the bridge hypothesis: the diagonal and disjoint-off-diagonal cases. -/

/-- **The diagonal (same-region) bridge lies in `G`.** When `i = j`, the region bridge is (eqOnSource)
the identity, so `bridgeTransition` reduces to region `i`'s own chart transition `(chartAt p)⁻¹ ≫
chartAt p'`, which lies in `G` because region `i` is a `G`-manifold. -/
theorem bridgeTransition_diag_mem (U : ι → Opens W) (cs : ∀ i, ChartedSpace H' (U i))
    (G : StructureGroupoid H') (i : ι) (p p' : ↥(U i))
    (hmfd : @HasGroupoid H' _ ↥(U i) _ (cs i) G) :
    bridgeTransition U cs i i p p' ∈ G := by
  letI := cs i
  haveI := hmfd
  have hbr : regionBridge U i i ⟨p⟩ ⟨p'⟩ ≈
      OpenPartialHomeomorph.ofSet ((U i).openPartialHomeomorphSubtypeCoe ⟨p⟩).source
        ((U i).openPartialHomeomorphSubtypeCoe ⟨p⟩).open_source :=
    OpenPartialHomeomorph.self_trans_symm _
  have hmid : regionBridge U i i ⟨p⟩ ⟨p'⟩ ≫ₕ chartAt H' p' ≈ chartAt H' p' := by
    refine Setoid.trans (OpenPartialHomeomorph.EqOnSource.trans' hbr
      (OpenPartialHomeomorph.eqOnSource_refl _)) ?_
    rw [OpenPartialHomeomorph.ofSet_trans, Opens.openPartialHomeomorphSubtypeCoe_source,
      OpenPartialHomeomorph.restr_univ]
  have heqv : bridgeTransition U cs i i p p' ≈ (chartAt H' p).symm ≫ₕ chartAt H' p' :=
    OpenPartialHomeomorph.EqOnSource.trans' (OpenPartialHomeomorph.eqOnSource_refl _) hmid
  exact G.mem_of_eqOnSource
    (G.compatible (chart_mem_atlas H' p) (chart_mem_atlas H' p')) heqv

/-- **The disjoint off-diagonal bridge lies in the smooth groupoid.** When the regions `U i`, `U j`
are disjoint, the region bridge has empty source, so `bridgeTransition` has empty source, hence lies in
`contDiffGroupoid` (any change of coordinates with empty source does). This is the cross-interior case:
the two interiors are disjoint (wave 2), so their transitions are trivially smooth. -/
theorem regionBridge_source_eq_empty (U : ι → Opens W) (i j : ι)
    (hi : Nonempty ↥(U i)) (hj : Nonempty ↥(U j)) (hdisj : Disjoint (U i : Set W) (U j)) :
    (regionBridge U i j hi hj).source = ∅ := by
  ext x
  simp only [regionBridge, OpenPartialHomeomorph.trans_source,
    Opens.openPartialHomeomorphSubtypeCoe_source, Set.univ_inter, Set.mem_preimage,
    OpenPartialHomeomorph.symm_source, Opens.openPartialHomeomorphSubtypeCoe_target,
    Set.mem_empty_iff_false, iff_false]
  intro hx
  exact Set.disjoint_left.mp hdisj x.2 hx

/-- **The disjoint off-diagonal bridge lies in `contDiffGroupoid`** — empty source. -/
theorem bridgeTransition_empty_mem {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (J : ModelWithCorners ℝ E' H') {k : WithTop ℕ∞}
    (U : ι → Opens W) (cs : ∀ i, ChartedSpace H' (U i)) (i j : ι) (p : ↥(U i)) (p' : ↥(U j))
    (hdisj : Disjoint (U i : Set W) (U j)) :
    bridgeTransition U cs i j p p' ∈ contDiffGroupoid k J := by
  apply ContDiffGroupoid.mem_of_source_eq_empty
  have hrb : (regionBridge U i j ⟨p⟩ ⟨p'⟩).source = ∅ :=
    regionBridge_source_eq_empty U i j ⟨p⟩ ⟨p'⟩ hdisj
  simp only [bridgeTransition, OpenPartialHomeomorph.trans_source, hrb, Set.empty_inter,
    Set.preimage_empty, Set.inter_empty]

/-! ### §1.2. Manifold-ness of a region transported through a single homeomorphism chart.

The interior regions carry `ChartedSpace.comp H' Y X` where `X ≃ₜ Y` is a single global homeo chart and
`Y` (an open subset of an end) is itself a `G`-manifold. The transported region is a `G`-manifold: the
homeo cancels (`self_trans_symm`), reducing each transition to `Y`'s own. -/

/-- **A region transported through a single homeomorphism chart inherits `HasGroupoid`.** If `Y` is a
`G`-manifold and `X ≃ₜ Y`, then `X` with the composite structure `chartedSpaceOfHomeo e ∘ (Y's charts)`
is a `G`-manifold. The homeo is a global chart with `univ` source, so each transition cancels to one of
`Y`'s. This is exactly how the two interior regions inherit their ends' smoothness. -/
theorem hasGroupoid_comp_of_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) [ChartedSpace H' Y] (G : StructureGroupoid H') [ClosedUnderRestriction G]
    [HasGroupoid Y G] :
    @HasGroupoid H' _ X _ (@ChartedSpace.comp H' _ Y _ X _ _ (chartedSpaceOfHomeo e)) G := by
  letI := chartedSpaceOfHomeo e
  letI := ChartedSpace.comp H' Y X
  refine ⟨fun {f f'} hf hf' => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hf
  obtain ⟨a', ha', b', hb', rfl⟩ := hf'
  obtain rfl : a = e.toOpenPartialHomeomorph := ha
  obtain rfl : a' = e.toOpenPartialHomeomorph := ha'
  -- transition = (e ≫ₕ b).symm ≫ₕ (e ≫ₕ b') ; cancel the homeo
  have hcompat : b.symm ≫ₕ b' ∈ G := G.compatible hb hb'
  refine G.mem_of_eqOnSource hcompat ?_
  have hcancel : e.toOpenPartialHomeomorph.symm ≫ₕ e.toOpenPartialHomeomorph ≈
      OpenPartialHomeomorph.ofSet e.toOpenPartialHomeomorph.target
        e.toOpenPartialHomeomorph.open_target :=
    OpenPartialHomeomorph.symm_trans_self _
  calc (e.toOpenPartialHomeomorph ≫ₕ b).symm ≫ₕ (e.toOpenPartialHomeomorph ≫ₕ b')
      = b.symm ≫ₕ (e.toOpenPartialHomeomorph.symm ≫ₕ e.toOpenPartialHomeomorph) ≫ₕ b' := by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc, OpenPartialHomeomorph.trans_assoc]
    _ ≈ b.symm ≫ₕ b' := by
        refine OpenPartialHomeomorph.EqOnSource.trans'
          (OpenPartialHomeomorph.eqOnSource_refl _) ?_
        refine Setoid.trans (OpenPartialHomeomorph.EqOnSource.trans' hcancel
          (OpenPartialHomeomorph.eqOnSource_refl _)) ?_
        rw [OpenPartialHomeomorph.ofSet_trans, Homeomorph.toOpenPartialHomeomorph_target,
          OpenPartialHomeomorph.restr_univ]

/-! ## §2. The surgery-trace three-region cover, named. -/

namespace SurgeryChartDatum

variable (D : SurgeryChartDatum)

/-- **The surgery-trace three-region open cover** `{cylinder-interior, handle-interior, seam-collar}`,
named (the inline cover of `carrierChartedSpace`). -/
@[reducible] def surgeryCover : Fin 3 → Opens D.toHandleAttachment.carrier := fun i =>
  ![⟨D.toHandleAttachment.cylInteriorRegion, D.toHandleAttachment.isOpen_cylInteriorRegion⟩,
    ⟨D.toHandleAttachment.handleInteriorRegion, D.toHandleAttachment.isOpen_handleInteriorRegion⟩,
    D.seamNbhd] i

/-- **The per-region charted structures** (the inline `cs` of `carrierChartedSpace`): the two interiors
inherit the ends' charts (§3, wave 2); the seam collar carries the datum's weld charts. -/
@[reducible] noncomputable def surgeryRegionCS :
    ∀ i, ChartedSpace D.H' ↥(D.surgeryCover i) := fun i =>
  match i with
  | 0 => D.toHandleAttachment.cylInteriorChartedSpace
  | 1 => D.toHandleAttachment.handleInteriorChartedSpace
  | 2 => D.chartSeam

/-- The named cover indeed covers the carrier (region topology, wave 2). -/
theorem surgeryCover_covers (w : D.toHandleAttachment.carrier) : ∃ i, w ∈ D.surgeryCover i := by
  have hcov := D.toHandleAttachment.cylInteriorRegion_union_handleInteriorRegion_union_seamRegion
  rw [Set.eq_univ_iff_forall] at hcov
  rcases hcov w with (hcyl | hhandle) | hs
  · exact ⟨0, hcyl⟩
  · exact ⟨1, hhandle⟩
  · exact ⟨2, D.hseam hs⟩

/-- **The named cover reproduces `carrierChartedSpace`** (definitionally — proof-irrelevant `hcover`). -/
theorem carrierChartedSpace_eq :
    D.carrierChartedSpace
      = chartedSpaceOfOpensCover D.surgeryCover D.surgeryCover_covers D.surgeryRegionCS :=
  rfl

end SurgeryChartDatum

/-! ## §3. The smoothness-enriched surgery datum, and `IsManifold` (Target 2).

`SmoothSurgeryChartDatum` enriches the wave-2 `SurgeryChartDatum` with the smoothness data the
`IsManifold` layer needs: a `ModelWithCorners J`, a smoothness order `k`, the two ends and the seam
collar as genuine `J`-manifolds, and — **the SmoothWeld field, the sole genuinely-geometric input** —
the collar-weld's compatibility with the two interior regions (the seam↔interior chart transitions lie
in the smooth groupoid). Wave 2 proved same-region transitions inherit and the two interiors are
disjoint (empty-source transitions); the SmoothWeld is exactly the remaining groupoid content. -/

/-- **A smoothness-enriched surgery-chart datum.** `SurgeryChartDatum` (wave 2) plus: the smooth model
`J` and order `k`; the two ends `B`, `Ha` and the seam collar as `J`-manifolds; and the SmoothWeld —
the seam-collar chart transitions with the two interior regions lie in `contDiffGroupoid k J`. From it
`IsManifold J k W` is assembled (`carrierIsManifold`). -/
structure SmoothSurgeryChartDatum extends SurgeryChartDatum where
  /-- the model tangent space of the smooth structure. -/
  E' : Type*
  [normedE' : NormedAddCommGroup E']
  [normedSpaceE' : NormedSpace ℝ E']
  /-- the smooth model-with-corners (`= (𝓡 4).prod (𝓡∂ 1)` for the KT surgery trace). -/
  J : ModelWithCorners ℝ E' toSurgeryChartDatum.H'
  /-- the smoothness order. -/
  k : WithTop ℕ∞
  /-- the cylinder end `B = M × I` is a genuine `J`-manifold. -/
  [mfdB : IsManifold J k toSurgeryChartDatum.toHandleAttachment.B]
  /-- the handle end `Ha` is a genuine `J`-manifold. -/
  [mfdHa : IsManifold J k toSurgeryChartDatum.toHandleAttachment.Ha]
  /-- the seam collar is a genuine `J`-manifold. -/
  [mfdSeam : IsManifold J k ↥toSurgeryChartDatum.seamNbhd]
  /-- **THE SMOOTH WELD** — the seam-collar chart transitions with the two interior regions lie in the
  smooth groupoid. The single genuinely-geometric input: the collar-neighborhood-theorem content
  applied once at the attaching sphere. (Interior↔interior transitions are empty-source, hence smooth
  automatically; same-region transitions inherit — so only these seam↔interior welds carry content.) -/
  smoothWeld : ∀ (i j : Fin 3), (i = 2 ∨ j = 2) → i ≠ j →
    ∀ (p : ↥(toSurgeryChartDatum.surgeryCover i)) (p' : ↥(toSurgeryChartDatum.surgeryCover j)),
      bridgeTransition toSurgeryChartDatum.surgeryCover toSurgeryChartDatum.surgeryRegionCS i j p p'
        ∈ contDiffGroupoid k J

attribute [instance] SmoothSurgeryChartDatum.normedE' SmoothSurgeryChartDatum.normedSpaceE'
  SmoothSurgeryChartDatum.mfdB SmoothSurgeryChartDatum.mfdHa SmoothSurgeryChartDatum.mfdSeam

namespace SmoothSurgeryChartDatum

variable (D : SmoothSurgeryChartDatum)

/-- **Region 0 (cylinder interior) is a `J`-manifold** — transported from the end `B` through the
interior homeo (`hasGroupoid_comp_of_homeo`), `B` being a manifold and `B ∖ range φ` an open subset. -/
theorem hasGroupoid_region0 :
    @HasGroupoid D.H' _ ↥(D.toHandleAttachment.cylInteriorRegion) _
      D.toHandleAttachment.cylInteriorChartedSpace (contDiffGroupoid D.k D.J) := by
  letI : ChartedSpace D.H' ↥((Set.range D.toHandleAttachment.φ)ᶜ) :=
    TopologicalSpace.Opens.instChartedSpace
      ⟨(Set.range D.toHandleAttachment.φ)ᶜ, D.toHandleAttachment.isClosed_range_φ.isOpen_compl⟩
  haveI : HasGroupoid ↥((Set.range D.toHandleAttachment.φ)ᶜ) (contDiffGroupoid D.k D.J) :=
    TopologicalSpace.Opens.instHasGroupoid (contDiffGroupoid D.k D.J)
      ⟨(Set.range D.toHandleAttachment.φ)ᶜ, D.toHandleAttachment.isClosed_range_φ.isOpen_compl⟩
  exact hasGroupoid_comp_of_homeo D.toHandleAttachment.cylInteriorHomeo (contDiffGroupoid D.k D.J)

/-- **Region 1 (handle interior) is a `J`-manifold** — transported from the end `Ha` through the
interior homeo, `Ha` being a manifold and `Ha ∖ S` an open subset. -/
theorem hasGroupoid_region1 :
    @HasGroupoid D.H' _ ↥(D.toHandleAttachment.handleInteriorRegion) _
      D.toHandleAttachment.handleInteriorChartedSpace (contDiffGroupoid D.k D.J) := by
  letI : ChartedSpace D.H' ↥(D.toHandleAttachment.Sᶜ) :=
    TopologicalSpace.Opens.instChartedSpace
      ⟨D.toHandleAttachment.Sᶜ, D.toHandleAttachment.hS.isOpen_compl⟩
  haveI : HasGroupoid ↥(D.toHandleAttachment.Sᶜ) (contDiffGroupoid D.k D.J) :=
    TopologicalSpace.Opens.instHasGroupoid (contDiffGroupoid D.k D.J)
      ⟨D.toHandleAttachment.Sᶜ, D.toHandleAttachment.hS.isOpen_compl⟩
  exact hasGroupoid_comp_of_homeo D.toHandleAttachment.handleInteriorHomeo (contDiffGroupoid D.k D.J)

/-- **TARGET 2 — the surgery-trace carrier is a `C^k` manifold-with-boundary** `IsManifold J k W`.
Assembled by the §1 keystone over the three-region cover: the two interiors are `J`-manifolds
transported from the ends (`hasGroupoid_region0/1`), the seam collar is one (`mfdSeam`), the two
interiors' cross-transitions are empty-source (disjoint, wave 2), and the seam↔interior welds are the
datum's `smoothWeld`. `HasGroupoid.mk` (through the keystone) assembles `IsManifold`. -/
theorem carrierIsManifold :
    letI := D.toSurgeryChartDatum.carrierChartedSpace
    IsManifold D.J D.k D.toSurgeryChartDatum.toHandleAttachment.carrier := by
  letI := D.toSurgeryChartDatum.carrierChartedSpace
  refine @IsManifold.mk' ℝ _ D.E' _ _ D.H' _ D.J D.k _ _ _ ?_
  refine hasGroupoid_of_opensCover D.toSurgeryChartDatum.surgeryCover
    D.toSurgeryChartDatum.surgeryCover_covers D.toSurgeryChartDatum.surgeryRegionCS
    (contDiffGroupoid D.k D.J) ?_
  intro i j p p'
  fin_cases i <;> fin_cases j <;>
    first
      | exact bridgeTransition_diag_mem _ _ _ _ p p' D.hasGroupoid_region0
      | exact bridgeTransition_diag_mem _ _ _ _ p p' D.hasGroupoid_region1
      | exact bridgeTransition_diag_mem _ _ _ _ p p' D.mfdSeam.toHasGroupoid
      | exact bridgeTransition_empty_mem _ _ _ _ _ p p'
          D.toHandleAttachment.cylInteriorRegion_disjoint_handleInteriorRegion
      | exact bridgeTransition_empty_mem _ _ _ _ _ p p'
          D.toHandleAttachment.cylInteriorRegion_disjoint_handleInteriorRegion.symm
      | exact D.smoothWeld _ _ (by decide) (by decide) p p'

end SmoothSurgeryChartDatum

/-! ## §4. THE PACKAGING (Target 4) — the surgery trace as a project `Bordism`.

With the manifold structure PROVEN (`carrierIsManifold`, Target 2), the surgery-trace carrier assembles
into a `BordismTheory.Bordism` given only the **boundary identification** `e : s.M ⊕ t.M → W` (the
source end `M × {0}` via `fromCyl`, the surgered end `M'` carved from the handle) and its properties.
This is exactly the design of `BordismGroup.lean`'s §-note: a bordism is a manifold-with-boundary `W`
plus a smooth injection onto its boundary. Previously no surgery-trace `Bordism` existed because the
`IsManifold` field was missing; that obstruction is now discharged, so the trace packages honestly with
the boundary map as the sole remaining geometric input. -/

open SKEFTHawking.BordismTheory
open scoped Manifold in
/-- **TARGET 4 — the surgery-trace `Bordism`.** Given a `SmoothSurgeryChartDatum` (so the carrier `W`
is a compact `C^k` manifold-with-boundary, Targets 1–2), a base model `I`, two closed singular
`I`-manifolds `s`, `t`, and the boundary identification `e` (a smooth injection onto `J.boundary W`
with the restriction data), the surgery trace is a genuine `Bordism J s t`. The topological +
manifold fields are the PROVEN carrier structure; `e`/`he_boundary` are the geometric boundary input. -/
noncomputable def surgeryTraceBordism
    {X : Type*} [TopologicalSpace X]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    (D : SmoothSurgeryChartDatum) [FiniteDimensional ℝ D.E']
    (s t : SingularManifold X D.k I)
    (e : s.M ⊕ t.M → D.toSurgeryChartDatum.toHandleAttachment.carrier)
    (he_smooth : letI := D.toSurgeryChartDatum.carrierChartedSpace
      ContMDiff I D.J D.k e)
    (he_inj : Function.Injective e)
    (he_boundary : letI := D.toSurgeryChartDatum.carrierChartedSpace
      Set.range e = D.J.boundary D.toSurgeryChartDatum.toHandleAttachment.carrier)
    (g : D.toSurgeryChartDatum.toHandleAttachment.carrier → X) (hg : Continuous g)
    (hg_restrict : g ∘ e = Sum.elim s.f t.f) :
    letI := D.toSurgeryChartDatum.carrierChartedSpace
    Bordism D.J s t :=
  letI := D.toSurgeryChartDatum.carrierChartedSpace
  letI := D.carrierIsManifold
  { W := D.toSurgeryChartDatum.toHandleAttachment.carrier
    e := e
    he_smooth := he_smooth
    he_inj := he_inj
    he_boundary := he_boundary
    g := g
    hg := hg
    hg_restrict := hg_restrict }

/-! ### The two convergence consumers — the hooks and their named residuals.

`surgeryTraceBordism` is the `Bordism J s t` object both consumers bottom out in; each adds a
tangential/tether enrichment on top of it (the named residual, a further geometric datum this wave does
NOT supply):

* **`PinPlusKTSurgeryTrace.AmbientSurgeryDatum`** (`b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1`): take
  `I := 𝓡 4`, `D.J := (𝓡 4).prod (𝓡∂ 1)`, `Ha` the `D² × D³` 2-handle, `s := p'.1`, `t := p.1`; then
  `surgeryTraceBordism` **is** the datum's `b` field, and its carrier's `T2Space` (opener) is the `hT2`
  field. RESIDUAL: `hBor : Nonempty (CharPairBorRealizedTethered b p'.2 p.2)` — the pin-membrane tether,
  a tangential enrichment on `b`.
* **`SpinSigmaPresentation.HandleTradeCobordism`** (`IsDataBordant ξ p ((S²×S²) ⊔ p')`): `IsDataBordant
  ξ p q = ∃ b : Bordism (I.prod (𝓡∂ 1)) p.1 q.1, Nonempty (ξ.Bor b p.2 q.2)`, so `surgeryTraceBordism`
  (with `Ha` the `S²×S²`-handle, `t := (S²×S²) ⊔ p'`) supplies the existential witness `b`. RESIDUAL:
  the `ξ.Bor` tangential structure on `b`.

Both residuals are tangential-data enrichments of the SAME topological `Bordism` this wave now
delivers; the manifold-structure obstruction that previously blocked BOTH is discharged (Target 2). -/

end SKEFTHawking.SurgeryFoundation
