/-
# Phase 5q.H — K6′a Leg 2: the E-side manifold-with-boundary certificate

Continues `KummerResolutionPiece.lean` (K6′a, Route B): the concrete 𝒪(−2) disk bundle `E = ResE`,
two `D² × D²` charts welded along the base equator `‖z‖ = 1` by the clutch `(z,w) ↦ (z⁻¹, z²·w)`,
with fiber-boundary `∂E = {‖w‖ = 1} ≅ ℝP³` (`bdryHomeoRP3`, banked). This module is the **interior-shell
mirror** of `KummerShellChart.lean` (the T⁴°-side exterior-shell certificate wt3 owns): the smooth weld
K6′b consumes this E-side certificate opposite the T⁴° certificate.

## §A — the interior open-embedding descent (deliverable 1)

Away from the base equator `‖z‖ = 1` (the only gluing locus), each chart inclusion `chart0`/`chart1`
restricted to the base-interior `{‖z‖ < 1}` is an **open embedding** into `ResE`: injective (banked
`chart0_inj_iff`/`chart1_inj_iff` — same-chart points are never welded), continuous (banked), and open
(the saturation of a base-interior set adds no welded partner, so the quotient map carries it to an open
set). This is the `KummerFreeQuotient.isOpenEmbedding_qmk_sepBall` sibling, here **simpler**: the
identification is the clutch weld (a nowhere-dense equator locus), not a free group action, so a
base-interior point has a single-chart neighborhood outright. The straddling equator charts (a point on
`‖z‖ = 1` needs the two-chart overlap where the clutch IS the transition) are localized as the residual.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerResolutionPiece
import SKEFTHawking.DiskChartGeneric

namespace SKEFTHawking.KummerResolutionPieceBoundary

open SKEFTHawking.KummerResolutionPiece
open Metric Set
open scoped Manifold

noncomputable section

/-! ## §A. The interior open-embedding descent -/

/-- **The base-interior locus** of a single chart: `{p : D² × D² ∣ ‖z‖ < 1}`, away from the base equator
`‖z‖ = 1` (the only gluing locus). Open in `ResChart`. -/
def baseInterior : Set ResChart := {p : ResChart | ‖(p.1 : ℂ)‖ < 1}

theorem isOpen_baseInterior : IsOpen baseInterior :=
  isOpen_lt (continuous_norm.comp (continuous_subtype_val.comp continuous_fst)) continuous_const

/-- **A base-interior chart-0 set has no welded partner.** For `V ⊆ baseInterior`, the `resSetoid`
saturation of `Sum.inl '' V` is exactly `Sum.inl '' V` — the quotient-map preimage of `chart0 '' V`. -/
theorem preimage_chart0_image_baseInterior {V : Set ResChart} (hV : V ⊆ baseInterior) :
    Quotient.mk resSetoid ⁻¹' (chart0 '' V) = Sum.inl '' V := by
  ext a
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨p, hp, hmk⟩
    cases a with
    | inl q =>
      exact ⟨p, hp, by rw [chart0_inj_iff.mp hmk]⟩
    | inr q =>
      exact absurd (chart0_eq_chart1_iff.mp hmk).1 (ne_of_lt (hV hp))
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩

/-- **`chart0` is an open map on the base-interior** (via the empty-saturation lemma). -/
theorem isOpenMap_chart0_baseInterior :
    IsOpenMap (fun p : ↥baseInterior => chart0 p.1) := by
  intro W hW
  have hV : IsOpen (Subtype.val '' W) := isOpen_baseInterior.isOpenMap_subtype_val W hW
  have hVsub : (Subtype.val '' W : Set ResChart) ⊆ baseInterior := by
    rintro _ ⟨x, _, rfl⟩; exact x.2
  have himg : (fun p : ↥baseInterior => chart0 p.1) '' W = chart0 '' (Subtype.val '' W) := by
    rw [Set.image_image]
  rw [himg]
  have hqm : Topology.IsQuotientMap (Quotient.mk resSetoid : (ResChart ⊕ ResChart) → ResE) :=
    isQuotientMap_quotient_mk'
  refine hqm.isOpen_preimage.mp ?_
  have hopen : IsOpen (Sum.inl '' (Subtype.val '' W) : Set (ResChart ⊕ ResChart)) :=
    isOpenMap_inl _ hV
  exact (preimage_chart0_image_baseInterior hVsub).symm ▸ hopen

/-- **The chart-0 inclusion is an open embedding on the base-interior** `{‖z‖ < 1}`: the single-chart
neighborhood of every base-interior point. The interior descent engine (the
`KummerFreeQuotient.isOpenEmbedding_qmk_sepBall` sibling). -/
theorem isOpenEmbedding_chart0_baseInterior :
    Topology.IsOpenEmbedding (fun p : ↥baseInterior => chart0 p.1) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_
    isOpenMap_chart0_baseInterior
  · exact continuous_chart0.comp continuous_subtype_val
  · intro a b hab
    exact Subtype.ext (chart0_inj_iff.mp hab)

/-- **A base-interior chart-1 set has no welded partner** — the `chart1` mirror. A weld to `chart1 p`
would come from a chart-0 point `q` with `glued q p`, forcing `‖p.1‖ = ‖q.1‖⁻¹ = 1`, impossible on the
base-interior. -/
theorem preimage_chart1_image_baseInterior {V : Set ResChart} (hV : V ⊆ baseInterior) :
    Quotient.mk resSetoid ⁻¹' (chart1 '' V) = Sum.inr '' V := by
  ext a
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨p, hp, hmk⟩
    cases a with
    | inr q =>
      exact ⟨p, hp, by rw [chart1_inj_iff.mp hmk]⟩
    | inl q =>
      have hg : glued q p := chart0_eq_chart1_iff.mp hmk.symm
      have hpn : ‖(p.1 : ℂ)‖ = 1 := by rw [hg.2.1, norm_inv, hg.1, inv_one]
      exact absurd hpn (ne_of_lt (hV hp))
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩

/-- **`chart1` is an open map on the base-interior.** -/
theorem isOpenMap_chart1_baseInterior :
    IsOpenMap (fun p : ↥baseInterior => chart1 p.1) := by
  intro W hW
  have hV : IsOpen (Subtype.val '' W) := isOpen_baseInterior.isOpenMap_subtype_val W hW
  have hVsub : (Subtype.val '' W : Set ResChart) ⊆ baseInterior := by
    rintro _ ⟨x, _, rfl⟩; exact x.2
  have himg : (fun p : ↥baseInterior => chart1 p.1) '' W = chart1 '' (Subtype.val '' W) := by
    rw [Set.image_image]
  rw [himg]
  have hqm : Topology.IsQuotientMap (Quotient.mk resSetoid : (ResChart ⊕ ResChart) → ResE) :=
    isQuotientMap_quotient_mk'
  refine hqm.isOpen_preimage.mp ?_
  have hopen : IsOpen (Sum.inr '' (Subtype.val '' W) : Set (ResChart ⊕ ResChart)) :=
    isOpenMap_inr _ hV
  exact (preimage_chart1_image_baseInterior hVsub).symm ▸ hopen

/-- **The chart-1 inclusion is an open embedding on the base-interior** `{‖z‖ < 1}`. -/
theorem isOpenEmbedding_chart1_baseInterior :
    Topology.IsOpenEmbedding (fun p : ↥baseInterior => chart1 p.1) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_
    isOpenMap_chart1_baseInterior
  · exact continuous_chart1.comp continuous_subtype_val
  · intro a b hab
    exact Subtype.ext (chart1_inj_iff.mp hab)

/-- **`chart0` restricted to any OPEN subset of the base-interior is an open embedding** into `ResE`.
The uniform descent engine (subsumes `isOpenEmbedding_chart0_baseInterior`): any open `S ⊆ baseInterior`
carries no weld, so its `chart0`-image is open. This is what the boundary-collar charts (below) use. -/
theorem isOpenEmbedding_chart0_of_subset {S : Set ResChart} (hopen : IsOpen S)
    (hsub : S ⊆ baseInterior) :
    Topology.IsOpenEmbedding (fun p : ↥S => chart0 p.1) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_chart0.comp continuous_subtype_val)
    (fun a b hab => Subtype.ext (chart0_inj_iff.mp hab)) ?_
  intro W hW
  have hV : IsOpen (Subtype.val '' W) := hopen.isOpenMap_subtype_val W hW
  have hVsub : (Subtype.val '' W : Set ResChart) ⊆ baseInterior := by
    rintro _ ⟨x, _, rfl⟩; exact hsub x.2
  have himg : (fun p : ↥S => chart0 p.1) '' W = chart0 '' (Subtype.val '' W) := by
    rw [Set.image_image]
  rw [himg]
  have hqm : Topology.IsQuotientMap (Quotient.mk resSetoid : (ResChart ⊕ ResChart) → ResE) :=
    isQuotientMap_quotient_mk'
  refine hqm.isOpen_preimage.mp ?_
  exact (preimage_chart0_image_baseInterior hVsub).symm ▸ (isOpenMap_inl _ hV)

/-- **`chart1` restricted to any OPEN subset of the base-interior is an open embedding** into `ResE`. -/
theorem isOpenEmbedding_chart1_of_subset {S : Set ResChart} (hopen : IsOpen S)
    (hsub : S ⊆ baseInterior) :
    Topology.IsOpenEmbedding (fun p : ↥S => chart1 p.1) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_chart1.comp continuous_subtype_val)
    (fun a b hab => Subtype.ext (chart1_inj_iff.mp hab)) ?_
  intro W hW
  have hV : IsOpen (Subtype.val '' W) := hopen.isOpenMap_subtype_val W hW
  have hVsub : (Subtype.val '' W : Set ResChart) ⊆ baseInterior := by
    rintro _ ⟨x, _, rfl⟩; exact hsub x.2
  have himg : (fun p : ↥S => chart1 p.1) '' W = chart1 '' (Subtype.val '' W) := by
    rw [Set.image_image]
  rw [himg]
  have hqm : Topology.IsQuotientMap (Quotient.mk resSetoid : (ResChart ⊕ ResChart) → ResE) :=
    isQuotientMap_quotient_mk'
  refine hqm.isOpen_preimage.mp ?_
  exact (preimage_chart1_image_baseInterior hVsub).symm ▸ (isOpenMap_inr _ hV)

/-! ## §B. The boundary-collar region and its homeomorphism (deliverable 2, topological core)

The fiber-boundary `∂E = {‖w‖ = 1}` is approached through the **outer fiber collar** `1/2 < ‖w‖ ≤ 1`.
On the base-interior (`‖z‖ < 1`, away from the equator weld) this collar region descends through a single
chart. This section delivers the `KummerShellChart.collarHomeo` mirror — `chart0` restricted to the
base-interior collar region is a homeomorphism onto a neighborhood of the base-interior part of `∂E`. -/

/-- **The base-interior outer-collar region** of a chart: base-interior `‖z‖ < 1` and fiber in the outer
collar `1/2 < ‖w‖` (near the fiber boundary `‖w‖ = 1`). Open in `ResChart`, contained in `baseInterior`. -/
def collarRegion : Set ResChart := {p : ResChart | ‖(p.1 : ℂ)‖ < 1 ∧ 1 / 2 < ‖(p.2 : ℂ)‖}

theorem collarRegion_subset_baseInterior : collarRegion ⊆ baseInterior := fun _ hp => hp.1

theorem isOpen_collarRegion : IsOpen collarRegion := by
  rw [collarRegion, Set.setOf_and]
  refine isOpen_baseInterior.inter ?_
  exact isOpen_lt continuous_const
    (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))

/-- **`chart0` is an open embedding on the outer-collar region** — the collar chart's underlying
open embedding (base direction `z`, fiber angular `w/‖w‖`, radial `1 − ‖w‖`; assembly into the
half-space model is the localized residual). -/
theorem isOpenEmbedding_chart0_collarRegion :
    Topology.IsOpenEmbedding (fun p : ↥collarRegion => chart0 p.1) :=
  isOpenEmbedding_chart0_of_subset isOpen_collarRegion collarRegion_subset_baseInterior

/-- **The collar homeomorphism** `↥collarRegion ≃ₜ ↥(range …)`: `chart0` restricts to a homeomorphism
from the base-interior outer-collar region onto its (open) image in `ResE`, a neighborhood of the
base-interior part of `∂E`. The topological core of the boundary chart (the
`KummerShellChart.collarHomeo` mirror), delivered by §A's open embedding. -/
noncomputable def collarHomeoE :
    ↥collarRegion ≃ₜ ↥(Set.range (fun p : ↥collarRegion => chart0 p.1)) :=
  isOpenEmbedding_chart0_collarRegion.isEmbedding.toHomeomorph

end

end SKEFTHawking.KummerResolutionPieceBoundary
