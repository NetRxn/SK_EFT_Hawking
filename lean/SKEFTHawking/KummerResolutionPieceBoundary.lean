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

/-- **The boundary `∂E` inside the base-interior is exactly the radial-zero locus `‖w‖ = 1`.** For a
base-interior point (`‖z‖ < 1`), `chart0 p ∈ ∂E ↔ ‖w‖ = 1`: the only way to hit `∂E` is the honest
fiber boundary (a cross-chart weld would force `‖z‖ = 1`, excluded). This is the "boundary = radial
coordinate `1 − ‖w‖` vanishes" fact the manifold-with-boundary structure rests on. -/
theorem chart0_mem_boundaryE_iff {p : ResChart} (hp : ‖(p.1 : ℂ)‖ < 1) :
    chart0 p ∈ boundaryE ↔ ‖(p.2 : ℂ)‖ = 1 := by
  constructor
  · rintro ⟨q, hq, (h | h)⟩
    · rw [chart0_inj_iff.mp h]; exact hq
    · exact absurd (chart0_eq_chart1_iff.mp h).1 (ne_of_lt hp)
  · intro h; exact ⟨p, h, Or.inl rfl⟩

/-- The `chart1` mirror: on the base-interior, `chart1 p ∈ ∂E ↔ ‖w‖ = 1`. -/
theorem chart1_mem_boundaryE_iff {p : ResChart} (hp : ‖(p.1 : ℂ)‖ < 1) :
    chart1 p ∈ boundaryE ↔ ‖(p.2 : ℂ)‖ = 1 := by
  constructor
  · rintro ⟨q, hq, (h | h)⟩
    · have hg : glued q p := chart0_eq_chart1_iff.mp h.symm
      exact absurd (by rw [hg.2.1, norm_inv, hg.1, inv_one] : ‖(p.1 : ℂ)‖ = 1) (ne_of_lt hp)
    · rw [chart1_inj_iff.mp h]; exact hq
  · intro h; exact ⟨p, h, Or.inr rfl⟩

/-! ### §B.1. The fiber-collar radial coordinate `1 − ‖w‖`

The half-space radial coordinate of the boundary collar chart (the `1 − ‖v‖` of
`DiskChartGeneric.diskCollarChart`, oriented as in the disk original — the mirror of the shell's
`‖t‖ − ρ`): nonnegative on the closed disk fiber, and exactly zero on the fiber boundary `‖w‖ = 1`. -/

/-- **The fiber radial coordinate** `1 − ‖w‖` of a chart point: the half-space coordinate of the collar
chart, `≥ 0` on the disk fiber, `= 0` on the fiber boundary `∂E`. -/
def fiberRadial (p : ResChart) : ℝ := 1 - ‖(p.2 : ℂ)‖

theorem fiberRadial_nonneg (p : ResChart) : 0 ≤ fiberRadial p := by
  have := p.2.2; simp only [fiberRadial]; linarith

theorem fiberRadial_eq_zero_iff (p : ResChart) : fiberRadial p = 0 ↔ ‖(p.2 : ℂ)‖ = 1 := by
  rw [fiberRadial, sub_eq_zero, eq_comm]

theorem continuous_fiberRadial : Continuous fiberRadial :=
  continuous_const.sub (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))

/-! ### §B.2. The fiber-collar angular direction `w/‖w‖ ∈ S¹`

The base direction of the collar chart pairs the base coordinate `z` with the **fiber angular direction**
`w/‖w‖`, a point of the unit circle in `ℂ` (total on the collar, where `‖w‖ > 1/2 > 0`). The `shellDir`
mirror one dimension down. Charting this circle to `E¹` (via the banked `Circle` manifold structure) and
merging with the base `E²` into `E³` is the localized model-assembly step (§C). -/

/-- **The fiber unit circle** `S¹ ⊆ ℂ` — the codomain of the collar chart's angular direction. -/
abbrev FiberCircle : Type := {c : ℂ // ‖c‖ = 1}

/-- **The fiber angular direction** `w/‖w‖ ∈ S¹` of a collar chart point (total on the collar, where
`‖w‖ > 1/2 > 0`). The `KummerShellChart.shellDir` mirror one dimension down; complex-division form,
matching the parent file's `bdryMap` convention `w/(‖w‖ : ℂ)`. -/
def fiberDir (p : ResChart) (hp : 1 / 2 < ‖(p.2 : ℂ)‖) : FiberCircle :=
  ⟨(p.2 : ℂ) / (‖(p.2 : ℂ)‖ : ℂ), by
    have hpos : (0 : ℝ) < ‖(p.2 : ℂ)‖ := by linarith
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_self (ne_of_gt hpos)]⟩

@[simp] theorem fiberDir_coe (p : ResChart) (hp : 1 / 2 < ‖(p.2 : ℂ)‖) :
    (fiberDir p hp : ℂ) = (p.2 : ℂ) / (‖(p.2 : ℂ)‖ : ℂ) := rfl

/-- **Polar reconstruction**: `(1 − radial) · dir = w`, i.e. `‖w‖ · (w/‖w‖) = w` — the collar chart's
inverse recovers the fiber coordinate from `(angular, radial)`. -/
theorem fiber_polar_reconstruction (p : ResChart) (hp : 1 / 2 < ‖(p.2 : ℂ)‖) :
    ((1 - fiberRadial p : ℝ) : ℂ) * (fiberDir p hp : ℂ) = (p.2 : ℂ) := by
  have hne : ((‖(p.2 : ℂ)‖ : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt (by linarith)
  rw [fiberDir_coe, fiberRadial]
  push_cast
  field_simp
  ring

/-- The fiber angular direction is continuous on the collar region (`‖w‖ > 1/2 > 0`). -/
theorem continuous_fiberDir :
    Continuous fun p : ↥collarRegion => fiberDir p.1 p.2.2 := by
  apply Continuous.subtype_mk
  have hval : Continuous fun p : ↥collarRegion => ((p.1.2 : ℂ)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  have hden : Continuous fun p : ↥collarRegion => ((‖(p.1.2 : ℂ)‖ : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_norm.comp hval)
  refine hval.div hden (fun p => ?_)
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (by have := p.2.2; linarith)

/-! ### §B.3. The collar seam lands in the ℝP³ boundary identification (deliverable 4 step)

The collar's radial-zero seam `{p ∈ collarRegion ∣ fiberRadial p = 0} = {‖w‖ = 1}` is exactly the part of
`∂E` this chart sees, and `∂E = range bdryMapRP3` (banked `range_bdryMapRP3_eq_boundaryE`). So every collar
seam point is in the image of the `ℝP³ → ∂E` identification `bdryMapRP3` that `bdryHomeoRP3` upgrades — the
chart-level compatibility with the smooth ∂-weld K6′b consumes. -/

/-- **The collar seam lands in the ℝP³ boundary image.** A collar point with vanishing radial coordinate
(`fiberRadial p = 0`, i.e. `‖w‖ = 1`) has `chart0 p ∈ range bdryMapRP3` — the pinned `S³/±1` boundary
presentation `bdryHomeoRP3` identifies. The concrete chart-vs-`bdryHomeoRP3` compatibility step. -/
theorem collar_seam_mem_rp3_image {p : ResChart} (hp : p ∈ collarRegion)
    (hr : fiberRadial p = 0) : chart0 p ∈ Set.range bdryMapRP3 := by
  rw [range_bdryMapRP3_eq_boundaryE]
  exact (chart0_mem_boundaryE_iff hp.1).mpr ((fiberRadial_eq_zero_iff p).mp hr)

/-! ## §C. The `ℂ ≅ 𝓔²` bridge (the `KummerShellChart.toE4/ofE4` mirror one dimension down)

The base coordinate `z` and the fiber coordinate `w` of a chart point live in `ℂ`, whereas the boundary
model `ModelProd (𝓔 3) (EuclideanHalfSpace 1)` and the banked sphere/disk chart machinery
(`DiskChartGeneric`, `NSphere 1`) live in `EuclideanSpace ℝ (Fin _)`. This block builds the bridge
`toE2`/`ofE2` (mutually inverse, continuous) with `‖toE2 c‖ = ‖c‖` — so the round disks/circles in `ℂ`
are round in `𝓔²`. The one-dimension-down analogue of `KummerShellChart.toE4`/`ofE4` (which bridges
`ℝ × ℝ × ℝ × ℝ ≅ 𝓔⁴`). -/

/-- Pack a complex number into `𝓔² = EuclideanSpace ℝ (Fin 2)` by real/imaginary parts. The
`KummerShellChart.toE4` mirror one dimension down. -/
def toE2 (c : ℂ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![c.re, c.im]

/-- Unpack `𝓔²` into a complex number `re + im·I`. -/
def ofE2 (v : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨v.ofLp 0, v.ofLp 1⟩

/-- `‖toE2 c‖² = ‖c‖²` — the modulus is carried faithfully into `𝓔²`. -/
theorem norm_sq_toE2 (c : ℂ) : ‖toE2 c‖ ^ 2 = ‖c‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [toE2, WithLp.ofLp_toLp, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- `‖toE2 c‖ = ‖c‖`. -/
theorem norm_toE2 (c : ℂ) : ‖toE2 c‖ = ‖c‖ := by
  have := norm_sq_toE2 c
  nlinarith [norm_nonneg (toE2 c), norm_nonneg c]

theorem continuous_toE2 : Continuous toE2 := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re
  · exact Complex.continuous_im

theorem continuous_ofE2 : Continuous ofE2 := by
  have h0 : Continuous fun v : EuclideanSpace ℝ (Fin 2) => v.ofLp 0 :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h1 : Continuous fun v : EuclideanSpace ℝ (Fin 2) => v.ofLp 1 :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  have hc : Continuous fun v : EuclideanSpace ℝ (Fin 2) =>
      (v.ofLp 0 : ℂ) + (v.ofLp 1 : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp h0).add
      ((Complex.continuous_ofReal.comp h1).mul continuous_const)
  refine hc.congr (fun v => ?_)
  apply Complex.ext <;> simp [ofE2]

@[simp] theorem ofE2_toE2 (c : ℂ) : ofE2 (toE2 c) = c := by
  apply Complex.ext <;> simp [ofE2, toE2]

@[simp] theorem toE2_ofE2 (v : EuclideanSpace ℝ (Fin 2)) : toE2 (ofE2 v) = v := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;> simp [toE2, ofE2]

theorem toE2_injective : Function.Injective toE2 :=
  Function.LeftInverse.injective ofE2_toE2

/-! ## §D. The half-space boundary model and the base/fiber chart bridges

The E-side boundary model is `Model = ModelProd (𝓔 3) (EuclideanHalfSpace 1)` (4 real dims = 2 base +
1 fiber-angular + 1 fiber-radial-halfspace), matching `KummerShellChart.Model`. A collar chart of a
disk-bundle point `(z, w)` decomposes as **base** `z ∈ D²(ℂ)` (charted plainly into `𝓔²`, no boundary)
× **fiber** `w ∈ D²(ℂ)` (charted by the banked `DiskChartGeneric.diskCollarChart 1` into
`𝓔¹ × HalfSpace¹`), reshaped `𝓔² × (𝓔¹ × HalfSpace¹) → 𝓔³ × HalfSpace¹`. The fiber reuses the fully
banked polar collar chart of the closed disk one dimension down (`n = 1`, `S¹` stereographic) through
the `Disk(ℂ) ≃ₜ NDisk 1` bridge — no bespoke sphere-chart inverse work. -/

open SKEFTHawking.DiskChartGeneric (NDisk NSphere ballClamp diskDir assemble splitLo diskCollarChart)

/-- The E-side half-space boundary model `ModelProd (𝓔 3) (EuclideanHalfSpace 1)` (`= (𝓡 3).prod (𝓡∂ 1)`).
The `KummerShellChart.Model` mirror. -/
abbrev Model : Type := ModelProd (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 1)

/-- **The `Disk(ℂ) ≃ₜ NDisk 1` bridge** — the closed unit disk in `ℂ` is homeomorphic to the closed
unit ball `D²` in `𝓔²`, by the norm-faithful `toE2`/`ofE2`. Lets the fiber reuse the banked
`DiskChartGeneric` disk-chart machinery. -/
def diskHomeoNDisk1 : Disk ≃ₜ NDisk 1 where
  toFun z := ⟨toE2 (z : ℂ), by rw [mem_closedBall_zero_iff, norm_toE2]; exact z.2⟩
  invFun v := ⟨ofE2 (v : EuclideanSpace ℝ (Fin 2)), by
    rw [show ‖ofE2 (v : EuclideanSpace ℝ (Fin 2))‖ = ‖(v : EuclideanSpace ℝ (Fin 2))‖ from by
      rw [← norm_toE2, toE2_ofE2]]
    exact mem_closedBall_zero_iff.mp v.2⟩
  left_inv z := by apply Subtype.ext; simp [ofE2_toE2]
  right_inv v := by apply Subtype.ext; simp [toE2_ofE2]
  continuous_toFun := by apply Continuous.subtype_mk; exact continuous_toE2.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk; exact continuous_ofE2.comp continuous_subtype_val

/-- **The base chart** `Disk → 𝓔²`: `toE2` on the OPEN base disk `{‖z‖ < 1}` (base-interior), a
homeomorphism onto the open ball `{‖v‖ < 1} ⊆ 𝓔²`. The base half of the collar chart — the base `z` is
charted plainly (no boundary; the fiber carries the manifold boundary). Junk-clamped off-source by
`ballClamp`. -/
def baseDiskChart : OpenPartialHomeomorph Disk (EuclideanSpace ℝ (Fin 2)) where
  source := {z : Disk | ‖(z : ℂ)‖ < 1}
  target := {v : EuclideanSpace ℝ (Fin 2) | ‖v‖ < 1}
  toFun z := toE2 (z : ℂ)
  invFun v := ⟨ofE2 (ballClamp 1 v : EuclideanSpace ℝ (Fin 2)), by
    rw [show ‖ofE2 (ballClamp 1 v : EuclideanSpace ℝ (Fin 2))‖
        = ‖(ballClamp 1 v : EuclideanSpace ℝ (Fin 2))‖ from by rw [← norm_toE2, toE2_ofE2]]
    exact mem_closedBall_zero_iff.mp (ballClamp 1 v).2⟩
  map_source' z hz := by show ‖toE2 (z : ℂ)‖ < 1; rw [norm_toE2]; exact hz
  map_target' v hv := by
    show ‖ofE2 (ballClamp 1 v : EuclideanSpace ℝ (Fin 2))‖ < 1
    rw [DiskChartGeneric.ballClamp_coe_of_norm_le (le_of_lt hv),
      show ‖ofE2 (v : EuclideanSpace ℝ (Fin 2))‖ = ‖(v : EuclideanSpace ℝ (Fin 2))‖ from by
        rw [← norm_toE2, toE2_ofE2]]
    exact hv
  left_inv' z hz := by
    apply Subtype.ext
    show ofE2 (ballClamp 1 (toE2 (z : ℂ)) : EuclideanSpace ℝ (Fin 2)) = (z : ℂ)
    rw [DiskChartGeneric.ballClamp_coe_of_norm_le (by rw [norm_toE2]; exact le_of_lt hz), ofE2_toE2]
  right_inv' v hv := by
    show toE2 (ofE2 (ballClamp 1 v : EuclideanSpace ℝ (Fin 2))) = v
    rw [DiskChartGeneric.ballClamp_coe_of_norm_le (le_of_lt hv), toE2_ofE2]
  open_source := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  open_target := isOpen_lt continuous_norm continuous_const
  continuousOn_toFun := (continuous_toE2.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    exact continuous_ofE2.comp (continuous_subtype_val.comp (DiskChartGeneric.continuous_ballClamp 1))

/-- **The model reshape** `𝓔² × (𝓔¹ × HalfSpace¹) ≃ₜ 𝓔³ × HalfSpace¹`: merge the base `𝓔²` and the
fiber-angular `𝓔¹` into `𝓔³` (via the banked `assemble 2`/`splitLo 2` — playing the
`EuclideanSpace.finAddEquivProd` role), keeping the fiber-radial `HalfSpace¹` untouched. -/
def reshapeModel :
    (EuclideanSpace ℝ (Fin 2) × ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)) ≃ₜ Model where
  toFun q := (assemble 2 q.1 (q.2.1.ofLp 0), q.2.2)
  invFun r := (splitLo 2 r.1, (WithLp.toLp 2 (fun _ : Fin 1 => r.1.ofLp (Fin.last 2)), r.2))
  left_inv q := by
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · exact DiskChartGeneric.splitLo_assemble 2 q.1 (q.2.1.ofLp 0)
    · show WithLp.toLp 2 (fun _ : Fin 1 => (assemble 2 q.1 (q.2.1.ofLp 0)).ofLp (Fin.last 2)) = q.2.1
      rw [DiskChartGeneric.assemble_ofLp_last]; exact DiskChartGeneric.toLp_ofLp_fin_one _
  right_inv r := by
    refine Prod.ext ?_ rfl
    show assemble 2 (splitLo 2 r.1)
        ((WithLp.toLp 2 (fun _ : Fin 1 => r.1.ofLp (Fin.last 2))).ofLp 0) = r.1
    rw [show (WithLp.toLp 2 (fun _ : Fin 1 => r.1.ofLp (Fin.last 2))).ofLp 0
        = r.1.ofLp (Fin.last 2) from by simp]
    exact DiskChartGeneric.assemble_splitLo 2 r.1
  continuous_toFun := by
    refine Continuous.prodMk ?_ (continuous_snd.comp continuous_snd)
    exact (DiskChartGeneric.continuous_assemble 2).comp (Continuous.prodMk continuous_fst
      ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp (continuous_fst.comp continuous_snd)))
  continuous_invFun := by
    refine Continuous.prodMk ((DiskChartGeneric.continuous_splitLo 2).comp continuous_fst) ?_
    refine Continuous.prodMk ?_ continuous_snd
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi; intro _
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (Fin.last 2)).comp continuous_fst

/-- **The fiber collar chart** `Disk → ModelProd 𝓔¹ HalfSpace¹` — the banked
`DiskChartGeneric.diskCollarChart 1` transported through the `Disk ≃ₜ NDisk 1` bridge:
`w ↦ (chart_{S¹}(w/‖w‖), 1 − ‖w‖)`. Reuses the full sphere-chart-inverse machinery one dimension down. -/
def fiberCollarChart (u₀ : NSphere 1) :
    OpenPartialHomeomorph Disk (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)) :=
  diskHomeoNDisk1.toOpenPartialHomeomorph.trans (diskCollarChart 1 u₀)

/-- **The disk-bundle collar chart on `ResChart`** at fiber-base direction `u₀ ∈ S¹`: base `z` charted
into `𝓔²`, fiber `w` into `𝓔¹ × HalfSpace¹` (polar), reshaped into `𝓔³ × HalfSpace¹`. The
`KummerShellChart.shellCollarChart` analogue on the disk bundle — pure packaging of the banked bricks. -/
def resChartCollarChart (u₀ : NSphere 1) : OpenPartialHomeomorph ResChart Model :=
  (baseDiskChart.prod (fiberCollarChart u₀)).trans reshapeModel.toOpenPartialHomeomorph

/-! ## §E. The E-side boundary collar chart on `ResE` (deliverable 2 complete)

The `ResChart` collar chart (§D) is restricted to the base-interior subtype `↥baseInterior` — where
`chart0` is an open embedding into `ResE` (§A) — and then **lifted** along that open embedding by
`OpenPartialHomeomorph.lift_openEmbedding` (the `KummerBoundaryChart.boundaryChart` compositional
pattern). No bespoke junk-value / open-map work: every obligation is discharged by the combinators. -/

instance instNonemptyBaseInterior : Nonempty ↥baseInterior :=
  ⟨⟨(⟨0, by simp⟩, ⟨0, by simp⟩), by simp [baseInterior]⟩⟩

/-- **The `ResChart` collar chart restricted to `↥baseInterior`** — precomposed with the open embedding
`Subtype.val : ↥baseInterior → ResChart`, so its source type matches the `chart0` open embedding for the
lift. -/
def collarChartInner (u₀ : NSphere 1) : OpenPartialHomeomorph (↥baseInterior) Model :=
  (Topology.IsOpenEmbedding.toOpenPartialHomeomorph (Subtype.val)
    isOpen_baseInterior.isOpenEmbedding_subtypeVal).trans (resChartCollarChart u₀)

/-- **The E-side boundary collar chart on `ResE`** at fiber-base direction `u₀ ∈ S¹` — the
`OpenPartialHomeomorph ResE Model` charting the base-interior part of the disk bundle onto the half-space
model `ModelProd (𝓔 3) (EuclideanHalfSpace 1)`. Built by lifting `collarChartInner` along the open
embedding `chart0 : ↥baseInterior → ResE` (§A); the fiber boundary `‖w‖ = 1` lands on the half-space wall.
The `KummerBoundaryChart.boundaryChart` mirror on the resolution piece `E`. -/
def collarChart (u₀ : NSphere 1) : OpenPartialHomeomorph ResE Model :=
  (collarChartInner u₀).lift_openEmbedding isOpenEmbedding_chart0_baseInterior

/-! ## §F. The E-side interior chart on `ResE` (deliverable 3, interior half)

The interior chart mirrors the collar chart exactly, swapping the banked fiber **collar** chart
`diskCollarChart 1` for the banked fiber **interior** chart `diskInteriorChart 1` — which charts the OPEN
fiber disk `{‖w‖ < 1}` (including the fiber centre `w = 0`, the zero section, where the collar's angular
direction is undefined) into the **interior** of the half-space (`radial > 0`). Base `z` is charted as
before. Both fiber charts use the SAME radial coordinate `‖w‖` (interior `‖w‖ < 1`, collar `‖w‖ > 0`), so
they overlap on `0 < ‖w‖ < 1` — the coverage discipline that avoids the metric-vs-chart-radius gap (the
settled route fact): no separate metric interior region, hence no gap. -/

/-- **The fiber interior chart** `Disk → ModelProd 𝓔¹ HalfSpace¹` — the banked
`DiskChartGeneric.diskInteriorChart 1` transported through the `Disk ≃ₜ NDisk 1` bridge. Charts the open
fiber disk (incl. the centre) into the interior of the half-space model. -/
def fiberInteriorChart :
    OpenPartialHomeomorph Disk (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)) :=
  diskHomeoNDisk1.toOpenPartialHomeomorph.trans (DiskChartGeneric.diskInteriorChart 1)

/-- **The disk-bundle interior chart on `ResChart`**: base `z → 𝓔²`, fiber `w → 𝓔¹ × HalfSpace¹`
(interior), reshaped into `𝓔³ × HalfSpace¹`. -/
def resChartInteriorChart : OpenPartialHomeomorph ResChart Model :=
  (baseDiskChart.prod fiberInteriorChart).trans reshapeModel.toOpenPartialHomeomorph

/-- **The `ResChart` interior chart restricted to `↥baseInterior`** — the `chart0`-open-embedding
source-type match for the lift. -/
def interiorChartInner : OpenPartialHomeomorph (↥baseInterior) Model :=
  (Topology.IsOpenEmbedding.toOpenPartialHomeomorph (Subtype.val)
    isOpen_baseInterior.isOpenEmbedding_subtypeVal).trans resChartInteriorChart

/-- **The E-side interior chart on `ResE`** — the `OpenPartialHomeomorph ResE Model` charting the
base-interior fiber-interior part of the disk bundle (incl. the zero section) onto the interior of the
half-space model `{q | 0 < q.2.val.ofLp 0}`. Built by lifting `interiorChartInner` along the `chart0`
open embedding. Coexists with the boundary collar charts of §E. -/
def interiorChart : OpenPartialHomeomorph ResE Model :=
  interiorChartInner.lift_openEmbedding isOpenEmbedding_chart0_baseInterior

/-! ## §G. The `chart1`-based mirror charts (the other base disk)

The base sphere `S²` is two disks welded at the equator; §E/§F chart the `chart0` base disk `{‖z‖ < 1}`.
The `chart1` base disk is charted by the SAME inner charts (`collarChartInner`, `interiorChartInner`),
lifted instead along the `chart1` open embedding (`isOpenEmbedding_chart1_baseInterior`, §A). Together the
`chart0`- and `chart1`-based charts cover every point of `ResE` OFF the base equator `‖z‖ = 1`. -/

/-- **The `chart1`-based boundary collar chart** — `collarChartInner` lifted along `chart1`. -/
def collarChart1 (u₀ : NSphere 1) : OpenPartialHomeomorph ResE Model :=
  (collarChartInner u₀).lift_openEmbedding isOpenEmbedding_chart1_baseInterior

/-- **The `chart1`-based interior chart** — `interiorChartInner` lifted along `chart1`. -/
def interiorChart1 : OpenPartialHomeomorph ResE Model :=
  interiorChartInner.lift_openEmbedding isOpenEmbedding_chart1_baseInterior

/-! ## §H. The off-equator covering (deliverable 3, coverage lemma)

Every point of `ResE` with a `chart0` representative in the base-interior (`‖z‖ < 1`) lies in the source
of the interior chart (if `‖w‖ < 1`) or a collar chart (if `w ≠ 0`), the two overlapping in the SAME
fiber-radial coordinate `‖w‖`. The `chart1` mirror is symmetric. Together these cover every point OFF the
base equator `‖z‖ = 1` — the covering lemma the manifold-with-boundary instance rests on (the residual
`chartAt` dispatch adds only the straddling equator chart). -/

/-- A base-interior fiber-interior point (`‖z‖ < 1`, `‖w‖ < 1`) lies in the interior chart's source. -/
theorem mem_interiorChart_source {p : ResChart} (hz : ‖(p.1 : ℂ)‖ < 1)
    (hw : ‖(p.2 : ℂ)‖ < 1) : chart0 p ∈ interiorChart.source := by
  rw [interiorChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨⟨p, hz⟩, ?_, rfl⟩
  simp only [interiorChartInner, OpenPartialHomeomorph.trans_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_univ,
    true_and, Set.mem_preimage]
  show p ∈ resChartInteriorChart.source
  simp only [resChartInteriorChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.prod_source,
    Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_preimage, Set.mem_prod]
  refine ⟨hz, ?_⟩
  simp only [fiberInteriorChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_univ, true_and,
    Set.mem_preimage]
  show ‖((diskHomeoNDisk1 p.2 : NDisk 1) : EuclideanSpace ℝ (Fin 2))‖ < 1
  rw [show ((diskHomeoNDisk1 p.2 : NDisk 1) : EuclideanSpace ℝ (Fin 2)) = toE2 (p.2 : ℂ) from rfl,
    norm_toE2]
  exact hw

/-- A base-interior off-fiber-centre point (`‖z‖ < 1`, `w ≠ 0`) lies in the source of the collar chart at
its own fiber direction `u₀ = diskDir (w/‖w‖)` — every point is in its own stereographic chart. -/
theorem mem_collarChart_source {p : ResChart} (hz : ‖(p.1 : ℂ)‖ < 1) (hw : (p.2 : ℂ) ≠ 0) :
    chart0 p ∈ (collarChart (diskDir 1 (diskHomeoNDisk1 p.2))).source := by
  rw [collarChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨⟨p, hz⟩, ?_, rfl⟩
  simp only [collarChartInner, OpenPartialHomeomorph.trans_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_univ,
    true_and, Set.mem_preimage]
  show p ∈ (resChartCollarChart (diskDir 1 (diskHomeoNDisk1 p.2))).source
  simp only [resChartCollarChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.prod_source,
    Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_preimage, Set.mem_prod]
  refine ⟨hz, ?_⟩
  simp only [fiberCollarChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_univ, true_and,
    Set.mem_preimage]
  refine ⟨?_, mem_chart_source (EuclideanSpace ℝ (Fin 1)) _⟩
  show ((diskHomeoNDisk1 p.2 : NDisk 1) : EuclideanSpace ℝ (Fin 2)) ≠ 0
  rw [show ((diskHomeoNDisk1 p.2 : NDisk 1) : EuclideanSpace ℝ (Fin 2)) = toE2 (p.2 : ℂ) from rfl]
  intro h0
  exact hw (norm_eq_zero.mp (by rw [← norm_toE2, h0, norm_zero]))

/-- **The off-equator covering.** Every point of `ResE` with a `chart0` representative in the
base-interior (`‖z‖ < 1`) is covered: it lies in the interior chart's source (fiber interior `‖w‖ < 1`)
or in a collar chart's source (fiber off-centre `w ≠ 0`). The two overlap on `0 < ‖w‖ < 1`, in the SAME
fiber-radial coordinate `‖w‖` — the coverage discipline (no metric-vs-chart-radius gap). -/
theorem chart0_baseInterior_covered {p : ResChart} (hz : ‖(p.1 : ℂ)‖ < 1) :
    chart0 p ∈ interiorChart.source ∨ ∃ u₀, chart0 p ∈ (collarChart u₀).source := by
  by_cases hw : ‖(p.2 : ℂ)‖ < 1
  · exact Or.inl (mem_interiorChart_source hz hw)
  · exact Or.inr ⟨_, mem_collarChart_source hz (by
      intro h0; exact hw (by rw [h0, norm_zero]; norm_num))⟩

/-! ## §Z. STATUS — the K6′a Leg-2 E-side certificate

**GREEN here — deliverable (1) COMPLETE; deliverable (2) topological core + coordinate infrastructure;
deliverable (4) seam step:**

Deliverable (1) — **the interior open-embedding descent** (§A):
- `isOpenEmbedding_chart0_baseInterior` / `isOpenEmbedding_chart1_baseInterior` (and the uniform
  `_of_subset` forms) — `chart0`/`chart1` restricted to any open subset of the base-interior `{‖z‖ < 1}`
  is an open embedding into `ResE`. The single-chart neighborhood of every point away from the equator
  weld (the `KummerFreeQuotient.isOpenEmbedding_qmk_sepBall` sibling; simpler — clutch weld, not a free
  action). Foundation: `preimage_chart0/1_image_baseInterior` (the empty-saturation lemma).

Deliverable (2) — **the boundary-collar region + coordinates** (§B):
- `collarRegion = {‖z‖ < 1 ∧ 1/2 < ‖w‖}` (base-interior outer fiber collar, `IsOpen`), and
  `collarHomeoE : ↥collarRegion ≃ₜ ↥(range …)` — `chart0` restricts to a homeomorphism onto its open
  image, a neighborhood of the base-interior part of `∂E` (the `KummerShellChart.collarHomeo` mirror).
- `chart0/1_mem_boundaryE_iff` — on the base-interior, `∂E` is EXACTLY the radial-zero locus `‖w‖ = 1`
  ("boundary ⟺ radial coordinate `1 − ‖w‖` vanishes").
- `fiberRadial = 1 − ‖w‖` (the half-space coordinate; `fiberRadial_nonneg`, `fiberRadial_eq_zero_iff`,
  `continuous_fiberRadial`) — the DiskChart-oriented radial mirror of the shell's `‖t‖ − ρ`.
- `fiberDir : ResChart → S¹`, `w ↦ w/‖w‖` (the angular direction; `fiberDir_coe`,
  `fiber_polar_reconstruction : (1 − radial)·dir = w`, `continuous_fiberDir`) — the `shellDir` mirror.

Deliverable (4) — **the smooth ∂-identification step** (§B.3):
- `collar_seam_mem_rp3_image` — the collar's radial-zero seam lands in `range bdryMapRP3`, the pinned
  `S³/±1` presentation `bdryHomeoRP3` identifies. The concrete chart-vs-`bdryHomeoRP3` compatibility hook.

Deliverable (2/3) — **the half-space-model charts on `ResE`** (§C–§F, K6′a Leg-2 completion, this pass):
- `toE2`/`ofE2` (`§C`) — the `ℂ ≅ 𝓔²` bridge (norm-faithful, continuous, mutually inverse), the
  `KummerShellChart.toE4`/`ofE4` mirror one dimension down.
- `diskHomeoNDisk1 : Disk ≃ₜ NDisk 1`, `baseDiskChart`, `reshapeModel : 𝓔² × (𝓔¹ × HS¹) ≃ₜ 𝓔³ × HS¹`
  (`§D`) — the base chart + the `𝓔² ⊕ 𝓔¹ → 𝓔³` assembly (via banked `assemble 2`/`splitLo 2`, the
  `EuclideanSpace.finAddEquivProd` role) adjoining `fiberRadial → HalfSpace¹`.
- `collarChart u₀ : OpenPartialHomeomorph ResE Model` (`§E`) — the boundary collar chart, base `z → 𝓔²` ×
  fiber `w → 𝓔¹ × HalfSpace¹` (banked `diskCollarChart 1` through the bridge) reshaped, then lifted along
  the `chart0` open embedding by `lift_openEmbedding`. The `KummerBoundaryChart.boundaryChart` mirror;
  kernel-pure `{propext, Classical.choice, Quot.sound}`.
- `interiorChart : OpenPartialHomeomorph ResE Model` (`§F`) — the interior chart, identical construction
  with the banked `diskInteriorChart 1` (covers the fiber centre `w = 0`; image in the half-space
  interior `radial > 0`). Overlaps the collar on `0 < ‖w‖ < 1` in the SAME radial coordinate `‖w‖` — the
  coverage discipline that structurally avoids the metric-vs-chart-radius gap. Kernel-pure.
- `collarChart1`/`interiorChart1` (`§G`) — the `chart1`-based mirrors (the SAME inner charts lifted along
  `chart1` instead of `chart0`), charting the other base disk.
- `mem_interiorChart_source`/`mem_collarChart_source`/`chart0_baseInterior_covered` (`§H`) — **the
  off-equator covering lemma**: every point with a `chart0` base-interior (`‖z‖ < 1`) representative lies
  in the interior chart's source (`‖w‖ < 1`) or a collar chart's source (`w ≠ 0`, at its own fiber
  direction `u₀ = diskDir (w/‖w‖)`). The `chart1` mirror is symmetric. Kernel-pure.

**RESIDUAL (walls, localized precisely) — the charted-space instance and the manifold instance:**

1. **`ChartedSpace Model ResE`** (deliverable 3) — `chartAt` dispatch. The `chart0`/`chart1`-based charts
   above cover every point OFF the base equator `‖z‖ = 1` (`chart0_baseInterior_covered` + its mirror).
   The base-equator locus (`chart0 p`, `‖p.1‖ = 1`; a circle × fiber) is the residual. **Not** a single
   straddling chart: over the equator circle the disk bundle has **Euler number −2** (the `z²` clutch
   twist), so it is topologically nontrivial and admits **no** product base-annulus × fiber
   trivialization. The equator neighborhood must be covered by a **family of charts over base ARCS** (each
   arc contractible ⟹ the bundle trivializes over it), with the base-arc coordinate glued across the weld
   through the banked `contDiffOn_clutch` (parent §1) transition `z ↦ z⁻¹`. This is the one genuinely-new
   geometric brick (nontrivial-bundle coverage), beyond the base-interior packaging above.

2. **`IsManifold` + smooth `bdryHomeoRP3`** (deliverables 3/4) — the transition classes:
   interior-interior = `contDiffOn_clutch` (banked); collar-collar and collar-interior = the fiber polar
   change of coordinates (smooth off `w = 0`, and the collar avoids `w = 0` since `‖w‖ > 1/2`); the smooth
   `∂E ≅ ℝP³` upgrade of `bdryHomeoRP3` in these charts.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom. -/

end

end SKEFTHawking.KummerResolutionPieceBoundary
