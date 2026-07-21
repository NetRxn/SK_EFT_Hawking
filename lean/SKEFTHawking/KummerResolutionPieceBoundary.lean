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

/-- The `chart1` mirror of `mem_interiorChart_source` (same inner chart, lifted along `chart1`). -/
theorem mem_interiorChart1_source {p : ResChart} (hz : ‖(p.1 : ℂ)‖ < 1)
    (hw : ‖(p.2 : ℂ)‖ < 1) : chart1 p ∈ interiorChart1.source := by
  rw [interiorChart1, OpenPartialHomeomorph.lift_openEmbedding_source]
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

/-- The `chart1` mirror of `mem_collarChart_source`. -/
theorem mem_collarChart1_source {p : ResChart} (hz : ‖(p.1 : ℂ)‖ < 1) (hw : (p.2 : ℂ) ≠ 0) :
    chart1 p ∈ (collarChart1 (diskDir 1 (diskHomeoNDisk1 p.2))).source := by
  rw [collarChart1, OpenPartialHomeomorph.lift_openEmbedding_source]
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

/-- **The off-equator covering, `chart1` side.** The symmetric mirror of `chart0_baseInterior_covered`. -/
theorem chart1_baseInterior_covered {p : ResChart} (hz : ‖(p.1 : ℂ)‖ < 1) :
    chart1 p ∈ interiorChart1.source ∨ ∃ u₀, chart1 p ∈ (collarChart1 u₀).source := by
  by_cases hw : ‖(p.2 : ℂ)‖ < 1
  · exact Or.inl (mem_interiorChart1_source hz hw)
  · exact Or.inr ⟨_, mem_collarChart1_source hz (by
      intro h0; exact hw (by rw [h0, norm_zero]; norm_num))⟩

/-! ## §I. The equatorial annulus trivialization (the last ChartedSpace gap)

The base-equator locus (`chart0 p`, `‖p.1‖ = 1`) is the residual left by §A–§H's base-interior charts.
This section charts an OPEN neighborhood of the ENTIRE equator by a SINGLE trivialization over the base
annulus `{1/2 < ‖β‖ < 2}`, resolving the equator gap.

**Why a product annulus chart exists** (and the Euler−2 twist does NOT obstruct it): over the base
equator circle the disk bundle is an oriented `D²`-bundle over `S¹`; every such bundle is trivial
(`π₀(SO(2)) = 0`). The clutch fiber factor `w ↦ z²·w` is a ROTATION on the equator (`‖z‖ = 1 ⟹
‖z²‖ = 1`), so it preserves the disk; the trivializing fiber coordinate is `ζ = (β/‖β‖)·w`, the fiber
`w` twisted by the UNIT angular part `β/‖β‖` — disk-preserving on BOTH chart sides. (The naive `z²`
factor blows the disk up off the equator; the angular part does not. The Euler−2 obstruction is the
global `S²` invariant — the obstruction to extending the trivialization over a DISK — not seen over the
equator annulus.) The base coordinate is `β = z` on the chart-0 side (`‖z‖ ≤ 1`) and `β = z'⁻¹` on the
chart-1 side (`‖z'‖ ≤ 1`), agreeing on the weld `‖z‖ = 1` (`z'⁻¹ = z`), sweeping the annulus. -/

/-- **Regularized angular direction** `z / max(‖z‖, 1/2)` — equals `z/‖z‖` for `‖z‖ ≥ 1/2` (the annulus
region) but is continuous EVERYWHERE (denominator `≥ 1/2 > 0`), with `‖regDir z‖ ≤ 1`. Junk-regularized
so the trivialization's forward map descends to a GLOBALLY continuous `Quotient.lift`. -/
def regDir (z : ℂ) : ℂ := z / ((max ‖z‖ (1 / 2) : ℝ) : ℂ)

theorem max_norm_half_pos (z : ℂ) : 0 < max ‖z‖ (1 / 2) :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

theorem regDir_eq {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : regDir z = z / (‖z‖ : ℂ) := by
  rw [regDir, max_eq_left hz]

theorem norm_regDir_le (z : ℂ) : ‖regDir z‖ ≤ 1 := by
  rw [regDir, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (max_norm_half_pos z),
    div_le_one (max_norm_half_pos z)]
  exact le_max_left _ _

theorem continuous_regDir : Continuous regDir := by
  refine Continuous.div continuous_id ?_ (fun z => ?_)
  · exact Complex.continuous_ofReal.comp (continuous_norm.max continuous_const)
  · simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (max_norm_half_pos z)

/-- **Regularized inverse** `conj z / max(‖z‖², 1/4)` — equals `z⁻¹` for `‖z‖ ≥ 1/2` but is continuous
EVERYWHERE (denominator `≥ 1/4 > 0`). The chart-1 base coordinate `β = z'⁻¹`, junk-regularized. -/
def regInv (z : ℂ) : ℂ := (starRingEnd ℂ) z / ((max (‖z‖ ^ 2) (1 / 4) : ℝ) : ℂ)

theorem max_normSq_quarter_pos (z : ℂ) : 0 < max (‖z‖ ^ 2) (1 / 4) :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

theorem regInv_eq {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : regInv z = z⁻¹ := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by positivity)
  have hmax : max (‖z‖ ^ 2) (1 / 4) = ‖z‖ ^ 2 := max_eq_left (by nlinarith)
  rw [regInv, hmax, Complex.sq_norm, Complex.inv_def, div_eq_mul_inv, Complex.ofReal_inv]

theorem continuous_regInv : Continuous regInv := by
  refine Continuous.div Complex.continuous_conj ?_ (fun z => ?_)
  · exact Complex.continuous_ofReal.comp ((continuous_norm.pow 2).max continuous_const)
  · simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (max_normSq_quarter_pos z)

/-- **The base-annulus locus of a single chart**: `{p : D² × D² ∣ 1/2 < ‖z‖}`. Open; both the chart-0
and chart-1 sides of the equatorial annulus region descend from it. -/
def annulusChartSet : Set ResChart := {p : ResChart | 1 / 2 < ‖(p.1 : ℂ)‖}

theorem isOpen_annulusChartSet : IsOpen annulusChartSet :=
  isOpen_lt continuous_const (continuous_norm.comp (continuous_subtype_val.comp continuous_fst))

/-- **The equatorial annulus region** in `ResE`: the union of both chart sides' base-annulus loci
(`chart0 '' {1/2<‖z‖}` covering `‖β‖ ∈ (1/2, 1]`, `chart1 '' {1/2<‖z'‖}` covering `‖β‖ ∈ [1, 2)`),
glued along the equator `‖z‖ = 1`. An OPEN neighborhood of the entire base equator. -/
def annulusRegion : Set ResE := chart0 '' annulusChartSet ∪ chart1 '' annulusChartSet

/-- **The annulus region is saturated**: its `Quotient.mk` preimage is exactly the two-chart union of
the base-annulus loci — the empty-extra-weld lemma (a base-annulus point's only welds stay inside the
annulus loci, since a weld forces `‖z‖ = 1 > 1/2`). -/
theorem preimage_annulusRegion :
    Quotient.mk resSetoid ⁻¹' annulusRegion
      = Sum.inl '' annulusChartSet ∪ Sum.inr '' annulusChartSet := by
  ext a
  simp only [Set.mem_preimage, annulusRegion, Set.mem_union, Set.mem_image]
  constructor
  · rintro (⟨p, hp, hmk⟩ | ⟨q, hq, hmk⟩)
    · cases a with
      | inl a0 => exact Or.inl ⟨a0, chart0_inj_iff.mp hmk ▸ hp, rfl⟩
      | inr a0 =>
        have hg : glued p a0 := chart0_eq_chart1_iff.mp hmk
        exact Or.inr ⟨a0, by
          show (1 : ℝ) / 2 < ‖(a0.1 : ℂ)‖; rw [hg.2.1, norm_inv, hg.1, inv_one]; norm_num, rfl⟩
    · cases a with
      | inl a0 =>
        have hg : glued a0 q := chart0_eq_chart1_iff.mp hmk.symm
        exact Or.inl ⟨a0, by show (1 : ℝ) / 2 < ‖(a0.1 : ℂ)‖; rw [hg.1]; norm_num, rfl⟩
      | inr a0 => exact Or.inr ⟨a0, chart1_inj_iff.mp hmk ▸ hq, rfl⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr ⟨q, hq, rfl⟩

theorem isOpen_annulusRegion : IsOpen annulusRegion := by
  have hqm : Topology.IsQuotientMap (Quotient.mk resSetoid : (ResChart ⊕ ResChart) → ResE) :=
    isQuotientMap_quotient_mk'
  refine hqm.isOpen_preimage.mp ?_
  rw [preimage_annulusRegion]
  exact (isOpenMap_inl _ isOpen_annulusChartSet).union (isOpenMap_inr _ isOpen_annulusChartSet)

/-- **The trivializing fiber coordinate** `ζ = regDir z · w = (z/‖z‖)·w` — the fiber `w` twisted by the
unit angular part of the base coordinate. Stays in the disk (`‖ζ‖ = ‖regDir z‖·‖w‖ ≤ 1`), because the
angular twist is a rotation. -/
def trivFiber (z : ℂ) (w : Disk) : Disk :=
  ⟨regDir z * (w : ℂ), by
    rw [norm_mul]; exact mul_le_one₀ (norm_regDir_le z) (norm_nonneg _) w.2⟩

@[simp] theorem trivFiber_coe (z : ℂ) (w : Disk) : (trivFiber z w : ℂ) = regDir z * (w : ℂ) := rfl

theorem continuous_trivFiber : Continuous (fun p : ℂ × Disk => trivFiber p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_regDir.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

/-- The forward trivialization on the two-chart disjoint union: chart-0 side `(z,w) ↦ (z, regDir z · w)`,
chart-1 side `(z',w') ↦ (z'⁻¹, regDir z' · w')` (base coordinate `β = z` resp. `z'⁻¹ = regInv z'`;
fiber `ζ = (angular)·w`). -/
def annulusTrivRaw : ResChart ⊕ ResChart → ℂ × Disk :=
  Sum.elim (fun p => ((p.1 : ℂ), trivFiber (p.1 : ℂ) p.2))
           (fun q => (regInv (q.1 : ℂ), trivFiber (q.1 : ℂ) q.2))

theorem continuous_annulusTrivRaw : Continuous annulusTrivRaw := by
  apply Continuous.sumElim
  · exact (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_trivFiber.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  · exact (continuous_regInv.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      (continuous_trivFiber.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))

/-- **The forward map respects the weld**: on a glued pair `glued p q` (`‖z‖ = 1`), both chart sides map
to `(z, z·w)`. This is what lets the forward trivialization descend to `ResE`. -/
theorem annulusTrivRaw_glued {p q : ResChart} (hg : glued p q) :
    annulusTrivRaw (Sum.inl p) = annulusTrivRaw (Sum.inr q) := by
  have hp1 : ‖(p.1 : ℂ)‖ = 1 := hg.1
  have hp0 : (p.1 : ℂ) ≠ 0 := norm_ne_zero_iff.mp (by rw [hp1]; norm_num)
  have hq1n : ‖(q.1 : ℂ)‖ = 1 := by rw [hg.2.1, norm_inv, hp1, inv_one]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · show (p.1 : ℂ) = regInv (q.1 : ℂ)
    rw [regInv_eq (by rw [hq1n]; norm_num), hg.2.1, inv_inv]
  · show regDir (p.1 : ℂ) * (p.2 : ℂ) = regDir (q.1 : ℂ) * (q.2 : ℂ)
    rw [regDir_eq (by rw [hp1]; norm_num), regDir_eq (by rw [hq1n]; norm_num), hg.2.1, hg.2.2,
      norm_inv, hp1, inv_one]
    push_cast
    field_simp

/-- **The forward trivialization** `ResE → ℂ × Disk`, `chart0/1 (z,w) ↦ (β, ζ)`. Globally continuous
(regularized coordinates), descends through the weld by `annulusTrivRaw_glued`. -/
def annulusTrivFun : ResE → ℂ × Disk :=
  Quotient.lift annulusTrivRaw (by
    rintro a b (rfl | hg)
    · rfl
    · cases a with
      | inl p => cases b with
        | inr q => exact annulusTrivRaw_glued hg
        | inl _ => exact (hg : False).elim
      | inr q => cases b with
        | inl p => exact (annulusTrivRaw_glued hg).symm
        | inr _ => exact (hg : False).elim)

@[simp] theorem annulusTrivFun_chart0 (p : ResChart) :
    annulusTrivFun (chart0 p) = ((p.1 : ℂ), trivFiber (p.1 : ℂ) p.2) := rfl

@[simp] theorem annulusTrivFun_chart1 (q : ResChart) :
    annulusTrivFun (chart1 q) = (regInv (q.1 : ℂ), trivFiber (q.1 : ℂ) q.2) := rfl

theorem continuous_annulusTrivFun : Continuous annulusTrivFun :=
  continuous_annulusTrivRaw.quotient_lift _

/-- **Clamp a complex number into the closed disk**: `z / max(‖z‖, 1)` — the identity on `‖z‖ ≤ 1`,
radial projection otherwise; continuous everywhere. The junk-regularized base coordinate of the inverse
trivialization (so its two chart branches are globally continuous, as `Continuous.if_le` demands). -/
def clampBall (z : ℂ) : Disk :=
  ⟨z / ((max ‖z‖ 1 : ℝ) : ℂ), by
    have hpos : (0 : ℝ) < max ‖z‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_le_one hpos]
    exact le_max_left _ _⟩

theorem clampBall_eq {z : ℂ} (h : ‖z‖ ≤ 1) : (clampBall z : ℂ) = z := by
  show z / ((max ‖z‖ 1 : ℝ) : ℂ) = z
  rw [max_eq_right h]; norm_num

theorem continuous_clampBall : Continuous clampBall := by
  apply Continuous.subtype_mk
  refine continuous_id.div ?_ (fun z => ?_)
  · exact Complex.continuous_ofReal.comp (continuous_norm.max continuous_const)
  · simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (lt_of_lt_of_le one_pos (le_max_right _ _))

/-- **The chart-0 recovered fiber** `w = conj(regDir z) · ζ` — the inverse of `ζ = regDir z · w` on the
annulus (`(regDir z)⁻¹ = conj(regDir z)` since `‖regDir z‖ = 1` there). Stays in the disk
(`‖conj(regDir z)‖ = ‖regDir z‖ ≤ 1`); continuous everywhere. -/
def recoverFiber0 (z : ℂ) (w : Disk) : Disk :=
  ⟨(starRingEnd ℂ) (regDir z) * (w : ℂ), by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (norm_regDir_le z) (norm_nonneg _) w.2⟩

@[simp] theorem recoverFiber0_coe (z : ℂ) (w : Disk) :
    (recoverFiber0 z w : ℂ) = (starRingEnd ℂ) (regDir z) * (w : ℂ) := rfl

theorem continuous_recoverFiber0 : Continuous (fun p : ℂ × Disk => recoverFiber0 p.1 p.2) := by
  apply Continuous.subtype_mk
  exact ((Complex.continuous_conj.comp continuous_regDir).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

/-- **The inverse trivialization** `ℂ × Disk → ResE`: on `‖β‖ ≤ 1` recover the chart-0 point
`chart0 (β, conj(regDir β)·ζ)`; on `‖β‖ > 1` the chart-1 point `chart1 (β⁻¹, regDir β·ζ)` (both via the
globally-continuous clamped coordinates). The two branches agree on the weld `‖β‖ = 1`. -/
def annulusTrivInv (q : ℂ × Disk) : ResE :=
  if ‖q.1‖ ≤ 1
    then chart0 (clampBall q.1, recoverFiber0 q.1 q.2)
    else chart1 (clampBall (regInv q.1), trivFiber q.1 q.2)

theorem continuous_annulusTrivInv : Continuous annulusTrivInv := by
  apply Continuous.if_le
  · exact continuous_chart0.comp ((continuous_clampBall.comp continuous_fst).prodMk
      continuous_recoverFiber0)
  · exact continuous_chart1.comp
      ((continuous_clampBall.comp (continuous_regInv.comp continuous_fst)).prodMk continuous_trivFiber)
  · exact continuous_norm.comp continuous_fst
  · exact continuous_const
  · intro q hq
    show chart0 (clampBall q.1, recoverFiber0 q.1 q.2)
      = chart1 (clampBall (regInv q.1), trivFiber q.1 q.2)
    have hq0 : q.1 ≠ 0 := norm_ne_zero_iff.mp (by rw [hq]; norm_num)
    have hA1 : ((clampBall q.1 : Disk) : ℂ) = q.1 := clampBall_eq hq.le
    have hrinv : regInv q.1 = q.1⁻¹ := regInv_eq (by rw [hq]; norm_num)
    have hB1 : ((clampBall (regInv q.1) : Disk) : ℂ) = q.1⁻¹ := by
      rw [hrinv]; exact clampBall_eq (by rw [norm_inv, hq]; norm_num)
    have hrdir : regDir q.1 = q.1 := by rw [regDir_eq (by rw [hq]; norm_num), hq]; norm_num
    refine chart0_eq_chart1' (q := (clampBall q.1, recoverFiber0 q.1 q.2))
      (p := (clampBall (regInv q.1), trivFiber q.1 q.2)) ?_ ?_ ?_
    · show ‖((clampBall q.1 : Disk) : ℂ)‖ = 1
      rw [hA1, hq]
    · show ((clampBall (regInv q.1) : Disk) : ℂ) = ((clampBall q.1 : Disk) : ℂ)⁻¹
      rw [hA1, hB1]
    · show (trivFiber q.1 q.2 : ℂ)
        = ((clampBall q.1 : Disk) : ℂ) ^ 2 * ((recoverFiber0 q.1 q.2 : Disk) : ℂ)
      rw [trivFiber_coe, recoverFiber0_coe, hA1, hrdir]
      rw [conj_eq_inv_of_norm_one hq]
      field_simp

/-- **The annulus target** `{(β, ζ) ∣ 1/2 < ‖β‖ < 2}` — the base annulus (fiber `ζ` free in the disk),
the image of the trivialization. -/
def annulusTarget : Set (ℂ × Disk) := {q : ℂ × Disk | 1 / 2 < ‖q.1‖ ∧ ‖q.1‖ < 2}

theorem isOpen_annulusTarget : IsOpen annulusTarget :=
  (isOpen_lt continuous_const (continuous_norm.comp continuous_fst)).inter
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const)

/-- Reciprocal bound: the annulus `(1/2, 2)` is inversion-stable — `n ∈ (1/2, 2) ⟹ n⁻¹ ∈ (1/2, 2)`.
The fact making both chart sides land in the base annulus. -/
theorem inv_mem_annulus {n : ℝ} (h1 : 1 / 2 < n) (h2 : n < 2) : 1 / 2 < n⁻¹ ∧ n⁻¹ < 2 := by
  have hpos : 0 < n := by linarith
  have hn : n * n⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
  have hipos : 0 < n⁻¹ := inv_pos.mpr hpos
  exact ⟨by nlinarith [hn, mul_pos (show (0 : ℝ) < 2 - n by linarith) hipos],
    by nlinarith [hn, mul_pos (show (0 : ℝ) < n - 1 / 2 by linarith) hipos]⟩

/-- **Forward maps the region into the target.** -/
theorem annulusTriv_mapsTo {y : ResE} (hy : y ∈ annulusRegion) :
    annulusTrivFun y ∈ annulusTarget := by
  rcases hy with ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩
  · rw [annulusTrivFun_chart0]
    exact ⟨hp, lt_of_le_of_lt p.1.2 (by norm_num)⟩
  · rw [annulusTrivFun_chart1, regInv_eq hq.le]
    obtain ⟨hlo, hhi⟩ := inv_mem_annulus hq (lt_of_le_of_lt q.1.2 (by norm_num))
    exact ⟨by rw [norm_inv]; exact hlo, by rw [norm_inv]; exact hhi⟩

/-- **Inverse maps the target into the region.** -/
theorem annulusTriv_mapsTo_inv {q : ℂ × Disk} (hq : q ∈ annulusTarget) :
    annulusTrivInv q ∈ annulusRegion := by
  obtain ⟨hq1, hq2⟩ := hq
  have hpos : (0 : ℝ) < ‖(q.1 : ℂ)‖ := lt_trans (by norm_num) hq1
  by_cases h : ‖q.1‖ ≤ 1
  · refine Or.inl ⟨(clampBall q.1, recoverFiber0 q.1 q.2), ?_, ?_⟩
    · show (1 : ℝ) / 2 < ‖((clampBall q.1 : Disk) : ℂ)‖
      rw [clampBall_eq h]; exact hq1
    · simp only [annulusTrivInv, if_pos h]
  · have h' : 1 < ‖q.1‖ := not_le.mp h
    have hle : ‖(regInv q.1 : ℂ)‖ ≤ 1 := by
      rw [regInv_eq (by linarith), norm_inv, inv_le_one₀ hpos]; exact h'.le
    refine Or.inr ⟨(clampBall (regInv q.1), trivFiber q.1 q.2), ?_, ?_⟩
    · show (1 : ℝ) / 2 < ‖((clampBall (regInv q.1) : Disk) : ℂ)‖
      rw [clampBall_eq hle, regInv_eq (by linarith), norm_inv]
      exact (inv_mem_annulus hq1 hq2).1
    · simp only [annulusTrivInv, if_neg h]

/-- **The angular direction is a unit** on the annulus: `regDir z · conj(regDir z) = 1` for `‖z‖ ≥ 1/2`
(`‖regDir z‖ = 1`). Recovers `w` from `ζ = regDir z · w` via `conj(regDir z)·ζ`. -/
theorem regDir_mul_conj {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) :
    regDir z * (starRingEnd ℂ) (regDir z) = 1 := by
  have hpos : (0 : ℝ) < ‖z‖ := by positivity
  have hnd : ‖regDir z‖ = 1 := by
    rw [regDir_eq hz, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
      div_self (ne_of_gt hpos)]
  rw [Complex.mul_conj, ← Complex.sq_norm, hnd]; norm_num

/-- **Opposite angular directions cancel**: `regDir z⁻¹ · regDir z = 1` when both `z` and `z⁻¹` are in
the annulus (`‖z‖, ‖z⁻¹‖ ≥ 1/2`). The chart-1↔chart-0 fiber consistency across the annulus. -/
theorem regDir_inv_mul {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) (hz2 : 1 / 2 ≤ ‖z⁻¹‖) :
    regDir z⁻¹ * regDir z = 1 := by
  have hpos : (0 : ℝ) < ‖z‖ := by positivity
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hpos)
  rw [regDir_eq hz2, regDir_eq hz, norm_inv, Complex.ofReal_inv]
  field_simp
  exact div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))

/-- `regDir z = z` when `‖z‖ = 1` (the angular direction is the point itself on the unit circle). -/
theorem regDir_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : regDir z = z := by
  rw [regDir_eq (by rw [hz]; norm_num), hz]; simp

/-- **Right inverse**: `annulusTrivFun ∘ annulusTrivInv = id` on the target. -/
theorem annulusTriv_right_inv {q : ℂ × Disk} (hq : q ∈ annulusTarget) :
    annulusTrivFun (annulusTrivInv q) = q := by
  obtain ⟨hq1, hq2⟩ := hq
  have hpos : (0 : ℝ) < ‖(q.1 : ℂ)‖ := lt_trans (by norm_num) hq1
  by_cases h : ‖q.1‖ ≤ 1
  · rw [annulusTrivInv, if_pos h, annulusTrivFun_chart0]
    have hcb : ((clampBall q.1 : Disk) : ℂ) = q.1 := clampBall_eq h
    refine Prod.ext hcb (Subtype.ext ?_)
    show regDir ((clampBall q.1 : Disk) : ℂ) * ((recoverFiber0 q.1 q.2 : Disk) : ℂ) = (q.2 : ℂ)
    rw [hcb, recoverFiber0_coe, ← mul_assoc, regDir_mul_conj hq1.le, one_mul]
  · have h' : 1 < ‖q.1‖ := not_le.mp h
    rw [annulusTrivInv, if_neg h, annulusTrivFun_chart1]
    have hrinv : regInv (q.1 : ℂ) = (q.1 : ℂ)⁻¹ := regInv_eq (by linarith)
    have hbn : 1 / 2 ≤ ‖(q.1 : ℂ)⁻¹‖ := by rw [norm_inv]; exact (inv_mem_annulus hq1 hq2).1.le
    have hcb : ((clampBall (regInv q.1) : Disk) : ℂ) = (q.1 : ℂ)⁻¹ := by
      rw [hrinv]; exact clampBall_eq (by rw [norm_inv, inv_le_one₀ hpos]; exact h'.le)
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show regInv ((clampBall (regInv q.1) : Disk) : ℂ) = (q.1 : ℂ)
      rw [hcb, regInv_eq hbn, inv_inv]
    · show regDir ((clampBall (regInv q.1) : Disk) : ℂ) * ((trivFiber q.1 q.2 : Disk) : ℂ) = (q.2 : ℂ)
      rw [hcb, trivFiber_coe, ← mul_assoc, regDir_inv_mul hq1.le hbn, one_mul]

/-- **Left inverse**: `annulusTrivInv ∘ annulusTrivFun = id` on the region. The equator case (chart-1
representative with `‖z'‖ = 1`) crosses branches and is closed by the weld (`chart0_eq_chart1'`). -/
theorem annulusTriv_left_inv {y : ResE} (hy : y ∈ annulusRegion) :
    annulusTrivInv (annulusTrivFun y) = y := by
  rcases hy with ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩
  · rw [annulusTrivFun_chart0]
    have hple : ‖(p.1 : ℂ)‖ ≤ 1 := p.1.2
    rw [annulusTrivInv, if_pos hple]
    refine congrArg chart0 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · exact clampBall_eq hple
    · show ((recoverFiber0 (p.1 : ℂ) (trivFiber (p.1 : ℂ) p.2) : Disk) : ℂ) = (p.2 : ℂ)
      rw [recoverFiber0_coe, trivFiber_coe, ← mul_assoc, mul_comm ((starRingEnd ℂ) _) (regDir _),
        regDir_mul_conj hp.le, one_mul]
  · rw [annulusTrivFun_chart1]
    have hpos : (0 : ℝ) < ‖(q.1 : ℂ)‖ := lt_trans (by norm_num) hq
    have hqle : ‖(q.1 : ℂ)‖ ≤ 1 := q.1.2
    have hrinv : regInv (q.1 : ℂ) = (q.1 : ℂ)⁻¹ := regInv_eq hq.le
    by_cases hb : ‖regInv (q.1 : ℂ)‖ ≤ 1
    · rw [annulusTrivInv, if_pos hb]
      have hq1 : ‖(q.1 : ℂ)‖ = 1 := by
        rw [hrinv, norm_inv, inv_le_one₀ hpos] at hb; exact le_antisymm hqle hb
      have hq0 : (q.1 : ℂ) ≠ 0 := norm_ne_zero_iff.mp (by rw [hq1]; norm_num)
      refine chart0_eq_chart1'
        (q := (clampBall (regInv q.1), recoverFiber0 (regInv q.1) (trivFiber q.1 q.2)))
        (p := q) ?_ ?_ ?_
      · show ‖((clampBall (regInv q.1) : Disk) : ℂ)‖ = 1
        rw [clampBall_eq hb, hrinv, norm_inv, hq1, inv_one]
      · show (q.1 : ℂ) = ((clampBall (regInv q.1) : Disk) : ℂ)⁻¹
        rw [clampBall_eq hb, hrinv, inv_inv]
      · show (q.2 : ℂ) = ((clampBall (regInv q.1) : Disk) : ℂ) ^ 2
          * ((recoverFiber0 (regInv q.1) (trivFiber q.1 q.2) : Disk) : ℂ)
        have hq1inv : ‖(q.1 : ℂ)⁻¹‖ = 1 := by rw [norm_inv, hq1, inv_one]
        rw [clampBall_eq hb, hrinv, recoverFiber0_coe, trivFiber_coe,
          regDir_of_norm_one hq1inv, regDir_of_norm_one hq1,
          show (starRingEnd ℂ) ((q.1 : ℂ)⁻¹) = (q.1 : ℂ) from by
            rw [map_inv₀, conj_eq_inv_of_norm_one hq1, inv_inv]]
        field_simp
    · rw [annulusTrivInv, if_neg hb]
      have hb' : 1 < ‖regInv (q.1 : ℂ)‖ := not_le.mp hb
      have hz2 : 1 / 2 ≤ ‖(q.1 : ℂ)⁻¹‖ := by rw [← hrinv]; linarith
      refine congrArg chart1 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
      · show ((clampBall (regInv (regInv q.1)) : Disk) : ℂ) = (q.1 : ℂ)
        rw [hrinv, regInv_eq hz2, inv_inv, clampBall_eq hqle]
      · show ((trivFiber (regInv q.1) (trivFiber q.1 q.2) : Disk) : ℂ) = (q.2 : ℂ)
        rw [trivFiber_coe, trivFiber_coe, hrinv, ← mul_assoc, regDir_inv_mul hq.le hz2, one_mul]

/-- **The equatorial annulus trivialization** `ResE ⊇ annulusRegion ≃ annulusTarget ⊆ ℂ × Disk` — the
product trivialization of the disk bundle over the base annulus `{1/2 < ‖β‖ < 2}` around the equator.
An `OpenPartialHomeomorph`; the genuinely-new geometric brick that closes the equator ChartedSpace gap. -/
def annulusTriv : OpenPartialHomeomorph ResE (ℂ × Disk) where
  toFun := annulusTrivFun
  invFun := annulusTrivInv
  source := annulusRegion
  target := annulusTarget
  map_source' _ hy := annulusTriv_mapsTo hy
  map_target' _ hq := annulusTriv_mapsTo_inv hq
  left_inv' _ hy := annulusTriv_left_inv hy
  right_inv' _ hq := annulusTriv_right_inv hq
  open_source := isOpen_annulusRegion
  open_target := isOpen_annulusTarget
  continuousOn_toFun := continuous_annulusTrivFun.continuousOn
  continuousOn_invFun := continuous_annulusTrivInv.continuousOn

/-! ## §J. The half-space-model equatorial charts (base annulus into `Model`) -/

/-- **The `ℂ ≃ₜ 𝓔²` homeomorphism** (the base-annulus chart into `𝓔²`) — the full-homeomorphism form of
the norm-faithful `toE2`/`ofE2` bridge (§C). The annulus base coordinate `β ∈ ℂ` is charted plainly. -/
def toE2Homeo : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) where
  toFun := toE2
  invFun := ofE2
  left_inv := ofE2_toE2
  right_inv := toE2_ofE2
  continuous_toFun := continuous_toE2
  continuous_invFun := continuous_ofE2

/-- **The `ℂ × Disk` collar chart into `Model`**: base `β → 𝓔²` (plainly) × fiber `w → 𝓔¹ × HalfSpace¹`
(banked `diskCollarChart 1` through the bridge), reshaped `𝓔² × (𝓔¹ × HS¹) → 𝓔³ × HS¹`. -/
def baseFiberCollarChart (u₀ : NSphere 1) : OpenPartialHomeomorph (ℂ × Disk) Model :=
  (toE2Homeo.toOpenPartialHomeomorph.prod (fiberCollarChart u₀)).trans
    reshapeModel.toOpenPartialHomeomorph

/-- **The `ℂ × Disk` interior chart into `Model`** (fiber `w → 𝓔¹ × HS¹` via banked `diskInteriorChart 1`,
covering the fiber centre). -/
def baseFiberInteriorChart : OpenPartialHomeomorph (ℂ × Disk) Model :=
  (toE2Homeo.toOpenPartialHomeomorph.prod fiberInteriorChart).trans
    reshapeModel.toOpenPartialHomeomorph

/-- **The E-side equatorial collar chart** `OpenPartialHomeomorph ResE Model` — the annulus
trivialization composed with the fiber collar chart. Charts the outer-fiber part (`w ≠ 0`) of the
equator neighborhood; the fiber boundary `‖w‖ = 1` lands on the half-space wall. -/
def annulusCollarChart (u₀ : NSphere 1) : OpenPartialHomeomorph ResE Model :=
  annulusTriv.trans (baseFiberCollarChart u₀)

/-- **The E-side equatorial interior chart** `OpenPartialHomeomorph ResE Model` — the annulus
trivialization composed with the fiber interior chart (covering the fiber centre `w = 0`, the zero
section over the equator). -/
def annulusInteriorChart : OpenPartialHomeomorph ResE Model :=
  annulusTriv.trans baseFiberInteriorChart

/-! ## §K. The equatorial covering and the `ChartedSpace Model ResE` instance -/

/-- `‖regDir z‖ = 1` on the annulus (`‖z‖ ≥ 1/2`). -/
theorem norm_regDir_of {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : ‖regDir z‖ = 1 := by
  have hpos : (0 : ℝ) < ‖z‖ := by positivity
  rw [regDir_eq hz, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    div_self (ne_of_gt hpos)]

/-- The fiber interior chart's source is the open fiber disk `‖w‖ < 1`. -/
theorem mem_fiberInteriorChart_source {w : Disk} (hw : ‖(w : ℂ)‖ < 1) :
    w ∈ fiberInteriorChart.source := by
  simp only [fiberInteriorChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_univ, true_and,
    Set.mem_preimage]
  show ‖((diskHomeoNDisk1 w : NDisk 1) : EuclideanSpace ℝ (Fin 2))‖ < 1
  rw [show ((diskHomeoNDisk1 w : NDisk 1) : EuclideanSpace ℝ (Fin 2)) = toE2 (w : ℂ) from rfl,
    norm_toE2]
  exact hw

/-- The fiber collar chart (at `w`'s own fiber direction) contains `w` when `w ≠ 0`. -/
theorem mem_fiberCollarChart_source {w : Disk} (hw : (w : ℂ) ≠ 0) :
    w ∈ (fiberCollarChart (diskDir 1 (diskHomeoNDisk1 w))).source := by
  simp only [fiberCollarChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_univ, true_and,
    Set.mem_preimage]
  refine ⟨?_, mem_chart_source (EuclideanSpace ℝ (Fin 1)) _⟩
  show ((diskHomeoNDisk1 w : NDisk 1) : EuclideanSpace ℝ (Fin 2)) ≠ 0
  rw [show ((diskHomeoNDisk1 w : NDisk 1) : EuclideanSpace ℝ (Fin 2)) = toE2 (w : ℂ) from rfl]
  intro h0
  exact hw (norm_eq_zero.mp (by rw [← norm_toE2, h0, norm_zero]))

/-- The `ℂ × Disk` interior chart's source is `{fiber ‖w‖ < 1}` (base `β` free). -/
theorem mem_baseFiberInteriorChart_source {β : ℂ} {w : Disk} (hw : ‖(w : ℂ)‖ < 1) :
    (β, w) ∈ baseFiberInteriorChart.source := by
  simp only [baseFiberInteriorChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.prod_source,
    Set.mem_inter_iff, Set.mem_univ, true_and, and_true, Set.mem_preimage, Set.mem_prod]
  exact mem_fiberInteriorChart_source hw

/-- The `ℂ × Disk` collar chart (at `w`'s fiber direction) contains `(β, w)` when `w ≠ 0`. -/
theorem mem_baseFiberCollarChart_source {β : ℂ} {w : Disk} (hw : (w : ℂ) ≠ 0) :
    (β, w) ∈ (baseFiberCollarChart (diskDir 1 (diskHomeoNDisk1 w))).source := by
  simp only [baseFiberCollarChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.prod_source,
    Set.mem_inter_iff, Set.mem_univ, true_and, and_true, Set.mem_preimage, Set.mem_prod]
  exact mem_fiberCollarChart_source hw

/-- The twisted fiber `ζ = trivFiber z w` is nonzero when `w ≠ 0` (on the annulus, `‖z‖ ≥ 1/2`). -/
theorem trivFiber_ne_zero {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) {w : Disk} (hw : (w : ℂ) ≠ 0) :
    (trivFiber z w : ℂ) ≠ 0 := by
  rw [trivFiber_coe]
  exact mul_ne_zero (norm_pos_iff.mp (by rw [norm_regDir_of hz]; norm_num)) hw

/-- **Equator, chart-0, fiber-interior** (`1/2 < ‖z‖`, `‖w‖ < 1`) lies in the annulus interior chart. -/
theorem mem_annulusInteriorChart_source_chart0 {p : ResChart} (hz : 1 / 2 < ‖(p.1 : ℂ)‖)
    (hw : ‖(p.2 : ℂ)‖ < 1) : chart0 p ∈ annulusInteriorChart.source := by
  rw [annulusInteriorChart, OpenPartialHomeomorph.trans_source]
  refine ⟨Or.inl ⟨p, hz, rfl⟩, ?_⟩
  rw [Set.mem_preimage]
  show annulusTrivFun (chart0 p) ∈ baseFiberInteriorChart.source
  rw [annulusTrivFun_chart0]
  apply mem_baseFiberInteriorChart_source
  rw [trivFiber_coe, norm_mul, norm_regDir_of hz.le, one_mul]; exact hw

/-- **Equator, chart-1, fiber-interior** lies in the annulus interior chart. -/
theorem mem_annulusInteriorChart_source_chart1 {q : ResChart} (hz : 1 / 2 < ‖(q.1 : ℂ)‖)
    (hw : ‖(q.2 : ℂ)‖ < 1) : chart1 q ∈ annulusInteriorChart.source := by
  rw [annulusInteriorChart, OpenPartialHomeomorph.trans_source]
  refine ⟨Or.inr ⟨q, hz, rfl⟩, ?_⟩
  rw [Set.mem_preimage]
  show annulusTrivFun (chart1 q) ∈ baseFiberInteriorChart.source
  rw [annulusTrivFun_chart1]
  apply mem_baseFiberInteriorChart_source
  rw [trivFiber_coe, norm_mul, norm_regDir_of hz.le, one_mul]; exact hw

/-- **Equator, chart-0, fiber-off-centre** (`1/2 < ‖z‖`, `w ≠ 0`) lies in the annulus collar chart at
the twisted fiber's own direction. -/
theorem mem_annulusCollarChart_source_chart0 {p : ResChart} (hz : 1 / 2 < ‖(p.1 : ℂ)‖)
    (hw : (p.2 : ℂ) ≠ 0) :
    chart0 p ∈
      (annulusCollarChart (diskDir 1 (diskHomeoNDisk1 (trivFiber (p.1 : ℂ) p.2)))).source := by
  rw [annulusCollarChart, OpenPartialHomeomorph.trans_source]
  refine ⟨Or.inl ⟨p, hz, rfl⟩, ?_⟩
  rw [Set.mem_preimage]
  show annulusTrivFun (chart0 p)
    ∈ (baseFiberCollarChart (diskDir 1 (diskHomeoNDisk1 (trivFiber (p.1 : ℂ) p.2)))).source
  rw [annulusTrivFun_chart0]
  exact mem_baseFiberCollarChart_source (trivFiber_ne_zero hz.le hw)

/-- **Equator, chart-1, fiber-off-centre** lies in the annulus collar chart. -/
theorem mem_annulusCollarChart_source_chart1 {q : ResChart} (hz : 1 / 2 < ‖(q.1 : ℂ)‖)
    (hw : (q.2 : ℂ) ≠ 0) :
    chart1 q ∈
      (annulusCollarChart (diskDir 1 (diskHomeoNDisk1 (trivFiber (q.1 : ℂ) q.2)))).source := by
  rw [annulusCollarChart, OpenPartialHomeomorph.trans_source]
  refine ⟨Or.inr ⟨q, hz, rfl⟩, ?_⟩
  rw [Set.mem_preimage]
  show annulusTrivFun (chart1 q)
    ∈ (baseFiberCollarChart (diskDir 1 (diskHomeoNDisk1 (trivFiber (q.1 : ℂ) q.2)))).source
  rw [annulusTrivFun_chart1]
  exact mem_baseFiberCollarChart_source (trivFiber_ne_zero hz.le hw)

/-- **The E-side atlas** — the base-interior charts (§E–§G) plus the equatorial annulus charts (§J). -/
def atlasE : Set (OpenPartialHomeomorph ResE Model) :=
  {interiorChart, interiorChart1, annulusInteriorChart}
    ∪ Set.range collarChart ∪ Set.range collarChart1 ∪ Set.range annulusCollarChart

/-- **The full covering**: every point of `ResE` lies in the source of some chart in `atlasE`. The
base-interior charts cover `‖z‖ < 1` (banked §H); the equatorial annulus charts cover the equator
`‖z‖ = 1` (§J–§K). The dispatch that makes `ResE` a charted space. -/
theorem exists_chart (x : ResE) : ∃ c ∈ atlasE, x ∈ c.source := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  cases a with
  | inl p =>
    by_cases hz : ‖(p.1 : ℂ)‖ < 1
    · rcases chart0_baseInterior_covered hz with h | ⟨u₀, h⟩
      · exact ⟨interiorChart, Or.inl (Or.inl (Or.inl (Set.mem_insert _ _))), h⟩
      · exact ⟨collarChart u₀, Or.inl (Or.inl (Or.inr (Set.mem_range_self u₀))), h⟩
    · have hz1 : 1 / 2 < ‖(p.1 : ℂ)‖ := lt_of_lt_of_le (by norm_num) (not_lt.mp hz)
      by_cases hw : ‖(p.2 : ℂ)‖ < 1
      · exact ⟨annulusInteriorChart,
          Or.inl (Or.inl (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))),
          mem_annulusInteriorChart_source_chart0 hz1 hw⟩
      · exact ⟨_, Or.inr (Set.mem_range_self _),
          mem_annulusCollarChart_source_chart0 hz1 (fun h0 => hw (by rw [h0, norm_zero]; norm_num))⟩
  | inr q =>
    by_cases hz : ‖(q.1 : ℂ)‖ < 1
    · rcases chart1_baseInterior_covered hz with h | ⟨u₀, h⟩
      · exact ⟨interiorChart1,
          Or.inl (Or.inl (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))), h⟩
      · exact ⟨collarChart1 u₀, Or.inl (Or.inr (Set.mem_range_self u₀)), h⟩
    · have hz1 : 1 / 2 < ‖(q.1 : ℂ)‖ := lt_of_lt_of_le (by norm_num) (not_lt.mp hz)
      by_cases hw : ‖(q.2 : ℂ)‖ < 1
      · exact ⟨annulusInteriorChart,
          Or.inl (Or.inl (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))),
          mem_annulusInteriorChart_source_chart1 hz1 hw⟩
      · exact ⟨_, Or.inr (Set.mem_range_self _),
          mem_annulusCollarChart_source_chart1 hz1 (fun h0 => hw (by rw [h0, norm_zero]; norm_num))⟩

/-- **`ResE` is a charted space over the half-space model** `ModelProd (𝓔 3) (EuclideanHalfSpace 1)` —
the topological manifold-with-boundary skeleton of the K6′a Leg-2 E-side certificate. `chartAt`
dispatches each point to a covering chart (base-interior §E–§G off the equator, equatorial annulus §J
on it). Kernel-pure `{propext, Classical.choice, Quot.sound}`. -/
noncomputable instance instChartedSpaceResE : ChartedSpace Model ResE where
  atlas := atlasE
  chartAt x := Classical.choose (exists_chart x)
  mem_chart_source x := (Classical.choose_spec (exists_chart x)).2
  chart_mem_atlas x := (Classical.choose_spec (exists_chart x)).1

/-! ## §L. Transition smoothness — the `regDir` fiber twist is `C^∞` on the annulus (deliverable 4 seed)

The `IsManifold` (smooth-structure) upgrade of `instChartedSpaceResE` needs the atlas transitions to be
`contDiffGroupoid`-compatible. The genuinely-new transition (beyond the banked `contDiffOn_clutch` and the
polar collar changes) is the annulus↔base fiber twist by `regDir`. This section lands its smoothness on the
annulus `{1/2 < ‖z‖}` (where `regDir z = z/‖z‖`, smooth since `z ≠ 0`). -/

open scoped ContDiff in
/-- **The fiber-twist direction `regDir` is `C^∞` on the annulus** `{1/2 < ‖z‖}` (there `regDir z = z/‖z‖`,
holomorphic-in-`z` since `z ≠ 0`). The smooth-transition seed for the annulus charts' `IsManifold`. -/
theorem contDiffOn_regDir : ContDiffOn ℝ ⊤ regDir {z : ℂ | 1 / 2 < ‖z‖} := by
  have hne : ∀ z ∈ {z : ℂ | 1 / 2 < ‖z‖}, z ≠ 0 := fun z hz =>
    norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by norm_num) hz))
  have hid : ContDiffOn ℝ ⊤ (fun z : ℂ => z) {z : ℂ | 1 / 2 < ‖z‖} := contDiffOn_id
  have hden : ContDiffOn ℝ ⊤ (fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) {z : ℂ | 1 / 2 < ‖z‖} :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hid.norm ℂ hne)
  have hinv : ContDiffOn ℝ ⊤ (fun z : ℂ => (((‖z‖ : ℝ) : ℂ))⁻¹) {z : ℂ | 1 / 2 < ‖z‖} :=
    hden.inv (fun z hz => by
      simp only [ne_eq, Complex.ofReal_eq_zero]; exact norm_ne_zero_iff.mpr (hne z hz))
  refine (hid.mul hinv).congr (fun z hz => ?_)
  rw [regDir_eq hz.le, div_eq_mul_inv]

open scoped ContDiff in
/-- **The chart-1 base coordinate `regInv` is `C^∞` on the annulus** `{1/2 < ‖z‖}` (there `regInv z = z⁻¹`,
holomorphic since `z ≠ 0`). The annulus↔chart-1 base-transition smoothness seed. -/
theorem contDiffOn_regInv : ContDiffOn ℝ ⊤ regInv {z : ℂ | 1 / 2 < ‖z‖} := by
  have hne : ∀ z ∈ {z : ℂ | 1 / 2 < ‖z‖}, z ≠ 0 := fun z hz =>
    norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by norm_num) hz))
  have hid : ContDiffOn ℝ ⊤ (fun z : ℂ => z) {z : ℂ | 1 / 2 < ‖z‖} := contDiffOn_id
  exact (hid.inv hne).congr (fun z hz => regInv_eq hz.le)

/-! ## §M. Atlas transition classes toward `IsManifold` (deliverable 4)

`atlasE` has six chart classes: the base-interior interior/collar charts on each base disk
(`interiorChart`/`collarChart u₀` via `chart0`; `interiorChart1`/`collarChart1 u₀` via `chart1`) and
the equatorial annulus interior/collar charts (`annulusInteriorChart`/`annulusCollarChart u₀`). This
section assembles the `contDiffGroupoid` transitions for `isManifold_of_contDiffOn`.

**§M.1 — the cross-side class is VACUOUS.** The `chart0`- and `chart1`-based charts have disjoint
sources off the base equator (the only gluing locus is `‖z‖ = 1`, excluded from `baseInterior`), so the
coordinate change between a `chart0`-family chart and a `chart1`-family chart has empty domain. -/

/-- The `chart0`-based interior chart's source lands in the `chart0` base-interior image. -/
theorem interiorChart_source_subset :
    interiorChart.source ⊆ Set.range (fun p : ↥baseInterior => chart0 p.1) := by
  rw [interiorChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact Set.image_subset_range _ _

/-- The `chart0`-based collar chart's source lands in the `chart0` base-interior image. -/
theorem collarChart_source_subset (u₀ : NSphere 1) :
    (collarChart u₀).source ⊆ Set.range (fun p : ↥baseInterior => chart0 p.1) := by
  rw [collarChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact Set.image_subset_range _ _

/-- The `chart1`-based interior chart's source lands in the `chart1` base-interior image. -/
theorem interiorChart1_source_subset :
    interiorChart1.source ⊆ Set.range (fun p : ↥baseInterior => chart1 p.1) := by
  rw [interiorChart1, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact Set.image_subset_range _ _

/-- The `chart1`-based collar chart's source lands in the `chart1` base-interior image. -/
theorem collarChart1_source_subset (u₀ : NSphere 1) :
    (collarChart1 u₀).source ⊆ Set.range (fun p : ↥baseInterior => chart1 p.1) := by
  rw [collarChart1, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact Set.image_subset_range _ _

/-- **The two base-interior images are disjoint.** A `chart0` and a `chart1` base-interior point coincide
in `ResE` only when glued, i.e. on the base equator `‖z‖ = 1` — excluded from `baseInterior` (`‖z‖ < 1`). -/
theorem disjoint_chart0_chart1_baseInterior :
    Disjoint (Set.range (fun p : ↥baseInterior => chart0 p.1))
      (Set.range (fun p : ↥baseInterior => chart1 p.1)) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  exact absurd (chart0_eq_chart1_iff.mp hb.symm).1 (ne_of_lt a.2)

/-- **Vacuous transition class.** If two charts have sources in disjoint regions of `ResE`, the
coordinate change between them is `C^k` on its (empty) domain. The `chart0`-family ↔ `chart1`-family
transitions all instantiate this via `disjoint_chart0_chart1_baseInterior`. -/
theorem contDiffOn_transition_vacuous_of_disjoint {k : WithTop ℕ∞}
    {e e' : OpenPartialHomeomorph ResE Model} {A B : Set ResE}
    (he : e.source ⊆ A) (he' : e'.source ⊆ B) (hAB : Disjoint A B) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘ ↑(e.symm ≫ₕ e') ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  have hempty : (e.symm ≫ₕ e').source = ∅ := by
    rw [OpenPartialHomeomorph.trans_source, Set.eq_empty_iff_forall_notMem]
    intro m hm
    rw [Set.mem_inter_iff, OpenPartialHomeomorph.symm_source, Set.mem_preimage] at hm
    obtain ⟨hmt, hms⟩ := hm
    exact Set.disjoint_left.mp hAB (he (e.map_target hmt)) (he' hms)
  rw [hempty, Set.preimage_empty, Set.empty_inter]
  exact contDiffOn_empty

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
- `mem_interiorChart_source`/`mem_collarChart_source`/`chart0_baseInterior_covered` and the `chart1`
  mirrors `mem_interiorChart1_source`/`mem_collarChart1_source`/`chart1_baseInterior_covered` (`§H`) —
  **the off-equator covering lemma (both base disks)**: every point with a `chart0`/`chart1` base-interior
  (`‖z‖ < 1`) representative lies in the interior chart's source (`‖w‖ < 1`) or a collar chart's source
  (`w ≠ 0`, at its own fiber direction `u₀ = diskDir (w/‖w‖)`). Kernel-pure.

Deliverable (3) — **`ChartedSpace Model ResE` COMPLETE** (§I–§K, this pass): the last equator gap closed.
- **The equatorial annulus trivialization** (§I): `annulusTriv : OpenPartialHomeomorph ResE (ℂ × Disk)`,
  the product trivialization of the disk bundle over the base annulus `{1/2 < ‖β‖ < 2}`, charting an
  OPEN neighborhood of the ENTIRE base equator in ONE chart. Built from regularized coordinates
  (`regDir`/`regInv`/`clampBall`/`recoverFiber0`, globally continuous ⟹ forward = `Quotient.lift`,
  inverse pastes via `Continuous.if_le`) with the weld-descent and the equator cross-branch case closed
  by `chart_glue`/`chart0_eq_chart1'`.
- **The half-space-model equatorial charts** (§J): `toE2Homeo : ℂ ≃ₜ 𝓔²`, and
  `annulusCollarChart u₀`/`annulusInteriorChart : OpenPartialHomeomorph ResE Model` (`annulusTriv` composed
  with the fiber collar/interior chart), mirroring the base-interior pair.
- **The full covering + the instance** (§K): `atlasE`, `exists_chart` (every point covered — base-interior
  §H off the equator, equatorial annulus on it), and `instChartedSpaceResE : ChartedSpace Model ResE`
  (`chartAt` = `Classical.choose` of the covering). Kernel-pure `{propext, Classical.choice, Quot.sound}`.

**CORRECTED TOPOLOGY FINDING (this pass).** The prior status note claimed the Euler−2 twist forbids a
product base-annulus × fiber trivialization, forcing arc charts. That is **not correct**: a single product
trivialization over the FULL equator annulus DOES exist (built above, kernel-checked). Over the equator
`S¹` the disk bundle is an ORIENTED `D²`-bundle, hence trivial (`π₀(SO(2)) = 0`); the Euler−2 obstruction
is the global `S²` invariant (the obstruction to extending the trivialization over a DISK), not seen over
the annulus. The trivializing fiber coordinate is `ζ = (β/‖β‖)·w` — the fiber twisted by the UNIT angular
part (a rotation, disk-preserving on BOTH chart sides); the naive `z²` factor blows the disk up off the
equator (`‖z‖ ≠ 1`), which is the artifact behind the earlier "no product" claim. Arc charts are therefore
unnecessary; the annulus chart is cleaner and completes the ChartedSpace directly.

Deliverable (4) seed — **transition smoothness** (§L, this pass): `contDiffOn_regDir` and
`contDiffOn_regInv` — the two genuinely-new equatorial transition ingredients (the annulus's fiber-twist
`regDir z = z/‖z‖` and base coordinate `regInv z = z⁻¹`) are `C^ω` on the annulus `{1/2 < ‖z‖}` (both smooth
since `z ≠ 0`). Because the equator is charted by a SINGLE annulus chart (not an arc family), there are NO
annulus-annulus overlap transitions to verify — only annulus↔base, which reduces to these two.

**RESIDUAL (wall, localized precisely) — the `IsManifold` instance:**

1. **`IsManifold Model ⊤ ResE` + smooth `bdryHomeoRP3`** (deliverable 4) — assemble the atlas transitions
   into `contDiffGroupoid`/`IsManifold` membership: interior-interior off the equator = `contDiffOn_clutch`
   (banked); collar/interior polar changes (smooth off `w = 0`, collar avoids `w = 0`); annulus↔base = the
   §L `contDiffOn_regDir`/`contDiffOn_regInv` seeds threaded through `toE2`/`reshapeModel`; the smooth
   `∂E ≅ ℝP³` upgrade of `bdryHomeoRP3` in these charts. `ChartedSpace` (topological) is DONE; the
   smooth-structure assembly is the remaining brick.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom. -/

end

end SKEFTHawking.KummerResolutionPieceBoundary
