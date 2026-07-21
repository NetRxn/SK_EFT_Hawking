import Mathlib
import SKEFTHawking.KummerResolutionPieceManifold
import SKEFTHawking.KummerRP3Smooth

/-!
# Phase 5q.H — K6′b Leg 2: the seam map `ℝP³ → ∂E` in the E-side collar coordinates

Leg 1 (`KummerRP3Smooth`) put a `C^k` structure on the pinned seam carrier
`KummerResolutionPiece.RP3`. This module supplies the **E-side half** of the smooth
`∂E ≅ ℝP³` upgrade: the seam map `bdryMap` read through the E-piece's *own* collar charts
(`KummerResolutionPieceBoundary.collarChart` / `collarChart1`), which is what makes the weld's
smooth structure a statement about `ResE`'s existing atlas rather than a fresh copy.

**Contents.**

* **§1 — the Hopf coordinate maps at `ℂ²` level.** `hopf0 (a,b) = (a/b, (b/‖b‖)²)` and
  `hopf1 (a,b) = (b/a, (a/‖a‖)²)` — the two hemisphere branches of `bdryMap`, as bare `ℂ × ℂ`
  maps. Each is `C^k` off the vanishing locus of its denominator (`contDiffOn_hopf0/1`), the fiber
  coordinate has unit modulus (`norm_hopf0_snd`), and the two branches are exchanged by the Euler−2
  clutch on the equator (banked `hopf_clutch`).
* **§2 — the collar-chart evaluation law.** `collarChart_chart0_apply`: on the base interior, the
  E-side collar chart of `chart0 p` is
  `(assemble 2 (toE2 p.1) (chart_{S¹}(diskDir (toE2 p.2)))₀, 1 − ‖p.2‖)`.
  Specialized to the seam (`collarChart_bdryMap_chart0`).
* **§3 — the wall law.** `bdryMap_radial_eq_zero`: the seam's half-space coordinate is **exactly
  `0`** — the image of `ℝP³` lies on the model's boundary wall `∂(ℝ³ × [0,∞))`, so the weld really
  is a boundary weld. Stated on the E-side chart, not on a fresh copy.
* **§4 — smoothness of the seam's collar coordinates.** `contDiffOn_seamCollarCoord0`: the full
  E-side collar-coordinate representation of the seam map is `C^k` in the `ℂ²` coordinates of `S³`,
  off the branch's denominator locus. The base block is `toE2 ∘ (a/b)`; the fiber block is the
  banked `contDiffOn_collarTargetForm` normal form of `KummerResolutionPieceManifold`, fed with the
  unit-modulus Hopf fiber. `collarChart_bdryMap_eq` **pins** it to the real atlas chart.
* **§5 — the `chart1` hemisphere branch**, mirroring §2–§4 on the other base disk.
* **§6 — `contMDiffAt_bdryMapRP3`**: the seam identification is `C^k` **as a map of manifolds**,
  from the Leg-1 structure on `ℝP³` into `ResE`'s own `IsManifold` structure, at every point of the
  strict chart-0 hemisphere. The equator (annulus-chart) branch is the remaining case.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/

open Metric Set
open scoped Manifold

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerResolutionPieceBoundary
open SKEFTHawking.KummerResolutionPieceManifold (contDiff_toE2 contDiff_ofE2
  contDiffOn_collarTargetForm)
open SKEFTHawking.DiskChartGeneric (NDisk NSphere diskDir assemble diskCollarChart diskDir_coe)

namespace SKEFTHawking.KummerSeamSmooth

noncomputable section

/-! ## §1. The Hopf coordinate maps at `ℂ²` level -/

/-- **The chart-0 Hopf coordinates** `(a, b) ↦ (a/b, (b/‖b‖)²)` — the `‖a‖ ≤ ‖b‖` branch of
`KummerResolutionPiece.bdryMap`, as a bare map of `ℂ × ℂ`. -/
def hopf0 (p : ℂ × ℂ) : ℂ × ℂ := (p.1 / p.2, (p.2 / (‖p.2‖ : ℂ)) ^ 2)

/-- **The chart-1 Hopf coordinates** `(a, b) ↦ (b/a, (a/‖a‖)²)` — the `‖b‖ ≤ ‖a‖` branch. -/
def hopf1 (p : ℂ × ℂ) : ℂ × ℂ := (p.2 / p.1, (p.1 / (‖p.1‖ : ℂ)) ^ 2)

@[simp] theorem hopf0_fst (p : ℂ × ℂ) : (hopf0 p).1 = p.1 / p.2 := rfl
@[simp] theorem hopf0_snd (p : ℂ × ℂ) : (hopf0 p).2 = (p.2 / (‖p.2‖ : ℂ)) ^ 2 := rfl
@[simp] theorem hopf1_fst (p : ℂ × ℂ) : (hopf1 p).1 = p.2 / p.1 := rfl
@[simp] theorem hopf1_snd (p : ℂ × ℂ) : (hopf1 p).2 = (p.1 / (‖p.1‖ : ℂ)) ^ 2 := rfl

/-- **The Hopf fiber coordinate has unit modulus** (the seam lands on the fiber boundary). -/
theorem norm_hopf0_snd {p : ℂ × ℂ} (hb : p.2 ≠ 0) : ‖(hopf0 p).2‖ = 1 :=
  fiber_norm_eq_one hb

/-- **The chart-1 Hopf fiber coordinate has unit modulus.** -/
theorem norm_hopf1_snd {p : ℂ × ℂ} (ha : p.1 ≠ 0) : ‖(hopf1 p).2‖ = 1 :=
  fiber_norm_eq_one ha

/-- **The unit-circle phase map `c ↦ (c/‖c‖)²` is `C^k` off the origin.** The squaring is what makes
it `±1`-invariant (hence descends to `ℝP³`); the normalization is smooth because `‖·‖` is smooth away
from `0`. -/
theorem contDiffOn_phaseSq {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (fun c : ℂ => (c / (‖c‖ : ℂ)) ^ 2) {c : ℂ | c ≠ 0} := by
  have hinv : ContDiffOn ℝ k (fun c : ℂ => (‖c‖⁻¹ : ℝ)) {c : ℂ | c ≠ 0} := fun c hc =>
    ((contDiffAt_norm ℝ (hc : c ≠ 0)).inv
      (norm_ne_zero_iff.mpr (hc : c ≠ 0))).contDiffWithinAt
  have hdir : ContDiffOn ℝ k (fun c : ℂ => (‖c‖⁻¹ : ℝ) • c) {c : ℂ | c ≠ 0} :=
    hinv.smul contDiffOn_id
  refine (hdir.mul hdir).congr (fun c hc => ?_)
  simp only [Complex.real_smul, Complex.ofReal_inv, sq, div_eq_mul_inv]
  ring

/-- **The chart-0 Hopf map is `C^k`** on `{b ≠ 0}` — the base coordinate is a complex division and
the fiber coordinate is the squared phase (§1). -/
theorem contDiffOn_hopf0 {k : WithTop ℕ∞} : ContDiffOn ℝ k hopf0 {p : ℂ × ℂ | p.2 ≠ 0} := by
  have hinv : ContDiffOn ℝ k (fun p : ℂ × ℂ => (p.2)⁻¹) {p : ℂ × ℂ | p.2 ≠ 0} :=
    contDiffOn_snd.inv (fun p hp => hp)
  have hbase : ContDiffOn ℝ k (fun p : ℂ × ℂ => p.1 / p.2) {p : ℂ × ℂ | p.2 ≠ 0} :=
    (contDiffOn_fst.mul hinv).congr (fun p _ => div_eq_mul_inv _ _)
  exact hbase.prodMk (contDiffOn_phaseSq.comp contDiffOn_snd (fun p hp => hp))

/-- **The chart-1 Hopf map is `C^k`** on `{a ≠ 0}`. -/
theorem contDiffOn_hopf1 {k : WithTop ℕ∞} : ContDiffOn ℝ k hopf1 {p : ℂ × ℂ | p.1 ≠ 0} := by
  have hinv : ContDiffOn ℝ k (fun p : ℂ × ℂ => (p.1)⁻¹) {p : ℂ × ℂ | p.1 ≠ 0} :=
    contDiffOn_fst.inv (fun p hp => hp)
  have hbase : ContDiffOn ℝ k (fun p : ℂ × ℂ => p.2 / p.1) {p : ℂ × ℂ | p.1 ≠ 0} :=
    (contDiffOn_snd.mul hinv).congr (fun p _ => div_eq_mul_inv _ _)
  exact hbase.prodMk (contDiffOn_phaseSq.comp contDiffOn_fst (fun p hp => hp))

/-! ## §2. The E-side collar chart evaluated on a `chart0`/`chart1` point -/

/-- **The collar chart's `𝔼²`-fiber input** — the chart point's fiber coordinate carried into the
banked `NDisk 1` model by the norm-faithful `toE2`. -/
def fiberND (w : Disk) : NDisk 1 :=
  ⟨toE2 (w : ℂ), by rw [mem_closedBall_zero_iff, norm_toE2]; exact w.2⟩

@[simp] theorem fiberND_coe (w : Disk) :
    (fiberND w : EuclideanSpace ℝ (Fin 2)) = toE2 (w : ℂ) := rfl

/-- **The E-side collar chart on a `chart0` point, base block.** -/
theorem collarChart_chart0_fst (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) :
    (collarChart u₀ (chart0 p)).1
      = assemble 2 (toE2 (p.1 : ℂ))
        ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀ (diskDir 1 (fiberND p.2))).ofLp 0) := by
  rw [collarChart, show chart0 p = (fun q : ↥baseInterior => chart0 q.1) ⟨p, hp⟩ from rfl,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

/-- **The E-side collar chart on a `chart0` point, half-space (radial) block.** The wall coordinate
is `1 − ‖w‖`, exactly the `fiberRadial` of §B. -/
theorem collarChart_chart0_radial (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) :
    ((collarChart u₀ (chart0 p)).2.val).ofLp 0 = fiberRadial p := by
  rw [collarChart, show chart0 p = (fun q : ↥baseInterior => chart0 q.1) ⟨p, hp⟩ from rfl,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  show (1 : ℝ) - ‖toE2 (p.2 : ℂ)‖ = fiberRadial p
  rw [norm_toE2, fiberRadial]

/-- **The E-side collar chart on a `chart0` point, half-space block in full** (the `𝔼¹` vector, not
just its single coordinate). -/
theorem collarChart_chart0_snd (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) :
    ((collarChart u₀ (chart0 p)).2).val
      = WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖toE2 (p.2 : ℂ)‖) := by
  rw [collarChart, show chart0 p = (fun q : ↥baseInterior => chart0 q.1) ⟨p, hp⟩ from rfl,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

/-- **The `chart1`-side collar chart, half-space (radial) block** — the same inner chart lifted
along the other base disk. -/
theorem collarChart1_chart1_radial (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) :
    ((collarChart1 u₀ (chart1 p)).2.val).ofLp 0 = fiberRadial p := by
  rw [collarChart1, show chart1 p = (fun q : ↥baseInterior => chart1 q.1) ⟨p, hp⟩ from rfl,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  show (1 : ℝ) - ‖toE2 (p.2 : ℂ)‖ = fiberRadial p
  rw [norm_toE2, fiberRadial]

/-! ## §3. The seam lands on the half-space wall -/

/-- **The chart-0 Hopf point of `S³` as an honest `ResChart`** — base `a/b` in the closed disk,
fiber the unit-modulus squared phase. This is literally the point `bdryMap` produces on the
`‖a‖ ≤ ‖b‖` hemisphere. -/
def hopfChart0 {x : S3} (h : ‖x.1.1‖ ≤ ‖x.1.2‖) : ResChart :=
  (⟨x.1.1 / x.1.2, by
      rw [norm_div]; exact (div_le_one (norm_pos_iff.mpr (S3_snd_ne_zero h))).mpr h⟩,
   ⟨(x.1.2 / (‖x.1.2‖ : ℂ)) ^ 2, le_of_eq (fiber_norm_eq_one (S3_snd_ne_zero h))⟩)

@[simp] theorem hopfChart0_fst_coe {x : S3} (h : ‖x.1.1‖ ≤ ‖x.1.2‖) :
    ((hopfChart0 h).1 : ℂ) = (hopf0 x.1).1 := rfl

@[simp] theorem hopfChart0_snd_coe {x : S3} (h : ‖x.1.1‖ ≤ ‖x.1.2‖) :
    ((hopfChart0 h).2 : ℂ) = (hopf0 x.1).2 := rfl

/-- **The seam map on the chart-0 hemisphere is `chart0` of the Hopf point.** -/
theorem bdryMap_eq_chart0 {x : S3} (h : ‖x.1.1‖ ≤ ‖x.1.2‖) :
    bdryMap x = chart0 (hopfChart0 h) := by
  unfold bdryMap
  rw [dif_pos h]
  rfl

/-- Strictly inside the chart-0 hemisphere the Hopf point is base-interior (`‖a/b‖ < 1`), so the
`chart0`-lifted collar chart of `KummerResolutionPieceBoundary` sees it. -/
theorem hopfChart0_mem_baseInterior {x : S3} (h : ‖x.1.1‖ < ‖x.1.2‖) :
    hopfChart0 h.le ∈ baseInterior := by
  show ‖(x.1.1 / x.1.2 : ℂ)‖ < 1
  rw [norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (S3_snd_ne_zero h.le))).mpr h

/-- **THE WALL LAW.** In the E-side collar chart, the seam point `bdryMap x` has half-space
coordinate **exactly `0`** — the `ℝP³` seam lands on the boundary wall `∂(ℝ³ × [0,∞))` of the model,
not in the interior. This is what makes the K6′b weld an honest *boundary* weld: it is stated on
`ResE`'s own atlas chart (`KummerResolutionPieceBoundary.collarChart`), not on a fresh copy. -/
theorem bdryMap_radial_eq_zero (u₀ : NSphere 1) {x : S3} (h : ‖x.1.1‖ < ‖x.1.2‖) :
    ((collarChart u₀ (bdryMap x)).2.val).ofLp 0 = 0 := by
  rw [bdryMap_eq_chart0 h.le, collarChart_chart0_radial u₀ (hopfChart0_mem_baseInterior h),
    fiberRadial, hopfChart0_snd_coe, norm_hopf0_snd (S3_snd_ne_zero h.le), sub_self]

/-- **The wall law descends to `ℝP³`** — the statement about the seam identification
`bdryMapRP3` itself (`bdryMap` is `±1`-invariant, so the class-level statement is the honest one). -/
theorem bdryMapRP3_radial_eq_zero (u₀ : NSphere 1) {x : S3} (h : ‖x.1.1‖ < ‖x.1.2‖) :
    ((collarChart u₀ (bdryMapRP3 (mkRP3 x))).2.val).ofLp 0 = 0 := by
  rw [bdryMapRP3_mk]
  exact bdryMap_radial_eq_zero u₀ h

/-! ## §4. The seam's E-side collar coordinates are `C^k` -/

/-- The `𝔼²` fiber vector of the seam's collar coordinates: the Hopf fiber phase carried into the
banked disk-chart model by `toE2`. -/
def seamFiberVec (q : ℂ × ℂ) : EuclideanSpace ℝ (Fin 2) := toE2 (hopf0 q).2

theorem norm_seamFiberVec {q : ℂ × ℂ} (hb : q.2 ≠ 0) : ‖seamFiberVec q‖ = 1 := by
  rw [seamFiberVec, norm_toE2, norm_hopf0_snd hb]

theorem seamFiberVec_ne_zero {q : ℂ × ℂ} (hb : q.2 ≠ 0) : seamFiberVec q ≠ 0 := by
  intro h0
  have := norm_seamFiberVec hb
  rw [h0, norm_zero] at this
  exact zero_ne_one this

/-- **The seam's E-side collar-chart coordinates**, as an explicit function of the `ℂ²` coordinates
of `S³`: base block `assemble 2 (toE2 (a/b)) (stereographic angle of the Hopf phase)`, half-space
block `1 − ‖phase‖`. `collarChart_bdryMap_eq` pins this to the actual `ResE` atlas chart. -/
def seamCollarCoord0 (u₀ : NSphere 1) (q : ℂ × ℂ) :
    EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) :=
  (assemble 2 (toE2 (hopf0 q).1)
    (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
      (ne_zero_of_mem_unit_sphere (-u₀))).repr
      (stereoToFun ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
        (‖seamFiberVec q‖⁻¹ • seamFiberVec q))).ofLp 0),
   WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖seamFiberVec q‖))

/-- **The pin**: the `ResE` atlas collar chart, evaluated on a seam point, IS `seamCollarCoord0`.
Without this the smoothness theorem below would be about a fresh definitional copy; with it, it is
about `KummerResolutionPieceBoundary.collarChart`. -/
theorem collarChart_bdryMap_eq (u₀ : NSphere 1) {x : S3} (h : ‖x.1.1‖ < ‖x.1.2‖) :
    ((collarChart u₀ (bdryMap x)).1, ((collarChart u₀ (bdryMap x)).2.val))
      = seamCollarCoord0 u₀ x.1 := by
  have hb : x.1.2 ≠ 0 := S3_snd_ne_zero h.le
  have hne : (fiberND (hopfChart0 h.le).2 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    show toE2 ((hopfChart0 h.le).2 : ℂ) ≠ 0
    rw [hopfChart0_snd_coe]
    exact seamFiberVec_ne_zero hb
  rw [bdryMap_eq_chart0 h.le]
  refine Prod.ext ?_ (collarChart_chart0_snd u₀ (hopfChart0_mem_baseInterior h))
  rw [collarChart_chart0_fst u₀ (hopfChart0_mem_baseInterior h)]
  show assemble 2 (toE2 ((hopfChart0 h.le).1 : ℂ))
      (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
        (ne_zero_of_mem_unit_sphere (-u₀))).repr
        (stereoToFun ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
          ((diskDir 1 (fiberND (hopfChart0 h.le).2) :
            EuclideanSpace ℝ (Fin (1 + 1)))))).ofLp 0) = _
  rw [diskDir_coe hne]
  rfl

/-- The smoothness domain of the chart-0 seam coordinates: the Hopf denominator is nonzero and the
Hopf phase avoids the `u₀`-chart's excluded pole. -/
def seamDom0 (u₀ : NSphere 1) : Set (ℂ × ℂ) :=
  {q : ℂ × ℂ | q.2 ≠ 0 ∧ innerSL ℝ ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
    (‖seamFiberVec q‖⁻¹ • seamFiberVec q) ≠ 1}

/-- **The seam's E-side collar coordinates are `C^k`.** The base block is the complex division
`a/b` carried through the `ℝ`-linear `toE2`; the fiber block is the banked collar-target normal form
`contDiffOn_collarTargetForm` of `KummerResolutionPieceManifold`, fed with the unit-modulus Hopf
phase. Together with `collarChart_bdryMap_eq` this says: **the `ℝP³ → ∂E` seam identification is
smooth when read in the E-piece's own collar chart** — the K6′b `∂E ≅ ℝP³` upgrade at coordinate
level. -/
theorem contDiffOn_seamCollarCoord0 {k : WithTop ℕ∞} (u₀ : NSphere 1) :
    ContDiffOn ℝ k (seamCollarCoord0 u₀) (seamDom0 u₀) := by
  have hsub : seamDom0 u₀ ⊆ {p : ℂ × ℂ | p.2 ≠ 0} := fun q hq => hq.1
  have hhopf : ContDiffOn ℝ k hopf0 (seamDom0 u₀) := contDiffOn_hopf0.mono hsub
  have hG : ContDiffOn ℝ k seamFiberVec (seamDom0 u₀) :=
    contDiff_toE2.comp_contDiffOn (contDiffOn_snd.comp hhopf (fun q _ => Set.mem_univ _))
  have hGne : ∀ q ∈ seamDom0 u₀, seamFiberVec q ≠ 0 := fun q hq => seamFiberVec_ne_zero hq.1
  have hinner : ∀ q ∈ seamDom0 u₀,
      innerSL ℝ ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
        (‖seamFiberVec q‖⁻¹ • seamFiberVec q) ≠ 1 := fun q hq => hq.2
  have hfiber := contDiffOn_collarTargetForm (k := k) u₀ hG hGne hinner
  have hbase : ContDiffOn ℝ k (fun q : ℂ × ℂ => toE2 (hopf0 q).1) (seamDom0 u₀) :=
    contDiff_toE2.comp_contDiffOn (contDiffOn_fst.comp hhopf (fun q _ => Set.mem_univ _))
  have hang : ContDiffOn ℝ k (fun q : ℂ × ℂ =>
      (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
        (ne_zero_of_mem_unit_sphere (-u₀))).repr
        (stereoToFun ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
          (‖seamFiberVec q‖⁻¹ • seamFiberVec q))).ofLp 0)) (seamDom0 u₀) :=
    (((contDiff_apply ℝ ℝ (0 : Fin 1)).comp PiLp.contDiff_ofLp).comp_contDiffOn
      (hfiber.fst))
  refine ContDiffOn.prodMk ?_ hfiber.snd
  exact (SKEFTHawking.KummerResolutionPieceBoundary.contDiff_assemble).comp_contDiffOn
    (hbase.prodMk hang)

/-! ## §5. The chart-1 hemisphere branch

The `‖b‖ < ‖a‖` branch of `bdryMap`, welded to the other base disk. Note the branch condition is
already *strict*, so the chart-1 Hopf point is automatically base-interior — no extra hypothesis is
needed (unlike the chart-0 branch, where the equator `‖a‖ = ‖b‖` sits inside `‖a‖ ≤ ‖b‖`). -/

/-- **The chart-1 Hopf point of `S³` as an honest `ResChart`.** -/
def hopfChart1 {x : S3} (h : ¬ ‖x.1.1‖ ≤ ‖x.1.2‖) : ResChart :=
  (⟨x.1.2 / x.1.1, by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr (S3_fst_ne_zero (not_le.mp h).le))).mpr
        (not_le.mp h).le⟩,
   ⟨(x.1.1 / (‖x.1.1‖ : ℂ)) ^ 2,
      le_of_eq (fiber_norm_eq_one (S3_fst_ne_zero (not_le.mp h).le))⟩)

@[simp] theorem hopfChart1_fst_coe {x : S3} (h : ¬ ‖x.1.1‖ ≤ ‖x.1.2‖) :
    ((hopfChart1 h).1 : ℂ) = (hopf1 x.1).1 := rfl

@[simp] theorem hopfChart1_snd_coe {x : S3} (h : ¬ ‖x.1.1‖ ≤ ‖x.1.2‖) :
    ((hopfChart1 h).2 : ℂ) = (hopf1 x.1).2 := rfl

/-- **The seam map on the chart-1 hemisphere is `chart1` of the Hopf point.** -/
theorem bdryMap_eq_chart1 {x : S3} (h : ¬ ‖x.1.1‖ ≤ ‖x.1.2‖) :
    bdryMap x = chart1 (hopfChart1 h) := by
  unfold bdryMap
  rw [dif_neg h]
  rfl

/-- The chart-1 Hopf point is base-interior: `‖b/a‖ < 1` is forced by the strict branch condition. -/
theorem hopfChart1_mem_baseInterior {x : S3} (h : ¬ ‖x.1.1‖ ≤ ‖x.1.2‖) :
    hopfChart1 h ∈ baseInterior := by
  show ‖(x.1.2 / x.1.1 : ℂ)‖ < 1
  rw [norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (S3_fst_ne_zero (not_le.mp h).le))).mpr (not_le.mp h)

/-- **The E-side `chart1` collar chart, base block.** -/
theorem collarChart1_chart1_fst (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) :
    (collarChart1 u₀ (chart1 p)).1
      = assemble 2 (toE2 (p.1 : ℂ))
        ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀ (diskDir 1 (fiberND p.2))).ofLp 0) := by
  rw [collarChart1, show chart1 p = (fun q : ↥baseInterior => chart1 q.1) ⟨p, hp⟩ from rfl,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

/-- **The E-side `chart1` collar chart, half-space block in full.** -/
theorem collarChart1_chart1_snd (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) :
    ((collarChart1 u₀ (chart1 p)).2).val
      = WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖toE2 (p.2 : ℂ)‖) := by
  rw [collarChart1, show chart1 p = (fun q : ↥baseInterior => chart1 q.1) ⟨p, hp⟩ from rfl,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

/-- **THE WALL LAW, chart-1 branch.** -/
theorem bdryMap_radial_eq_zero_chart1 (u₀ : NSphere 1) {x : S3} (h : ¬ ‖x.1.1‖ ≤ ‖x.1.2‖) :
    ((collarChart1 u₀ (bdryMap x)).2.val).ofLp 0 = 0 := by
  rw [bdryMap_eq_chart1 h, collarChart1_chart1_radial u₀ (hopfChart1_mem_baseInterior h),
    fiberRadial, hopfChart1_snd_coe,
    norm_hopf1_snd (S3_fst_ne_zero (not_le.mp h).le), sub_self]

/-- The `𝔼²` fiber vector of the chart-1 seam coordinates. -/
def seamFiberVec1 (q : ℂ × ℂ) : EuclideanSpace ℝ (Fin 2) := toE2 (hopf1 q).2

theorem norm_seamFiberVec1 {q : ℂ × ℂ} (ha : q.1 ≠ 0) : ‖seamFiberVec1 q‖ = 1 := by
  rw [seamFiberVec1, norm_toE2, norm_hopf1_snd ha]

theorem seamFiberVec1_ne_zero {q : ℂ × ℂ} (ha : q.1 ≠ 0) : seamFiberVec1 q ≠ 0 := by
  intro h0
  have := norm_seamFiberVec1 ha
  rw [h0, norm_zero] at this
  exact zero_ne_one this

/-- **The seam's E-side collar-chart coordinates, chart-1 branch.** -/
def seamCollarCoord1 (u₀ : NSphere 1) (q : ℂ × ℂ) :
    EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) :=
  (assemble 2 (toE2 (hopf1 q).1)
    (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
      (ne_zero_of_mem_unit_sphere (-u₀))).repr
      (stereoToFun ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
        (‖seamFiberVec1 q‖⁻¹ • seamFiberVec1 q))).ofLp 0),
   WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖seamFiberVec1 q‖))

/-- **The chart-1 pin**: the `ResE` atlas chart `collarChart1`, evaluated on a chart-1-branch seam
point, IS `seamCollarCoord1`. -/
theorem collarChart1_bdryMap_eq (u₀ : NSphere 1) {x : S3} (h : ¬ ‖x.1.1‖ ≤ ‖x.1.2‖) :
    ((collarChart1 u₀ (bdryMap x)).1, ((collarChart1 u₀ (bdryMap x)).2.val))
      = seamCollarCoord1 u₀ x.1 := by
  have ha : x.1.1 ≠ 0 := S3_fst_ne_zero (not_le.mp h).le
  have hne : (fiberND (hopfChart1 h).2 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    show toE2 ((hopfChart1 h).2 : ℂ) ≠ 0
    rw [hopfChart1_snd_coe]
    exact seamFiberVec1_ne_zero ha
  rw [bdryMap_eq_chart1 h]
  refine Prod.ext ?_ (collarChart1_chart1_snd u₀ (hopfChart1_mem_baseInterior h))
  rw [collarChart1_chart1_fst u₀ (hopfChart1_mem_baseInterior h)]
  show assemble 2 (toE2 ((hopfChart1 h).1 : ℂ))
      (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
        (ne_zero_of_mem_unit_sphere (-u₀))).repr
        (stereoToFun ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
          ((diskDir 1 (fiberND (hopfChart1 h).2) :
            EuclideanSpace ℝ (Fin (1 + 1)))))).ofLp 0) = _
  rw [diskDir_coe hne]
  rfl

/-- The smoothness domain of the chart-1 seam coordinates. -/
def seamDom1 (u₀ : NSphere 1) : Set (ℂ × ℂ) :=
  {q : ℂ × ℂ | q.1 ≠ 0 ∧ innerSL ℝ ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
    (‖seamFiberVec1 q‖⁻¹ • seamFiberVec1 q) ≠ 1}

/-- **The seam's E-side collar coordinates are `C^k`, chart-1 branch.** -/
theorem contDiffOn_seamCollarCoord1 {k : WithTop ℕ∞} (u₀ : NSphere 1) :
    ContDiffOn ℝ k (seamCollarCoord1 u₀) (seamDom1 u₀) := by
  have hsub : seamDom1 u₀ ⊆ {p : ℂ × ℂ | p.1 ≠ 0} := fun q hq => hq.1
  have hhopf : ContDiffOn ℝ k hopf1 (seamDom1 u₀) := contDiffOn_hopf1.mono hsub
  have hG : ContDiffOn ℝ k seamFiberVec1 (seamDom1 u₀) :=
    contDiff_toE2.comp_contDiffOn (contDiffOn_snd.comp hhopf (fun q _ => Set.mem_univ _))
  have hGne : ∀ q ∈ seamDom1 u₀, seamFiberVec1 q ≠ 0 := fun q hq => seamFiberVec1_ne_zero hq.1
  have hinner : ∀ q ∈ seamDom1 u₀,
      innerSL ℝ ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
        (‖seamFiberVec1 q‖⁻¹ • seamFiberVec1 q) ≠ 1 := fun q hq => hq.2
  have hfiber := contDiffOn_collarTargetForm (k := k) u₀ hG hGne hinner
  have hbase : ContDiffOn ℝ k (fun q : ℂ × ℂ => toE2 (hopf1 q).1) (seamDom1 u₀) :=
    contDiff_toE2.comp_contDiffOn (contDiffOn_fst.comp hhopf (fun q _ => Set.mem_univ _))
  have hang : ContDiffOn ℝ k (fun q : ℂ × ℂ =>
      (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
        (ne_zero_of_mem_unit_sphere (-u₀))).repr
        (stereoToFun ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
          (‖seamFiberVec1 q‖⁻¹ • seamFiberVec1 q))).ofLp 0)) (seamDom1 u₀) :=
    (((contDiff_apply ℝ ℝ (0 : Fin 1)).comp PiLp.contDiff_ofLp).comp_contDiffOn (hfiber.fst))
  refine ContDiffOn.prodMk ?_ hfiber.snd
  exact (SKEFTHawking.KummerResolutionPieceBoundary.contDiff_assemble).comp_contDiffOn
    (hbase.prodMk hang)

/-! ## §6. The seam map `ℝP³ → E` is `ContMDiffAt` off the equator

The pieces line up exactly: `(𝓡 3)` is boundaryless (`e.extend (𝓡 3) = e`, `range (𝓡 3) = univ`)
and `((𝓡 3).prod (𝓡∂ 1)) (v, hs) = (v, hs.val)` — which is precisely the pairing
`collarChart_bdryMap_eq` was stated in. So the chart-level composite of Mathlib's
`contMDiffWithinAt_iff_of_mem_maximalAtlas` is literally
`seamCollarCoord0 u₀ ∘ eucToC2 ∘ (Φ y).symm`, `C^k` by §4. -/

open SKEFTHawking.KummerRP3Smooth
open SKEFTHawking.KummerRP3EuclCharts (S3E RP3E mkE)
open SKEFTHawking.KummerRP3SphereHomeo (sphToS3 sphHomeoS3)

/-- `eucToC2` is `ℝ`-linear in each coordinate, hence `C^k`. -/
theorem contDiff_eucToC2 {k : WithTop ℕ∞} :
    ContDiff ℝ k SKEFTHawking.KummerK7Opener.eucToC2 := by
  have hcoord : ∀ i : Fin 4,
      ContDiff ℝ k (fun v : EuclideanSpace ℝ (Fin 4) => v i) :=
    fun i => (contDiff_apply ℝ ℝ i).comp PiLp.contDiff_ofLp
  exact (Complex.equivRealProdCLM.symm.contDiff.comp ((hcoord 0).prodMk (hcoord 1))).prodMk
    (Complex.equivRealProdCLM.symm.contDiff.comp ((hcoord 2).prodMk (hcoord 3)))

/-- On its domain the Hopf phase is already a unit vector, so the normalization in `seamDom0` is
the identity. -/
theorem seamDom0_eq (u₀ : NSphere 1) :
    seamDom0 u₀ = {q : ℂ × ℂ | q.2 ≠ 0} ∩
      ((fun q : ℂ × ℂ => innerSL ℝ ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
        (seamFiberVec q)) ⁻¹' {(1 : ℝ)}ᶜ) := by
  ext q
  constructor
  · rintro ⟨hq, hin⟩
    refine ⟨hq, ?_⟩
    rwa [norm_seamFiberVec hq, inv_one, one_smul] at hin
  · rintro ⟨hq, hin⟩
    refine ⟨hq, ?_⟩
    rwa [norm_seamFiberVec hq, inv_one, one_smul]

theorem continuousOn_seamFiberVec : ContinuousOn seamFiberVec {q : ℂ × ℂ | q.2 ≠ 0} :=
  continuous_toE2.comp_continuousOn
    (continuous_snd.comp_continuousOn (contDiffOn_hopf0 (k := 0)).continuousOn)

/-- The chart-0 seam domain is open. -/
theorem isOpen_seamDom0 (u₀ : NSphere 1) : IsOpen (seamDom0 u₀) := by
  rw [seamDom0_eq]
  refine ContinuousOn.isOpen_inter_preimage ?_ ?_ isOpen_compl_singleton
  · exact ((innerSL ℝ ((-u₀ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))).continuous).comp_continuousOn
      continuousOn_seamFiberVec
  · exact isOpen_compl_singleton.preimage continuous_snd

/-- The canonical collar-chart base direction at a chart-0 seam point: the Hopf phase itself, viewed
as a point of `S¹`. Every point lies in its own stereographic chart, so this choice always works. -/
def seamDir {x : S3} (h : ‖x.1.1‖ < ‖x.1.2‖) : NSphere 1 :=
  diskDir 1 (diskHomeoNDisk1 (hopfChart0 h.le).2)

/-- The canonical direction is the (unit) Hopf phase vector. -/
theorem seamDir_coe {x : S3} (h : ‖x.1.1‖ < ‖x.1.2‖) :
    ((seamDir h : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1))) = seamFiberVec x.1 := by
  have hb : x.1.2 ≠ 0 := S3_snd_ne_zero h.le
  have hne : ((diskHomeoNDisk1 (hopfChart0 h.le).2 : NDisk 1) :
      EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    show toE2 ((hopfChart0 h.le).2 : ℂ) ≠ 0
    rw [hopfChart0_snd_coe]
    exact seamFiberVec_ne_zero hb
  rw [seamDir, diskDir_coe hne,
    show ((diskHomeoNDisk1 (hopfChart0 h.le).2 : NDisk 1) : EuclideanSpace ℝ (Fin 2))
      = seamFiberVec x.1 from rfl, norm_seamFiberVec hb, inv_one, one_smul]

/-- At its own canonical direction the seam point avoids the excluded pole: the inner product is
`-1`, not `1`. So the seam point lies in `seamDom0 (seamDir h)`. -/
theorem mem_seamDom0_seamDir {x : S3} (h : ‖x.1.1‖ < ‖x.1.2‖) : x.1 ∈ seamDom0 (seamDir h) := by
  have hb : x.1.2 ≠ 0 := S3_snd_ne_zero h.le
  refine ⟨hb, ?_⟩
  rw [norm_seamFiberVec hb, inv_one, one_smul, innerSL_apply_apply,
    show ((-seamDir h : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
      = -((seamDir h : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1))) from rfl,
    seamDir_coe h, inner_neg_left, real_inner_self_eq_norm_sq, norm_seamFiberVec hb]
  norm_num

/-- The chart-0 seam neighbourhood in the `ℝP³` chart's coordinates: the chart target intersected
with the (open) strict chart-0 branch condition. -/
def seamChartNbhd (y : S3E) : Set (EuclideanSpace ℝ (Fin 3)) :=
  (rp3Chart y).target ∩
    {t | ‖(SKEFTHawking.KummerK7Opener.eucToC2 ((Φ y).symm t : E4)).1‖
      < ‖(SKEFTHawking.KummerK7Opener.eucToC2 ((Φ y).symm t : E4)).2‖}

theorem isOpen_seamChartNbhd (y : S3E) : IsOpen (seamChartNbhd y) := by
  refine (rp3Chart y).open_target.inter ?_
  have hcont : Continuous (fun t : EuclideanSpace ℝ (Fin 3) =>
      SKEFTHawking.KummerK7Opener.eucToC2 ((Φ y).symm t : E4)) :=
    (contDiff_eucToC2 (k := 0)).continuous.comp
      (contDiff_chartSymm_coe_S3E (k := 0) y).continuous
  exact isOpen_lt (continuous_norm.comp (continuous_fst.comp hcont))
    (continuous_norm.comp (continuous_snd.comp hcont))

/-- **THE SEAM IS SMOOTH (off the equator).** The `ℝP³ → E` boundary identification `bdryMapRP3` is
`C^k` as a map of manifolds, from the Leg-1 smooth structure on the pinned seam carrier `ℝP³` into
the E-piece's own smooth manifold-with-boundary structure
(`KummerResolutionPieceManifold.isManifold_resE`), at every point of the strict chart-0 hemisphere.
Together with `bdryMap_radial_eq_zero` (the image lies on the model's boundary wall) this is the
`∂E ≅ ℝP³` smooth upgrade the two `§Z` status blocks named as the K6′b-side residual — with the
equator (annulus-chart) branch as the remaining case. -/
theorem contMDiffAt_bdryMapRP3 {k : WithTop ℕ∞} {x : S3} (h : ‖x.1.1‖ < ‖x.1.2‖) :
    ContMDiffAt (𝓡 3) ((𝓡 3).prod (𝓡∂ 1)) k bdryMapRP3 (mkRP3 x) := by
  classical
  set y : S3E := sphHomeoS3.symm x with hydef
  have hyx : sphToS3 y = x := by
    rw [hydef, ← sphHomeoS3_apply, sphHomeoS3.apply_symm_apply]
  have hcoe : SKEFTHawking.KummerK7Opener.eucToC2 (y : E4) = x.1 := congrArg Subtype.val hyx
  set u₀ : NSphere 1 := seamDir h with hu₀
  -- the two charts, and their maximal-atlas membership
  have he : rp3PinChart y ∈ IsManifold.maximalAtlas (𝓡 3) k RP3 :=
    IsManifold.subset_maximalAtlas (I := (𝓡 3)) (n := k) (Set.mem_range_self y)
  have he' : collarChart u₀ ∈ IsManifold.maximalAtlas ((𝓡 3).prod (𝓡∂ 1)) k ResE :=
    IsManifold.subset_maximalAtlas (I := (𝓡 3).prod (𝓡∂ 1)) (n := k)
      (Or.inl (Or.inl (Or.inr (Set.mem_range_self u₀))))
  -- the base point in both charts
  have hmkE : mkRP3 x ∈ (rp3PinChart y).source := by
    refine ⟨mkE y, ?_, ?_⟩
    · rw [rp3Chart_source]; exact ⟨y, mem_hemi_self y, rfl⟩
    · rw [← mkRP3_sphToS3, hyx]
  have hseam : bdryMapRP3 (mkRP3 x) = chart0 (hopfChart0 h.le) := by
    rw [bdryMapRP3_mk, bdryMap_eq_chart0 h.le]
  have hsrc' : bdryMapRP3 (mkRP3 x) ∈ (collarChart u₀).source := by
    rw [hseam, hu₀, seamDir]
    refine mem_collarChart_source (hopfChart0_mem_baseInterior h) ?_
    rw [hopfChart0_snd_coe]
    exact fun h0 => (by
      have := norm_hopf0_snd (S3_snd_ne_zero h.le)
      rw [h0, norm_zero] at this
      exact zero_ne_one this)
  -- the chart base point
  have htarget : rp3PinChart y (mkRP3 x) = Φ y y := by
    rw [← hyx, mkRP3_sphToS3, rp3PinChart,
      OpenPartialHomeomorph.lift_openEmbedding_apply, rp3Chart_apply_mkE y (mem_hemi_self y)]
  rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hmkE hsrc']
  refine ⟨continuous_bdryMapRP3.continuousAt.continuousWithinAt, ?_⟩
  have hsrcE : mkE y ∈ (rp3Chart y).source := by
    rw [rp3Chart_source]; exact ⟨y, mem_hemi_self y, rfl⟩
  have hsymm_pt : (Φ y).symm (Φ y y) = y :=
    (Φ y).left_inv (hemi_subset_source y (mem_hemi_self y))
  have hmemNbhd : Φ y y ∈ seamChartNbhd y := by
    refine ⟨?_, ?_⟩
    · rw [← rp3Chart_apply_mkE y (mem_hemi_self y)]
      exact (rp3Chart y).map_source hsrcE
    · show ‖(SKEFTHawking.KummerK7Opener.eucToC2 (((Φ y).symm (Φ y y)) : E4)).1‖
        < ‖(SKEFTHawking.KummerK7Opener.eucToC2 (((Φ y).symm (Φ y y)) : E4)).2‖
      rw [hsymm_pt, hcoe]
      exact h
  have hgood : ContDiffAt ℝ k
      (fun t : EuclideanSpace ℝ (Fin 3) =>
        seamCollarCoord0 u₀ (SKEFTHawking.KummerK7Opener.eucToC2 ((Φ y).symm t : E4)))
      (Φ y y) := by
    have hin : SKEFTHawking.KummerK7Opener.eucToC2 (((Φ y).symm (Φ y y)) : E4) ∈ seamDom0 u₀ := by
      rw [hsymm_pt, hcoe, hu₀]
      exact mem_seamDom0_seamDir h
    exact ((contDiffOn_seamCollarCoord0 u₀).contDiffAt
      ((isOpen_seamDom0 u₀).mem_nhds hin)).comp (Φ y y)
      (contDiff_eucToC2.comp (contDiff_chartSymm_coe_S3E y)).contDiffAt
  have hEq : ∀ t ∈ seamChartNbhd y,
      (fun s : EuclideanSpace ℝ (Fin 3) =>
        ((collarChart u₀).extend ((𝓡 3).prod (𝓡∂ 1)))
          (bdryMapRP3 (((rp3PinChart y).extend (𝓡 3)).symm s))) t
        = seamCollarCoord0 u₀ (SKEFTHawking.KummerK7Opener.eucToC2 ((Φ y).symm t : E4)) := by
    intro t ht
    have hbr : ‖(sphToS3 ((Φ y).symm t) : ℂ × ℂ).1‖ < ‖(sphToS3 ((Φ y).symm t) : ℂ × ℂ).2‖ := ht.2
    have hsy : ((rp3PinChart y).symm t : RP3) = mkRP3 (sphToS3 ((Φ y).symm t)) := by
      show rp3EHomeoRP3 ((rp3Chart y).symm t) = _
      rw [rp3Chart_symm_apply y ht.1, ← mkRP3_sphToS3]
    show ((𝓡 3).prod (𝓡∂ 1)) (collarChart u₀ (bdryMapRP3 ((rp3PinChart y).symm t))) = _
    rw [hsy, bdryMapRP3_mk]
    exact collarChart_bdryMap_eq u₀ hbr
  have hpt2 : (((rp3PinChart y).extend (𝓡 3)) (mkRP3 x) : EuclideanSpace ℝ (Fin 3)) = Φ y y :=
    htarget
  rw [hpt2]
  exact (hgood.contDiffWithinAt).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem
      (mem_nhdsWithin_of_mem_nhds ((isOpen_seamChartNbhd y).mem_nhds hmemNbhd)) hEq)
    (hEq _ hmemNbhd)

end

end SKEFTHawking.KummerSeamSmooth
