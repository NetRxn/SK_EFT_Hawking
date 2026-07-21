/-
# Phase 5q.H — K6′b Leg 20: the `ℝP³` CHART IN PINNED `ℂ²` COORDINATES

`KummerRP3Smooth` charts the pinned `ℝP³ = S³_{ℂ²}/±` by transporting the descended stereographic
atlas of `ℝP³_𝔼 = S³_𝔼/±` along the coordinate homeomorphism `rp3EHomeoRP3`. That homeomorphism is
built compact-to-`T2` from `sphHomeoS3`, so its *inverse* has no formula — and the weld's remaining
transition classes need one, because they must evaluate `chartAt 𝓔³ r₀` on an explicitly
constructed `ℝP³` point.

This module supplies it. `c2ToEuc` is the explicit `ℝ`-linear inverse of `KummerK7Opener.eucToC2`;
`sphHomeoS3_symm_eq` identifies `sphHomeoS3.symm` with it on the nose (by injectivity, no
compactness), and `rp3PinChart_mkRP3` evaluates the pinned chart:

    rp3PinChart x₀ (mkRP3 σ) = repr (stereoToFun (−x₀) (c2ToEuc σ))   whenever `c2ToEuc σ ∈ hemi x₀`,

which `contDiffOn_rp3Coord` makes `C^k` in `σ` — reusing `KummerRP3Smooth.contDiffOn_reprStereo`.
The opposite direction `rp3PinChart_symm` reads the chart's inverse as `mkRP3 ∘ eucToC2 ∘ Φ.symm`,
`C^k` by `contDiff_chartSymm_coe_S3E`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerRP3Smooth
import SKEFTHawking.KummerEIntChartCoord

namespace SKEFTHawking.KummerRP3ChartCoord

open Metric Set
open scoped Manifold RealInnerProductSpace
open SKEFTHawking.KummerRP3EuclCharts
open SKEFTHawking.KummerRP3SphereHomeo (sphToS3 sphHomeoS3)
open SKEFTHawking.KummerResolutionPiece (S3 RP3 mkRP3)
open SKEFTHawking.KummerRP3Smooth

noncomputable section

variable {k : WithTop ℕ∞}

/-! ## §1. The explicit `ℝ`-linear inverse of the coordinate map -/

/-- **The explicit coordinate map `ℂ² → 𝔼⁴`** — the `ℝ`-linear inverse of
`KummerK7Opener.eucToC2`. -/
def c2ToEuc (q : ℂ × ℂ) : E4 := WithLp.toLp 2 ![q.1.re, q.1.im, q.2.re, q.2.im]

@[simp] theorem c2ToEuc_ofLp (q : ℂ × ℂ) (i : Fin 4) :
    (c2ToEuc q).ofLp i = (![q.1.re, q.1.im, q.2.re, q.2.im] : Fin 4 → ℝ) i := rfl

theorem eucToC2_c2ToEuc (q : ℂ × ℂ) : SKEFTHawking.KummerK7Opener.eucToC2 (c2ToEuc q) = q := by
  refine Prod.ext ?_ ?_
  · show Complex.equivRealProdCLM.symm ((c2ToEuc q).ofLp 0, (c2ToEuc q).ofLp 1) = q.1
    exact Complex.ext rfl rfl
  · show Complex.equivRealProdCLM.symm ((c2ToEuc q).ofLp 2, (c2ToEuc q).ofLp 3) = q.2
    exact Complex.ext rfl rfl

theorem norm_sq_c2ToEuc (q : ℂ × ℂ) : ‖c2ToEuc q‖ ^ 2 = ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [c2ToEuc, WithLp.ofLp_toLp, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
  ring_nf
  rfl

theorem contDiff_c2ToEuc : ContDiff ℝ k c2ToEuc := by
  have h : ContDiff ℝ k
      (fun q : ℂ × ℂ => (![q.1.re, q.1.im, q.2.re, q.2.im] : Fin 4 → ℝ)) := by
    refine contDiff_pi.mpr fun i => ?_
    fin_cases i
    · exact Complex.reCLM.contDiff.comp contDiff_fst
    · exact Complex.imCLM.contDiff.comp contDiff_fst
    · exact Complex.reCLM.contDiff.comp contDiff_snd
    · exact Complex.imCLM.contDiff.comp contDiff_snd
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.contDiff).comp h

theorem continuous_c2ToEuc : Continuous c2ToEuc :=
  (contDiff_c2ToEuc (k := (0 : WithTop ℕ∞))).continuous

/-- The pinned `S³ ⊂ ℂ²` transported into the Euclidean sphere `S³ ⊂ 𝔼⁴`. -/
def s3ToSphE (σ : S3) : S3E :=
  ⟨c2ToEuc (σ : ℂ × ℂ), by
    rw [mem_sphere_zero_iff_norm]
    have h : ‖c2ToEuc (σ : ℂ × ℂ)‖ ^ 2 = 1 := by rw [norm_sq_c2ToEuc]; exact σ.2
    nlinarith [norm_nonneg (c2ToEuc (σ : ℂ × ℂ))]⟩

@[simp] theorem s3ToSphE_coe (σ : S3) : ((s3ToSphE σ : S3E) : E4) = c2ToEuc (σ : ℂ × ℂ) := rfl

theorem sphToS3_s3ToSphE (σ : S3) : sphToS3 (s3ToSphE σ) = σ :=
  Subtype.ext (eucToC2_c2ToEuc (σ : ℂ × ℂ))

/-- **`sphHomeoS3.symm` is the explicit coordinate map** — no compactness argument needed. -/
theorem sphHomeoS3_symm_eq (σ : S3) : sphHomeoS3.symm σ = s3ToSphE σ :=
  sphHomeoS3.injective (by
    rw [sphHomeoS3.apply_symm_apply]
    exact (sphToS3_s3ToSphE σ).symm)

theorem rp3EHomeoRP3_s3ToSphE (σ : S3) : rp3EHomeoRP3 (mkE (s3ToSphE σ)) = mkRP3 σ := by
  rw [rp3EHomeoRP3_mkE, sphToS3_s3ToSphE]

/-! ## §2. Evaluating the pinned `ℝP³` chart -/

/-- The pinned `ℝP³` chart at `x₀`, evaluated on a class `mkRP3 σ` whose Euclidean lift lies in the
`x₀`-hemisphere. -/
theorem rp3PinChart_mkRP3 (x₀ : S3E) {σ : S3} (hs : s3ToSphE σ ∈ hemi x₀) :
    rp3PinChart x₀ (mkRP3 σ) = Φ x₀ (s3ToSphE σ) := by
  rw [rp3PinChart, ← rp3EHomeoRP3_s3ToSphE σ]
  rw [show (rp3EHomeoRP3 (mkE (s3ToSphE σ)) : RP3)
      = (rp3EHomeoRP3 : RP3E → RP3) (mkE (s3ToSphE σ)) from rfl,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  exact rp3Chart_apply_mkE x₀ hs

/-- **The `ℝP³` chart coordinate as an explicit function of the pinned `ℂ²` representative.** -/
def rp3Coord (x₀ : S3E) (q : ℂ × ℂ) : E3 :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
    (ne_zero_of_mem_unit_sphere (-x₀))).repr (stereoToFun ((-x₀ : S3E) : E4) (c2ToEuc q))

theorem rp3PinChart_mkRP3_eq_rp3Coord (x₀ : S3E) {σ : S3} (hs : s3ToSphE σ ∈ hemi x₀) :
    rp3PinChart x₀ (mkRP3 σ) = rp3Coord x₀ (σ : ℂ × ℂ) := by
  rw [rp3PinChart_mkRP3 x₀ hs, chartAt_S3E_apply]
  rfl

/-- The open locus on which `rp3Coord x₀` is defined (the stereographic pole is excluded). -/
def rp3CoordDom (x₀ : S3E) : Set (ℂ × ℂ) :=
  {q : ℂ × ℂ | innerSL ℝ ((-x₀ : S3E) : E4) (c2ToEuc q) ≠ 1}

theorem isOpen_rp3CoordDom (x₀ : S3E) : IsOpen (rp3CoordDom x₀) := by
  refine IsOpen.preimage
    (f := fun q : ℂ × ℂ => innerSL ℝ ((-x₀ : S3E) : E4) (c2ToEuc q)) ?_ isOpen_compl_singleton
  exact (innerSL ℝ ((-x₀ : S3E) : E4)).continuous.comp continuous_c2ToEuc

/-- A hemisphere point is in the coordinate domain. -/
theorem mem_rp3CoordDom_of_mem_hemi {x₀ : S3E} {σ : S3} (hs : s3ToSphE σ ∈ hemi x₀) :
    (σ : ℂ × ℂ) ∈ rp3CoordDom x₀ := by
  have hpos : 0 < ⟪(x₀ : E4), ((s3ToSphE σ : S3E) : E4)⟫ := hs
  show innerSL ℝ ((-x₀ : S3E) : E4) (c2ToEuc (σ : ℂ × ℂ)) ≠ 1
  rw [innerSL_apply_apply, show ((-x₀ : S3E) : E4) = -(x₀ : E4) from rfl, inner_neg_left]
  rw [s3ToSphE_coe] at hpos
  intro heq; linarith

/-- **The `ℝP³` chart coordinate is `C^k` in the pinned representative.** -/
theorem contDiffOn_rp3Coord (x₀ : S3E) :
    ContDiffOn ℝ k (rp3Coord x₀) (rp3CoordDom x₀) :=
  (contDiffOn_reprStereo x₀).comp contDiff_c2ToEuc.contDiffOn (fun _ hq => hq)

/-! ## §3. The inverse direction -/

/-- **The pinned `ℝP³` chart's inverse**, read on its target: lift the stereographic inverse and
push it through the coordinate map. -/
theorem rp3PinChart_symm (x₀ : S3E) {t : E3} (ht : t ∈ (rp3PinChart x₀).target) :
    (rp3PinChart x₀).symm t = mkRP3 (sphToS3 ((Φ x₀).symm t)) := by
  have ht' : t ∈ (rp3Chart x₀).target := by
    rw [rp3PinChart, OpenPartialHomeomorph.lift_openEmbedding_target] at ht
    exact ht
  rw [rp3PinChart, OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply,
    rp3Chart_symm_apply x₀ ht', rp3EHomeoRP3_mkE]

@[simp] theorem sphToS3_coe (v : S3E) :
    ((sphToS3 v : S3) : ℂ × ℂ) = SKEFTHawking.KummerK7Opener.eucToC2 (v : E4) := rfl

end

end SKEFTHawking.KummerRP3ChartCoord
