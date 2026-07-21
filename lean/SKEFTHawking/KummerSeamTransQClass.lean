/-
# Phase 5q.H — K6′b Leg 24: the Q-INTERIOR ↔ SEAM transition class (2,3)

Leg 23 (`KummerSeamTransQ`) kernel-checked the two structural facts that fix this class; this module
closes it, together with its `symm` mirror (3,2).

**The shape.** Leg 23's `innerCollarChart_qShellPoint` reads a Q-collar point in the Q-side chart as

    ( Φ u₀ (s3ToSphE a) , s − 1/2 ) ,

while the seam chart reads the *same* point as `(Φ x₀ (s3ToSphE a′), 1/2 − s)` with `a′ = ±a` the
antipodal representative that lands in the `x₀`-hemisphere. So — unlike the E side, which needed a
square-root section builder and a three-way branch dispatch — class (2,3) is one generic map

    qSeamG x₀ u₀ ε (w, t) = (Φ x₀ (ε • (Φ u₀).symm w), −t) ,     ε = ±1,

the descended sphere-chart change paired with the affine flip `t ↦ −t`. Its smoothness is the two
reusable coordinate-level primitives already banked for `ℝP³`
(`KummerRP3Smooth.contDiffOn_reprStereo` and `contDiff_chartSymm_coe_S3E`), and — the saving the
E side taught us — the **inverse direction is free**: `qSeamG` is its own inverse with `x₀`, `u₀`
swapped (`qSeamG_qSeamG`), so no second set-level analysis is needed.

**The set-level residual** (§3–§4), the three items Leg 23 named:

* `chosenC_eq` — the collar centre picked by the `Q`-chart dispatch **is** the seam component: the
  Q-collar puts the point within chart radius `5/8` of `c`, the collar puts it within `3/4` of
  `chosenC h`, and `5/8 + 3/4 = 11/8 < 2 ≤ dist` for distinct fixed points;
* the sheet bookkeeping — `(qmk_local x).symm` returns *one* of the two representatives, and
  `qShellPoint (negS3 a) s = chartNeg (qShellPoint a s)` absorbs the other into `a ↦ negS3 a`;
* the interior branch of the `Q`-chart dispatch is vacuous against the seam — Leg 23's
  `disjoint_qmkInteriorChart_qOpenCollarSet`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamTransQ
import SKEFTHawking.KummerSeamTransE

namespace SKEFTHawking.KummerSeamTransQClass

open Set Topology
open scoped Manifold RealInnerProductSpace
open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerInvolution (torusFourInvolution)
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerResolutionPiece (S3 RP3 mkRP3 negS3 mkRP3_neg)
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerShellChart
open SKEFTHawking.KummerBoundaryChart
open SKEFTHawking.HalfSpaceInteriorFlatten
open SKEFTHawking.KummerSeamCollarQ
open SKEFTHawking.KummerSeamDoubleCollar
open SKEFTHawking.KummerSeamOpenNbhd
open SKEFTHawking.KummerSeamComponentOpen
open SKEFTHawking.KummerSeamChart
open SKEFTHawking.KummerRP3ChartCoord
open SKEFTHawking.KummerRP3EuclCharts
open SKEFTHawking.KummerRP3Smooth
open SKEFTHawking.KummerSeamTransQ
open SKEFTHawking.KummerSeamTransE (pinPt chartAt_rp3_eq hemi_or_neg s3ToSphE_negS3)
open SKEFTHawking.KummerWeldQInterior (interiorQ qInteriorPiece isOpenEmbedding_qInteriorPiece)
open SKEFTHawking.KummerQInteriorChart (qIntChart interiorQIncl)

noncomputable section

variable {k : WithTop ℕ∞}

/-! ## §1. The generic half — a descended sphere-chart change with a flipped collar parameter -/

/-- **The raw sphere-chart coordinate** `v ↦ repr (stereoToFun (−x₀) v)` on the ambient `ℝ⁴`. On the
coercion of a sphere point it is the stereographic chart `Φ x₀`; on `c2ToEuc q` it is
`rp3Coord x₀ q`. Both identifications are `rfl`. -/
def sphCoord (x₀ : S3E) (v : E4) : E3 :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
    (ne_zero_of_mem_unit_sphere (-x₀))).repr (stereoToFun ((-x₀ : S3E) : E4) v)

theorem sphCoord_coe (x₀ y : S3E) : sphCoord x₀ (y : E4) = Φ x₀ y := rfl

theorem sphCoord_c2ToEuc (x₀ : S3E) (q : ℂ × ℂ) : sphCoord x₀ (c2ToEuc q) = rp3Coord x₀ q := rfl

theorem contDiffOn_sphCoord (x₀ : S3E) :
    ContDiffOn ℝ k (sphCoord x₀) {v : E4 | innerSL ℝ ((-x₀ : S3E) : E4) v ≠ 1} :=
  contDiffOn_reprStereo x₀

/-- **THE GENERIC HALF** of the Q-interior ↔ seam transition at sign `ε = ±1`. -/
def qSeamG (x₀ u₀ : S3E) (ε : ℝ) (p : FModel) : FModel :=
  (sphCoord x₀ (ε • (((Φ u₀).symm p.1 : S3E) : E4)), -p.2)

/-- **The smoothness domain** — the `ε`-signed lift avoids the stereographic pole of the
`x₀`-chart. This is the *weak* domain: it is all the analysis needs, and — unlike the hemisphere
domain below — it is stable under the backward direction, where the Q-side base point `u₀` is only
known to avoid its own pole, not to see the point in its hemisphere. -/
def qSeamGDomW (x₀ u₀ : S3E) (ε : ℝ) : Set FModel :=
  {p : FModel | innerSL ℝ ((-x₀ : S3E) : E4) (ε • (((Φ u₀).symm p.1 : S3E) : E4)) ≠ 1}

/-- **The identification domain** — the `ε`-signed lift lands in the `x₀`-hemisphere. Stronger than
`qSeamGDomW`; this is what pins the antipodal sheet, so that the *same* `ε` works at every point of
the domain, not just at the one it was chosen at. -/
def qSeamGDom (x₀ u₀ : S3E) (ε : ℝ) : Set FModel :=
  {p : FModel | 0 < ⟪(x₀ : E4), ε • (((Φ u₀).symm p.1 : S3E) : E4)⟫}

theorem continuous_liftFst (u₀ : S3E) :
    Continuous (fun p : FModel => (((Φ u₀).symm p.1 : S3E) : E4)) :=
  (contDiff_chartSymm_coe_S3E (k := (0 : WithTop ℕ∞)) u₀).continuous.comp continuous_fst

theorem isOpen_qSeamGDomW (x₀ u₀ : S3E) (ε : ℝ) : IsOpen (qSeamGDomW x₀ u₀ ε) :=
  IsOpen.preimage (f := fun p : FModel =>
    innerSL ℝ ((-x₀ : S3E) : E4) (ε • (((Φ u₀).symm p.1 : S3E) : E4)))
    ((innerSL ℝ ((-x₀ : S3E) : E4)).continuous.comp ((continuous_liftFst u₀).const_smul ε))
    isOpen_compl_singleton

theorem isOpen_qSeamGDom (x₀ u₀ : S3E) (ε : ℝ) : IsOpen (qSeamGDom x₀ u₀ ε) :=
  isOpen_lt continuous_const
    (Continuous.inner continuous_const ((continuous_liftFst u₀).const_smul ε))

theorem qSeamGDom_subset_W (x₀ u₀ : S3E) (ε : ℝ) :
    qSeamGDom x₀ u₀ ε ⊆ qSeamGDomW x₀ u₀ ε := by
  intro p hp
  have hpos : 0 < ⟪(x₀ : E4), ε • (((Φ u₀).symm p.1 : S3E) : E4)⟫ := hp
  show innerSL ℝ ((-x₀ : S3E) : E4) (ε • (((Φ u₀).symm p.1 : S3E) : E4)) ≠ 1
  rw [innerSL_apply_apply, show ((-x₀ : S3E) : E4) = -(x₀ : E4) from rfl, inner_neg_left]
  intro heq; linarith

/-- **The generic half is `C^k`** — the banked `repr ∘ stereoToFun` and inverse-stereographic
primitives, plus the affine flip on the collar coordinate. -/
theorem contDiffOn_qSeamG (x₀ u₀ : S3E) (ε : ℝ) :
    ContDiffOn ℝ k (qSeamG x₀ u₀ ε) (qSeamGDomW x₀ u₀ ε) := by
  refine ContDiffOn.prodMk ?_ (contDiff_snd.neg.contDiffOn)
  exact (contDiffOn_sphCoord x₀).comp
    (((contDiff_chartSymm_coe_S3E u₀).comp contDiff_fst).const_smul ε).contDiffOn
    (fun p hp => hp)

/-- The `ε`-signed lift, as a sphere point. -/
def signLift (u₀ : S3E) {ε : ℝ} (hε : ε * ε = 1) (p : FModel) : S3E :=
  ⟨ε • (((Φ u₀).symm p.1 : S3E) : E4), by
    have hu : ‖(((Φ u₀).symm p.1 : S3E) : E4)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp ((Φ u₀).symm p.1).2
    have habs : |ε| = 1 := by
      have h1 : |ε| * |ε| = 1 := by rw [abs_mul_abs_self]; exact hε
      nlinarith [abs_nonneg ε]
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, habs, hu, mul_one]⟩

@[simp] theorem signLift_coe (u₀ : S3E) {ε : ℝ} (hε : ε * ε = 1) (p : FModel) :
    ((signLift u₀ hε p : S3E) : E4) = ε • (((Φ u₀).symm p.1 : S3E) : E4) := rfl

/-- **THE ROUND TRIP.** The generic half is its own inverse with the two base points swapped — the
Q-side analogue of `KummerSeamTransE.seamBwdG_seamFwdG`, and the reason the inverse direction of
class (2,3) costs nothing. -/
theorem qSeamG_qSeamG (x₀ u₀ : S3E) {ε : ℝ} (hε : ε * ε = 1) {p : FModel}
    (hp : p ∈ qSeamGDom x₀ u₀ ε) : qSeamG u₀ x₀ ε (qSeamG x₀ u₀ ε p) = p := by
  set z : S3E := signLift u₀ hε p with hzdef
  have hz : z ∈ hemi x₀ := hp
  have hfst : (qSeamG x₀ u₀ ε p).1 = Φ x₀ z := rfl
  have hzs : (Φ x₀).symm ((qSeamG x₀ u₀ ε p).1) = z := by
    rw [hfst]; exact (Φ x₀).left_inv (hemi_subset_source x₀ hz)
  refine Prod.ext ?_ (by show -(-p.2) = p.2; ring)
  show sphCoord u₀ (ε • (((Φ x₀).symm ((qSeamG x₀ u₀ ε p).1) : S3E) : E4)) = p.1
  rw [hzs]
  have hy : ε • ((z : S3E) : E4) = (((Φ u₀).symm p.1 : S3E) : E4) := by
    rw [hzdef, signLift_coe, smul_smul, hε, one_smul]
  rw [hy, sphCoord_coe]
  exact (Φ u₀).right_inv (by rw [SKEFTHawking.DiskChartGeneric.chart_target_univ]; trivial)

/-! ## §2. Set-level: the seam neighbourhood on the Q side -/

/-- A `Q`-piece point of the seam neighbourhood lies in the Q-side open collar — the `inr` half of
the saturated per-component carrier cannot be an `inl`. -/
theorem mem_qOpenCollarSet_of_mem_seamCompNbhd {c : EIndex} {Y : FreeQuotient}
    (h : weldMk (Sum.inl Y) ∈ seamCompNbhd c) : Y ∈ qOpenCollarSet c := by
  have hpre : Sum.inl Y ∈ weldMk ⁻¹' (weldMk '' seamCompCarrier c) := h
  rw [preimage_image_seamCompCarrier] at hpre
  rcases hpre with ⟨q, hq, hqe⟩ | ⟨q, -, hqe⟩
  · exact Sum.inl.inj hqe ▸ hq
  · exact absurd hqe (by simp)

/-- The double collar is the `Q` branch on the whole *closed* negative half — at `v = 0` the two
branches agree (`eBranch_eq_qBranch_of_zero`, the weld identity). -/
theorem dblCollar_of_nonpos (c : EIndex) {p : RP3 × ↥dblParam} (h : (p.2 : ℝ) ≤ 0) :
    dblCollar c p = qBranch c p := by
  by_cases h0 : (0 : ℝ) ≤ (p.2 : ℝ)
  · rw [dblCollar_of_nonneg c h0]
    exact eBranch_eq_qBranch_of_zero c (le_antisymm h0 h)
  · exact dblCollar_of_neg c h0

/-- **The seam parametrisation on its Q half** — at collar parameter `v = 1/2 − s` the seam
parametrisation is the Q-collar point of chart radius `s`. -/
theorem seamParam_eq_weldMk_qCollarS3 (c : EIndex) (a : S3) (s : ↥qParam) (v : ↥openParam)
    (hsv : (v : ℝ) = 1 / 2 - (s : ℝ)) :
    seamParam c (mkRP3 a, v) = weldMk (Sum.inl (qCollarS3 c a s)) := by
  have hlow : (1 : ℝ) / 2 ≤ (s : ℝ) := s.2.1
  have hnp : ((toDbl v : ↥dblParam) : ℝ) ≤ 0 := by
    show (v : ℝ) ≤ 0
    rw [hsv]; linarith
  have hclamp : clampQ (toDbl v) = s := by
    apply Subtype.ext
    rw [clampQ_coe, min_eq_left hnp]
    show (1 : ℝ) / 2 - (v : ℝ) = (s : ℝ)
    rw [hsv]; ring
  show dblCollar c (mkRP3 a, toDbl v) = _
  rw [dblCollar_of_nonpos c hnp]
  show weldMk (Sum.inl (qCollar c (mkRP3 a, clampQ (toDbl v)))) = _
  rw [hclamp]
  rfl

/-- **The seam chart on a Q-collar point.** -/
theorem seamChart_weldMk_qCollarS3 (c : EIndex) (r₀ : RP3) (a : S3) (s : ↥qParam)
    (v : ↥openParam) (hsv : (v : ℝ) = 1 / 2 - (s : ℝ))
    (hhemi : s3ToSphE a ∈ hemi (pinPt r₀)) :
    seamChart c r₀ (weldMk (Sum.inl (qCollarS3 c a s)))
      = (rp3Coord (pinPt r₀) (a : ℂ × ℂ), (v : ℝ)) := by
  rw [← seamParam_eq_weldMk_qCollarS3 c a s v hsv]
  exact SKEFTHawking.KummerSeamTransE.seamChart_seamParam c r₀ v hhemi

/-- The Q-collar ball is `τ`-stable (the involution is `t ↦ −t` in the centred chart at a fixed
point, and the ball is centrally symmetric). -/
theorem qOpenBall_involution (c : EIndex) {x : TorusFour} (hx : x ∈ qOpenBall c) :
    torusFourInvolution x ∈ qOpenBall c := by
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨chartNeg t, ?_, ?_⟩
  · show sqNorm (chartNeg t) < (5 / 8 : ℝ) ^ 2
    rwa [sqNorm_chartNeg]
  · exact (centeredChartParam_involution c.1 (eIndex_fixedSet c) t).symm

/-- Every point of the collar of `c` is within chart radius `3/4` of `c`. -/
theorem dist_lt_of_mem_collarSet {c x : TorusFour} (hx : x ∈ collarSet c) : dist x c < 3 / 4 := by
  obtain ⟨w, hw, rfl⟩ := hx
  have hn : ‖w‖ < 3 / 4 := hw.2
  have hsq : sqNorm (ofE4 w) < (3 / 4 : ℝ) ^ 2 := by
    rw [sqNorm_ofE4]; nlinarith [norm_nonneg w]
  show dist (centeredChartParam c (ofE4 w)) c < 3 / 4
  exact dist_centeredChartParam_lt c (by norm_num) hsq

/-- **THE COLLAR CENTRE IS THE SEAM COMPONENT.** A point of the open Q collar of `c` is within
chart radius `5/8` of `c` and within `3/4` of the centre `chosenC h` its own `Q`-chart dispatch
picked; `5/8 + 3/4 = 11/8 < 2 ≤ dist` for distinct fixed points forces the two to agree. -/
theorem chosenC_eq (c : EIndex) {x : ↥puncturedTorus} (h : (x : TorusFour) ∉ interiorSet)
    {t : TorusFour} (ht : t ∈ collarSet (chosenC h)) (hq : t ∈ qOpenBall c) : chosenC h = c.1 := by
  by_contra hne
  have h1 : dist t c.1 < 5 / 8 := dist_lt_of_mem_qOpenBall hq
  have h2 : dist t (chosenC h) < 3 / 4 := dist_lt_of_mem_collarSet ht
  have hsep : (2 : ℝ) ≤ dist (chosenC h) c.1 :=
    fixedSet_dist_ge (chosenC_mem h) (eIndex_fixedSet c) hne
  have htri : dist (chosenC h) c.1 ≤ dist (chosenC h) t + dist t c.1 := dist_triangle _ _ _
  rw [dist_comm (chosenC h) t] at htri
  linarith

/-- A point in the source of the selected collar chart is in the selected collar. -/
theorem mem_collarSet_of_mem_bdyChartAt_source {x : ↥puncturedTorus}
    (h : (x : TorusFour) ∉ interiorSet) {y : ↥puncturedTorus} (hsrc : y ∈ (bdyChartAt h).source) :
    (y : TorusFour) ∈ collarSet (chosenC h) := by
  rw [bdyChartAt, boundaryChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hsrc
  obtain ⟨w, -, hwy⟩ := hsrc
  exact congrArg Subtype.val hwy ▸ w.2

/-- **THE SHEET BOOKKEEPING.** Whichever of the two `qmk`-representatives of a Q-collar point a
chart dispatch returns, it is the shell point of *some* pinned direction at the collar radius —
`qShellPoint (negS3 a) s = chartNeg (qShellPoint a s)` absorbs the antipodal sheet into `a`. -/
theorem exists_shell_rep {c : EIndex} {Y : FreeQuotient} (hY : Y ∈ qOpenCollarSet c)
    {y : ↥puncturedTorus} (hy : qmk y = Y) :
    ∃ (a : S3) (s : ↥qParam), (s : ℝ) < 5 / 8 ∧ Y = qCollarS3 c a s ∧
      (y : TorusFour) = centeredChartParam c.1 (qShellPoint a (s : ℝ)) := by
  rw [qOpenCollarSet_eq_qCollar_image] at hY
  obtain ⟨⟨r, s⟩, hs, rfl⟩ := hY
  induction r using Quotient.inductionOn with
  | _ a =>
    have hz : qCollarS3 c a s = qmk ⟨centeredChartParam c.1 (qShellPoint a (s : ℝ)),
        qShellPoint_mem_puncturedTorus c a qParam_lower qParam_lt_threeQuarters⟩ := rfl
    have hzy : qmk (⟨centeredChartParam c.1 (qShellPoint a (s : ℝ)),
        qShellPoint_mem_puncturedTorus c a qParam_lower qParam_lt_threeQuarters⟩ :
        ↥puncturedTorus) = qmk y := by rw [← hz]; exact hy.symm
    rcases (qmk_eq_iff _ y).mp hzy with heq | hτ
    · exact ⟨a, s, hs, rfl, (congrArg Subtype.val heq).symm⟩
    · refine ⟨negS3 a, s, hs, ?_, ?_⟩
      · show qCollar c (mkRP3 a, s) = qCollarS3 c (negS3 a) s
        exact (qCollarS3_negS3 c a s).symm
      · have hv : centeredChartParam c.1 (qShellPoint a (s : ℝ))
            = torusFourInvolution (y : TorusFour) := by
          have := congrArg Subtype.val hτ
          rwa [neg_one_smul_val] at this
        have hy' : (y : TorusFour)
            = torusFourInvolution (centeredChartParam c.1 (qShellPoint a (s : ℝ))) := by
          rw [hv, SKEFTHawking.KummerInvolution.torusFourInvolution_involutive]
        rw [hy', centeredChartParam_involution c.1 (eIndex_fixedSet c), qShellPoint_negS3]

/-! ## §3. The collar branch of the `Q`-chart dispatch on a Q-collar point -/

/-- Transport of the inner collar chart along an equality of centres and of points (the subtype
membership proofs are irrelevant, but the *types* depend on the centre, so this cannot be a `rw`). -/
theorem innerCollarChart_congr {c c' : TorusFour} (hcc : c = c')
    (u₀ : SKEFTHawking.DiskChartGeneric.NSphere 3) {t t' : TorusFour} (htt : t = t')
    (ht : t ∈ collarSet c) (ht' : t' ∈ collarSet c') :
    innerCollarChart c u₀ ⟨t, ht⟩ = innerCollarChart c' u₀ ⟨t', ht'⟩ := by
  subst hcc; subst htt; rfl

/-- The same transport for the collar homeomorphism's inverse. -/
theorem collarHomeo_symm_congr {c c' : TorusFour} (hcc : c = c') {t t' : TorusFour} (htt : t = t')
    (ht : t ∈ collarSet c) (ht' : t' ∈ collarSet c') :
    ((collarHomeo c).symm ⟨t, ht⟩ : ↥shellSetE4) = (collarHomeo c').symm ⟨t', ht'⟩ := by
  subst hcc; subst htt; rfl

/-- **THE COLLAR BRANCH ON A Q-COLLAR POINT** — the payoff of Leg 23 §1 in chart form: the collar
chart of `T⁴°` selected by the `Q`-chart dispatch reads a Q-collar point of chart radius `s` as
`(Φ u₀ (s3ToSphE a), s − 1/2)`, and its `S³` direction is in the base chart's source. -/
theorem bdyChartAt_apply_shell {x : ↥puncturedTorus} (h : (x : TorusFour) ∉ interiorSet)
    {c : EIndex} (hC : chosenC h = c.1) (a : S3) {s : ℝ}
    (h1 : (1 : ℝ) / 2 ≤ s) (h2 : s < 5 / 8)
    {y : ↥puncturedTorus} (hy : (y : TorusFour) = centeredChartParam c.1 (qShellPoint a s))
    (hsrc : y ∈ (bdyChartAt h).source) :
    (bdyChartAt h y).1 = Φ (shellDir (shellIncl (chosenShell h))) (s3ToSphE a) ∧
      height (bdyChartAt h y) = s - 1 / 2 ∧
      s3ToSphE a ∈ (Φ (shellDir (shellIncl (chosenShell h)))).source := by
  set u₀ := shellDir (shellIncl (chosenShell h)) with hu₀
  have h2' : s < 3 / 4 := by linarith
  rw [bdyChartAt, boundaryChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hsrc
  obtain ⟨w, hw, hwy⟩ := hsrc
  have hwval : (w : TorusFour) = (y : TorusFour) := congrArg Subtype.val hwy
  have hmem : (y : TorusFour) ∈ collarSet (chosenC h) := hwval ▸ w.2
  have hmem' : centeredChartParam c.1 (qShellPoint a s) ∈ collarSet c.1 := by
    rw [← hy, ← hC]; exact hmem
  have key : bdyChartAt h y = innerCollarChart (chosenC h) u₀ ⟨(y : TorusFour), hmem⟩ :=
    (innerCollarChart (chosenC h) u₀).lift_openEmbedding_apply
      (isOpenEmbedding_collarIncl (chosenC_mem h)) (x := ⟨(y : TorusFour), hmem⟩)
  have keyval : bdyChartAt h y
      = (Φ u₀ (s3ToSphE a), ⟨WithLp.toLp 2 (fun _ : Fin 1 => s - 1 / 2), by
          show (0 : ℝ) ≤ (WithLp.toLp 2 (fun _ : Fin 1 => s - 1 / 2)).ofLp 0
          linarith⟩) := by
    rw [key, innerCollarChart_congr hC u₀ hy hmem hmem',
      innerCollarChart_qShellPoint c.1 u₀ a h1 h2' hmem']
  refine ⟨by rw [keyval], ?_, ?_⟩
  · rw [keyval]
    show (WithLp.toLp 2 (fun _ : Fin 1 => s - 1 / 2)).ofLp 0 = s - 1 / 2
    simp
  -- the direction of the collar preimage is the pinned `S³` point
  have hwsrc : shellIncl ((collarHomeo (chosenC h)).symm w) ∈ (shellCollarChart u₀).source := hw.2.2
  have hshell : (1 : ℝ) / 2 ≤ ‖toE4 (qShellPoint a s)‖ := by
    rw [norm_toE4_qShellPoint (by linarith : (0 : ℝ) ≤ s)]; exact h1
  have hweq : (collarHomeo (chosenC h)).symm w
      = ⟨toE4 (qShellPoint a s), toE4_qShellPoint_mem_shellSetE4 h1 h2'⟩ := by
    have hw' : w = ⟨centeredChartParam c.1 (qShellPoint a s), by rw [hC]; exact hmem'⟩ :=
      Subtype.ext (hwval.trans hy)
    rw [hw', collarHomeo_symm_congr hC (rfl : centeredChartParam c.1 (qShellPoint a s)
      = centeredChartParam c.1 (qShellPoint a s)) (by rw [hC]; exact hmem') hmem']
    exact collarHomeo_symm_qShellPoint c.1 a h1 h2' hmem'
  have hdir : shellDir (shellIncl ((collarHomeo (chosenC h)).symm w)) = s3ToSphE a := by
    rw [hweq]
    exact shellDir_qShellPoint h1 hshell
  have := hwsrc
  show s3ToSphE a ∈ (Φ u₀).source
  rw [← hdir]
  exact this

/-! ## §4. The (2,3) source analysis -/

theorem qFamChart_symm_apply (y₀ : ↥interiorQ) (p : FModel) :
    (SKEFTHawking.KummerK3Chart.qFamChart y₀).symm p
      = qInteriorPiece ((qIntChart y₀).symm p) := rfl

/-- **The data extracted from a point of the (2,3) transition source.** -/
theorem transQ_source_data (y₀ : ↥interiorQ) {c : EIndex} {r₀ : RP3} {p : FModel}
    (hp : p ∈ ((SKEFTHawking.KummerK3Chart.qFamChart y₀).symm.trans (seamChart c r₀)).source) :
    (((qIntChart y₀).symm p : ↥interiorQ) : FreeQuotient) ∈ qOpenCollarSet c ∧
      (qIntChart y₀).symm p ∈ (qIntChart y₀).source ∧
      qIntChart y₀ ((qIntChart y₀).symm p) = p ∧
      qInteriorPiece ((qIntChart y₀).symm p) ∈ (seamChart c r₀).source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hp1' : p ∈ (qIntChart y₀).target := hp1
  rw [qFamChart_symm_apply] at hp2
  exact ⟨mem_qOpenCollarSet_of_mem_seamCompNbhd (seamChart_source_subset c r₀ hp2),
    (qIntChart y₀).map_target hp1', (qIntChart y₀).right_inv hp1', hp2⟩

/-- The collar parameter of a Q-collar point of chart radius `s ∈ [1/2, 5/8)`. -/
theorem half_sub_mem_openParam {s : ℝ} (h1 : (1 : ℝ) / 2 ≤ s) (h2 : s < 5 / 8) :
    1 / 2 - s ∈ openParam := ⟨by show -(1 / 8 : ℝ) < 1 / 2 - s; linarith,
      by show (1 : ℝ) / 2 - s < 1 / 2; linarith⟩

/-- **THE (2,3) SOURCE ANALYSIS.** On the collar branch of the `Q`-chart dispatch, a point of the
transition source is `(Φ u₀ (s3ToSphE a), s − 1/2)` in the `Q` chart and the Q-collar point of
pinned direction `a` at chart radius `s` in `K3`. -/
theorem transQ_core (y₀ : ↥interiorQ) {x : ↥puncturedTorus} (h : (x : TorusFour) ∉ interiorSet)
    (hCH : chartAt HModel (y₀ : FreeQuotient) = qmkBoundaryChart x h)
    (c : EIndex) (r₀ : RP3) {p : FModel}
    (hp : p ∈ ((SKEFTHawking.KummerK3Chart.qFamChart y₀).symm.trans (seamChart c r₀)).source) :
    ∃ (a : S3) (s : ↥qParam), (s : ℝ) < 5 / 8 ∧
      p = (Φ (shellDir (shellIncl (chosenShell h))) (s3ToSphE a), (s : ℝ) - 1 / 2) ∧
      s3ToSphE a ∈ (Φ (shellDir (shellIncl (chosenShell h)))).source ∧
      mkRP3 a ∈ (rp3PinChart (pinPt r₀)).source ∧
      (SKEFTHawking.KummerK3Chart.qFamChart y₀).symm p
        = weldMk (Sum.inl (qCollarS3 c a s)) := by
  obtain ⟨hY, hYsrc, hYp, hqsrc⟩ := transQ_source_data y₀ hp
  set Y : ↥interiorQ := (qIntChart y₀).symm p with hYdef
  have hCHsrc : (Y : FreeQuotient) ∈ (chartAt HModel (y₀ : FreeQuotient)).source := hYsrc.2.1
  rw [hCH, qmkBoundaryChart, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
    OpenPartialHomeomorph.symm_source, Set.mem_preimage] at hCHsrc
  obtain ⟨ht1, ht2⟩ := hCHsrc
  have hqy : qmk ((SKEFTHawking.KummerChartedSpace.qmk_localOpenPartialHomeomorph x).symm
      (Y : FreeQuotient)) = (Y : FreeQuotient) := by
    have hri := (SKEFTHawking.KummerChartedSpace.qmk_localOpenPartialHomeomorph x).right_inv ht1
    rwa [SKEFTHawking.KummerChartedSpace.qmk_localOpenPartialHomeomorph_apply] at hri
  obtain ⟨a, s, hs58, hYeq, hyval⟩ := exists_shell_rep hY hqy
  have hslow : (1 : ℝ) / 2 ≤ (s : ℝ) := s.2.1
  have hqball : (((SKEFTHawking.KummerChartedSpace.qmk_localOpenPartialHomeomorph x).symm
      (Y : FreeQuotient) : ↥puncturedTorus) : TorusFour) ∈ qOpenBall c := by
    rw [hyval]
    refine ⟨qShellPoint a (s : ℝ), ?_, rfl⟩
    show sqNorm (qShellPoint a (s : ℝ)) < (5 / 8 : ℝ) ^ 2
    rw [sqNorm_qShellPoint]; nlinarith
  have hC : chosenC h = c.1 :=
    chosenC_eq c h (mem_collarSet_of_mem_bdyChartAt_source h ht2) hqball
  obtain ⟨hfst, hhgt, hsphsrc⟩ := bdyChartAt_apply_shell h hC a hslow hs58 hyval ht2
  have hpieceeq : (SKEFTHawking.KummerK3Chart.qFamChart y₀).symm p
      = weldMk (Sum.inl (qCollarS3 c a s)) := by
    rw [qFamChart_symm_apply]
    show weldMk (Sum.inl (Y : FreeQuotient)) = _
    rw [hYeq]
  refine ⟨a, s, hs58, ?_, hsphsrc, ?_, hpieceeq⟩
  · rw [← hYp]
    show flatChart (chartAt HModel (y₀ : FreeQuotient)) (Y : FreeQuotient) = _
    rw [hCH]
    show ((SKEFTHawking.KummerBoundaryChart.qmkBoundaryChart x h (Y : FreeQuotient)).1,
      height (SKEFTHawking.KummerBoundaryChart.qmkBoundaryChart x h (Y : FreeQuotient))) = _
    rw [show SKEFTHawking.KummerBoundaryChart.qmkBoundaryChart x h (Y : FreeQuotient)
        = bdyChartAt h ((SKEFTHawking.KummerChartedSpace.qmk_localOpenPartialHomeomorph x).symm
          (Y : FreeQuotient)) from rfl, hfst, hhgt]
  · have hv : 1 / 2 - (s : ℝ) ∈ openParam := half_sub_mem_openParam hslow hs58
    have hseam : qInteriorPiece Y = seamParam c (mkRP3 a, ⟨1 / 2 - (s : ℝ), hv⟩) := by
      show weldMk (Sum.inl (Y : FreeQuotient)) = _
      rw [hYeq]
      exact (seamParam_eq_weldMk_qCollarS3 c a s ⟨1 / 2 - (s : ℝ), hv⟩ rfl).symm
    rw [hseam] at hqsrc
    rw [seamChart, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      Set.mem_preimage] at hqsrc
    have h2 := hqsrc.2
    rw [show (seamParamHomeo c).symm (seamParam c (mkRP3 a, ⟨1 / 2 - (s : ℝ), hv⟩))
        = (mkRP3 a, (⟨1 / 2 - (s : ℝ), hv⟩ : ↥openParam)) from
      (seamParamHomeo c).left_inv (by trivial)] at h2
    have h3 : mkRP3 a ∈ (chartAt E3 r₀).source := h2.1
    rwa [chartAt_rp3_eq] at h3

/-! ## §5. The local identity, and the transition class (2,3) -/

/-- **THE BRANCH SIGN IS FREE.** At every point of the (2,3) transition source, one of the two
antipodal representatives of the seam class lies in the `r₀`-chart's hemisphere. -/
theorem exists_sign (y₀ : ↥interiorQ) {x : ↥puncturedTorus} (h : (x : TorusFour) ∉ interiorSet)
    (hCH : chartAt HModel (y₀ : FreeQuotient) = qmkBoundaryChart x h)
    (c : EIndex) (r₀ : RP3) {p₀ : FModel}
    (hp₀ : p₀ ∈ ((SKEFTHawking.KummerK3Chart.qFamChart y₀).symm.trans (seamChart c r₀)).source) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      p₀ ∈ qSeamGDom (pinPt r₀) (shellDir (shellIncl (chosenShell h))) ε := by
  obtain ⟨a, s, -, hpeq, hsphsrc, hmk, -⟩ := transQ_core y₀ h hCH c r₀ hp₀
  have hlift : ((Φ (shellDir (shellIncl (chosenShell h)))).symm p₀.1 : S3E) = s3ToSphE a := by
    rw [hpeq]; exact (Φ _).left_inv hsphsrc
  rcases hemi_or_neg hmk with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_⟩
    show (0 : ℝ) < ⟪((pinPt r₀ : S3E) : E4),
      (1 : ℝ) • (((Φ (shellDir (shellIncl (chosenShell h)))).symm p₀.1 : S3E) : E4)⟫
    rw [one_smul, hlift]
    exact hpos
  · refine ⟨-1, Or.inr rfl, ?_⟩
    show (0 : ℝ) < ⟪((pinPt r₀ : S3E) : E4),
      (-1 : ℝ) • (((Φ (shellDir (shellIncl (chosenShell h)))).symm p₀.1 : S3E) : E4)⟫
    rw [neg_one_smul, hlift]
    have hn : (0 : ℝ) < ⟪((pinPt r₀ : S3E) : E4), ((s3ToSphE (negS3 a) : S3E) : E4)⟫ := hneg
    rwa [s3ToSphE_negS3, coe_neg_S3E] at hn

/-- **THE LOCAL FORWARD IDENTITY** for class (2,3): on the collar branch, the transition **is** the
generic descended sphere-chart change `qSeamG` at the sign pinned by the hemisphere domain. -/
theorem transQ_apply_eq (y₀ : ↥interiorQ) {x : ↥puncturedTorus} (h : (x : TorusFour) ∉ interiorSet)
    (hCH : chartAt HModel (y₀ : FreeQuotient) = qmkBoundaryChart x h)
    (c : EIndex) (r₀ : RP3) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {p : FModel}
    (hp : p ∈ ((SKEFTHawking.KummerK3Chart.qFamChart y₀).symm.trans (seamChart c r₀)).source)
    (hdom : p ∈ qSeamGDom (pinPt r₀) (shellDir (shellIncl (chosenShell h))) ε) :
    ((SKEFTHawking.KummerK3Chart.qFamChart y₀).symm.trans (seamChart c r₀)) p
      = qSeamG (pinPt r₀) (shellDir (shellIncl (chosenShell h))) ε p := by
  obtain ⟨a, s, hs58, hpeq, hsphsrc, -, hpiece⟩ := transQ_core y₀ h hCH c r₀ hp
  have hlift : ((Φ (shellDir (shellIncl (chosenShell h)))).symm p.1 : S3E) = s3ToSphE a := by
    rw [hpeq]; exact (Φ _).left_inv hsphsrc
  have hp2 : p.2 = (s : ℝ) - 1 / 2 := by rw [hpeq]
  have hv : 1 / 2 - (s : ℝ) ∈ openParam := half_sub_mem_openParam s.2.1 hs58
  have hlhs : ((SKEFTHawking.KummerK3Chart.qFamChart y₀).symm.trans (seamChart c r₀)) p
      = seamChart c r₀ (weldMk (Sum.inl (qCollarS3 c a s))) := by
    show seamChart c r₀ ((SKEFTHawking.KummerK3Chart.qFamChart y₀).symm p) = _
    rw [hpiece]
  have hdom' : (0 : ℝ) < ⟪((pinPt r₀ : S3E) : E4), ε • ((s3ToSphE a : S3E) : E4)⟫ := by
    have hd : (0 : ℝ) < ⟪((pinPt r₀ : S3E) : E4),
        ε • (((Φ (shellDir (shellIncl (chosenShell h)))).symm p.1 : S3E) : E4)⟫ := hdom
    rwa [hlift] at hd
  rcases hε with rfl | rfl
  · have hhemi : s3ToSphE a ∈ hemi (pinPt r₀) := by
      show (0 : ℝ) < ⟪((pinPt r₀ : S3E) : E4), ((s3ToSphE a : S3E) : E4)⟫
      rwa [one_smul] at hdom'
    rw [hlhs, seamChart_weldMk_qCollarS3 c r₀ a s ⟨1 / 2 - (s : ℝ), hv⟩ rfl hhemi]
    show (rp3Coord (pinPt r₀) (a : ℂ × ℂ), (1 : ℝ) / 2 - (s : ℝ))
      = (sphCoord (pinPt r₀) ((1 : ℝ) •
          (((Φ (shellDir (shellIncl (chosenShell h)))).symm p.1 : S3E) : E4)), -p.2)
    rw [one_smul, hlift, hp2]
    exact Prod.ext rfl (by show (1 : ℝ) / 2 - (s : ℝ) = -((s : ℝ) - 1 / 2); ring)
  · have hhemi : s3ToSphE (negS3 a) ∈ hemi (pinPt r₀) := by
      show (0 : ℝ) < ⟪((pinPt r₀ : S3E) : E4), ((s3ToSphE (negS3 a) : S3E) : E4)⟫
      rw [s3ToSphE_negS3, coe_neg_S3E]
      rwa [neg_one_smul] at hdom'
    have hcol : qCollarS3 c a s = qCollarS3 c (negS3 a) s := (qCollarS3_negS3 c a s).symm
    rw [hlhs, hcol, seamChart_weldMk_qCollarS3 c r₀ (negS3 a) s ⟨1 / 2 - (s : ℝ), hv⟩ rfl hhemi]
    show (rp3Coord (pinPt r₀) ((negS3 a : S3) : ℂ × ℂ), (1 : ℝ) / 2 - (s : ℝ))
      = (sphCoord (pinPt r₀) ((-1 : ℝ) •
          (((Φ (shellDir (shellIncl (chosenShell h)))).symm p.1 : S3E) : E4)), -p.2)
    rw [neg_one_smul, hlift, hp2]
    refine Prod.ext ?_ (by show (1 : ℝ) / 2 - (s : ℝ) = -((s : ℝ) - 1 / 2); ring)
    show rp3Coord (pinPt r₀) ((negS3 a : S3) : ℂ × ℂ)
      = sphCoord (pinPt r₀) (-((s3ToSphE a : S3E) : E4))
    rw [← coe_neg_S3E, ← s3ToSphE_negS3]
    rfl

/-! ## §6. Class (2,3), and its `symm` mirror (3,2) -/

/-- **CLASS (2,3) CLOSED on the collar branch of the `Q`-chart dispatch.** Forward: the transition
is locally `qSeamG`. Backward: `qSeamG` is its own inverse with the base points swapped
(`qSeamG_qSeamG`), so no second set-level analysis is needed. -/
theorem mem_contDiffGroupoid_qFam_seam_bdy (y₀ : ↥interiorQ) {x : ↥puncturedTorus}
    (h : (x : TorusFour) ∉ interiorSet)
    (hCH : chartAt HModel (y₀ : FreeQuotient) = qmkBoundaryChart x h)
    (c : EIndex) (r₀ : RP3) :
    ((SKEFTHawking.KummerK3Chart.qFamChart y₀).symm.trans (seamChart c r₀))
      ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  set g := (SKEFTHawking.KummerK3Chart.qFamChart y₀).symm.trans (seamChart c r₀) with hg
  set u₀ := shellDir (shellIncl (chosenShell h)) with hu₀
  rw [SKEFTHawking.ManifoldModelTransport.mem_contDiffGroupoid_self]
  constructor
  · refine contDiffOn_of_locally_contDiffOn fun p₀ hp₀ => ?_
    obtain ⟨ε, hε, hmem⟩ := exists_sign y₀ h hCH c r₀ hp₀
    refine ⟨qSeamGDom (pinPt r₀) u₀ ε, isOpen_qSeamGDom _ _ _, hmem, ?_⟩
    refine ((contDiffOn_qSeamG (k := k) (pinPt r₀) u₀ ε).mono
      (fun p hp => qSeamGDom_subset_W _ _ _ hp.2)).congr ?_
    exact fun p hp => transQ_apply_eq y₀ h hCH c r₀ hε hp.1 hp.2
  · refine contDiffOn_of_locally_contDiffOn fun v₀ hv₀ => ?_
    have hp₀ : g.symm v₀ ∈ g.source := g.map_target hv₀
    obtain ⟨ε, hε, hmem⟩ := exists_sign y₀ h hCH c r₀ hp₀
    have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    have hUopen := isOpen_qSeamGDom (pinPt r₀) u₀ ε
    have hmain : ∀ v ∈ g.target ∩ (g.target ∩ g.symm ⁻¹' qSeamGDom (pinPt r₀) u₀ ε),
        v ∈ qSeamGDomW u₀ (pinPt r₀) ε ∧ g.symm v = qSeamG u₀ (pinPt r₀) ε v := by
      intro v hv
      have hpU : g.symm v ∈ qSeamGDom (pinPt r₀) u₀ ε := hv.2.2
      have hpS : g.symm v ∈ g.source := g.map_target hv.1
      have hvp : g (g.symm v) = v := g.right_inv hv.1
      have hveq : v = qSeamG (pinPt r₀) u₀ ε (g.symm v) :=
        hvp.symm.trans (transQ_apply_eq y₀ h hCH c r₀ hε hpS hpU)
      refine ⟨?_, ?_⟩
      · -- the weak domain of the *backward* half is the `u₀`-pole exclusion, which the source gives
        obtain ⟨a, s, -, hpeq, hsphsrc, -, -⟩ := transQ_core y₀ h hCH c r₀ hpS
        have hlift : ((Φ u₀).symm (g.symm v).1 : S3E) = s3ToSphE a := by
          rw [hpeq]; exact (Φ _).left_inv hsphsrc
        set z : S3E := signLift u₀ hεε (g.symm v) with hzdef
        have hz : z ∈ hemi (pinPt r₀) := hpU
        have hzs : (Φ (pinPt r₀)).symm v.1 = z := by
          have hv1 : v.1 = Φ (pinPt r₀) z := by rw [hveq]; rfl
          rw [hv1]
          exact (Φ (pinPt r₀)).left_inv (hemi_subset_source _ hz)
        show innerSL ℝ ((-u₀ : S3E) : E4)
          (ε • (((Φ (pinPt r₀)).symm v.1 : S3E) : E4)) ≠ 1
        rw [hzs, hzdef, signLift_coe, smul_smul, hεε, one_smul, hlift]
        exact SKEFTHawking.KummerBoundaryChartSmooth.innerSL_ne_one_of_mem_source hsphsrc
      · calc g.symm v
            = qSeamG u₀ (pinPt r₀) ε (qSeamG (pinPt r₀) u₀ ε (g.symm v)) :=
              (qSeamG_qSeamG (pinPt r₀) u₀ hεε hpU).symm
          _ = qSeamG u₀ (pinPt r₀) ε v := by rw [← hveq]
    refine ⟨g.target ∩ g.symm ⁻¹' qSeamGDom (pinPt r₀) u₀ ε,
      g.continuousOn_symm.isOpen_inter_preimage g.open_target hUopen, ⟨hv₀, hmem⟩, ?_⟩
    exact ((contDiffOn_qSeamG (k := k) u₀ (pinPt r₀) ε).mono
      (fun v hv => (hmain v hv).1)).congr (fun v hv => (hmain v hv).2)

/-- **CLASS (2,3) CLOSED** — a Q-interior chart of the weld atlas and a seam chart have a `C^k`
transition on the flat model `𝓔³ × ℝ`. The *interior* branch of the `Q`-chart dispatch is vacuous
against the seam (Leg 23 `disjoint_qmkInteriorChart_qOpenCollarSet`); the collar branch is the
explicit `qSeamG` pair. -/
theorem mem_contDiffGroupoid_qFam_trans_seamFam (y₀ : ↥interiorQ) (c : EIndex) (r₀ : RP3) :
    ((SKEFTHawking.KummerK3Chart.qFamChart y₀).symm.trans (seamChart c r₀))
      ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  by_cases hx : ((Quotient.out (y₀ : FreeQuotient) : ↥puncturedTorus) : TorusFour) ∈ interiorSet
  · -- interior branch: the source is empty
    refine SKEFTHawking.KummerInteriorManifold.mem_groupoid_of_source_empty ?_
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    obtain ⟨hY, hYsrc, -, -⟩ := transQ_source_data y₀ hp
    have hCH : chartAt HModel (y₀ : FreeQuotient)
        = qmkInteriorChart (Quotient.out (y₀ : FreeQuotient)) hx := dif_pos hx
    have hsrc : (((qIntChart y₀).symm p : ↥interiorQ) : FreeQuotient)
        ∈ (qmkInteriorChart (Quotient.out (y₀ : FreeQuotient)) hx).source := by
      rw [← hCH]; exact hYsrc.2.1
    exact Set.disjoint_left.mp
      (disjoint_qmkInteriorChart_qOpenCollarSet c hx) hsrc hY
  · exact mem_contDiffGroupoid_qFam_seam_bdy y₀ hx (dif_neg hx) c r₀

/-- **CLASS (3,2) CLOSED** — the `symm` mirror: a structure groupoid is closed under `symm`, and
`(e.symm ≫ₕ f).symm = f.symm ≫ₕ e`. -/
theorem mem_contDiffGroupoid_seamFam_trans_qFam (y₀ : ↥interiorQ) (c : EIndex) (r₀ : RP3) :
    ((seamChart c r₀).symm.trans (SKEFTHawking.KummerK3Chart.qFamChart y₀))
      ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  have h := (contDiffGroupoid k 𝓘(ℝ, FModel)).symm
    (mem_contDiffGroupoid_qFam_trans_seamFam (k := k) y₀ c r₀)
  rwa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm] at h

/-! ## §7. Non-vacuity — the (2,3) overlap is genuinely nonempty -/

/-- A Q-collar point of chart radius **strictly** above `1/2` misses `∂Q`: a boundary point of any
component would be a `qBdryMap c₀ r`, `seam_separation` forces `c₀ = c`, and `qCollar_injective`
then pins the radius to `1/2`. -/
theorem qCollarS3_mem_interiorQ (c : EIndex) (a : S3) (s : ↥qParam)
    (hlt : (1 : ℝ) / 2 < (s : ℝ)) (hs58 : (s : ℝ) < 5 / 8) : qCollarS3 c a s ∈ interiorQ := by
  intro hb
  obtain ⟨c₀, hc₀, hmem⟩ := Set.mem_iUnion₂.mp hb
  obtain ⟨r, hr⟩ : qCollarS3 c a s ∈
      Set.range (qBdryMap ⟨c₀, (mem_fixedFinset c₀).mpr hc₀⟩) := by
    rw [SKEFTHawking.KummerWeldQInterior.range_qBdryMap_eq_boundaryComponent]; exact hmem
  have hin : qBdryMap (⟨c₀, (mem_fixedFinset c₀).mpr hc₀⟩ : EIndex) r ∈ qOpenCollarSet c := by
    rw [hr]; exact qCollar_mem_qOpenCollarSet c (mkRP3 a, s) hs58
  have hdc : (⟨c₀, (mem_fixedFinset c₀).mpr hc₀⟩ : EIndex) = c := seam_separation hin
  rw [hdc] at hr
  have hhalf : (1 : ℝ) / 2 ∈ qParam := ⟨le_refl _, by norm_num⟩
  have hcol : qCollar c (r, ⟨1 / 2, hhalf⟩) = qCollar c (mkRP3 a, s) := by
    rw [qCollar_half]; exact hr
  have heq := qCollar_injective c hcol
  have hrad : (1 : ℝ) / 2 = (s : ℝ) :=
    congrArg (fun t : ↥qParam => (t : ℝ)) (Prod.ext_iff.mp heq).2
  linarith

/-- **CLASS (2,3) IS NOT VACUOUS.** For *every* seam component `c` and *every* pinned direction `a`
there is a Q-interior chart of `K3` and a seam chart whose transition has a point in its source: the
Q-collar point at chart radius `9/16 ∈ (1/2, 5/8)` is simultaneously a `Q`-interior point of the weld
(it misses `∂Q`) and a point of the seam neighbourhood of its own component. So
`mem_contDiffGroupoid_qFam_trans_seamFam` is a statement about a genuine coordinate change, not an
empty-source triviality. -/
theorem transQ_source_nonempty (c : EIndex) (a : S3) :
    ∃ (y₀ : ↥interiorQ) (r₀ : RP3) (p : FModel),
      p ∈ ((SKEFTHawking.KummerK3Chart.qFamChart y₀).symm.trans (seamChart c r₀)).source := by
  have hsmem : (9 : ℝ) / 16 ∈ qParam := ⟨by norm_num, by norm_num⟩
  set s : ↥qParam := ⟨9 / 16, hsmem⟩ with hsdef
  have hlt : (1 : ℝ) / 2 < (s : ℝ) := by rw [hsdef]; norm_num
  have h58 : (s : ℝ) < 5 / 8 := by rw [hsdef]; norm_num
  set y₀ : ↥interiorQ := ⟨qCollarS3 c a s, qCollarS3_mem_interiorQ c a s hlt h58⟩ with hy₀
  refine ⟨y₀, mkRP3 a, SKEFTHawking.KummerK3Chart.qFamChart y₀ (qInteriorPiece y₀), ?_⟩
  have hxsrc : qInteriorPiece y₀ ∈ (SKEFTHawking.KummerK3Chart.qFamChart y₀).source :=
    SKEFTHawking.KummerK3Chart.mem_qFamChart_source y₀
  have hv : 1 / 2 - (s : ℝ) ∈ openParam := half_sub_mem_openParam s.2.1 h58
  have hseam : qInteriorPiece y₀ = seamParam c (mkRP3 a, ⟨1 / 2 - (s : ℝ), hv⟩) :=
    (seamParam_eq_weldMk_qCollarS3 c a s ⟨1 / 2 - (s : ℝ), hv⟩ rfl).symm
  have hseamsrc : qInteriorPiece y₀ ∈ (seamChart c (mkRP3 a)).source := by
    rw [hseam]
    exact mem_seamChart_source c (mkRP3 a, ⟨1 / 2 - (s : ℝ), hv⟩)
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage]
  refine ⟨(SKEFTHawking.KummerK3Chart.qFamChart y₀).map_source hxsrc, ?_⟩
  rw [(SKEFTHawking.KummerK3Chart.qFamChart y₀).left_inv hxsrc]
  exact hseamsrc

end

end SKEFTHawking.KummerSeamTransQClass
