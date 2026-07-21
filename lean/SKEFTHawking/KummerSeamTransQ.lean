/-
# Phase 5q.H — K6′b Leg 23: the Q-SIDE SEAM COORDINATES

Leg 22 closed the E-interior ↔ seam transition class (1,3). The remaining open class (2,3) — the
Q-interior against the seam — has a *different* shape, and this module pins the two structural facts
that fix it, both kernel-checked here rather than read off definitions.

**Fact 1 (§1) — the Q collar chart's direction IS the pinned `S³` point.** The Q-side collar map is
`qCollar c (mkRP3 a, s) = qmk (centeredChartParam c (qShellPoint a s))`, and

    toE4 (qShellPoint a s) = s • c2ToEuc a          (`toE4_qShellPoint`)

because `scaleToChart` is exactly `c2ToEuc` scaled by the excision radius `1/2` and `qShellPoint`
reinstates the factor `2s`. Since `KummerShellChart.shellCollarChart` is **polar** —
`v ↦ (chartAt 𝓔³ u₀ (v/‖v‖), ‖v‖ − 1/2)` — the collar chart's `𝓔³` coordinate of a Q-collar point is
`Φ u₀ (s3ToSphE a)` (`shellDir_qShellPoint`). The seam chart's `𝓔³` coordinate of the same point is
`Φ x₀ (s3ToSphE a)`. So class (2,3) is a **descended sphere-chart transition**, with the radial
coordinate related by `v = 1/2 − s`: no square root, no section, no branch — structurally the
`rp3Chart` compatibility already proved in `KummerRP3Smooth` §4.

**Fact 2 (§2) — the Q chart's interior branch is vacuous against the seam.** The open Q collar sits
inside the round closed ball of chart radius `5/8` (`qOpenBall_subset_chartClosedBall58`), that ball
is `τ`-stable (`chartClosedBall58_involution`, since `τ` is `w ↦ −w` in the round chart), and
`interiorSet` is the complement of the sixteen such balls. Hence **no representative** of a Q-collar
point lies in `interiorSet` (`notMem_interiorSet_of_mem_qOpenCollarSet`) — so only the *collar*
branch of the Q-chart dispatch can ever meet a seam neighbourhood.

Both facts were flagged as unverified reads by the analytic-substrate pass; §1 and §2 are their
kernel-checked forms.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamCollarQ
import SKEFTHawking.KummerRP3ChartCoord
import SKEFTHawking.KummerQInteriorChart
import SKEFTHawking.KummerSeamComponentOpen
import SKEFTHawking.KummerQuotientManifold

namespace SKEFTHawking.KummerSeamTransQ

open Set Topology
open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerInvolution (torusFourInvolution)
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerResolutionPiece (S3 RP3 mkRP3 negS3)
open SKEFTHawking.KummerWeld (EIndex scaleToChart eIndex_fixedSet)
open SKEFTHawking.KummerShellChart
open SKEFTHawking.KummerBoundaryChart
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerSeamCollarQ
open SKEFTHawking.KummerSeamOpenNbhd (qOpenBall qOpenShell qOpenCollarSet)
open SKEFTHawking.KummerRP3ChartCoord
open SKEFTHawking.KummerRP3EuclCharts

noncomputable section

/-! ## §1. The Q-collar direction is the pinned `S³` point -/

/-- **The Q-side shell vector is the pinned representative, radially scaled.** `scaleToChart` is
`c2ToEuc` shrunk by the excision radius `1/2`; `qShellPoint`'s factor `2s` reinstates it. -/
theorem toE4_qShellPoint (a : S3) (s : ℝ) :
    toE4 (qShellPoint a s) = s • c2ToEuc (a : ℂ × ℂ) := by
  refine PiLp.ext fun i => ?_
  fin_cases i <;>
  · show _ = s * _
    simp [toE4, qShellPoint, scale4, scaleToChart, c2ToEuc,
      show excisionRadius = (1 : ℝ) / 2 from rfl]
    ring

theorem norm_toE4_qShellPoint {a : S3} {s : ℝ} (hs : 0 ≤ s) :
    ‖toE4 (qShellPoint a s)‖ = s := by
  rw [norm_toE4, sqNorm_qShellPoint, Real.sqrt_sq hs]

/-- **THE Q-COLLAR DIRECTION.** The polar collar chart reads the shell vector of a Q-collar point at
radius `s` as the pinned `S³` point `a` itself — the fact that makes class (2,3) a descended
sphere-chart transition rather than a section problem. -/
theorem shellDir_qShellPoint {a : S3} {s : ℝ} (hs : (1 : ℝ) / 2 ≤ s)
    (h : (1 : ℝ) / 2 ≤ ‖toE4 (qShellPoint a s)‖) :
    shellDir ⟨toE4 (qShellPoint a s), h⟩ = s3ToSphE a := by
  have hu : ((s3ToSphE a : S3E) : EuclideanSpace ℝ (Fin 4)) = c2ToEuc (a : ℂ × ℂ) := rfl
  have hcast : toE4 (qShellPoint a s)
      = s • ((s3ToSphE a : S3E) : EuclideanSpace ℝ (Fin 4)) := by
    rw [hu]; exact toE4_qShellPoint a s
  have hshell : (1 : ℝ) / 2 ≤ ‖s • ((s3ToSphE a : S3E) : EuclideanSpace ℝ (Fin 4))‖ := by
    rwa [← hcast]
  have hstep : shellDir ⟨s • ((s3ToSphE a : S3E) : EuclideanSpace ℝ (Fin 4)), hshell⟩
      = s3ToSphE a := shellDir_smul_unit (s3ToSphE a) hs hshell
  rw [← hstep]
  exact congrArg shellDir (Subtype.ext hcast)

/-- The Q-collar shell vector at radius `s ∈ [1/2, 3/4)` lies in the Euclidean collar shell. -/
theorem toE4_qShellPoint_mem_shellSetE4 {a : S3} {s : ℝ} (h1 : (1 : ℝ) / 2 ≤ s) (h2 : s < 3 / 4) :
    toE4 (qShellPoint a s) ∈ shellSetE4 := by
  have hn : ‖toE4 (qShellPoint a s)‖ = s := norm_toE4_qShellPoint (by linarith)
  exact ⟨by rw [hn]; exact h1, by rw [hn]; exact h2⟩

theorem collarHomeo_apply (c : TorusFour) (w : ↥shellSetE4) :
    ((collarHomeo c w : ↥(collarSet c)) : TorusFour)
      = centeredChartParam c (ofE4 (w : EuclideanSpace ℝ (Fin 4))) := rfl

/-- **THE COLLAR PREIMAGE OF A Q-COLLAR POINT.** The collar homeomorphism carries the shell vector
`toE4 (qShellPoint a s)` to the Q-collar point, so its inverse recovers that vector — the input the
polar collar chart's direction reader consumes. -/
theorem collarHomeo_symm_qShellPoint (c : TorusFour) (a : S3) {s : ℝ} (h1 : (1 : ℝ) / 2 ≤ s)
    (h2 : s < 3 / 4)
    (hy : centeredChartParam c (qShellPoint a s) ∈ collarSet c) :
    (collarHomeo c).symm ⟨centeredChartParam c (qShellPoint a s), hy⟩
      = ⟨toE4 (qShellPoint a s), toE4_qShellPoint_mem_shellSetE4 h1 h2⟩ := by
  refine (Homeomorph.symm_apply_eq _).mpr (Subtype.ext ?_)
  rw [collarHomeo_apply, ofE4_toE4]

/-- **THE Q-SIDE COLLAR CHART ON A Q-COLLAR POINT** — the payoff of §1. The polar collar chart at
base direction `u₀` reads the point `qCollar c (mkRP3 a, s)`'s representative as

    ( Φ u₀ (s3ToSphE a) , s − 1/2 ) ,

i.e. **the `𝓔³` coordinate is the `S³` chart at `u₀` evaluated on the pinned representative of the
seam class, and the half-space coordinate is the collar radius above `1/2`**. Compare the seam
chart, which reads the same point as `(Φ x₀ (s3ToSphE a), 1/2 − s)`: class (2,3) is the sphere-chart
change `Φ x₀ ∘ (Φ u₀).symm` paired with the affine flip `t ↦ −t`. -/
theorem innerCollarChart_qShellPoint (c : TorusFour)
    (u₀ : SKEFTHawking.DiskChartGeneric.NSphere 3) (a : S3) {s : ℝ}
    (h1 : (1 : ℝ) / 2 ≤ s) (h2 : s < 3 / 4)
    (hy : centeredChartParam c (qShellPoint a s) ∈ collarSet c) :
    innerCollarChart c u₀ ⟨centeredChartParam c (qShellPoint a s), hy⟩
      = (chartAt (EuclideanSpace ℝ (Fin 3)) u₀ (s3ToSphE a),
        ⟨WithLp.toLp 2 (fun _ : Fin 1 => s - 1 / 2), by
          show (0 : ℝ) ≤ (WithLp.toLp 2 (fun _ : Fin 1 => s - 1 / 2)).ofLp 0
          linarith⟩) := by
  have hshell : (1 : ℝ) / 2 ≤ ‖toE4 (qShellPoint a s)‖ := by
    rw [norm_toE4_qShellPoint (by linarith)]; exact h1
  have hstep : innerCollarChart c u₀ ⟨centeredChartParam c (qShellPoint a s), hy⟩
      = shellCollarChart u₀ ⟨toE4 (qShellPoint a s), hshell⟩ := by
    show shellCollarChart u₀ (shellIncl ((collarHomeo c).symm
      ⟨centeredChartParam c (qShellPoint a s), hy⟩)) = _
    rw [collarHomeo_symm_qShellPoint c a h1 h2 hy]
    rfl
  rw [hstep]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · show chartAt (EuclideanSpace ℝ (Fin 3)) u₀
      (shellDir ⟨toE4 (qShellPoint a s), hshell⟩) = _
    rw [shellDir_qShellPoint h1 hshell]
  · show WithLp.toLp 2 (fun _ : Fin 1 => ‖toE4 (qShellPoint a s)‖ - 1 / 2) = _
    rw [norm_toE4_qShellPoint (by linarith : (0 : ℝ) ≤ s)]

/-! ## §2. The Q chart's interior branch is vacuous against the seam -/

/-- The open Q collar ball sits inside the round **closed** ball of chart radius `5/8`. -/
theorem qOpenBall_subset_chartClosedBall58 (c : EIndex) :
    qOpenBall c ⊆ chartClosedBall58 c.1 := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨toE4 t, ?_, ?_⟩
  · have h1 : ‖toE4 t‖ ^ 2 = sqNorm t := norm_sq_toE4 t
    have h2 : sqNorm t < (5 / 8 : ℝ) ^ 2 := ht
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg (toE4 t)]
  · show centeredChartParam c.1 (ofE4 (toE4 t)) = centeredChartParam c.1 t
    rw [ofE4_toE4]

/-- **The round closed ball is `τ`-stable** — the involution is `w ↦ −w` in the round chart at a
fixed point, and the ball is centrally symmetric. -/
theorem chartClosedBall58_involution {c : TorusFour} (hc : c ∈ fixedSet) {x : TorusFour}
    (hx : x ∈ chartClosedBall58 c) : torusFourInvolution x ∈ chartClosedBall58 c := by
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨-w, by rwa [Metric.mem_closedBall, dist_zero_right, norm_neg,
    ← dist_zero_right], ?_⟩
  exact (SKEFTHawking.KummerQuotientManifold.param_invol hc w).symm

/-- **THE Q-SIDE VACUITY.** No representative of a point of the open Q collar lies in the
round-ball interior region: the point itself is inside the closed `5/8` ball, and so is its
`τ`-image. Hence the *interior* branch of the `Q`-chart dispatch can never meet a seam
neighbourhood — only the collar branch can. -/
theorem notMem_interiorSet_of_mem_qOpenCollarSet {c : EIndex} {q : FreeQuotient}
    (hq : q ∈ qOpenCollarSet c) {y : ↥puncturedTorus} (hy : qmk y = q) :
    (y : TorusFour) ∉ interiorSet := by
  obtain ⟨w, hw, hwq⟩ := hq
  have hball : (w : TorusFour) ∈ chartClosedBall58 c.1 :=
    qOpenBall_subset_chartClosedBall58 c hw
  have hmem : (y : TorusFour) ∈ chartClosedBall58 c.1 := by
    rcases (qmk_eq_iff w y).mp (hwq.trans hy.symm) with rfl | hτ
    · exact hball
    · have hwy : (w : TorusFour) = torusFourInvolution (y : TorusFour) := by
        rw [hτ]; exact neg_one_smul_val y
      have hτb := chartClosedBall58_involution (eIndex_fixedSet c) hball
      rwa [hwy, SKEFTHawking.KummerInvolution.torusFourInvolution_involutive] at hτb
  intro hint
  exact hint (Set.mem_biUnion (Finset.mem_coe.mpr c.2) hmem)

/-! ## §3. The interior branch of the `Q`-chart dispatch never meets a seam neighbourhood -/

/-- A point in the source of a descended **interior** `Q`-chart has a representative in the
round-ball interior region. -/
theorem exists_rep_mem_interiorSet {x : ↥puncturedTorus} (hx : (x : TorusFour) ∈ interiorSet)
    {q : FreeQuotient} (hq : q ∈ (qmkInteriorChart x hx).source) :
    ∃ y : ↥puncturedTorus, qmk y = q ∧ (y : TorusFour) ∈ interiorSet := by
  rw [qmkInteriorChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hq
  obtain ⟨hq1, hq2⟩ := hq
  rw [interiorChartR, OpenPartialHomeomorph.lift_openEmbedding_source] at hq2
  obtain ⟨w, -, hw⟩ := hq2
  refine ⟨(SKEFTHawking.KummerChartedSpace.qmk_localOpenPartialHomeomorph x).symm q, ?_, ?_⟩
  · have := (SKEFTHawking.KummerChartedSpace.qmk_localOpenPartialHomeomorph x).right_inv hq1
    rwa [SKEFTHawking.KummerChartedSpace.qmk_localOpenPartialHomeomorph_apply] at this
  · rw [← hw]; exact w.2

/-- **THE INTERIOR BRANCH IS VACUOUS AGAINST THE SEAM.** No descended interior `Q`-chart has any
point of the open Q collar in its source — so in the (2,3) transition class only the *collar* branch
of the `Q`-chart dispatch carries content. -/
theorem disjoint_qmkInteriorChart_qOpenCollarSet (c : EIndex) {x : ↥puncturedTorus}
    (hx : (x : TorusFour) ∈ interiorSet) :
    Disjoint (qmkInteriorChart x hx).source (qOpenCollarSet c) := by
  rw [Set.disjoint_left]
  intro q hq hqc
  obtain ⟨y, hy, hyint⟩ := exists_rep_mem_interiorSet hx hq
  exact notMem_interiorSet_of_mem_qOpenCollarSet hqc hy hyint

end

end SKEFTHawking.KummerSeamTransQ
