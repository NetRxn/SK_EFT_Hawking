/-
# Phase 5q.H — K7 NO-GO: the un-thickened seam-cover hypothesis is FALSE

**`¬ K7SeamCoverHyp`** (`k7SeamCoverHyp_false`): the interiors of the two CLOSED pieces
`qImage`, `eImage` of the Kummer weld do NOT cover `K3`. A seam point is interior to neither:

* not interior to `qImage` — every neighborhood contains `E`-points of fiber radius `< 1`
  (approach along the banked inward fiber scaling `deform`), and any `E`-point of `qImage` is a
  seam point of fiber radius `1`;
* not interior to `eImage` — every neighborhood contains `Q`-points strictly outside the excision
  spheres (approach along the outward chart ray `s ↦ centeredChartParam c (s • t₀)`, `s > 1`),
  and any `Q`-point of `eImage` is a seam point ON one of the 16 spheres. The outward ray needs
  chart injectivity slightly BEYOND the excision radius; §0 widens the banked per-factor
  `circle_exp_injOn_half` to `|s| ≤ 1` (`Circle.exp` has period `2π > 6`), giving injectivity of
  the centered chart on the doubled ball `{sqNorm ≤ 1}` (`centeredChartParam_injOn_double`).

Consequence: the K7 Mayer–Vietoris can NEVER be run on the closed pieces directly — the opener's
`K7SeamCoverHyp`-conditional layer is settled-dead, and the collar-thickened instantiation
(`KummerK7MVAssembly.k7_hcov`) is the unique route. Candidate for `KERNEL_NOGO_REGISTRY`
(encode-on-settle, Invariant #17).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerK7Opener
import SKEFTHawking.KummerWeldFiberFlow

namespace SKEFTHawking.KummerK7SeamCoverNoGo

open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerInvolution
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerWeldFiberFlow

noncomputable section

/-! ## §0. Chart injectivity on the doubled ball -/

/-- **Per-factor chart injectivity on `[−1, 1]`**: `Circle.exp` is injective there (its period is
`2π > 6 > 2`). Widens the banked `circle_exp_injOn_half` beyond the excision radius, for the
outward approach ray. -/
theorem circle_exp_injOn_one {s s' : ℝ} (hs : |s| ≤ 1) (hs' : |s'| ≤ 1)
    (h : Circle.exp s = Circle.exp s') : s = s' := by
  have hc : Complex.exp (↑s * Complex.I) = Complex.exp (↑s' * Complex.I) := by
    rw [← Circle.coe_exp, ← Circle.coe_exp, h]
  rw [Complex.exp_eq_exp_iff_exists_int] at hc
  obtain ⟨n, hn⟩ := hc
  have hfac : (↑s : ℂ) * Complex.I = (↑s' + ↑n * (2 * ↑Real.pi)) * Complex.I := by rw [hn]; ring
  have hcC : (↑s : ℂ) = ↑s' + ↑n * (2 * ↑Real.pi) := mul_right_cancel₀ Complex.I_ne_zero hfac
  have hR : s = s' + (n : ℝ) * (2 * Real.pi) := by exact_mod_cast hcC
  have hpi : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hdiff : |(n : ℝ) * (2 * Real.pi)| ≤ 2 := by
    have he : (n : ℝ) * (2 * Real.pi) = s - s' := by linarith [hR]
    rw [he]
    calc |s - s'| ≤ |s| + |s'| := abs_sub _ _
      _ ≤ 1 + 1 := by linarith [hs, hs']
      _ = 2 := by norm_num
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hz : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hne)
      have hz' := (Int.cast_le (R := ℝ)).mpr hz
      rwa [Int.cast_abs, Int.cast_one] at hz'
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hdiff
    nlinarith [hdiff, h1, hpi]
  rw [hn0] at hR; simpa using hR

/-- **Chart injectivity on the doubled closed ball `{sqNorm ≤ 1}`** (radius `1 = 2ρ`): each
coordinate satisfies `|t.i| ≤ 1`, where `Circle.exp` is injective (`circle_exp_injOn_one`). -/
theorem centeredChartParam_injOn_double (c : TorusFour) :
    Set.InjOn (centeredChartParam c) {t | sqNorm t ≤ 1} := by
  intro t ht t' ht' h
  rw [Set.mem_setOf_eq] at ht ht'
  have a1 : |t.1| ≤ 1 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.2.1, sq_nonneg t.2.2.1, sq_nonneg t.2.2.2])
  have a2 : |t.2.1| ≤ 1 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.1, sq_nonneg t.2.2.1, sq_nonneg t.2.2.2])
  have a3 : |t.2.2.1| ≤ 1 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2.2])
  have a4 : |t.2.2.2| ≤ 1 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2.1])
  have a1' : |t'.1| ≤ 1 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.2.1, sq_nonneg t'.2.2.1, sq_nonneg t'.2.2.2])
  have a2' : |t'.2.1| ≤ 1 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.2.1, sq_nonneg t'.2.2.2])
  have a3' : |t'.2.2.1| ≤ 1 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.1, sq_nonneg t'.2.2.2])
  have a4' : |t'.2.2.2| ≤ 1 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.1, sq_nonneg t'.2.2.1])
  simp only [centeredChartParam, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4⟩ := h
  exact Prod.ext (circle_exp_injOn_one a1 a1' (mul_left_cancel e1))
    (Prod.ext (circle_exp_injOn_one a2 a2' (mul_left_cancel e2))
      (Prod.ext (circle_exp_injOn_one a3 a3' (mul_left_cancel e3))
        (circle_exp_injOn_one a4 a4' (mul_left_cancel e4))))

theorem sqNorm_smul (s : ℝ) (t : ℝ × ℝ × ℝ × ℝ) : sqNorm (s • t) = s ^ 2 * sqNorm t := by
  simp only [sqNorm, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The inward fiber scaling scales the fiber norm: `fiberNorm (deform (x, t)) = t · fiberNorm x`. -/
theorem fiberNorm_deform (x : ResE) (t : unitInterval) :
    fiberNorm (deform (x, t)) = (t : ℝ) * fiberNorm x := by
  induction x using Quotient.ind with
  | _ a => cases a with
    | inl q =>
      show fiberNorm (chart0 (q.1, scaleDisk t q.2)) = _
      rw [fiberNorm_chart0]
      show ‖((scaleDisk t q.2 : Disk) : ℂ)‖ = _
      rw [scaleDisk_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (unitInterval.nonneg t)]
      rfl
    | inr q =>
      show fiberNorm (chart1 (q.1, scaleDisk t q.2)) = _
      rw [fiberNorm_chart1]
      show ‖((scaleDisk t q.2 : Disk) : ℂ)‖ = _
      rw [scaleDisk_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (unitInterval.nonneg t)]
      rfl

/-- A concrete point of `S³ ⊂ ℂ²`. -/
def s3Base : S3 := ⟨(1, 0), by simp⟩

/-! ## §1. A seam point is not interior to the `Q`-piece (`E`-side approach) -/

/-- **A seam point is never interior to `qImage`**: the inward fiber-scaling path enters every
neighborhood at fiber radius `< 1`, but `E`-points of `qImage` are seam points of fiber radius
`1`. -/
theorem seam_not_mem_interior_qImage (c : EIndex) (r : RP3) :
    weldMk (Sum.inr (c, bdryMapRP3 r)) ∉ interior qImage := by
  intro hmem
  have hg : Continuous (fun e : ResE => weldMk (Sum.inr (c, e))) :=
    continuous_weldMk.comp (continuous_inr.comp (Continuous.prodMk continuous_const continuous_id))
  have hUsub : ((fun e : ResE => weldMk (Sum.inr (c, e))) ⁻¹' interior qImage) ⊆ boundaryE := by
    intro e he
    have hq : weldMk (Sum.inr (c, e)) ∈ qImage := interior_subset he
    have hseam : weldMk (Sum.inr (c, e)) ∈ seam :=
      qImage_inter_eImage ▸ (⟨hq, ⟨(c, e), rfl⟩⟩ : _ ∈ qImage ∩ eImage)
    simp only [seam, Set.mem_iUnion, Set.mem_range] at hseam
    obtain ⟨c', r', heq⟩ := hseam
    have hpair := weldMk_inr_injective heq
    have he' : e = bdryMapRP3 r' := (congrArg Prod.snd hpair).symm
    rw [he']
    exact range_bdryMapRP3_eq_boundaryE ▸ Set.mem_range_self r'
  -- the inward fiber path, ℝ-parametrized through the interval clamp
  set γ : ℝ → ResE :=
    fun s => deform (bdryMapRP3 r, Set.projIcc (0 : ℝ) 1 zero_le_one s) with hγdef
  have hγc : Continuous γ :=
    continuous_deform.comp (Continuous.prodMk continuous_const (continuous_projIcc))
  have hγ1 : γ 1 = bdryMapRP3 r := by
    have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = 1 :=
      Subtype.ext (by
        rw [Set.projIcc_of_mem _ (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)]
        rfl)
    rw [hγdef]
    show deform (bdryMapRP3 r, Set.projIcc (0 : ℝ) 1 zero_le_one 1) = bdryMapRP3 r
    rw [hproj]
    exact deform_one _
  have hopen : IsOpen (γ ⁻¹' ((fun e : ResE => weldMk (Sum.inr (c, e))) ⁻¹' interior qImage)) :=
    (isOpen_interior.preimage hg).preimage hγc
  have h1mem : (1 : ℝ) ∈ γ ⁻¹' ((fun e : ResE => weldMk (Sum.inr (c, e))) ⁻¹' interior qImage) := by
    simp only [Set.mem_preimage, hγ1]
    exact hmem
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 1 h1mem
  set s₁ : ℝ := 1 - min ε 1 / 2 with hs₁def
  have hminpos : 0 < min ε 1 := lt_min hε one_pos
  have hs₁lt : s₁ < 1 := by rw [hs₁def]; linarith
  have hs₁icc : s₁ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · rw [hs₁def]; have := min_le_right ε 1; linarith
    · exact hs₁lt.le
  have hs₁mem : s₁ ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, hs₁def,
      show 1 - min ε 1 / 2 - 1 = -(min ε 1 / 2) by ring, abs_neg,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ min ε 1 / 2)]
    have := min_le_left ε 1
    linarith
  have hs₁b : γ s₁ ∈ boundaryE := hUsub (hball hs₁mem)
  have hval : fiberNorm (γ s₁) = s₁ := by
    rw [hγdef]
    show fiberNorm (deform (bdryMapRP3 r, Set.projIcc (0 : ℝ) 1 zero_le_one s₁)) = s₁
    rw [fiberNorm_deform, fiberNorm_bdryMapRP3, mul_one, Set.projIcc_of_mem _ hs₁icc]
  have hone : fiberNorm (γ s₁) = 1 := fiberNorm_eq_one_iff.mpr hs₁b
  rw [hval] at hone
  linarith

/-! ## §2. A seam point is not interior to the `E`-piece (`Q`-side outward ray) -/

/-- The outward chart ray stays in the punctured torus: for `1 ≤ s ≤ 3/2`, the scaled sphere point
`centeredChartParam c (s • t₀)` (`sqNorm t₀ = ρ²`) misses all 16 excised balls — its own by the
doubled-ball chart injectivity, the others by the metric separation `2` of the fixed points. -/
theorem scaled_sphere_mem_puncturedTorus (c : EIndex) {t₀ : ℝ × ℝ × ℝ × ℝ}
    (ht₀ : sqNorm t₀ = excisionRadius ^ 2) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 3 / 2) :
    centeredChartParam c.1 (s • t₀) ∈ puncturedTorus := by
  rw [puncturedTorus, Set.mem_compl_iff, excisedBalls]
  intro hmem
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨c'', hc'', hball⟩ := hmem
  obtain ⟨u, hu, hequ⟩ := hball
  rw [Set.mem_setOf_eq, show excisionRadius = (1 : ℝ) / 2 from rfl] at hu
  by_cases hcc : c'' = c.1
  · subst hcc
    have hu1 : u ∈ {t | sqNorm t ≤ 1} := by
      rw [Set.mem_setOf_eq]; nlinarith [hu]
    have hst1 : s • t₀ ∈ {t | sqNorm t ≤ 1} := by
      rw [Set.mem_setOf_eq, sqNorm_smul, ht₀, show excisionRadius = (1 : ℝ) / 2 from rfl]
      nlinarith
    have hust := centeredChartParam_injOn_double c.1 hu1 hst1 hequ
    rw [hust, sqNorm_smul, ht₀, show excisionRadius = (1 : ℝ) / 2 from rfl] at hu
    nlinarith
  · have hd1 : dist (centeredChartParam c.1 (s • t₀)) c.1 ≤ 3 / 4 := by
      refine dist_centeredChartParam_le c.1 (by norm_num) ?_
      rw [sqNorm_smul, ht₀, show excisionRadius = (1 : ℝ) / 2 from rfl]
      nlinarith
    have hd2 : dist (centeredChartParam c.1 (s • t₀)) c'' < 1 / 2 := by
      have hb := chartBall_subset_metricBall c'' ⟨u, by
        rw [Set.mem_setOf_eq, show excisionRadius = (1 : ℝ) / 2 from rfl]; exact hu, hequ⟩
      rw [Metric.mem_ball, show excisionRadius = (1 : ℝ) / 2 from rfl] at hb
      exact hb
    have hsep : 2 ≤ dist c'' c.1 :=
      fixedSet_dist_ge hc'' (eIndex_fixedSet c) hcc
    have htri := dist_triangle c'' (centeredChartParam c.1 (s • t₀)) c.1
    rw [dist_comm c'' (centeredChartParam c.1 (s • t₀))] at htri
    linarith

/-- The outward ray at `s > 1` is on NO excision sphere — its own by the doubled-ball injectivity
(`sqNorm` mismatch), the others by metric separation. -/
theorem scaled_sphere_not_mem_chartSphere (c : EIndex) {t₀ : ℝ × ℝ × ℝ × ℝ}
    (ht₀ : sqNorm t₀ = excisionRadius ^ 2) {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 3 / 2)
    (c' : EIndex) : centeredChartParam c.1 (s • t₀) ∉ chartSphere c'.1 := by
  rintro ⟨w, hw, hequ⟩
  rw [Set.mem_setOf_eq, show excisionRadius = (1 : ℝ) / 2 from rfl] at hw
  by_cases hcc : c'.1 = c.1
  · rw [hcc] at hequ
    have hw1 : w ∈ {t | sqNorm t ≤ 1} := by
      rw [Set.mem_setOf_eq]; nlinarith [hw]
    have hst1 : s • t₀ ∈ {t | sqNorm t ≤ 1} := by
      rw [Set.mem_setOf_eq, sqNorm_smul, ht₀, show excisionRadius = (1 : ℝ) / 2 from rfl]
      nlinarith
    have hwst := centeredChartParam_injOn_double c.1 hw1 hst1 hequ
    rw [hwst, sqNorm_smul, ht₀, show excisionRadius = (1 : ℝ) / 2 from rfl] at hw
    nlinarith
  · have hd1 : dist (centeredChartParam c.1 (s • t₀)) c.1 ≤ 3 / 4 := by
      refine dist_centeredChartParam_le c.1 (by norm_num) ?_
      rw [sqNorm_smul, ht₀, show excisionRadius = (1 : ℝ) / 2 from rfl]
      nlinarith
    have hd2 : dist (centeredChartParam c.1 (s • t₀)) c'.1 ≤ 1 / 2 := by
      rw [← hequ]
      refine dist_centeredChartParam_le c'.1 (by norm_num) ?_
      exact le_of_eq hw
    have hsep : 2 ≤ dist c'.1 c.1 :=
      fixedSet_dist_ge (eIndex_fixedSet c') (eIndex_fixedSet c) hcc
    have htri := dist_triangle c'.1 (centeredChartParam c.1 (s • t₀)) c.1
    rw [dist_comm c'.1 (centeredChartParam c.1 (s • t₀))] at htri
    linarith

/-- **A seam point is never interior to `eImage`**: the outward chart ray enters every
neighborhood strictly outside the excision spheres, but `Q`-points of `eImage` are seam points ON
one of the 16 spheres. -/
theorem seam_not_mem_interior_eImage (c : EIndex) (a : S3) :
    weldMk (Sum.inl (qBdryMap c (mkRP3 a))) ∉ interior eImage := by
  intro hmem
  have hh : Continuous (fun q : FreeQuotient => weldMk (Sum.inl q)) :=
    continuous_weldMk.comp continuous_inl
  -- Q-points of the interior are boundary-sphere points of Q
  have hWsub : ∀ q ∈ ((fun q : FreeQuotient => weldMk (Sum.inl q)) ⁻¹' interior eImage),
      ∃ (c' : EIndex) (r' : RP3), q = qBdryMap c' r' := by
    intro q hq
    have he : weldMk (Sum.inl q) ∈ eImage := interior_subset hq
    have hseam : weldMk (Sum.inl q) ∈ seam :=
      qImage_inter_eImage ▸ (⟨⟨q, rfl⟩, he⟩ : _ ∈ qImage ∩ eImage)
    rw [seam_eq_qBoundary_image] at hseam
    simp only [Set.mem_iUnion, Set.mem_range] at hseam
    obtain ⟨c', r', heq⟩ := hseam
    exact ⟨c', r', (weldMk_inl_injective heq).symm⟩
  -- the base point upstairs, on the sphere of `c`
  set t₀ : ℝ × ℝ × ℝ × ℝ := scaleToChart a with ht₀def
  have ht₀ : sqNorm t₀ = excisionRadius ^ 2 := sqNorm_scaleToChart a
  -- the clamped outward ray in the punctured torus
  set cs : ℝ → ℝ := fun s => min (max s 1) (3 / 2) with hcsdef
  have hcs_mem : ∀ s : ℝ, 1 ≤ cs s ∧ cs s ≤ 3 / 2 := fun s =>
    ⟨le_min (le_max_right s 1) (by norm_num), min_le_right _ _⟩
  set σ : ℝ → ↥puncturedTorus := fun s =>
    ⟨centeredChartParam c.1 (cs s • t₀),
      scaled_sphere_mem_puncturedTorus c ht₀ (hcs_mem s).1 (hcs_mem s).2⟩ with hσdef
  have hσc : Continuous σ := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_centeredChartParam c.1).comp
      (((continuous_id.max continuous_const).min continuous_const).smul continuous_const)
  have hσ1 : σ 1 = ⟨centeredChartParam c.1 t₀,
      sphere_subset_puncturedTorus (eIndex_fixedSet c) ⟨t₀, ht₀, rfl⟩⟩ := by
    refine Subtype.ext ?_
    show centeredChartParam c.1 (cs 1 • t₀) = centeredChartParam c.1 t₀
    rw [show cs 1 = 1 by rw [hcsdef]; norm_num, one_smul]
  -- the pulled-back neighborhood of 1
  have hopen : IsOpen (σ ⁻¹' (qmk ⁻¹'
      ((fun q : FreeQuotient => weldMk (Sum.inl q)) ⁻¹' interior eImage))) :=
    (((isOpen_interior.preimage hh).preimage continuous_quotient_mk').preimage hσc)
  have h1mem : (1 : ℝ) ∈ σ ⁻¹' (qmk ⁻¹'
      ((fun q : FreeQuotient => weldMk (Sum.inl q)) ⁻¹' interior eImage)) := by
    simp only [Set.mem_preimage, hσ1]
    exact hmem
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 1 h1mem
  set s₁ : ℝ := 1 + min ε 1 / 2 with hs₁def
  have hminpos : 0 < min ε 1 := lt_min hε one_pos
  have hminle : min ε 1 ≤ 1 := min_le_right ε 1
  have hs₁gt : 1 < s₁ := by rw [hs₁def]; linarith
  have hs₁le : s₁ ≤ 3 / 2 := by rw [hs₁def]; linarith
  have hcs₁ : cs s₁ = s₁ := by
    rw [hcsdef]
    show min (max s₁ 1) (3 / 2) = s₁
    rw [max_eq_left hs₁gt.le, min_eq_left hs₁le]
  have hs₁mem : s₁ ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, hs₁def,
      show 1 + min ε 1 / 2 - 1 = min ε 1 / 2 by ring,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ min ε 1 / 2)]
    have := min_le_left ε 1
    linarith
  obtain ⟨c', r', hq⟩ := hWsub (qmk (σ s₁)) (hball hs₁mem)
  -- unwrap the boundary identification: σ s₁ is (a lift of) a sphere point of c'
  induction r' using Quotient.ind with
  | _ a' =>
    rw [show (Quotient.mk antipSetoid a' : RP3) = mkRP3 a' from rfl, qBdryMap_mk] at hq
    rcases (qmk_eq_iff (σ s₁) _).mp hq with heq | heq
    · have hval := congrArg Subtype.val heq
      have hσval : (σ s₁ : TorusFour) = centeredChartParam c.1 (s₁ • t₀) := by
        rw [hσdef]
        show centeredChartParam c.1 (cs s₁ • t₀) = centeredChartParam c.1 (s₁ • t₀)
        rw [hcs₁]
      rw [hσval] at hval
      exact scaled_sphere_not_mem_chartSphere c ht₀ hs₁gt hs₁le c'
        ⟨scaleToChart a', sqNorm_scaleToChart a', hval.symm⟩
    · have hval := congrArg Subtype.val heq
      rw [neg_one_smul_val] at hval
      have hτ : torusFourInvolution (centeredChartParam c'.1 (scaleToChart a'))
          = centeredChartParam c'.1 (chartNeg (scaleToChart a')) :=
        centeredChartParam_involution c'.1 (eIndex_fixedSet c') _
      rw [show ((⟨centeredChartParam c'.1 (scaleToChart a'),
          sphere_subset_puncturedTorus (eIndex_fixedSet c')
            ⟨scaleToChart a', sqNorm_scaleToChart a', rfl⟩⟩ : ↥puncturedTorus) : TorusFour)
          = centeredChartParam c'.1 (scaleToChart a') from rfl, hτ] at hval
      have hσval : (σ s₁ : TorusFour) = centeredChartParam c.1 (s₁ • t₀) := by
        rw [hσdef]
        show centeredChartParam c.1 (cs s₁ • t₀) = centeredChartParam c.1 (s₁ • t₀)
        rw [hcs₁]
      rw [hσval] at hval
      refine scaled_sphere_not_mem_chartSphere c ht₀ hs₁gt hs₁le c'
        ⟨chartNeg (scaleToChart a'), ?_, hval.symm⟩
      rw [Set.mem_setOf_eq, sqNorm_chartNeg]
      exact sqNorm_scaleToChart a'

/-! ## §3. The no-go -/

/-- **THE K7 SEAM-COVER NO-GO** — the K7 opener's `K7SeamCoverHyp` is FALSE: the interiors of the
closed pieces `qImage`, `eImage` do not cover `K3` (a seam point is interior to neither). The K7
Mayer–Vietoris must be run on the collar-thickened pieces (`KummerK7MVAssembly.k7_hcov`); any
attempt to discharge `K7SeamCoverHyp` itself is settled-dead. -/
theorem k7SeamCoverHyp_false : ¬ SKEFTHawking.KummerK7Opener.K7SeamCoverHyp := by
  intro h
  obtain ⟨c⟩ : Nonempty EIndex :=
    Fintype.card_pos_iff.mp (by rw [eIndex_card]; norm_num)
  have hpu : weldMk (Sum.inl (qBdryMap c (mkRP3 s3Base)))
      ∈ (⋃ U ∈ ({qImage, eImage} : Set (Set KummerK3)), interior U) := by
    rw [h]; exact Set.mem_univ _
  simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop] at hpu
  obtain ⟨U, hU, hpU⟩ := hpu
  rcases hU with rfl | rfl
  · rw [weldMk_seam] at hpU
    exact seam_not_mem_interior_qImage c (mkRP3 s3Base) hpU
  · exact seam_not_mem_interior_eImage c s3Base hpU

end

end SKEFTHawking.KummerK7SeamCoverNoGo
