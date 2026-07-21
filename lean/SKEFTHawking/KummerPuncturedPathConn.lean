/-
# Phase 5q.H — K7 residual (a): path-connectedness of the punctured torus `T⁴°`

`T⁴° = T⁴ ∖ (16 round chart balls)` is path-connected — the degree-0 input of the `Q`-side Smith
sequence solve (`inclAH₀`-injectivity needs the augmentation/filling argument at a base point, which
requires `PathConnectedSpace ↥puncturedTorus`). It also discharges the hypothesis of the banked
`KummerK7Opener.freeQuotient_pathConnected`, giving `PathConnectedSpace FreeQuotient` for free.

Route (explicit coordinatewise `exp`-paths; the sup-product metric makes one safe coordinate a
global certificate):
* §1 chord calculus: `dist (a·exp θ) a = 2|sin(θ/2)|`, `dist (a·exp θ) (−a) = 2|cos(θ/2)|`.
* §2 the far-coordinate membership certificate: a point with one coordinate at distance `> 1/2`
  from BOTH square roots of unity lies outside every excised ball.
* §3 the widened chart injectivity (`|s| ≤ 3/2`) and the shell certificate: a chart point over
  `c` with `sqNorm ≥ ρ²` and all chart angles `≤ 7/5` is in `T⁴°`.
* §4 chart-coordinate extraction: a point within `1/2` of a fixed point has chart angles `≤ 1`
  (Jordan's inequality).
* §5 the path bricks: hub move (coordinates 1–3 → `i` under a `±i` fourth-coordinate
  certificate), the `−i → i` bridge, the protected fourth-coordinate move, the self-protected
  fourth-coordinate move (interval trig bounds), and the in-chart escape of the fourth coordinate
  to angle `±7/5`.
* §6 assembly: every point joins `(i,i,i,i)`; `IsPathConnected puncturedTorus`;
  `PathConnectedSpace ↥puncturedTorus`; `PathConnectedSpace FreeQuotient`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerFreeQuotient
import SKEFTHawking.KummerK7Opener

namespace SKEFTHawking.KummerPuncturedPathConn

open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerInvolution (negOne coe_negOne torusFourInvolution)
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerFreeQuotient (circleI coe_circleI FreeQuotient)

noncomputable section

/-! ## §1. Chord calculus on the circle -/

/-- `‖exp(θi) − 1‖ = 2|sin(θ/2)|` — the chord to `1`. -/
theorem norm_exp_sub_one (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hre : (Complex.exp (θ * Complex.I) - 1).re = Real.cos θ - 1 := by
    simp [Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  have him : (Complex.exp (θ * Complex.I) - 1).im = Real.sin θ := by
    simp [Complex.exp_mul_I, Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  have hsq : Complex.normSq (Complex.exp (θ * Complex.I) - 1)
      = 4 * Real.sin (θ / 2) ^ 2 := by
    rw [Complex.normSq_apply, hre, him]
    have h1 := Real.sin_sq_add_cos_sq θ
    have h2 := Real.sin_sq_eq_half_sub (θ / 2)
    have h3 : 2 * (θ / 2) = θ := by ring
    rw [h3] at h2
    nlinarith [h1, h2]
  rw [Complex.norm_def, hsq,
    show (4 : ℝ) * Real.sin (θ / 2) ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 by
      rw [mul_pow, sq_abs]; ring]
  exact Real.sqrt_sq (by positivity)

/-- `‖exp(θi) + 1‖ = 2|cos(θ/2)|` — the chord to `−1`. -/
theorem norm_exp_add_one (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) + 1‖ = 2 * |Real.cos (θ / 2)| := by
  have hre : (Complex.exp (θ * Complex.I) + 1).re = Real.cos θ + 1 := by
    simp [Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  have him : (Complex.exp (θ * Complex.I) + 1).im = Real.sin θ := by
    simp [Complex.exp_mul_I, Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  have hsq : Complex.normSq (Complex.exp (θ * Complex.I) + 1)
      = 4 * Real.cos (θ / 2) ^ 2 := by
    rw [Complex.normSq_apply, hre, him]
    have h1 := Real.sin_sq_add_cos_sq θ
    have h2 := Real.cos_sq (θ / 2)
    have h3 : 2 * (θ / 2) = θ := by ring
    rw [h3] at h2
    nlinarith [h1, h2]
  rw [Complex.norm_def, hsq,
    show (4 : ℝ) * Real.cos (θ / 2) ^ 2 = (2 * |Real.cos (θ / 2)|) ^ 2 by
      rw [mul_pow, sq_abs]; ring]
  exact Real.sqrt_sq (by positivity)

/-- The chord from `a·exp θ` back to the center `a`. -/
theorem dist_mul_exp_self (a : Circle) (θ : ℝ) :
    dist (a * Circle.exp θ) a = 2 * |Real.sin (θ / 2)| := by
  show dist ((↑(a * Circle.exp θ) : ℂ)) (↑a) = _
  rw [Complex.dist_eq, Circle.coe_mul, Circle.coe_exp,
    show (↑a : ℂ) * Complex.exp (↑θ * Complex.I) - ↑a
      = ↑a * (Complex.exp (↑θ * Complex.I) - 1) by ring,
    norm_mul, Circle.norm_coe, one_mul]
  exact norm_exp_sub_one θ

/-- The chord from `a·exp θ` to the opposite pole `−a = negOne · a`. -/
theorem dist_mul_exp_negMul (a : Circle) (θ : ℝ) :
    dist (a * Circle.exp θ) (negOne * a) = 2 * |Real.cos (θ / 2)| := by
  show dist ((↑(a * Circle.exp θ) : ℂ)) (↑(negOne * a)) = _
  rw [Complex.dist_eq, Circle.coe_mul, Circle.coe_exp, Circle.coe_mul, coe_negOne,
    show (↑a : ℂ) * Complex.exp (↑θ * Complex.I) - (-1) * ↑a
      = ↑a * (Complex.exp (↑θ * Complex.I) + 1) by ring,
    norm_mul, Circle.norm_coe, one_mul]
  exact norm_exp_add_one θ

@[simp] theorem negOne_mul_negOne : (negOne : Circle) * negOne = 1 := by
  apply Subtype.ext
  rw [Circle.coe_mul, coe_negOne]
  norm_num

/-- `exp(π/2) = i` on the circle. -/
theorem exp_pi_div_two : Circle.exp (Real.pi / 2) = circleI := by
  apply Subtype.ext
  rw [Circle.coe_exp, coe_circleI, Complex.exp_mul_I]
  rw [show ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) from rfl]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `exp(−π/2) = −i` on the circle. -/
theorem exp_neg_pi_div_two : Circle.exp (-(Real.pi / 2)) = negOne * circleI := by
  apply Subtype.ext
  rw [Circle.coe_exp, Circle.coe_mul, coe_negOne, coe_circleI, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-! ## §2. The far-coordinate membership certificate -/

/-- A circle coordinate is **far** when it is `> 1/2` from both square roots of unity. -/
def FarCoord (z : Circle) : Prop := 1 / 2 < dist z 1 ∧ 1 / 2 < dist z negOne

/-- The generic certificate: a coordinate projection that contracts distances and sends fixed
points to `{1, negOne}` protects the whole point when far. -/
theorem mem_puncturedTorus_of_far (x : TorusFour) (proj : TorusFour → Circle)
    (hd : ∀ y c : TorusFour, dist (proj y) (proj c) ≤ dist y c)
    (hf : ∀ c ∈ fixedSet, proj c = 1 ∨ proj c = negOne)
    (hfar : FarCoord (proj x)) : x ∈ puncturedTorus := by
  rw [show puncturedTorus = (excisedBalls)ᶜ from rfl, Set.mem_compl_iff,
    show excisedBalls = ⋃ c ∈ fixedSet, chartBall c from rfl]
  intro hx
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨c, hc, hball⟩ := hx
  have hmem := chartBall_subset_metricClosedBall c hball
  rw [Metric.mem_closedBall, show excisionRadius = (1 : ℝ) / 2 from rfl] at hmem
  have hle : dist (proj x) (proj c) ≤ 1 / 2 := le_trans (hd x c) hmem
  rcases hf c hc with hpc | hpc <;> rw [hpc] at hle
  · linarith [hfar.1]
  · linarith [hfar.2]

theorem mem_of_far₁ {x : TorusFour} (h : FarCoord x.1) : x ∈ puncturedTorus :=
  mem_puncturedTorus_of_far x Prod.fst le_dist_c1
    (fun c hc => ((mem_fixedSet_iff c).mp hc).1) h

theorem mem_of_far₂ {x : TorusFour} (h : FarCoord x.2.1) : x ∈ puncturedTorus :=
  mem_puncturedTorus_of_far x (fun y => y.2.1) le_dist_c2
    (fun c hc => ((mem_fixedSet_iff c).mp hc).2.1) h

theorem mem_of_far₃ {x : TorusFour} (h : FarCoord x.2.2.1) : x ∈ puncturedTorus :=
  mem_puncturedTorus_of_far x (fun y => y.2.2.1) le_dist_c3
    (fun c hc => ((mem_fixedSet_iff c).mp hc).2.2.1) h

theorem mem_of_far₄ {x : TorusFour} (h : FarCoord x.2.2.2) : x ∈ puncturedTorus :=
  mem_puncturedTorus_of_far x (fun y => y.2.2.2) le_dist_c4
    (fun c hc => ((mem_fixedSet_iff c).mp hc).2.2.2) h

/-- `±i` is far from both square roots of unity (the imaginary part is `±1`). -/
theorem farCoord_of_im (z : Circle) (hz : |(↑z : ℂ).im| = 1) : FarCoord z := by
  constructor
  · show (1 : ℝ) / 2 < dist ((↑z : ℂ)) ((1 : Circle) : ℂ)
    rw [Complex.dist_eq, Circle.coe_one]
    have h1 : |((↑z : ℂ) - 1).im| ≤ ‖(↑z : ℂ) - 1‖ := Complex.abs_im_le_norm _
    have h2 : ((↑z : ℂ) - 1).im = (↑z : ℂ).im := by simp
    rw [h2, hz] at h1
    linarith
  · show (1 : ℝ) / 2 < dist ((↑z : ℂ)) ((negOne : Circle) : ℂ)
    rw [Complex.dist_eq, coe_negOne]
    have h1 : |((↑z : ℂ) - (-1)).im| ≤ ‖(↑z : ℂ) - (-1)‖ := Complex.abs_im_le_norm _
    have h2 : ((↑z : ℂ) - (-1)).im = (↑z : ℂ).im := by simp
    rw [h2, hz] at h1
    linarith

theorem farCoord_circleI : FarCoord circleI :=
  farCoord_of_im circleI (by rw [coe_circleI]; simp)

theorem farCoord_negI : FarCoord (negOne * circleI) :=
  farCoord_of_im (negOne * circleI) (by rw [Circle.coe_mul, coe_negOne, coe_circleI]; simp)

/-! ## §3. Widened chart injectivity and the shell certificate -/

/-- `Circle.exp` is injective on `[−3/2, 3/2]` (period `2π > 6`). -/
theorem circle_exp_injOn_wide {s s' : ℝ} (hs : |s| ≤ 3 / 2) (hs' : |s'| ≤ 3 / 2)
    (h : Circle.exp s = Circle.exp s') : s = s' := by
  have hc : Complex.exp (↑s * Complex.I) = Complex.exp (↑s' * Complex.I) := by
    rw [← Circle.coe_exp, ← Circle.coe_exp, h]
  rw [Complex.exp_eq_exp_iff_exists_int] at hc
  obtain ⟨n, hn⟩ := hc
  have hfac : (↑s : ℂ) * Complex.I = (↑s' + ↑n * (2 * ↑Real.pi)) * Complex.I := by rw [hn]; ring
  have hcC : (↑s : ℂ) = ↑s' + ↑n * (2 * ↑Real.pi) := mul_right_cancel₀ Complex.I_ne_zero hfac
  have hR : s = s' + (n : ℝ) * (2 * Real.pi) := by exact_mod_cast hcC
  have hpi : (6 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hdiff : |(n : ℝ) * (2 * Real.pi)| ≤ 3 := by
    have he : (n : ℝ) * (2 * Real.pi) = s - s' := by linarith [hR]
    rw [he]
    calc |s - s'| ≤ |s| + |s'| := abs_sub _ _
      _ ≤ 3 / 2 + 3 / 2 := by linarith [hs, hs']
      _ = 3 := by norm_num
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hz : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hne)
      have hz' := (Int.cast_le (R := ℝ)).mpr hz
      rwa [Int.cast_abs, Int.cast_one] at hz'
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hdiff
    nlinarith [hdiff, h1, hpi]
  rw [hn0] at hR; simpa using hR

/-- Chart injectivity from per-coordinate `≤ 3/2` angle bounds. -/
theorem centeredChartParam_inj_wide (c : TorusFour) {t t' : ℝ × ℝ × ℝ × ℝ}
    (h1 : |t.1| ≤ 3 / 2) (h2 : |t.2.1| ≤ 3 / 2) (h3 : |t.2.2.1| ≤ 3 / 2)
    (h4 : |t.2.2.2| ≤ 3 / 2)
    (h1' : |t'.1| ≤ 3 / 2) (h2' : |t'.2.1| ≤ 3 / 2) (h3' : |t'.2.2.1| ≤ 3 / 2)
    (h4' : |t'.2.2.2| ≤ 3 / 2)
    (h : centeredChartParam c t = centeredChartParam c t') : t = t' := by
  simp only [centeredChartParam, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4⟩ := h
  exact Prod.ext (circle_exp_injOn_wide h1 h1' (mul_left_cancel e1))
    (Prod.ext (circle_exp_injOn_wide h2 h2' (mul_left_cancel e2))
      (Prod.ext (circle_exp_injOn_wide h3 h3' (mul_left_cancel e3))
        (circle_exp_injOn_wide h4 h4' (mul_left_cancel e4))))

/-- The sup-metric chart displacement bound: all angles `≤ b` ⟹ `dist (param c t) c ≤ b`. -/
theorem dist_chart_le_of_coords (c : TorusFour) {t : ℝ × ℝ × ℝ × ℝ} {b : ℝ}
    (h1 : |t.1| ≤ b) (h2 : |t.2.1| ≤ b) (h3 : |t.2.2.1| ≤ b) (h4 : |t.2.2.2| ≤ b) :
    dist (centeredChartParam c t) c ≤ b := by
  have d1 : dist (c.1 * Circle.exp t.1) c.1 ≤ b :=
    le_trans (circle_chartParam_dist_le c.1 t.1) h1
  have d2 : dist (c.2.1 * Circle.exp t.2.1) c.2.1 ≤ b :=
    le_trans (circle_chartParam_dist_le c.2.1 t.2.1) h2
  have d3 : dist (c.2.2.1 * Circle.exp t.2.2.1) c.2.2.1 ≤ b :=
    le_trans (circle_chartParam_dist_le c.2.2.1 t.2.2.1) h3
  have d4 : dist (c.2.2.2 * Circle.exp t.2.2.2) c.2.2.2 ≤ b :=
    le_trans (circle_chartParam_dist_le c.2.2.2 t.2.2.2) h4
  show dist ((c.1 * Circle.exp t.1, c.2.1 * Circle.exp t.2.1,
      c.2.2.1 * Circle.exp t.2.2.1, c.2.2.2 * Circle.exp t.2.2.2) : TorusFour) c ≤ b
  rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
  exact max_le d1 (max_le d2 (max_le d3 d4))

/-- **The shell certificate**: a chart point over a fixed point `c` with `sqNorm ≥ ρ² = 1/4` and
all chart angles `≤ 7/5` lies in `T⁴°` — outside `chartBall c` by widened injectivity, outside
every other ball by the `2`-separation of the fixed points. -/
theorem shell_mem_puncturedTorus {c : TorusFour} (hcf : c ∈ fixedSet) {t : ℝ × ℝ × ℝ × ℝ}
    (h1 : |t.1| ≤ 7 / 5) (h2 : |t.2.1| ≤ 7 / 5) (h3 : |t.2.2.1| ≤ 7 / 5)
    (h4 : |t.2.2.2| ≤ 7 / 5) (hlo : 1 / 4 ≤ sqNorm t) :
    centeredChartParam c t ∈ puncturedTorus := by
  rw [show puncturedTorus = (excisedBalls)ᶜ from rfl, Set.mem_compl_iff,
    show excisedBalls = ⋃ c ∈ fixedSet, chartBall c from rfl]
  intro hx
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨c', hc', hball⟩ := hx
  by_cases hcc : c' = c
  · subst hcc
    obtain ⟨t', ht', heq⟩ := hball
    rw [Set.mem_setOf_eq, show excisionRadius = (1 : ℝ) / 2 from rfl] at ht'
    have b1 : |t'.1| ≤ 1 / 2 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
      simp only [sqNorm] at ht'
      nlinarith [sq_nonneg t'.2.1, sq_nonneg t'.2.2.1, sq_nonneg t'.2.2.2])
    have b2 : |t'.2.1| ≤ 1 / 2 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
      simp only [sqNorm] at ht'
      nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.2.1, sq_nonneg t'.2.2.2])
    have b3 : |t'.2.2.1| ≤ 1 / 2 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
      simp only [sqNorm] at ht'
      nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.1, sq_nonneg t'.2.2.2])
    have b4 : |t'.2.2.2| ≤ 1 / 2 := KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
      simp only [sqNorm] at ht'
      nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.1, sq_nonneg t'.2.2.1])
    have hteq : t' = t :=
      centeredChartParam_inj_wide c' (by linarith) (by linarith) (by linarith) (by linarith)
        (le_trans h1 (by norm_num)) (le_trans h2 (by norm_num))
        (le_trans h3 (by norm_num)) (le_trans h4 (by norm_num)) heq
    rw [hteq] at ht'
    linarith
  · have hd1 : dist (centeredChartParam c t) c ≤ 7 / 5 :=
      dist_chart_le_of_coords c h1 h2 h3 h4
    have hsep : (2 : ℝ) ≤ dist c c' := fixedSet_dist_ge hcf hc' (fun h => hcc h.symm)
    have hd2 : dist (centeredChartParam c t) c' ≤ 1 / 2 := by
      have := chartBall_subset_metricClosedBall c' hball
      rwa [Metric.mem_closedBall, show excisionRadius = (1 : ℝ) / 2 from rfl] at this
    have htri := dist_triangle c (centeredChartParam c t) c'
    rw [dist_comm c (centeredChartParam c t)] at htri
    linarith

/-! ## §4. Chart-coordinate extraction near a fixed point -/

/-- A circle point within `1/2` of a pole `a` is `a·exp s` with `|s| ≤ 1` (Jordan). -/
theorem circle_close_form {z a : Circle} (hd : dist z a ≤ 1 / 2) :
    ∃ s : ℝ, |s| ≤ 1 ∧ z = a * Circle.exp s := by
  refine ⟨(↑(a⁻¹ * z) : ℂ).arg, ?_, ?_⟩
  · set s := (↑(a⁻¹ * z) : ℂ).arg with hs
    have hsπ : |s| ≤ Real.pi :=
      abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
    have hsabs := abs_le.mp hsπ
    have hz : a * Circle.exp s = z := by
      rw [hs, Circle.exp_arg, mul_inv_cancel_left]
    have hchord : 2 * |Real.sin (s / 2)| ≤ 1 / 2 := by
      rw [← dist_mul_exp_self a s, hz]
      exact hd
    have habs : |Real.sin (s / 2)| = Real.sin (|s| / 2) := by
      rcases le_total 0 s with h0 | h0
      · rw [abs_of_nonneg h0, abs_of_nonneg
          (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hsabs.2]))]
      · have hnn : 0 ≤ Real.sin (-s / 2) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hsabs.1])
        rw [abs_of_nonpos h0, show s / 2 = -(-s / 2) by ring, Real.sin_neg, abs_neg,
          abs_of_nonneg hnn]
    have hjordan : 2 / Real.pi * (|s| / 2) ≤ Real.sin (|s| / 2) :=
      Real.mul_le_sin (by positivity) (by linarith [abs_nonneg s])
    have hpi4 := Real.pi_le_four
    have hpipos := Real.pi_pos
    rw [habs] at hchord
    have h1 : 2 / Real.pi * (|s| / 2) ≤ 1 / 4 := by linarith
    have h2 : |s| / Real.pi ≤ 1 / 4 := by
      have he : 2 / Real.pi * (|s| / 2) = |s| / Real.pi := by field_simp
      linarith [he ▸ h1]
    have h3 : |s| ≤ Real.pi / 4 := by
      rw [div_le_div_iff₀ hpipos (by norm_num : (0 : ℝ) < 4)] at h2
      linarith
    linarith
  · rw [Circle.exp_arg, mul_inv_cancel_left]

/-- **Chart-coordinate extraction**: a torus point within sup-distance `1/2` of a fixed point is a
chart point with all angles `≤ 1`. -/
theorem exists_chart_form {x c : TorusFour} (hd : dist x c ≤ 1 / 2) :
    ∃ t : ℝ × ℝ × ℝ × ℝ, x = centeredChartParam c t ∧
      |t.1| ≤ 1 ∧ |t.2.1| ≤ 1 ∧ |t.2.2.1| ≤ 1 ∧ |t.2.2.2| ≤ 1 := by
  obtain ⟨s1, hs1, he1⟩ := circle_close_form (le_trans (le_dist_c1 x c) hd)
  obtain ⟨s2, hs2, he2⟩ := circle_close_form (le_trans (le_dist_c2 x c) hd)
  obtain ⟨s3, hs3, he3⟩ := circle_close_form (le_trans (le_dist_c3 x c) hd)
  obtain ⟨s4, hs4, he4⟩ := circle_close_form (le_trans (le_dist_c4 x c) hd)
  exact ⟨(s1, s2, s3, s4), Prod.ext he1 (Prod.ext he2 (Prod.ext he3 he4)), hs1, hs2, hs3, hs4⟩

/-- Shell entry: a `T⁴°`-point in chart form over a fixed point has `sqNorm ≥ 1/4`. -/
theorem quarter_le_sqNorm_of_mem {x c : TorusFour} {t : ℝ × ℝ × ℝ × ℝ}
    (hx : x ∈ puncturedTorus) (hcf : c ∈ fixedSet) (heq : x = centeredChartParam c t) :
    1 / 4 ≤ sqNorm t := by
  by_contra h
  have h : sqNorm t < 1 / 4 := lt_of_not_ge h
  have hball : x ∈ chartBall c := by
    refine ⟨t, ?_, heq.symm⟩
    rw [Set.mem_setOf_eq, show excisionRadius = (1 : ℝ) / 2 from rfl]
    linarith
  exact hx (Set.mem_iUnion₂.mpr ⟨c, hcf, hball⟩)

/-! ## §5. The interval trig bound for the self-protected move -/

/-- `√2/2 > 1/4`. -/
theorem sqrt_two_div_two_gt : (1 : ℝ) / 4 < Real.sqrt 2 / 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- **The interval bound**: along the straight angle path from `|θ₀|` to `π/2`, both half-angle
`sin` and `cos` stay `> 1/4` when they do at `θ₀` (monotonicity toward the `π/2` maximum). -/
theorem chords_interval {θ₀ : ℝ} (hθ0 : 0 ≤ θ₀) (hθπ : θ₀ ≤ Real.pi)
    (hs : 1 / 4 < Real.sin (θ₀ / 2)) (hc : 1 / 4 < Real.cos (θ₀ / 2))
    {φ : ℝ} (hφlo : min θ₀ (Real.pi / 2) ≤ φ) (hφhi : φ ≤ max θ₀ (Real.pi / 2)) :
    1 / 4 < Real.sin (φ / 2) ∧ 1 / 4 < Real.cos (φ / 2) := by
  have hpipos := Real.pi_pos
  have hφ0 : 0 ≤ φ := le_trans (le_min hθ0 (by positivity)) hφlo
  have hφπ : φ ≤ Real.pi := le_trans hφhi (max_le hθπ (by linarith))
  constructor
  · -- sin: monotone up from the lower endpoint
    have hmono : Real.sin (min θ₀ (Real.pi / 2) / 2) ≤ Real.sin (φ / 2) := by
      have hmem1 : min θ₀ (Real.pi / 2) / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor
        · have : 0 ≤ min θ₀ (Real.pi / 2) := le_min hθ0 (by positivity)
          linarith
        · have : min θ₀ (Real.pi / 2) ≤ Real.pi / 2 := min_le_right _ _
          linarith
      have hmem2 : φ / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor
        · linarith
        · have : φ ≤ max θ₀ (Real.pi / 2) := hφhi
          rcases max_cases θ₀ (Real.pi / 2) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at this
          · -- max = θ₀: φ ≤ θ₀; but also need φ/2 ≤ π/2, from φ ≤ π
            linarith
          · linarith
      exact Real.strictMonoOn_sin.monotoneOn hmem1 hmem2 (by linarith)
    rcases min_cases θ₀ (Real.pi / 2) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hmono
    · linarith
    · have : Real.sin (Real.pi / 2 / 2) = Real.sqrt 2 / 2 := by
        rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four]
      rw [this] at hmono
      linarith [sqrt_two_div_two_gt]
  · -- cos: antitone down to the upper endpoint
    have hanti : Real.cos (max θ₀ (Real.pi / 2) / 2) ≤ Real.cos (φ / 2) := by
      have hmem1 : φ / 2 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
      have hmem2 : max θ₀ (Real.pi / 2) / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor
        · have : 0 ≤ max θ₀ (Real.pi / 2) := le_trans (by positivity) (le_max_right _ _)
          linarith
        · have : max θ₀ (Real.pi / 2) ≤ Real.pi := max_le hθπ (by linarith)
          linarith
      exact Real.strictAntiOn_cos.antitoneOn hmem1 hmem2 (by linarith)
    rcases max_cases θ₀ (Real.pi / 2) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hanti
    · linarith
    · have : Real.cos (Real.pi / 2 / 2) = Real.sqrt 2 / 2 := by
        rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four]
      rw [this] at hanti
      linarith [sqrt_two_div_two_gt]

/-! ## §6. The path bricks -/

/-- The affine real path from `p` to `q`, as a function of `unitInterval`. -/
def aff (p q : ℝ) (u : unitInterval) : ℝ := (1 - (u : ℝ)) * p + (u : ℝ) * q

theorem aff_continuous (p q : ℝ) : Continuous (aff p q) := by
  unfold aff; fun_prop

@[simp] theorem aff_zero (p q : ℝ) : aff p q 0 = p := by simp [aff]

@[simp] theorem aff_one (p q : ℝ) : aff p q 1 = q := by simp [aff]

/-- **Hub move**: with a `±i`-type fourth coordinate as certificate, the first three coordinates
travel simultaneously to `i`. -/
theorem joined_first_three (x : TorusFour) (h4 : FarCoord x.2.2.2) :
    JoinedIn puncturedTorus x (circleI, circleI, circleI, x.2.2.2) := by
  refine ⟨{
    toFun := fun u => (Circle.exp (aff (↑x.1 : ℂ).arg (Real.pi / 2) u),
      Circle.exp (aff (↑x.2.1 : ℂ).arg (Real.pi / 2) u),
      Circle.exp (aff (↑x.2.2.1 : ℂ).arg (Real.pi / 2) u), x.2.2.2)
    continuous_toFun := by
      refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)) <;>
        first
          | exact Circle.exp.continuous.comp (aff_continuous _ _)
          | exact continuous_const
    source' := by
      simp only [aff_zero]
      exact Prod.ext (Circle.exp_arg x.1) (Prod.ext (Circle.exp_arg x.2.1)
        (Prod.ext (Circle.exp_arg x.2.2.1) rfl))
    target' := by
      simp only [aff_one, exp_pi_div_two] }, ?_⟩
  intro u
  exact mem_of_far₄ h4

/-- **The `−i → i` bridge** for the fourth coordinate, protected by the first coordinate `i`. -/
theorem joined_bridge :
    JoinedIn puncturedTorus (circleI, circleI, circleI, negOne * circleI)
      (circleI, circleI, circleI, circleI) := by
  refine ⟨{
    toFun := fun u => (circleI, circleI, circleI,
      Circle.exp (aff (-(Real.pi / 2)) (Real.pi / 2) u))
    continuous_toFun := by
      refine Continuous.prodMk continuous_const (Continuous.prodMk continuous_const
        (Continuous.prodMk continuous_const ?_))
      exact Circle.exp.continuous.comp (aff_continuous _ _)
    source' := by simp only [aff_zero, exp_neg_pi_div_two]
    target' := by simp only [aff_one, exp_pi_div_two] }, ?_⟩
  intro u
  exact mem_of_far₁ farCoord_circleI

/-- **The protected fourth-coordinate move**: with one of the first three coordinates far, the
fourth coordinate travels freely to `i`. -/
theorem joined_move4 (x : TorusFour)
    (hfar : FarCoord x.1 ∨ FarCoord x.2.1 ∨ FarCoord x.2.2.1) :
    JoinedIn puncturedTorus x (x.1, x.2.1, x.2.2.1, circleI) := by
  refine ⟨{
    toFun := fun u => (x.1, x.2.1, x.2.2.1,
      Circle.exp (aff (↑x.2.2.2 : ℂ).arg (Real.pi / 2) u))
    continuous_toFun := by
      refine Continuous.prodMk continuous_const (Continuous.prodMk continuous_const
        (Continuous.prodMk continuous_const ?_))
      exact Circle.exp.continuous.comp (aff_continuous _ _)
    source' := by
      simp only [aff_zero]
      exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Circle.exp_arg x.2.2.2)))
    target' := by simp only [aff_one, exp_pi_div_two] }, ?_⟩
  intro u
  rcases hfar with h | h | h
  · exact mem_of_far₁ h
  · exact mem_of_far₂ h
  · exact mem_of_far₃ h

/-- **The self-protected fourth-coordinate move**: a fourth coordinate `a·exp θ₀` (pole
`a ∈ {1, negOne}`) whose half-angle `sin`/`cos` both exceed `1/4` travels to a `±i` value along
the straight angle path, protected by its own chords throughout. -/
theorem joined_own4 (x : TorusFour) (a : Circle) (ha : a = 1 ∨ a = negOne) (θ₀ : ℝ)
    (hx4 : x.2.2.2 = a * Circle.exp θ₀) (hθπ : |θ₀| ≤ Real.pi)
    (hs : 1 / 4 < |Real.sin (θ₀ / 2)|) (hc : 1 / 4 < |Real.cos (θ₀ / 2)|) :
    ∃ z4 : Circle, (z4 = circleI ∨ z4 = negOne * circleI) ∧
      JoinedIn puncturedTorus x (x.1, x.2.1, x.2.2.1, z4) := by
  have hpipos := Real.pi_pos
  -- the sign of the move
  set ε : ℝ := if θ₀ < 0 then -1 else 1 with hε
  have hε1 : ε = 1 ∨ ε = -1 := by
    rw [hε]; split <;> simp
  -- the absolute-value form of the path angle
  have habs : ∀ u : unitInterval, |aff θ₀ (ε * (Real.pi / 2)) u|
      = (1 - (u : ℝ)) * |θ₀| + (u : ℝ) * (Real.pi / 2) := by
    intro u
    have hu0 : (0 : ℝ) ≤ u := u.2.1
    have hu1 : (u : ℝ) ≤ 1 := u.2.2
    rw [hε]
    split
    · next hneg =>
        have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
        rw [aff, abs_of_nonpos (by nlinarith [le_of_lt hneg]), abs_of_neg hneg]
        ring
    · next hpos =>
        rw [not_lt] at hpos
        have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
        rw [aff, abs_of_nonneg (by nlinarith [hpos]), abs_of_nonneg hpos]
        ring
  -- the endpoint
  refine ⟨a * Circle.exp (ε * (Real.pi / 2)), ?_, ?_⟩
  · rcases hε1 with he | he <;> rw [he] <;> rcases ha with hae | hae <;> rw [hae]
    · rw [one_mul, one_mul, exp_pi_div_two]; exact Or.inl rfl
    · rw [one_mul, exp_pi_div_two]; exact Or.inr rfl
    · rw [one_mul, show (-1 : ℝ) * (Real.pi / 2) = -(Real.pi / 2) by ring,
        exp_neg_pi_div_two]
      exact Or.inr rfl
    · rw [show (-1 : ℝ) * (Real.pi / 2) = -(Real.pi / 2) by ring, exp_neg_pi_div_two,
        ← mul_assoc, negOne_mul_negOne, one_mul]
      exact Or.inl rfl
  · refine ⟨{
      toFun := fun u => (x.1, x.2.1, x.2.2.1,
        a * Circle.exp (aff θ₀ (ε * (Real.pi / 2)) u))
      continuous_toFun := by
        refine Continuous.prodMk continuous_const (Continuous.prodMk continuous_const
          (Continuous.prodMk continuous_const ?_))
        exact continuous_const.mul (Circle.exp.continuous.comp (aff_continuous _ _))
      source' := by
        simp only [aff_zero]
        exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hx4.symm))
      target' := by simp only [aff_one] }, ?_⟩
    intro u
    have hu0 : (0 : ℝ) ≤ u := u.2.1
    have hu1 : (u : ℝ) ≤ 1 := u.2.2
    set φ : ℝ := aff θ₀ (ε * (Real.pi / 2)) u with hφ
    -- interval bounds on |φ|
    have habsu := habs u
    rw [← hφ] at habsu
    have hlo : min |θ₀| (Real.pi / 2) ≤ |φ| := by
      rcases le_total |θ₀| (Real.pi / 2) with hle | hle
      · rw [min_eq_left hle, habsu]; nlinarith
      · rw [min_eq_right hle, habsu]; nlinarith
    have hhi : |φ| ≤ max |θ₀| (Real.pi / 2) := by
      rcases le_total |θ₀| (Real.pi / 2) with hle | hle
      · rw [max_eq_right hle, habsu]; nlinarith
      · rw [max_eq_left hle, habsu]; nlinarith
    -- half-angle sin/cos of |θ₀| coincide with the abs values at θ₀
    have hθabs := abs_le.mp hθπ
    have hsin0 : Real.sin (|θ₀| / 2) = |Real.sin (θ₀ / 2)| := by
      rcases le_total 0 θ₀ with h0 | h0
      · rw [abs_of_nonneg h0, abs_of_nonneg
          (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθabs.2]))]
      · have hnn : 0 ≤ Real.sin (-θ₀ / 2) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθabs.1])
        rw [abs_of_nonpos h0, show θ₀ / 2 = -(-θ₀ / 2) by ring, Real.sin_neg, abs_neg,
          abs_of_nonneg hnn]
    have hcos0 : Real.cos (|θ₀| / 2) = |Real.cos (θ₀ / 2)| := by
      have hcnn : 0 ≤ Real.cos (θ₀ / 2) := by
        apply Real.cos_nonneg_of_mem_Icc
        constructor
        · linarith [hθabs.1]
        · linarith [hθabs.2]
      rcases le_total 0 θ₀ with h0 | h0
      · rw [abs_of_nonneg h0, abs_of_nonneg hcnn]
      · have h' : 0 ≤ Real.cos (-θ₀ / 2) := by
          rw [show -θ₀ / 2 = -(θ₀ / 2) by ring, Real.cos_neg]
          exact hcnn
        rw [abs_of_nonpos h0, show θ₀ / 2 = -(-θ₀ / 2) by ring, Real.cos_neg,
          abs_of_nonneg h']
    -- interval trig bounds at |φ|
    have hint := chords_interval (θ₀ := |θ₀|) (abs_nonneg θ₀) hθπ
      (by rw [hsin0]; exact hs) (by rw [hcos0]; exact hc) hlo hhi
    -- convert to chords at φ
    have hsinφ : 1 / 4 < |Real.sin (φ / 2)| := by
      have : Real.sin (|φ| / 2) ≤ |Real.sin (φ / 2)| := by
        rcases le_total 0 φ with h0 | h0
        · rw [abs_of_nonneg h0]; exact le_abs_self _
        · rw [abs_of_nonpos h0, show -φ / 2 = -(φ / 2) by ring, Real.sin_neg]
          calc -Real.sin (φ / 2) ≤ |(-Real.sin (φ / 2))| := le_abs_self _
            _ = |Real.sin (φ / 2)| := abs_neg _
      linarith [hint.1]
    have hcosφ : 1 / 4 < |Real.cos (φ / 2)| := by
      have : Real.cos (|φ| / 2) ≤ |Real.cos (φ / 2)| := by
        rcases le_total 0 φ with h0 | h0
        · rw [abs_of_nonneg h0]; exact le_abs_self _
        · rw [abs_of_nonpos h0, show -φ / 2 = -(φ / 2) by ring, Real.cos_neg]
          exact le_abs_self _
      linarith [hint.2]
    -- the far certificate at the fourth coordinate
    refine mem_of_far₄ ?_
    show FarCoord (a * Circle.exp φ)
    have hd1 : dist (a * Circle.exp φ) a = 2 * |Real.sin (φ / 2)| := dist_mul_exp_self a φ
    have hd2 : dist (a * Circle.exp φ) (negOne * a) = 2 * |Real.cos (φ / 2)| :=
      dist_mul_exp_negMul a φ
    rcases ha with hae | hae
    · constructor
      · rw [show (1 : Circle) = a from hae.symm, hd1]; linarith
      · rw [show (negOne : Circle) = negOne * a by rw [hae, mul_one], hd2]; linarith
    · constructor
      · rw [show (1 : Circle) = negOne * a by rw [hae, negOne_mul_negOne], hd2]; linarith
      · rw [show (negOne : Circle) = a from hae.symm, hd1]; linarith

/-- **The in-chart escape**: from a chart point over a fixed point (all angles `≤ 1`,
`sqNorm ≥ 1/4`), the fourth chart angle travels to `±7/5`, staying in the shell throughout. -/
theorem joined_escape {c : TorusFour} (hcf : c ∈ fixedSet) {t : ℝ × ℝ × ℝ × ℝ}
    (h1 : |t.1| ≤ 1) (h2 : |t.2.1| ≤ 1) (h3 : |t.2.2.1| ≤ 1) (h4 : |t.2.2.2| ≤ 1)
    (hlo : 1 / 4 ≤ sqNorm t) :
    ∃ s : ℝ, (s = 7 / 5 ∨ s = -(7 / 5)) ∧
      JoinedIn puncturedTorus (centeredChartParam c t)
        (centeredChartParam c (t.1, t.2.1, t.2.2.1, s)) := by
  set s : ℝ := if t.2.2.2 < 0 then -(7 / 5) else 7 / 5 with hsdef
  have hscases : s = 7 / 5 ∨ s = -(7 / 5) := by
    rw [hsdef]; split <;> simp
  refine ⟨s, hscases, ?_⟩
  refine ⟨{
    toFun := fun u => centeredChartParam c (t.1, t.2.1, t.2.2.1, aff t.2.2.2 s u)
    continuous_toFun := by
      refine (continuous_centeredChartParam c).comp ?_
      exact (continuous_const.prodMk (continuous_const.prodMk
        (continuous_const.prodMk (aff_continuous _ _))))
    source' := by
      simp only [aff_zero]
    target' := by
      simp only [aff_one] }, ?_⟩
  intro u
  have hu0 : (0 : ℝ) ≤ u := u.2.1
  have hu1 : (u : ℝ) ≤ 1 := u.2.2
  set θ : ℝ := aff t.2.2.2 s u with hθ
  -- the moving angle grows in absolute value and stays `≤ 7/5`
  have habs4 := abs_le.mp h4
  have hθval : θ = (1 - (u : ℝ)) * t.2.2.2 + (u : ℝ) * s := by rw [hθ, aff]
  have hθsq : t.2.2.2 ^ 2 ≤ θ ^ 2 := by
    rw [hθval, hsdef]
    split
    · next hneg =>
        -- θ ≤ t₄ < 0
        have hle : (1 - (u : ℝ)) * t.2.2.2 + (u : ℝ) * -(7 / 5) ≤ t.2.2.2 := by nlinarith
        nlinarith [hle, le_of_lt hneg]
    · next hpos =>
        rw [not_lt] at hpos
        -- t₄ ≤ θ, 0 ≤ t₄
        have hle : t.2.2.2 ≤ (1 - (u : ℝ)) * t.2.2.2 + (u : ℝ) * (7 / 5) := by nlinarith
        nlinarith [hle, hpos]
  have hθle : |θ| ≤ 7 / 5 := by
    rw [hθval, hsdef]
    split
    · next hneg =>
        rw [abs_of_nonpos (by nlinarith [le_of_lt hneg])]
        nlinarith
    · next hpos =>
        rw [not_lt] at hpos
        rw [abs_of_nonneg (by nlinarith [hpos])]
        nlinarith
  have hgoal : centeredChartParam c (t.1, t.2.1, t.2.2.1, θ) ∈ puncturedTorus := by
    refine shell_mem_puncturedTorus hcf (t := (t.1, t.2.1, t.2.2.1, θ))
      (by simpa using le_trans h1 (by norm_num))
      (by simpa using le_trans h2 (by norm_num))
      (by simpa using le_trans h3 (by norm_num))
      (by simpa using hθle) ?_
    show 1 / 4 ≤ sqNorm (t.1, t.2.1, t.2.2.1, θ)
    simp only [sqNorm] at hlo ⊢
    nlinarith [hθsq]
  exact hgoal

/-! ## §7. Assembly -/

/-- The chord form of the far predicate at a pole `a ∈ {1, negOne}`. -/
theorem farCoord_iff_chords (a : Circle) (ha : a = 1 ∨ a = negOne) (θ : ℝ) :
    FarCoord (a * Circle.exp θ)
      ↔ 1 / 4 < |Real.sin (θ / 2)| ∧ 1 / 4 < |Real.cos (θ / 2)| := by
  have hd1 : dist (a * Circle.exp θ) a = 2 * |Real.sin (θ / 2)| := dist_mul_exp_self a θ
  have hd2 : dist (a * Circle.exp θ) (negOne * a) = 2 * |Real.cos (θ / 2)| :=
    dist_mul_exp_negMul a θ
  rcases ha with hae | hae
  · subst hae
    rw [FarCoord, show (negOne : Circle) = negOne * 1 by rw [mul_one]]
    rw [show ((1 : Circle)) = (1 : Circle) from rfl] at hd1
    constructor
    · rintro ⟨hx, hy⟩
      rw [hd1] at hx
      rw [hd2] at hy
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hx, hy⟩
      rw [hd1, hd2]
      exact ⟨by linarith, by linarith⟩
  · subst hae
    rw [FarCoord, show ((1 : Circle)) = negOne * negOne by rw [negOne_mul_negOne]]
    constructor
    · rintro ⟨hx, hy⟩
      rw [hd2] at hx
      rw [hd1] at hy
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hx, hy⟩
      rw [hd2, hd1]
      exact ⟨by linarith, by linarith⟩

/-- Trig facts at the escape angle `7/5`: both half-angle chords exceed `1/4`. -/
theorem chords_at_escape :
    1 / 4 < |Real.sin ((7 / 5 : ℝ) / 2)| ∧ 1 / 4 < |Real.cos ((7 / 5 : ℝ) / 2)| := by
  have hpi4 := Real.pi_le_four
  have hpipos := Real.pi_pos
  constructor
  · have hjordan : 2 / Real.pi * (7 / 10) ≤ Real.sin (7 / 10) :=
      Real.mul_le_sin (by norm_num) (by nlinarith [Real.pi_gt_three])
    have h1 : (1 : ℝ) / 4 < 2 / Real.pi * (7 / 10) := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hpipos]
      nlinarith
    have : (1 : ℝ) / 4 < Real.sin (7 / 10) := by linarith
    calc (1 : ℝ) / 4 < Real.sin (7 / 10) := this
      _ ≤ |Real.sin ((7 / 5 : ℝ) / 2)| := by
          rw [show (7 / 5 : ℝ) / 2 = 7 / 10 by norm_num]
          exact le_abs_self _
  · have hcos : (1 : ℝ) - (7 / 10) ^ 2 / 2 ≤ Real.cos (7 / 10) :=
      Real.one_sub_sq_div_two_le_cos
    have : (1 : ℝ) / 4 < Real.cos (7 / 10) := by nlinarith
    calc (1 : ℝ) / 4 < Real.cos (7 / 10) := this
      _ ≤ |Real.cos ((7 / 5 : ℝ) / 2)| := by
          rw [show (7 / 5 : ℝ) / 2 = 7 / 10 by norm_num]
          exact le_abs_self _

/-- The escape angle is `≤ π` in absolute value. -/
theorem escape_le_pi : |(7 / 5 : ℝ)| ≤ Real.pi := by
  rw [abs_of_nonneg (by norm_num)]
  nlinarith [Real.pi_gt_three]

/-- **Every `T⁴°`-point joins the all-`i` witness.** -/
theorem joinedIn_allI {x : TorusFour} (hx : x ∈ puncturedTorus) :
    JoinedIn puncturedTorus x (circleI, circleI, circleI, circleI) := by
  -- Reduction: reach any point whose fourth coordinate is `±i`.
  suffices h : ∃ y : TorusFour, JoinedIn puncturedTorus x y ∧
      (y.2.2.2 = circleI ∨ y.2.2.2 = negOne * circleI) by
    obtain ⟨y, hxy, hy4⟩ := h
    have hfar4 : FarCoord y.2.2.2 := by
      rcases hy4 with h4 | h4 <;> rw [h4]
      · exact farCoord_circleI
      · exact farCoord_negI
    have hhub := joined_first_three y hfar4
    rcases hy4 with h4 | h4
    · rw [h4] at hhub
      exact hxy.trans hhub
    · rw [h4] at hhub
      exact (hxy.trans hhub).trans joined_bridge
  -- Case split on the far coordinates.
  by_cases hf1 : FarCoord x.1
  · exact ⟨(x.1, x.2.1, x.2.2.1, circleI), joined_move4 x (Or.inl hf1), Or.inl rfl⟩
  by_cases hf2 : FarCoord x.2.1
  · exact ⟨(x.1, x.2.1, x.2.2.1, circleI), joined_move4 x (Or.inr (Or.inl hf2)), Or.inl rfl⟩
  by_cases hf3 : FarCoord x.2.2.1
  · exact ⟨(x.1, x.2.1, x.2.2.1, circleI),
      joined_move4 x (Or.inr (Or.inr hf3)), Or.inl rfl⟩
  by_cases hf4 : FarCoord x.2.2.2
  · -- self-protected move at pole `1`
    have hx4 : x.2.2.2 = 1 * Circle.exp ((↑x.2.2.2 : ℂ).arg) := by
      rw [one_mul, Circle.exp_arg]
    have hθπ : |(↑x.2.2.2 : ℂ).arg| ≤ Real.pi :=
      abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
    have hchords := (farCoord_iff_chords 1 (Or.inl rfl) ((↑x.2.2.2 : ℂ).arg)).mp
      (by rw [← hx4]; exact hf4)
    obtain ⟨z4, hz4, hjoin⟩ := joined_own4 x 1 (Or.inl rfl) _ hx4 hθπ hchords.1 hchords.2
    exact ⟨(x.1, x.2.1, x.2.2.1, z4), hjoin, hz4⟩
  · -- no far coordinate: extract chart coordinates at the nearest fixed point and escape
    have hnear : ∀ z : Circle, ¬FarCoord z → (dist z 1 ≤ 1 / 2 ∨ dist z negOne ≤ 1 / 2) := by
      intro z hz
      rw [FarCoord, not_and_or, not_lt, not_lt] at hz
      exact hz
    -- the nearest-pole fixed point
    set c1 : Circle := if dist x.1 1 ≤ 1 / 2 then 1 else negOne with hc1
    set c2 : Circle := if dist x.2.1 1 ≤ 1 / 2 then 1 else negOne with hc2
    set c3 : Circle := if dist x.2.2.1 1 ≤ 1 / 2 then 1 else negOne with hc3
    set c4 : Circle := if dist x.2.2.2 1 ≤ 1 / 2 then 1 else negOne with hc4
    have hpole : ∀ (z : Circle) (w : Circle), ¬FarCoord z →
        w = (if dist z 1 ≤ 1 / 2 then (1 : Circle) else negOne) →
        dist z w ≤ 1 / 2 ∧ (w = 1 ∨ w = negOne) := by
      intro z w hz hw
      rcases hnear z hz with hd | hd
      · rw [hw, if_pos hd]
        exact ⟨hd, Or.inl rfl⟩
      · by_cases hd1 : dist z 1 ≤ 1 / 2
        · rw [hw, if_pos hd1]
          exact ⟨hd1, Or.inl rfl⟩
        · rw [hw, if_neg hd1]
          exact ⟨hd, Or.inr rfl⟩
    obtain ⟨hd1, hp1⟩ := hpole x.1 c1 hf1 hc1
    obtain ⟨hd2, hp2⟩ := hpole x.2.1 c2 hf2 hc2
    obtain ⟨hd3, hp3⟩ := hpole x.2.2.1 c3 hf3 hc3
    obtain ⟨hd4, hp4⟩ := hpole x.2.2.2 c4 hf4 hc4
    set c : TorusFour := (c1, c2, c3, c4) with hcdef
    have hcf : c ∈ fixedSet := by
      show torusFourInvolution c = c
      exact (mem_fixedSet_iff c).mpr ⟨hp1, hp2, hp3, hp4⟩
    have hdc : dist x c ≤ 1 / 2 := by
      have : dist x c = max (dist x.1 c.1) (max (dist x.2.1 c.2.1)
          (max (dist x.2.2.1 c.2.2.1) (dist x.2.2.2 c.2.2.2))) := by
        rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
      rw [this]
      exact max_le hd1 (max_le hd2 (max_le hd3 hd4))
    obtain ⟨t, hteq, ht1, ht2, ht3, ht4⟩ := exists_chart_form hdc
    have hsq : 1 / 4 ≤ sqNorm t := quarter_le_sqNorm_of_mem hx hcf hteq
    obtain ⟨s, hscases, hesc⟩ := joined_escape hcf ht1 ht2 ht3 ht4 hsq
    rw [← hteq] at hesc
    -- the escaped point, with its fourth coordinate in pole-relative exp form
    set y : TorusFour := centeredChartParam c (t.1, t.2.1, t.2.2.1, s) with hydef
    have hy4 : y.2.2.2 = c4 * Circle.exp s := rfl
    have hsπ : |s| ≤ Real.pi := by
      rcases hscases with hse | hse <;> rw [hse]
      · exact escape_le_pi
      · rw [abs_neg]; exact escape_le_pi
    have hschords : 1 / 4 < |Real.sin (s / 2)| ∧ 1 / 4 < |Real.cos (s / 2)| := by
      rcases hscases with hse | hse <;> rw [hse]
      · exact chords_at_escape
      · rw [show -(7 / 5 : ℝ) / 2 = -((7 / 5 : ℝ) / 2) by ring, Real.sin_neg,
          Real.cos_neg, abs_neg]
        exact chords_at_escape
    obtain ⟨z4, hz4, hown⟩ := joined_own4 y c4 hp4 s hy4 hsπ hschords.1 hschords.2
    exact ⟨(y.1, y.2.1, y.2.2.1, z4), hesc.trans hown, hz4⟩

/-- **`T⁴°` is path-connected** (as a set). -/
theorem isPathConnected_puncturedTorus : IsPathConnected puncturedTorus := by
  have hW : ((circleI, circleI, circleI, circleI) : TorusFour) ∈ puncturedTorus :=
    mem_of_far₁ farCoord_circleI
  exact ⟨(circleI, circleI, circleI, circleI), hW, fun {y} hy => (joinedIn_allI hy).symm⟩

/-- **`↥T⁴°` is a path-connected space** — the degree-0 input of the `Q`-side Smith solve. -/
instance : PathConnectedSpace (↥puncturedTorus) :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_puncturedTorus

/-- **`Q = T⁴°/τ` is a path-connected space** — discharges the standing hypothesis of the banked
`KummerK7Opener.freeQuotient_pathConnected`. -/
instance : PathConnectedSpace FreeQuotient :=
  SKEFTHawking.KummerK7Opener.freeQuotient_pathConnected inferInstance

end

end SKEFTHawking.KummerPuncturedPathConn
