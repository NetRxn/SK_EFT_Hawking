import SKEFTHawking.TetradGapEquation

/-!
# Exact-real NJL roots and uncapped sign brackets

These results use the original scalar `gapIntegral`, `gapOperator`,
`reducedGapFn` and `criticalCoupling`. They do not identify that model with
microscopic ADW dynamics or certify the signs of a floating-point evaluator.
The physical UV cutoff is fixed while the mathematical gap varies.
-/

noncomputable section
open Set Filter
namespace SKEFTHawking.TetradGapEquation

/-- Cancellation of a strictly positive gap relates the actual fixed-point
equation to the actual scalar residual. Zero remains a separate fixed point. -/
theorem positive_fixed_iff_reduced_zero (G N Λ d : ℝ) (hd : 0 < d) :
    gapOperator G N Λ d = d ↔ reducedGapFn G N Λ d = 0 := by
  unfold gapOperator reducedGapFn
  constructor
  · intro h
    have hm : (G * N * gapIntegral d Λ - 1) * d = 0 := by nlinarith [h]
    exact (mul_eq_zero.mp hm).resolve_right (ne_of_gt hd)
  · intro h
    nlinarith [h]

/-- Strict decrease is derived from the existing integral theorem, rather
than supplied as a numerical solver hypothesis. -/
theorem reducedGapFn_strictAntiOn (G N Λ : ℝ)
    (hG : 0 < G) (hN : 0 < N) (hΛ : 0 < Λ) :
    StrictAntiOn (reducedGapFn G N Λ) (Ici 0) := by
  intro x hx y hy hxy
  unfold reducedGapFn
  exact sub_lt_sub_right
    (mul_lt_mul_of_pos_left (gapIntegral_strictAnti x y Λ hx hy hΛ hxy)
      (mul_pos hG hN)) 1

/-- Every positive fixed point is unique, including when it equals or
exceeds the cutoff. -/
theorem positive_fixed_unique (G N Λ x y : ℝ)
    (hG : 0 < G) (hN : 0 < N) (hΛ : 0 < Λ)
    (hx : 0 < x) (hy : 0 < y)
    (hfx : gapOperator G N Λ x = x) (hfy : gapOperator G N Λ y = y) :
    x = y := by
  apply (reducedGapFn_strictAntiOn G N Λ hG hN hΛ).injOn hx.le hy.le
  rw [(positive_fixed_iff_reduced_zero G N Λ x hx).mp hfx,
    (positive_fixed_iff_reduced_zero G N Λ y hy).mp hfy]

/-- The critical endpoint has no positive root; it is included here rather
than inferred from the older strictly-subcritical theorem. -/
theorem no_positive_fixed_at_or_below_critical (G N Λ : ℝ)
    (hG : 0 < G) (hN : 0 < N) (hΛ : 0 < Λ)
    (hGc : G ≤ criticalCoupling Λ N) :
    ¬ ∃ d, 0 < d ∧ gapOperator G N Λ d = d := by
  rintro ⟨d, hd, hfix⟩
  have hzero : reducedGapFn G N Λ 0 ≤ 0 := by
    rw [gap_vestigial_connection G N Λ hG hN hΛ]
    have := (div_le_one₀ (criticalCoupling_pos Λ N hΛ hN)).mpr hGc
    linarith
  have hdec := reducedGapFn_strictAntiOn G N Λ hG hN hΛ
    (show (0 : ℝ) ∈ Ici 0 from by simp) hd.le hd
  rw [(positive_fixed_iff_reduced_zero G N Λ d hd).mp hfix] at hdec
  linarith

/-- The actual supercritical model has exactly one positive fixed point. -/
theorem existsUnique_positive_fixed (G N Λ : ℝ)
    (hG : 0 < G) (hN : 0 < N) (hΛ : 0 < Λ)
    (hGc : criticalCoupling Λ N < G) :
    ∃! d, 0 < d ∧ gapOperator G N Λ d = d := by
  obtain ⟨d, hd, hfix⟩ := gap_nontrivial_exists G N Λ hG hN hΛ hGc
  refine ⟨d, ⟨hd, hfix⟩, ?_⟩
  intro y hy
  exact positive_fixed_unique G N Λ y d hG hN hΛ hy.1 hd hy.2 hfix

/-- The coupling at which the positive gap reaches the fixed UV cutoff. -/
def cutoffCoupling (Λ N : ℝ) : ℝ := 1 / (N * gapIntegral Λ Λ)

theorem cutoffCoupling_pos (Λ N : ℝ) (hΛ : 0 < Λ) (hN : 0 < N) :
    0 < cutoffCoupling Λ N := by
  exact one_div_pos.mpr (mul_pos hN (gapIntegral_pos Λ Λ hΛ.le hΛ))

/-- Exact cutoff evaluation; the logarithmic term is retained. -/
theorem gapIntegral_at_cutoff (Λ : ℝ) (hΛ : 0 < Λ) :
    gapIntegral Λ Λ = gapIntegral 0 Λ * (1 - Real.log 2) := by
  unfold gapIntegral
  rw [if_neg (ne_of_gt hΛ), if_pos rfl, div_self (pow_ne_zero 2 (ne_of_gt hΛ))]
  norm_num
  ring

theorem one_sub_log_two_pos : 0 < 1 - Real.log (2 : ℝ) := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)
  linarith

theorem cutoffCoupling_eq_critical_div (Λ N : ℝ) (hΛ : 0 < Λ) :
    cutoffCoupling Λ N = criticalCoupling Λ N / (1 - Real.log 2) := by
  unfold cutoffCoupling criticalCoupling
  rw [gapIntegral_at_cutoff Λ hΛ]
  rw [div_div, mul_assoc]

theorem critical_lt_cutoffCoupling (Λ N : ℝ) (hΛ : 0 < Λ) (hN : 0 < N) :
    criticalCoupling Λ N < cutoffCoupling Λ N := by
  unfold criticalCoupling cutoffCoupling
  apply one_div_lt_one_div_of_lt
    (mul_pos hN (gapIntegral_pos Λ Λ hΛ.le hΛ))
  exact mul_lt_mul_of_pos_left
    (gapIntegral_strictAnti 0 Λ Λ (le_refl 0) hΛ.le hΛ hΛ) hN

/-- Equality at the cutoff gives a genuine positive fixed point. -/
theorem cutoff_is_fixed (Λ N : ℝ) (hΛ : 0 < Λ) (hN : 0 < N) :
    gapOperator (cutoffCoupling Λ N) N Λ Λ = Λ := by
  unfold gapOperator cutoffCoupling
  have hI := (gapIntegral_pos Λ Λ hΛ.le hΛ).ne'
  field_simp

theorem positive_fixed_above_cutoff (G N Λ d : ℝ)
    (hG : 0 < G) (hN : 0 < N) (hΛ : 0 < Λ) (hd : 0 < d)
    (hfix : gapOperator G N Λ d = d) (hcut : cutoffCoupling Λ N < G) :
    Λ < d := by
  exact gap_solution_monotone (cutoffCoupling Λ N) G N Λ Λ d
    (cutoffCoupling_pos Λ N hΛ hN) hG hN hΛ hΛ hd
    (cutoff_is_fixed Λ N hΛ hN) hfix hcut

theorem positive_fixed_below_cutoff (G N Λ d : ℝ)
    (hG : 0 < G) (hN : 0 < N) (hΛ : 0 < Λ) (hd : 0 < d)
    (hfix : gapOperator G N Λ d = d) (hcut : G < cutoffCoupling Λ N) :
    d < Λ := by
  exact gap_solution_monotone G (cutoffCoupling Λ N) N Λ d Λ hG
    (cutoffCoupling_pos Λ N hΛ hN) hN hΛ hd hΛ hfix
    (cutoff_is_fixed Λ N hΛ hN) hcut

/-- The cutoff and coupling trichotomies agree for every positive fixed point. -/
theorem positive_fixed_cutoff_trichotomy (G N Λ d : ℝ)
    (hG : 0 < G) (hN : 0 < N) (hΛ : 0 < Λ) (hd : 0 < d)
    (hfix : gapOperator G N Λ d = d) :
    (d < Λ ↔ G < cutoffCoupling Λ N) ∧
    (d = Λ ↔ G = cutoffCoupling Λ N) ∧
    (Λ < d ↔ cutoffCoupling Λ N < G) := by
  have heq : G = cutoffCoupling Λ N → d = Λ := by
    intro h
    subst G
    exact positive_fixed_unique _ N Λ d Λ
      (cutoffCoupling_pos Λ N hΛ hN) hN hΛ hd hΛ hfix (cutoff_is_fixed Λ N hΛ hN)
  have hlo := positive_fixed_below_cutoff G N Λ d hG hN hΛ hd hfix
  have hhi := positive_fixed_above_cutoff G N Λ d hG hN hΛ hd hfix
  rcases lt_trichotomy G (cutoffCoupling Λ N) with h | h | h
  · have := hlo h
    constructor
    · exact ⟨fun _ => h, fun _ => this⟩
    · constructor <;> constructor <;> intro hbad <;> linarith
  · have := heq h
    constructor
    · constructor <;> intro hbad <;> linarith
    · constructor
      · exact ⟨fun _ => h, fun _ => this⟩
      · constructor <;> intro hbad <;> linarith
  · have := hhi h
    constructor
    · constructor <;> intro hbad <;> linarith
    · constructor
      · constructor <;> intro hbad <;> linarith
      · exact ⟨fun _ => h, fun _ => this⟩

/-- Closed residual signs, including equality at either endpoint. -/
def IsNJLBracket (G N Λ : ℝ) (p : ℝ × ℝ) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ 0 ≤ reducedGapFn G N Λ p.1 ∧
    reducedGapFn G N Λ p.2 ≤ 0

theorem positive_fixed_mem_bracket (G N Λ d : ℝ) (p : ℝ × ℝ)
    (hG : 0 < G) (hN : 0 < N) (hΛ : 0 < Λ) (hd : 0 < d)
    (hfix : gapOperator G N Λ d = d) (hp : IsNJLBracket G N Λ p) :
    p.1 ≤ d ∧ d ≤ p.2 := by
  have hz := (positive_fixed_iff_reduced_zero G N Λ d hd).mp hfix
  have hanti := reducedGapFn_strictAntiOn G N Λ hG hN hΛ
  constructor
  · by_contra hn
    have hlt := hanti hd.le hp.1 (lt_of_not_ge hn)
    rw [hz] at hlt
    linarith [hp.2.2.1]
  · by_contra hn
    have hlt := hanti (hp.1.trans hp.2.1) hd.le (lt_of_not_ge hn)
    rw [hz] at hlt
    linarith [hp.2.2.2]

/-- Actual residual signs locate any nonnegative trial gap relative to the
unique positive root. This includes an exact zero at the trial point. -/
theorem reduced_sign_at_positive_fixed (G N Λ d x : ℝ)
    (hG : 0 < G) (hN : 0 < N) (hΛ : 0 < Λ) (hd : 0 < d) (hx : 0 ≤ x)
    (hfix : gapOperator G N Λ d = d) :
    (0 < reducedGapFn G N Λ x ↔ x < d) ∧
    (reducedGapFn G N Λ x = 0 ↔ x = d) ∧
    (reducedGapFn G N Λ x < 0 ↔ d < x) := by
  have hz := (positive_fixed_iff_reduced_zero G N Λ d hd).mp hfix
  have ha := reducedGapFn_strictAntiOn G N Λ hG hN hΛ
  rcases lt_trichotomy x d with h | h | h
  · have hs := ha hx hd.le h
    rw [hz] at hs
    constructor
    · exact ⟨fun _ => h, fun _ => hs⟩
    · constructor <;> constructor <;> intro hbad <;> linarith
  · subst x
    rw [hz]
    simp
  · have hs := ha hd.le hx h
    rw [hz] at hs
    constructor
    · constructor <;> intro hbad <;> linarith
    · constructor
      · constructor <;> intro hbad <;> linarith
      · exact ⟨fun _ => h, fun _ => hs⟩

/-- Exact-real bisection keeps an endpoint zero and halves the interval.
This is an explanatory sign algorithm, not the production log-coordinate solver. -/
def njlBisectStep (G N Λ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  let m := (p.1 + p.2) / 2
  if 0 ≤ reducedGapFn G N Λ m then (m, p.2) else (p.1, m)

theorem njlBisectStep_bracket (G N Λ : ℝ) (p : ℝ × ℝ)
    (hp : IsNJLBracket G N Λ p) :
    IsNJLBracket G N Λ (njlBisectStep G N Λ p) := by
  unfold njlBisectStep
  dsimp only
  split_ifs with hm
  · exact ⟨by linarith [hp.1, hp.2.1], by linarith [hp.2.1], hm, hp.2.2.2⟩
  · exact ⟨hp.1, by linarith [hp.2.1], hp.2.2.1, le_of_not_ge hm⟩

theorem njlBisectStep_width (G N Λ : ℝ) (p : ℝ × ℝ) :
    (njlBisectStep G N Λ p).2 - (njlBisectStep G N Λ p).1 = (p.2 - p.1) / 2 := by
  unfold njlBisectStep
  dsimp only
  split_ifs <;> dsimp <;> ring

def njlBisect (G N Λ : ℝ) (p : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => p
  | n + 1 => njlBisectStep G N Λ (njlBisect G N Λ p n)

theorem njlBisect_bracket (G N Λ : ℝ) (p : ℝ × ℝ)
    (hp : IsNJLBracket G N Λ p) (n : ℕ) :
    IsNJLBracket G N Λ (njlBisect G N Λ p n) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact njlBisectStep_bracket G N Λ _ ih

theorem njlBisect_width (G N Λ : ℝ) (p : ℝ × ℝ) (n : ℕ) :
    (njlBisect G N Λ p n).2 - (njlBisect G N Λ p n).1 =
      (p.2 - p.1) / (2 : ℝ) ^ n := by
  induction n with
  | zero => simp [njlBisect]
  | succ n ih =>
    rw [njlBisect, njlBisectStep_width, ih, pow_succ, div_mul_eq_div_div]

/-- The midpoint error follows from the actual retained sign bracket. -/
theorem njlBisect_midpoint_error (G N Λ d : ℝ) (p : ℝ × ℝ)
    (hG : 0 < G) (hN : 0 < N) (hΛ : 0 < Λ) (hd : 0 < d)
    (hfix : gapOperator G N Λ d = d) (hp : IsNJLBracket G N Λ p) (n : ℕ) :
    |((njlBisect G N Λ p n).1 + (njlBisect G N Λ p n).2) / 2 - d| ≤
      (p.2 - p.1) / (2 : ℝ) ^ (n + 1) := by
  have hb := positive_fixed_mem_bracket G N Λ d (njlBisect G N Λ p n)
    hG hN hΛ hd hfix (njlBisect_bracket G N Λ p hp n)
  have hw := njlBisect_width G N Λ p n
  rw [pow_succ, div_mul_eq_div_div]
  apply abs_le.mpr
  constructor <;> linarith

/-- A negative upper residual exists strictly beyond the fixed cutoff;
the cutoff itself is never presumed to bracket a supercritical root. -/
theorem exists_upper_bracket_beyond_cutoff (G N Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ b, Λ < b ∧ reducedGapFn G N Λ b < 0 := by
  have ht : Tendsto (fun d => G * N * gapIntegral d Λ) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (gapIntegral_tendsto_zero Λ hΛ)
  obtain ⟨b, hb, hg⟩ := ((eventually_gt_atTop Λ).and
    (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))).exists
  refine ⟨b, hb, ?_⟩
  unfold reducedGapFn
  linarith

/-- The actual supercritical model supplies a valid initial bracket with
upper endpoint strictly beyond the cutoff; no endpoint sign is stipulated. -/
theorem exists_supercritical_initial_bracket (G N Λ : ℝ)
    (hG : 0 < G) (hN : 0 < N) (hΛ : 0 < Λ)
    (hGc : criticalCoupling Λ N < G) :
    ∃ b, Λ < b ∧ IsNJLBracket G N Λ (0, b) := by
  obtain ⟨b, hb, hg⟩ := exists_upper_bracket_beyond_cutoff G N Λ hΛ
  have hzero : 0 < reducedGapFn G N Λ 0 := by
    rw [gap_vestigial_connection G N Λ hG hN hΛ]
    have := (one_lt_div₀ (criticalCoupling_pos Λ N hΛ hN)).mpr hGc
    linarith
  exact ⟨b, hb, le_refl 0, (hΛ.trans hb).le, hzero.le, hg.le⟩

end SKEFTHawking.TetradGapEquation
end
