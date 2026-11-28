import SKEFTHawking.FiniteGibbsResetScheduleDosePartition

/-! A fixed pair of reset baths generates a closed segment of channels at
fixed per-bath doses. An arbitrary schedule can be replaced by at most
three slices at those same doses. -/

namespace SKEFTHawking.FinitePositiveKernel.GibbsReset

variable {n : Type*} [Fintype n]

/-- The first and second bath attenuations and the coefficient of the
second target minus the first in the schedule's accumulated target. -/
noncomputable def twoBathCoefficients : List (Bool × ResetSlice n) → ℝ × ℝ × ℝ
  | [] => (1, 1, 0)
  | (bath, s) :: tail =>
    let (x, y, w) := twoBathCoefficients tail
    let u := Real.exp (-s.dose)
    if bath then (x, u * y, w + x * y * (1 - u)) else (u * x, y, w)

/-- The second bath's weight lies precisely between the outer block
coefficients, with attenuation in (0,1] for each bath. -/
theorem twoBathCoefficients_bounds (steps : List (Bool × ResetSlice n)) :
    let (x, y, w) := twoBathCoefficients steps
    0 < x ∧ x ≤ 1 ∧ 0 < y ∧ y ≤ 1 ∧ x * (1 - y) ≤ w ∧ w ≤ 1 - y := by
  induction steps with
  | nil => simp [twoBathCoefficients]
  | cons head tail ih =>
    obtain ⟨bath, s⟩ := head
    generalize hCoeff : twoBathCoefficients tail = coeff
    rw [hCoeff] at ih
    obtain ⟨x, y, w⟩ := coeff
    dsimp at ih
    obtain ⟨hx, hx1, hy, hy1, hlow, hhigh⟩ := ih
    let u := Real.exp (-s.dose)
    have hu : 0 < u := Real.exp_pos _
    have hu1 : u ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr
      (mul_nonneg s.rate_nonneg s.duration_nonneg))
    have hux : u * x ≤ x := mul_le_of_le_one_left hx.le hu1
    have huy : u * y ≤ y := mul_le_of_le_one_left hy.le hu1
    cases bath
    · simp only [twoBathCoefficients, hCoeff, Bool.false_eq_true, if_false]
      change 0 < u * x ∧ u * x ≤ 1 ∧ 0 < y ∧ y ≤ 1 ∧
        u * x * (1 - y) ≤ w ∧ w ≤ 1 - y
      exact ⟨mul_pos hu hx, hux.trans hx1, hy, hy1,
        (mul_le_mul_of_nonneg_right hux (sub_nonneg.mpr hy1)).trans hlow, hhigh⟩
    · simp only [twoBathCoefficients, hCoeff, if_true]
      change 0 < x ∧ x ≤ 1 ∧ 0 < u * y ∧ u * y ≤ 1 ∧
        x * (1 - u * y) ≤ w + x * y * (1 - u) ∧
        w + x * y * (1 - u) ≤ 1 - u * y
      refine ⟨hx, hx1, mul_pos hu hy, huy.trans hy1, ?_, ?_⟩
      · calc
          x * (1 - u * y) = x * (1 - y) + x * y * (1 - u) := by ring
          _ ≤ _ := add_le_add hlow le_rfl
      · calc
          w + x * y * (1 - u) ≤ (1 - y) + y * (1 - u) :=
            add_le_add hhigh
              (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hy.le hx1) (sub_nonneg.mpr hu1))
          _ = 1 - u * y := by ring

/-- The dose of one tagged bath across all slices assigned to it. -/
def resetBathDose (bath : Bool) (steps : List (Bool × ResetSlice n)) : ℝ :=
  (steps.map fun part => if part.1 == bath then part.2.dose else 0).sum

theorem resetBathDose_nonnegative (bath : Bool) (steps : List (Bool × ResetSlice n)) :
    0 ≤ resetBathDose bath steps := by
  unfold resetBathDose
  apply List.sum_nonneg
  intro x hx
  obtain ⟨part, _, rfl⟩ := List.mem_map.mp hx
  split
  · exact mul_nonneg part.2.rate_nonneg part.2.duration_nonneg
  · exact le_rfl

theorem twoBathCoefficients_attenuation (steps : List (Bool × ResetSlice n)) :
    let (x, y, _) := twoBathCoefficients steps
    x = Real.exp (-resetBathDose false steps) ∧ y = Real.exp (-resetBathDose true steps) := by
  induction steps with
  | nil => simp [twoBathCoefficients, resetBathDose]
  | cons head tail ih =>
    obtain ⟨bath, s⟩ := head
    generalize hCoeff : twoBathCoefficients tail = coeff
    rw [hCoeff] at ih
    obtain ⟨x, y, w⟩ := coeff
    dsimp at ih
    obtain ⟨hx, hy⟩ := ih
    cases bath <;> simp [twoBathCoefficients, hCoeff, resetBathDose, hx, hy, Real.exp_add] <;> exact mul_comm _ _

variable [DecidableEq n]

/-- The three coefficients describe the action on the whole matrix
space, including trace-zero and off-diagonal inputs. -/
theorem evolveResetSchedule_eq_twoBathCoefficients (steps : List (Bool × ResetSlice n))
    (A B : Matrix n n ℂ)
    (hTargets : ∀ p ∈ steps, p.2.target = if p.1 then B else A) (X : Matrix n n ℂ) :
    let (x, y, w) := twoBathCoefficients steps
    evolveResetSchedule (steps.map Prod.snd) X =
      ((x * y : ℝ) : ℂ) • X + ((1 - x * y : ℝ) : ℂ) • (X.trace • A) +
        (w : ℂ) • (X.trace • (B - A)) := by
  induction steps generalizing X with
  | nil => simp [twoBathCoefficients, evolveResetSchedule]
  | cons head tail ih =>
    obtain ⟨bath, s⟩ := head
    have hTarget := hTargets (bath, s) (by simp)
    have hTail : ∀ p ∈ tail, p.2.target = if p.1 then B else A :=
      fun p hp => hTargets p (List.mem_cons_of_mem (bath, s) hp)
    simp only [List.map_cons, evolveResetSchedule]
    rw [ih hTail]
    generalize hCoeff : twoBathCoefficients tail = coeff
    obtain ⟨x, y, w⟩ := coeff
    rw [s.trace_evolve, s.evolve_affine, hTarget]
    cases bath <;> simp [twoBathCoefficients, hCoeff, ResetSlice.attenuation] <;> module

omit [DecidableEq n] in
/-- Reproduce one bath at unit rate with the given nonnegative dose. -/
def ResetSlice.withUnitRateDose (s : ResetSlice n) (dose : ℝ) (hDose : 0 ≤ dose) : ResetSlice n :=
  { s with rate := 1, duration := dose, rate_nonneg := zero_le_one, duration_nonneg := hDose }

omit [DecidableEq n] in
@[simp] theorem ResetSlice.withUnitRateDose_dose (s : ResetSlice n) (dose : ℝ) (h : 0 ≤ dose) :
    (s.withUnitRateDose dose h).dose = dose := by simp [ResetSlice.withUnitRateDose, ResetSlice.dose]

@[simp] theorem ResetSlice.withUnitRateDose_target (s : ResetSlice n) (dose : ℝ) (h : 0 ≤ dose) :
    (s.withUnitRateDose dose h).target = s.target := rfl

private theorem exists_trailingDose (a b w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hlo : Real.exp (-a) * (1 - Real.exp (-b)) ≤ w)
    (hhi : w ≤ 1 - Real.exp (-b)) :
    ∃ r ∈ Set.Icc 0 a, Real.exp (-r) * (1 - Real.exp (-b)) = w := by
  by_cases hb0 : b = 0
  · subst b
    have hw : w = 0 := le_antisymm (by simpa using hhi) (by simpa using hlo)
    exact ⟨0, ⟨le_rfl, ha⟩, by simp [hw]⟩
  let y := Real.exp (-b)
  have hy : 0 < 1 - y := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (lt_of_le_of_ne hb (Ne.symm hb0))))
  let v := w / (1 - y)
  have hvlo : Real.exp (-a) ≤ v := (le_div_iff₀ hy).mpr hlo
  have hvhi : v ≤ 1 := (div_le_iff₀ hy).mpr (by simpa using hhi)
  have hv : 0 < v := (Real.exp_pos _).trans_le hvlo
  refine ⟨-Real.log v, ⟨neg_nonneg.mpr (Real.log_nonpos hv.le hvhi), ?_⟩, ?_⟩
  · have h := Real.log_le_log (Real.exp_pos _) hvlo
    rw [Real.log_exp] at h
    linarith only [h]
  · rw [neg_neg, Real.exp_log hv]
    exact div_mul_cancel₀ _ hy.ne'

omit [DecidableEq n] in
private theorem threeSlice_coefficients (s t : ResetSlice n)
    (a b r : ℝ) (hr : 0 ≤ r) (hra : r ≤ a) (hb : 0 ≤ b) :
    twoBathCoefficients ([
      (false, s.withUnitRateDose (a-r) (sub_nonneg.mpr hra)),
      (true, t.withUnitRateDose b hb),
      (false, s.withUnitRateDose r hr)] : List (Bool × ResetSlice n)) =
    (Real.exp (-a), Real.exp (-b), Real.exp (-r) * (1 - Real.exp (-b))) := by
  simp only [twoBathCoefficients, ResetSlice.withUnitRateDose_dose,
    Bool.false_eq_true, if_false, if_true, mul_one, zero_add]
  rw [← Real.exp_add]
  congr 2
  ring

/-- Every finite two-bath schedule has one three-slice realization at
the same two doses. The selected split works on every input matrix. -/
theorem exists_equivalent_threeSlice_schedule (steps : List (Bool × ResetSlice n))
    (s t : ResetSlice n) (hTargets : ∀ p ∈ steps, p.2.target = if p.1 then t.target else s.target) :
    let a := resetBathDose false steps
    let b := resetBathDose true steps
    ∃ (r : ℝ) (hr : 0 ≤ r) (hra : r ≤ a),
      ∀ X : Matrix n n ℂ, evolveResetSchedule (steps.map Prod.snd) X =
        evolveResetSchedule [
          s.withUnitRateDose (a-r) (sub_nonneg.mpr hra),
          t.withUnitRateDose b (resetBathDose_nonnegative true steps),
          s.withUnitRateDose r hr] X := by
  let a := resetBathDose false steps
  let b := resetBathDose true steps
  have ha : 0 ≤ a := resetBathDose_nonnegative false steps
  have hb : 0 ≤ b := resetBathDose_nonnegative true steps
  generalize hCoeff : twoBathCoefficients steps = coeff
  obtain ⟨x, y, w⟩ := coeff
  have hAtten := twoBathCoefficients_attenuation steps
  have hBounds := twoBathCoefficients_bounds steps
  rw [hCoeff] at hAtten hBounds
  obtain ⟨hx, hy⟩ := hAtten
  obtain ⟨_, _, _, _, hlo, hhi⟩ := hBounds
  change x = Real.exp (-a) at hx
  change y = Real.exp (-b) at hy
  rw [hx, hy] at hlo
  rw [hy] at hhi
  obtain ⟨r, ⟨hr, hra⟩, hw⟩ := exists_trailingDose a b w ha hb hlo hhi
  refine ⟨r, hr, hra, fun X => ?_⟩
  let compressed : List (Bool × ResetSlice n) := [
    (false, s.withUnitRateDose (a-r) (sub_nonneg.mpr hra)),
    (true, t.withUnitRateDose b hb),
    (false, s.withUnitRateDose r hr)]
  have hCompressed : ∀ p ∈ compressed, p.2.target = if p.1 then t.target else s.target := by
    intro p hp
    simp only [compressed, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  change evolveResetSchedule (steps.map Prod.snd) X =
    evolveResetSchedule (compressed.map Prod.snd) X
  have hOriginal := evolveResetSchedule_eq_twoBathCoefficients steps _ _ hTargets X
  have hReplacement := evolveResetSchedule_eq_twoBathCoefficients compressed _ _ hCompressed X
  have hThree := threeSlice_coefficients s t a b r hr hra hb
  change twoBathCoefficients compressed = _ at hThree
  rw [hCoeff] at hOriginal
  rw [hThree] at hReplacement
  simp only [hx, hy, hw] at hOriginal hReplacement
  exact hOriginal.trans hReplacement.symm

/-- At fixed nonnegative doses, the entire reachable family is the
closed affine segment between the two opposing block orders. The same
coefficient describes the map for all input matrices. -/
theorem twoBath_channel_reachable_iff (s t : ResetSlice n) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (F : Matrix n n ℂ → Matrix n n ℂ) :
    (∃ steps : List (Bool × ResetSlice n),
      resetBathDose false steps = a ∧ resetBathDose true steps = b ∧
      (∀ p ∈ steps, p.2.target = if p.1 then t.target else s.target) ∧
      ∀ X, F X = evolveResetSchedule (steps.map Prod.snd) X) ↔
    ∃ w ∈ Set.Icc (Real.exp (-a) * (1 - Real.exp (-b))) (1 - Real.exp (-b)),
      ∀ X, F X = ((Real.exp (-a) * Real.exp (-b) : ℝ) : ℂ) • X +
        ((1 - Real.exp (-a) * Real.exp (-b) : ℝ) : ℂ) • (X.trace • s.target) +
        (w : ℂ) • (X.trace • (t.target - s.target)) := by
  constructor
  · rintro ⟨steps, hA, hB, hTarget, hF⟩
    generalize hCoeff : twoBathCoefficients steps = coeff
    obtain ⟨x, y, w⟩ := coeff
    have hAtten := twoBathCoefficients_attenuation steps
    have hBounds := twoBathCoefficients_bounds steps
    rw [hCoeff, hA, hB] at hAtten
    rw [hCoeff] at hBounds
    obtain ⟨hx, hy⟩ := hAtten
    obtain ⟨_, _, _, _, hlo, hhi⟩ := hBounds
    refine ⟨w, ⟨?_, ?_⟩, fun X => ?_⟩
    · simpa only [← hx, ← hy] using hlo
    · simpa only [← hy] using hhi
    · have h := evolveResetSchedule_eq_twoBathCoefficients steps _ _ hTarget X
      rw [hCoeff] at h
      simpa only [← hx, ← hy] using (hF X).trans h
  · rintro ⟨w, ⟨hlo, hhi⟩, hF⟩
    obtain ⟨r, ⟨hr, hra⟩, hw⟩ := exists_trailingDose a b w ha hb hlo hhi
    let steps : List (Bool × ResetSlice n) := [
      (false, s.withUnitRateDose (a-r) (sub_nonneg.mpr hra)),
      (true, t.withUnitRateDose b hb),
      (false, s.withUnitRateDose r hr)]
    have hTarget : ∀ p ∈ steps, p.2.target = if p.1 then t.target else s.target := by
      intro p hp
      simp only [steps, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp
    refine ⟨steps, ?_, ?_, hTarget, fun X => ?_⟩
    · simp [steps, resetBathDose]
    · simp [steps, resetBathDose]
    · have h := evolveResetSchedule_eq_twoBathCoefficients steps _ _ hTarget X
      have hThree := threeSlice_coefficients s t a b r hr hra hb
      change twoBathCoefficients steps = _ at hThree
      rw [hThree] at h
      exact (hF X).trans (by simpa only [hw] using h.symm)

end SKEFTHawking.FinitePositiveKernel.GibbsReset
