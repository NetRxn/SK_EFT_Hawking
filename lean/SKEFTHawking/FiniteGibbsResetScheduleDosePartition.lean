import SKEFTHawking.FiniteGibbsResetScheduleOrdering

/-! Partitioning one finite reset bath into different slices preserves its
action at the same total dose. With two baths, the extremal orders depend
only on the dose and target of each bath. -/

namespace SKEFTHawking.FinitePositiveKernel.GibbsReset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A block whose slices share one target depends only on the total
dose, even when rates and durations vary from slice to slice. -/
theorem evolveResetSchedule_eq_of_common_target
    (steps : List (ResetSlice n)) (target : Matrix n n ℂ)
    (hTarget : ∀ s ∈ steps, s.target = target) (X : Matrix n n ℂ) :
    evolveResetSchedule steps X = resetScheduleAttenuation steps • X +
      (1 - resetScheduleAttenuation steps) • (X.trace • target) := by
  induction steps generalizing X with
  | nil => simp [evolveResetSchedule, resetScheduleAttenuation, resetScheduleDose]
  | cons s steps ih =>
      have hs : s.target = target := hTarget s (by simp)
      have htail : ∀ t ∈ steps, t.target = target :=
        fun t ht => hTarget t (List.mem_cons_of_mem s ht)
      rw [evolveResetSchedule, ih htail, s.trace_evolve, s.evolve_affine, hs,
        resetScheduleAttenuation_cons]
      module

/-- Arbitrarily repartitioning a single bath's exposure into valid
slices preserves the entire channel action, for every input matrix. -/
theorem evolveResetSchedule_common_target_eq_of_dose_eq
    (left right : List (ResetSlice n)) (target X : Matrix n n ℂ)
    (hl : ∀ s ∈ left, s.target = target) (hr : ∀ s ∈ right, s.target = target)
    (hDose : resetScheduleDose left = resetScheduleDose right) :
    evolveResetSchedule left X = evolveResetSchedule right X := by
  rw [evolveResetSchedule_eq_of_common_target left target hl X,
    evolveResetSchedule_eq_of_common_target right target hr X]
  simp only [resetScheduleAttenuation, hDose]

omit [DecidableEq n] in
private theorem pairwise_common_bath_scores
    (score : ResetSlice n → ℝ) (left right : List (ResetSlice n)) (a b : ℝ)
    (hl : ∀ s ∈ left, score s = a) (hr : ∀ s ∈ right, score s = b)
    (hab : a ≤ b) :
    (left ++ right).Pairwise (fun s t => score s ≤ score t) := by
  rw [List.pairwise_append]
  have same (xs : List (ResetSlice n)) (c : ℝ) (hc : ∀ s ∈ xs, score s = c) :
      xs.Pairwise (fun s t => score s ≤ score t) :=
    List.pairwise_of_forall_mem_list fun s hs t ht => by rw [hc s hs, hc t ht]
  exact ⟨same left a hl, same right b hr,
    fun s hs t ht => by simpa only [hl s hs, hr t ht] using hab⟩

/-- The matrix difference of two opposite orders of constant-target
blocks depends only on the total dose of each block. -/
theorem evolveResetSchedule_block_reversal_of_common_targets
    (left right : List (ResetSlice n)) (A B X : Matrix n n ℂ)
    (hl : ∀ s ∈ left, s.target = A) (hr : ∀ s ∈ right, s.target = B) :
    evolveResetSchedule (left ++ right) X - evolveResetSchedule (right ++ left) X =
      ((1 - resetScheduleAttenuation left) * (1 - resetScheduleAttenuation right) *
        X.trace) • (B - A) := by
  rw [evolveResetSchedule_append, evolveResetSchedule_append,
    evolveResetSchedule_eq_of_common_target right B hr (evolveResetSchedule left X),
    evolveResetSchedule_eq_of_common_target left A hl (evolveResetSchedule right X),
    evolveResetSchedule_trace, evolveResetSchedule_trace,
    evolveResetSchedule_eq_of_common_target left A hl X,
    evolveResetSchedule_eq_of_common_target right B hr X]
  module

/-- Slicing either bath exposure into arbitrary physical segments leaves
the two extremal block readouts and their gap unchanged. -/
theorem twoBath_readout_spread_by_dose (readout : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (left right : List (ResetSlice n)) (A B X : Matrix n n ℂ)
    (hl : ∀ s ∈ left, s.target = A) (hr : ∀ s ∈ right, s.target = B)
    (hX : X.trace = 1) (hOrder : readout A ≤ readout B) :
    (∀ other : List (ResetSlice n), other.Perm (left ++ right) →
      readout (evolveResetSchedule (right ++ left) X) ≤
        readout (evolveResetSchedule other X) ∧
      readout (evolveResetSchedule other X) ≤
        readout (evolveResetSchedule (left ++ right) X)) ∧
    readout (evolveResetSchedule (left ++ right) X) -
      readout (evolveResetSchedule (right ++ left) X) =
      (1 - Real.exp (-resetScheduleDose left)) *
        (1 - Real.exp (-resetScheduleDose right)) * (readout B - readout A) := by
  refine ⟨?_, ?_⟩
  · intro other hOther
    have hHi := pairwise_common_bath_scores (fun s => readout s.target)
      left right (readout A) (readout B)
      (fun s hs => congrArg readout (hl s hs))
      (fun s hs => congrArg readout (hr s hs)) hOrder
    have hLo := pairwise_common_bath_scores (fun s => (-readout) s.target)
      right left ((-readout) B) ((-readout) A)
      (fun s hs => congrArg (-readout) (hr s hs))
      (fun s hs => congrArg (-readout) (hl s hs))
      (by simpa only [LinearMap.neg_apply, neg_le_neg_iff] using hOrder)
    refine ⟨?_, sorted_resetSchedule_readout_maximal readout _ other X hX hHi hOther⟩
    have bound := sorted_resetSchedule_readout_maximal (-readout) _ other X hX hLo
      (hOther.trans List.perm_append_comm)
    simpa only [LinearMap.neg_apply, neg_le_neg_iff] using bound
  · rw [← map_sub, evolveResetSchedule_block_reversal_of_common_targets left right A B X hl hr,
      hX, mul_one]
    let c := (1 - Real.exp (-resetScheduleDose left)) * (1 - Real.exp (-resetScheduleDose right))
    have hc : (c : ℂ) = (1 - resetScheduleAttenuation left) *
        (1 - resetScheduleAttenuation right) := by
      dsimp only [c, resetScheduleAttenuation]
      push_cast
      rfl
    rw [← hc]
    change readout ((algebraMap ℝ ℂ c) • (B - A)) = c * (readout B - readout A)
    rw [IsScalarTower.algebraMap_smul, map_smul, map_sub, smul_eq_mul]

/-- The two extremal block actions are unchanged when either common
bath is independently segmented again at the same total dose. -/
theorem twoBath_extremal_blocks_eq_of_doses_eq
    (left right left' right' : List (ResetSlice n)) (A B X : Matrix n n ℂ)
    (hl : ∀ s ∈ left, s.target = A) (hr : ∀ s ∈ right, s.target = B)
    (hl' : ∀ s ∈ left', s.target = A) (hr' : ∀ s ∈ right', s.target = B)
    (hL : resetScheduleDose left = resetScheduleDose left')
    (hR : resetScheduleDose right = resetScheduleDose right') :
    evolveResetSchedule (left ++ right) X = evolveResetSchedule (left' ++ right') X ∧
      evolveResetSchedule (right ++ left) X = evolveResetSchedule (right' ++ left') X := by
  have leftAction (Y : Matrix n n ℂ) :=
    evolveResetSchedule_common_target_eq_of_dose_eq left left' A Y hl hl' hL
  have rightAction (Y : Matrix n n ℂ) :=
    evolveResetSchedule_common_target_eq_of_dose_eq right right' B Y hr hr' hR
  constructor <;> simp only [evolveResetSchedule_append, leftAction, rightAction]

end SKEFTHawking.FinitePositiveKernel.GibbsReset
