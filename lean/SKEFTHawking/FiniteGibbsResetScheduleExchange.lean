import SKEFTHawking.FiniteGibbsResetSchedule

/-! An adjacent exchange in a driven Gibbs schedule changes the output
by the two-slice contrast discounted by the remaining reset dose. -/

noncomputable section

set_option autoImplicit false

namespace SKEFTHawking.FinitePositiveKernel.GibbsReset

open Matrix QuantumNetwork

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem evolveResetSchedule_append (pre post : List (ResetSlice n)) (X : Matrix n n ℂ) :
    evolveResetSchedule (pre ++ post) X =
      evolveResetSchedule post (evolveResetSchedule pre X) := by
  induction pre generalizing X with
  | nil => rfl
  | cons s pre ih =>
      change evolveResetSchedule (pre ++ post) (s.evolve X) =
        evolveResetSchedule post (evolveResetSchedule pre (s.evolve X))
      exact ih _

/-- Earlier slices affect this exchange only through the input trace.
Later slices discount the exchange by their total retained fraction. -/
theorem evolveResetSchedule_adjacent_exchange (pre post : List (ResetSlice n))
    (s t : ResetSlice n) (X : Matrix n n ℂ) :
    evolveResetSchedule (pre ++ s :: t :: post) X -
      evolveResetSchedule (pre ++ t :: s :: post) X =
      (resetScheduleAttenuation post * (1-s.attenuation) *
        (1-t.attenuation) * X.trace) • (t.target - s.target) := by
  let Y := evolveResetSchedule pre X
  have hTrace : Y.trace = X.trace := evolveResetSchedule_trace pre X
  have hCommon : (evolveResetSchedule [s,t] Y).trace =
      (evolveResetSchedule [t,s] Y).trace := by
    exact (evolveResetSchedule_trace [s,t] Y).trans (evolveResetSchedule_trace [t,s] Y).symm
  rw [evolveResetSchedule_append, evolveResetSchedule_append]
  change evolveResetSchedule post (evolveResetSchedule [s,t] Y) -
      evolveResetSchedule post (evolveResetSchedule [t,s] Y) = _
  rw [evolveResetSchedule_equal_trace_difference post _ _ hCommon,
    evolveResetSchedule_two_slice_reversal, hTrace]
  change resetScheduleAttenuation post •
      (((1-s.attenuation)*(1-t.attenuation)*X.trace) • (t.target-s.target)) = _
  rw [smul_smul]
  module

end SKEFTHawking.FinitePositiveKernel.GibbsReset
