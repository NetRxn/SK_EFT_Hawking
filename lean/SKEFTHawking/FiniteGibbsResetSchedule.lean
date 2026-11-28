import SKEFTHawking.FiniteGibbsReset

/-! Finite schedules of actual Gibbs reset propagators with changing bath
targets. Equal-trace memory decays with total dose, while the target
contribution depends on chronological order. -/

noncomputable section

set_option autoImplicit false

namespace SKEFTHawking.FinitePositiveKernel.GibbsReset

open Matrix QuantumNetwork OpenSystems GibbsObservable DiagonalLindblad
open scoped BigOperators

/-- One physical reset slice. Each slice may have its own thermal target. -/
structure ResetSlice (n : Type*) [Fintype n] where
  weights : n → ℝ
  weights_nonneg : ∀ i, 0 ≤ weights i
  weights_normalized : ∑ i, weights i = 1
  rate : ℝ
  duration : ℝ
  rate_nonneg : 0 ≤ rate
  duration_nonneg : 0 ≤ duration

variable {n : Type*} [Fintype n] [DecidableEq n]

def ResetSlice.dose (s : ResetSlice n) : ℝ := s.rate*s.duration

def ResetSlice.target (s : ResetSlice n) : Matrix n n ℂ := density s.weights

def ResetSlice.attenuation (s : ResetSlice n) : ℂ := Real.exp (-s.dose)

def ResetSlice.evolve (s : ResetSlice n) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  lindbladPropagatorAction 0 (jumps s.weights s.rate) s.duration X

theorem ResetSlice.evolve_affine (s : ResetSlice n) (X : Matrix n n ℂ) :
    s.evolve X = s.attenuation • X +
      (1-s.attenuation) • (X.trace • s.target) := by
  simpa only [ResetSlice.evolve,ResetSlice.attenuation,ResetSlice.dose,ResetSlice.target,neg_mul] using
    propagator_state s.weights s.weights_nonneg s.weights_normalized
      s.rate s.rate_nonneg s.duration X

theorem ResetSlice.trace_evolve (s : ResetSlice n) (X : Matrix n n ℂ) :
    (s.evolve X).trace = X.trace := by
  rw [s.evolve_affine]
  simp only [Matrix.trace_add,Matrix.trace_smul,ResetSlice.target,density_trace,
    s.weights_normalized,Complex.ofReal_one,smul_eq_mul,mul_one]
  ring

/-- Every nonnegative physical slice is a normalized Kraus channel. -/
theorem ResetSlice.normalized_kraus (s : ResetSlice n) :
    IsKrausChannel (timeKraus s.weights (Real.exp (-s.rate*s.duration))) :=
  time_normalized _ s.weights_nonneg s.weights_normalized _
    (Real.exp_pos _).le (exp_rate_le_one _ _ s.rate_nonneg s.duration_nonneg)

theorem ResetSlice.evolve_eq_kraus (s : ResetSlice n) (X : Matrix n n ℂ) :
    s.evolve X = krausMap (timeKraus s.weights (Real.exp (-s.rate*s.duration))) X :=
  (time_state_eq_propagator _ s.weights_nonneg s.weights_normalized _
    _ s.rate_nonneg s.duration_nonneg X).symm

theorem ResetSlice.trace_target (s : ResetSlice n) : s.target.trace = 1 := by
  rw [ResetSlice.target,density_trace,s.weights_normalized,Complex.ofReal_one]

def resetScheduleDose (steps : List (ResetSlice n)) : ℝ :=
  (steps.map ResetSlice.dose).sum

def resetScheduleAttenuation (steps : List (ResetSlice n)) : ℂ :=
  Real.exp (-resetScheduleDose steps)

omit [DecidableEq n] in
theorem resetScheduleAttenuation_cons (s : ResetSlice n) (steps : List (ResetSlice n)) :
    resetScheduleAttenuation (s::steps) = resetScheduleAttenuation steps * s.attenuation := by
  simp only [resetScheduleAttenuation,resetScheduleDose,List.map_cons,List.sum_cons,neg_add_rev,
    Real.exp_add,Complex.ofReal_mul,ResetSlice.attenuation]

/-- Run the head slice first. A later bath attenuates earlier target
contributions. -/
def evolveResetSchedule : List (ResetSlice n) → Matrix n n ℂ → Matrix n n ℂ
  | [], X => X
  | s::steps, X => evolveResetSchedule steps (s.evolve X)

/-- The total returned target on a trace-one state. In this recursion the
weight of the first target is multiplied by the attenuation of the tail. -/
def resetScheduleTarget : List (ResetSlice n) → Matrix n n ℂ
  | [] => 0
  | s::steps => resetScheduleAttenuation steps • ((1-s.attenuation) • s.target) +
      resetScheduleTarget steps

theorem evolveResetSchedule_affine (steps : List (ResetSlice n)) (X : Matrix n n ℂ) :
    evolveResetSchedule steps X = resetScheduleAttenuation steps • X +
      X.trace • resetScheduleTarget steps := by
  induction steps generalizing X with
  | nil => simp [evolveResetSchedule,resetScheduleAttenuation,resetScheduleDose,resetScheduleTarget]
  | cons s steps ih =>
      rw [evolveResetSchedule,ih,s.trace_evolve,s.evolve_affine,resetScheduleTarget,
        resetScheduleAttenuation_cons]
      module

theorem evolveResetSchedule_trace (steps : List (ResetSlice n)) (X : Matrix n n ℂ) :
    (evolveResetSchedule steps X).trace = X.trace := by
  induction steps generalizing X with
  | nil => rfl
  | cons s steps ih =>
      change (evolveResetSchedule steps (s.evolve X)).trace = X.trace
      rw [ih,s.trace_evolve]

/-- The accumulated target contribution carries the trace not retained
from the preceding state. -/
theorem resetScheduleTarget_trace (steps : List (ResetSlice n)) :
    (resetScheduleTarget steps).trace = 1-resetScheduleAttenuation steps := by
  induction steps with
  | nil => simp [resetScheduleTarget,resetScheduleAttenuation,resetScheduleDose]
  | cons s steps ih =>
      rw [resetScheduleTarget,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,
        s.trace_target,ih,resetScheduleAttenuation_cons]
      simp only [smul_eq_mul,mul_one]
      ring

omit [DecidableEq n] in
theorem resetScheduleDose_reversal (s t : ResetSlice n) :
    resetScheduleDose [s,t] = resetScheduleDose [t,s] := by
  simp [resetScheduleDose,add_comm]

/-- The preceding state contributes exactly an exponential of the negative
total dose to the difference of any two equal-trace states. -/
theorem evolveResetSchedule_equal_trace_difference (steps : List (ResetSlice n))
    (X Y : Matrix n n ℂ) (hTrace : X.trace = Y.trace) :
    evolveResetSchedule steps X - evolveResetSchedule steps Y =
      (Real.exp (-resetScheduleDose steps) : ℂ) • (X-Y) := by
  rw [evolveResetSchedule_affine,evolveResetSchedule_affine,hTrace]
  unfold resetScheduleAttenuation
  module

/-- Reversing two slices changes the output by a scalar times the difference
of their equilibrium targets. Reversal preserves total dose. -/
theorem evolveResetSchedule_two_slice_reversal (s t : ResetSlice n) (X : Matrix n n ℂ) :
    evolveResetSchedule [s,t] X - evolveResetSchedule [t,s] X =
      ((1-s.attenuation)*(1-t.attenuation)*X.trace) • (t.target-s.target) := by
  change t.evolve (s.evolve X) - s.evolve (t.evolve X) = _
  rw [t.evolve_affine (s.evolve X),s.evolve_affine (t.evolve X),
    s.trace_evolve,t.trace_evolve,s.evolve_affine X,t.evolve_affine X]
  module

/-- With positive doses and a nonzero trace, order is invisible exactly
when the normalized bath targets agree. -/
theorem evolveResetSchedule_two_slice_order_iff (s t : ResetSlice n) (X : Matrix n n ℂ)
    (hs : 0 < s.dose) (ht : 0 < t.dose) (hX : X.trace ≠ 0) :
    evolveResetSchedule [s,t] X = evolveResetSchedule [t,s] X ↔ s.target = t.target := by
  have hAtten (r : ResetSlice n) (hr : 0 < r.dose) : (1:ℂ)-r.attenuation ≠ 0 := by
    rw [sub_ne_zero,ResetSlice.attenuation,← Complex.ofReal_one]
    exact_mod_cast (show Real.exp (-r.dose) ≠ 1 from
      (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hr)).ne).symm
  have hCoeff : (1-s.attenuation)*(1-t.attenuation)*X.trace ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hAtten s hs) (hAtten t ht)) hX
  calc
    _ ↔ evolveResetSchedule [s,t] X - evolveResetSchedule [t,s] X = 0 :=
      sub_eq_zero.symm
    _ ↔ ((1-s.attenuation)*(1-t.attenuation)*X.trace) • (t.target-s.target) = 0 := by
      rw [evolveResetSchedule_two_slice_reversal]
    _ ↔ _ := by
      rw [smul_eq_zero,or_iff_right hCoeff,sub_eq_zero]
      exact eq_comm

/-- Each slice may be supplied independently by actual Boltzmann weights. -/
def gibbsResetSlice [Nonempty n] (energies : n → ℝ) (β rate duration : ℝ)
    (hr : 0 ≤ rate) (ht : 0 ≤ duration) : ResetSlice n where
  weights := gibbsWeights energies β
  weights_nonneg i := (gibbsWeights_pos energies β i).le
  weights_normalized := gibbsWeights_normalized energies β
  rate := rate
  duration := duration
  rate_nonneg := hr
  duration_nonneg := ht

theorem gibbsResetSlice_target [Nonempty n] (energies : n → ℝ) (β rate duration : ℝ)
    (hr : 0 ≤ rate) (ht : 0 ≤ duration) :
    (gibbsResetSlice energies β rate duration hr ht).target =
      FiniteGibbsClock.gibbs (density energies) β := by
  exact density_gibbsWeights energies β

end SKEFTHawking.FinitePositiveKernel.GibbsReset
