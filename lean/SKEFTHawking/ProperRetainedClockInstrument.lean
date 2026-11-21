import SKEFTHawking.ProperRetainedClockReadout
import SKEFTHawking.QuantumNetwork.FiniteInstrument

/-! A three-outcome projective instrument for the proper retained clock.
The branch states are unnormalized. An impossible outcome needs no division
by its weight. -/

noncomputable section
open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
open QuantumNetwork FiniteGibbsClock GibbsObservable

/-- The two hand outcomes occupy the first indices. The last index is the spectator. -/
def outcomeProjector : Fin 3 → Mat := Fin.lastCases spectator event

private theorem outcomeProjector_adjoint (a : Fin 3) : (outcomeProjector a)ᴴ = outcomeProjector a := by
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simpa only [outcomeProjector, Fin.lastCases_last] using spectator_adjoint
  · simpa [outcomeProjector] using event_adjoint b

private theorem outcomeProjector_mul (a b : Fin 3) :
    outcomeProjector a * outcomeProjector b =
      if a = b then outcomeProjector a else 0 := by
  refine Fin.lastCases ?_ (fun a => ?_) a
  · refine Fin.lastCases ?_ (fun b => ?_) b
    · simpa only [outcomeProjector, Fin.lastCases_last, if_true] using spectator_mul_self
    · simpa only [outcomeProjector, Fin.lastCases_last, Fin.lastCases_castSucc,
        Ne.symm (Fin.castSucc_ne_last (i := b)), if_false] using spectator_mul_event b
  · refine Fin.lastCases ?_ (fun b => ?_) b
    · simpa only [outcomeProjector, Fin.lastCases_last, Fin.lastCases_castSucc,
        Fin.castSucc_ne_last, if_false] using event_mul_spectator a
    · simpa only [outcomeProjector, Fin.lastCases_castSucc, Fin.castSucc_inj] using event_mul a b

/-- Evolve the measured projectors by the original clock Hamiltonian. -/
def evolvedProjector (ω ℏ E t : ℝ) (a : Fin 3) : Mat :=
  heisenberg (hamiltonian ω ℏ E) ℏ t (outcomeProjector a)

theorem evolvedProjector_adjoint (ω ℏ E t : ℝ) (a : Fin 3) :
    (evolvedProjector ω ℏ E t a)ᴴ = evolvedProjector ω ℏ E t a := by
  unfold evolvedProjector
  rw [← heisenberg_star (hamiltonian_hermitian ω ℏ E), outcomeProjector_adjoint]

theorem evolvedProjector_mul (ω ℏ E t : ℝ) (a b : Fin 3) :
    evolvedProjector ω ℏ E t a * evolvedProjector ω ℏ E t b =
      if a = b then evolvedProjector ω ℏ E t a else 0 := by
  unfold evolvedProjector
  rw [← heisenberg_mul, outcomeProjector_mul]
  split
  · rfl
  · simp [heisenberg, conjugate]

private theorem evolvedProjector_idempotent (ω ℏ E t : ℝ) (a : Fin 3) :
    evolvedProjector ω ℏ E t a * evolvedProjector ω ℏ E t a = evolvedProjector ω ℏ E t a := by
  simpa only [if_true] using evolvedProjector_mul ω ℏ E t a a

theorem evolvedProjector_complete (ω ℏ E t : ℝ) : (∑ a, evolvedProjector ω ℏ E t a) = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [evolvedProjector, outcomeProjector, Fin.lastCases_castSucc, Fin.lastCases_last]
  have h := readout_complete
  rw [Fin.sum_univ_two] at h
  rw [Fin.sum_univ_two, ← heisenberg_add, ← heisenberg_add, h, heisenberg_one]

/-- The normalized Lüders instrument with one projector Kraus operator per outcome. -/
def clockInstrument (ω ℏ E t : ℝ) : FiniteInstrument Level 3 where
  count := 1
  operators a _ := evolvedProjector ω ℏ E t a
  normalized := by
    simpa [evolvedProjector_adjoint, evolvedProjector_idempotent] using evolvedProjector_complete ω ℏ E t

theorem clockInstrument_branch (ω ℏ E t : ℝ) (a : Fin 3) (X : Mat) :
    (clockInstrument ω ℏ E t).branch a X =
      evolvedProjector ω ℏ E t a * X * evolvedProjector ω ℏ E t a := by
  change (∑ _ : Fin 1, evolvedProjector ω ℏ E t a * X * (evolvedProjector ω ℏ E t a)ᴴ) = _
  rw [Fin.sum_univ_one, evolvedProjector_adjoint]

/-- Under immediate remeasurement, the same record gives the original branch
and a different record gives the zero matrix, including on zero-weight input. -/
theorem clockInstrument_repeat (ω ℏ E t : ℝ) (a b : Fin 3) (X : Mat) :
    (clockInstrument ω ℏ E t).branch b ((clockInstrument ω ℏ E t).branch a X) =
      if b = a then (clockInstrument ω ℏ E t).branch a X else 0 := by
  simp only [clockInstrument_branch]
  let P := evolvedProjector ω ℏ E t a
  let Q := evolvedProjector ω ℏ E t b
  change Q * (P * X * P) * Q = if b = a then P * X * P else 0
  rw [show Q * (P * X * P) * Q = (Q * P) * X * (P * Q) by simp only [mul_assoc]]
  by_cases h : b = a
  · subst b
    simp only [P, Q, evolvedProjector_idempotent, if_true]
  · simp only [P, Q, evolvedProjector_mul, if_neg h, if_neg (Ne.symm h), zero_mul]

theorem clockInstrument_weight (ω ℏ E t : ℝ) (a : Fin 3) (X : Mat) :
    (clockInstrument ω ℏ E t).weight a X = ((evolvedProjector ω ℏ E t a * X).trace).re := by
  rw [FiniteInstrument.weight, clockInstrument_branch, Matrix.trace_mul_cycle,
    evolvedProjector_idempotent]

theorem clockInstrument_spectator_weight (ω ℏ E t : ℝ) :
    (clockInstrument ω ℏ E t).weight (Fin.last 2) prepared = 0 := by
  rw [clockInstrument_weight]
  simpa only [evolvedProjector, outcomeProjector, Fin.lastCases_last, Complex.zero_re] using
    congrArg Complex.re (spectator_dark ω ℏ E t)

/-- The instrument recovers the hand Born law at the signed physical time. -/
theorem clockInstrument_hand_weight (ω ℏ E β s : ℝ) (hℏ : 0 < ℏ) (a : Fin 2) :
    (clockInstrument ω ℏ E (-β * ℏ * s)).weight a.castSucc prepared =
      QuantumNetwork.FiniteClockHandReadout.mass ω (-β * ℏ * s) a := by
  rw [clockInstrument_weight]
  simp only [evolvedProjector, outcomeProjector, Fin.lastCases_castSucc]
  have h := retained_born ω ℏ E β s hℏ a
  change preparedGibbsExpectation (hamiltonian_hermitian ω ℏ E) β prepared
    (Clock.quotientModular (hamiltonian_hermitian ω ℏ E) β s
      (GibbsObservable.observable
        (gibbs_posDef (hamiltonian_hermitian ω ℏ E) β).posSemidef (event a))) = _ at h
  rw [Clock.quotientModular_eq_heisenberg _ _ _ _ hℏ, preparedGibbsExpectation_observable] at h
  exact h

theorem evolvedProjector_mem_fixedAlgebra (ω ℏ E β s : ℝ) (hℏ : 0 < ℏ) (a : Fin 3) :
    evolvedProjector ω ℏ E (-β * ℏ * s) a ∈ fixedAlgebra signatures := by
  let hH := hamiltonian_hermitian ω ℏ E
  let hfixed := hamiltonian_fixed ω ℏ E
  have ha : observable (gibbs_posDef hH β).posSemidef (outcomeProjector a) ∈
      retainedGibbsSpace signatures hH hfixed β := by
    refine Fin.lastCases ?_ (fun b => ?_) a
    · rw [outcomeProjector, Fin.lastCases_last]
      change (spectatorVector ω ℏ E β).val ∈ retainedGibbsSpace signatures hH hfixed β
      exact (spectatorVector ω ℏ E β).property
    · rw [outcomeProjector, Fin.lastCases_castSucc]
      change (eventVector ω ℏ E β b).val ∈ retainedGibbsSpace signatures hH hfixed β
      exact (eventVector ω ℏ E β b).property
  have hm := quotientModular_mem_retainedGibbsSpace signatures hH hfixed β s ha
  rw [Clock.quotientModular_eq_heisenberg hH β s ℏ hℏ] at hm
  exact (observable_mem_retainedGibbsSpace signatures hH hfixed β _).mp hm

/-- Every unnormalized branch preserves the block algebra at modular time. -/
theorem clockInstrument_branch_mem_fixedAlgebra (ω ℏ E β s : ℝ) (hℏ : 0 < ℏ) (a : Fin 3)
    (X : Mat) (hX : X ∈ fixedAlgebra signatures) :
    (clockInstrument ω ℏ E (-β * ℏ * s)).branch a X ∈ fixedAlgebra signatures := by
  rw [clockInstrument_branch]
  have hP := evolvedProjector_mem_fixedAlgebra ω ℏ E β s hℏ a
  exact (fixedAlgebra signatures).mul_mem ((fixedAlgebra signatures).mul_mem hP hX) hP

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
