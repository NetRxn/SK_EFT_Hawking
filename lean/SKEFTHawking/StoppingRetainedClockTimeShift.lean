import SKEFTHawking.StoppingRetainedClockErrorBudget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The exact projector allowance and a uniform time-shift bound for the three-level retained clock. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
open QuantumNetwork FiniteGibbsClock

private theorem norm_phase_sub_eq (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ =
      2 * |Real.sin ((x - y) / 2)| := by
  have hfactor : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (y : ℂ)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hy : ‖Complex.exp (Complex.I * (y : ℂ))‖ = 1 := by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [hfactor, norm_mul, hy, mul_one, Complex.norm_exp_I_mul_ofReal_sub_one]
  simp

private def offDiagonal (z : ℂ) : Mat :=
  corner !![0, z; star z, 0]

private theorem offDiagonal_opNorm (z : ℂ) : ‖offDiagonal z‖ = ‖z‖ := by
  let v : Level → ℂ := Sum.elim (fun _ => (Complex.normSq z : ℂ)) (fun _ => 0)
  have hM : (offDiagonal z)ᴴ * offDiagonal z = Matrix.diagonal v := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        fin_cases i <;> fin_cases j <;>
          simp [offDiagonal, corner, v, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Fintype.sum_sum_type, Fin.sum_univ_two,
            Complex.mul_conj, mul_comm]
      | inr j => simp [offDiagonal, corner, v, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Fintype.sum_sum_type]
    | inr i =>
      cases j <;> simp [offDiagonal, corner, v, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_sum_type]
  have hv : ‖v‖ = ‖z‖ ^ 2 := by
    have hp : ∀ i, ‖v i‖ ≤ ‖z‖ ^ 2 := by
      intro i
      cases i <;> simp [v, abs_of_nonneg (Complex.normSq_nonneg z), Complex.sq_norm, Complex.normSq_nonneg]
    have hp' : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
    apply le_antisymm ((pi_norm_le_iff_of_nonneg hp').2 hp)
    have low := norm_le_pi_norm v (Sum.inl (0 : Fin 2))
    simpa [v, abs_of_nonneg (Complex.normSq_nonneg z), Complex.sq_norm, Complex.normSq_nonneg] using low
  have hs := Matrix.l2_opNorm_conjTranspose_mul_self (offDiagonal z)
  rw [hM, Matrix.l2_opNorm_diagonal, hv] at hs
  nlinarith [norm_nonneg (offDiagonal z), norm_nonneg z, sq_nonneg (‖z‖ - ‖offDiagonal z‖)]

private def phase (ω t : ℝ) : ℂ := Complex.exp (Complex.I * ((ω * t : ℝ) : ℂ))

private theorem hand_phase_mul (ω ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    Complex.I * ((t : ℂ) / (ℏ : ℂ)) * ((ℏ : ℂ) * (ω : ℂ)) =
      Complex.I * ((ω : ℂ) * (t : ℂ)) := by
  field_simp [Complex.ofReal_ne_zero.mpr hℏ]

private theorem handProjector_diff (ω ℏ E t t' : ℝ) (hℏ : ℏ ≠ 0) (a : Fin 2) :
    evolvedProjector ω ℏ E t a.castSucc - evolvedProjector ω ℏ E t' a.castSucc =
      offDiagonal (star ((phase ω t - phase ω t') *
        (if a = 0 then (-1 / 2 : ℂ) else (1 / 2 : ℂ)))) := by
  let e : Level → ℂ := Sum.elim (![0, ((ℏ * ω : ℝ) : ℂ)] : Fin 2 → ℂ) (fun _ => E)
  unfold evolvedProjector outcomeProjector
  simp only [Fin.lastCases_castSucc]
  change conjugate (Matrix.diagonal e) (Complex.I * ((t : ℂ) / (ℏ : ℂ))) (event a) -
    conjugate (Matrix.diagonal e) (Complex.I * ((t' : ℂ) / (ℏ : ℂ))) (event a) = _
  ext i j
  simp only [Matrix.sub_apply, diagonal_conjugate_entry]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      fin_cases a <;> fin_cases i <;> fin_cases j <;>
        simp [e, event, corner, QuantumNetwork.FiniteClockHandReadout.Q, offDiagonal,
          map_mul, phase, ← Complex.exp_conj, Complex.conj_I,
          hand_phase_mul ω ℏ _ hℏ] <;> ring
    | inr j => simp [event, corner, offDiagonal]
  | inr i =>
    cases j <;> simp [event, corner, offDiagonal]

private theorem spectatorProjector_eq (ω ℏ E t : ℝ) :
    evolvedProjector ω ℏ E t (Fin.last 2) = spectator := by
  let e : Level → ℂ := Sum.elim (![0, ((ℏ * ω : ℝ) : ℂ)] : Fin 2 → ℂ) (fun _ => E)
  unfold evolvedProjector outcomeProjector
  simp only [Fin.lastCases_last]
  change conjugate (Matrix.diagonal e) (Complex.I * ((t : ℂ) / (ℏ : ℂ))) spectator = _
  ext i j
  rw [diagonal_conjugate_entry]
  cases i <;> cases j <;> simp [spectator, e]

/-- Only the two hand outcomes contribute to the clock allowance. -/
theorem clockProjectorAllowance_eq_phase (ω ℏ E t t' : ℝ) (hℏ : ℏ ≠ 0) :
    clockProjectorAllowance ω ℏ E t t' =
      2 * ‖Complex.exp (Complex.I * ((ω * t : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((ω * t' : ℝ) : ℂ))‖ := by
  change _ = 2 * ‖phase ω t - phase ω t'‖
  rw [clockProjectorAllowance, Fin.sum_univ_castSucc, spectatorProjector_eq,
    spectatorProjector_eq, sub_self, norm_zero, add_zero]
  simp_rw [handProjector_diff ω ℏ E t t' hℏ, offDiagonal_opNorm, norm_star, norm_mul]
  rw [Fin.sum_univ_two]
  norm_num
  ring

/-- The clock allowance sees the relative hand phase, with its exact periodic variation. -/
theorem clockProjectorAllowance_eq_sine (ω ℏ E t t' : ℝ) (hℏ : ℏ ≠ 0) :
    clockProjectorAllowance ω ℏ E t t' = 4 * |Real.sin (ω * (t - t') / 2)| := by
  rw [clockProjectorAllowance_eq_phase ω ℏ E t t' hℏ, norm_phase_sub_eq, mul_sub]
  ring

theorem clockProjectorAllowance_le_time (ω ℏ E t t' : ℝ) (hℏ : ℏ ≠ 0) :
    clockProjectorAllowance ω ℏ E t t' ≤ 2 * |ω| * |t - t'| := by
  rw [clockProjectorAllowance_eq_sine ω ℏ E t t' hℏ]
  calc
    _ ≤ 4 * |ω * (t - t') / 2| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = _ := by rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring

/-- A common modular shift bound gives a quantitative constant on every decision. -/
theorem StoppingSchedule.localErrorBound_uniformTimeShift (ω ℏ E β : ℝ) (A : Type*)
    [Fintype A] [DecidableEq A] (hℏ : ℏ ≠ 0) (S : StoppingSchedule)
    (shift : List (Fin 3) → ℝ) (δ : ℝ) (hshift : ∀ r, |shift r| ≤ δ) :
    S.LocalErrorBound (S.clockPolicy ω ℏ E β A shift) (S.clockPolicy ω ℏ E β A (fun _ => 0))
      (S.uniformAllowance (2 * |ω| * |β * ℏ| * δ)) := by
  induction S generalizing shift with
  | done => trivial
  | measure s next ih =>
    refine ⟨?_, fun a => ih a (fun pre => shift (a :: pre)) (fun pre => hshift (a :: pre))⟩
    intro Y hY
    simp only [StoppingSchedule.clockPolicy, StoppingSchedule.uniformAllowance, add_zero]
    have horig := clockInstrument_lift_localError_le ω ℏ E (-β * ℏ * (s + shift []))
      (-β * ℏ * s) A hY
    refine horig.trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · refine (clockProjectorAllowance_le_time ω ℏ E _ _ hℏ).trans ?_
      rw [show -β * ℏ * (s + shift []) - (-β * ℏ * s) = (-(β * ℏ)) * shift [] by ring,
        abs_mul, abs_neg, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (hshift []) (by positivity)
    · rw [← traceNorm_posSemidef hY]
      exact traceNorm_nonneg Y

/-- Bounded modular clock shifts give a terminal-state error proportional
to the nominal duration's first moment. For a normalized reference this
moment equals the mean number of clock measurements. -/
theorem StoppingSchedule.shiftedClock_leaf_error_le_timeBound (ω ℏ E β : ℝ) (A : Type*)
    [Fintype A] [DecidableEq A] (hℏ : ℏ ≠ 0) (S : StoppingSchedule)
    (shift : List (Fin 3) → ℝ) (δ : ℝ) (hshift : ∀ r, |shift r| ≤ δ)
    {X Y : Matrix (Level × A) (Level × A) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (∑ r : S.Record, QuantumNetwork.traceNorm
      (S.leafState (S.clockPolicy ω ℏ E β A shift) r X -
        ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y)) ≤
      QuantumNetwork.traceNorm (X - Y) + (2 * |ω| * |β * ℏ| * δ) *
        ∑ b : Fin (S.height + 1), (b.val : ℝ) * ((S.durationInstrument ω ℏ E β).lift A).weight b Y := by
  exact S.shiftedClock_leaf_error_le_meanDuration ω ℏ E β A shift _
    (S.localErrorBound_uniformTimeShift ω ℏ E β A hℏ shift δ hshift) hX hY

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
