import SKEFTHawking.StoppingRetainedClockTimeShift
import SKEFTHawking.QuantumNetwork.FidelityBounds

/-! Operational readout stability for the retained clock, allowing a measurement
effect to depend on the terminal record and to act on a joint output. -/

noncomputable section
open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.QuantumNetwork

/-- The centered score of effects on Hermitian errors is bounded by half
the sum of the branch trace norms. -/
theorem finite_effect_score_centered_abs_le_half {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
    (Z E : R → Matrix ι ι ℂ) (hZ : ∀ r, (Z r).IsHermitian)
    (hE : ∀ r, (E r).PosSemidef) (hI : ∀ r, (1 - E r).PosSemidef) :
    |(∑ r, (Z r * E r).trace.re) - (∑ r, (Z r).trace.re) / 2| ≤
      (∑ r, traceNorm (Z r)) / 2 := by
  let C (r : R) := E r + E r - 1
  have hsub (r) : (1 - C r).PosSemidef := by
    have he : (1 : Matrix ι ι ℂ) - C r = (1 - E r) + (1 - E r) := by dsimp [C]; abel
    rw [he]
    exact (hI r).add (hI r)
  have hadd (r) : (1 + C r).PosSemidef := by
    have he : (1 : Matrix ι ι ℂ) + C r = E r + E r := by dsimp [C]; abel
    rw [he]
    exact (hE r).add (hE r)
  have hpoint (r) : |(Z r * C r).trace.re| ≤ traceNorm (Z r) := by
    apply abs_le.mpr
    refine ⟨?_, re_trace_mul_le_traceNorm_hermitian (hZ r) (hsub r) (hadd r)⟩
    have h := re_trace_mul_le_traceNorm_hermitian (hZ r) (R := -C r)
      (by simpa only [sub_neg_eq_add] using hadd r) (by simpa only [sub_eq_add_neg] using hsub r)
    simp only [Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re] at h
    linarith
  have hscore : (∑ r, (Z r * C r).trace.re) =
      2 * ((∑ r, (Z r * E r).trace.re) - (∑ r, (Z r).trace.re) / 2) := by
    simp only [C, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_add, Complex.sub_re, Complex.add_re, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    ring
  have h := (Finset.abs_sum_le_sum_abs (fun r => (Z r * C r).trace.re) Finset.univ).trans
    (Finset.sum_le_sum (fun r _ => hpoint r))
  rw [hscore, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
  linarith

/-- A family of record-dependent effects attains the positive centered bound. -/
theorem finite_effect_score_attains_centered {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
    (Z : R → Matrix ι ι ℂ) (hZ : ∀ r, (Z r).IsHermitian) :
    ∃ E : R → Matrix ι ι ℂ, (∀ r, (E r).PosSemidef) ∧ (∀ r, (1 - E r).PosSemidef) ∧
      (∑ r, (Z r * E r).trace.re) =
        ((∑ r, (Z r).trace.re) + (∑ r, traceNorm (Z r))) / 2 := by
  let E (r : R) := (((1 / 2 : ℝ) : ℂ)) • (1 + signOp (hZ r))
  have hhalf : (0 : ℂ) ≤ ((1 / 2 : ℝ) : ℂ) := by
    rw [Complex.zero_le_real]
    norm_num
  refine ⟨E, fun r => (one_add_signOp_posSemidef (hZ r)).smul hhalf, ?_, ?_⟩
  · intro r
    have he : 1 - E r = (((1 / 2 : ℝ) : ℂ)) • (1 - signOp (hZ r)) := by
      ext i j
      simp only [E, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [he]
    exact (one_sub_signOp_posSemidef (hZ r)).smul hhalf
  · have hE (r : R) :
        (Z r * E r).trace.re = (1 / 2 : ℝ) * ((Z r).trace.re + traceNorm (Z r)) := by
      simp only [E, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, self_mul_signOp,
        Matrix.trace_smul, smul_eq_mul, Matrix.trace_add, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re]
      rw [traceNorm_hermitian_eq_pos_add_neg]
    simp only [hE, ← Finset.mul_sum, Finset.sum_add_distrib]
    ring


/-- The score of a finite family of effects on Hermitian errors of zero total
trace is bounded by half the sum of the branch trace norms. -/
theorem finite_effect_score_abs_le_half {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
    (Z E : R → Matrix ι ι ℂ) (hZ : ∀ r, (Z r).IsHermitian)
    (hE : ∀ r, (E r).PosSemidef) (hI : ∀ r, (1 - E r).PosSemidef)
    (htrace : ∑ r, (Z r).trace.re = 0) :
    |∑ r, (Z r * E r).trace.re| ≤ (∑ r, traceNorm (Z r)) / 2 := by
  simpa only [htrace, zero_div, sub_zero] using
    finite_effect_score_centered_abs_le_half Z E hZ hE hI

/-- The half trace-norm bound is attained by a record-dependent effect. -/
theorem finite_effect_score_attains_half {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
    (Z : R → Matrix ι ι ℂ) (hZ : ∀ r, (Z r).IsHermitian)
    (htrace : ∑ r, (Z r).trace.re = 0) :
    ∃ E : R → Matrix ι ι ℂ, (∀ r, (E r).PosSemidef) ∧ (∀ r, (1 - E r).PosSemidef) ∧
      (∑ r, (Z r * E r).trace.re) = (∑ r, traceNorm (Z r)) / 2 := by
  simpa only [htrace, zero_add] using finite_effect_score_attains_centered Z hZ

end SKEFTHawking.QuantumNetwork

namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock

open QuantumNetwork

theorem StoppingSchedule.leafState_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : StoppingSchedule) (P : S.Instruments ι) (r : S.Record) {X : Matrix ι ι ℂ}
    (hX : X.PosSemidef) : (S.leafState P r X).PosSemidef := by
  induction S generalizing X with
  | done => exact hX
  | measure s next ih =>
    exact ih r.1 (P.2 r.1) r.2 (P.1.branch_posSemidef r.1 hX)

/-- A record-dependent effect on the stopped output has an operational
probability bound under the uniform time perturbation. -/
theorem StoppingSchedule.shiftedClock_effect_error_le_timeBound (ω ℏ E β : ℝ) (A : Type*)
    [Fintype A] [DecidableEq A] (hℏ : ℏ ≠ 0) (S : StoppingSchedule)
    (shift : List (Fin 3) → ℝ) (δ : ℝ) (hshift : ∀ r, |shift r| ≤ δ)
    {X Y : Matrix (Level × A) (Level × A) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htrace : X.trace.re = Y.trace.re)
    (effect : S.Record → Matrix (Level × A) (Level × A) ℂ)
    (hp : ∀ r, (effect r).PosSemidef) (hI : ∀ r, (1 - effect r).PosSemidef) :
    let P (r : S.Record) := S.leafState (S.clockPolicy ω ℏ E β A shift) r X
    let Q (r : S.Record) := ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y
    |(∑ r, (P r * effect r).trace.re) - (∑ r, (Q r * effect r).trace.re)| ≤
      (QuantumNetwork.traceNorm (X - Y) + (2 * |ω| * |β * ℏ| * δ) *
        ∑ b : Fin (S.height + 1), (b.val : ℝ) * ((S.durationInstrument ω ℏ E β).lift A).weight b Y) / 2 := by
  intro P Q
  let Z (r : S.Record) := P r - Q r
  have hQ (r) : Q r = S.leafState (S.clockPolicy ω ℏ E β A (fun _ => 0)) r Y :=
    (S.zero_clockPolicy_leafState ω ℏ E β A r Y).symm
  have hZ (r) : (Z r).IsHermitian := by
    dsimp [Z]
    rw [hQ r]
    exact ((S.leafState_posSemidef _ r hX).isHermitian).sub
      (S.leafState_posSemidef _ r hY).isHermitian
  have hmass : ∑ r, (Z r).trace.re = 0 := by
    simp only [Z, Matrix.trace_sub, Complex.sub_re, Finset.sum_sub_distrib]
    simp_rw [hQ]
    change (∑ r, (S.leafState (S.clockPolicy ω ℏ E β A shift) r X).trace.re) - _ = 0
    rw [S.sum_leafState_trace, S.sum_leafState_trace, htrace, sub_self]
  calc
    _ = |∑ r, (Z r * effect r).trace.re| := by
      simp only [Z, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Finset.sum_sub_distrib]
    _ ≤ (∑ r, QuantumNetwork.traceNorm (Z r)) / 2 :=
      finite_effect_score_abs_le_half Z effect hZ hp hI hmass
    _ ≤ _ := div_le_div_of_nonneg_right
      (S.shiftedClock_leaf_error_le_timeBound ω ℏ E β A hℏ shift δ hshift hX hY) (by norm_num)

/-- An event of the stopped record is the special case with a zero or identity effect. -/
theorem StoppingSchedule.shiftedClock_event_error_le_timeBound (ω ℏ E β : ℝ) (A : Type*)
    [Fintype A] [DecidableEq A] (hℏ : ℏ ≠ 0) (S : StoppingSchedule)
    (shift : List (Fin 3) → ℝ) (δ : ℝ) (hshift : ∀ r, |shift r| ≤ δ)
    {X Y : Matrix (Level × A) (Level × A) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htrace : X.trace.re = Y.trace.re) (event : Finset S.Record) :
    |(∑ r ∈ event, (S.leafState (S.clockPolicy ω ℏ E β A shift) r X).trace.re) -
        (∑ r ∈ event, (((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y).trace.re)| ≤
      (QuantumNetwork.traceNorm (X - Y) + (2 * |ω| * |β * ℏ| * δ) *
        ∑ b : Fin (S.height + 1), (b.val : ℝ) * ((S.durationInstrument ω ℏ E β).lift A).weight b Y) / 2 := by
  classical
  let effect (r : S.Record) : Matrix (Level × A) (Level × A) ℂ :=
    if r ∈ event then 1 else 0
  have hp (r) : (effect r).PosSemidef := by
    by_cases h : r ∈ event
    · simpa [effect, h] using (Matrix.PosSemidef.one : (1 : Matrix (Level × A) (Level × A) ℂ).PosSemidef)
    · simpa [effect, h] using (Matrix.PosSemidef.zero : (0 : Matrix (Level × A) (Level × A) ℂ).PosSemidef)
  have hI (r) : (1 - effect r).PosSemidef := by
    by_cases h : r ∈ event
    · simpa [effect, h] using (Matrix.PosSemidef.zero : (0 : Matrix (Level × A) (Level × A) ℂ).PosSemidef)
    · simpa [effect, h] using (Matrix.PosSemidef.one : (1 : Matrix (Level × A) (Level × A) ℂ).PosSemidef)
  have he (P : S.Record → Matrix (Level × A) (Level × A) ℂ) :
      (∑ r, (P r * effect r).trace.re) = ∑ r ∈ event, (P r).trace.re := by
    have hfilter : Finset.univ.filter (fun r : S.Record => r ∈ event) = event := by
      ext r
      simp
    rw [← hfilter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : r ∈ event <;> simp [effect, h]
  have h := S.shiftedClock_effect_error_le_timeBound ω ℏ E β A hℏ shift δ hshift hX hY
    htrace effect hp hI
  simpa only [he] using h

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
