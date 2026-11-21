import SKEFTHawking.StoppingRetainedClockBinaryDecision
import SKEFTHawking.QuantumNetwork.NegativityGeneral
import SKEFTHawking.QuantumNetwork.BinaryMemoryFixture

/-!
# Record-only and quantum readout of a stopped clock

The smaller signed spectral mass at each record is the contribution of the
conditional quantum state to the optimal readout. A spectator memory gives
an exact separation on the actual finite stopping experiment.
-/


noncomputable section
open Matrix
open scoped ComplexOrder Kronecker

namespace SKEFTHawking.QuantumNetwork

/-- The score of a deterministic binary decision using only the retained record. -/
def finite_binary_record_success {ι R : Type*} [Fintype ι] [Fintype R]
    (P Q : R → Matrix ι ι ℂ) (d : R → Bool) : ℝ :=
  ∑ r, if d r then (P r).trace.re else (Q r).trace.re

/-- Record-only decisions use the identity effect or zero for each record. -/
theorem finite_binary_success_record_only {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (P Q : R → Matrix ι ι ℂ) (d : R → Bool) :
    finite_binary_success P Q (fun r => if d r then 1 else 0) =
      finite_binary_record_success P Q d := by
  rw [finite_binary_success, finite_binary_record_success, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  cases d r <;> simp

private theorem sum_max_trace_eq_of_total_trace_one {ι R : Type*}
    [Fintype ι] [Fintype R] (P Q : R → Matrix ι ι ℂ)
    (htrace : (∑ r, (P r).trace.re) + (∑ r, (Q r).trace.re) = 1) :
    (∑ r, max (P r).trace.re (Q r).trace.re) =
      (1 + ∑ r, |(P r).trace.re - (Q r).trace.re|) / 2 := by
  calc
    _ = ∑ r, ((P r).trace.re + (Q r).trace.re +
        |(P r).trace.re - (Q r).trace.re|) / 2 := by
      apply Finset.sum_congr rfl
      intro r _
      rcases le_total (Q r).trace.re (P r).trace.re with h | h
      · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
      · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
    _ = _ := by simp only [← Finset.sum_div, Finset.sum_add_distrib, htrace]

/-- The exact attainable record-only success uses the absolute trace
difference at each record. -/
theorem finite_binary_record_success_optimal {ι R : Type*}
    [Fintype ι] [Fintype R] (P Q : R → Matrix ι ι ℂ)
    (htrace : (∑ r, (P r).trace.re) + (∑ r, (Q r).trace.re) = 1) :
    (∀ d : R → Bool, finite_binary_record_success P Q d ≤
      (1 + ∑ r, |(P r).trace.re - (Q r).trace.re|) / 2) ∧
    (∃ d : R → Bool, finite_binary_record_success P Q d =
      (1 + ∑ r, |(P r).trace.re - (Q r).trace.re|) / 2) := by
  have hsum := sum_max_trace_eq_of_total_trace_one P Q htrace
  constructor
  · intro d
    rw [← hsum, finite_binary_record_success]
    apply Finset.sum_le_sum
    intro r _
    cases d r <;> simp
  · classical
    let d : R → Bool := fun r => decide ((Q r).trace.re ≤ (P r).trace.re)
    refine ⟨d, ?_⟩
    rw [← hsum, finite_binary_record_success]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : (Q r).trace.re ≤ (P r).trace.re
    · simp [d, h]
    · simp [d, h, max_eq_right (le_of_not_ge h)]

/-- Randomizing a decision on the same record cannot improve the optimum. -/
theorem finite_binary_randomized_record_success_le {ι R : Type*}
    [Fintype ι] [Fintype R] (P Q : R → Matrix ι ι ℂ)
    (htrace : (∑ r, (P r).trace.re) + (∑ r, (Q r).trace.re) = 1)
    (p : R → ℝ) (hlo : ∀ r, 0 ≤ p r) (hhi : ∀ r, p r ≤ 1) :
    (∑ r : R, (p r * (P r).trace.re + (1 - p r) * (Q r).trace.re)) ≤
      (1 + ∑ r, |(P r).trace.re - (Q r).trace.re|) / 2 := by
  rw [← sum_max_trace_eq_of_total_trace_one P Q htrace]
  apply Finset.sum_le_sum
  intro r _
  let m := max (P r).trace.re (Q r).trace.re
  calc
    _ ≤ p r * m + (1 - p r) * m := add_le_add
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (hlo r))
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr (hhi r)))
    _ = m := by ring

/-- The record-only optimum cannot exceed the optimum with access to the
conditional quantum output. -/
theorem finite_binary_record_optimum_le_effect_optimum {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (P Q : R → Matrix ι ι ℂ) (hP : ∀ r, (P r).PosSemidef) (hQ : ∀ r, (Q r).PosSemidef) :
    (1 + ∑ r, |(P r).trace.re - (Q r).trace.re|) / 2 ≤
      (1 + ∑ r, traceNorm (P r - Q r)) / 2 := by
  have hsum : (∑ r, |(P r).trace.re - (Q r).trace.re|) ≤
      ∑ r, traceNorm (P r - Q r) := Finset.sum_le_sum (fun r _ => by
    simpa only [Matrix.trace_sub, Complex.sub_re] using
      traceNorm_ge_abs_re_trace ((hP r).isHermitian.sub (hQ r).isHermitian))
  linarith only [hsum]

/-- The gain from retaining the conditional quantum output is the sum of
the smaller signed spectral masses at each record. -/
theorem finite_binary_effect_optimum_sub_record_optimum {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (P Q : R → Matrix ι ι ℂ) (hZ : ∀ r, (P r - Q r).IsHermitian) :
    (1 + ∑ r, traceNorm (P r - Q r)) / 2 -
      (1 + ∑ r, |(P r).trace.re - (Q r).trace.re|) / 2 =
    ∑ r, min (posPart (hZ r)).trace.re (negPart (hZ r)).trace.re := by
  calc
    _ = ((∑ r, traceNorm (P r - Q r)) -
        (∑ r, |(P r).trace.re - (Q r).trace.re|)) / 2 := by ring
    _ = _ := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      have ht : (P r).trace.re - (Q r).trace.re =
          (posPart (hZ r)).trace.re - (negPart (hZ r)).trace.re := by
        simpa only [Matrix.trace_sub, Complex.sub_re] using
          congrArg (fun M : Matrix ι ι ℂ => M.trace.re) (self_eq_posPart_sub_negPart (hZ r))
      rw [traceNorm_hermitian_eq_pos_add_neg (hZ r), ht]
      rcases le_total (posPart (hZ r)).trace.re (negPart (hZ r)).trace.re with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring

end SKEFTHawking.QuantumNetwork



namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock

open Matrix QuantumNetwork

/-- Optimal success for the same stopped-clock discrimination task when the
decision can use the terminal record alone. -/
theorem StoppingSchedule.shiftedClock_record_success_optimal (ω ℏ E β : ℝ) (A : Type*)
    [Fintype A] [DecidableEq A] (S : StoppingSchedule) (shift : List (Fin 3) → ℝ)
    {X Y : Matrix (Level × A) (Level × A) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htX : X.trace.re = 1) (htY : Y.trace.re = 1)
    (prior : ℝ) (hlo : 0 ≤ prior) (hhi : prior ≤ 1) :
    let P (r : S.Record) := (prior : ℂ) • S.leafState (S.clockPolicy ω ℏ E β A shift) r X
    let Q (r : S.Record) := ((1 - prior : ℝ) : ℂ) •
      ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y
    (∀ r : S.Record, (P r).PosSemidef ∧ (Q r).PosSemidef) ∧
    (∀ d : S.Record → Bool, finite_binary_record_success P Q d ≤
      (1 + ∑ r, |(P r).trace.re - (Q r).trace.re|) / 2) ∧
    (∃ d : S.Record → Bool, finite_binary_record_success P Q d =
      (1 + ∑ r, |(P r).trace.re - (Q r).trace.re|) / 2) := by
  intro P Q
  have hQ (r : S.Record) :
      Q r = ((1 - prior : ℝ) : ℂ) •
        S.leafState (S.clockPolicy ω ℏ E β A (fun _ => 0)) r Y := by
    rw [S.zero_clockPolicy_leafState ω ℏ E β A r Y]
  refine ⟨?_, finite_binary_record_success_optimal P Q ?_⟩
  · intro r
    rw [hQ]
    exact ⟨(S.leafState_posSemidef _ r hX).smul (Complex.zero_le_real.mpr hlo),
      (S.leafState_posSemidef _ r hY).smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hhi))⟩
  simp_rw [hQ]
  simp only [P, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, ← Finset.mul_sum, S.sum_leafState_trace,
    htX, htY, mul_one, add_sub_cancel]

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock

namespace SKEFTHawking.QuantumNetwork

/-- A spectator lift acts only on the first factor of a product input. -/
theorem FiniteInstrument.lift_branch_kronecker {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] {n : ℕ} (I : FiniteInstrument ι n) (b : Fin n)
    (X : Matrix ι ι ℂ) (Y : Matrix A A ℂ) :
    (I.lift A).branch b (X ⊗ₖ Y) = I.branch b X ⊗ₖ Y := by
  simp only [FiniteInstrument.branch, krausMap, FiniteInstrument.lift,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
  rfl

private theorem binaryDiagonalState_one_mul_effect :
    binaryDiagonalState 1 * binaryOneEffect = binaryDiagonalState 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryDiagonalState, binaryOneEffect]

private theorem binaryDiagonalState_zero_mul_complement :
    binaryDiagonalState 0 * (1 - binaryOneEffect) = binaryDiagonalState 0 := by
  have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) - binaryOneEffect = binaryDiagonalState 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [binaryDiagonalState, binaryOneEffect]
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryDiagonalState]

end SKEFTHawking.QuantumNetwork

namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
open QuantumNetwork

/-- With identical clock inputs and orthogonal spectator memories, every
terminal-record decision succeeds with probability one half. Joint access
can recover the input memory perfectly at any finite stopping schedule. -/
theorem StoppingSchedule.spectator_readout_separation (S : StoppingSchedule)
    (ω ℏ E β : ℝ) (ρ : Mat) (hρ : IsDensityOperator ρ) :
    let P (r : S.Record) := ((1 / 2 : ℝ) : ℂ) •
      S.leafState (S.clockPolicy ω ℏ E β (Fin 2) (fun _ => 0)) r
        (ρ ⊗ₖ binaryDiagonalState 1)
    let Q (r : S.Record) := ((1 / 2 : ℝ) : ℂ) •
      ((S.instrument ω ℏ E β).lift (Fin 2)).branch (S.recordEquiv r)
        (ρ ⊗ₖ binaryDiagonalState 0)
    (∀ r : S.Record, (P r).PosSemidef ∧ (Q r).PosSemidef) ∧
    (∀ d : S.Record → Bool, finite_binary_record_success P Q d = 1 / 2) ∧
    (∃ F : Matrix (Level × Fin 2) (Level × Fin 2) ℂ,
      IsBinaryPOVM F ∧ finite_binary_success P Q (fun _ => F) = 1) := by
  intro P Q
  let I := S.instrument ω ℏ E β
  let B (r : S.Record) := I.branch (S.recordEquiv r) ρ
  let F := (1 : Matrix Level Level ℂ) ⊗ₖ binaryOneEffect
  have hP (r : S.Record) : P r = ((1 / 2 : ℝ) : ℂ) • (B r ⊗ₖ binaryDiagonalState 1) := by
    dsimp only [P, B, I]
    rw [S.zero_clockPolicy_leafState ω ℏ E β (Fin 2) r (ρ ⊗ₖ binaryDiagonalState 1)]
    rw [FiniteInstrument.lift_branch_kronecker]
  have hQ (r : S.Record) : Q r = ((1 / 2 : ℝ) : ℂ) • (B r ⊗ₖ binaryDiagonalState 0) := by
    dsimp only [Q, B, I]
    rw [FiniteInstrument.lift_branch_kronecker]
  have ht₁ := (binaryDiagonalState_density (r := 1) ⟨by norm_num, le_rfl⟩).2
  have ht₀ := (binaryDiagonalState_density (r := 0) ⟨le_rfl, by norm_num⟩).2
  have hc : 1 - F = (1 : Matrix Level Level ℂ) ⊗ₖ (1 - binaryOneEffect) := by
    rw [show (1 : Matrix (Level × Fin 2) (Level × Fin 2) ℂ) =
      (1 : Matrix Level Level ℂ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) from
      Matrix.one_kronecker_one.symm]
    ext i j
    simp only [F, Matrix.sub_apply, Matrix.kroneckerMap_apply, mul_sub]
  have hf : IsBinaryPOVM F := by
    refine ⟨Matrix.PosSemidef.one.kronecker binaryOneEffect_isBinaryPOVM.1, ?_⟩
    rw [hc]
    exact Matrix.PosSemidef.one.kronecker binaryOneEffect_isBinaryPOVM.2
  have ht : (∑ r : S.Record, (B r).trace.re) = 1 := by
    have htC : (∑ r : S.Record, (B r).trace) = ρ.trace :=
      (S.recordEquiv.sum_comp fun b => (I.branch b ρ).trace).trans (I.sum_trace ρ)
    rw [← Complex.re_sum, htC, hρ.2]
    norm_num
  have htrace_tensor (U : Mat) (V : Matrix (Fin 2) (Fin 2) ℂ) (hV : V.trace = 1) :
      (((((1 / 2 : ℝ) : ℂ) • (U ⊗ₖ V))).trace).re = (1 / 2 : ℝ) * U.trace.re := by
    rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_kronecker, hV, mul_one]
    simp only [Complex.re_ofReal_mul]
  have htraceP (r : S.Record) : (P r).trace.re = (1 / 2 : ℝ) * (B r).trace.re := by
    rw [hP, htrace_tensor _ _ ht₁]
  have htraceQ (r : S.Record) : (Q r).trace.re = (1 / 2 : ℝ) * (B r).trace.re := by
    rw [hQ, htrace_tensor _ _ ht₀]
  have hmP (r : S.Record) : (P r * F).trace.re = (1 / 2 : ℝ) * (B r).trace.re := by
    rw [hP, smul_mul_assoc]
    dsimp only [F]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, binaryDiagonalState_one_mul_effect,
      htrace_tensor _ _ ht₁]
  have hmQ (r : S.Record) : (Q r * (1 - F)).trace.re = (1 / 2 : ℝ) * (B r).trace.re := by
    rw [hQ, hc, smul_mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      binaryDiagonalState_zero_mul_complement, htrace_tensor _ _ ht₀]
  refine ⟨?_, ?_, ?_⟩
  · intro r
    rw [hP, hQ]
    have hb := I.branch_posSemidef (S.recordEquiv r) hρ.1
    have nonneg : (0 : ℂ) ≤ ((1 / 2 : ℝ) : ℂ) :=
      Complex.zero_le_real.mpr (by norm_num)
    exact ⟨(hb.kronecker (binaryDiagonalState_density (r := 1) ⟨by norm_num, le_rfl⟩).1).smul nonneg,
      (hb.kronecker (binaryDiagonalState_density (r := 0) ⟨le_rfl, by norm_num⟩).1).smul nonneg⟩
  · intro d
    unfold finite_binary_record_success
    simp_rw [htraceP, htraceQ, ite_self, ← Finset.mul_sum, ht, mul_one]
  · refine ⟨F, hf, ?_⟩
    simp only [finite_binary_success, hmP, hmQ, ← Finset.mul_sum, ht, mul_one]
    norm_num

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
