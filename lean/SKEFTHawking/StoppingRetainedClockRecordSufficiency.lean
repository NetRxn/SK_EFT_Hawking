import SKEFTHawking.StoppingRetainedClockRecordDecision

/-!
# Sufficiency of terminal clock records

The record alone is sufficient for binary readout exactly when the two
prior-weighted terminal states are comparable in the positive semidefinite
order at each record.
-/

noncomputable section
open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.QuantumNetwork

/-- The terminal record by itself is sufficient exactly when one weighted
hypothesis dominates the other as an operator at each record. -/
theorem finite_binary_record_optimum_eq_effect_optimum_iff {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (P Q : R → Matrix ι ι ℂ) (hZ : ∀ r, (P r - Q r).IsHermitian) :
    (1 + ∑ r, traceNorm (P r - Q r)) / 2 =
      (1 + ∑ r, |(P r).trace.re - (Q r).trace.re|) / 2 ↔
    ∀ r, (P r - Q r).PosSemidef ∨ (Q r - P r).PosSemidef := by
  have hz {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (ht : A.trace.re = 0) : A = 0 := by
    apply hA.trace_eq_zero_iff.mp
    apply Complex.ext
    · simpa only [Complex.zero_re] using ht
    · exact (Complex.le_def.mp hA.trace_nonneg).2.symm
  have hn {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : 0 ≤ A.trace.re :=
    (Complex.le_def.mp hA.trace_nonneg).1
  constructor
  · intro h r
    have hsum : (∑ r, min (posPart (hZ r)).trace.re (negPart (hZ r)).trace.re) = 0 := by
      rw [← finite_binary_effect_optimum_sub_record_optimum P Q hZ, h, sub_self]
    have hm := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ =>
      le_min (hn (posPart_posSemidef (hZ t))) (hn (negPart_posSemidef (hZ t))))).mp hsum
      r (Finset.mem_univ r)
    have hdecomp := self_eq_posPart_sub_negPart (hZ r)
    rcases le_total (posPart (hZ r)).trace.re (negPart (hZ r)).trace.re with hpos | hneg
    · refine Or.inr ?_
      rw [min_eq_left hpos] at hm
      rw [hz (posPart_posSemidef (hZ r)) hm, zero_sub] at hdecomp
      have he := congrArg Neg.neg hdecomp
      rw [neg_sub, neg_neg] at he
      rw [he]
      exact negPart_posSemidef _
    · refine Or.inl ?_
      rw [min_eq_right hneg] at hm
      rw [hz (negPart_posSemidef (hZ r)) hm, sub_zero] at hdecomp
      rw [hdecomp]
      exact posPart_posSemidef _
  · intro h
    suffices he : (∑ r, traceNorm (P r - Q r)) =
        ∑ r, |(P r).trace.re - (Q r).trace.re| by rw [he]
    apply Finset.sum_congr rfl
    intro r _
    rcases h r with hp | hq
    · rw [← Complex.sub_re, ← Matrix.trace_sub, traceNorm_posSemidef hp, abs_of_nonneg (hn hp)]
    · rw [← abs_sub_comm, ← Complex.sub_re, ← Matrix.trace_sub,
        ← traceNorm_neg (P r - Q r), neg_sub, traceNorm_posSemidef hq, abs_of_nonneg (hn hq)]

end SKEFTHawking.QuantumNetwork

namespace SKEFTHawking.QuantumNetwork

/-- One record rule matches every allowed joint readout exactly when the two
prior-weighted branch outputs are comparable at every record. -/
theorem finite_binary_record_sufficient_iff {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (P Q : R → Matrix ι ι ℂ) (hP : ∀ r, (P r).PosSemidef) (hQ : ∀ r, (Q r).PosSemidef)
    (htrace : (∑ r, (P r).trace.re) + (∑ r, (Q r).trace.re) = 1) :
    (∃ d : R → Bool, ∀ F : R → Matrix ι ι ℂ,
      (∀ r, (F r).PosSemidef) → (∀ r, (1 - F r).PosSemidef) →
      finite_binary_success P Q F ≤ finite_binary_record_success P Q d) ↔
    ∀ r, (P r - Q r).PosSemidef ∨ (Q r - P r).PosSemidef := by
  let C := (1 + ∑ r, |(P r).trace.re - (Q r).trace.re|) / 2
  let J := (1 + ∑ r, traceNorm (P r - Q r)) / 2
  have heq : J = C ↔ ∀ r, (P r - Q r).PosSemidef ∨ (Q r - P r).PosSemidef :=
    finite_binary_record_optimum_eq_effect_optimum_iff P Q
      (fun r => (hP r).isHermitian.sub (hQ r).isHermitian)
  have hr := finite_binary_record_success_optimal P Q htrace
  have hj := finite_binary_success_optimal P Q hP hQ htrace
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨F, hF, hI, hval⟩ := hj.2
    have hJC : J ≤ C := by
      have hs := (hd F hF hI).trans (hr.1 d)
      rw [hval] at hs
      exact hs
    exact heq.mp (le_antisymm hJC (finite_binary_record_optimum_le_effect_optimum P Q hP hQ))
  · intro h
    obtain ⟨d, hd⟩ := hr.2
    refine ⟨d, fun F hF hI => ?_⟩
    exact (hj.1 F hF hI).trans_eq ((heq.mpr h).trans hd.symm)

end SKEFTHawking.QuantumNetwork

namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock

open QuantumNetwork

/-- For the actual stopped-clock outputs, the terminal record is sufficient
precisely when the two weighted leaves are ordered at each record. -/
theorem StoppingSchedule.shiftedClock_record_sufficient_iff (ω ℏ E β : ℝ) (A : Type*)
    [Fintype A] [DecidableEq A] (S : StoppingSchedule) (shift : List (Fin 3) → ℝ)
    {X Y : Matrix (Level × A) (Level × A) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htX : X.trace.re = 1) (htY : Y.trace.re = 1)
    (prior : ℝ) (hlo : 0 ≤ prior) (hhi : prior ≤ 1) :
    let P (r : S.Record) := (prior : ℂ) • S.leafState (S.clockPolicy ω ℏ E β A shift) r X
    let Q (r : S.Record) := ((1 - prior : ℝ) : ℂ) •
      ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y
    (∃ d : S.Record → Bool, ∀ F : S.Record → Matrix (Level × A) (Level × A) ℂ,
      (∀ r, (F r).PosSemidef) → (∀ r, (1 - F r).PosSemidef) →
      finite_binary_success P Q F ≤ finite_binary_record_success P Q d) ↔
    ∀ r, (P r - Q r).PosSemidef ∨ (Q r - P r).PosSemidef := by
  intro P Q
  have hpos := (S.shiftedClock_record_success_optimal ω ℏ E β A shift hX hY htX htY prior hlo hhi).1
  have hQ (r : S.Record) :
      Q r = ((1 - prior : ℝ) : ℂ) •
        S.leafState (S.clockPolicy ω ℏ E β A (fun _ => 0)) r Y := by
    rw [S.zero_clockPolicy_leafState ω ℏ E β A r Y]
  apply finite_binary_record_sufficient_iff P Q (fun r => (hpos r).1) (fun r => (hpos r).2)
  simp_rw [hQ]
  simp only [P, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, ← Finset.mul_sum, S.sum_leafState_trace,
    htX, htY, mul_one, add_sub_cancel]

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
