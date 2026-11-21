import SKEFTHawking.StoppingRetainedClockReadoutStability

/-! Optimal binary decisions for the stopped-clock outputs with arbitrary prior weights. -/

noncomputable section
open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.QuantumNetwork

/-- Binary success for prior-weighted finite output families. -/
def finite_binary_success {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
    (P Q E : R → Matrix ι ι ℂ) : ℝ :=
  (∑ r, (P r * E r).trace.re) + (∑ r, (Q r * (1 - E r)).trace.re)

/-- The optimal binary decision after seeing a record. The traces of the
two prior-weighted output families sum to one. -/
theorem finite_binary_success_optimal {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
    (P Q : R → Matrix ι ι ℂ) (hP : ∀ r, (P r).PosSemidef) (hQ : ∀ r, (Q r).PosSemidef)
    (htrace : (∑ r, (P r).trace.re) + (∑ r, (Q r).trace.re) = 1) :
    (∀ E : R → Matrix ι ι ℂ, (∀ r, (E r).PosSemidef) → (∀ r, (1 - E r).PosSemidef) →
      finite_binary_success P Q E ≤ (1 + ∑ r, traceNorm (P r - Q r)) / 2) ∧
    (∃ E : R → Matrix ι ι ℂ, (∀ r, (E r).PosSemidef) ∧ (∀ r, (1 - E r).PosSemidef) ∧
      finite_binary_success P Q E = (1 + ∑ r, traceNorm (P r - Q r)) / 2) := by
  let Z (r : R) := P r - Q r
  have hZ (r) : (Z r).IsHermitian := (hP r).isHermitian.sub (hQ r).isHermitian
  have hs (E : R → Matrix ι ι ℂ) :
      finite_binary_success P Q E = (∑ r, (Z r * E r).trace.re) + ∑ r, (Q r).trace.re := by
    simp only [finite_binary_success, Z, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Matrix.trace_sub, Complex.sub_re, Finset.sum_sub_distrib]
    ring
  have hz : (∑ r, (Z r).trace.re) = (∑ r, (P r).trace.re) - ∑ r, (Q r).trace.re := by
    simp only [Z, Matrix.trace_sub, Complex.sub_re, Finset.sum_sub_distrib]
  constructor
  · intro E hp hi
    have h := (abs_le.mp (finite_effect_score_centered_abs_le_half Z E hZ hp hi)).2
    rw [hz] at h
    rw [hs]
    change _ ≤ (1 + ∑ r, traceNorm (Z r)) / 2
    linarith
  · obtain ⟨E,hE,hI,h⟩ := finite_effect_score_attains_centered Z hZ
    refine ⟨E,hE,hI,?_⟩
    rw [hz] at h
    rw [hs, h]
    change _ = (1 + ∑ r, traceNorm (Z r)) / 2
    linarith

end SKEFTHawking.QuantumNetwork

namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
open QuantumNetwork

/-- Optimal success for discriminating the shifted and nominal retained-clock
outputs with a specified prior for the shifted hypothesis. -/
theorem StoppingSchedule.shiftedClock_binary_success_optimal (ω ℏ E β : ℝ) (A : Type*)
    [Fintype A] [DecidableEq A] (S : StoppingSchedule) (shift : List (Fin 3) → ℝ)
    {X Y : Matrix (Level × A) (Level × A) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htX : X.trace.re = 1) (htY : Y.trace.re = 1) (prior : ℝ)
    (hlo : 0 ≤ prior) (hhi : prior ≤ 1) :
    let P (r : S.Record) := (prior : ℂ) • S.leafState (S.clockPolicy ω ℏ E β A shift) r X
    let Q (r : S.Record) := ((1 - prior : ℝ) : ℂ) •
      ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y
    (∀ F : S.Record → Matrix (Level × A) (Level × A) ℂ,
      (∀ r, (F r).PosSemidef) → (∀ r, (1 - F r).PosSemidef) →
      finite_binary_success P Q F ≤ (1 + ∑ r, QuantumNetwork.traceNorm (P r - Q r)) / 2) ∧
    (∃ F : S.Record → Matrix (Level × A) (Level × A) ℂ,
      (∀ r, (F r).PosSemidef) ∧ (∀ r, (1 - F r).PosSemidef) ∧
      finite_binary_success P Q F = (1 + ∑ r, QuantumNetwork.traceNorm (P r - Q r)) / 2) := by
  intro P Q
  have hloC := Complex.zero_le_real.mpr hlo
  have hhiC := Complex.zero_le_real.mpr (sub_nonneg.mpr hhi)
  have hQ (r : S.Record) :
      Q r = ((1 - prior : ℝ) : ℂ) •
        S.leafState (S.clockPolicy ω ℏ E β A (fun _ => 0)) r Y := by
    rw [S.zero_clockPolicy_leafState ω ℏ E β A r Y]
  refine finite_binary_success_optimal P Q (fun r => (S.leafState_posSemidef _ r hX).smul hloC)
    (fun r => hQ r ▸ (S.leafState_posSemidef _ r hY).smul hhiC) ?_
  simp_rw [hQ]
  simp only [P, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, ← Finset.mul_sum, S.sum_leafState_trace,
    htX, htY, mul_one, add_sub_cancel]


/-- Equal-prior discrimination advantage is controlled by the time-shift budget. -/
theorem StoppingSchedule.shiftedClock_equalPrior_success_le (ω ℏ E β : ℝ) (A : Type*)
    [Fintype A] [DecidableEq A] (hℏ : ℏ ≠ 0) (S : StoppingSchedule)
    (shift : List (Fin 3) → ℝ) (δ : ℝ) (hshift : ∀ r, |shift r| ≤ δ)
    {X Y : Matrix (Level × A) (Level × A) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htX : X.trace.re = 1) (htY : Y.trace.re = 1)
    (F : S.Record → Matrix (Level × A) (Level × A) ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hI : ∀ r, (1 - F r).PosSemidef) :
    let P (r : S.Record) := S.leafState (S.clockPolicy ω ℏ E β A shift) r X
    let Q (r : S.Record) := ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y
    finite_binary_success
      (fun r => (((1 / 2 : ℝ) : ℂ)) • P r)
      (fun r => (((1 / 2 : ℝ) : ℂ)) • Q r) F ≤
      1 / 2 + (QuantumNetwork.traceNorm (X - Y) + (2 * |ω| * |β * ℏ| * δ) *
        ∑ b : Fin (S.height + 1), (b.val : ℝ) * ((S.durationInstrument ω ℏ E β).lift A).weight b Y) / 4 := by
  intro P Q
  have hn : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
  have hb := (S.shiftedClock_binary_success_optimal ω ℏ E β A shift hX hY htX htY
    (1 / 2 : ℝ) (by norm_num) (by norm_num)).1 F hF hI
  simp only [hn] at hb
  have scale (W : Matrix (Level × A) (Level × A) ℂ) :
      QuantumNetwork.traceNorm (((1 / 2 : ℝ) : ℂ) • W) = (1 / 2 : ℝ) * QuantumNetwork.traceNorm W := by
    simp only [traceNorm_eq_physlib, Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simp only [← smul_sub, scale, ← Finset.mul_sum] at hb
  have hnorm := S.shiftedClock_leaf_error_le_timeBound ω ℏ E β A hℏ shift δ hshift hX hY
  linarith

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
