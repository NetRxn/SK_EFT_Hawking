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

/-- The balanced portion of the two priors controls the evidence gain over
guessing the more likely hypothesis. -/
theorem finite_binary_success_le_prior_guess_add {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R]
    (P Q : R → Matrix ι ι ℂ) (hP : ∀ r, (P r).PosSemidef) (hQ : ∀ r, (Q r).PosSemidef)
    (htP : (∑ r, (P r).trace.re) = 1) (htQ : (∑ r, (Q r).trace.re) = 1)
    (p : ℝ) (hlo : 0 ≤ p) (hhi : p ≤ 1)
    (E : R → Matrix ι ι ℂ) (hE : ∀ r, (E r).PosSemidef)
    (hI : ∀ r, (1 - E r).PosSemidef) :
    finite_binary_success (fun r => (p : ℂ) • P r)
      (fun r => ((1 - p : ℝ) : ℂ) • Q r) E ≤
      max p (1 - p) + min p (1 - p) * (∑ r, traceNorm (P r - Q r)) / 2 := by
  let q : ℝ := 1 - p
  have hq : 0 ≤ q := sub_nonneg.mpr hhi
  have htotal : p + q = 1 := by dsimp [q]; ring
  change finite_binary_success (fun r => (p : ℂ) • P r) (fun r => (q : ℂ) • Q r) E ≤
    max p q + min p q * (∑ r, traceNorm (P r - Q r)) / 2
  have ht :
      (∑ r, (((p : ℂ) • P r)).trace.re) + (∑ r, (((q : ℂ) • Q r)).trace.re) = 1 := by
    simp only [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      ← Finset.mul_sum, htP, htQ, mul_one, htotal]
  have hb := (finite_binary_success_optimal _ _
    (fun r => (hP r).smul (Complex.zero_le_real.mpr hlo))
    (fun r => (hQ r).smul (Complex.zero_le_real.mpr hq)) ht).1 E hE hI
  have scale (a : ℝ) (ha : 0 ≤ a) (W : Matrix ι ι ℂ) :
      traceNorm ((a : ℂ) • W) = a * traceNorm W := by
    simp only [traceNorm_eq_physlib, Matrix.traceNorm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ha]
  have hbound {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
      (U V : R → Matrix ι ι ℂ) (hV : ∀ r, (V r).PosSemidef)
      (htV : (∑ r, (V r).trace.re) = 1) :
      (∑ r, traceNorm ((a : ℂ) • U r - (b : ℂ) • V r)) ≤
        a * (∑ r, traceNorm (U r - V r)) + (b-a) := by
    have hpoint (r : R) : traceNorm ((a : ℂ) • U r - (b : ℂ) • V r) ≤
        a * traceNorm (U r - V r) + (b-a) * (V r).trace.re := by
      have hdecomp : (a : ℂ) • U r - (b : ℂ) • V r =
          (a : ℂ) • (U r - V r) + -(((b-a : ℝ) : ℂ) • V r) := by
        push_cast
        rw [smul_sub, sub_smul]
        abel
      rw [hdecomp]
      exact (traceNorm_triangle _ _).trans_eq (by
        rw [traceNorm_neg, scale a ha, scale (b-a) (sub_nonneg.mpr hab),
          traceNorm_posSemidef (hV r)])
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, htV, mul_one] using
      (Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hpoint r)
  rcases le_total p q with hpq | hqp
  · have h := hbound hlo hpq P Q hQ htQ
    rw [max_eq_right hpq, min_eq_left hpq]
    linarith
  · have h := hbound hq hqp Q P hP htP
    have hswap (X Y : Matrix ι ι ℂ) : traceNorm (X - Y) = traceNorm (Y - X) := by
      rw [← traceNorm_neg (Y - X), neg_sub]
    have hw : (∑ r, traceNorm ((p : ℂ) • P r - (q : ℂ) • Q r)) =
        ∑ r, traceNorm ((q : ℂ) • Q r - (p : ℂ) • P r) :=
      Finset.sum_congr rfl fun r _ => hswap _ _
    rw [hw] at hb
    rw [max_eq_left hqp, min_eq_right hqp]
    have hrev : (∑ r, traceNorm (Q r - P r)) = ∑ r, traceNorm (P r - Q r) :=
      Finset.sum_congr rfl fun r _ => hswap _ _
    rw [hrev] at h
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


/-- The physical time-shift budget limits the improvement over the
prior-only decision for the actual stopped-clock outputs. -/
theorem StoppingSchedule.shiftedClock_binary_success_le_prior_guess_add
    (ω ℏ E β : ℝ) (A : Type*) [Fintype A] [DecidableEq A]
    (hℏ : ℏ ≠ 0) (S : StoppingSchedule)
    (shift : List (Fin 3) → ℝ) (δ : ℝ) (hshift : ∀ r, |shift r| ≤ δ)
    {X Y : Matrix (Level × A) (Level × A) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htX : X.trace.re = 1) (htY : Y.trace.re = 1)
    (p : ℝ) (hlo : 0 ≤ p) (hhi : p ≤ 1)
    (F : S.Record → Matrix (Level × A) (Level × A) ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hI : ∀ r, (1 - F r).PosSemidef) :
    let P (r : S.Record) := S.leafState (S.clockPolicy ω ℏ E β A shift) r X
    let Q (r : S.Record) := ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y
    finite_binary_success (fun r => (p : ℂ) • P r)
      (fun r => ((1 - p : ℝ) : ℂ) • Q r) F ≤
      max p (1 - p) + min p (1 - p) *
        (QuantumNetwork.traceNorm (X - Y) + (2 * |ω| * |β * ℏ| * δ) *
          ∑ b : Fin (S.height + 1), (b.val : ℝ) *
            ((S.durationInstrument ω ℏ E β).lift A).weight b Y) / 2 := by
  intro P Q
  have hQ (r : S.Record) :
      Q r = S.leafState (S.clockPolicy ω ℏ E β A (fun _ => 0)) r Y :=
    (S.zero_clockPolicy_leafState ω ℏ E β A r Y).symm
  have hp : (∑ r, (P r).trace.re) = 1 := by
    simp only [P, S.sum_leafState_trace, htX]
  have hq : (∑ r, (Q r).trace.re) = 1 := by
    simp only [hQ, S.sum_leafState_trace, htY]
  refine (finite_binary_success_le_prior_guess_add P Q (fun r => S.leafState_posSemidef _ r hX)
    (fun r => hQ r ▸ S.leafState_posSemidef _ r hY) hp hq p hlo hhi F hF hI).trans ?_
  have he := S.shiftedClock_leaf_error_le_timeBound ω ℏ E β A hℏ shift δ hshift hX hY
  have hmin : 0 ≤ min p (1-p) := le_min hlo (sub_nonneg.mpr hhi)
  exact add_le_add_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hmin)
    (by norm_num : (0 : ℝ) ≤ 2)) (max p (1 - p))

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
  have h := S.shiftedClock_binary_success_le_prior_guess_add ω ℏ E β A hℏ shift δ hshift
    hX hY htX htY (1 / 2) (by norm_num) (by norm_num) F hF hI
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  simp only [hhalf, max_self, min_self] at h
  convert h using 1; ring

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
