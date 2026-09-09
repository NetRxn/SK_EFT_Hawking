import SKEFTHawking.QuantumNetwork.BinaryMemoryRobustness
import SKEFTHawking.QuantumNetwork.PauliChannel

/-!
# Exact diagonal qubit fixture for binary memory robustness

This mathematical model connects a diagonal-state, bit-flip reference experiment
to the common-channel theorem. It does not certify numerical eigensolvers,
floating-point probabilities, or numerical error budgets.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

/-- Diagonal qubit state with outcome-one probability `r`. -/
noncomputable def binaryDiagonalState (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((1 - r : ℝ) : ℂ), (r : ℂ)]

theorem binaryDiagonalState_density {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    IsDensityOperator (binaryDiagonalState r) := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> change 0 ≤ (_ : ℂ) <;> rw [Complex.le_def]
    · exact ⟨sub_nonneg.mpr hr.2, rfl⟩
    · exact ⟨hr.1, rfl⟩
  · simp [binaryDiagonalState, Matrix.trace_diagonal, Fin.sum_univ_two]

/-- The computational-basis outcome-one effect. -/
noncomputable def binaryOneEffect : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![0, 1]

theorem binaryOneEffect_isBinaryPOVM : IsBinaryPOVM binaryOneEffect := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> simp
  · have he : (1 : Matrix (Fin 2) (Fin 2) ℂ) - binaryOneEffect =
        Matrix.diagonal ![1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [binaryOneEffect]
    rw [he]
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> simp

theorem binaryOneEffect_probability (r : ℝ) :
    binaryOutcomeProb binaryOneEffect (binaryDiagonalState r) = r := by
  simp [binaryOutcomeProb, binaryOneEffect, binaryDiagonalState,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_two]

/-- Bit-flip channel, padded with two zero Pauli weights. -/
noncomputable def binaryBitFlipKraus (q : ℝ) := pauliKraus ![1 - q, q, 0, 0]

theorem binaryBitFlipKraus_normalized {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    IsKrausChannel (binaryBitFlipKraus q) := by
  apply isKrausChannel_pauliKraus
  · intro i
    fin_cases i <;> simp
    · exact hq.2
    · exact hq.1
  · simp [Fin.sum_univ_four]

theorem binaryBitFlip_action {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    krausMap (binaryBitFlipKraus q) ρ =
      ((1 - q : ℝ) : ℂ) • ρ + (q : ℂ) • (pauliX * ρ * pauliX) := by
  simp [krausMap, binaryBitFlipKraus, pauliKraus, Fin.sum_univ_four, pauliOp,
    pauliX_conjTranspose, smul_smul, Real.mul_self_sqrt hq.1,
    Real.mul_self_sqrt (sub_nonneg.mpr hq.2)]
  ext i j
  simp [Complex.real_smul, Complex.ofReal_sub]

theorem binaryBitFlip_diagonal {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (r : ℝ) :
    krausMap (binaryBitFlipKraus q) (binaryDiagonalState r) =
      binaryDiagonalState (q + (1 - 2 * q) * r) := by
  rw [binaryBitFlip_action hq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryDiagonalState, pauliX, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul] <;> ring

theorem binaryBitFlip_probability {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (r : ℝ) :
    binaryOutcomeProb binaryOneEffect
      (krausMap (binaryBitFlipKraus q) (binaryDiagonalState r)) = q + (1 - 2 * q) * r := by
  rw [binaryBitFlip_diagonal hq, binaryOneEffect_probability]

theorem binaryDiagonalState_traceDist (r s : ℝ) :
    traceDist (binaryDiagonalState r) (binaryDiagonalState s) = |r - s| := by
  let A := binaryDiagonalState r - binaryDiagonalState s
  have habs : absOp A = ((|r - s| : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _) ?_ ?_
    · exact Matrix.PosSemidef.one.smul (by exact_mod_cast abs_nonneg (r - s))
    · rw [absOp_mul_self]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, binaryDiagonalState, Matrix.mul_apply,
          Fin.sum_univ_two, Complex.ofReal_sub] <;>
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im];
        nlinarith [sq_abs (r - s)]
  change (1 / 2 : ℝ) * traceNorm A = _
  rw [traceNorm_eq_trace_absOp, habs]
  simp [Matrix.trace, Complex.mul_re]

/-- The two fixture inputs and their common reference are valid density operators. -/
theorem binaryFixture_density {t a b : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) t) (hb : b ∈ Set.Icc (0 : ℝ) (1 - t)) :
    IsDensityOperator (binaryDiagonalState (t - a)) ∧
      IsDensityOperator (binaryDiagonalState (t + b)) ∧
      IsDensityOperator (binaryDiagonalState t) := by
  refine ⟨binaryDiagonalState_density ⟨by linarith [ha.2], by linarith [ha.1, ht.2]⟩,
    binaryDiagonalState_density ⟨by linarith [hb.1, ht.1], by linarith [hb.2]⟩,
    binaryDiagonalState_density ht⟩

/-- Exact reset distances: the budgets are attained, not merely postulated. -/
theorem binaryFixture_distances (t : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    traceDist (binaryDiagonalState (t - a)) (binaryDiagonalState t) = a ∧
      traceDist (binaryDiagonalState (t + b)) (binaryDiagonalState t) = b ∧
      traceDist (binaryDiagonalState (t - a)) (binaryDiagonalState (t + b)) = a + b := by
  simp only [binaryDiagonalState_traceDist]
  rw [show t - a - t = -a by ring, show t + b - t = b by ring,
    show t - a - (t + b) = -(a + b) by ring, abs_neg, abs_neg,
    abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (add_nonneg ha hb)]
  exact ⟨rfl, rfl, rfl⟩

/-- For bit-flip probability at most one half, the signal contracts by `1-2q`. -/
theorem binaryFixture_separation {q a b : ℝ} (t : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) (1 / 2)) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |binaryOutcomeProb binaryOneEffect
      (krausMap (binaryBitFlipKraus q) (binaryDiagonalState (t - a))) -
      binaryOutcomeProb binaryOneEffect
      (krausMap (binaryBitFlipKraus q) (binaryDiagonalState (t + b)))| =
      (1 - 2 * q) * (a + b) := by
  have hq' : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1, by linarith [hq.2]⟩
  rw [binaryBitFlip_probability hq', binaryBitFlip_probability hq']
  rw [show q + (1 - 2 * q) * (t - a) - (q + (1 - 2 * q) * (t + b)) =
    -((1 - 2 * q) * (a + b)) by ring, abs_neg]
  exact abs_of_nonneg (mul_nonneg (by linarith [hq.2]) (add_nonneg ha hb))

/-- The concrete fixture consumes the general common-channel robustness theorem. -/
theorem binaryFixture_memoryless_bound {t a b q : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ha : a ∈ Set.Icc (0 : ℝ) t)
    (hb : b ∈ Set.Icc (0 : ℝ) (1 - t)) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    |binaryOutcomeProb binaryOneEffect
      (krausMap (binaryBitFlipKraus q) (binaryDiagonalState (t - a))) -
      binaryOutcomeProb binaryOneEffect
      (krausMap (binaryBitFlipKraus q) (binaryDiagonalState (t + b)))| ≤ min 1 (a + b) := by
  obtain ⟨hρ₀, hρ₁, hτ⟩ := binaryFixture_density ht ha hb
  obtain ⟨hd₀, hd₁, _⟩ := binaryFixture_distances t ha.1 hb.1
  exact binary_memoryless_separation_le hρ₀ hρ₁ hτ (binaryBitFlipKraus_normalized hq)
    binaryOneEffect_isBinaryPOVM hd₀.le hd₁.le

end SKEFTHawking.QuantumNetwork
