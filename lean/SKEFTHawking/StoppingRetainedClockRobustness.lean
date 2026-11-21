import SKEFTHawking.StoppingRetainedClockInstrument
import SKEFTHawking.QuantumNetwork.BinaryMemoryRobustness

/-! Total-variation stability of finite reports and stopped-clock duration laws. -/

noncomputable section
open Matrix
open scoped ComplexOrder
namespace SKEFTHawking.QuantumNetwork.FiniteInstrument

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The effect for accepting an arbitrary subset of the instrument's reports. -/
def eventEffect (J : FiniteInstrument ι n) (A : Finset (Fin n)) : Matrix ι ι ℂ :=
  ∑ a ∈ A, ∑ k, (J.operators a k)ᴴ * J.operators a k

theorem eventEffect_posSemidef (J : FiniteInstrument ι n) (A : Finset (Fin n)) :
    (J.eventEffect A).PosSemidef :=
  Matrix.posSemidef_sum _ fun a _ =>
    Matrix.posSemidef_sum _ fun k _ =>
      Matrix.posSemidef_conjTranspose_mul_self (J.operators a k)

theorem eventEffect_binaryPOVM (J : FiniteInstrument ι n) (A : Finset (Fin n)) :
    IsBinaryPOVM (J.eventEffect A) := by
  have hsum : J.eventEffect (Finset.univ \ A) + J.eventEffect A = 1 := by
    unfold eventEffect
    rw [Finset.sum_sdiff (Finset.subset_univ A), J.normalized]
  have hcomp : J.eventEffect (Finset.univ \ A) = 1 - J.eventEffect A :=
    eq_sub_iff_add_eq.mpr hsum
  exact ⟨J.eventEffect_posSemidef A, hcomp ▸ J.eventEffect_posSemidef (Finset.univ \ A)⟩

theorem sum_weight_eq_eventEffect (J : FiniteInstrument ι n) (A : Finset (Fin n))
    (X : Matrix ι ι ℂ) : ∑ a ∈ A, J.weight a X = binaryOutcomeProb (J.eventEffect A) X := by
  simp only [FiniteInstrument.weight, FiniteInstrument.branch, krausMap,
    binaryOutcomeProb, eventEffect, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun k _ => congrArg Complex.re (Matrix.trace_mul_cycle _ _ _)

theorem sum_weight_event_gap_le_traceDist (J : FiniteInstrument ι n) (A : Finset (Fin n))
    {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    |(∑ a ∈ A, J.weight a ρ) - ∑ a ∈ A, J.weight a σ| ≤ traceDist ρ σ := by
  rw [J.sum_weight_eq_eventEffect, J.sum_weight_eq_eventEffect]
  exact abs_binaryOutcomeProb_sub_le_traceDist (J.eventEffect_binaryPOVM A) hρ hσ

/-- The total variation of the whole reported law is bounded by input trace distance. -/
theorem weight_totalVariation_le_traceDist (J : FiniteInstrument ι n)
    {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    (∑ a, |J.weight a ρ - J.weight a σ|) / 2 ≤ traceDist ρ σ := by
  let d (a : Fin n) := J.weight a ρ - J.weight a σ
  let A := Finset.univ.filter fun a => 0 ≤ d a
  have hz : ∑ a, d a = 0 := by
    simp only [d, Finset.sum_sub_distrib, J.sum_weight, hρ.2, hσ.2, sub_self]
  have he (a : Fin n) : |d a| = 2 * (if 0 ≤ d a then d a else 0) - d a := by
    by_cases ha : 0 ≤ d a
    · rw [abs_of_nonneg ha, if_pos ha]
      ring
    · rw [abs_of_neg (lt_of_not_ge ha), if_neg ha]
      ring
  change (∑ a, |d a|) / 2 ≤ _
  have htotal : (∑ a, |d a|) = 2 * ∑ a ∈ A, d a := by
    simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum, hz, sub_zero]
    rw [Finset.sum_filter]
  rw [htotal]
  have h := J.sum_weight_event_gap_le_traceDist A hρ hσ
  rw [← Finset.sum_sub_distrib] at h
  linarith only [le_abs_self (∑ a ∈ A, d a), h]

/-- A common joint reference gives a bound from the two state-preparation budgets. -/
theorem weight_totalVariation_le_reference (J : FiniteInstrument ι n)
    {ρ σ τ : Matrix ι ι ℂ} {ε₀ ε₁ : ℝ}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) (hτ : IsDensityOperator τ)
    (h₀ : traceDist ρ τ ≤ ε₀) (h₁ : traceDist σ τ ≤ ε₁) :
    (∑ a, |J.weight a ρ - J.weight a σ|) / 2 ≤ ε₀ + ε₁ := by
  have ht := traceDist_triangle ρ τ σ hρ.1.isHermitian hτ.1.isHermitian hσ.1.isHermitian
  rw [traceDist_comm τ σ] at ht
  exact (J.weight_totalVariation_le_traceDist hρ hσ).trans (ht.trans (add_le_add h₀ h₁))

end SKEFTHawking.QuantumNetwork.FiniteInstrument

namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
open QuantumNetwork FiniteGibbsClock

/-- The same stopping schedule and report are applied to both joint states.
The bound admits arbitrary correlations with an untouched finite auxiliary system. -/
theorem StoppingSchedule.reportedInstrument_lift_totalVariation_le_traceDist
    (ω ℏ E β : ℝ) {q : ℕ} (S : StoppingSchedule) (report : S.Record → Fin q)
    (A : Type*) [Fintype A] [DecidableEq A]
    {ρ σ : Matrix (Level × A) (Level × A) ℂ} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) :
    (∑ b, |((S.reportedInstrument ω ℏ E β report).lift A).weight b ρ -
      ((S.reportedInstrument ω ℏ E β report).lift A).weight b σ|) / 2 ≤ traceDist ρ σ :=
  ((S.reportedInstrument ω ℏ E β report).lift A).weight_totalVariation_le_traceDist hρ hσ

theorem StoppingSchedule.durationInstrument_lift_totalVariation_le_traceDist
    (ω ℏ E β : ℝ) (S : StoppingSchedule) (A : Type*) [Fintype A] [DecidableEq A]
    {ρ σ : Matrix (Level × A) (Level × A) ℂ} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) :
    (∑ b, |((S.durationInstrument ω ℏ E β).lift A).weight b ρ -
      ((S.durationInstrument ω ℏ E β).lift A).weight b σ|) / 2 ≤ traceDist ρ σ :=
  S.reportedInstrument_lift_totalVariation_le_traceDist ω ℏ E β S.duration A hρ hσ

/-- A shared duration report inherits the common-reference bound on the full joint state. -/
theorem StoppingSchedule.durationInstrument_lift_totalVariation_le_reference
    (ω ℏ E β : ℝ) (S : StoppingSchedule) (A : Type*) [Fintype A] [DecidableEq A]
    {ρ σ τ : Matrix (Level × A) (Level × A) ℂ} {ε₀ ε₁ : ℝ}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) (hτ : IsDensityOperator τ)
    (h₀ : traceDist ρ τ ≤ ε₀) (h₁ : traceDist σ τ ≤ ε₁) :
    (∑ b, |((S.durationInstrument ω ℏ E β).lift A).weight b ρ -
      ((S.durationInstrument ω ℏ E β).lift A).weight b σ|) / 2 ≤ ε₀ + ε₁ :=
  ((S.durationInstrument ω ℏ E β).lift A).weight_totalVariation_le_reference hρ hσ hτ h₀ h₁

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
