import SKEFTHawking.QuantumNetwork.QuantumKlein

/-!
# Concavity of the von Neumann entropy (Phase 6AL, Wave 1, item A)

`S(∑ₖ wₖ ρₖ) ≥ ∑ₖ wₖ S(ρₖ)` for a convex combination of density operators with a positive-definite
average. Mixing states never decreases entropy. Proof: for the average `ρ̄ = ∑ₖ wₖ ρₖ`, Klein's
inequality gives `relativeEntropy ρₖ ρ̄ ≥ 0` for each `k`; the weighted sum
`∑ₖ wₖ · relativeEntropy ρₖ ρ̄ = S(ρ̄) − ∑ₖ wₖ S(ρₖ)` (using the bridge `Re tr(ρ log ρ) = −S(ρ)` and
ℝ-linearity of `Re tr(· M)` over the convex combination), hence `S(ρ̄) ≥ ∑ₖ wₖ S(ρₖ)`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **ℝ-linearity bridge:** `∑ₖ wₖ · Re tr(ρₖ M) = Re tr((∑ₖ wₖ ρₖ) M)` for real weights `wₖ`. -/
theorem re_trace_sum_smul_mul {κ : Type*} [Fintype κ] (w : κ → ℝ) (ρ : κ → Matrix ι ι ℂ)
    (M : Matrix ι ι ℂ) :
    ∑ k, w k * (ρ k * M).trace.re = ((∑ k, (w k : ℂ) • ρ k) * M).trace.re := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- **Concavity of the von Neumann entropy:** `S(∑ₖ wₖ ρₖ) ≥ ∑ₖ wₖ S(ρₖ)` for a convex combination of
density operators whose average is positive definite. -/
theorem vonNeumannEntropy_concave {κ : Type*} [Fintype κ] {ρ : κ → Matrix ι ι ℂ}
    (w : κ → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1)
    (hρ : ∀ k, IsDensityOperator (ρ k))
    (hbar : (∑ k, (w k : ℂ) • ρ k).PosDef) :
    ∑ k, w k * vonNeumannEntropy (hρ k).1.isHermitian ≤ vonNeumannEntropy hbar.1 := by
  set ρbar := ∑ k, (w k : ℂ) • ρ k with hρbar
  have hbartr : ρbar.trace = 1 := by
    rw [hρbar, Matrix.trace_sum,
      Finset.sum_congr rfl fun k _ => by rw [Matrix.trace_smul, smul_eq_mul, (hρ k).2, mul_one],
      ← Complex.ofReal_sum, hw1, Complex.ofReal_one]
  have hsum : 0 ≤ ∑ k, w k * relativeEntropy (hρ k).1.isHermitian hbar.1 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) (relativeEntropy_nonneg (hρ k) hbar hbartr)
  have hb : ∑ k, w k * (ρ k * matrixLog hbar.1).trace.re = -vonNeumannEntropy hbar.1 := by
    rw [re_trace_sum_smul_mul, ← hρbar, re_trace_mul_matrixLog hbar.1]
  have ha : ∑ k, w k * (ρ k * matrixLog (hρ k).1.isHermitian).trace.re
      = -∑ k, w k * vonNeumannEntropy (hρ k).1.isHermitian := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [re_trace_mul_matrixLog (hρ k).1.isHermitian]; ring
  have hexpand : ∑ k, w k * relativeEntropy (hρ k).1.isHermitian hbar.1
      = vonNeumannEntropy hbar.1 - ∑ k, w k * vonNeumannEntropy (hρ k).1.isHermitian := by
    calc ∑ k, w k * relativeEntropy (hρ k).1.isHermitian hbar.1
        = (∑ k, w k * (ρ k * matrixLog (hρ k).1.isHermitian).trace.re)
            - ∑ k, w k * (ρ k * matrixLog hbar.1).trace.re := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun k _ => by rw [relativeEntropy, mul_sub]
      _ = vonNeumannEntropy hbar.1 - ∑ k, w k * vonNeumannEntropy (hρ k).1.isHermitian := by
          rw [ha, hb]; ring
  rw [hexpand] at hsum
  linarith
