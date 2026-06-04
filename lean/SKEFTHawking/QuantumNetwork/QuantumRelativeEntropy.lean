import SKEFTHawking.QuantumNetwork.VonNeumannEntropy

/-!
# Matrix logarithm, `tr(ρ log ρ)`, and quantum relative entropy (Phase 6AK, Wave FU-8)

Builds the **matrix logarithm** `log ρ := cfc(Real.log) ρ` of a Hermitian operator (via the continuous
functional calculus already in `MixedState.lean`), the bridge to the eigenvalue-sum von Neumann entropy
`Re tr(ρ log ρ) = −S(ρ)`, and the **quantum relative entropy**
`S(ρ ‖ σ) = Re tr(ρ (log ρ − log σ)) = Re tr(ρ log ρ) − Re tr(ρ log σ)`.

Shipped: matrix log, the `tr(ρ log ρ) = −S(ρ)` bridge, the relative-entropy definition, and
`S(ρ ‖ ρ) = 0`. Klein's inequality `S(ρ ‖ σ) ≥ 0` (the doubly-stochastic eigenbasis-overlap + classical
Gibbs argument) is the next increment; the relative-entropy-of-entanglement `inf_{σ ∈ SEP}` is the
separable-set optimization residual.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **matrix logarithm** of a Hermitian operator via the continuous functional calculus:
`log A := cfc(Real.log) A` (eigenvalues `λᵢ ↦ log λᵢ`; `log 0 = 0` by the `Real.log` convention). -/
noncomputable def matrixLog {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : Matrix ι ι ℂ :=
  hA.cfc Real.log

/-- `ρ · log ρ = cfc(x ↦ x·log x) ρ`. -/
theorem mul_matrixLog {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    ρ * matrixLog hρ = hρ.cfc (fun x => x * Real.log x) := by
  unfold matrixLog
  rw [← cfc_mul hρ (fun x => x) Real.log, cfc_id]

/-- **Bridge to the von Neumann entropy:** `Re tr(ρ log ρ) = −S(ρ)`. -/
theorem re_trace_mul_matrixLog {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    (ρ * matrixLog hρ).trace.re = -vonNeumannEntropy hρ := by
  rw [mul_matrixLog, trace_cfc, vonNeumannEntropy, Complex.re_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.ofReal_re, Real.negMulLog]
  ring

/-- **Quantum relative entropy** `S(ρ ‖ σ) = Re tr(ρ log ρ) − Re tr(ρ log σ)`. -/
noncomputable def relativeEntropy {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ℝ :=
  (ρ * matrixLog hρ).trace.re - (ρ * matrixLog hσ).trace.re

/-- `S(ρ ‖ ρ) = 0`. -/
theorem relativeEntropy_self {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    relativeEntropy hρ hρ = 0 := by
  rw [relativeEntropy, sub_self]

/-- In terms of the von Neumann entropy: `S(ρ ‖ σ) = −S(ρ) − Re tr(ρ log σ)`. -/
theorem relativeEntropy_eq_neg_entropy_sub {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) :
    relativeEntropy hρ hσ = -vonNeumannEntropy hρ - (ρ * matrixLog hσ).trace.re := by
  rw [relativeEntropy, re_trace_mul_matrixLog]

end SKEFTHawking.QuantumNetwork
