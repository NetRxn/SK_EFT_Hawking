import SKEFTHawking.QuantumNetwork.QuantumKlein

/-!
# Gibbs variational principle / free energy (Phase 6AL, Wave 1, item D)

The variational characterization of equilibrium, as a corollary of Klein's inequality. For any density
operator `ρ` and a positive-definite reference density `σ`, the **cross entropy** `−Re tr(ρ log σ)`
dominates the von Neumann entropy, and the gap is exactly the relative entropy:

`(−Re tr(ρ log σ)) − S(ρ) = S(ρ ‖ σ) ≥ 0`,  with equality iff `ρ = σ`.

**Physical reading (Gibbs / thermal):** take `σ = τ_β = e^{−βH}/Z` the thermal state at inverse
temperature `β` (partition function `Z = tr e^{−βH}`). Then `−log τ_β = βH + (log Z)·1`, so
`−Re tr(ρ log τ_β) = β⟨H⟩_ρ + log Z`, and the bound reads `β⟨H⟩_ρ − S(ρ) ≥ −log Z`, i.e. the (scaled)
free energy `β F(ρ) = β⟨H⟩_ρ − S(ρ)` is minimized by the thermal state with minimum `−log Z`. The explicit
thermal-state construction (matrix exponential `cfc exp`) is a separate optional brick; the variational
content above is the Klein corollary, stated reference-state-generically and free of matrix-exp machinery.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Free-energy gap = relative entropy:** `(−Re tr(ρ log σ)) − S(ρ) = S(ρ ‖ σ)`. The variational
gap between the cross entropy `−Re tr(ρ log σ)` and the von Neumann entropy is exactly the quantum
relative entropy to the reference. -/
theorem cross_sub_entropy_eq_relativeEntropy {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) :
    -(ρ * matrixLog hσ).trace.re - vonNeumannEntropy hρ = relativeEntropy hρ hσ := by
  rw [relativeEntropy, re_trace_mul_matrixLog hρ]
  ring

/-- **Gibbs variational bound:** `S(ρ) ≤ −Re tr(ρ log σ)` for any density operator `ρ` and positive-
definite reference density `σ`. With `σ` the thermal state this is the free-energy lower bound
`β⟨H⟩_ρ − S(ρ) ≥ −log Z`; equality holds at `ρ = σ` (where the gap, the relative entropy, vanishes). -/
theorem vonNeumannEntropy_le_cross {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ)
    (hσ : σ.PosDef) (hσtr : σ.trace = 1) :
    vonNeumannEntropy hρ.1.isHermitian ≤ -(ρ * matrixLog hσ.1).trace.re := by
  have h := relativeEntropy_nonneg hρ hσ hσtr
  rw [← cross_sub_entropy_eq_relativeEntropy hρ.1.isHermitian hσ.1] at h
  linarith

/-- At the reference state itself the cross entropy equals the von Neumann entropy
(`−Re tr(σ log σ) = S(σ)`): the variational bound is saturated at `ρ = σ`. -/
theorem cross_self_eq_entropy {σ : Matrix ι ι ℂ} (hσ : σ.IsHermitian) :
    -(σ * matrixLog hσ).trace.re = vonNeumannEntropy hσ := by
  rw [re_trace_mul_matrixLog hσ]; ring

end SKEFTHawking.QuantumNetwork
