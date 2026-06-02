import SKEFTHawking.QuantumNetwork.MixedState

/-!
# Fidelity bounds: `F ≤ 1` and Fuchs–van de Graaf (Phase 6AF-7, in progress)

The quantitative fidelity↔trace-distance bridge that Phase 6AF deferred. This file builds it
incrementally. The headline target is `sqrtFidelity ρ σ ≤ 1` (`F ∈ [0,1]`), and then the
Fuchs–van de Graaf inequalities `1 − F ≤ D ≤ √(1 − F²)`.

## Proof blueprint for `F ≤ 1` (the double–Cauchy-Schwarz route)

Mathlib at pin has **no** Schatten norms, matrix Hölder, von Neumann trace inequality, polar
decomposition, SVD, or singular-value majorization (all verified absent). The "light" routes
fail: Frobenius–Cauchy-Schwarz bounds `tr(√σ√ρ) ≤ 1` (the *trace*, not the trace *norm* `F`),
and Weyl monotonicity (`√ρσ√ρ ≤ ρ ⟹ νᵢ ≤ ρᵢ`) is insufficient (`νᵢ ≤ ρᵢ` with `∑ρᵢ = 1` does
not give `∑√νᵢ ≤ 1`). So `F ≤ 1` genuinely needs new structure — but it is reachable by an
elementary argument using only the spectral theorem + Cauchy-Schwarz twice:

Let `M = √ρ σ √ρ` (PSD), with eigenpairs `(μᵢ, vᵢ)` (`vᵢ` an orthonormal eigenbasis). Then
* `F = ‖√σ√ρ‖₁ = ∑ᵢ √μᵢ`  (this file: `sqrtFidelity_eq_sum_sqrt_eig`, since
  `(√σ√ρ)ᴴ(√σ√ρ) = M`);
* `μᵢ = ‖√σ√ρ vᵢ‖²`, so `√μᵢ = ‖√σ√ρ vᵢ‖`;
* with `wᵢ := √σ√ρ vᵢ / √μᵢ` (orthonormal where `μᵢ > 0`), `√μᵢ = ⟨√σ wᵢ, √ρ vᵢ⟩`;
* `F = ∑ ⟨√σ wᵢ, √ρ vᵢ⟩ ≤ √(∑‖√σ wᵢ‖²) · √(∑‖√ρ vᵢ‖²)`  (Cauchy-Schwarz twice);
* `∑‖√ρ vᵢ‖² = tr ρ = 1` (orthonormal eigenbasis), and `∑‖√σ wᵢ‖² ≤ tr σ = 1` (a partial sum
  over an orthonormal set, `σ` PSD), giving `F ≤ 1`.

Remaining sub-lemmas to formalize (the `wᵢ` construction + orthonormality, `√μᵢ = ⟨…⟩`, the two
Cauchy-Schwarz steps, `∑‖√ρ vᵢ‖² = tr ρ`, and partial-sum ≤ trace) use `IsHermitian.eigenvectorBasis`,
`mulVec_eigenvectorBasis`, and inner-product `norm_inner_le_norm` — all present. FvdG then needs
its own additional argument (the trace-distance↔fidelity spectral coupling).

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Entry point of the `F ≤ 1` proof**: the root fidelity is the sum of `√` of the eigenvalues
of `M = √ρ σ √ρ`. Since `‖A‖₁ = ∑ √eigenvalues(AᴴA)` and `(√σ√ρ)ᴴ(√σ√ρ) = √ρ σ √ρ`, the
fidelity `F = ‖√σ√ρ‖₁` is exactly `∑ √eigenvalues(M)`. -/
theorem sqrtFidelity_eq_traceNormOf {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hM : (psdSqrt hρ * σ * psdSqrt hρ).PosSemidef) :
    sqrtFidelity hρ hσ = traceNormOf hM := by
  rw [sqrtFidelity, traceNorm]
  exact traceNormOf_congr _ hM (conjTranspose_mul_self_sqrtFidelity hρ hσ)

/-- The operator under the fidelity square root, `√ρ σ √ρ`, is positive semidefinite. -/
theorem posSemidef_sqrt_mul_mid_mul_sqrt {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) : (psdSqrt hρ * σ * psdSqrt hρ).PosSemidef := by
  have h := hσ.conjTranspose_mul_mul_same (psdSqrt hρ)
  rwa [(psdSqrt_isHermitian hρ).eq] at h

/-- **`F = ∑ √eigenvalues(√ρ σ √ρ)`** — the explicit singular-value-sum form the double
Cauchy-Schwarz bound operates on. -/
theorem sqrtFidelity_eq_sum_sqrt_eig {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    sqrtFidelity hρ hσ
      = ∑ i, Real.sqrt ((posSemidef_sqrt_mul_mid_mul_sqrt hρ hσ).isHermitian.eigenvalues i) :=
  sqrtFidelity_eq_traceNormOf hρ hσ (posSemidef_sqrt_mul_mid_mul_sqrt hρ hσ)

end SKEFTHawking.QuantumNetwork
