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

omit [DecidableEq ι] in
/-- **Matrix Cauchy–Schwarz for the trace (Hilbert–Schmidt) pairing**, discriminant form:
`(Re tr(WᴴV))² ≤ Re tr(WᴴW) · Re tr(VᴴV)`. Proven from the nonnegativity of the quadratic
`t ↦ tr((W − tV)ᴴ(W − tV)) ≥ 0` (a PSD trace) via `discrim_le_zero` — no Schatten/inner-product
instance needed. The keystone of the `F ≤ 1` bound. -/
theorem re_trace_conjTranspose_mul_sq_le (W V : Matrix ι ι ℂ) :
    (Wᴴ * V).trace.re ^ 2 ≤ (Wᴴ * W).trace.re * (Vᴴ * V).trace.re := by
  have hcross : (Vᴴ * W).trace.re = (Wᴴ * V).trace.re := by
    have h : Vᴴ * W = (Wᴴ * V)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [h, Matrix.trace_conjTranspose]
    simp
  have key : ∀ t : ℝ,
      0 ≤ (Vᴴ * V).trace.re * (t * t) + (-2 * (Wᴴ * V).trace.re) * t + (Wᴴ * W).trace.re := by
    intro t
    have hps : (((W - (t : ℂ) • V)ᴴ * (W - (t : ℂ) • V)).trace).re
        = (Vᴴ * V).trace.re * (t * t) + (-2 * (Wᴴ * V).trace.re) * t + (Wᴴ * W).trace.re := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Complex.star_def,
        Complex.conj_ofReal]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Complex.sub_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul]
      rw [hcross]
      ring
    rw [← hps]
    exact (Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg).1
  have hdisc := discrim_le_zero key
  simp only [discrim] at hdisc
  nlinarith [hdisc]

/-- **`0 ≤ tr(σ R)`** for positive-semidefinite `σ, R` (`tr(σR) = tr(√σ R √σ)`, a PSD trace). -/
theorem trace_mul_nonneg {σ R : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (hR : R.PosSemidef) :
    0 ≤ (σ * R).trace := by
  have hPSD : (psdSqrt hσ * R * psdSqrt hσ).PosSemidef := by
    have h := hR.conjTranspose_mul_mul_same (psdSqrt hσ)
    rwa [(psdSqrt_isHermitian hσ).eq] at h
  have heq : (σ * R).trace = (psdSqrt hσ * R * psdSqrt hσ).trace := by
    conv_lhs => rw [← psdSqrt_mul_self hσ]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [heq]; exact hPSD.trace_nonneg

/-- **A Hermitian idempotent (projection) is `≤ 1`**: `1 − Q` is positive semidefinite, since
`1 − Q = (1−Q)ᴴ(1−Q)`. -/
theorem one_sub_posSemidef_of_projection {Q : Matrix ι ι ℂ} (hQh : Q.IsHermitian)
    (hQi : Q * Q = Q) : (1 - Q).PosSemidef := by
  have h : (1 - Q) = (1 - Q)ᴴ * (1 - Q) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQh.eq]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQi]
    abel
  rw [h]; exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **Trace is monotone against a `≤ 1` factor**: if `σ` is PSD and `1 − Q` is PSD, then
`Re tr(σ Q) ≤ Re tr σ`. -/
theorem re_trace_mul_le_of_one_sub_posSemidef {σ Q : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (hQ : (1 - Q).PosSemidef) : (σ * Q).trace.re ≤ σ.trace.re := by
  have h := trace_mul_nonneg hσ hQ
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub] at h
  have hre := (Complex.le_def.mp h).1
  simp only [Complex.sub_re, Complex.zero_re] at hre
  linarith

/-- **`Uᴴ M U = diagonal(eigenvalues)`** for the eigenvector unitary `U` of a Hermitian `M`
(the spectral theorem in conjugated form). -/
theorem eigenvectorUnitary_conj_eq_diagonal {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    (↑hM.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * M * (↑hM.eigenvectorUnitary : Matrix ι ι ℂ)
      = diagonal (fun i => (hM.eigenvalues i : ℂ)) := by
  have h0 := hM.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply] at h0
  simpa [Matrix.star_eq_conjTranspose, Function.comp] using h0

/-! ### Pointwise `√`-inverse arithmetic (for the normalized column matrix `Ĉ = C · D⁺`) -/

/-- `(√x)⁻¹ · x = √x` for `x ≥ 0` (with `(√0)⁻¹ = 0`). -/
theorem inv_sqrt_mul_self {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x)⁻¹ * x = Real.sqrt x := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [← h]
  · have hx' : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr h
    calc (Real.sqrt x)⁻¹ * x
        = (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) := by rw [Real.mul_self_sqrt hx]
      _ = Real.sqrt x := by rw [← mul_assoc, inv_mul_cancel₀ hx', one_mul]

/-- `√x · (√x)⁻¹` is idempotent (`= 0` or `1`). -/
theorem sqrt_mul_inv_idem {x : ℝ} :
    (Real.sqrt x * (Real.sqrt x)⁻¹) * (Real.sqrt x * (Real.sqrt x)⁻¹)
      = Real.sqrt x * (Real.sqrt x)⁻¹ := by
  rcases eq_or_ne (Real.sqrt x) 0 with h | h
  · simp [h]
  · rw [mul_inv_cancel₀ h, mul_one]

/-- `(√x)⁻¹ · (√x · (√x)⁻¹) = (√x)⁻¹`. -/
theorem inv_sqrt_mul_sqrt_mul_inv {x : ℝ} :
    (Real.sqrt x)⁻¹ * (Real.sqrt x * (Real.sqrt x)⁻¹) = (Real.sqrt x)⁻¹ := by
  rcases eq_or_ne (Real.sqrt x) 0 with h | h
  · simp [h]
  · rw [mul_inv_cancel₀ h, mul_one]

end SKEFTHawking.QuantumNetwork
