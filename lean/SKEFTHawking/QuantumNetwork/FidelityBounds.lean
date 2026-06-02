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

/-- ℂ-cast version of `inv_sqrt_mul_self`. -/
theorem inv_sqrt_mul_self_C {x : ℝ} (hx : 0 ≤ x) :
    ((Real.sqrt x : ℂ))⁻¹ * (x : ℂ) = (Real.sqrt x : ℂ) := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_sqrt_mul_self hx]

/-- ℂ-cast version of `inv_sqrt_mul_sqrt_mul_inv`. -/
theorem inv_sqrt_mul_sqrt_mul_inv_C {x : ℝ} :
    ((Real.sqrt x : ℂ))⁻¹ * ((Real.sqrt x : ℂ) * ((Real.sqrt x : ℂ))⁻¹) = ((Real.sqrt x : ℂ))⁻¹ := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, inv_sqrt_mul_sqrt_mul_inv]

/-- **`F ≤ 1`** — the root fidelity of two density operators is at most `1`. Proven by the
column-assembly double-Cauchy-Schwarz: with `M = √ρ σ √ρ` (eigenvalues `f`, eigenvector unitary
`U`), `C = √σ√ρ U` has `CᴴC = diagonal f`; the normalized `Ĉ = C·D⁺` (`D⁺ = diagonal √(fᵢ)⁻¹`)
gives `W = √σ Ĉ`, `V = √ρ U` with `tr(WᴴV) = ∑√fᵢ = F`, `tr(VᴴV) = tr ρ = 1`, and
`tr(WᴴW) = tr(σ ĈĈᴴ) ≤ tr σ = 1` (`ĈĈᴴ` a projection). Matrix Cauchy–Schwarz then gives
`F² ≤ 1·1`. -/
theorem sqrtFidelity_le_one {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : sqrtFidelity hρ.1 hσ.1 ≤ 1 := by
  obtain ⟨hρp, hρt⟩ := hρ
  obtain ⟨hσp, hσt⟩ := hσ
  set p := psdSqrt hρp with hp
  set s := psdSqrt hσp with hs
  have hpH : pᴴ = p := (psdSqrt_isHermitian hρp).eq
  have hsH : sᴴ = s := (psdSqrt_isHermitian hσp).eq
  have hpp : p * p = ρ := psdSqrt_mul_self hρp
  have hss : s * s = σ := psdSqrt_mul_self hσp
  set hM := posSemidef_sqrt_mul_mid_mul_sqrt hρp hσp with hMdef
  set hMh := hM.isHermitian with hMhdef
  set f := hMh.eigenvalues with hfdef
  have hfnn : ∀ i, 0 ≤ f i := hM.eigenvalues_nonneg
  set U : Matrix ι ι ℂ := (↑hMh.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  have hUsU : Uᴴ * U = 1 := by
    have h := hMh.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hUUs : U * Uᴴ = 1 := by
    have h := hMh.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hspec : Uᴴ * (p * σ * p) * U = diagonal (fun i => (f i : ℂ)) :=
    eigenvectorUnitary_conj_eq_diagonal hMh
  -- C = √σ√ρ U, CᴴC = diagonal f
  set C : Matrix ι ι ℂ := s * p * U with hCdef
  have hCC : Cᴴ * C = diagonal (fun i => (f i : ℂ)) := by
    have key : Cᴴ * C = Uᴴ * (p * σ * p) * U := by
      rw [hCdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hpH, hsH, ← hss]
      noncomm_ring
    rw [key, hspec]
  set Dp : Matrix ι ι ℂ := diagonal (fun i => ((Real.sqrt (f i))⁻¹ : ℂ)) with hDpdef
  have hDpH : Dpᴴ = Dp := by
    rw [hDpdef, Matrix.diagonal_conjTranspose]; simp
  set Chat : Matrix ι ι ℂ := C * Dp with hChatdef
  set V : Matrix ι ι ℂ := p * U with hVdef
  set W : Matrix ι ι ℂ := s * Chat with hWdef
  -- (1) tr(WᴴV) = ∑ √f = F
  have hWV : (Wᴴ * V).trace = ∑ i, (Real.sqrt (f i) : ℂ) := by
    have hWeq : Wᴴ = Dp * Cᴴ * s := by
      rw [hWdef, hChatdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hsH, hDpH]
    have e : Wᴴ * V = diagonal (fun i => (Real.sqrt (f i) : ℂ)) := by
      rw [hWeq, hVdef, show Dp * Cᴴ * s * (p * U) = Dp * (Cᴴ * (s * p * U)) by noncomm_ring,
        ← hCdef, hCC, hDpdef, Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_sqrt_mul_self (hfnn i)]
    rw [e, Matrix.trace_diagonal]
  -- (2) tr(VᴴV).re = tr ρ = 1
  have hVV : (Vᴴ * V).trace.re = 1 := by
    have e : Vᴴ * V = Uᴴ * ρ * U := by
      rw [hVdef, Matrix.conjTranspose_mul, hpH, ← hpp]; noncomm_ring
    rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUUs, Matrix.one_mul, hρt, Complex.one_re]
  -- ĈĈᴴ is a Hermitian projection ⟹ ≤ 1
  have hCCdiag : Chatᴴ * Chat
      = diagonal (fun i => (Real.sqrt (f i) : ℂ) * ((Real.sqrt (f i) : ℂ))⁻¹) := by
    rw [hChatdef, Matrix.conjTranspose_mul, hDpH,
      show Dp * Cᴴ * (C * Dp) = Dp * (Cᴴ * C) * Dp by noncomm_ring, hCC, hDpdef,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [inv_sqrt_mul_self_C (hfnn i)]
  have hChatProj : Chat * (Chatᴴ * Chat) = Chat := by
    have hDpPi : Dp * (Chatᴴ * Chat) = Dp := by
      rw [hCCdiag, hDpdef, Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      rw [inv_sqrt_mul_sqrt_mul_inv_C]
    calc Chat * (Chatᴴ * Chat)
        = C * (Dp * (Chatᴴ * Chat)) := by nth_rewrite 1 [hChatdef]; rw [Matrix.mul_assoc]
      _ = C * Dp := by rw [hDpPi]
      _ = Chat := hChatdef.symm
  have hPidem : (Chat * Chatᴴ) * (Chat * Chatᴴ) = Chat * Chatᴴ := by
    rw [show (Chat * Chatᴴ) * (Chat * Chatᴴ) = (Chat * (Chatᴴ * Chat)) * Chatᴴ by noncomm_ring,
      hChatProj]
  have hPherm : (Chat * Chatᴴ).IsHermitian := (Matrix.posSemidef_self_mul_conjTranspose Chat).1
  have hP1 : (1 - Chat * Chatᴴ).PosSemidef := one_sub_posSemidef_of_projection hPherm hPidem
  -- (3) tr(WᴴW).re = tr(σ ĈĈᴴ).re ≤ tr σ = 1
  have hWW : (Wᴴ * W).trace.re ≤ 1 := by
    have e : (Wᴴ * W).trace = (σ * (Chat * Chatᴴ)).trace := by
      rw [hWdef, Matrix.conjTranspose_mul, hsH,
        show Chatᴴ * s * (s * Chat) = Chatᴴ * (σ * Chat) by rw [← hss]; noncomm_ring,
        Matrix.trace_mul_comm, Matrix.mul_assoc]
    rw [e]
    have hb := re_trace_mul_le_of_one_sub_posSemidef hσp hP1
    rwa [hσt, Complex.one_re] at hb
  -- conclude via matrix Cauchy–Schwarz
  have hF : sqrtFidelity hρp hσp = (Wᴴ * V).trace.re := by
    rw [sqrtFidelity_eq_sum_sqrt_eig hρp hσp, hWV, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => (Complex.ofReal_re _).symm
  have hX : 0 ≤ (Wᴴ * V).trace.re := hF ▸ sqrtFidelity_nonneg hρp hσp
  have hcs := re_trace_conjTranspose_mul_sq_le W V
  rw [hVV, mul_one] at hcs
  rw [hF]
  nlinarith [hcs, hWW, hX]

/-- **The Jozsa fidelity lies in `[0,1]`**: `0 ≤ F(ρ,σ)² ≤ 1` for density operators. -/
theorem fidelity_le_one {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : fidelity hρ.1 hσ.1 ≤ 1 := by
  have h := sqrtFidelity_le_one hρ hσ
  have h0 := sqrtFidelity_nonneg hρ.1 hσ.1
  rw [fidelity]
  nlinarith [h, h0]

/-- **`F(ρ,σ) ∈ [0,1]`** — the root fidelity of two density operators is a `[0,1]`-valued
quantity (combines `sqrtFidelity_nonneg` and `sqrtFidelity_le_one`). -/
theorem sqrtFidelity_mem_Icc {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : sqrtFidelity hρ.1 hσ.1 ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sqrtFidelity_nonneg hρ.1 hσ.1, sqrtFidelity_le_one hρ hσ⟩

end SKEFTHawking.QuantumNetwork

