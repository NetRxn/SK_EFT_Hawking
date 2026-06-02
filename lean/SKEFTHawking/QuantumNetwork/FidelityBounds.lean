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

omit [DecidableEq ι] in
/-- A **diagonal entry is bounded by its column's sum of squares**: `‖Mᵢᵢ‖² ≤ Re (MᴴM)ᵢᵢ`. Stated
for an ABSTRACT `M` so the `single_le_sum` step never forces evaluation of a heavy concrete `M`
(this is the key to keeping the `Re tr ≤ ‖·‖₁` proof off the spectral-`whnf` wall). -/
theorem normSq_diag_le_re_conjTranspose_mul_self (M : Matrix ι ι ℂ) (i : ι) :
    Complex.normSq (M i i) ≤ ((Mᴴ * M) i i).re := by
  have h : ((Mᴴ * M) i i).re = ∑ k, Complex.normSq (M k i) := by
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_apply, Complex.star_def]
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]
  rw [h]
  exact Finset.single_le_sum (f := fun k => Complex.normSq (M k i))
    (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

/-- **`Re tr A ≤ ‖A‖₁`** for any matrix `A` — real part of the trace ≤ trace norm. Conjugate by the
eigenvector unitary `U` of `AᴴA` (`B = UᴴAU`, `BᴴB = diagonal(eig)`); then `‖Bᵢᵢ‖² ≤ (BᴴB)ᵢᵢ = eigᵢ`
gives `Re tr A = ∑ Re Bᵢᵢ ≤ ∑ √eigᵢ = ‖A‖₁`. `clear_value` freezes the heavy `U`/`B` so per-entry
access stays symbolic (no `maxHeartbeats`); the final `∑√eig = ‖A‖₁` uses the proven
`traceNorm_eq_sqrtRootSum` + `roots_charpoly_eq_eigenvalues` rewrites. -/
theorem re_trace_le_traceNorm (A : Matrix ι ι ℂ) : A.trace.re ≤ traceNorm A := by
  set U : Matrix ι ι ℂ :=
    (↑(Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorUnitary :
      Matrix ι ι ℂ) with hUdef
  have hUUs : U * Uᴴ = 1 := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h; exact h
  set B : Matrix ι ι ℂ := Uᴴ * A * U with hBdef
  have htr : A.trace = B.trace := by
    rw [hBdef, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUUs, Matrix.one_mul]
  have hBB : Bᴴ * B = diagonal (fun i =>
      ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i : ℂ)) := by
    have hBdag : Bᴴ = Uᴴ * Aᴴ * U := by
      rw [hBdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have heq : Bᴴ * B = Uᴴ * (Aᴴ * A) * U := by
      rw [hBdag, hBdef,
        show Uᴴ * Aᴴ * U * (Uᴴ * A * U) = Uᴴ * Aᴴ * (U * Uᴴ) * A * U by noncomm_ring, hUUs]
      noncomm_ring
    rw [heq, eigenvectorUnitary_conj_eq_diagonal
      (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian]
  clear_value B U
  have hdiag : ∀ i, Complex.normSq (B i i) ≤
      (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i := by
    intro i
    have h := normSq_diag_le_re_conjTranspose_mul_self B i
    rwa [hBB, Matrix.diagonal_apply_eq, Complex.ofReal_re] at h
  rw [htr]
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  calc ∑ i, (B i i).re
      ≤ ∑ i, Real.sqrt
          ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i) :=
        Finset.sum_le_sum fun i _ => by
          have h1 : (B i i).re ≤ Real.sqrt (Complex.normSq (B i i)) :=
            calc (B i i).re ≤ |(B i i).re| := le_abs_self _
              _ = Real.sqrt ((B i i).re ^ 2) := (Real.sqrt_sq_eq_abs _).symm
              _ ≤ Real.sqrt (Complex.normSq (B i i)) := Real.sqrt_le_sqrt (by
                  rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg (B i i).im])
          exact h1.trans (Real.sqrt_le_sqrt (hdiag i))
    _ = traceNorm A := by
        rw [traceNorm_eq_sqrtRootSum, sqrtRootSum,
          (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.roots_charpoly_eq_eigenvalues,
          Multiset.map_map, Finset.sum_eq_multiset_sum]
        exact congrArg Multiset.sum (Multiset.map_congr rfl fun i _ => by
          simp [Function.comp_apply, Complex.ofReal_re])

/-- **Hermitian dual-norm bound `Re tr(H·R) ≤ ‖H‖₁`** for Hermitian `H` and a Loewner contraction
`−1 ≤ R ≤ 1` (`1−R` and `1+R` PSD). Diagonalize `H = U diag(λ) Uᴴ`; then
`Re tr(HR) = ∑ λᵢ Re(UᴴRU)ᵢᵢ` with `Re(UᴴRU)ᵢᵢ ∈ [−1,1]` (diagonal of the PSD `Uᴴ(1∓R)U`), so
`≤ ∑ |λᵢ| = ‖H‖₁`. The keystone of the Powers–Størmer / FvdG-lower argument. -/
theorem re_trace_mul_le_traceNorm_hermitian {H R : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hR1 : (1 - R).PosSemidef) (hR2 : (1 + R).PosSemidef) :
    (H * R).trace.re ≤ traceNorm H := by
  set U : Matrix ι ι ℂ := (↑hH.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  have hUUs : U * Uᴴ = 1 := by
    have h := hH.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h; exact h
  have hUsU : Uᴴ * U = 1 := by
    have h := hH.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h; exact h
  set G : Matrix ι ι ℂ := Uᴴ * R * U with hGdef
  -- spectral form
  have hHspec : H = U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ := by
    have hd := eigenvectorUnitary_conj_eq_diagonal hH
    calc H = U * (Uᴴ * H * U) * Uᴴ := by
              rw [show U * (Uᴴ * H * U) * Uᴴ = (U * Uᴴ) * H * (U * Uᴴ) by noncomm_ring, hUUs,
                Matrix.one_mul, Matrix.mul_one]
      _ = U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ := by rw [hd]
  -- G's diagonal real part lies in [-1, 1]
  have hGub : ∀ i, (G i i).re ≤ 1 := by
    intro i
    have hP : (Uᴴ * (1 - R) * U).PosSemidef := by
      have h := hR1.conjTranspose_mul_mul_same U
      simpa [Matrix.conjTranspose_conjTranspose] using h
    have hdg : (0 : ℂ) ≤ (Uᴴ * (1 - R) * U) i i := hP.diag_nonneg
    have he : (Uᴴ * (1 - R) * U) i i = 1 - G i i := by
      rw [hGdef]
      rw [show Uᴴ * (1 - R) * U = Uᴴ * U - Uᴴ * R * U by noncomm_ring, hUsU]
      simp [Matrix.sub_apply, Matrix.one_apply_eq]
    rw [he] at hdg
    have := (Complex.le_def.mp hdg).1
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hGlb : ∀ i, -1 ≤ (G i i).re := by
    intro i
    have hP : (Uᴴ * (1 + R) * U).PosSemidef := by
      have h := hR2.conjTranspose_mul_mul_same U
      simpa [Matrix.conjTranspose_conjTranspose] using h
    have hdg : (0 : ℂ) ≤ (Uᴴ * (1 + R) * U) i i := hP.diag_nonneg
    have he : (Uᴴ * (1 + R) * U) i i = 1 + G i i := by
      rw [hGdef]
      rw [show Uᴴ * (1 + R) * U = Uᴴ * U + Uᴴ * R * U by noncomm_ring, hUsU]
      simp [Matrix.add_apply, Matrix.one_apply_eq]
    rw [he] at hdg
    have := (Complex.le_def.mp hdg).1
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  -- trace identity
  have htr : (H * R).trace = ∑ i, (hH.eigenvalues i : ℂ) * G i i := by
    have h1 : (H * R).trace = (diagonal (fun i => (hH.eigenvalues i : ℂ)) * G).trace := by
      conv_lhs => rw [hHspec]
      rw [show U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ * R
            = U * (diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ * R) by noncomm_ring,
        Matrix.trace_mul_comm,
        show diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ * R * U
            = diagonal (fun i => (hH.eigenvalues i : ℂ)) * G by rw [hGdef]; noncomm_ring]
    rw [h1, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [htr, Complex.re_sum, traceNorm_hermitian hH]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith [hGub i, hGlb i, le_abs_self (hH.eigenvalues i), neg_abs_le (hH.eigenvalues i)]

/-! ### The sign operator `sgn(S)` and `S·sgn(S) = |S|` (FvdG-lower, Powers–Størmer pieces) -/

/-- The matrix cfc is additive: `cfc f M + cfc g M = cfc (f+g) M`. -/
theorem cfc_add {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (f g : ℝ → ℝ) :
    hM.cfc f + hM.cfc g = hM.cfc (fun x => f x + g x) := by
  have hfun : (fun i => (RCLike.ofReal ∘ f ∘ hM.eigenvalues) i
        + (RCLike.ofReal ∘ g ∘ hM.eigenvalues) i)
      = (RCLike.ofReal ∘ (fun x => f x + g x) ∘ hM.eigenvalues : ι → ℂ) := by
    funext i; simp only [Function.comp_apply]; push_cast; ring
  rw [Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, ← map_add,
    Matrix.diagonal_add, hfun]

/-- `cfc(const 1) M = 1` (the cfc is a unital star-algebra map: `diagonal 1 ↦ 1`). -/
theorem cfc_one {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    hM.cfc (fun _ => (1:ℝ)) = 1 := by
  have hfun : (RCLike.ofReal ∘ (fun _ => (1:ℝ)) ∘ hM.eigenvalues : ι → ℂ) = 1 := by
    funext i; simp
  rw [Matrix.IsHermitian.cfc, hfun, show (Matrix.diagonal (1 : ι → ℂ)) = 1 from
    Matrix.diagonal_one, map_one]

/-- The **sign operator** of a Hermitian matrix, `cfc(sgn)S` with `sgn(x) = 1, 0, −1` for
`x >, =, < 0`. The keystone's Loewner contraction in the Powers–Størmer argument. -/
noncomputable def signOp {S : Matrix ι ι ℂ} (hS : S.IsHermitian) : Matrix ι ι ℂ :=
  hS.cfc (fun x => if 0 < x then (1:ℝ) else if x < 0 then -1 else 0)

theorem signOp_isHermitian {S : Matrix ι ι ℂ} (hS : S.IsHermitian) :
    (signOp hS).IsHermitian := cfc_isHermitian hS _

/-- `1 − sgn(S)` is PSD (`1 − sgn(x) ∈ {0,1,2} ≥ 0`). -/
theorem one_sub_signOp_posSemidef {S : Matrix ι ι ℂ} (hS : S.IsHermitian) :
    (1 - signOp hS).PosSemidef := by
  rw [signOp, ← cfc_one hS, cfc_sub]
  exact cfc_posSemidef hS fun i => by split_ifs <;> norm_num

/-- `1 + sgn(S)` is PSD (`1 + sgn(x) ∈ {0,1,2} ≥ 0`). -/
theorem one_add_signOp_posSemidef {S : Matrix ι ι ℂ} (hS : S.IsHermitian) :
    (1 + signOp hS).PosSemidef := by
  rw [signOp, ← cfc_one hS, cfc_add]
  exact cfc_posSemidef hS fun i => by split_ifs <;> norm_num

/-- **`S · sgn(S) = |S| = posPart S + negPart S`** — the operator modulus, via `cfc_mul`
(`x · sgn(x) = |x| = max(x,0) + max(−x,0)`). -/
theorem self_mul_signOp {S : Matrix ι ι ℂ} (hS : S.IsHermitian) :
    S * signOp hS = posPart hS + negPart hS := by
  have h := cfc_mul hS (fun x => x) (fun x => if 0 < x then (1:ℝ) else if x < 0 then -1 else 0)
  rw [cfc_id hS] at h
  rw [signOp, h, posPart, negPart, cfc_add]
  exact cfc_congr_eig hS fun i => by
    rcases lt_trichotomy (hS.eigenvalues i) 0 with hlt | heq | hgt
    · rw [if_neg (not_lt.mpr hlt.le), if_pos hlt, max_eq_right hlt.le,
        max_eq_left (neg_nonneg.mpr hlt.le)]; ring
    · simp [heq]
    · rw [if_pos hgt, max_eq_left hgt.le, max_eq_right (by linarith : -hS.eigenvalues i ≤ 0)]; ring

/-- **`sgn(S) · S = |S|`** — the modulus from the other side (cfc commutes). -/
theorem signOp_mul_self {S : Matrix ι ι ℂ} (hS : S.IsHermitian) :
    signOp hS * S = posPart hS + negPart hS := by
  have h := cfc_mul hS (fun x => if 0 < x then (1:ℝ) else if x < 0 then -1 else 0) (fun x => x)
  rw [cfc_id hS] at h
  rw [signOp, h, posPart, negPart, cfc_add]
  exact cfc_congr_eig hS fun i => by
    rcases lt_trichotomy (hS.eigenvalues i) 0 with hlt | heq | hgt
    · rw [if_neg (not_lt.mpr hlt.le), if_pos hlt, max_eq_right hlt.le,
        max_eq_left (neg_nonneg.mpr hlt.le)]; ring
    · simp [heq]
    · rw [if_pos hgt, max_eq_left hgt.le, max_eq_right (by linarith : -hS.eigenvalues i ≤ 0)]; ring

/-- `cfc(const 0) M = 0` (the cfc maps `diagonal 0 ↦ 0`). -/
theorem cfc_zero {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    hM.cfc (fun _ => (0:ℝ)) = 0 := by
  have hfun : (RCLike.ofReal ∘ (fun _ => (0:ℝ)) ∘ hM.eigenvalues : ι → ℂ) = 0 := by
    funext i; simp
  rw [Matrix.IsHermitian.cfc, hfun, show (Matrix.diagonal (0 : ι → ℂ)) = 0 from
    Matrix.diagonal_zero, map_zero]

/-- **`posPart S · negPart S = 0`** — the positive and negative parts are orthogonal
(`max(x,0)·max(−x,0) = 0` pointwise). -/
theorem posPart_mul_negPart_eq_zero {S : Matrix ι ι ℂ} (hS : S.IsHermitian) :
    posPart hS * negPart hS = 0 := by
  rw [posPart, negPart, cfc_mul, ← cfc_zero hS]
  exact cfc_congr_eig hS fun i => by
    rcases le_total (hS.eigenvalues i) 0 with h | h
    · rw [max_eq_right h, zero_mul]
    · rw [max_eq_right (neg_nonpos.mpr h), mul_zero]

/-- **Fuchs–van de Graaf LOWER bound `1 − F(ρ,σ) ≤ D(ρ,σ)`** for density operators, via the
Powers–Størmer inequality. Let `S = √ρ−√σ = P−Q` (`P=posPart,Q=negPart`, `PQ=0`), `T=√ρ+√σ`.
Then `tr((ρ−σ)·sgn(S)) = tr(T·|S|) ≥ tr(S²)` (the posPart/negPart bound `tr(√ρ·P)≥tr(P²)`,
`tr(Q·√σ)≥tr(Q²)`; no `|S|≤T` needed), and `tr(S²) = 2−2tr(√σ√ρ)`. The dual-norm keystone
gives `tr((ρ−σ)·sgn(S)).re ≤ ‖ρ−σ‖₁ = 2D`, so `1−tr(√σ√ρ).re ≤ D`; and `tr(√σ√ρ).re ≤ F`
(`re_trace_le_traceNorm`), whence `1−F ≤ D`. -/
theorem one_sub_sqrtFidelity_le_traceDist {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (htρ : ρ.trace = 1) (htσ : σ.trace = 1) :
    1 - sqrtFidelity hρ hσ ≤ traceDist ρ σ := by
  set rt := psdSqrt hρ with hrt
  set st := psdSqrt hσ with hst
  have hrtP : rt.PosSemidef := psdSqrt_posSemidef hρ
  have hstP : st.PosSemidef := psdSqrt_posSemidef hσ
  set S := rt - st with hSdef
  have hSh : S.IsHermitian := (psdSqrt_isHermitian hρ).sub (psdSqrt_isHermitian hσ)
  set P := posPart hSh with hPdef
  set Q := negPart hSh with hQdef
  have hPP : P.PosSemidef := posPart_posSemidef hSh
  have hQP : Q.PosSemidef := negPart_posSemidef hSh
  have hrr : rt * rt = ρ := by rw [hrt, psdSqrt_mul_self hρ]
  have hss : st * st = σ := by rw [hst, psdSqrt_mul_self hσ]
  have hPQ0 : (P * Q).trace = 0 := by rw [hPdef, hQdef, posPart_mul_negPart_eq_zero hSh, trace_zero]
  have hQP0 : (Q * P).trace = 0 := by rw [Matrix.trace_mul_comm, hPdef, hQdef,
    posPart_mul_negPart_eq_zero hSh, trace_zero]
  have hSpq : S = P - Q := self_eq_posPart_sub_negPart hSh
  have heq : rt - st = P - Q := by rw [← hSdef]; exact hSpq
  -- (1) ρ − σ = rt*S + S*st
  have hρσ : ρ - σ = rt * S + S * st := by
    rw [hSdef, mul_sub, sub_mul, hrr, hss]; abel
  -- (2) trace identity: tr((ρ−σ)·sgn S) = tr(rt·(P+Q)) + tr((P+Q)·st)
  have hterm1 : (rt * S * signOp hSh).trace = (rt * (P + Q)).trace := by
    rw [Matrix.mul_assoc, self_mul_signOp hSh, ← hPdef, ← hQdef]
  have hterm2 : (S * st * signOp hSh).trace = ((P + Q) * st).trace := by
    rw [Matrix.trace_mul_comm (S * st) (signOp hSh), ← Matrix.mul_assoc, signOp_mul_self hSh,
      ← hPdef, ← hQdef]
  have htr_eq : ((ρ - σ) * signOp hSh).trace
      = (rt * (P + Q)).trace + ((P + Q) * st).trace := by
    rw [hρσ, add_mul, Matrix.trace_add, hterm1, hterm2]
  -- (3) Powers–Størmer core: tr(S²) ≤ tr((ρ−σ)·sgn S)
  have hAP : (P * P).trace.re ≤ (rt * P).trace.re := by
    have hAdecomp : rt = st + P - Q := by linear_combination (norm := abel) heq
    have hexp : (rt * P).trace = (st * P).trace + (P * P).trace - (Q * P).trace := by
      rw [hAdecomp, sub_mul, add_mul, Matrix.trace_sub, Matrix.trace_add]
    rw [hexp, hQP0, sub_zero, Complex.add_re]
    have := (Complex.le_def.mp (trace_mul_nonneg hstP hPP)).1; simp only [Complex.zero_re] at this
    linarith
  have hQB : (Q * Q).trace.re ≤ (Q * st).trace.re := by
    have hBdecomp : st = rt - P + Q := by linear_combination (norm := abel) -heq
    have hexp : (Q * st).trace = (Q * rt).trace - (Q * P).trace + (Q * Q).trace := by
      rw [hBdecomp, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
    rw [hexp, hQP0, sub_zero, Complex.add_re]
    have := (Complex.le_def.mp (trace_mul_nonneg hQP hrtP)).1; simp only [Complex.zero_re] at this
    linarith
  have hps : (S * S).trace.re ≤ ((ρ - σ) * signOp hSh).trace.re := by
    rw [htr_eq, Complex.add_re, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add,
      Complex.add_re, Complex.add_re]
    have hAQ := (Complex.le_def.mp (trace_mul_nonneg hrtP hQP)).1
    have hPB := (Complex.le_def.mp (trace_mul_nonneg hPP hstP)).1
    simp only [Complex.zero_re] at hAQ hPB
    have hSS : (S * S).trace.re = (P * P).trace.re + (Q * Q).trace.re := by
      have : S * S = P * P - P * Q - Q * P + Q * Q := by rw [hSpq]; noncomm_ring
      rw [this, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, hPQ0, hQP0]
      simp [Complex.add_re]
    rw [hSS]; linarith
  -- (4) tr(S²) = 2 − 2·tr(√σ√ρ)
  have hSsq : (S * S).trace.re = 2 - 2 * (st * rt).trace.re := by
    have hSS : S * S = ρ - rt * st - st * rt + σ := by
      rw [hSdef, sub_mul, mul_sub, mul_sub, hrr, hss]; abel
    rw [hSS, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, htρ, htσ,
      Matrix.trace_mul_comm rt st]
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re]; ring
  -- (5) assemble
  have hkey : ((ρ - σ) * signOp hSh).trace.re ≤ traceNorm (ρ - σ) :=
    re_trace_mul_le_traceNorm_hermitian (hρ.isHermitian.sub hσ.isHermitian)
      (one_sub_signOp_posSemidef hSh) (one_add_signOp_posSemidef hSh)
  have hF : (st * rt).trace.re ≤ sqrtFidelity hρ hσ := by
    rw [sqrtFidelity, hst, hrt]; exact re_trace_le_traceNorm _
  rw [traceDist]
  have h2D : 2 - 2 * (st * rt).trace.re ≤ traceNorm (ρ - σ) := by
    calc 2 - 2 * (st * rt).trace.re = (S * S).trace.re := hSsq.symm
      _ ≤ ((ρ - σ) * signOp hSh).trace.re := hps
      _ ≤ traceNorm (ρ - σ) := hkey
  rw [hst, hrt] at hF
  nlinarith [hF, h2D]

/-
## Fuchs–van de Graaf bounds (6AF-7 remainder) — status after the FENCE-GATE sweep (2026-06-01)

`F ≤ 1` is proven above. The two FvdG bounds `1 − F ≤ D ≤ √(1 − F²)` split (verified by a
fresh 2-agent toehold sweep + roadmap re-read, per the fence discipline):

* **`D ≤ √(1 − F²)` (upper) — DEFERRED but REACHABLE (route known; no sorry, no axiom).**
  ⚠️ **FENCE-WAS-TOO-WIDE CATCH (2026-06-02, DR `Lit-Search/Phase-6AF/…Blueprints…Phase 6AF.md`):**
  the earlier note claimed "every route needs Uhlmann purification (absent), hence multi-week."
  Uhlmann IS absent — but that does NOT make the bound unreachable: the DR found a **purification-FREE**
  finite-dim route via **Holevo–Helstrom + classical Fuchs–van de Graaf**, reusing the shipped
  trace-distance / `eigPosSum` / `posProj` / `re_trace_proj_mul_le_eigPosSum` / matrix-CS substrate.
  Sketch: (1) Helstrom rep `D(ρ,σ) = max_{0≤E≤1} (tr(E(ρ−σ))).re`, attained at `E = posProj(ρ−σ)`
  (project substrate nearly in hand); (2) classical FvdG on reals `(½‖p−q‖₁)² + (∑√(pᵢqᵢ))² ≤ 1`
  (AM-GM, pure ℝ); (3) the crux `fidelity_monotone_under_kraus` (fidelity data-processing, the dual
  of the shipped `traceDist_krausMap_le`, ~8 lemmas via the matrix-CS keystone). LOE ≈ 18–25 lemmas
  (the `fidelity_monotone_under_kraus` sub-build is the hardest). Deferred as a dedicated follow-on
  sub-wave, NOT blocked — the "needs Uhlmann" framing was the over-wide fence.

* **`1 − F ≤ D` (lower) — ✅ PROVEN** as `one_sub_sqrtFidelity_le_traceDist` above (kernel-pure,
  no `maxHeartbeats`). The Powers–Størmer route, but with the `|S| ≤ T` Loewner step REMOVED (it is
  non-trivial / possibly false for non-commuting `√ρ, √σ`). Instead, with `S = √ρ−√σ = P−Q`
  (`P = posPart, Q = negPart`, `PQ = 0`), `T = √ρ+√σ`:
  - `tr((ρ−σ)·sgn(S)) = tr(T·|S|)` via `S·sgn(S) = sgn(S)·S = |S| = P+Q` (`self_mul_signOp` /
    `signOp_mul_self`) and `ρ−σ = √ρ·S + S·√σ`;
  - `tr(T·|S|) ≥ tr(S²)` directly from `√ρ = √σ + P − Q` ⟹ `tr(√ρ·P) = tr(√σ·P) + tr(P²) ≥ tr(P²)`
    and `tr(Q·√σ) ≥ tr(Q²)` (`trace_mul_nonneg`), dropping the nonneg cross terms — NO `|S|≤T`;
  - `tr((ρ−σ)·sgn(S)).re ≤ ‖ρ−σ‖₁` by the dual-norm-Hermitian keystone
    `re_trace_mul_le_traceNorm_hermitian` (`−1 ≤ sgn(S) ≤ 1` via `one_sub/​one_add_signOp_posSemidef`);
  - `tr(S²) = 2 − 2 tr(√σ√ρ)` and `tr(√σ√ρ).re ≤ F` (`re_trace_le_traceNorm`) ⟹ `1 − F ≤ D`.
  The whnf "wall" hit while proving `re_trace_le_traceNorm` (piece B) was an INEFFICIENCY, not an
  intrinsic limit: `set`-bound eigenvector unitaries are reducible, so per-entry access forces a
  spectral whnf-explosion. FIX (no `maxHeartbeats`): prove the diagonal bound as a generic lemma over
  an ABSTRACT `M` (`normSq_diag_le_re_conjTranspose_mul_self`) + `clear_value`. **Lesson: "spectral
  whnf timeout" ⟹ abstract the heavy term, do NOT bump heartbeats.** Only the FvdG-UPPER bound
  remains fenced (Uhlmann purification, above).
-/

end SKEFTHawking.QuantumNetwork

