import SKEFTHawking.QuantumNetwork.FidelityForwardBound
import SKEFTHawking.QuantumNetwork.FidelityBounds
import SKEFTHawking.QuantumNetwork.DiamondNormChoi
import SKEFTHawking.QuantumNetwork.DiamondNormAttainment

/-!
# Forward Alberti bound for positive-SEMIdefinite states (Phase 6AJ — rank-deficient outputs)

Relaxes `re_trace_block_le_sqrtFidelity` from positive-DEFINITE `ρ,σ` to positive-SEMIdefinite
`ρ,σ`, removing the full-rank regularity from the general-CPTP fidelity data-processing theorem so it
holds for arbitrary (possibly rank-deficient) channel outputs.

The Schur-complement forward bound needs `σ⁻¹`, hence `σ` invertible. We discharge the singular case
by **ε-regularization along the commuting ray** `ρ_ε = ρ + ε·1`: the regularized inputs are positive
definite, the block stays PSD (adds `ε·1` on the diagonal blocks), and `F(ρ_ε,σ_ε) → F(ρ,σ)` as
`ε → 0⁺`. The convergence is the crux: the project's `psdSqrt` is the CFC-via-eigendecomposition sqrt,
and matrix-sqrt continuity in general fails to read off the eigendecomposition (eigenvectors jump). But
**along the commuting ray the eigenbasis is fixed** — `ρ + ε·1` has the *same* eigenvectors as `ρ` —
so by PSD-square-root uniqueness `psdSqrt(ρ + ε·1) = U·diag(√(λᵢ+ε))·Uᴴ` with `U` *fixed* (`ρ`'s
eigenvector unitary), making continuity in `ε` elementary. No `CFC.continuousOn_sqrt` (whose isometric
non-unital CFC instance is unavailable on bare `Matrix`), no `CStarMatrix` detour, no Powers–Størmer
modulus bound.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix Filter Topology
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **PSD square root along the regularizing ray, explicit fixed-eigenbasis form.** For `c ≥ 0`,
`psdSqrt(ρ + c·1) = U · diag(√(λᵢ+c)) · Uᴴ`, where `U` is `ρ`'s eigenvector unitary and `λ` its
eigenvalues. The point is that `U` does **not** depend on `c` (the ray commutes with `ρ`), so this is
the vehicle for continuity in `c`. Proven by PSD-square-root uniqueness
(`posSemidef_eq_of_mul_self_eq`): both sides are PSD and both square to `ρ + c·1`. -/
theorem psdSqrt_eq_conj_diag {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (hρc : (ρ + (c : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef) :
    psdSqrt hρc = (↑hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)
        * diagonal (fun i => (Real.sqrt (hρ.isHermitian.eigenvalues i + c) : ℂ))
        * (↑hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  set U : Matrix ι ι ℂ := (↑hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  have hUsU : Uᴴ * U = 1 := by
    have h := hρ.isHermitian.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h; exact h
  have hUUs : U * Uᴴ = 1 := by
    have h := hρ.isHermitian.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h; exact h
  have hfnn : ∀ i, 0 ≤ hρ.isHermitian.eigenvalues i := hρ.eigenvalues_nonneg
  have hρspec : ρ = U * diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ)) * Uᴴ := by
    have hd := eigenvectorUnitary_conj_eq_diagonal hρ.isHermitian
    rw [← hUdef] at hd
    calc ρ = (U * Uᴴ) * ρ * (U * Uᴴ) := by rw [hUUs, Matrix.one_mul, Matrix.mul_one]
      _ = U * (Uᴴ * ρ * U) * Uᴴ := by noncomm_ring
      _ = U * diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ)) * Uᴴ := by rw [hd]
  set s : ι → ℂ := fun i => (Real.sqrt (hρ.isHermitian.eigenvalues i + c) : ℂ) with hsdef
  have hsnn : ∀ i, (0 : ℂ) ≤ s i := fun i => by
    rw [hsdef]; exact Mathlib.Meta.Positivity.ofReal_nonneg (Real.sqrt_nonneg _)
  have hRHS : U * diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ) + (c : ℂ)) * Uᴴ
      = ρ + (c : ℂ) • (1 : Matrix ι ι ℂ) := by
    have hsplit : diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ) + (c : ℂ))
        = diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ)) + diagonal (fun _ : ι => (c : ℂ)) :=
      (Matrix.diagonal_add _ _).symm
    rw [hsplit, Matrix.mul_add, Matrix.add_mul, ← hρspec,
      show diagonal (fun _ : ι => (c : ℂ)) = (c : ℂ) • (1 : Matrix ι ι ℂ) from
        (Matrix.smul_one_eq_diagonal _).symm, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUUs]
  refine posSemidef_eq_of_mul_self_eq (psdSqrt_posSemidef hρc)
    (posSemidef_unitary_conj U (Matrix.PosSemidef.diagonal hsnn)) ?_
  rw [psdSqrt_mul_self, ← hRHS]
  have hsq : diagonal s * diagonal s
      = diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ) + (c : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt (add_nonneg (hfnn i) hc), Complex.ofReal_add]
  rw [show (U * diagonal s * Uᴴ) * (U * diagonal s * Uᴴ)
      = U * (diagonal s * (Uᴴ * U) * diagonal s) * Uᴴ by noncomm_ring, hUsU, Matrix.mul_one, hsq]

/-- The `c = 0` endpoint of `psdSqrt_eq_conj_diag`: `psdSqrt ρ = U · diag(√λᵢ) · Uᴴ`. -/
theorem psdSqrt_eq_conj_diag0 {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    psdSqrt hρ = (↑hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)
        * diagonal (fun i => (Real.sqrt (hρ.isHermitian.eigenvalues i) : ℂ))
        * (↑hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  set U : Matrix ι ι ℂ := (↑hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  have hUsU : Uᴴ * U = 1 := by
    have h := hρ.isHermitian.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h; exact h
  have hUUs : U * Uᴴ = 1 := by
    have h := hρ.isHermitian.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h; exact h
  have hfnn : ∀ i, 0 ≤ hρ.isHermitian.eigenvalues i := hρ.eigenvalues_nonneg
  have hρspec : ρ = U * diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ)) * Uᴴ := by
    have hd := eigenvectorUnitary_conj_eq_diagonal hρ.isHermitian
    rw [← hUdef] at hd
    calc ρ = (U * Uᴴ) * ρ * (U * Uᴴ) := by rw [hUUs, Matrix.one_mul, Matrix.mul_one]
      _ = U * (Uᴴ * ρ * U) * Uᴴ := by noncomm_ring
      _ = U * diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ)) * Uᴴ := by rw [hd]
  set s : ι → ℂ := fun i => (Real.sqrt (hρ.isHermitian.eigenvalues i) : ℂ) with hsdef
  have hsnn : ∀ i, (0 : ℂ) ≤ s i := fun i => by
    rw [hsdef]; exact Mathlib.Meta.Positivity.ofReal_nonneg (Real.sqrt_nonneg _)
  refine posSemidef_eq_of_mul_self_eq (psdSqrt_posSemidef hρ)
    (posSemidef_unitary_conj U (Matrix.PosSemidef.diagonal hsnn)) ?_
  rw [psdSqrt_mul_self]
  have hsq : diagonal s * diagonal s = diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt (hfnn i)]
  rw [hρspec, show (U * diagonal s * Uᴴ) * (U * diagonal s * Uᴴ)
      = U * (diagonal s * (Uᴴ * U) * diagonal s) * Uᴴ by noncomm_ring, hUsU, Matrix.mul_one, hsq]

/-- **Convergence of `psdSqrt` along the regularizing ray.** If `c k ≥ 0` and `c k → 0`, then
`psdSqrt(ρ + c k·1) → psdSqrt ρ`. The fixed eigenbasis (`psdSqrt_eq_conj_diag`) reduces this to
continuity of the diagonal map `c ↦ diag(√(λᵢ+c))`. -/
theorem tendsto_psdSqrt_perturb {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k) (hc : Tendsto c atTop (𝓝 0))
    (hρc : ∀ k, (ρ + (c k : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef) :
    Tendsto (fun k => psdSqrt (hρc k)) atTop (𝓝 (psdSqrt hρ)) := by
  set U : Matrix ι ι ℂ := (↑hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  set lam : ι → ℝ := hρ.isHermitian.eigenvalues with hlamdef
  set g : ℝ → Matrix ι ι ℂ :=
    fun t => U * diagonal (fun i => (Real.sqrt (lam i + t) : ℂ)) * Uᴴ with hgdef
  have hg : Continuous g := by
    have hdiag : Continuous (fun t : ℝ => diagonal (fun i => (Real.sqrt (lam i + t) : ℂ))) :=
      Continuous.matrix_diagonal (continuous_pi fun i =>
        Complex.continuous_ofReal.comp
          (Real.continuous_sqrt.comp (continuous_const.add continuous_id)))
    exact (continuous_const.matrix_mul hdiag).matrix_mul continuous_const
  have hkey : (fun k => psdSqrt (hρc k)) = fun k => g (c k) := by
    funext k; rw [psdSqrt_eq_conj_diag hρ (hc0 k) (hρc k)]
  have hg0 : g 0 = psdSqrt hρ := by
    rw [hgdef]; simp only [add_zero]; rw [← psdSqrt_eq_conj_diag0 hρ]
  rw [hkey, ← hg0]
  exact (hg.tendsto 0).comp hc

omit [Fintype ι] in
/-- The fidelity block adds a scalar on its diagonal blocks under `ρ,σ ↦ ρ+c·1, σ+c·1`:
`fidelityBlock (ρ+c·1) X (σ+c·1) = fidelityBlock ρ X σ + c·1`. -/
theorem fidelityBlock_add_smul_one (ρ X σ : Matrix ι ι ℂ) (c : ℂ) :
    fidelityBlock (ρ + c • (1 : Matrix ι ι ℂ)) X (σ + c • (1 : Matrix ι ι ℂ))
      = fidelityBlock ρ X σ + c • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  unfold fidelityBlock
  rw [show (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) = fromBlocks 1 0 0 1 from (Matrix.fromBlocks_one).symm,
    Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
  simp

/-- **Forward Alberti bound for positive-SEMIdefinite states.** `[[ρ,X],[Xᴴ,σ]] ⪰ 0 ⟹ Re tr X ≤
F(ρ,σ)` for `ρ,σ` merely positive *semidefinite*. Proven from the positive-definite case
(`re_trace_block_le_sqrtFidelity`) by ε-regularizing along the ray `ρ+ε·1` and passing to the limit
`ε → 0⁺` with `tendsto_psdSqrt_perturb` + `continuous_traceNorm`. -/
theorem re_trace_block_le_sqrtFidelity_psd [Nonempty ι] {ρ X σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hblock : (fidelityBlock ρ X σ).PosSemidef) :
    X.trace.re ≤ sqrtFidelity hρ hσ := by
  set c : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹ with hcdef
  have hc0 : ∀ k, 0 < c k := fun k => by rw [hcdef]; positivity
  have hclim : Tendsto c atTop (𝓝 0) := by
    have heq : c = fun n : ℕ => 1 / ((n : ℝ) + 1) := by funext n; rw [hcdef, one_div]
    rw [heq]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hcc : ∀ k, (0 : ℂ) ≤ (c k : ℂ) := fun k =>
    Mathlib.Meta.Positivity.ofReal_nonneg (hc0 k).le
  have hccp : ∀ k, (0 : ℂ) < (c k : ℂ) := fun k => by exact_mod_cast hc0 k
  have hsmulPSD : ∀ k, ((c k : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := fun k =>
    (Matrix.PosSemidef.one).smul (hcc k)
  have hsmulPD : ∀ k, ((c k : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := fun k =>
    (Matrix.PosDef.one).smul (hccp k)
  have hρk : ∀ k, (ρ + (c k : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := fun k => hρ.add (hsmulPSD k)
  have hσk : ∀ k, (σ + (c k : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := fun k => hσ.add (hsmulPSD k)
  have hρkd : ∀ k, (ρ + (c k : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := fun k => by
    rw [add_comm]; exact (hsmulPD k).add_posSemidef hρ
  have hσkd : ∀ k, (σ + (c k : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := fun k => by
    rw [add_comm]; exact (hsmulPD k).add_posSemidef hσ
  have hblockk : ∀ k, (fidelityBlock (ρ + (c k : ℂ) • 1) X (σ + (c k : ℂ) • 1)).PosSemidef :=
    fun k => by
      rw [fidelityBlock_add_smul_one]
      exact hblock.add ((Matrix.PosSemidef.one).smul (hcc k))
  have hbound : ∀ k, X.trace.re ≤ sqrtFidelity (hρkd k).posSemidef (hσkd k).posSemidef := fun k =>
    re_trace_block_le_sqrtFidelity (hρkd k) (hσkd k) (hblockk k)
  have hpρ : Tendsto (fun k => psdSqrt (hρk k)) atTop (𝓝 (psdSqrt hρ)) :=
    tendsto_psdSqrt_perturb hρ (fun k => (hc0 k).le) hclim hρk
  have hpσ : Tendsto (fun k => psdSqrt (hσk k)) atTop (𝓝 (psdSqrt hσ)) :=
    tendsto_psdSqrt_perturb hσ (fun k => (hc0 k).le) hclim hσk
  have hF : Tendsto (fun k => sqrtFidelity (hρkd k).posSemidef (hσkd k).posSemidef) atTop
      (𝓝 (sqrtFidelity hρ hσ)) := by
    have heq : (fun k => sqrtFidelity (hρkd k).posSemidef (hσkd k).posSemidef)
        = fun k => traceNorm (psdSqrt (hσk k) * psdSqrt (hρk k)) := rfl
    rw [heq, show sqrtFidelity hρ hσ = traceNorm (psdSqrt hσ * psdSqrt hρ) from rfl]
    exact (continuous_traceNorm.tendsto _).comp (hpσ.mul hpρ)
  exact ge_of_tendsto hF (Filter.Eventually.of_forall hbound)

end SKEFTHawking.QuantumNetwork
