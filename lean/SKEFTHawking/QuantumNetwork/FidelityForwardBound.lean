import SKEFTHawking.QuantumNetwork.FidelityBlockForm
import SKEFTHawking.QuantumNetwork.OpNormHolder

/-!
# Forward Alberti bound (Phase 6AJ continuation, brick 4)

`Re tr X ≤ F(ρ,σ)` whenever the fidelity block `[[ρ,X],[Xᴴ,σ]]` is PSD (positive-definite `ρ,σ`).
The Schur complement (`fidelityBlock_posDef_schur`) exhibits `X = √ρ·K·√σ` with the contraction
`K = √ρ⁻¹·X·√σ⁻¹` satisfying `1 − K·Kᴴ = √ρ⁻¹·(ρ − Xσ⁻¹Xᴴ)·√ρ⁻¹ ⪰ 0`; then
`Re tr X = Re tr(K·√σ√ρ) ≤ ‖K‖·‖√σ√ρ‖₁ ≤ ‖√σ√ρ‖₁ = F` (brick 3b `re_trace_mul_le_opNorm_mul_traceNorm`
+ brick 4a `opNorm_le_one_of_mul_conjTranspose_le_one`).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `psdSqrt` of an invertible PSD matrix is invertible (its square `M` is a unit). -/
theorem isUnit_psdSqrt {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (hMu : IsUnit M) :
    IsUnit (psdSqrt hM) := by
  have h2 : IsUnit (psdSqrt hM * psdSqrt hM) := by rw [psdSqrt_mul_self]; exact hMu
  rw [← pow_two] at h2
  exact (isUnit_pow_iff two_ne_zero).mp h2

/-- **Forward Alberti bound (positive-definite case).** `[[ρ,X],[Xᴴ,σ]] ⪰ 0 ⟹ Re tr X ≤ F(ρ,σ)`. -/
theorem re_trace_block_le_sqrtFidelity {ρ X σ : Matrix ι ι ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hblock : (fidelityBlock ρ X σ).PosSemidef) :
    X.trace.re ≤ sqrtFidelity hρ.posSemidef hσ.posSemidef := by
  have hSchur : (ρ - X * σ⁻¹ * Xᴴ).PosSemidef := (fidelityBlock_posDef_schur hσ).mp hblock
  set rρ := psdSqrt hρ.posSemidef with hrρ
  set rσ := psdSqrt hσ.posSemidef with hrσ
  have hrρd : IsUnit rρ.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_psdSqrt _ hρ.isUnit)
  have hrσd : IsUnit rσ.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_psdSqrt _ hσ.isUnit)
  have hrρih : (rρ⁻¹)ᴴ = rρ⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, (psdSqrt_isHermitian _).eq]
  have hrσih : (rσ⁻¹)ᴴ = rσ⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, (psdSqrt_isHermitian _).eq]
  have hrρi : rρ⁻¹ * rρ = 1 := Matrix.nonsing_inv_mul _ hrρd
  have hrρi' : rρ * rρ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hrρd
  have hrσi : rσ⁻¹ * rσ = 1 := Matrix.nonsing_inv_mul _ hrσd
  have hrσi' : rσ * rσ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hrσd
  have hrρsq : rρ * rρ = ρ := psdSqrt_mul_self _
  have hrσsq : rσ * rσ = σ := psdSqrt_mul_self _
  have hσinv : rσ⁻¹ * rσ⁻¹ = σ⁻¹ := by rw [← Matrix.mul_inv_rev, hrσsq]
  set K := rρ⁻¹ * X * rσ⁻¹ with hK
  have hXdecomp : rρ * K * rσ = X := by
    rw [hK, show rρ * (rρ⁻¹ * X * rσ⁻¹) * rσ = (rρ * rρ⁻¹) * X * (rσ⁻¹ * rσ) by noncomm_ring,
      hrρi', hrσi, Matrix.one_mul, Matrix.mul_one]
  have hKKle : ((1 : Matrix ι ι ℂ) - K * Kᴴ).PosSemidef := by
    have hconj := hSchur.conjTranspose_mul_mul_same rρ⁻¹
    rw [hrρih] at hconj
    have heq : rρ⁻¹ * (ρ - X * σ⁻¹ * Xᴴ) * rρ⁻¹ = 1 - K * Kᴴ := by
      have hKKexp : K * Kᴴ = rρ⁻¹ * X * (rσ⁻¹ * rσ⁻¹) * Xᴴ * rρ⁻¹ := by
        rw [hK, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hrρih, hrσih]; noncomm_ring
      rw [hKKexp, hσinv, Matrix.mul_sub, Matrix.sub_mul]
      congr 1
      · rw [← hrρsq, show rρ⁻¹ * (rρ * rρ) * rρ⁻¹ = (rρ⁻¹ * rρ) * (rρ * rρ⁻¹) by noncomm_ring,
          hrρi, hrρi', Matrix.one_mul]
      · noncomm_ring
    rw [heq] at hconj; exact hconj
  have hMu : IsUnit (rσ * rρ) := (isUnit_psdSqrt _ hσ.isUnit).mul (isUnit_psdSqrt _ hρ.isUnit)
  have htr : X.trace = (K * (rσ * rρ)).trace := by
    rw [← hXdecomp, show rρ * K * rσ = rρ * (K * rσ) by noncomm_ring, Matrix.trace_mul_comm,
      show K * rσ * rρ = K * (rσ * rρ) by noncomm_ring]
  rw [htr, show sqrtFidelity hρ.posSemidef hσ.posSemidef = traceNorm (rσ * rρ) from rfl]
  calc (K * (rσ * rρ)).trace.re ≤ ‖K‖ * traceNorm (rσ * rρ) :=
        re_trace_mul_le_opNorm_mul_traceNorm hMu
    _ ≤ 1 * traceNorm (rσ * rρ) :=
        mul_le_mul_of_nonneg_right (opNorm_le_one_of_mul_conjTranspose_le_one hKKle)
          (traceNorm_nonneg _)
    _ = traceNorm (rσ * rρ) := one_mul _

end SKEFTHawking.QuantumNetwork
