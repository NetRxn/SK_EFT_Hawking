import SKEFTHawking.QuantumNetwork.DiamondNormChoiUpper
import SKEFTHawking.QuantumNetwork.TraceNormCauchySchwarz
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# General operator-norm trace bound (Phase 6AJ continuation, brick 3)

`Re tr(C·P) ≤ ‖C‖ · tr P` (L2-operator norm `‖·‖`) for an **arbitrary** matrix `C` and a PSD `P`.
This generalizes the shipped Hermitian keystone `re_trace_mul_le_l2opNorm_mul_trace` to non-Hermitian
`C` via the Hermitian-part decomposition `C = H + A`, `H = ½(C+Cᴴ)` Hermitian, `A = ½(C−Cᴴ)`
anti-Hermitian: `Re tr(A·P) = 0` (the trace is purely imaginary) and `‖H‖ ≤ ‖C‖`.

This is the analytic core of the forward Alberti bound `Re tr X ≤ sqrtFidelity` — with the polar
`√σ√ρ = U·|√σ√ρ|` it gives `Re tr(K√σ√ρ) = Re tr((KU)·|√σ√ρ|) ≤ ‖KU‖·tr|√σ√ρ| ≤ ‖√σ√ρ‖₁`.
NO continuous-functional-calculus C*-instance machinery is needed.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **`Re tr(A·P) = 0` for anti-Hermitian `A` and PSD `P`** — the trace `tr(AP)` is purely imaginary,
since `conj(tr(AP)) = tr((AP)ᴴ) = tr(Pᴴ·(−A)) = −tr(AP)`. -/
theorem re_trace_antiHermitian_mul_posSemidef {A P : Matrix ι ι ℂ} (hA : Aᴴ = -A)
    (hP : P.PosSemidef) : (A * P).trace.re = 0 := by
  have hconj : (starRingEnd ℂ) ((A * P).trace) = -((A * P).trace) := by
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      hP.isHermitian.eq, hA, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
  have h := Complex.add_conj ((A * P).trace)
  rw [hconj, add_neg_cancel] at h
  have : ((A * P).trace.re : ℝ) = 0 := by
    have h2 : (2 : ℝ) * (A * P).trace.re = 0 := by exact_mod_cast h.symm
    linarith
  exact this

/-- **General operator-norm trace bound:** `Re tr(C·P) ≤ ‖C‖ · Re tr P` for any matrix `C` and any
positive-semidefinite `P`. The non-Hermitian generalization of `re_trace_mul_le_l2opNorm_mul_trace`. -/
theorem re_trace_mul_le_opNorm_mul_trace {C P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    (C * P).trace.re ≤ ‖C‖ * (P.trace).re := by
  set H : Matrix ι ι ℂ := (2⁻¹ : ℂ) • (C + Cᴴ) with hHdef
  set Asym : Matrix ι ι ℂ := (2⁻¹ : ℂ) • (C - Cᴴ) with hAdef
  have hHh : H.IsHermitian := by
    show Hᴴ = H
    rw [hHdef]
    simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, add_comm]
  have hAanti : Asymᴴ = -Asym := by
    rw [hAdef]
    simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, smul_sub, neg_sub]
  have hCdecomp : C = H + Asym := by
    rw [hHdef, hAdef, ← smul_add]
    rw [show C + Cᴴ + (C - Cᴴ) = (2 : ℂ) • C by rw [two_smul]; abel]
    rw [smul_smul]; norm_num
  have hPtr : 0 ≤ (P.trace).re := (Complex.le_def.mp hP.trace_nonneg).1.trans_eq' (by simp)
  calc (C * P).trace.re
      = (H * P).trace.re + (Asym * P).trace.re := by
        rw [hCdecomp, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    _ = (H * P).trace.re := by rw [re_trace_antiHermitian_mul_posSemidef hAanti hP, add_zero]
    _ ≤ ‖H‖ * (P.trace).re := re_trace_mul_le_l2opNorm_mul_trace hHh hP
    _ ≤ ‖C‖ * (P.trace).re := by
        apply mul_le_mul_of_nonneg_right _ hPtr
        calc ‖H‖ = 2⁻¹ * ‖C + Cᴴ‖ := by rw [hHdef, norm_smul]; simp
          _ ≤ 2⁻¹ * (‖C‖ + ‖Cᴴ‖) := by
              apply mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
          _ = ‖C‖ := by rw [← Matrix.star_eq_conjTranspose, norm_star]; ring

/-- **Op-norm/trace-norm Hölder bound (invertible case):** `Re tr(K·M) ≤ ‖K‖ · ‖M‖₁` for invertible
`M`. Via the polar `M = U·|M|` (`U = M·|M|⁻¹` unitary), `Re tr(K·M) = Re tr((K·U)·|M|) ≤ ‖K·U‖·tr|M|`
(`re_trace_mul_le_opNorm_mul_trace`, `|M|` PSD) `≤ ‖K‖·‖U‖·‖M‖₁ ≤ ‖K‖·‖M‖₁` (`‖U‖ ≤ 1`). -/
theorem re_trace_mul_le_opNorm_mul_traceNorm {K M : Matrix ι ι ℂ} (hM : IsUnit M) :
    (K * M).trace.re ≤ ‖K‖ * traceNorm M := by
  have hPh := absOp_isHermitian M
  have hPpsd := absOp_posSemidef M
  have hPd : IsUnit (absOp M).det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_absOp hM)
  set P := absOp M with hPdef
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hPih : (P⁻¹)ᴴ = P⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hPh.eq]
  have hPP : P * P = Mᴴ * M := absOp_mul_self M
  set U := M * P⁻¹ with hUdef
  have hMUP : U * P = M := by rw [hUdef, Matrix.mul_assoc, hPiP, Matrix.mul_one]
  have hUU : Uᴴ * U = 1 := by
    rw [hUdef, Matrix.conjTranspose_mul, hPih]
    calc P⁻¹ * Mᴴ * (M * P⁻¹) = P⁻¹ * (Mᴴ * M) * P⁻¹ := by noncomm_ring
      _ = P⁻¹ * (P * P) * P⁻¹ := by rw [hPP]
      _ = 1 := by
          rw [show P⁻¹ * (P * P) * P⁻¹ = (P⁻¹ * P) * (P * P⁻¹) by noncomm_ring, hPiP,
            Matrix.mul_nonsing_inv P hPd, Matrix.one_mul]
  have hUunit : U ∈ Matrix.unitaryGroup ι ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact hUU
  have hUle : ‖U‖ ≤ 1 := by
    have h2 : ‖U‖ * ‖U‖ = 1 := by
      rw [← CStarRing.norm_star_mul_self, Matrix.star_eq_conjTranspose, hUU, norm_one]
    nlinarith [norm_nonneg U]
  have hKU : ‖K * U‖ ≤ ‖K‖ := by
    calc ‖K * U‖ ≤ ‖K‖ * ‖U‖ := norm_mul_le K U
      _ ≤ ‖K‖ * 1 := by gcongr
      _ = ‖K‖ := mul_one _
  have hPtrnn : 0 ≤ (P.trace).re := (Complex.le_def.mp hPpsd.trace_nonneg).1.trans_eq' (by simp)
  calc (K * M).trace.re = ((K * U) * P).trace.re := by rw [← hMUP, ← Matrix.mul_assoc]
    _ ≤ ‖K * U‖ * (P.trace).re := re_trace_mul_le_opNorm_mul_trace hPpsd
    _ ≤ ‖K‖ * (P.trace).re := mul_le_mul_of_nonneg_right hKU hPtrnn
    _ = ‖K‖ * traceNorm M := by rw [traceNorm_eq_trace_absOp]

/-- **`‖K‖ ≤ 1` from the Loewner contraction `K·Kᴴ ⪯ 1`** (`1 − K·Kᴴ ⪰ 0`). Proved via the
EuclideanLin operator picture (NOT the matrix `CStarAlgebra` instance, which whnf-times-out):
`‖K‖ = ‖Kᴴ‖ = ‖toEuclideanCLM Kᴴ‖`, and `ContinuousLinearMap.opNNNorm_le_iff` reduces to
`∀ x, ‖toEuclideanCLM Kᴴ x‖ ≤ ‖x‖`; the bound `‖toEuclideanCLM Kᴴ x‖² = re⟪x, (KKᴴ) x⟫ ≤ ‖x‖²` follows
from `Matrix.isPositive_toEuclideanLin_iff` applied to `1 − KKᴴ` (adjoint `toEuclideanCLM K`). -/
theorem opNorm_le_one_of_mul_conjTranspose_le_one {K : Matrix ι ι ℂ}
    (h : ((1 : Matrix ι ι ℂ) - K * Kᴴ).PosSemidef) : ‖K‖ ≤ 1 := by
  have hKstar : ‖K‖ = ‖Kᴴ‖ := by rw [← Matrix.star_eq_conjTranspose, norm_star]
  rw [hKstar, ← NNReal.coe_one, ← coe_nnnorm, NNReal.coe_le_coe, Matrix.cstar_nnnorm_def,
    ContinuousLinearMap.opNNNorm_le_iff]
  intro x
  rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
  set S := Matrix.toEuclideanCLM (𝕜 := ℂ) Kᴴ with hS
  have hadj : ContinuousLinearMap.adjoint S = Matrix.toEuclideanCLM (𝕜 := ℂ) K := by
    rw [hS, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    congr 1; rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hmul : (toEuclideanLin (K * Kᴴ)) x = (ContinuousLinearMap.adjoint S) (S x) := by
    rw [hadj, hS]
    show (Matrix.toEuclideanCLM (𝕜 := ℂ) (K * Kᴴ)) x = _
    rw [map_mul, ContinuousLinearMap.mul_apply]
  have hpos := (Matrix.isPositive_toEuclideanLin_iff (A := 1 - K * Kᴴ)).mpr h
  have h0 := hpos.2 x
  rw [map_sub, LinearMap.sub_apply, inner_sub_left, hmul, ContinuousLinearMap.adjoint_inner_left,
    show (toEuclideanLin (1 : Matrix ι ι ℂ)) x = x from by simp, map_sub,
    inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h0
  calc ‖S x‖ = Real.sqrt (‖S x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt (by linarith [h0])
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

end SKEFTHawking.QuantumNetwork
