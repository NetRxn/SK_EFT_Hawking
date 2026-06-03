import SKEFTHawking.QuantumNetwork.DiamondNormChoiUpper

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

end SKEFTHawking.QuantumNetwork
