import SKEFTHawking.QuantumNetwork.BellNegativity
import SKEFTHawking.QuantumNetwork.DiamondNormChoi
import SKEFTHawking.QuantumNetwork.TraceNormCauchySchwarz
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Log-negativity and its additivity (Phase 6AK, Wave FU-3 rung 3 / FU-4)

The **log-negativity** `E_N(ρ) = log₂‖ρ^Γ‖₁` is the additive cousin of the negativity built in
`BellNegativity.lean`. (The negativity `N = ½(‖ρ^Γ‖₁ − 1)` is *not* additive; the logarithm makes it so.)
Additivity `E_N(ρ⊗σ) = E_N(ρ) + E_N(σ)` is the third rung of the `E_D ≤ E_N` decomposition — and its
substantive core is the **multiplicativity of the trace norm under tensor products**:

`‖A ⊗ B‖₁ = ‖A‖₁ · ‖B‖₁`  (`traceNorm_kronecker`, dimension-general, reusable).

This follows from `|A ⊗ B| = |A| ⊗ |B|` (the absolute value distributes over the Kronecker product, by
PSD-square-root uniqueness applied to `(A⊗B)ᴴ(A⊗B) = AᴴA ⊗ BᴴB`) and `tr(P ⊗ Q) = tr P · tr Q`. Since the
partial transpose also distributes over the tensor product (`(ρ⊗σ)^Γ = ρ^Γ ⊗ σ^Γ`, in the natural
bipartite regrouping — here represented by `pt2 ρ ⊗ pt2 σ`), `log₂` of the product gives additivity.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

/-- The trace of a positive-semidefinite (indeed any Hermitian) matrix is real. -/
theorem trace_im_zero_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) : M.trace.im = 0 := by
  have h : (starRingEnd ℂ) M.trace = M.trace := by
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, hM.isHermitian.eq]
  exact Complex.conj_eq_iff_im.mp h

/-- **The absolute value distributes over the Kronecker product:** `|A ⊗ B| = |A| ⊗ |B|`. -/
theorem absOp_kronecker {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    absOp (A ⊗ₖ B) = absOp A ⊗ₖ absOp B := by
  refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _)
    ((absOp_posSemidef A).kronecker (absOp_posSemidef B)) ?_
  rw [absOp_mul_self, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, absOp_mul_self, absOp_mul_self]

/-- **Trace-norm multiplicativity under tensor products:** `‖A ⊗ B‖₁ = ‖A‖₁ · ‖B‖₁`. Dimension-general
and reusable; the analytic core of log-negativity additivity. -/
theorem traceNorm_kronecker {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    traceNorm (A ⊗ₖ B) = traceNorm A * traceNorm B := by
  have hA : (absOp A).trace = ((traceNorm A : ℝ) : ℂ) := by
    rw [traceNorm_eq_trace_absOp]
    apply Complex.ext <;> simp [trace_im_zero_of_posSemidef (absOp_posSemidef A)]
  have hB : (absOp B).trace = ((traceNorm B : ℝ) : ℂ) := by
    rw [traceNorm_eq_trace_absOp]
    apply Complex.ext <;> simp [trace_im_zero_of_posSemidef (absOp_posSemidef B)]
  rw [traceNorm_eq_trace_absOp (A ⊗ₖ B), absOp_kronecker, Matrix.trace_kronecker, hA, hB,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-! ## Log-negativity -/

/-- **Log-negativity** of a two-qubit state: `E_N(ρ) = log₂‖ρ^Γ‖₁`. -/
noncomputable def logNegativity (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  Real.logb 2 (traceNorm (pt2 ρ))

/-- **Additivity of log-negativity under tensor products:** `E_N(ρ ⊗ σ) = E_N(ρ) + E_N(σ)`. The tensor
state's partial transpose is `pt2 ρ ⊗ pt2 σ` (the partial transpose distributes over `⊗`), so its
log-negativity is `log₂(‖pt2 ρ‖₁ · ‖pt2 σ‖₁) = E_N(ρ) + E_N(σ)`. Hypotheses: each partial transpose is
nonzero (automatic for density operators, where `‖ρ^Γ‖₁ ≥ 1`). -/
theorem logNegativity_add {ρ σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hρ : traceNorm (pt2 ρ) ≠ 0) (hσ : traceNorm (pt2 σ) ≠ 0) :
    Real.logb 2 (traceNorm (pt2 ρ ⊗ₖ pt2 σ)) = logNegativity ρ + logNegativity σ := by
  rw [traceNorm_kronecker, logNegativity, logNegativity, Real.logb_mul hρ hσ]

/-- For a normalised Bell-diagonal state `‖ρ^Γ‖₁ = ∑ⱼ|μⱼ| ≥ 1 > 0`, so the additivity hypothesis is
automatic. -/
theorem traceNorm_pt2_bellDiagState_ne_zero {p : Fin 4 → ℝ} (h1 : ∑ i, p i = 1) :
    traceNorm (pt2 (bellDiagState p)) ≠ 0 := by
  rw [traceNorm_pt2_bellDiagState]
  have : (1 : ℝ) ≤ ∑ j, |bellPTeig p j| := by
    rw [← bellPTeig_sum p h1]; exact Finset.sum_le_sum fun j _ => le_abs_self _
  linarith

/-- **Log-negativity additivity for Bell-diagonal states** (no side conditions beyond normalisation):
`E_N(ρ(p) ⊗ ρ(q)) = E_N(ρ(p)) + E_N(ρ(q))`. -/
theorem logNegativity_bellDiag_add {p q : Fin 4 → ℝ} (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) :
    Real.logb 2 (traceNorm (pt2 (bellDiagState p) ⊗ₖ pt2 (bellDiagState q)))
      = logNegativity (bellDiagState p) + logNegativity (bellDiagState q) :=
  logNegativity_add (traceNorm_pt2_bellDiagState_ne_zero hp) (traceNorm_pt2_bellDiagState_ne_zero hq)

end SKEFTHawking.QuantumNetwork
