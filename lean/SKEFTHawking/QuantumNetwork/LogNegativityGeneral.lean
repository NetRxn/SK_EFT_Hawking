import SKEFTHawking.QuantumNetwork.NegativityMonotoneGeneral
import SKEFTHawking.QuantumNetwork.LogNegativity

/-!
# Log-negativity at general bipartite dimension: monotone + additive (Phase 6AK, Wave FU-6 brick 2)

The log-negativity `E_N(ρ) = log₂‖ρ^Γ‖₁` on an arbitrary bipartite system `Fin dA × Fin dB`, with the
two structural facts that make it the right bound for the regularized `E_D ≤ E_N` rate:
- **monotone** under any local operation on the first party (`logNegB_localKraus_le`, from brick 1);
- **additive** over tensor products (`logNegB_add`, from the dimension-general `traceNorm_kronecker`).

Together these say: a local operation on a tensor product cannot produce more log-negativity than the
sum of the inputs' — the additive-monotone bound at the heart of `E_D ≤ E_N`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

variable {dA dB m : ℕ}

/-- **Log-negativity** at general bipartite dimension: `E_N(ρ) = log₂‖ρ^Γ‖₁`. -/
noncomputable def logNegB (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : ℝ :=
  Real.logb 2 (traceNorm (ptB ρ))

/-- **Additivity of log-negativity** over tensor products: `E_N(ρ ⊗ σ) = E_N(ρ) + E_N(σ)`. The tensor
state's partial transpose is `ptB ρ ⊗ ptB σ`, so `log₂` of the multiplicative trace norm
(`traceNorm_kronecker`) gives the sum. -/
theorem logNegB_add {dA' dB' : ℕ} {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    {σ : Matrix (Fin dA' × Fin dB') (Fin dA' × Fin dB') ℂ}
    (hρ : traceNorm (ptB ρ) ≠ 0) (hσ : traceNorm (ptB σ) ≠ 0) :
    Real.logb 2 (traceNorm (ptB ρ ⊗ₖ ptB σ)) = logNegB ρ + logNegB σ := by
  rw [traceNorm_kronecker, logNegB, logNegB, Real.logb_mul hρ hσ]

/-- **Log-negativity is monotone under local operations** on the first party:
`E_N((Φ_A ⊗ id) ρ) ≤ E_N(ρ)`. From brick 1's trace-norm monotonicity + monotonicity of `log₂`
(the partial transpose of a Hermitian operator has nonzero trace norm unless it vanishes). -/
theorem logNegB_localKraus_le {M : Fin m → Matrix (Fin dA) (Fin dA) ℂ} (hM : IsKrausChannel M)
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ} (hρ : ρ.IsHermitian)
    (hpos : 0 < traceNorm (ptB (krausMap (fun a => M a ⊗ₖ 1) ρ))) :
    logNegB (krausMap (fun a => M a ⊗ₖ 1) ρ) ≤ logNegB ρ := by
  unfold logNegB
  exact Real.logb_le_logb_of_le (by norm_num) hpos (traceNorm_ptB_localKraus_le hM hρ)

end SKEFTHawking.QuantumNetwork
