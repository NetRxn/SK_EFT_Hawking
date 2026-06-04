import SKEFTHawking.QuantumNetwork.MaxEntNegativity

/-!
# Single-copy distillation rate bound (Phase 6AK, Wave FU-6 brick 5)

Assembles the log-negativity monotone (brick 1/2, `logNegB_localKraus_le`) with the maximally
entangled target value (brick 4, `logNegB_maxEntState`) into the **single-copy distillation bound**:

> A local operation on one copy of `ρ` (a channel on the `A` party, identity on `B`) that produces
> the `k`-dimensional maximally entangled state `Φ_k` requires `log₂ k ≤ E_N(ρ)`.

This is the `n = 1` case of the regularized `E_D ≤ E_N` rate: the log-negativity of the input upper
bounds the log-dimension of any maximally entangled state distillable from it by a single-copy local
operation. The asymptotic (`n`-copy) statement requires the n-fold additivity on the grouped
`n`-copy bipartite system; the per-copy monotone bound is exact and unconditional.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

variable {k m : ℕ}

/-- **Single-copy distillation rate bound:** if a local operation on the first party (a Kraus channel
`M` on `A`, identity on `B`) maps `ρ` exactly to the maximally entangled state `Φ_k`, then
`log₂ k ≤ E_N(ρ)`. The output's log-negativity is `log₂ k` (brick 4); local-operation monotonicity
(brick 1/2) caps it by `E_N(ρ)`. -/
theorem distillation_single_copy_bound (hk : k ≠ 0)
    {M : Fin m → Matrix (Fin k) (Fin k) ℂ} (hM : IsKrausChannel M)
    {ρ : Matrix (Fin k × Fin k) (Fin k × Fin k) ℂ} (hρ : ρ.IsHermitian)
    (hout : krausMap (fun a => M a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) ρ = maxEntState k) :
    Real.logb 2 k ≤ logNegB ρ := by
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have htn : traceNorm (ptB (krausMap (fun a => M a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) ρ)) = (k : ℝ) := by
    rw [hout, ptB_maxEntState, traceNorm_smul_nonneg (by positivity), traceNorm_swapMat]
    field_simp
  have hpos : 0 < traceNorm (ptB (krausMap (fun a => M a ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)) ρ)) := by
    rw [htn]; exact_mod_cast Nat.pos_of_ne_zero hk
  calc Real.logb 2 k = logNegB (maxEntState k) := (logNegB_maxEntState hk).symm
    _ = logNegB (krausMap (fun a => M a ⊗ₖ 1) ρ) := by rw [hout]
    _ ≤ logNegB ρ := logNegB_localKraus_le hM hρ hpos

end SKEFTHawking.QuantumNetwork
