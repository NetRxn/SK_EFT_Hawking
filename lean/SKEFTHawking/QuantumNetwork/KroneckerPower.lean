import SKEFTHawking.QuantumNetwork.LogNegativityGeneral

/-!
# Kronecker power and the n-fold log-negativity (Phase 6AK, Wave FU-6 brick 3)

The regularized `E_D ≤ E_N` rate needs `n` copies. This module builds the **Kronecker power**
`A^⊗n` on the recursive index type `KronIdx m n` (base `Fin 1`, step `m × ·`, so the `n`-fold
Kronecker product needs no reindexing and `traceNorm_kronecker` applies at each step), proves the
multiplicativity `‖A^⊗n‖₁ = ‖A‖₁ⁿ` (`traceNorm_kronPow`), and concludes the **n-fold log-negativity
additivity** `E_N(ρ^⊗n) = n·E_N(ρ)` (`logNegB_kronPow`, using `(ρ^Γ)^⊗n` as the representative of
`(ρ^⊗n)^Γ` — the partial transpose distributes over the tensor power).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

/-- The index type of the `n`-fold Kronecker power: `KronIdx m 0 = Fin 1`, `KronIdx m (n+1) = m × …`. -/
def KronIdx (m : Type) : ℕ → Type
  | 0 => Fin 1
  | n + 1 => m × KronIdx m n

instance instFintypeKronIdx (m : Type) [Fintype m] : ∀ n, Fintype (KronIdx m n)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | n + 1 => letI := instFintypeKronIdx m n; inferInstanceAs (Fintype (m × KronIdx m n))

instance instDecidableEqKronIdx (m : Type) [DecidableEq m] : ∀ n, DecidableEq (KronIdx m n)
  | 0 => inferInstanceAs (DecidableEq (Fin 1))
  | n + 1 => letI := instDecidableEqKronIdx m n; inferInstanceAs (DecidableEq (m × KronIdx m n))

/-- The **`n`-fold Kronecker power** `A^⊗n`. -/
noncomputable def kronPow {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) :
    ∀ n, Matrix (KronIdx m n) (KronIdx m n) ℂ
  | 0 => 1
  | n + 1 => A ⊗ₖ kronPow A n

/-- `‖1‖₁ = 1` for the `1×1` identity. -/
theorem traceNorm_one_fin_one : traceNorm (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
  rw [traceNorm_posSemidef Matrix.PosSemidef.one, Matrix.trace_one]
  simp

/-- **Trace-norm multiplicativity over the Kronecker power:** `‖A^⊗n‖₁ = ‖A‖₁ⁿ`. -/
theorem traceNorm_kronPow {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (n : ℕ) :
    traceNorm (kronPow A n) = (traceNorm A) ^ n := by
  induction n with
  | zero => simp only [kronPow, pow_zero]; exact traceNorm_one_fin_one
  | succ k ih =>
    rw [pow_succ', ← ih]
    exact traceNorm_kronecker A (kronPow A k)

/-- **n-fold log-negativity additivity:** `E_N(ρ^⊗n) = n·E_N(ρ)`. The representative `(ρ^Γ)^⊗n` is the
partial transpose of the `n`-copy state `ρ^⊗n` (the partial transpose distributes over the tensor
power); its trace norm is `‖ρ^Γ‖₁ⁿ`, so `log₂` of it is `n·E_N(ρ)`. -/
theorem logNegB_kronPow {dA dB : ℕ} (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (n : ℕ) :
    Real.logb 2 (traceNorm (kronPow (ptB ρ) n)) = n * logNegB ρ := by
  rw [traceNorm_kronPow, Real.logb_pow, logNegB]

end SKEFTHawking.QuantumNetwork
