import SKEFTHawking.QuantumNetwork.DiamondNormAttainment
import SKEFTHawking.QuantumNetwork.TraceNormCauchySchwarz

/-!
# General-dimensional partial transpose (Phase 6AK, Wave FU-6 substrate)

`pt2` (in `BellNegativity`) is hardwired to a two-qubit `Fin 2 × Fin 2` system. The regularized
`E_D ≤ E_N` rate (tensor powers `ρ^⊗n`) and the repeaterless Choi-state bound (FU-7) both need the
partial transpose on an **arbitrary bipartite system** `Fin dA × Fin dB`. This module builds it:

`ptB ρ ((a,b),(c,d)) = ρ ((a,d),(c,b))`  — transpose of the `B` (second) factor only.

The two facts that carry over from the two-qubit case, now at general dimension:
- `norm_ptB : ‖ρ^Γ‖_F = ‖ρ‖_F` — the Frobenius norm is preserved (the partial transpose is an
  entry permutation; proved here via the index involution, not a finite `ring`);
- `traceNorm_ptB_le : ‖ρ^Γ‖₁ ≤ √(dA·dB)·‖ρ‖₁` — the partial transpose is trace-norm-bounded.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.Frobenius

variable {dA dB : ℕ}

/-- **Partial transpose on the second factor**, general bipartite dimension:
`(Tᵦ ρ)((a,b),(c,d)) = ρ((a,d),(c,b))`. -/
noncomputable def ptB (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
  Matrix.of fun p q => ρ (p.1, q.2) (q.1, p.2)

/-- The index involution underlying the partial transpose: swap the `B`-components of the row/column
index pair. `((a,b),(c,d)) ↦ ((a,d),(c,b))`. -/
def ptBSwap : (Fin dA × Fin dB) × (Fin dA × Fin dB) ≃ (Fin dA × Fin dB) × (Fin dA × Fin dB) where
  toFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  invFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  left_inv := by intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv := by intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

/-- **The partial transpose preserves the Frobenius norm** (it permutes matrix entries). -/
theorem norm_ptB (X : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : ‖ptB X‖ = ‖X‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (ptB X)), ← Real.sqrt_sq (norm_nonneg X)]
  congr 1
  rw [← re_trace_conjTranspose_mul_self_eq_frobenius_sq,
    ← re_trace_conjTranspose_mul_self_eq_frobenius_sq]
  congr 1
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, ptB, Matrix.of_apply]
  rw [← Finset.sum_product', ← Finset.sum_product']
  exact (Fintype.sum_equiv ptBSwap _ _ fun p => rfl).symm

/-- **The partial transpose is trace-norm-bounded:** `‖X^Γ‖₁ ≤ √(dA·dB)·‖X‖₁`. -/
theorem traceNorm_ptB_le (X : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    traceNorm (ptB X) ≤ Real.sqrt (dA * dB) * traceNorm X := by
  have hcard : Real.sqrt (Fintype.card (Fin dA × Fin dB)) = Real.sqrt (dA * dB) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; ring_nf
  calc traceNorm (ptB X) ≤ Real.sqrt (Fintype.card (Fin dA × Fin dB)) * ‖ptB X‖ :=
        traceNorm_le_sqrt_card_mul_norm (ptB X)
    _ = Real.sqrt (dA * dB) * ‖X‖ := by rw [hcard, norm_ptB]
    _ ≤ Real.sqrt (dA * dB) * traceNorm X := by
        gcongr; exact frobenius_le_traceNorm X

end SKEFTHawking.QuantumNetwork
