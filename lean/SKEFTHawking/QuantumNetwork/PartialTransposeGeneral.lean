import SKEFTHawking.QuantumNetwork.DiamondNormAttainment
import SKEFTHawking.QuantumNetwork.TraceNormCauchySchwarz

/-!
# General-dimensional partial transpose (Phase 6AK, Wave FU-6 substrate)

`pt2` (in `BellNegativity`) is hardwired to a two-qubit `Fin 2 × Fin 2` system. The regularized
`E_D ≤ E_N` rate (tensor powers `ρ^⊗n`) and the repeaterless Choi-state bound (FU-7) both need the
partial transpose on an **arbitrary bipartite system** `A × B` (any finite parties). This module
builds it:

`ptB ρ ((a,b),(c,d)) = ρ ((a,d),(c,b))`  — transpose of the `B` (second) factor only.

The two facts that carry over from the two-qubit case, now at general (arbitrary-party) dimension:
- `norm_ptB : ‖ρ^Γ‖_F = ‖ρ‖_F` — the Frobenius norm is preserved (the partial transpose is an
  entry permutation; proved here via the index involution, not a finite `ring`);
- `traceNorm_ptB_le : ‖ρ^Γ‖₁ ≤ √(|A|·|B|)·‖ρ‖₁` — the partial transpose is trace-norm-bounded.

Parties are arbitrary `Fintype`s with `DecidableEq`; instantiating `A := Fin dA, B := Fin dB`
recovers the finite-dimensional case, and `A := KronIdx _ n` gives the grouped `n`-copy systems.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.Frobenius

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **Partial transpose on the second factor**, general bipartite parties:
`(Tᵦ ρ)((a,b),(c,d)) = ρ((a,d),(c,b))`. -/
noncomputable def ptB (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  Matrix.of fun p q => ρ (p.1, q.2) (q.1, p.2)

/-- The index involution underlying the partial transpose: swap the `B`-components of the row/column
index pair. `((a,b),(c,d)) ↦ ((a,d),(c,b))`. -/
def ptBSwap : (A × B) × (A × B) ≃ (A × B) × (A × B) where
  toFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  invFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  left_inv := by intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv := by intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

/-- **The partial transpose preserves the Frobenius norm** (it permutes matrix entries). -/
theorem norm_ptB (X : Matrix (A × B) (A × B) ℂ) : ‖ptB X‖ = ‖X‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (ptB X)), ← Real.sqrt_sq (norm_nonneg X)]
  congr 1
  rw [← re_trace_conjTranspose_mul_self_eq_frobenius_sq,
    ← re_trace_conjTranspose_mul_self_eq_frobenius_sq]
  congr 1
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, ptB, Matrix.of_apply]
  rw [← Finset.sum_product', ← Finset.sum_product']
  exact (Fintype.sum_equiv ptBSwap _ _ fun p => rfl).symm

/-- **The partial transpose is trace-norm-bounded:** `‖X^Γ‖₁ ≤ √(|A|·|B|)·‖X‖₁`. -/
theorem traceNorm_ptB_le (X : Matrix (A × B) (A × B) ℂ) :
    traceNorm (ptB X) ≤ Real.sqrt (Fintype.card A * Fintype.card B) * traceNorm X := by
  have hcard : Real.sqrt (Fintype.card (A × B)) = Real.sqrt (Fintype.card A * Fintype.card B) := by
    rw [Fintype.card_prod]; push_cast; ring_nf
  calc traceNorm (ptB X) ≤ Real.sqrt (Fintype.card (A × B)) * ‖ptB X‖ :=
        traceNorm_le_sqrt_card_mul_norm (ptB X)
    _ = Real.sqrt (Fintype.card A * Fintype.card B) * ‖X‖ := by rw [hcard, norm_ptB]
    _ ≤ Real.sqrt (Fintype.card A * Fintype.card B) * traceNorm X := by
        gcongr; exact frobenius_le_traceNorm X

end SKEFTHawking.QuantumNetwork
