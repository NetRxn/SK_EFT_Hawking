import SKEFTHawking.QuantumNetwork.LogNegativity
import SKEFTHawking.QuantumNetwork.DiamondNormAttainment

/-!
# Continuity of the negativity (Phase 6AK, Wave FU-5)

The negativity is **Lipschitz in trace distance**: `|‖ρ^Γ‖₁ − ‖σ^Γ‖₁| ≤ 2‖ρ − σ‖₁`. The crux is that the
partial transpose, while not trace-norm-preserving, is trace-norm *bounded*: `‖X^Γ‖₁ ≤ 2‖X‖₁`
(`traceNorm_pt2_le`). This decomposes entirely into already-shipped bounds and one elementary new lemma:
`pt2` permutes matrix entries, so it preserves the **Frobenius** norm (`norm_pt2`), and then
`‖X^Γ‖₁ ≤ √(card)·‖X^Γ‖_F = 2·‖X‖_F ≤ 2·‖X‖₁` via `traceNorm_le_sqrt_card_mul_norm` +
`frobenius_le_traceNorm` (`card (Fin 2 × Fin 2) = 4`, `√4 = 2`).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.Frobenius

/-- **The partial transpose preserves the Frobenius norm** (it permutes matrix entries). -/
theorem norm_pt2 (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ‖pt2 X‖ = ‖X‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (pt2 X)), ← Real.sqrt_sq (norm_nonneg X)]
  congr 1
  rw [← re_trace_conjTranspose_mul_self_eq_frobenius_sq,
    ← re_trace_conjTranspose_mul_self_eq_frobenius_sq]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, pt2,
    Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- **The partial transpose is trace-norm-bounded:** `‖X^Γ‖₁ ≤ 2‖X‖₁`. -/
theorem traceNorm_pt2_le (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    traceNorm (pt2 X) ≤ 2 * traceNorm X := by
  have hcard : Real.sqrt (Fintype.card (Fin 2 × Fin 2)) = 2 := by
    have h4 : ((Fintype.card (Fin 2 × Fin 2) : ℕ) : ℝ) = 4 := by
      norm_num [Fintype.card_prod, Fintype.card_fin]
    rw [h4, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc traceNorm (pt2 X) ≤ Real.sqrt (Fintype.card (Fin 2 × Fin 2)) * ‖pt2 X‖ :=
        traceNorm_le_sqrt_card_mul_norm (pt2 X)
    _ = 2 * ‖X‖ := by rw [hcard, norm_pt2]
    _ ≤ 2 * traceNorm X := by gcongr; exact frobenius_le_traceNorm X

/-- The partial transpose is additive (it is a linear reindexing). -/
theorem pt2_sub (X Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    pt2 (X - Y) = pt2 X - pt2 Y := by
  ext p q; simp only [pt2, Matrix.of_apply, Matrix.sub_apply]

/-- **The negativity is 2-Lipschitz in trace distance:** `|‖ρ^Γ‖₁ − ‖σ^Γ‖₁| ≤ 2‖ρ − σ‖₁`. The partial
transpose is trace-norm-bounded (`traceNorm_pt2_le`) and the trace norm obeys the reverse triangle
inequality, so the negativity (an affine function of `‖ρ^Γ‖₁`) is continuous in the trace distance. -/
theorem abs_traceNorm_pt2_sub_le (ρ σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    |traceNorm (pt2 ρ) - traceNorm (pt2 σ)| ≤ 2 * traceNorm (ρ - σ) := by
  have hrev : |traceNorm (pt2 ρ) - traceNorm (pt2 σ)| ≤ traceNorm (pt2 ρ - pt2 σ) := by
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · have h := traceNorm_triangle (pt2 ρ - pt2 σ) (pt2 σ); rw [sub_add_cancel] at h; linarith
    · have h := traceNorm_triangle (pt2 σ - pt2 ρ) (pt2 ρ)
      rw [sub_add_cancel, show pt2 σ - pt2 ρ = -(pt2 ρ - pt2 σ) by abel, traceNorm_neg] at h
      linarith
  rw [← pt2_sub] at hrev
  exact hrev.trans (traceNorm_pt2_le (ρ - σ))

/-- **Negativity continuity in trace distance:** `|‖ρ^Γ‖₁ − ‖σ^Γ‖₁| ≤ 4·D(ρ,σ)`, equivalently the
negativity `N = ½(‖ρ^Γ‖₁ − 1)` is **2-Lipschitz** in the trace distance `D(ρ,σ) = ½‖ρ−σ‖₁`. -/
theorem abs_traceNorm_pt2_sub_le_traceDist (ρ σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    |traceNorm (pt2 ρ) - traceNorm (pt2 σ)| ≤ 4 * traceDist ρ σ := by
  have h := abs_traceNorm_pt2_sub_le ρ σ
  rw [traceDist]; linarith

end SKEFTHawking.QuantumNetwork
