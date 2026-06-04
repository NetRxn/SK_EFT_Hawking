import SKEFTHawking.QuantumNetwork.LogNegativityGeneral
import SKEFTHawking.QuantumNetwork.DiamondNormChoi

/-!
# Log-negativity of the maximally entangled state (Phase 6AK, Wave FU-6 brick 4)

The distillation target. The `d`-dimensional maximally entangled state `Φ_d = |Φ⟩⟨Φ|`,
`|Φ⟩ = d^(−1/2) ∑ᵢ |ii⟩`, has log-negativity `E_N(Φ_d) = log₂ d` — the maximal value at dimension `d`,
and the quantity a distillation protocol must produce.

The partial transpose of `Φ_d` is `d⁻¹·SWAP`, where `SWAP` is the swap permutation matrix on
`Fin d × Fin d` (`swapMat`, realized as the `Prod.swap` permutation). `SWAP` is Hermitian and
involutive (`SWAP·SWAP = 1`), so `|SWAP| = 1` (PSD-square-root uniqueness) and `‖SWAP‖₁ = tr 1 = d²`.
Hence `‖Φ_d^Γ‖₁ = d⁻¹·d² = d` and `E_N(Φ_d) = log₂ d`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {d : ℕ}

/-- The **swap permutation matrix** on `Fin d × Fin d`: `SWAP p q = [p = Prod.swap q]`. -/
def swapMat (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => if p = Prod.swap q then 1 else 0

/-- `SWAP` is Hermitian (it is a real symmetric permutation matrix). -/
theorem swapMat_isHermitian : (swapMat d)ᴴ = swapMat d := by
  ext p q
  simp only [Matrix.conjTranspose_apply, swapMat, Matrix.of_apply, apply_ite (star : ℂ → ℂ),
    star_one, star_zero]
  refine if_congr ?_ rfl rfl
  constructor <;> (intro h; rw [h, Prod.swap_swap])

/-- `SWAP` is involutive: `SWAP · SWAP = 1`. -/
theorem swapMat_mul_self : swapMat d * swapMat d = 1 := by
  ext p q
  rw [Matrix.mul_apply, Finset.sum_eq_single (Prod.swap p)]
  · simp only [swapMat, Matrix.of_apply, Prod.swap_swap, if_true, one_mul,
      Matrix.one_apply]
    by_cases h : p = q
    · subst h; simp
    · rw [if_neg (fun hh => h (Prod.swap_injective hh)), if_neg h]
  · intro b _ hb
    simp only [swapMat, Matrix.of_apply]
    rw [if_neg (fun hh => hb (by rw [hh, Prod.swap_swap])), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `‖SWAP‖₁ = d²`: `|SWAP| = 1` by PSD-square-root uniqueness, so the trace norm is `tr 1 = d²`. -/
theorem traceNorm_swapMat : traceNorm (swapMat d) = (d : ℝ) ^ 2 := by
  have habs : absOp (swapMat d) = 1 := by
    refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _) Matrix.PosSemidef.one ?_
    rw [absOp_mul_self, Matrix.mul_one, swapMat_isHermitian, swapMat_mul_self]
  rw [traceNorm_eq_trace_absOp, habs, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin,
    Complex.natCast_re]
  push_cast
  ring

/-- The **maximally entangled state** `Φ_d` (density matrix): `Φ_d (a,b)(c,e) = d⁻¹·[a=b][c=e]`. -/
noncomputable def maxEntState (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (Complex.ofReal (d : ℝ)⁻¹) else 0

/-- The partial transpose of the maximally entangled state is `d⁻¹·SWAP`. -/
theorem ptB_maxEntState : ptB (maxEntState d) = (Complex.ofReal (d : ℝ)⁻¹) • swapMat d := by
  ext p q
  simp only [ptB, maxEntState, swapMat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : p = Prod.swap q
  · have hL : p.1 = q.2 ∧ q.1 = p.2 := by
      obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
      simp only [Prod.swap, Prod.mk.injEq] at h; exact ⟨h.1, h.2.symm⟩
    rw [if_pos hL, if_pos h, mul_one]
  · have hL : ¬ (p.1 = q.2 ∧ q.1 = p.2) := by
      obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
      simp only [Prod.swap, Prod.mk.injEq] at h ⊢
      exact fun hc => h ⟨hc.1, hc.2.symm⟩
    rw [if_neg hL, if_neg h, mul_zero]

/-- **Log-negativity of the maximally entangled state:** `E_N(Φ_d) = log₂ d`, the maximal value at
dimension `d` and the target a distillation protocol must reach. -/
theorem logNegB_maxEntState (hd : d ≠ 0) :
    logNegB (maxEntState d) = Real.logb 2 d := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  unfold logNegB
  rw [ptB_maxEntState, traceNorm_smul_nonneg (by positivity), traceNorm_swapMat]
  congr 1
  field_simp

end SKEFTHawking.QuantumNetwork
