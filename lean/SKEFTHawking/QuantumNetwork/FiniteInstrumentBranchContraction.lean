import SKEFTHawking.QuantumNetwork.FiniteInstrument
import SKEFTHawking.QuantumNetwork.CPTPChannel

/-! Trace-norm contraction for a finite instrument retaining its branch states. -/

noncomputable section
open Matrix
open scoped ComplexOrder
namespace SKEFTHawking.QuantumNetwork.FiniteInstrument

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem branch_sub (J : FiniteInstrument ι n) (a : Fin n) (X Y : Matrix ι ι ℂ) :
    J.branch a (X - Y) = J.branch a X - J.branch a Y := krausMap_sub _ _ _

/-- Retaining all unnormalized output states still gives trace-norm contraction
when the branches are kept in separate classical records. -/
theorem sum_traceNorm_branch_le (J : FiniteInstrument ι n)
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (∑ a, traceNorm (J.branch a X)) ≤ traceNorm X := by
  have hb (a : Fin n) :
      traceNorm (J.branch a X) ≤ J.weight a (posPart hX) + J.weight a (negPart hX) := by
    have hsplit : J.branch a X = J.branch a (posPart hX) - J.branch a (negPart hX) := by
      conv_lhs => rw [self_eq_posPart_sub_negPart hX]
      exact J.branch_sub a _ _
    have h := traceNorm_triangle (J.branch a (posPart hX)) (-(J.branch a (negPart hX)))
    rw [← sub_eq_add_neg, ← hsplit, traceNorm_neg] at h
    rw [traceNorm_posSemidef (J.branch_posSemidef a (posPart_posSemidef hX)),
      traceNorm_posSemidef (J.branch_posSemidef a (negPart_posSemidef hX))] at h
    exact h
  calc
    _ ≤ ∑ a, (J.weight a (posPart hX) + J.weight a (negPart hX)) :=
      Finset.sum_le_sum (fun a _ => hb a)
    _ = traceNorm X := by
      rw [Finset.sum_add_distrib, J.sum_weight, J.sum_weight,
        traceNorm_hermitian_eq_pos_add_neg hX]

private theorem traceNorm_branch_change (I J : FiniteInstrument ι n)
    (a : Fin n) (X Y : Matrix ι ι ℂ) :
    traceNorm (I.branch a X - J.branch a Y) ≤
      traceNorm (I.branch a (X-Y)) + traceNorm (I.branch a Y - J.branch a Y) := by
  have e : I.branch a X - J.branch a Y =
      I.branch a (X-Y) + (I.branch a Y - J.branch a Y) :=
    (sub_add_sub_cancel _ _ _).symm.trans
      (congrArg (· + (I.branch a Y - J.branch a Y)) (I.branch_sub a X Y).symm)
  exact (congrArg traceNorm e).le.trans (traceNorm_triangle _ _)

/-- A local change of instrument contributes its discrepancy on the reference
input, in addition to the incoming discrepancy. -/
theorem sum_traceNorm_branch_sub_le (I J : FiniteInstrument ι n)
    {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (∑ a, traceNorm (I.branch a X - J.branch a Y)) ≤
      traceNorm (X-Y) + ∑ a, traceNorm (I.branch a Y - J.branch a Y) := by
  calc
    _ ≤ ∑ a, (traceNorm (I.branch a (X-Y)) + traceNorm (I.branch a Y - J.branch a Y)) :=
      Finset.sum_le_sum (fun a _ => traceNorm_branch_change I J a X Y)
    _ = (∑ a, traceNorm (I.branch a (X-Y))) +
        ∑ a, traceNorm (I.branch a Y - J.branch a Y) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add_left (I.sum_traceNorm_branch_le (X := X-Y) (hX.sub hY)) _

end SKEFTHawking.QuantumNetwork.FiniteInstrument
