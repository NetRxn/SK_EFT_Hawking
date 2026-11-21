import SKEFTHawking.StoppingRetainedClockBinaryDecision

/-!
# Trace-norm stability of finite binary decisions

The optimal-score formula from the retained-clock decision theorem
is Lipschitz in the prior-weighted output matrices. This gives an
error budget for comparing two discrimination experiments.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix

/-- The optimal binary score for normalized weighted output families
is stable under the sum of the prior-weighted trace-norm errors. The
formula inequality itself holds for any four matrix families. -/
theorem finite_binary_optimum_abs_sub_le {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] (P Q P' Q' : R → Matrix ι ι ℂ) :
    |(1 + ∑ r : R, traceNorm (P r - Q r)) / 2 - (1 + ∑ r : R, traceNorm (P' r - Q' r)) / 2| ≤
      (∑ r : R, (traceNorm (P r - P' r) + traceNorm (Q r - Q' r))) / 2 := by
  have reverseTriangle (A B : Matrix ι ι ℂ) :
      |traceNorm A - traceNorm B| ≤ traceNorm (A - B) := by
    rw [abs_sub_le_iff]
    constructor
    · have h := traceNorm_triangle (A - B) B
      rw [sub_add_cancel] at h
      linarith only [h]
    · have h := traceNorm_triangle (B - A) A
      rw [sub_add_cancel, show B - A = -(A - B) by abel, traceNorm_neg] at h
      linarith only [h]
  have hpoint (r : R) :
      |traceNorm (P r - Q r) - traceNorm (P' r - Q' r)| ≤
        traceNorm (P r - P' r) + traceNorm (Q r - Q' r) := by
    refine (reverseTriangle _ _).trans ?_
    rw [show P r - Q r - (P' r - Q' r) = (P r - P' r) + -(Q r - Q' r) by abel]
    simpa only [traceNorm_neg] using traceNorm_triangle (P r - P' r) (-(Q r - Q' r))
  have hsum : |∑ r : R, (traceNorm (P r - Q r) - traceNorm (P' r - Q' r))| ≤
      ∑ r : R, (traceNorm (P r - P' r) + traceNorm (Q r - Q' r)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => hpoint r)
  have hdiff : (1 + ∑ r : R, traceNorm (P r - Q r)) / 2 - (1 + ∑ r : R, traceNorm (P' r - Q' r)) / 2 =
      (∑ r : R, (traceNorm (P r - Q r) - traceNorm (P' r - Q' r))) / 2 := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hdiff, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact div_le_div_of_nonneg_right hsum (by norm_num)


/-- A strict gap between two optimal binary scores survives per-experiment
trace-norm errors whose two half-sums fit inside the gap. -/
theorem finite_binary_optimum_lt_of_traceNorm_budget {ι κ R S : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype R] [Fintype S]
    (P Q P' Q' : R → Matrix ι ι ℂ) (A B A' B' : S → Matrix κ κ ℂ)
    (hbudget :
      ((∑ r : R, (traceNorm (P r - P' r) + traceNorm (Q r - Q' r))) +
        ∑ s : S, (traceNorm (A s - A' s) + traceNorm (B s - B' s))) / 2 <
        ((∑ s : S, traceNorm (A s - B s)) - ∑ r : R, traceNorm (P r - Q r)) / 2) :
    (1 + ∑ r : R, traceNorm (P' r - Q' r)) / 2 <
      (1 + ∑ s : S, traceNorm (A' s - B' s)) / 2 := by
  have hSmall := abs_le.mp (finite_binary_optimum_abs_sub_le P Q P' Q')
  have hLarge := abs_le.mp (finite_binary_optimum_abs_sub_le A B A' B')
  linarith only [hbudget, hSmall.1, hLarge.2]

end SKEFTHawking.QuantumNetwork
