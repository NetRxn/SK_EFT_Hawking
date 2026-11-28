import SKEFTHawking.FiniteGibbsResetScheduleOrdering

/-! Repeated homogeneous blocks keep a geometric fraction of their input.
Opposite block orders give the maximal and minimal readouts for a fixed
multiset containing two kinds of reset slice. -/

noncomputable section

set_option autoImplicit false

namespace SKEFTHawking.FinitePositiveKernel.GibbsReset

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A block of repeated slices is an affine reset toward the same target,
with retained fraction equal to the corresponding geometric power. -/
theorem evolveResetSchedule_replicate (k : ℕ) (s : ResetSlice n) (X : Matrix n n ℂ) :
    evolveResetSchedule (List.replicate k s) X =
      s.attenuation ^ k • X + (1 - s.attenuation ^ k) • (X.trace • s.target) := by
  induction k generalizing X with
  | zero => simp [evolveResetSchedule]
  | succ k ih =>
      rw [List.replicate_succ]
      change evolveResetSchedule (List.replicate k s) (s.evolve X) = _
      rw [ih, s.trace_evolve, s.evolve_affine, pow_succ]
      module

/-- Reversing homogeneous blocks scales their target difference by both
blocks' reset fractions. A block of length zero contributes no contrast. -/
theorem evolveResetSchedule_replicated_block_reversal (k l : ℕ) (s t : ResetSlice n)
    (X : Matrix n n ℂ) :
    evolveResetSchedule (List.replicate k s ++ List.replicate l t) X -
      evolveResetSchedule (List.replicate l t ++ List.replicate k s) X =
      ((1 - s.attenuation ^ k) * (1 - t.attenuation ^ l) * X.trace) •
        (t.target - s.target) := by
  rw [evolveResetSchedule_append, evolveResetSchedule_append]
  rw [evolveResetSchedule_replicate l t (evolveResetSchedule (List.replicate k s) X),
    evolveResetSchedule_trace (List.replicate k s) X,
    evolveResetSchedule_replicate k s (evolveResetSchedule (List.replicate l t) X),
    evolveResetSchedule_trace (List.replicate l t) X]
  simp only [evolveResetSchedule_replicate]
  module

private theorem pairwise_two_blocks {α : Type*} (score : α → ℝ) (s t : α)
    (k l : ℕ) (hOrder : score s ≤ score t) :
    (List.replicate k s ++ List.replicate l t).Pairwise (fun u v => score u ≤ score v) := by
  refine List.pairwise_append.mpr
    ⟨List.pairwise_replicate.mpr (Or.inr le_rfl),
      List.pairwise_replicate.mpr (Or.inr le_rfl), ?_⟩
  intro u hu v hv
  rw [(List.mem_replicate.mp hu).2, (List.mem_replicate.mp hv).2]
  exact hOrder

/-- The two block orders bound all schedules containing the same slices.
Their terminal readout gap is the target gap times the two block reset
fractions. The gap is independent of the common trace-one input. -/
theorem twoBath_fixedDose_readout_spread (readout : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (s t : ResetSlice n) (k l : ℕ) (X : Matrix n n ℂ)
    (hX : X.trace = 1) (hOrder : readout s.target ≤ readout t.target) :
    let hi := List.replicate k s ++ List.replicate l t
    let lo := List.replicate l t ++ List.replicate k s
    (∀ other : List (ResetSlice n), other.Perm hi →
      readout (evolveResetSchedule lo X) ≤ readout (evolveResetSchedule other X) ∧
      readout (evolveResetSchedule other X) ≤ readout (evolveResetSchedule hi X)) ∧
    readout (evolveResetSchedule hi X) - readout (evolveResetSchedule lo X) =
      (1 - Real.exp (-s.dose) ^ k) * (1 - Real.exp (-t.dose) ^ l) *
        (readout t.target - readout s.target) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro other hOther
    constructor
    · have hNeg : (-readout) s.target ≤ (-readout) t.target ↔
          readout t.target ≤ readout s.target := by simp
      have hRev : (-readout) t.target ≤ (-readout) s.target := by
        simpa only [LinearMap.neg_apply, neg_le_neg_iff] using hOrder
      have hSort := pairwise_two_blocks (fun r => (-readout) r.target) t s l k hRev
      have bound := sorted_resetSchedule_readout_maximal (-readout) _ other X hX hSort
        (hOther.trans List.perm_append_comm)
      simpa only [LinearMap.neg_apply, neg_le_neg_iff] using bound
    · exact sorted_resetSchedule_readout_maximal readout _ other X hX
        (pairwise_two_blocks (fun r => readout r.target) s t k l hOrder) hOther
  · rw [← map_sub, evolveResetSchedule_replicated_block_reversal, hX, mul_one]
    let c := (1 - Real.exp (-s.dose) ^ k) * (1 - Real.exp (-t.dose) ^ l)
    have hcast : (c : ℂ) = (1 - s.attenuation ^ k) * (1 - t.attenuation ^ l) := by
      dsimp only [c, ResetSlice.attenuation]
      push_cast
      rfl
    rw [← hcast]
    change readout ((algebraMap ℝ ℂ c) • (t.target - s.target)) =
      c * (readout t.target - readout s.target)
    rw [IsScalarTower.algebraMap_smul, map_smul, map_sub, smul_eq_mul]

end SKEFTHawking.FinitePositiveKernel.GibbsReset
