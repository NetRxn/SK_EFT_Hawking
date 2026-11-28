import SKEFTHawking.FiniteGibbsResetScheduleExchange

/-! Reordering a fixed finite collection of Gibbs slices changes a readout
through their target weights. An increasing target-readout order maximizes
the terminal readout over all permutations of the given slices. -/

noncomputable section

set_option autoImplicit false

namespace SKEFTHawking.FinitePositiveKernel.GibbsReset

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem readout_adjacent_le
    (readout : Matrix n n ℂ →ₗ[ℝ] ℝ) (s t : ResetSlice n) (post : List (ResetSlice n))
    (X : Matrix n n ℂ) (hX : X.trace = 1) (hOrder : readout s.target ≤ readout t.target) :
    readout (evolveResetSchedule (t :: s :: post) X) ≤
      readout (evolveResetSchedule (s :: t :: post) X) := by
  let c := Real.exp (-resetScheduleDose post) *
    (1 - Real.exp (-s.dose)) * (1 - Real.exp (-t.dose))
  have hDose (u : ResetSlice n) : 0 ≤ u.dose := mul_nonneg u.rate_nonneg u.duration_nonneg
  have hFraction (u : ResetSlice n) : 0 ≤ 1 - Real.exp (-u.dose) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hDose u)))
  have hc : 0 ≤ c :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (hFraction s)) (hFraction t)
  have hcast : (c : ℂ) = resetScheduleAttenuation post *
      (1 - s.attenuation) * (1 - t.attenuation) := by
    dsimp only [c, resetScheduleAttenuation, ResetSlice.attenuation]
    push_cast
    rfl
  have h := evolveResetSchedule_adjacent_exchange [] post s t X
  simp only [List.nil_append, hX, mul_one, ← hcast] at h
  apply sub_nonneg.mp
  rw [← map_sub, h]
  change 0 ≤ readout ((algebraMap ℝ ℂ c) • (t.target-s.target))
  rw [IsScalarTower.algebraMap_smul, map_smul, map_sub, smul_eq_mul]
  exact mul_nonneg hc (sub_nonneg.mpr hOrder)

private theorem moveLeastToFront
    (readout : Matrix n n ℂ →ₗ[ℝ] ℝ) (s : ResetSlice n) (pre post : List (ResetSlice n))
    (X : Matrix n n ℂ) (hX : X.trace = 1)
    (hLeast : ∀ t ∈ pre, readout s.target ≤ readout t.target) :
    readout (evolveResetSchedule (pre ++ s :: post) X) ≤
      readout (evolveResetSchedule (s :: (pre ++ post)) X) := by
  induction pre generalizing X with
  | nil => exact le_rfl
  | cons t pre ih =>
      have hMoved := ih (t.evolve X) ((t.trace_evolve X).trans hX)
        (fun u hu => hLeast u (List.mem_cons_of_mem t hu))
      change readout (evolveResetSchedule (t :: (pre ++ s :: post)) X) ≤
        readout (evolveResetSchedule (s :: t :: (pre ++ post)) X)
      have hSwap := readout_adjacent_le readout s t (pre ++ post) X hX
        (hLeast t List.mem_cons_self)
      exact hMoved.trans hSwap

/-- Any increasing target-readout order attains the maximum among schedules
with the same slices, including repeated slices and zero-duration slices. -/
theorem sorted_resetSchedule_readout_maximal (readout : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (sorted other : List (ResetSlice n)) (X : Matrix n n ℂ) (hX : X.trace = 1)
    (hSort : sorted.Pairwise (fun s t => readout s.target ≤ readout t.target))
    (hPerm : other.Perm sorted) :
    readout (evolveResetSchedule other X) ≤ readout (evolveResetSchedule sorted X) := by
  induction sorted generalizing other X with
  | nil =>
      rw [List.perm_nil.mp hPerm]
  | cons s tail ih =>
      have hMem : s ∈ other := hPerm.mem_iff.mpr List.mem_cons_self
      obtain ⟨pre, post, rfl⟩ := List.append_of_mem hMem
      obtain ⟨hLeast, hTail⟩ := List.pairwise_cons.mp hSort
      have hFront (t : ResetSlice n) (ht : t ∈ pre) :
          readout s.target ≤ readout t.target := by
        have hIn : t ∈ s :: tail := hPerm.mem_iff.mp (List.mem_append_left _ ht)
        rcases List.mem_cons.mp hIn with rfl | hIn
        · exact le_rfl
        · exact hLeast t hIn
      have hRest : (pre ++ post).Perm tail := (List.perm_middle.symm.trans hPerm).cons_inv
      have hMove := moveLeastToFront readout s pre post X hX hFront
      have hMax := ih (pre ++ post) (s.evolve X) ((s.trace_evolve X).trans hX) hTail hRest
      exact hMove.trans hMax

/-- Sorting by target readout gives a certificate of the maximal terminal
readout for every trace-one input, with one shared maximizing order. -/
theorem exists_optimal_resetSchedule_readout (readout : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (steps : List (ResetSlice n)) :
    ∃ order : List (ResetSlice n), order.Perm steps ∧
      order.Pairwise (fun s t => readout s.target ≤ readout t.target) ∧
      ∀ (other : List (ResetSlice n)) (X : Matrix n n ℂ), X.trace = 1 →
        other.Perm steps →
        readout (evolveResetSchedule other X) ≤ readout (evolveResetSchedule order X) := by
  classical
  let before : ResetSlice n → ResetSlice n → Bool :=
    fun s t => decide (readout s.target ≤ readout t.target)
  let order := steps.mergeSort before
  have hPerm : order.Perm steps := List.mergeSort_perm steps before
  have hTrans : ∀ s t u, before s t → before t u → before s u := by
    intro s t u hst htu
    simp only [before, decide_eq_true_eq] at hst htu ⊢
    exact hst.trans htu
  have hTotal : ∀ s t, before s t || before t s := by
    intro s t
    rcases le_total (readout s.target) (readout t.target) with h | h <;> simp [before, h]
  have hSort : order.Pairwise (fun s t => readout s.target ≤ readout t.target) := by
    simpa only [before, decide_eq_true_eq] using (List.pairwise_mergeSort hTrans hTotal steps)
  exact ⟨order, hPerm, hSort, fun other X hX hOther =>
    sorted_resetSchedule_readout_maximal readout order other X hX hSort (hOther.trans hPerm.symm)⟩

omit [DecidableEq n] in
theorem resetScheduleDose_eq_of_perm {left right : List (ResetSlice n)}
    (h : left.Perm right) : resetScheduleDose left = resetScheduleDose right :=
  (h.map ResetSlice.dose).sum_eq

/-- Increasing and decreasing target-readout orders are simultaneous upper
and lower certificates. The two extremizers preserve the original dose
and bound every permutation, using the same orders for all trace-one inputs. -/
theorem exists_extremal_resetSchedule_readouts (readout : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (steps : List (ResetSlice n)) :
    ∃ lo hi : List (ResetSlice n),
      lo.Perm steps ∧ hi.Perm steps ∧
      lo.Pairwise (fun s t => readout t.target ≤ readout s.target) ∧
      hi.Pairwise (fun s t => readout s.target ≤ readout t.target) ∧
      resetScheduleDose lo = resetScheduleDose steps ∧
      resetScheduleDose hi = resetScheduleDose steps ∧
      ∀ (other : List (ResetSlice n)) (X : Matrix n n ℂ), X.trace = 1 →
        other.Perm steps →
        readout (evolveResetSchedule lo X) ≤ readout (evolveResetSchedule other X) ∧
        readout (evolveResetSchedule other X) ≤ readout (evolveResetSchedule hi X) := by
  obtain ⟨lo, hLo, hLoSorted, hLoBound⟩ := exists_optimal_resetSchedule_readout (-readout) steps
  obtain ⟨hi, hHi, hHiSorted, hHiBound⟩ := exists_optimal_resetSchedule_readout readout steps
  have hLoOrder : lo.Pairwise (fun s t => readout t.target ≤ readout s.target) := by
    simpa only [LinearMap.neg_apply, neg_le_neg_iff] using hLoSorted
  refine ⟨lo, hi, hLo, hHi, hLoOrder, hHiSorted, resetScheduleDose_eq_of_perm hLo,
    resetScheduleDose_eq_of_perm hHi, ?_⟩
  intro other X hX hOther
  refine ⟨?_, hHiBound other X hX hOther⟩
  simpa only [LinearMap.neg_apply, neg_le_neg_iff] using hLoBound other X hX hOther

end SKEFTHawking.FinitePositiveKernel.GibbsReset
