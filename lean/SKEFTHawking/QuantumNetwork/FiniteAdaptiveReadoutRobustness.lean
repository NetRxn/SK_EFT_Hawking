import SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutDiscrimination

/-! Quantitative stability of attained equal-prior finite readout discrimination.
All branch families are normalized globally. No branch mass is inverted, and
the nominal physical readout is distinguished from a perturbed optimal readout. -/
namespace SKEFTHawking.QuantumNetwork
open Matrix
open scoped BigOperators ComplexOrder

namespace FiniteAdaptiveReadoutRobustness
open FiniteAdaptiveReadoutDiscrimination
variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Fintype H]

theorem branchDistance_comm (A B : H → Matrix ι ι ℂ) :
    branchDistance A B = branchDistance B A := by
  unfold branchDistance
  simp_rw [traceDist_comm]

theorem branchDistance_nonneg (A B : H → Matrix ι ι ℂ) :
    0 ≤ branchDistance A B :=
  Finset.sum_nonneg fun _ _ => traceDist_nonneg _ _

theorem branchDistance_self (A : H → Matrix ι ι ℂ) :
    branchDistance A A = 0 := by
  simp [branchDistance, traceDist, traceNorm_zero]

theorem branchDistance_triangle {A B C : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) (hC : IsBranchFamily C) :
    branchDistance A C ≤ branchDistance A B + branchDistance B C := by
  unfold branchDistance
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun h _ =>
    traceDist_triangle _ _ _ (hA.1 h).isHermitian (hB.1 h).isHermitian
      (hC.1 h).isHermitian

theorem branchDistance_pair_lipschitz {A B A' B' : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hA' : IsBranchFamily A') (hB' : IsBranchFamily B') :
    |branchDistance A B - branchDistance A' B'| ≤
      branchDistance A A' + branchDistance B B' := by
  have h₁ := branchDistance_triangle hA hA' hB
  have h₂ := branchDistance_triangle hA' hB' hB
  have h₃ := branchDistance_triangle hA' hA hB'
  have h₄ := branchDistance_triangle hA hB hB'
  rw [branchDistance_comm B' B] at h₂
  rw [branchDistance_comm A' A] at h₃
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The sharp bound cancels only the GLOBAL signed trace defect. -/
theorem bounded_observable_difference {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (F : H → Matrix ι ι ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) :
    |(∑ h, (F h * A h).trace.re) - (∑ h, (F h * B h).trace.re)| ≤
      branchDistance A B := by
  have h₁ := readoutError_lower hA hB hF
  have h₂ := readoutError_lower hB hA hF
  rw [readoutError_eq _ _ _ hA.2] at h₁
  rw [readoutError_eq _ _ _ hB.2, branchDistance_comm B A] at h₂
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    Finset.sum_sub_distrib] at h₁ h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem fixed_readout_lipschitz {A B A' B' : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hA' : IsBranchFamily A') (hB' : IsBranchFamily B')
    (F : H → Matrix ι ι ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) :
    |readoutError A B F - readoutError A' B' F| ≤
      (branchDistance A A' + branchDistance B B') / 2 := by
  have hx := abs_le.mp (bounded_observable_difference hA hA' F hF)
  have hy := abs_le.mp (bounded_observable_difference hB hB' F hF)
  rw [readoutError_eq _ _ _ hA.2, readoutError_eq _ _ _ hA'.2]
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    Finset.sum_sub_distrib]
  exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

theorem attained_optimum_lipschitz {A B A' B' : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hA' : IsBranchFamily A') (hB' : IsBranchFamily B') :
    |(1 - branchDistance A B) / 2 - (1 - branchDistance A' B') / 2| ≤
      (branchDistance A A' + branchDistance B B') / 2 := by
  have hd := abs_le.mp (branchDistance_pair_lipschitz hA hB hA' hB')
  exact abs_le.mpr ⟨by linarith [hd.2], by linarith [hd.1]⟩

/-- Both infima are independently attained; no optimum is supplied as a premise. -/
theorem attained_optima_stability {A B A' B' : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hA' : IsBranchFamily A') (hB' : IsBranchFamily B') :
    IsLeast {x : ℝ | ∃ F : H → Matrix ι ι ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧ readoutError A B F = x}
      ((1 - branchDistance A B) / 2) ∧
    IsLeast {x : ℝ | ∃ F : H → Matrix ι ι ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧ readoutError A' B' F = x}
      ((1 - branchDistance A' B') / 2) ∧
    |(1 - branchDistance A B) / 2 - (1 - branchDistance A' B') / 2| ≤
      (branchDistance A A' + branchDistance B B') / 2 :=
  ⟨readoutError_isLeast hA hB, readoutError_isLeast hA' hB',
    attained_optimum_lipschitz hA hB hA' hB'⟩

/-- Actual instrument error, with outcome zero choosing A. -/
noncomputable def instrumentError (A B : H → Matrix ι ι ℂ)
    (I : H → FiniteInstrument ι 2) : ℝ :=
  ((∑ h, readoutTable I B h 0) + (∑ h, readoutTable I A h 1)) / 2

/-- The NOMINAL Kraus instrument realizes its same effect on arbitrary new matrices. -/
theorem nominal_optimalReadout_realizes {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (C D : H → Matrix ι ι ℂ) :
    instrumentError C D (optimalReadout hA hB) =
      readoutError C D (optimalEffect hA hB) := by
  simp only [instrumentError, readoutTable, optimalReadout,
    projectiveReadout_weight_zero, projectiveReadout_weight_one, readoutError]

theorem transported_optimalReadout_stability {A B A' B' : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hA' : IsBranchFamily A') (hB' : IsBranchFamily B') :
    |instrumentError A' B' (optimalReadout hA hB) -
      (1 - branchDistance A B) / 2| ≤
      (branchDistance A A' + branchDistance B B') / 2 := by
  rw [nominal_optimalReadout_realizes, ← optimalEffect_attains hA hB, abs_sub_comm]
  exact fixed_readout_lipschitz hA hB hA' hB' _ (optimalEffect_admissible hA hB)

/-- Perturbed optimization uses a separately constructed physical instrument. -/
theorem reoptimized_optimalReadout_attains {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    instrumentError A B (optimalReadout hA hB) = (1 - branchDistance A B) / 2 :=
  optimalReadout_error hA hB

theorem transported_readout_probabilities {A B A' B' : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hA' : IsBranchFamily A') (hB' : IsBranchFamily B') :
    (∀ h a, 0 ≤ readoutTable (optimalReadout hA hB) A' h a) ∧
    (∑ h, ∑ a, readoutTable (optimalReadout hA hB) A' h a) = 1 ∧
    (∀ h a, 0 ≤ readoutTable (optimalReadout hA hB) B' h a) ∧
    (∑ h, ∑ a, readoutTable (optimalReadout hA hB) B' h a) = 1 ∧
    (∀ h a, 0 ≤ readoutTable (optimalReadout hA' hB') A' h a) ∧
    (∑ h, ∑ a, readoutTable (optimalReadout hA' hB') A' h a) = 1 ∧
    (∀ h a, 0 ≤ readoutTable (optimalReadout hA' hB') B' h a) ∧
    (∑ h, ∑ a, readoutTable (optimalReadout hA' hB') B' h a) = 1 :=
  ⟨readoutTable_nonneg _ hA', readoutTable_total _ hA',
    readoutTable_nonneg _ hB', readoutTable_total _ hB',
    readoutTable_nonneg _ hA', readoutTable_total _ hA',
    readoutTable_nonneg _ hB', readoutTable_total _ hB'⟩

/-- Variation of the actual trace-weight law, without conditional branch states. -/
noncomputable def familyHistoryVariation (A B : H → Matrix ι ι ℂ) : ℝ :=
  (∑ h, |(A h).trace.re - (B h).trace.re|) / 2

omit [DecidableEq ι] in
theorem familyHistoryVariation_nonneg (A B : H → Matrix ι ι ℂ) :
    0 ≤ familyHistoryVariation A B :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

omit [DecidableEq ι] in
theorem familyHistoryVariation_comm (A B : H → Matrix ι ι ℂ) :
    familyHistoryVariation A B = familyHistoryVariation B A := by
  simp only [familyHistoryVariation, abs_sub_comm]

omit [DecidableEq ι] in
theorem familyHistoryVariation_triangle (A B C : H → Matrix ι ι ℂ) :
    familyHistoryVariation A C ≤ familyHistoryVariation A B + familyHistoryVariation B C := by
  unfold familyHistoryVariation
  have hs := Finset.sum_le_sum fun h (_ : h ∈ Finset.univ) =>
    abs_sub_le ((A h).trace.re) ((B h).trace.re) ((C h).trace.re)
  rw [Finset.sum_add_distrib] at hs
  linarith

theorem familyHistoryVariation_le_branchDistance {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    familyHistoryVariation A B ≤ branchDistance A B := by
  have hs := Finset.sum_le_sum fun h (_ : h ∈ Finset.univ) =>
    traceNorm_ge_abs_re_trace ((hA.1 h).isHermitian.sub (hB.1 h).isHermitian)
  simp only [Matrix.trace_sub, Complex.sub_re] at hs
  unfold familyHistoryVariation branchDistance traceDist
  rw [← Finset.mul_sum]
  linarith

/-- Centering uses only total signed mass zero, never branchwise trace zero. -/
theorem centered_score_bound (d a : H → ℝ) (hd : ∑ h, d h = 0)
    (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    |∑ h, a h * d h| ≤ (∑ h, |d h|) / 2 := by
  have he : (∑ h, a h * d h) = ∑ h, (a h - 1/2) * d h := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hd, mul_zero, sub_zero]
  rw [he]
  calc
    _ ≤ ∑ h, |(a h - 1/2) * d h| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h, (1/2) * |d h| := by
      apply Finset.sum_le_sum
      intro h _
      rw [abs_mul]
      have hc : |a h - 1/2| ≤ (1/2 : ℝ) :=
        abs_le.mpr ⟨by linarith [(ha h).1], by linarith [(ha h).2]⟩
      exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

omit [DecidableEq ι] in
theorem classical_observable_difference {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (a : H → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    |(∑ h, a h * (A h).trace.re) - (∑ h, a h * (B h).trace.re)| ≤
      familyHistoryVariation A B := by
  have hd : (∑ h, ((A h).trace.re - (B h).trace.re)) = 0 := by
    rw [Finset.sum_sub_distrib, hA.2, hB.2, sub_self]
  have hs := centered_score_bound (fun h => (A h).trace.re - (B h).trace.re) a hd ha
  simpa only [mul_sub, Finset.sum_sub_distrib, familyHistoryVariation] using hs

omit [DecidableEq ι] in
theorem historyError_eq {A : H → Matrix ι ι ℂ} (hA : IsBranchFamily A)
    (B : H → Matrix ι ι ℂ) (a : H → ℝ) :
    historyError A B a =
      (1 - ∑ h, a h * ((A h).trace.re - (B h).trace.re)) / 2 := by
  simp only [historyError, sub_mul, one_mul, mul_sub, Finset.sum_sub_distrib, hA.2]
  ring

omit [DecidableEq ι] in
/-- Every randomized classifier enjoys the sharper HISTORY variation bound. -/
theorem randomized_history_lipschitz {A B A' B' : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hA' : IsBranchFamily A') (hB' : IsBranchFamily B')
    (a : H → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    |historyError A B a - historyError A' B' a| ≤
      (familyHistoryVariation A A' + familyHistoryVariation B B') / 2 := by
  have hx := abs_le.mp (classical_observable_difference hA hA' a ha)
  have hy := abs_le.mp (classical_observable_difference hB hB' a ha)
  rw [historyError_eq hA, historyError_eq hA']
  simp only [mul_sub, Finset.sum_sub_distrib]
  exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

noncomputable def signClassifier (A B : H → Matrix ι ι ℂ) (h : H) : ℝ :=
  if 0 ≤ (A h).trace.re - (B h).trace.re then 1 else 0

omit [DecidableEq ι] [Fintype H] in
theorem signClassifier_admissible (A B : H → Matrix ι ι ℂ) (h : H) :
    signClassifier A B h ∈ Set.Icc (0 : ℝ) 1 := by
  unfold signClassifier
  split <;> norm_num

omit [DecidableEq ι] in
theorem signClassifier_score {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    (∑ h, signClassifier A B h * ((A h).trace.re - (B h).trace.re)) =
      familyHistoryVariation A B := by
  have hp (h : H) : signClassifier A B h * ((A h).trace.re - (B h).trace.re) =
      (|(A h).trace.re - (B h).trace.re| +
        ((A h).trace.re - (B h).trace.re)) / 2 := by
    unfold signClassifier
    split
    · rw [abs_of_nonneg ‹_›]; ring
    · rw [abs_of_neg (lt_of_not_ge ‹_›)]; ring
  simp_rw [hp]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, hA.2, hB.2]
  unfold familyHistoryVariation
  ring

omit [DecidableEq ι] in
theorem historyError_lower {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (a : H → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    (1 - familyHistoryVariation A B) / 2 ≤ historyError A B a := by
  have hs := (abs_le.mp (classical_observable_difference hA hB a ha)).2
  rw [historyError_eq hA]
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

omit [DecidableEq ι] in
theorem signClassifier_attains {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    historyError A B (signClassifier A B) = (1 - familyHistoryVariation A B) / 2 := by
  rw [historyError_eq hA, signClassifier_score hA hB]

omit [DecidableEq ι] in
theorem historyError_isLeast {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    IsLeast {x : ℝ | ∃ a : H → ℝ, (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) ∧
      historyError A B a = x} ((1 - familyHistoryVariation A B) / 2) := by
  refine ⟨⟨signClassifier A B, signClassifier_admissible A B, signClassifier_attains hA hB⟩, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  exact historyError_lower hA hB a ha

/-- The sign rule has actual globally normalized nonnegative Born probabilities. -/
theorem sign_classifier_probabilities {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    (∀ h b, 0 ≤ effectTable (fun h => (signClassifier A B h : ℂ) • 1) A h b) ∧
    (∑ h, ∑ b, effectTable (fun h => (signClassifier A B h : ℂ) • 1) A h b) = 1 ∧
    (∀ h b, 0 ≤ effectTable (fun h => (signClassifier A B h : ℂ) • 1) B h b) ∧
    (∑ h, ∑ b, effectTable (fun h => (signClassifier A B h : ℂ) • 1) B h b) = 1 :=
  ⟨effectTable_nonneg (scalar_effect_admissible _ (signClassifier_admissible A B)) hA,
    effectTable_total _ hA,
    effectTable_nonneg (scalar_effect_admissible _ (signClassifier_admissible A B)) hB,
    effectTable_total _ hB⟩

/-- Universal perturbed-classifier advantage over the same transported quantum rule. -/
theorem readout_advantage_lower {A B A' B' : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hA' : IsBranchFamily A') (hB' : IsBranchFamily B')
    (F : H → Matrix ι ι ℂ) (hF : ∀ h, IsBinaryPOVM (F h))
    (eh : ℝ)
    (hfloor : ∀ a : H → ℝ, (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) → eh ≤ historyError A B a)
    (a : H → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    eh - readoutError A B F -
      (branchDistance A A' + branchDistance B B' +
        familyHistoryVariation A A' + familyHistoryVariation B B') / 2 ≤
      historyError A' B' a - readoutError A' B' F := by
  have hc := (abs_le.mp (randomized_history_lipschitz hA hB hA' hB' a ha)).2
  have hq := (abs_le.mp (fixed_readout_lipschitz hA hB hA' hB' F hF)).1
  linarith [hfloor a ha]

theorem readout_advantage_conservative {A B A' B' : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hA' : IsBranchFamily A') (hB' : IsBranchFamily B')
    (F : H → Matrix ι ι ℂ) (hF : ∀ h, IsBinaryPOVM (F h))
    (eh : ℝ)
    (hfloor : ∀ a : H → ℝ, (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) → eh ≤ historyError A B a)
    (a : H → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    eh - readoutError A B F - branchDistance A A' - branchDistance B B' ≤
      historyError A' B' a - readoutError A' B' F := by
  have h := readout_advantage_lower hA hB hA' hB' F hF eh hfloor a ha
  have hx := familyHistoryVariation_le_branchDistance hA hA'
  have hy := familyHistoryVariation_le_branchDistance hB hB'
  linarith

/-- A deterministic sign rule is a scalar orthogonal projection. -/
noncomputable def signProjection (A B : H → Matrix ι ι ℂ) (h : H) : Matrix ι ι ℂ :=
  if 0 ≤ (A h).trace.re - (B h).trace.re then 1 else 0

omit [Fintype H] in
theorem signProjection_hermitian (A B : H → Matrix ι ι ℂ) (h : H) :
    (signProjection A B h).IsHermitian := by
  unfold signProjection
  split
  · exact Matrix.isHermitian_one
  · exact Matrix.isHermitian_zero

omit [Fintype H] in
theorem signProjection_idem (A B : H → Matrix ι ι ℂ) (h : H) :
    signProjection A B h * signProjection A B h = signProjection A B h := by
  unfold signProjection
  split <;> simp

omit [Fintype H] in
theorem signProjection_scalar (A B : H → Matrix ι ι ℂ) (h : H) :
    signProjection A B h = (signClassifier A B h : ℂ) • 1 := by
  unfold signProjection signClassifier
  split <;> simp

noncomputable def signReadout (A B : H → Matrix ι ι ℂ) (h : H) : FiniteInstrument ι 2 :=
  projectiveReadout (signProjection A B h) (signProjection_hermitian A B h)
    (signProjection_idem A B h)

/-- The same actual Kraus rule realizes its scalar effect on ALL complex inputs. -/
theorem signReadout_realizes (A B C D : H → Matrix ι ι ℂ) :
    instrumentError C D (signReadout A B) = historyError C D (signClassifier A B) := by
  simp only [instrumentError, readoutTable, signReadout,
    projectiveReadout_weight_zero, projectiveReadout_weight_one, signProjection_scalar]
  exact historyError_scalar_effect C D (signClassifier A B)

theorem signReadout_attains {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    instrumentError A B (signReadout A B) = (1 - familyHistoryVariation A B) / 2 := by
  rw [signReadout_realizes, signClassifier_attains hA hB]

theorem signReadout_probabilities {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    (∀ h a, 0 ≤ readoutTable (signReadout A B) A h a) ∧
    (∑ h, ∑ a, readoutTable (signReadout A B) A h a) = 1 ∧
    (∀ h a, 0 ≤ readoutTable (signReadout A B) B h a) ∧
    (∑ h, ∑ a, readoutTable (signReadout A B) B h a) = 1 :=
  ⟨readoutTable_nonneg _ hA, readoutTable_total _ hA,
    readoutTable_nonneg _ hB, readoutTable_total _ hB⟩

theorem readout_advantage_strict {A B A' B' : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hA' : IsBranchFamily A') (hB' : IsBranchFamily B')
    (F : H → Matrix ι ι ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) (eh : ℝ)
    (hfloor : ∀ a : H → ℝ, (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) → eh ≤ historyError A B a)
    (hgap : (branchDistance A A' + branchDistance B B' +
      familyHistoryVariation A A' + familyHistoryVariation B B') / 2 <
      eh - readoutError A B F)
    (a : H → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    readoutError A' B' F < historyError A' B' a := by
  have h := readout_advantage_lower hA hB hA' hB' F hF eh hfloor a ha
  linarith

theorem readout_advantage_conservative_strict {A B A' B' : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hA' : IsBranchFamily A') (hB' : IsBranchFamily B')
    (F : H → Matrix ι ι ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) (eh : ℝ)
    (hfloor : ∀ a : H → ℝ, (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) → eh ≤ historyError A B a)
    (hgap : branchDistance A A' + branchDistance B B' < eh - readoutError A B F)
    (a : H → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    readoutError A' B' F < historyError A' B' a := by
  have h := readout_advantage_conservative hA hB hA' hB' F hF eh hfloor a ha
  linarith

section ActualTrees
open FiniteInterventionProcess FiniteAdaptiveMapPerturbation FiniteAdaptiveMixtureSurvival
variable {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]
variable {o n : ℕ}

theorem tree_branchDistance (T U : Tree S E o n) (X Y : Matrix (S × E) (S × E) ℂ) :
    branchDistance (fun h => run S E o T h X) (fun h => run S E o U h Y) = outputDistance S E o T U X Y := by
  simp only [branchDistance, outputDistance, traceDist, div_eq_mul_inv,
    mul_comm, one_mul, Finset.mul_sum]

theorem tree_familyHistoryVariation (T U : Tree S E o n) (X Y : Matrix (S × E) (S × E) ℂ) :
    familyHistoryVariation (fun h => run S E o T h X) (fun h => run S E o U h Y) = historyVariation S E o T U X Y := rfl

theorem tree_distance_stability (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B Y_A Y_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B) :
    |outputDistance S E o T_A T_B X_A X_B - outputDistance S E o U_A U_B Y_A Y_B| ≤ outputDistance S E o T_A U_A X_A Y_A + outputDistance S E o T_B U_B X_B Y_B := by
  simpa only [tree_branchDistance, tree_familyHistoryVariation] using
    branchDistance_pair_lipschitz (run_family T_A hXA) (run_family T_B hXB)
      (run_family U_A hYA) (run_family U_B hYB)

theorem tree_optimum_stability (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B Y_A Y_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B) :
    |(1 - outputDistance S E o T_A T_B X_A X_B)/2 - (1 - outputDistance S E o U_A U_B Y_A Y_B)/2| ≤ (outputDistance S E o T_A U_A X_A Y_A + outputDistance S E o T_B U_B X_B Y_B)/2 := by
  simpa only [tree_branchDistance, tree_familyHistoryVariation] using
    attained_optimum_lipschitz (run_family T_A hXA) (run_family T_B hXB)
      (run_family U_A hYA) (run_family U_B hYB)

theorem tree_fixed_stability (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B Y_A Y_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) :
    |readoutError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) F - readoutError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) F| ≤ (outputDistance S E o T_A U_A X_A Y_A + outputDistance S E o T_B U_B X_B Y_B)/2 := by
  simpa only [tree_branchDistance, tree_familyHistoryVariation] using
    fixed_readout_lipschitz (run_family T_A hXA) (run_family T_B hXB)
      (run_family U_A hYA) (run_family U_B hYB) F hF

theorem tree_history_stability (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B Y_A Y_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B)
    (a : History o n → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    |historyError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) a - historyError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) a| ≤ (historyVariation S E o T_A U_A X_A Y_A + historyVariation S E o T_B U_B X_B Y_B)/2 := by
  simpa only [tree_branchDistance, tree_familyHistoryVariation] using
    randomized_history_lipschitz (run_family T_A hXA) (run_family T_B hXB)
      (run_family U_A hYA) (run_family U_B hYB) a ha

theorem tree_transport_stability (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B Y_A Y_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B) :
    |instrumentError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) (optimalReadout (run_family T_A hXA) (run_family T_B hXB)) - (1 - outputDistance S E o T_A T_B X_A X_B)/2| ≤ (outputDistance S E o T_A U_A X_A Y_A + outputDistance S E o T_B U_B X_B Y_B)/2 := by
  simpa only [tree_branchDistance, tree_familyHistoryVariation] using
    transported_optimalReadout_stability (run_family T_A hXA) (run_family T_B hXB)
      (run_family U_A hYA) (run_family U_B hYB)

/-- Both actual tree optima are proved and independently realized. -/
theorem tree_attained_optima (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B Y_A Y_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B) :
    IsLeast {x : ℝ | ∃ F : History o n → Matrix (S × E) (S × E) ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧ readoutError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) F = x}
      ((1 - outputDistance S E o T_A T_B X_A X_B)/2) ∧
    IsLeast {x : ℝ | ∃ F : History o n → Matrix (S × E) (S × E) ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧ readoutError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) F = x}
      ((1 - outputDistance S E o U_A U_B Y_A Y_B)/2) ∧
    instrumentError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B)
      (optimalReadout (run_family U_A hYA) (run_family U_B hYB)) =
      (1 - outputDistance S E o U_A U_B Y_A Y_B)/2 :=
  ⟨tree_error_isLeast T_A T_B hXA hXB, tree_error_isLeast U_A U_B hYA hYB,
    tree_optimalReadout_error U_A U_B hYA hYB⟩

theorem tree_history_isLeast (T U : Tree S E o n) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    IsLeast {x : ℝ | ∃ a : History o n → ℝ, (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) ∧
      historyError (fun h => run S E o T h X) (fun h => run S E o U h Y) a = x}
      ((1 - historyVariation S E o T U X Y)/2) := by
  simpa only [tree_familyHistoryVariation] using
    historyError_isLeast (run_family T hX) (run_family U hY)

/-- The NOMINAL physical instrument is normalized on all FOUR actual families;
the perturbed optimum has its own two independently normalized tables. -/
theorem tree_physical_probabilities (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B Y_A Y_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B) :
    let I := optimalReadout (run_family T_A hXA) (run_family T_B hXB)
    let J := optimalReadout (run_family U_A hYA) (run_family U_B hYB)
    ((∀ h a, 0 ≤ readoutTable I (fun h => run S E o T_A h X_A) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run S E o T_A h X_A) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable I (fun h => run S E o T_B h X_B) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run S E o T_B h X_B) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable I (fun h => run S E o U_A h Y_A) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run S E o U_A h Y_A) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable I (fun h => run S E o U_B h Y_B) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run S E o U_B h Y_B) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable J (fun h => run S E o U_A h Y_A) h a) ∧ (∑ h, ∑ a, readoutTable J (fun h => run S E o U_A h Y_A) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable J (fun h => run S E o U_B h Y_B) h a) ∧ (∑ h, ∑ a, readoutTable J (fun h => run S E o U_B h Y_B) h a) = 1) := by
  dsimp only
  exact ⟨tree_readout_probabilities T_A hXA _, tree_readout_probabilities T_B hXB _,
    tree_readout_probabilities U_A hYA _, tree_readout_probabilities U_B hYB _,
    tree_readout_probabilities U_A hYA _, tree_readout_probabilities U_B hYB _⟩

theorem tree_signReadout_attains (T U : Tree S E o n) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    instrumentError (fun h => run S E o T h X) (fun h => run S E o U h Y)
      (signReadout (fun h => run S E o T h X) (fun h => run S E o U h Y)) =
      (1 - historyVariation S E o T U X Y)/2 := by
  simpa only [tree_familyHistoryVariation] using
    signReadout_attains (run_family T hX) (run_family U hY)

/-- Useful budget glue keeps the TWO comparison bounds separate. -/
theorem tree_budget_stability (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B Y_A Y_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B) (βA βB : ℝ)
    (hA : outputDistance S E o T_A U_A X_A Y_A ≤ βA)
    (hB : outputDistance S E o T_B U_B X_B Y_B ≤ βB)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h))
    (a : History o n → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    (|(1-outputDistance S E o T_A T_B X_A X_B)/2 -
       (1-outputDistance S E o U_A U_B Y_A Y_B)/2| ≤ (βA+βB)/2) ∧
    (|readoutError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) F - readoutError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) F| ≤ (βA+βB)/2) ∧
    (|instrumentError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B)
      (optimalReadout (run_family T_A hXA) (run_family T_B hXB)) -
      (1-outputDistance S E o T_A T_B X_A X_B)/2| ≤ (βA+βB)/2) ∧
    (|historyError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) a - historyError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) a| ≤ (βA+βB)/2) := by
  have hb : (outputDistance S E o T_A U_A X_A Y_A + outputDistance S E o T_B U_B X_B Y_B)/2 ≤ (βA+βB)/2 := by linarith
  have hc := tree_history_stability T_A T_B U_A U_B hXA hXB hYA hYB a ha
  have hx := historyVariation_le_outputDistance S E o T_A U_A hXA.1.isHermitian hYA.1.isHermitian
  have hy := historyVariation_le_outputDistance S E o T_B U_B hXB.1.isHermitian hYB.1.isHermitian
  exact ⟨(tree_optimum_stability T_A T_B U_A U_B hXA hXB hYA hYB).trans hb,
    (tree_fixed_stability T_A T_B U_A U_B hXA hXB hYA hYB F hF).trans hb,
    (tree_transport_stability T_A T_B U_A U_B hXA hXB hYA hYB).trans hb,
    hc.trans (by linarith)⟩

theorem tree_paired_errors_stability (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B Y_A Y_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B)
    {esA esB : List ℝ}
    (cA : PairedErrors S E o T_A U_A esA)
    (cB : PairedErrors S E o T_B U_B esB)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h))
    (a : History o n → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    let βA := min 1 (traceDist X_A Y_A + esA.sum)
    let βB := min 1 (traceDist X_B Y_B + esB.sum)
    (|(1-outputDistance S E o T_A T_B X_A X_B)/2 -
       (1-outputDistance S E o U_A U_B Y_A Y_B)/2| ≤ (βA+βB)/2) ∧
    (|readoutError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) F - readoutError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) F| ≤ (βA+βB)/2) ∧
    (|instrumentError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B)
      (optimalReadout (run_family T_A hXA) (run_family T_B hXB)) -
      (1-outputDistance S E o T_A T_B X_A X_B)/2| ≤ (βA+βB)/2) ∧
    (|historyError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) a - historyError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) a| ≤ (βA+βB)/2) := by
  exact tree_budget_stability T_A T_B U_A U_B hXA hXB hYA hYB _ _
    (pairedErrors_capped S E o cA hXA hYA)
    (pairedErrors_capped S E o cB hXB hYB) F hF a ha

theorem tree_paired_mixture_stability (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B Y_A Y_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B)
    {rsA rsB : List NoiseRates}
    (cA : PairedMixture S E o T_A U_A rsA)
    (cB : PairedMixture S E o T_B U_B rsB)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h))
    (a : History o n → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    let βA := survival rsA * traceDist X_A Y_A + 1 - survival rsA
    let βB := survival rsB * traceDist X_B Y_B + 1 - survival rsB
    (|(1-outputDistance S E o T_A T_B X_A X_B)/2 -
       (1-outputDistance S E o U_A U_B Y_A Y_B)/2| ≤ (βA+βB)/2) ∧
    (|readoutError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) F - readoutError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) F| ≤ (βA+βB)/2) ∧
    (|instrumentError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B)
      (optimalReadout (run_family T_A hXA) (run_family T_B hXB)) -
      (1-outputDistance S E o T_A T_B X_A X_B)/2| ≤ (βA+βB)/2) ∧
    (|historyError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) a - historyError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) a| ≤ (βA+βB)/2) := by
  exact tree_budget_stability T_A T_B U_A U_B hXA hXB hYA hYB _ _
    (pairedMixture_changed_input S E o cA hXA hYA)
    (pairedMixture_changed_input S E o cB hXB hYB) F hF a ha

theorem tree_paired_mixture_history {T U : Tree S E o n} {rs : List NoiseRates}
    (c : PairedMixture S E o T U rs) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    familyHistoryVariation (fun h => run S E o T h X) (fun h => run S E o U h Y) ≤
      survival rs * traceDist X Y + 1 - survival rs := by
  rw [tree_familyHistoryVariation]
  exact pairedMixture_history S E o c hX hY

theorem tree_mixture_budget_cap (rs : List NoiseRates) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    survival rs * traceDist X Y + 1 - survival rs ≤ 1 :=
  survival_bound_cap S E rs hX hY

/-- The sharper gap retains actual history TV instead of replacing it by joint distance. -/
theorem tree_sharp_advantage (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B Y_A Y_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h))
    (eh : ℝ)
    (hfloor : ∀ a : History o n → ℝ, (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) →
      eh ≤ historyError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) a)
    (a : History o n → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    eh - readoutError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) F -
      (outputDistance S E o T_A U_A X_A Y_A + outputDistance S E o T_B U_B X_B Y_B +
       historyVariation S E o T_A U_A X_A Y_A + historyVariation S E o T_B U_B X_B Y_B)/2 ≤
      historyError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) a -
      readoutError (fun h => run S E o U_A h Y_A) (fun h => run S E o U_B h Y_B) F := by
  simpa only [tree_branchDistance, tree_familyHistoryVariation] using
    readout_advantage_lower (run_family T_A hXA) (run_family T_B hXB)
      (run_family U_A hYA) (run_family U_B hYB) F hF eh hfloor a ha

/-- Zero certificates keep actual trees and physical transport in the statement. -/
theorem tree_zero_errors (T_A T_B U_A U_B : Tree S E o n)
    {X_A X_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    {esA esB : List ℝ} (cA : PairedErrors S E o T_A U_A esA)
    (cB : PairedErrors S E o T_B U_B esB) (hA : esA.sum = 0) (hB : esB.sum = 0)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h))
    (a : History o n → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    (1-outputDistance S E o T_A T_B X_A X_B)/2 =
      (1-outputDistance S E o U_A U_B X_A X_B)/2 ∧
    readoutError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) F =
      readoutError (fun h => run S E o U_A h X_A) (fun h => run S E o U_B h X_B) F ∧
    instrumentError (fun h => run S E o U_A h X_A) (fun h => run S E o U_B h X_B)
      (optimalReadout (run_family T_A hXA) (run_family T_B hXB)) =
      (1-outputDistance S E o T_A T_B X_A X_B)/2 ∧
    historyError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B) a =
      historyError (fun h => run S E o U_A h X_A) (fun h => run S E o U_B h X_B) a := by
  have h := tree_paired_errors_stability T_A T_B U_A U_B hXA hXB hXA hXB cA cB F hF a ha
  simp only [hA, hB, traceDist_self, zero_add, min_eq_right (by norm_num : (0 : ℝ) ≤ 1),
    zero_div] at h
  have hz (x y : ℝ) (hxy : |x-y| ≤ 0) : x = y := by
    have hb := abs_le.mp hxy
    linarith [hb.1, hb.2]
  exact ⟨hz _ _ h.1, hz _ _ h.2.1, hz _ _ h.2.2.1, hz _ _ h.2.2.2⟩

theorem tree_survival_zero_bound {T U : Tree S E o n} {rs : List NoiseRates}
    (c : PairedMixture S E o T U rs) (hs : survival rs = 0)
    {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance S E o T U X Y ≤ 1 ∧ historyVariation S E o T U X Y ≤ 1 := by
  constructor
  · simpa only [hs, zero_mul, zero_add, sub_zero] using pairedMixture_changed_input S E o c hX hY
  · simpa only [hs, zero_mul, zero_add, sub_zero] using pairedMixture_history S E o c hX hY

theorem tree_survival_one_bound {T U : Tree S E o n} {rs : List NoiseRates}
    (c : PairedMixture S E o T U rs) (hs : survival rs = 1)
    {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance S E o T U X Y ≤ traceDist X Y ∧
    historyVariation S E o T U X Y ≤ traceDist X Y := by
  constructor
  · simpa only [hs, one_mul, add_sub_cancel_right] using pairedMixture_changed_input S E o c hX hY
  · simpa only [hs, one_mul, add_sub_cancel_right] using pairedMixture_history S E o c hX hY

/-- An actual arbitrary tree always has a constructed zero-error self certificate. -/
theorem tree_self_errors (T : Tree S E o n) :
    PairedErrors S E o T T (List.replicate n 0) := by
  induction T with
  | done => exact .done
  | @node n D F ih =>
    apply PairedErrors.node
    · constructor
      · norm_num
      · intro Z _
        simp [stepDistance, traceNorm_zero]
    · exact List.length_replicate ..
    · exact ih

theorem tree_self_zero_guard (T_A T_B : Tree S E o n)
    {X_A X_B : Matrix (S × E) (S × E) ℂ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) :
    instrumentError (fun h => run S E o T_A h X_A) (fun h => run S E o T_B h X_B)
      (optimalReadout (run_family T_A hXA) (run_family T_B hXB)) =
      (1-outputDistance S E o T_A T_B X_A X_B)/2 := by
  exact (tree_zero_errors T_A T_B T_A T_B hXA hXB (tree_self_errors T_A)
    (tree_self_errors T_B) (by simp) (by simp) F hF
    (fun _ => 0) (by intro h; norm_num)).2.2.1

end ActualTrees

section Guards
open FiniteMemoryProcess FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open scoped Kronecker

/-- Convex preparation uses the original genuinely complex noncommuting pair. -/
noncomputable def qubitMixture (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1-r : ℝ) : ℂ) • qubitX + (r : ℂ) • qubitY

theorem qubitMixture_density {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsDensityOperator (qubitMixture r) := by
  refine ⟨(qubitX_density.1.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hr1))).add
    (qubitY_density.1.smul (Complex.zero_le_real.mpr hr)), ?_⟩
  simp [qubitMixture, Matrix.trace_add, Matrix.trace_smul,
    qubitX_density.2, qubitY_density.2]

theorem qubitMixture_change {r : ℝ} (hr : 0 ≤ r) :
    traceDist qubitX (qubitMixture r) = r * invSqrtTwo := by
  have he : qubitX - qubitMixture r = (r : ℂ) • (qubitX - qubitY) := by
    unfold qubitMixture
    push_cast
    module
  unfold traceDist
  rw [he, traceNorm_smul_nonneg hr]
  have h := qubit_distance
  unfold traceDist at h
  nlinarith

theorem qubitMixture_distance {r : ℝ} (hr1 : r ≤ 1) :
    traceDist (qubitMixture r) qubitY = (1-r) * invSqrtTwo := by
  have he : qubitMixture r - qubitY = ((1-r : ℝ) : ℂ) • (qubitX - qubitY) := by
    unfold qubitMixture
    push_cast
    module
  unfold traceDist
  rw [he, traceNorm_smul_nonneg (sub_nonneg.mpr hr1)]
  have h := qubit_distance
  unfold traceDist at h
  nlinarith

/-- Exact linearity of an ACTUAL instrument's weights on all complex matrices. -/
theorem instrument_weight_real_linear (I : FiniteInstrument ι 2) (b : Fin 2)
    (X Y : Matrix ι ι ℂ) (c d : ℝ) :
    I.weight b ((c : ℂ) • X + (d : ℂ) • Y) =
      c * I.weight b X + d * I.weight b Y := by
  simp only [FiniteInstrument.weight, FiniteInstrument.branch_add,
    FiniteInstrument.branch_smul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem qubitMixture_readout_error (r : ℝ) :
    instrumentError (fun _ : Unit => qubitMixture r) (fun _ : Unit => qubitY)
      (fun _ => qubitReadout) = (1-(1-r)*invSqrtTwo)/2 := by
  simp only [instrumentError, readoutTable]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [qubitMixture, instrument_weight_real_linear]
  rw [qubit_readout_probabilities.2.1, qubit_readout_probabilities.2.2.1,
    qubit_readout_probabilities.2.2.2]
  ring

theorem qubitMixture_isLeast {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsLeast {x : ℝ | ∃ F : Unit → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (fun _ => qubitMixture r) (fun _ => qubitY) F = x}
      ((1-(1-r)*invSqrtTwo)/2) := by
  simpa only [singleton_distance, qubitMixture_distance hr1] using
    readoutError_isLeast (singleton_family (qubitMixture_density hr hr1))
      (singleton_family qubitY_density)

/-- Both fixed physical and independently attained optimal errors saturate the half factor. -/
theorem complex_factor_sharp {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    qubitX * qubitY ≠ qubitY * qubitX ∧
    |instrumentError (fun _ : Unit => qubitX) (fun _ => qubitY) (fun _ => qubitReadout) -
      instrumentError (fun _ : Unit => qubitMixture r) (fun _ => qubitY) (fun _ => qubitReadout)| =
      (branchDistance (fun _ : Unit => qubitX) (fun _ => qubitMixture r) +
       branchDistance (fun _ : Unit => qubitY) (fun _ => qubitY))/2 ∧
    |(1-branchDistance (fun _ : Unit => qubitX) (fun _ => qubitY))/2 -
      (1-branchDistance (fun _ : Unit => qubitMixture r) (fun _ => qubitY))/2| =
      r * invSqrtTwo / 2 := by
  refine ⟨qubit_noncommuting, ?_, ?_⟩
  · have hn : instrumentError (fun _ : Unit => qubitX) (fun _ => qubitY)
        (fun _ => qubitReadout) = (1-invSqrtTwo)/2 := by
      simpa [qubitMixture] using qubitMixture_readout_error 0
    rw [hn, qubitMixture_readout_error, singleton_distance, singleton_distance,
      qubitMixture_change hr, traceDist_self, add_zero]
    have he : (1-invSqrtTwo)/2 - (1-(1-r)*invSqrtTwo)/2 = -(r*invSqrtTwo/2) := by ring
    rw [he, abs_neg, abs_of_nonneg (div_nonneg (mul_nonneg hr invSqrtTwo_pos.le) (by norm_num))]
  · rw [singleton_distance, singleton_distance, qubit_distance, qubitMixture_distance hr1]
    have he : (1-invSqrtTwo)/2 - (1-(1-r)*invSqrtTwo)/2 = -(r*invSqrtTwo/2) := by ring
    rw [he, abs_neg, abs_of_nonneg (div_nonneg (mul_nonneg hr invSqrtTwo_pos.le) (by norm_num))]

theorem qubitMixture_probabilities {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (∀ h b, 0 ≤ readoutTable (fun _ : Unit => qubitReadout) (fun _ => qubitMixture r) h b) ∧
    (∑ h : Unit, ∑ b, readoutTable (fun _ => qubitReadout) (fun _ => qubitMixture r) h b) = 1 ∧
    (∀ h b, 0 ≤ readoutTable (fun _ : Unit => qubitReadout) (fun _ => qubitY) h b) ∧
    (∑ h : Unit, ∑ b, readoutTable (fun _ => qubitReadout) (fun _ => qubitY) h b) = 1 :=
  ⟨readoutTable_nonneg _ (singleton_family (qubitMixture_density hr hr1)),
    readoutTable_total _ (singleton_family (qubitMixture_density hr hr1)),
    readoutTable_nonneg _ (singleton_family qubitY_density),
    readoutTable_total _ (singleton_family qubitY_density)⟩

theorem qubitMixture_genuine {r : ℝ} (hr : 0 < r) :
    qubitMixture r ≠ qubitX := by
  intro he
  have h := qubitMixture_change hr.le
  rw [he, traceDist_self] at h
  have hp := mul_pos hr invSqrtTwo_pos
  linarith

/-- Unequal branch trace defects cancel only after the complete history sum. -/
noncomputable def unequalEffect (h : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  if h = 0 then 1 else 0

theorem unequalEffect_admissible (h : Fin 3) : IsBinaryPOVM (unequalEffect h) := by
  unfold unequalEffect
  split
  · exact isBinaryPOVM_of_projection Matrix.isHermitian_one (by simp)
  · exact isBinaryPOVM_of_projection Matrix.isHermitian_zero (by simp)

theorem unequal_global_sharp :
    |(∑ h, (unequalEffect h * unequalA h).trace.re) -
      (∑ h, (unequalEffect h * unequalB h).trace.re)| = branchDistance unequalA unequalB ∧
    (unequalA 0 - unequalB 0).trace.re ≠ 0 := by
  rw [unequal_distance]
  norm_num [unequalEffect, unequalA, unequalB, Fin.sum_univ_three,
    Matrix.trace_sub, Matrix.trace_smul, qubitX_density.2,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide]

theorem unequal_historyVariation : familyHistoryVariation unequalA unequalB = 3/4 := by
  norm_num [familyHistoryVariation, unequalA, unequalB, Fin.sum_univ_three,
    Matrix.trace_smul, qubitX_density.2, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem unequal_classical_isLeast :
    IsLeast {x : ℝ | ∃ a : Fin 3 → ℝ, (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) ∧
      historyError unequalA unequalB a = x} (1/8) := by
  have h := historyError_isLeast unequalA_family unequalB_family
  norm_num [unequal_historyVariation] at h
  exact h

theorem unequal_signReadout_attains :
    instrumentError unequalA unequalB (signReadout unequalA unequalB) = 1/8 := by
  rw [signReadout_attains unequalA_family unequalB_family, unequal_historyVariation]
  norm_num

/-- Any outcome instrument at a common impossible branch still has zero Born mass. -/
theorem unequal_impossible_readout (I : Fin 3 → FiniteInstrument (Fin 2) 2) (b : Fin 2) :
    readoutTable I unequalA 2 b = 0 ∧ readoutTable I unequalB 2 b = 0 ∧
    readoutTable I unequalA 1 b = 0 := by
  simp [readoutTable, unequalA, unequalB, FiniteInstrument.weight,
    FiniteInstrument.branch_zero, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 0 by decide]

/-- No admissibility or branchwise normalization is needed for identical inputs. -/
theorem identical_family_error {A : H → Matrix ι ι ℂ} (hA : IsBranchFamily A)
    (F : H → Matrix ι ι ℂ) : readoutError A A F = 1/2 := by
  rw [readoutError_eq _ _ _ hA.2]
  simp

omit [DecidableEq ι] in
theorem identical_family_history_error {A : H → Matrix ι ι ℂ} (hA : IsBranchFamily A)
    (a : H → ℝ) : historyError A A a = 1/2 := by
  rw [historyError_eq hA]
  simp

/-- Four REAL depth-zero trees retain the Fin 2 × Unit carrier and arbitrary four inputs. -/
theorem depth_zero_stability {X Y X' Y' : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y)
    (hX' : IsDensityOperator X') (hY' : IsDensityOperator Y')
    (F : History 2 0 → Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ)
    (hF : ∀ h, IsBinaryPOVM (F h)) :
    |readoutError (fun h => run (Fin 2) Unit 2 .done h (qubitJoint X))
      (fun h => run (Fin 2) Unit 2 .done h (qubitJoint Y)) F -
      readoutError (fun h => run (Fin 2) Unit 2 .done h (qubitJoint X'))
      (fun h => run (Fin 2) Unit 2 .done h (qubitJoint Y')) F| ≤
      (traceDist X X' + traceDist Y Y')/2 := by
  simpa only [outputDistance_done, qubitJoint_distance] using
    tree_fixed_stability (S := Fin 2) (E := Unit) (o := 2) .done .done .done .done
      (qubitJoint_density hX) (qubitJoint_density hY)
      (qubitJoint_density hX') (qubitJoint_density hY') F hF

theorem orthogonal_depth_zero_physical :
    let A := fun h => run (Fin 2) Unit 2 (.done : Tree (Fin 2) Unit 2 0) h
      (qubitJoint (basisState 1))
    let B := fun h => run (Fin 2) Unit 2 (.done : Tree (Fin 2) Unit 2 0) h
      (qubitJoint (basisState 0))
    instrumentError A B
      (optimalReadout (run_family .done (qubitJoint_density (basisState_density 1)))
        (run_family .done (qubitJoint_density (basisState_density 0)))) = 0 ∧
    ((∀ h a, 0 ≤ readoutTable
      (optimalReadout (run_family .done (qubitJoint_density (basisState_density 1)))
        (run_family .done (qubitJoint_density (basisState_density 0)))) A h a) ∧
      (∑ h, ∑ a, readoutTable
      (optimalReadout (run_family .done (qubitJoint_density (basisState_density 1)))
        (run_family .done (qubitJoint_density (basisState_density 0)))) A h a) = 1) := by
  dsimp only
  constructor
  · rw [reoptimized_optimalReadout_attains, tree_branchDistance, outputDistance_done,
      qubitJoint_distance, basis_one_zero_distance]
    norm_num
  · exact tree_readout_probabilities .done (qubitJoint_density (basisState_density 1)) _

theorem identical_depth_zero_guard
    (F : History 2 0 → Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ) :
    readoutError
      (fun h => run (Fin 2) Unit 2 .done h (qubitJoint (basisState 0)))
      (fun h => run (Fin 2) Unit 2 .done h (qubitJoint (basisState 0))) F = 1/2 :=
  identical_family_error (run_family .done (qubitJoint_density (basisState_density 0))) F

theorem complex_endpoint_guards :
    qubitMixture 0 = qubitX ∧ qubitMixture 1 = qubitY ∧
    instrumentError (fun _ : Unit => qubitMixture 0) (fun _ => qubitY)
      (fun _ => qubitReadout) = (1-invSqrtTwo)/2 ∧
    instrumentError (fun _ : Unit => qubitMixture 1) (fun _ => qubitY)
      (fun _ => qubitReadout) = 1/2 := by
  refine ⟨by simp [qubitMixture], by simp [qubitMixture], ?_, ?_⟩
  · simpa using qubitMixture_readout_error 0
  · simpa using qubitMixture_readout_error 1

theorem unequal_impossible_classifier (a : Fin 3 → ℝ) (z : ℝ) :
    historyError unequalA unequalB (fun h => if h = 2 then z else a h) =
      historyError unequalA unequalB a := by
  norm_num [historyError, Fin.sum_univ_three, unequalA, unequalB,
    Matrix.trace_smul, qubitX_density.2,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide]

theorem complex_reoptimized_guard {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    let A := fun _ : Unit => qubitMixture r
    let B := fun _ : Unit => qubitY
    let I := optimalReadout (singleton_family (qubitMixture_density hr hr1))
      (singleton_family qubitY_density)
    instrumentError A B I = (1-(1-r)*invSqrtTwo)/2 ∧
    ((∀ h b, 0 ≤ readoutTable I A h b) ∧ (∑ h, ∑ b, readoutTable I A h b) = 1) ∧
    ((∀ h b, 0 ≤ readoutTable I B h b) ∧ (∑ h, ∑ b, readoutTable I B h b) = 1) := by
  dsimp only
  refine ⟨?_, ⟨readoutTable_nonneg _ (singleton_family (qubitMixture_density hr hr1)),
    readoutTable_total _ (singleton_family (qubitMixture_density hr hr1))⟩,
    ⟨readoutTable_nonneg _ (singleton_family qubitY_density),
     readoutTable_total _ (singleton_family qubitY_density)⟩⟩
  rw [reoptimized_optimalReadout_attains, singleton_distance, qubitMixture_distance hr1]

theorem orthogonal_depth_zero_second_probabilities :
    let B := fun h => run (Fin 2) Unit 2 (.done : Tree (Fin 2) Unit 2 0) h
      (qubitJoint (basisState 0))
    let I := optimalReadout (run_family .done (qubitJoint_density (basisState_density 1)))
      (run_family .done (qubitJoint_density (basisState_density 0)))
    (∀ h a, 0 ≤ readoutTable I B h a) ∧ (∑ h, ∑ a, readoutTable I B h a) = 1 := by
  dsimp only
  exact tree_readout_probabilities .done (qubitJoint_density (basisState_density 0)) _

/-- Endpoint bound on EXISTING actual strategies, using a realized certificate. -/
theorem actual_survival_zero_guard :
    outputDistance Qubit Qubit 2 (idealFeedback 1)
      (noisyFeedback 1 (by norm_num) le_rfl 1) correlatedInput correlatedInput ≤ 1 ∧
    historyVariation Qubit Qubit 2 (idealFeedback 1)
      (noisyFeedback 1 (by norm_num) le_rfl 1) correlatedInput correlatedInput ≤ 1 := by
  apply tree_survival_zero_bound
    (FiniteAdaptiveMixtureSurvival.feedback_paired 1 (by norm_num) le_rfl 1)
    (by norm_num [FiniteAdaptiveMixtureSurvival.survival, FiniteAdaptiveMixtureSurvival.retention,
      FiniteAdaptiveMixtureSurvival.zeroRates, FiniteAdaptiveMixtureSurvival.feedbackRate]) correlatedInput_density correlatedInput_density

theorem actual_survival_one_guard :
    outputDistance Qubit Qubit 2 (idealFeedback 1)
      (noisyFeedback 0 le_rfl (by norm_num) 1) correlatedInput correlatedInput ≤ 0 ∧
    historyVariation Qubit Qubit 2 (idealFeedback 1)
      (noisyFeedback 0 le_rfl (by norm_num) 1) correlatedInput correlatedInput ≤ 0 := by
  simpa only [traceDist_self] using tree_survival_one_bound
    (FiniteAdaptiveMixtureSurvival.feedback_paired 0 le_rfl (by norm_num) 1)
    (by norm_num [FiniteAdaptiveMixtureSurvival.survival, FiniteAdaptiveMixtureSurvival.retention,
      FiniteAdaptiveMixtureSurvival.zeroRates, FiniteAdaptiveMixtureSurvival.feedbackRate]) correlatedInput_density correlatedInput_density

end Guards

end FiniteAdaptiveReadoutRobustness
end SKEFTHawking.QuantumNetwork

namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
open Matrix FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open FiniteAdaptiveMixtureSurvival FiniteAdaptiveReadoutDiscrimination FiniteMemoryProcess
open scoped BigOperators ComplexOrder Kronecker
noncomputable section

section NodeWrappers
variable {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E] {o : ℕ}

/-- Independent evolution and instrument noise wraps the actual nominal fields. -/
def wrapStep {l : ℕ} (D : Step S E o) (L : Fin l → Matrix (S × E) (S × E) ℂ)
    (hL : IsKrausChannel L) (J : FiniteInstrument S o) (r : NoiseRates) : Step S E o :=
  mixedStep S E o D.evolution L D.normalized hL D.instrument J r.p r.q r.hp r.hp1 r.hq r.hq1

/-- Both action fields quantify every complex joint matrix and every outcome. -/
def wrapStep_realizes {l : ℕ} (D : Step S E o) (L : Fin l → Matrix (S × E) (S × E) ℂ)
    (hL : IsKrausChannel L) (J : FiniteInstrument S o) (r : NoiseRates) :
    RealizesMixture S E o D (wrapStep D L hL J r) r.p r.q where
  k := D.count
  l := l
  K := D.evolution
  L := L
  hK := D.normalized
  hL := hL
  D := D.instrument
  D' := J
  hp := r.hp
  hp1 := r.hp1
  hq := r.hq
  hq1 := r.hq1
  ideal_action := fun _ _ => rfl
  mixed_action := fun _ _ => rfl

theorem wrapStep_four_terms {l : ℕ} (D : Step S E o)
    (L : Fin l → Matrix (S × E) (S × E) ℂ) (hL : IsKrausChannel L)
    (J : FiniteInstrument S o) (r : NoiseRates) (a : Fin o) (Z : Matrix (S × E) (S × E) ℂ) :
    (wrapStep D L hL J r).branch S E o a Z =
      ((1-r.p)*(1-r.q)) • D.branch S E o a Z +
      (r.p*(1-r.q)) • (D.instrument.lift E).branch a (krausMap L Z) +
      ((1-r.p)*r.q) • (J.lift E).branch a (krausMap D.evolution Z) +
      (r.p*r.q) • (J.lift E).branch a (krausMap L Z) :=
  mixedStep_branch S E o D.evolution L D.normalized hL D.instrument J
    r.p r.q r.hp r.hp1 r.hq r.hq1 a Z

end NodeWrappers

/-- Both physical fields have strictly positive dimensionless rate. -/
def positiveNoise : NoiseRates := ⟨1/256,1/256,by norm_num,by norm_num,by norm_num,by norm_num⟩

def correlationNoisyKeep : Tree Qubit Qubit 2 2 :=
  .node (wrapStep readStep environmentXKraus environmentX_normalized (FiniteInstrument.prepare 1) positiveNoise)
    (fun _ => .node (wrapStep identityPrepare environmentXKraus environmentX_normalized
      (FiniteInstrument.prepare 1) positiveNoise) (fun _ => .done))

def correlationNoisyFlip : Tree Qubit Qubit 2 2 :=
  .node (wrapStep readStep environmentXKraus environmentX_normalized (FiniteInstrument.prepare 1) positiveNoise)
    (fun _ => .node (wrapStep flipPrepare identityKraus identityKraus_normalized
      (FiniteInstrument.prepare 1) positiveNoise) (fun _ => .done))

theorem correlationNoisyKeep_paired :
    PairedMixture Qubit Qubit 2 correlationKeep correlationNoisyKeep [positiveNoise,positiveNoise] := by
  apply PairedMixture.node (wrapStep_realizes ..) (by rfl)
  intro a
  apply PairedMixture.node (wrapStep_realizes ..) (by rfl)
  intro b
  exact .done

theorem correlationNoisyFlip_paired :
    PairedMixture Qubit Qubit 2 correlationFlip correlationNoisyFlip [positiveNoise,positiveNoise] := by
  apply PairedMixture.node (wrapStep_realizes ..) (by rfl)
  intro a
  apply PairedMixture.node (wrapStep_realizes ..) (by rfl)
  intro b
  exact .done

def quarterMemoryStep : Step Qubit Qubit 2 := memoryMixed (1/4) (1/4)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def quarterMemoryTree : Tree Qubit Qubit 2 1 := .node quarterMemoryStep (fun _ => .done)

def memoryNoisyMixed : Tree Qubit Qubit 2 1 :=
  .node (wrapStep quarterMemoryStep environmentXKraus environmentX_normalized
    (FiniteInstrument.prepare 1) positiveNoise) (fun _ => .done)

def memoryNoisyIdentity : Tree Qubit Qubit 2 1 :=
  .node (wrapStep identityPrepare environmentXKraus environmentX_normalized
    (FiniteInstrument.prepare 1) positiveNoise) (fun _ => .done)

theorem memoryNoisyMixed_paired :
    PairedMixture Qubit Qubit 2 quarterMemoryTree memoryNoisyMixed [positiveNoise] := by
  apply PairedMixture.node (wrapStep_realizes ..) (by rfl)
  intro a
  exact .done

theorem memoryNoisyIdentity_paired :
    PairedMixture Qubit Qubit 2 memoryIdentityTree memoryNoisyIdentity [positiveNoise] := by
  apply PairedMixture.node (wrapStep_realizes ..) (by rfl)
  intro a
  exact .done

theorem correlation_survival : survival [positiveNoise,positiveNoise] = (255/256 : ℝ)^4 := by
  norm_num [survival,retention,positiveNoise]

theorem memory_survival : survival [positiveNoise] = (255/256 : ℝ)^2 := by
  norm_num [survival,retention,positiveNoise]

def correlationBudget : ℝ := survival [positiveNoise,positiveNoise]/1024 + 1-survival [positiveNoise,positiveNoise]
def memoryBudget : ℝ := survival [positiveNoise]/1024 + 1-survival [positiveNoise]

theorem correlationBudget_exact : 2*correlationBudget = 72546121729/2199023255552 ∧
    2*correlationBudget < 1/16 := by
  norm_num [correlationBudget,correlation_survival]

theorem memoryBudget_exact : 2*memoryBudget = 588289/33554432 ∧ 2*memoryBudget < 1/32 := by
  norm_num [memoryBudget,memory_survival]

end
end SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness

namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
open Matrix FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open FiniteAdaptiveMixtureSurvival FiniteAdaptiveReadoutDiscrimination FiniteMemoryProcess
open scoped BigOperators ComplexOrder Kronecker
noncomputable section

def changedCorrelationInput : Matrix Joint Joint ℂ :=
  (1023/1024 : ℂ) • correlatedInput + (1/1024 : ℂ) • (basisState 0 ⊗ₖ basisState 1)
def changedMemoryInput : Matrix Joint Joint ℂ :=
  (1023/1024 : ℂ) • memoryInput + (1/1024 : ℂ) • (basisState 0 ⊗ₖ basisState 1)

theorem changedCorrelationInput_density : IsDensityOperator changedCorrelationInput := by
  refine ⟨(correlatedInput_density.1.smul (by norm_num [Complex.le_def])).add
    ((basisJoint_density 0 1).1.smul (by norm_num [Complex.le_def])), ?_⟩
  norm_num [changedCorrelationInput,Matrix.trace_add,Matrix.trace_smul,
    correlatedInput_density.2,(basisJoint_density 0 1).2]

theorem changedMemoryInput_density : IsDensityOperator changedMemoryInput := by
  refine ⟨(memoryInput_density.1.smul (by norm_num [Complex.le_def])).add
    ((basisJoint_density 0 1).1.smul (by norm_num [Complex.le_def])), ?_⟩
  norm_num [changedMemoryInput,Matrix.trace_add,Matrix.trace_smul,
    memoryInput_density.2,(basisJoint_density 0 1).2]

theorem correlationInput_diagonal : correlatedInput - changedCorrelationInput =
    diagonal (fun i : Joint => ((if i=(0,0) ∨ i=(1,1) then 1/2048 else
      if i=(0,1) then -1/1024 else 0 : ℝ) : ℂ)) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [changedCorrelationInput,correlatedInput,Matrix.kronecker_apply,basisState,Matrix.diagonal_apply]

theorem memoryInput_diagonal : memoryInput - changedMemoryInput =
    diagonal (fun i : Joint => ((if i=(1,0) then 1/1024 else
      if i=(0,1) then -1/1024 else 0 : ℝ) : ℂ)) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [changedMemoryInput,memoryInput,Matrix.kronecker_apply,basisState,Matrix.diagonal_apply]

theorem changedCorrelationInput_distance : traceDist correlatedInput changedCorrelationInput = 1/1024 := by
  rw [traceDist,correlationInput_diagonal,traceNorm_real_diagonal]
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_two]

theorem changedMemoryInput_distance : traceDist memoryInput changedMemoryInput = 1/1024 := by
  rw [traceDist,memoryInput_diagonal,traceNorm_real_diagonal]
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_two]

theorem changedCorrelationInput_ne : changedCorrelationInput ≠ correlatedInput := by
  intro h
  have e := changedCorrelationInput_distance
  rw [h,traceDist_self] at e
  norm_num at e

theorem changedMemoryInput_ne : changedMemoryInput ≠ memoryInput := by
  intro h
  have e := changedMemoryInput_distance
  rw [h,traceDist_self] at e
  norm_num at e
end
end SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness

namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
open Matrix FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open FiniteAdaptiveMixtureSurvival FiniteAdaptiveReadoutDiscrimination FiniteMemoryProcess
open scoped BigOperators ComplexOrder Kronecker
noncomputable section

theorem correlationReadout_realizes (A B : History 2 2 → Matrix Joint Joint ℂ) :
    instrumentError A B correlationReadout = readoutError A B correlationEffect := by
  simp only [instrumentError,readoutTable,correlationReadout_weight_zero,
    correlationReadout_weight_one,readoutError]

theorem memoryReadout_realizes (A B : History 2 1 → Matrix Joint Joint ℂ) :
    instrumentError A B memoryReadout = readoutError A B memoryEffect := by
  simp only [instrumentError,readoutTable,memoryReadout_weight_zero,
    memoryReadout_weight_one,readoutError]

theorem correlation_mixture_advantage (U V : Tree Qubit Qubit 2 2)
    {Y Z : Matrix Joint Joint ℂ} (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z)
    {rsA rsB : List NoiseRates}
    (cA : PairedMixture Qubit Qubit 2 correlationKeep U rsA)
    (cB : PairedMixture Qubit Qubit 2 correlationFlip V rsB)
    (a : History 2 2 → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    1/2 - (survival rsA * traceDist correlatedInput Y + 1-survival rsA) -
      (survival rsB * traceDist correlatedInput Z + 1-survival rsB) ≤
    historyError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) a -
      instrumentError (fun h => run Qubit Qubit 2 U h Y)
        (fun h => run Qubit Qubit 2 V h Z) correlationReadout := by
  have h := readout_advantage_conservative (run_family correlationKeep correlatedInput_density)
    (run_family correlationFlip correlatedInput_density) (run_family U hY) (run_family V hZ)
    correlationEffect (fun h => isBinaryPOVM_of_projection (correlationEffect_hermitian h)
      (correlationEffect_idem h)) (1/2)
    (fun a ha => le_of_eq (correlation_history_only a ha).symm) a ha
  rw [correlation_effect_error_zero,sub_zero,tree_branchDistance,tree_branchDistance] at h
  rw [correlationReadout_realizes]
  have hA := pairedMixture_changed_input Qubit Qubit 2 cA correlatedInput_density hY
  have hB := pairedMixture_changed_input Qubit Qubit 2 cB correlatedInput_density hZ
  linarith

theorem memory_mixture_advantage (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (U V : Tree Qubit Qubit 2 1) {Y Z : Matrix Joint Joint ℂ}
    (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z) {rsA rsB : List NoiseRates}
    (cA : PairedMixture Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) U rsA)
    (cB : PairedMixture Qubit Qubit 2 memoryIdentityTree V rsB)
    (a : History 2 1 → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    p*(1-q)/2 - (survival rsA * traceDist memoryInput Y + 1-survival rsA) -
      (survival rsB * traceDist memoryInput Z + 1-survival rsB) ≤
    historyError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) a -
      instrumentError (fun h => run Qubit Qubit 2 U h Y)
        (fun h => run Qubit Qubit 2 V h Z) memoryReadout := by
  have h := readout_advantage_conservative
    (run_family (memoryMixedTree p q hp hp1 hq hq1) memoryInput_density)
    (run_family memoryIdentityTree memoryInput_density) (run_family U hY) (run_family V hZ)
    memoryEffect (fun h => isBinaryPOVM_of_projection (memoryEffect_hermitian h)
      (memoryEffect_idem h)) ((1-q)/2) (fun a ha => memory_history_lower p q hp hp1 hq hq1 a ha) a ha
  rw [memoryReadout_optimal_effect,tree_branchDistance,tree_branchDistance] at h
  rw [memoryReadout_realizes]
  have hA := pairedMixture_changed_input Qubit Qubit 2 cA memoryInput_density hY
  have hB := pairedMixture_changed_input Qubit Qubit 2 cB memoryInput_density hZ
  nlinarith

theorem correlation_mixture_strict (U V : Tree Qubit Qubit 2 2)
    {Y Z : Matrix Joint Joint ℂ} (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z)
    {rsA rsB : List NoiseRates}
    (cA : PairedMixture Qubit Qubit 2 correlationKeep U rsA)
    (cB : PairedMixture Qubit Qubit 2 correlationFlip V rsB)
    (hsmall : (survival rsA * traceDist correlatedInput Y + 1-survival rsA) +
      (survival rsB * traceDist correlatedInput Z + 1-survival rsB) < 1/2)
    (a : History 2 2 → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    instrumentError (fun h => run Qubit Qubit 2 U h Y)
      (fun h => run Qubit Qubit 2 V h Z) correlationReadout <
    historyError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) a := by
  have h := correlation_mixture_advantage U V hY hZ cA cB a ha
  linarith

theorem memory_mixture_strict (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (U V : Tree Qubit Qubit 2 1) {Y Z : Matrix Joint Joint ℂ}
    (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z) {rsA rsB : List NoiseRates}
    (cA : PairedMixture Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) U rsA)
    (cB : PairedMixture Qubit Qubit 2 memoryIdentityTree V rsB)
    (hsmall : (survival rsA * traceDist memoryInput Y + 1-survival rsA) +
      (survival rsB * traceDist memoryInput Z + 1-survival rsB) < p*(1-q)/2)
    (a : History 2 1 → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    instrumentError (fun h => run Qubit Qubit 2 U h Y)
      (fun h => run Qubit Qubit 2 V h Z) memoryReadout <
    historyError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) a := by
  have h := memory_mixture_advantage p q hp hp1 hq hq1 U V hY hZ cA cB a ha
  linarith

theorem correlationNoisy_comparisons :
    outputDistance Qubit Qubit 2 correlationKeep correlationNoisyKeep correlatedInput changedCorrelationInput ≤ correlationBudget ∧
    outputDistance Qubit Qubit 2 correlationFlip correlationNoisyFlip correlatedInput changedCorrelationInput ≤ correlationBudget := by
  constructor
  · simpa [changedCorrelationInput_distance,correlationBudget,div_eq_mul_inv] using
      pairedMixture_changed_input Qubit Qubit 2 correlationNoisyKeep_paired correlatedInput_density changedCorrelationInput_density
  · simpa [changedCorrelationInput_distance,correlationBudget,div_eq_mul_inv] using
      pairedMixture_changed_input Qubit Qubit 2 correlationNoisyFlip_paired correlatedInput_density changedCorrelationInput_density

theorem memoryNoisy_comparisons :
    outputDistance Qubit Qubit 2 quarterMemoryTree memoryNoisyMixed memoryInput changedMemoryInput ≤ memoryBudget ∧
    outputDistance Qubit Qubit 2 memoryIdentityTree memoryNoisyIdentity memoryInput changedMemoryInput ≤ memoryBudget := by
  constructor
  · simpa [changedMemoryInput_distance,memoryBudget,div_eq_mul_inv] using
      pairedMixture_changed_input Qubit Qubit 2 memoryNoisyMixed_paired memoryInput_density changedMemoryInput_density
  · simpa [changedMemoryInput_distance,memoryBudget,div_eq_mul_inv] using
      pairedMixture_changed_input Qubit Qubit 2 memoryNoisyIdentity_paired memoryInput_density changedMemoryInput_density

theorem correlationNoisy_universal_gap (a : History 2 2 → ℝ)
    (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    7/16 < historyError (fun h => run Qubit Qubit 2 correlationNoisyKeep h changedCorrelationInput)
      (fun h => run Qubit Qubit 2 correlationNoisyFlip h changedCorrelationInput) a -
      instrumentError (fun h => run Qubit Qubit 2 correlationNoisyKeep h changedCorrelationInput)
        (fun h => run Qubit Qubit 2 correlationNoisyFlip h changedCorrelationInput) correlationReadout := by
  have h := correlation_mixture_advantage correlationNoisyKeep correlationNoisyFlip
    changedCorrelationInput_density changedCorrelationInput_density
    correlationNoisyKeep_paired correlationNoisyFlip_paired a ha
  simp only [changedCorrelationInput_distance] at h
  have hb := correlationBudget_exact.2
  unfold correlationBudget at hb
  linarith

theorem memoryNoisy_universal_gap (a : History 2 1 → ℝ)
    (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    1/16 < historyError (fun h => run Qubit Qubit 2 memoryNoisyMixed h changedMemoryInput)
      (fun h => run Qubit Qubit 2 memoryNoisyIdentity h changedMemoryInput) a -
      instrumentError (fun h => run Qubit Qubit 2 memoryNoisyMixed h changedMemoryInput)
        (fun h => run Qubit Qubit 2 memoryNoisyIdentity h changedMemoryInput) memoryReadout := by
  have h := memory_mixture_advantage (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    memoryNoisyMixed memoryNoisyIdentity changedMemoryInput_density changedMemoryInput_density
    memoryNoisyMixed_paired memoryNoisyIdentity_paired a ha
  simp only [changedMemoryInput_distance] at h
  have hb := memoryBudget_exact.2
  unfold memoryBudget at hb
  norm_num at h
  linarith

theorem correlationNoisy_tables :
    ((∀ h a, 0 ≤ readoutTable correlationReadout (fun h => run Qubit Qubit 2 correlationNoisyKeep h changedCorrelationInput) h a) ∧
      (∑ h, ∑ a, readoutTable correlationReadout (fun h => run Qubit Qubit 2 correlationNoisyKeep h changedCorrelationInput) h a)=1) ∧
    ((∀ h a, 0 ≤ readoutTable correlationReadout (fun h => run Qubit Qubit 2 correlationNoisyFlip h changedCorrelationInput) h a) ∧
      (∑ h, ∑ a, readoutTable correlationReadout (fun h => run Qubit Qubit 2 correlationNoisyFlip h changedCorrelationInput) h a)=1) :=
  ⟨tree_readout_probabilities correlationNoisyKeep changedCorrelationInput_density correlationReadout,
    tree_readout_probabilities correlationNoisyFlip changedCorrelationInput_density correlationReadout⟩

theorem memoryNoisy_tables :
    ((∀ h a, 0 ≤ readoutTable memoryReadout (fun h => run Qubit Qubit 2 memoryNoisyMixed h changedMemoryInput) h a) ∧
      (∑ h, ∑ a, readoutTable memoryReadout (fun h => run Qubit Qubit 2 memoryNoisyMixed h changedMemoryInput) h a)=1) ∧
    ((∀ h a, 0 ≤ readoutTable memoryReadout (fun h => run Qubit Qubit 2 memoryNoisyIdentity h changedMemoryInput) h a) ∧
      (∑ h, ∑ a, readoutTable memoryReadout (fun h => run Qubit Qubit 2 memoryNoisyIdentity h changedMemoryInput) h a)=1) :=
  ⟨tree_readout_probabilities memoryNoisyMixed changedMemoryInput_density memoryReadout,
    tree_readout_probabilities memoryNoisyIdentity changedMemoryInput_density memoryReadout⟩
end
end SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness


namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
open Matrix FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open FiniteAdaptiveMixtureSurvival FiniteAdaptiveReadoutDiscrimination FiniteMemoryProcess
open scoped BigOperators ComplexOrder Kronecker
noncomputable section

/-- Real scalar homogeneity includes negative coefficients without positivity premises. -/
theorem traceNorm_real_signed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (Z : Matrix ι ι ℂ) : traceNorm (c • Z) = |c| * traceNorm Z := by
  have hc (d : ℝ) : d • Z = (d:ℂ) • Z := by ext i j; simp [Complex.real_smul]
  by_cases h : 0≤c
  · rw [hc,traceNorm_smul_nonneg h,abs_of_nonneg h]
  · have hn : 0≤ -c := by linarith
    have he : c • Z = -((-c) • Z) := by module
    rw [he,traceNorm_neg,hc,traceNorm_smul_nonneg hn,abs_of_neg (lt_of_not_ge h)]

/-- The symmetric control mixes the evolution before the same prepare-zero instrument. -/
def symmetricKeepStep (r : ℝ) (hr : 0≤r) (hr1 : r≤1) : Step Qubit Qubit 2 :=
  realizedStep Qubit Qubit 2 (mixKraus identityKraus environmentXKraus r)
    (mixKraus_channel identityKraus_normalized environmentX_normalized hr hr1) (FiniteInstrument.prepare 0)
def symmetricFlipStep (r : ℝ) (hr : 0≤r) (hr1 : r≤1) : Step Qubit Qubit 2 :=
  realizedStep Qubit Qubit 2 (mixKraus environmentXKraus identityKraus r)
    (mixKraus_channel environmentX_normalized identityKraus_normalized hr hr1) (FiniteInstrument.prepare 0)
def symmetricKeep (r : ℝ) (hr : 0≤r) (hr1 : r≤1) : Tree Qubit Qubit 2 2 :=
  .node readStep (fun _ => .node (symmetricKeepStep r hr hr1) (fun _ => .done))
def symmetricFlip (r : ℝ) (hr : 0≤r) (hr1 : r≤1) : Tree Qubit Qubit 2 2 :=
  .node readStep (fun _ => .node (symmetricFlipStep r hr hr1) (fun _ => .done))

theorem symmetricKeepStep_action (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (a : Qubit) (Z : Matrix Joint Joint ℂ) :
    (symmetricKeepStep r hr hr1).branch Qubit Qubit 2 a Z =
      (1-r) • identityPrepare.branch Qubit Qubit 2 a Z + r • flipPrepare.branch Qubit Qubit 2 a Z := by
  rw [identityPrepare,localStep_branch]
  change ((FiniteInstrument.prepare 0).lift Qubit).branch a (krausMap (mixKraus identityKraus environmentXKraus r) Z)=
    (1-r) • ((FiniteInstrument.prepare 0).lift Qubit).branch a Z +
      r • ((FiniteInstrument.prepare 0).lift Qubit).branch a (krausMap environmentXKraus Z)
  rw [mixKraus_action identityKraus environmentXKraus hr hr1,FiniteInstrument.branch_add,branch_real_smul,branch_real_smul]
  congr 2
  simp [krausMap,identityKraus]

theorem symmetricFlipStep_action (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (a : Qubit) (Z : Matrix Joint Joint ℂ) :
    (symmetricFlipStep r hr hr1).branch Qubit Qubit 2 a Z =
      (1-r) • flipPrepare.branch Qubit Qubit 2 a Z + r • identityPrepare.branch Qubit Qubit 2 a Z := by
  rw [identityPrepare,localStep_branch]
  change ((FiniteInstrument.prepare 0).lift Qubit).branch a (krausMap (mixKraus environmentXKraus identityKraus r) Z)=
    (1-r) • ((FiniteInstrument.prepare 0).lift Qubit).branch a (krausMap environmentXKraus Z) +
      r • ((FiniteInstrument.prepare 0).lift Qubit).branch a Z
  rw [mixKraus_action environmentXKraus identityKraus hr hr1,FiniteInstrument.branch_add,branch_real_smul,branch_real_smul]
  congr 2
  simp [krausMap,identityKraus]

theorem symmetricKeep_run (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (h : History 2 2) (Z : Matrix Joint Joint ℂ) :
    run Qubit Qubit 2 (symmetricKeep r hr hr1) h Z =
      (1-r) • run Qubit Qubit 2 correlationKeep h Z + r • run Qubit Qubit 2 correlationFlip h Z := by
  rcases h with ⟨a,b,u⟩; cases u
  exact symmetricKeepStep_action r hr hr1 b _

theorem symmetricFlip_run (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (h : History 2 2) (Z : Matrix Joint Joint ℂ) :
    run Qubit Qubit 2 (symmetricFlip r hr hr1) h Z =
      (1-r) • run Qubit Qubit 2 correlationFlip h Z + r • run Qubit Qubit 2 correlationKeep h Z := by
  rcases h with ⟨a,b,u⟩; cases u
  exact symmetricFlipStep_action r hr hr1 b _

theorem symmetric_run_difference (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (h : History 2 2) (Z : Matrix Joint Joint ℂ) :
    run Qubit Qubit 2 (symmetricKeep r hr hr1) h Z - run Qubit Qubit 2 (symmetricFlip r hr hr1) h Z =
      (1-2*r) • (run Qubit Qubit 2 correlationKeep h Z - run Qubit Qubit 2 correlationFlip h Z) := by
  rw [symmetricKeep_run,symmetricFlip_run]; module

theorem symmetric_half_all_complex (h : History 2 2) (Z : Matrix Joint Joint ℂ) :
    run Qubit Qubit 2 (symmetricKeep (1/2) (by norm_num) (by norm_num)) h Z =
      run Qubit Qubit 2 (symmetricFlip (1/2) (by norm_num) (by norm_num)) h Z := by
  rw [symmetricKeep_run,symmetricFlip_run]; norm_num; abel

theorem symmetric_full_swap_all_complex (h : History 2 2) (Z : Matrix Joint Joint ℂ) :
    run Qubit Qubit 2 (symmetricKeep 1 (by norm_num) le_rfl) h Z = run Qubit Qubit 2 correlationFlip h Z ∧
    run Qubit Qubit 2 (symmetricFlip 1 (by norm_num) le_rfl) h Z = run Qubit Qubit 2 correlationKeep h Z := by
  simp [symmetricKeep_run,symmetricFlip_run]

theorem symmetric_zero_all_complex (h : History 2 2) (Z : Matrix Joint Joint ℂ) :
    run Qubit Qubit 2 (symmetricKeep 0 le_rfl (by norm_num)) h Z = run Qubit Qubit 2 correlationKeep h Z ∧
    run Qubit Qubit 2 (symmetricFlip 0 le_rfl (by norm_num)) h Z = run Qubit Qubit 2 correlationFlip h Z := by
  simp [symmetricKeep_run,symmetricFlip_run]

theorem symmetric_outputDistance (r : ℝ) (hr : 0≤r) (hr1 : r≤1) :
    outputDistance Qubit Qubit 2 (symmetricKeep r hr hr1) (symmetricFlip r hr hr1) correlatedInput correlatedInput = |1-2*r| := by
  unfold outputDistance
  simp only [symmetric_run_difference,traceNorm_real_signed,← Finset.mul_sum]
  have hn := correlation_outputDistance_one
  unfold outputDistance at hn
  rw [mul_div_assoc,hn,mul_one]

theorem symmetric_same_history (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (h : History 2 2) :
    (run Qubit Qubit 2 (symmetricKeep r hr hr1) h correlatedInput).trace.re =
      (run Qubit Qubit 2 (symmetricFlip r hr hr1) h correlatedInput).trace.re := by
  have he : (run Qubit Qubit 2 correlationKeep h correlatedInput).trace.re =
      (run Qubit Qubit 2 correlationFlip h correlatedInput).trace.re := correlation_same_history h
  simp only [symmetricKeep_run,symmetricFlip_run,Matrix.trace_add,Matrix.trace_smul,Complex.add_re,
    Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [he]

theorem symmetric_history_error (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (a : History 2 2 → ℝ) :
    historyError (fun h => run Qubit Qubit 2 (symmetricKeep r hr hr1) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip r hr hr1) h correlatedInput) a = 1/2 :=
  historyError_same_law (run_family (symmetricKeep r hr hr1) correlatedInput_density) (symmetric_same_history r hr hr1) a

theorem symmetric_same_terminal (r : ℝ) (hr : 0≤r) (hr1 : r≤1) :
    terminalState Qubit Qubit 2 (symmetricKeep r hr hr1) correlatedInput =
      terminalState Qubit Qubit 2 (symmetricFlip r hr hr1) correlatedInput := by
  have ht : (∑ h, run Qubit Qubit 2 correlationKeep h correlatedInput) =
    ∑ h, run Qubit Qubit 2 correlationFlip h correlatedInput := correlation_terminal.1.trans correlation_terminal.2.symm
  simp only [terminalState,symmetricKeep_run,symmetricFlip_run,Finset.sum_add_distrib,← Finset.smul_sum]
  rw [ht]

end
end SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness


namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
open Matrix FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open FiniteAdaptiveMixtureSurvival FiniteAdaptiveReadoutDiscrimination FiniteMemoryProcess
open scoped BigOperators ComplexOrder Kronecker
noncomputable section

/-- Arbitrary-depth feedback uses two independent directional actual-tree certificates. -/
theorem feedback_mixture_optimum (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    (U V : Tree Qubit Qubit 2 (m+1)) {Y Z : Matrix Joint Joint ℂ}
    (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z) {rsA rsB : List NoiseRates}
    (cA : PairedMixture Qubit Qubit 2 (idealFeedback m) U rsA)
    (cB : PairedMixture Qubit Qubit 2 (noisyFeedback p hp hp1 m) V rsB) :
    IsLeast {x : ℝ | ∃ F : History 2 (m+1) → Matrix Joint Joint ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧ readoutError (fun h => run Qubit Qubit 2 U h Y)
        (fun h => run Qubit Qubit 2 V h Z) F = x}
      ((1-outputDistance Qubit Qubit 2 U V Y Z)/2) ∧
    instrumentError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z)
      (optimalReadout (run_family U hY) (run_family V hZ)) = (1-outputDistance Qubit Qubit 2 U V Y Z)/2 ∧
    |(1-outputDistance Qubit Qubit 2 U V Y Z)/2 - (1-p)^m/2| ≤
      ((survival rsA * traceDist correlatedInput Y + 1-survival rsA) +
       (survival rsB * traceDist correlatedInput Z + 1-survival rsB))/2 := by
  refine ⟨tree_error_isLeast U V hY hZ, ?_, ?_⟩
  · simpa only [instrumentError] using tree_optimalReadout_error U V hY hZ
  · have h := tree_optimum_stability (idealFeedback m) (noisyFeedback p hp hp1 m) U V
      correlatedInput_density correlatedInput_density hY hZ
    rw [(noisyFeedback_exact p hp hp1 m).1,sub_sub_cancel,abs_sub_comm] at h
    have hA := pairedMixture_changed_input Qubit Qubit 2 cA correlatedInput_density hY
    have hB := pairedMixture_changed_input Qubit Qubit 2 cB correlatedInput_density hZ
    linarith

/-- The old physical feedback instrument is transported separately from reoptimization. -/
theorem feedback_mixture_fixed (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    (U V : Tree Qubit Qubit 2 (m+1)) {Y Z : Matrix Joint Joint ℂ}
    (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z) {rsA rsB : List NoiseRates}
    (cA : PairedMixture Qubit Qubit 2 (idealFeedback m) U rsA)
    (cB : PairedMixture Qubit Qubit 2 (noisyFeedback p hp hp1 m) V rsB) :
    |instrumentError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z)
      (feedbackReadout p hp hp1 m) - (1-p)^m/2| ≤
      ((survival rsA * traceDist correlatedInput Y + 1-survival rsA) +
       (survival rsB * traceDist correlatedInput Z + 1-survival rsB))/2 := by
  have h := tree_transport_stability (idealFeedback m) (noisyFeedback p hp hp1 m) U V
    correlatedInput_density correlatedInput_density hY hZ
  rw [(noisyFeedback_exact p hp hp1 m).1,sub_sub_cancel] at h
  change |instrumentError _ _ (feedbackReadout p hp hp1 m) - _| ≤ _ at h
  have hA := pairedMixture_changed_input Qubit Qubit 2 cA correlatedInput_density hY
  have hB := pairedMixture_changed_input Qubit Qubit 2 cB correlatedInput_density hZ
  linarith

/-- The independent additive route is available for the same arbitrary-depth consumer. -/
theorem feedback_errors_optimum_fixed (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    (U V : Tree Qubit Qubit 2 (m+1)) {Y Z : Matrix Joint Joint ℂ}
    (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z) {esA esB : List ℝ}
    (cA : PairedErrors Qubit Qubit 2 (idealFeedback m) U esA)
    (cB : PairedErrors Qubit Qubit 2 (noisyFeedback p hp hp1 m) V esB) :
    |(1-outputDistance Qubit Qubit 2 U V Y Z)/2 - (1-p)^m/2| ≤
      (min 1 (traceDist correlatedInput Y + esA.sum) + min 1 (traceDist correlatedInput Z + esB.sum))/2 ∧
    |instrumentError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z)
      (feedbackReadout p hp hp1 m) - (1-p)^m/2| ≤
      (min 1 (traceDist correlatedInput Y + esA.sum) + min 1 (traceDist correlatedInput Z + esB.sum))/2 := by
  have hA := pairedErrors_capped Qubit Qubit 2 cA correlatedInput_density hY
  have hB := pairedErrors_capped Qubit Qubit 2 cB correlatedInput_density hZ
  have ho := tree_optimum_stability (idealFeedback m) (noisyFeedback p hp hp1 m) U V
    correlatedInput_density correlatedInput_density hY hZ
  have hf := tree_transport_stability (idealFeedback m) (noisyFeedback p hp hp1 m) U V
    correlatedInput_density correlatedInput_density hY hZ
  rw [(noisyFeedback_exact p hp hp1 m).1,sub_sub_cancel,abs_sub_comm] at ho
  rw [(noisyFeedback_exact p hp hp1 m).1,sub_sub_cancel] at hf
  change |instrumentError _ _ (feedbackReadout p hp hp1 m) - _| ≤ _ at hf
  exact ⟨by linarith,by linarith⟩

theorem feedback_perturbed_tables (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    (U V : Tree Qubit Qubit 2 (m+1)) {Y Z : Matrix Joint Joint ℂ}
    (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z) :
    let I := feedbackReadout p hp hp1 m
    let J := optimalReadout (run_family U hY) (run_family V hZ)
    ((∀ h a, 0 ≤ readoutTable I (fun h => run Qubit Qubit 2 U h Y) h a) ∧
      (∑ h, ∑ a, readoutTable I (fun h => run Qubit Qubit 2 U h Y) h a)=1) ∧
    ((∀ h a, 0 ≤ readoutTable I (fun h => run Qubit Qubit 2 V h Z) h a) ∧
      (∑ h, ∑ a, readoutTable I (fun h => run Qubit Qubit 2 V h Z) h a)=1) ∧
    ((∀ h a, 0 ≤ readoutTable J (fun h => run Qubit Qubit 2 U h Y) h a) ∧
      (∑ h, ∑ a, readoutTable J (fun h => run Qubit Qubit 2 U h Y) h a)=1) ∧
    ((∀ h a, 0 ≤ readoutTable J (fun h => run Qubit Qubit 2 V h Z) h a) ∧
      (∑ h, ∑ a, readoutTable J (fun h => run Qubit Qubit 2 V h Z) h a)=1) := by
  dsimp only
  exact ⟨tree_readout_probabilities U hY _,tree_readout_probabilities V hZ _,
    tree_readout_probabilities U hY _,tree_readout_probabilities V hZ _⟩

/-- Every depth/rate boundary is obtained from the actual fixed Kraus-rule attainment. -/
theorem feedback_actual_boundary_errors (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    instrumentError (fun h => run Qubit Qubit 2 (idealFeedback 0) h correlatedInput)
      (fun h => run Qubit Qubit 2 (noisyFeedback p hp hp1 0) h correlatedInput) (feedbackReadout p hp hp1 0)=1/2 ∧
    instrumentError (fun h => run Qubit Qubit 2 (idealFeedback m) h correlatedInput)
      (fun h => run Qubit Qubit 2 (noisyFeedback 0 le_rfl (by norm_num) m) h correlatedInput)
      (feedbackReadout 0 le_rfl (by norm_num) m)=1/2 ∧
    instrumentError (fun h => run Qubit Qubit 2 (idealFeedback 0) h correlatedInput)
      (fun h => run Qubit Qubit 2 (noisyFeedback 1 (by norm_num) le_rfl 0) h correlatedInput)
      (feedbackReadout 1 (by norm_num) le_rfl 0)=1/2 ∧
    (0<m → instrumentError (fun h => run Qubit Qubit 2 (idealFeedback m) h correlatedInput)
      (fun h => run Qubit Qubit 2 (noisyFeedback 1 (by norm_num) le_rfl m) h correlatedInput)
      (feedbackReadout 1 (by norm_num) le_rfl m)=0) := by
  exact ⟨feedback_zero_layers p hp hp1,feedback_zero_noise_error m,
    feedback_full_noise_zero_layers,feedback_full_noise_error m⟩
end
end SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness


namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
open Matrix FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open FiniteAdaptiveMixtureSurvival FiniteAdaptiveReadoutDiscrimination FiniteMemoryProcess
open scoped BigOperators ComplexOrder Kronecker
noncomputable section

/-- The transported old physical correlation rule has error r, even above one half. -/
theorem symmetric_fixed_error (r : ℝ) (hr : 0≤r) (hr1 : r≤1) :
    instrumentError (fun h => run Qubit Qubit 2 (symmetricKeep r hr hr1) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip r hr hr1) h correlatedInput) correlationReadout = r := by
  rw [correlationReadout_realizes,readoutError_eq _ _ _ (run_family (symmetricKeep r hr hr1) correlatedInput_density).2]
  have hscore : (∑ h, (correlationEffect h * (run Qubit Qubit 2 correlationKeep h correlatedInput -
      run Qubit Qubit 2 correlationFlip h correlatedInput)).trace.re) = 1 := by
    have h := correlation_effect_error_zero
    rw [readoutError_eq _ _ _ (run_family correlationKeep correlatedInput_density).2] at h
    linarith
  simp only [symmetric_run_difference,Matrix.mul_smul,Matrix.trace_smul,Complex.real_smul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,← Finset.mul_sum]
  rw [hscore]; ring

theorem complementary_readout_error {ι H : Type*} [Fintype ι] [DecidableEq ι] [Fintype H]
    (A B F : H → Matrix ι ι ℂ) :
    readoutError A B (fun h => 1-F h)=readoutError B A F := by
  simp only [readoutError,sub_sub_cancel,add_comm]

theorem swapped_readout_errors {ι H : Type*} [Fintype ι] [DecidableEq ι] [Fintype H]
    {A B : H → Matrix ι ι ℂ} (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (F : H → Matrix ι ι ℂ) : readoutError A B F + readoutError B A F = 1 := by
  rw [readoutError_eq _ _ _ hA.2,readoutError_eq _ _ _ hB.2]
  simp only [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,Finset.sum_sub_distrib]
  ring

def symmetricEffect (r : ℝ) (h : History 2 2) : Matrix Joint Joint ℂ :=
  if r≤1/2 then correlationEffect h else 1-correlationEffect h

theorem symmetricEffect_hermitian (r : ℝ) (h : History 2 2) : (symmetricEffect r h).IsHermitian := by
  unfold symmetricEffect; split
  · exact correlationEffect_hermitian h
  · exact Matrix.isHermitian_one.sub (correlationEffect_hermitian h)

theorem symmetricEffect_idem (r : ℝ) (h : History 2 2) :
    symmetricEffect r h * symmetricEffect r h=symmetricEffect r h := by
  unfold symmetricEffect; split
  · exact correlationEffect_idem h
  · rw [sub_mul,one_mul,mul_sub,mul_one,correlationEffect_idem,sub_self,sub_zero]

def symmetricReadout (r : ℝ) (h : History 2 2) : FiniteInstrument Joint 2 :=
  projectiveReadout (symmetricEffect r h) (symmetricEffect_hermitian r h) (symmetricEffect_idem r h)

theorem symmetricReadout_weights (r : ℝ) (h : History 2 2) (Z : Matrix Joint Joint ℂ) :
    (symmetricReadout r h).weight 0 Z=(symmetricEffect r h * Z).trace.re ∧
    (symmetricReadout r h).weight 1 Z=((1-symmetricEffect r h)*Z).trace.re :=
  ⟨projectiveReadout_weight_zero _ _ _ _,projectiveReadout_weight_one _ _ _ _⟩

theorem symmetricReadout_realizes (r : ℝ) (A B : History 2 2 → Matrix Joint Joint ℂ) :
    instrumentError A B (symmetricReadout r)=readoutError A B (symmetricEffect r) := by
  simp only [instrumentError,readoutTable,symmetricReadout,projectiveReadout_weight_zero,
    projectiveReadout_weight_one,readoutError]

theorem symmetric_min_formula (r : ℝ) : (1-|1-2*r|)/2=min r (1-r) := by
  by_cases h : r≤1/2
  · rw [abs_of_nonneg (by linarith),min_eq_left (by linarith)]; ring
  · rw [abs_of_neg (by linarith),min_eq_right (by linarith)]; ring

theorem symmetric_reoptimized_error (r : ℝ) (hr : 0≤r) (hr1 : r≤1) :
    instrumentError (fun h => run Qubit Qubit 2 (symmetricKeep r hr hr1) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip r hr hr1) h correlatedInput) (symmetricReadout r) = min r (1-r) := by
  rw [symmetricReadout_realizes]
  have hfixed := symmetric_fixed_error r hr hr1
  rw [correlationReadout_realizes] at hfixed
  by_cases h : r≤1/2
  · have he : symmetricEffect r=correlationEffect := by funext k; simp only [symmetricEffect,if_pos h]
    rw [he,hfixed,min_eq_left (by linarith)]
  · have he : symmetricEffect r=(fun k => 1-correlationEffect k) := by funext k; simp only [symmetricEffect,if_neg h]
    rw [he,complementary_readout_error,min_eq_right (by linarith)]
    have hs := swapped_readout_errors (run_family (symmetricKeep r hr hr1) correlatedInput_density)
      (run_family (symmetricFlip r hr hr1) correlatedInput_density) correlationEffect
    linarith

theorem symmetric_optimum_isLeast (r : ℝ) (hr : 0≤r) (hr1 : r≤1) :
    IsLeast {x : ℝ | ∃ F : History 2 2 → Matrix Joint Joint ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧ readoutError
        (fun h => run Qubit Qubit 2 (symmetricKeep r hr hr1) h correlatedInput)
        (fun h => run Qubit Qubit 2 (symmetricFlip r hr hr1) h correlatedInput) F=x}
      (min r (1-r)) := by
  have h := tree_error_isLeast (symmetricKeep r hr hr1) (symmetricFlip r hr hr1)
    correlatedInput_density correlatedInput_density
  rw [symmetric_outputDistance,symmetric_min_formula] at h
  exact h

theorem symmetric_physical_tables (r : ℝ) (hr : 0≤r) (hr1 : r≤1) :
    ((∀ h a, 0≤readoutTable (symmetricReadout r) (fun h => run Qubit Qubit 2 (symmetricKeep r hr hr1) h correlatedInput) h a) ∧
      (∑ h, ∑ a, readoutTable (symmetricReadout r) (fun h => run Qubit Qubit 2 (symmetricKeep r hr hr1) h correlatedInput) h a)=1) ∧
    ((∀ h a, 0≤readoutTable (symmetricReadout r) (fun h => run Qubit Qubit 2 (symmetricFlip r hr hr1) h correlatedInput) h a) ∧
      (∑ h, ∑ a, readoutTable (symmetricReadout r) (fun h => run Qubit Qubit 2 (symmetricFlip r hr hr1) h correlatedInput) h a)=1) ∧
    ((∀ h a, 0≤readoutTable correlationReadout (fun h => run Qubit Qubit 2 (symmetricKeep r hr hr1) h correlatedInput) h a) ∧
      (∑ h, ∑ a, readoutTable correlationReadout (fun h => run Qubit Qubit 2 (symmetricKeep r hr hr1) h correlatedInput) h a)=1) ∧
    ((∀ h a, 0≤readoutTable correlationReadout (fun h => run Qubit Qubit 2 (symmetricFlip r hr hr1) h correlatedInput) h a) ∧
      (∑ h, ∑ a, readoutTable correlationReadout (fun h => run Qubit Qubit 2 (symmetricFlip r hr hr1) h correlatedInput) h a)=1) :=
  ⟨tree_readout_probabilities _ correlatedInput_density _,tree_readout_probabilities _ correlatedInput_density _,
    tree_readout_probabilities _ correlatedInput_density _,tree_readout_probabilities _ correlatedInput_density _⟩

theorem symmetric_old_rule_suboptimal (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (hh : 1/2<r) :
    instrumentError (fun h => run Qubit Qubit 2 (symmetricKeep r hr hr1) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip r hr hr1) h correlatedInput) (symmetricReadout r) <
    instrumentError (fun h => run Qubit Qubit 2 (symmetricKeep r hr hr1) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip r hr hr1) h correlatedInput) correlationReadout := by
  rw [symmetric_reoptimized_error,symmetric_fixed_error,min_eq_right (by linarith)]; linarith

theorem symmetric_half_no_advantage (a : History 2 2 → ℝ)
    (F : History 2 2 → Matrix Joint Joint ℂ) :
    outputDistance Qubit Qubit 2 (symmetricKeep (1/2) (by norm_num) (by norm_num))
      (symmetricFlip (1/2) (by norm_num) (by norm_num)) correlatedInput correlatedInput=0 ∧
    readoutError (fun h => run Qubit Qubit 2 (symmetricKeep (1/2) (by norm_num) (by norm_num)) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip (1/2) (by norm_num) (by norm_num)) h correlatedInput) F=1/2 ∧
    historyError (fun h => run Qubit Qubit 2 (symmetricKeep (1/2) (by norm_num) (by norm_num)) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip (1/2) (by norm_num) (by norm_num)) h correlatedInput) a=1/2 := by
  refine ⟨by rw [symmetric_outputDistance]; norm_num,?_,symmetric_history_error _ _ _ a⟩
  rw [readoutError_eq _ _ _ (run_family (symmetricKeep (1/2) (by norm_num) (by norm_num)) correlatedInput_density).2]
  simp only [symmetric_half_all_complex,sub_self,Matrix.mul_zero,Matrix.trace_zero,Complex.zero_re,Finset.sum_const_zero,sub_zero]

/-- The half-rate equality is evaluated on every complex joint input at the evolution level. -/
theorem symmetric_half_evolution (Z : Matrix Joint Joint ℂ) :
    krausMap (symmetricKeepStep (1/2) (by norm_num) (by norm_num)).evolution Z =
      krausMap (symmetricFlipStep (1/2) (by norm_num) (by norm_num)).evolution Z := by
  change krausMap (mixKraus identityKraus environmentXKraus (1/2)) Z=
    krausMap (mixKraus environmentXKraus identityKraus (1/2)) Z
  rw [mixKraus_action _ _ (by norm_num) (by norm_num),mixKraus_action _ _ (by norm_num) (by norm_num)]
  norm_num; abel
end
end SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness


namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
open Matrix FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open FiniteAdaptiveMixtureSurvival FiniteAdaptiveReadoutDiscrimination FiniteMemoryProcess
open scoped BigOperators ComplexOrder Kronecker
noncomputable section

section LiteralFields
variable {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E] {o l : ℕ}
theorem wrapStep_evolution_action (D : Step S E o) (L : Fin l → Matrix (S × E) (S × E) ℂ)
    (hL : IsKrausChannel L) (J : FiniteInstrument S o) (r : NoiseRates) (Z : Matrix (S × E) (S × E) ℂ) :
    krausMap (wrapStep D L hL J r).evolution Z =
      (1-r.p) • krausMap D.evolution Z + r.p • krausMap L Z :=
  mixKraus_action D.evolution L r.hp r.hp1 Z

theorem wrapStep_instrument_action (D : Step S E o) (L : Fin l → Matrix (S × E) (S × E) ℂ)
    (hL : IsKrausChannel L) (J : FiniteInstrument S o) (r : NoiseRates) (a : Fin o) (Z : Matrix (S × E) (S × E) ℂ) :
    ((wrapStep D L hL J r).instrument.lift E).branch a Z =
      (1-r.q) • (D.instrument.lift E).branch a Z + r.q • (J.lift E).branch a Z :=
  mixInstrument_lift_branch S E o D.instrument J r.q r.hq r.hq1 a Z
end LiteralFields

theorem positive_environment_action_change (D : Step Qubit Qubit 2)
    (hD : krausMap D.evolution (basisState 0 ⊗ₖ basisState 0)=basisState 0 ⊗ₖ basisState 0) :
    krausMap (wrapStep D environmentXKraus environmentX_normalized (FiniteInstrument.prepare 1) positiveNoise).evolution
      (basisState 0 ⊗ₖ basisState 0) ≠ krausMap D.evolution (basisState 0 ⊗ₖ basisState 0) := by
  rw [wrapStep_evolution_action,hD,environmentX_basis]
  intro h
  have he := congrArg (fun M : Matrix Joint Joint ℂ => (M (0,1) (0,1)).re) h
  norm_num [positiveNoise,Matrix.kronecker_apply,basisState,Complex.real_smul] at he

theorem positive_instrument_action_change (D : Step Qubit Qubit 2) (c : ℝ) (hc : c≠0)
    (hD : (D.instrument.lift Qubit).branch 0 (basisState 0 ⊗ₖ basisState 0)=c • (basisState 0 ⊗ₖ basisState 0))
    {l : ℕ} (L : Fin l → Matrix Joint Joint ℂ) (hL : IsKrausChannel L) :
    ((wrapStep D L hL (FiniteInstrument.prepare 1) positiveNoise).instrument.lift Qubit).branch 0
      (basisState 0 ⊗ₖ basisState 0) ≠ (D.instrument.lift Qubit).branch 0 (basisState 0 ⊗ₖ basisState 0) := by
  rw [wrapStep_instrument_action,hD,lift_branch_tensor,prepare_basis]
  intro h
  have he := congrArg (fun M : Matrix Joint Joint ℂ => (M (0,0) (0,0)).re) h
  norm_num [positiveNoise,Matrix.kronecker_apply,basisState,Complex.real_smul] at he
  apply hc
  linarith

theorem positiveReadStep_actions :
    IsDensityOperator (basisState 0 ⊗ₖ basisState 0) ∧
    krausMap (wrapStep readStep environmentXKraus environmentX_normalized (FiniteInstrument.prepare 1) positiveNoise).evolution
      (basisState 0 ⊗ₖ basisState 0) ≠ krausMap readStep.evolution (basisState 0 ⊗ₖ basisState 0) ∧
    ((wrapStep readStep environmentXKraus environmentX_normalized (FiniteInstrument.prepare 1) positiveNoise).instrument.lift Qubit).branch 0
      (basisState 0 ⊗ₖ basisState 0) ≠ (readStep.instrument.lift Qubit).branch 0 (basisState 0 ⊗ₖ basisState 0) := by
  refine ⟨basisJoint_density 0 0,positive_environment_action_change readStep ?_,
    positive_instrument_action_change readStep 1 (by norm_num) ?_ _ _⟩
  · simp [readStep,localStep,krausMap]
  · change (FiniteInstrument.computational.lift Qubit).branch 0 (basisState 0 ⊗ₖ basisState 0)=_
    rw [lift_branch_tensor,computational_basis]; simp

theorem positiveIdentityStep_actions :
    IsDensityOperator (basisState 0 ⊗ₖ basisState 0) ∧
    krausMap (wrapStep identityPrepare environmentXKraus environmentX_normalized (FiniteInstrument.prepare 1) positiveNoise).evolution
      (basisState 0 ⊗ₖ basisState 0) ≠ krausMap identityPrepare.evolution (basisState 0 ⊗ₖ basisState 0) ∧
    ((wrapStep identityPrepare environmentXKraus environmentX_normalized (FiniteInstrument.prepare 1) positiveNoise).instrument.lift Qubit).branch 0
      (basisState 0 ⊗ₖ basisState 0) ≠ (identityPrepare.instrument.lift Qubit).branch 0 (basisState 0 ⊗ₖ basisState 0) := by
  refine ⟨basisJoint_density 0 0,positive_environment_action_change identityPrepare ?_,
    positive_instrument_action_change identityPrepare 1 (by norm_num) ?_ _ _⟩
  · simp [identityPrepare,localStep,krausMap]
  · change ((FiniteInstrument.prepare 0).lift Qubit).branch 0 (basisState 0 ⊗ₖ basisState 0)=_
    rw [lift_branch_tensor,prepare_basis]; simp

theorem positiveFlipStep_actions :
    IsDensityOperator (basisState 0 ⊗ₖ basisState 0) ∧
    krausMap (wrapStep flipPrepare identityKraus identityKraus_normalized (FiniteInstrument.prepare 1) positiveNoise).evolution
      (basisState 0 ⊗ₖ basisState 0) ≠ krausMap flipPrepare.evolution (basisState 0 ⊗ₖ basisState 0) ∧
    ((wrapStep flipPrepare identityKraus identityKraus_normalized (FiniteInstrument.prepare 1) positiveNoise).instrument.lift Qubit).branch 0
      (basisState 0 ⊗ₖ basisState 0) ≠ (flipPrepare.instrument.lift Qubit).branch 0 (basisState 0 ⊗ₖ basisState 0) := by
  refine ⟨basisJoint_density 0 0,?_,positive_instrument_action_change flipPrepare 1 (by norm_num) ?_ _ _⟩
  · rw [wrapStep_evolution_action]
    change (1-positiveNoise.p) • krausMap environmentXKraus (basisState 0 ⊗ₖ basisState 0) +
      positiveNoise.p • krausMap identityKraus (basisState 0 ⊗ₖ basisState 0) ≠ krausMap environmentXKraus (basisState 0 ⊗ₖ basisState 0)
    rw [environmentX_basis]
    simp only [krausMap,identityKraus,Fin.sum_univ_one,Matrix.one_mul,Matrix.conjTranspose_one,Matrix.mul_one]
    intro h
    have he := congrArg (fun M : Matrix Joint Joint ℂ => (M (0,0) (0,0)).re) h
    norm_num [positiveNoise,Matrix.kronecker_apply,basisState,Complex.real_smul] at he
  · change ((FiniteInstrument.prepare 0).lift Qubit).branch 0 (basisState 0 ⊗ₖ basisState 0)=_
    rw [lift_branch_tensor,prepare_basis]; simp

theorem quarterMemory_evolution_zero_basis :
    krausMap quarterMemoryStep.evolution (basisState 0 ⊗ₖ basisState 0)=basisState 0 ⊗ₖ basisState 0 := by
  change krausMap (mixKraus identityKraus swapKraus (1/4)) (basisState 0 ⊗ₖ basisState 0)=_
  rw [mixKraus_action _ _ (by norm_num) (by norm_num)]
  have hs : krausMap swapKraus (basisState 0 ⊗ₖ basisState 0)=basisState 0 ⊗ₖ basisState 0 := swapJoint_basis 0 0
  rw [hs]
  simp only [krausMap,identityKraus,Fin.sum_univ_one,Matrix.one_mul,Matrix.conjTranspose_one,Matrix.mul_one]
  module

theorem quarterMemory_instrument_zero_basis :
    (quarterMemoryStep.instrument.lift Qubit).branch 0 (basisState 0 ⊗ₖ basisState 0)=
      (3/4:ℝ) • (basisState 0 ⊗ₖ basisState 0) := by
  change ((mixInstrument (FiniteInstrument.prepare 0) (FiniteInstrument.prepare 1) (1/4)
    (by norm_num) (by norm_num)).lift Qubit).branch 0 (basisState 0 ⊗ₖ basisState 0)=_
  rw [mixInstrument_lift_branch,lift_branch_tensor,lift_branch_tensor,prepare_basis,prepare_basis]
  norm_num

theorem positiveQuarterStep_actions :
    IsDensityOperator (basisState 0 ⊗ₖ basisState 0) ∧
    krausMap (wrapStep quarterMemoryStep environmentXKraus environmentX_normalized (FiniteInstrument.prepare 1) positiveNoise).evolution
      (basisState 0 ⊗ₖ basisState 0) ≠ krausMap quarterMemoryStep.evolution (basisState 0 ⊗ₖ basisState 0) ∧
    ((wrapStep quarterMemoryStep environmentXKraus environmentX_normalized (FiniteInstrument.prepare 1) positiveNoise).instrument.lift Qubit).branch 0
      (basisState 0 ⊗ₖ basisState 0) ≠ (quarterMemoryStep.instrument.lift Qubit).branch 0 (basisState 0 ⊗ₖ basisState 0) :=
  ⟨basisJoint_density 0 0,positive_environment_action_change quarterMemoryStep quarterMemory_evolution_zero_basis,
    positive_instrument_action_change quarterMemoryStep (3/4) (by norm_num) quarterMemory_instrument_zero_basis _ _⟩
end
end SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness


namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
open Matrix FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open FiniteAdaptiveMixtureSurvival FiniteAdaptiveReadoutDiscrimination FiniteMemoryProcess
open scoped BigOperators ComplexOrder Kronecker
noncomputable section

/-- The symmetric fixture law retains the impossible suffix outcome explicitly. -/
theorem symmetric_fixture_branches (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (h a : Qubit) :
    run Qubit Qubit 2 (symmetricKeep r hr hr1) (h,a,()) correlatedInput =
      (if a=0 then (1-r) • ((1/2:ℂ) • (basisState 0 ⊗ₖ basisState h)) +
        r • ((1/2:ℂ) • (basisState 0 ⊗ₖ basisState (1-h))) else 0) ∧
    run Qubit Qubit 2 (symmetricFlip r hr hr1) (h,a,()) correlatedInput =
      (if a=0 then (1-r) • ((1/2:ℂ) • (basisState 0 ⊗ₖ basisState (1-h))) +
        r • ((1/2:ℂ) • (basisState 0 ⊗ₖ basisState h)) else 0) := by
  rw [symmetricKeep_run,symmetricFlip_run,correlationKeep_run,correlationFlip_run]
  by_cases ha : a=0 <;> simp only [ha,if_true,if_false,smul_zero,zero_add,and_self]

/-- Impossible suffixes remain zero on every complex input, without postselection. -/
theorem symmetric_impossible_all_complex (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (h : Qubit) (Z : Matrix Joint Joint ℂ) :
    run Qubit Qubit 2 (symmetricKeep r hr hr1) (h,1,()) Z=0 ∧
    run Qubit Qubit 2 (symmetricFlip r hr hr1) (h,1,()) Z=0 := by
  constructor <;>
    exact FiniteInstrument.lift_prepare_other Qubit 0 1 (by decide) _

theorem symmetric_boundary_errors :
    outputDistance Qubit Qubit 2 (symmetricKeep 0 le_rfl (by norm_num)) (symmetricFlip 0 le_rfl (by norm_num)) correlatedInput correlatedInput=1 ∧
    instrumentError (fun h => run Qubit Qubit 2 (symmetricKeep 0 le_rfl (by norm_num)) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip 0 le_rfl (by norm_num)) h correlatedInput) correlationReadout=0 ∧
    instrumentError (fun h => run Qubit Qubit 2 (symmetricKeep 0 le_rfl (by norm_num)) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip 0 le_rfl (by norm_num)) h correlatedInput) (symmetricReadout 0)=0 ∧
    instrumentError (fun h => run Qubit Qubit 2 (symmetricKeep (1/2) (by norm_num) (by norm_num)) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip (1/2) (by norm_num) (by norm_num)) h correlatedInput) correlationReadout=1/2 ∧
    instrumentError (fun h => run Qubit Qubit 2 (symmetricKeep (1/2) (by norm_num) (by norm_num)) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip (1/2) (by norm_num) (by norm_num)) h correlatedInput) (symmetricReadout (1/2))=1/2 ∧
    outputDistance Qubit Qubit 2 (symmetricKeep 1 (by norm_num) le_rfl) (symmetricFlip 1 (by norm_num) le_rfl) correlatedInput correlatedInput=1 ∧
    instrumentError (fun h => run Qubit Qubit 2 (symmetricKeep 1 (by norm_num) le_rfl) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip 1 (by norm_num) le_rfl) h correlatedInput) correlationReadout=1 ∧
    instrumentError (fun h => run Qubit Qubit 2 (symmetricKeep 1 (by norm_num) le_rfl) h correlatedInput)
      (fun h => run Qubit Qubit 2 (symmetricFlip 1 (by norm_num) le_rfl) h correlatedInput) (symmetricReadout 1)=0 := by
  simp only [symmetric_outputDistance,symmetric_fixed_error,symmetric_reoptimized_error]
  norm_num

theorem quarterMemory_nominal_errors :
    instrumentError (fun h => run Qubit Qubit 2 quarterMemoryTree h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) memoryReadout=9/32 ∧
    instrumentError (fun h => run Qubit Qubit 2 quarterMemoryTree h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) historyOnlyReadout=3/8 ∧
    (∀ a : History 2 1 → ℝ, (∀ h, a h ∈ Set.Icc (0:ℝ) 1) →
      3/8 ≤ historyError (fun h => run Qubit Qubit 2 quarterMemoryTree h memoryInput)
        (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) a) := by
  refine ⟨memory_quarter_actual_error,quarter_history_actual_error,?_⟩
  intro a ha
  exact quarter_history_isLeast.2 ⟨a,ha,rfl⟩

/-- Zero-gap memory boundaries concern actual physical rules, not an abstract margin. -/
theorem memory_zero_gap_endpoints (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    instrumentError (fun h => run Qubit Qubit 2 (memoryMixedTree 0 q le_rfl (by norm_num) hq hq1) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) historyOnlyReadout -
    instrumentError (fun h => run Qubit Qubit 2 (memoryMixedTree 0 q le_rfl (by norm_num) hq hq1) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) memoryReadout=0 ∧
    instrumentError (fun h => run Qubit Qubit 2 (memoryMixedTree p 1 hp hp1 (by norm_num) le_rfl) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) historyOnlyReadout -
    instrumentError (fun h => run Qubit Qubit 2 (memoryMixedTree p 1 hp hp1 (by norm_num) le_rfl) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) memoryReadout=0 := by
  have h0 := actual_memory_readout_gap 0 q le_rfl (by norm_num) hq hq1
  have h1 := actual_memory_readout_gap p 1 hp hp1 (by norm_num) le_rfl
  exact ⟨by simpa only [instrumentError,zero_mul,zero_div] using h0,
    by simpa only [instrumentError,sub_self,mul_zero,zero_div] using h1⟩

/-- Both zero-error certificates preserve the feedback optimum and its old physical rule. -/
theorem feedback_zero_comparisons (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    (U V : Tree Qubit Qubit 2 (m+1)) {esA esB : List ℝ}
    (cA : PairedErrors Qubit Qubit 2 (idealFeedback m) U esA)
    (cB : PairedErrors Qubit Qubit 2 (noisyFeedback p hp hp1 m) V esB)
    (hA : esA.sum=0) (hB : esB.sum=0) :
    (1-outputDistance Qubit Qubit 2 U V correlatedInput correlatedInput)/2=(1-p)^m/2 ∧
    instrumentError (fun h => run Qubit Qubit 2 U h correlatedInput)
      (fun h => run Qubit Qubit 2 V h correlatedInput) (feedbackReadout p hp hp1 m)=(1-p)^m/2 := by
  have h := feedback_errors_optimum_fixed p hp hp1 m U V correlatedInput_density correlatedInput_density cA cB
  simp only [hA,hB,traceDist_self,zero_add,min_eq_right (by norm_num : (0:ℝ)≤1),zero_div] at h
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h.1 (abs_nonneg _))),
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h.2 (abs_nonneg _)))⟩

theorem feedback_survival_one_exact (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    (U V : Tree Qubit Qubit 2 (m+1)) {rsA rsB : List NoiseRates}
    (cA : PairedMixture Qubit Qubit 2 (idealFeedback m) U rsA)
    (cB : PairedMixture Qubit Qubit 2 (noisyFeedback p hp hp1 m) V rsB)
    (hA : survival rsA=1) (hB : survival rsB=1) :
    (1-outputDistance Qubit Qubit 2 U V correlatedInput correlatedInput)/2=(1-p)^m/2 ∧
    instrumentError (fun h => run Qubit Qubit 2 U h correlatedInput)
      (fun h => run Qubit Qubit 2 V h correlatedInput) (feedbackReadout p hp hp1 m)=(1-p)^m/2 := by
  have ho := (feedback_mixture_optimum p hp hp1 m U V correlatedInput_density correlatedInput_density cA cB).2.2
  have hf := feedback_mixture_fixed p hp hp1 m U V correlatedInput_density correlatedInput_density cA cB
  simp only [hA,hB,traceDist_self,mul_zero,zero_add,sub_self,zero_div] at ho hf
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm ho (abs_nonneg _))),
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hf (abs_nonneg _)))⟩

theorem feedback_survival_zero_guard (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    (U V : Tree Qubit Qubit 2 (m+1)) {Y Z : Matrix Joint Joint ℂ}
    (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z) {rsA rsB : List NoiseRates}
    (cA : PairedMixture Qubit Qubit 2 (idealFeedback m) U rsA)
    (cB : PairedMixture Qubit Qubit 2 (noisyFeedback p hp hp1 m) V rsB)
    (hA : survival rsA=0) (hB : survival rsB=0) :
    |(1-outputDistance Qubit Qubit 2 U V Y Z)/2-(1-p)^m/2|≤1 ∧
    |instrumentError (fun h => run Qubit Qubit 2 U h Y)
      (fun h => run Qubit Qubit 2 V h Z) (feedbackReadout p hp hp1 m)-(1-p)^m/2|≤1 := by
  have ho := (feedback_mixture_optimum p hp hp1 m U V hY hZ cA cB).2.2
  have hf := feedback_mixture_fixed p hp hp1 m U V hY hZ cA cB
  simpa only [hA,hB,zero_mul,zero_add,sub_zero,show (1+1:ℝ)/2=1 by norm_num] using And.intro ho hf
end
end SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness


namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
open Matrix FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open FiniteAdaptiveMixtureSurvival FiniteAdaptiveReadoutDiscrimination FiniteMemoryProcess
open scoped BigOperators ComplexOrder Kronecker
noncomputable section

/-- Every complex branch of any perturbed tree uses the original fixed E measurement. -/
theorem correlation_transported_fixed_relabel (U : Tree Qubit Qubit 2 2)
    (Z : Matrix Joint Joint ℂ) (k : History 2 2) (b : Qubit) :
    readoutTable correlationReadout (fun h => run Qubit Qubit 2 U h Z) k b =
      fixedEnvironmentReadout.weight (if k.1=0 then b else 1-b) (run Qubit Qubit 2 U k Z) :=
  correlationReadout_fixed_relabel k b _

/-- Reoptimization exchanges only the hypothesis labels of that same physical rule. -/
theorem symmetricReadout_relabel (r : ℝ) (k : History 2 2) (b : Qubit) (Z : Matrix Joint Joint ℂ) :
    (symmetricReadout r k).weight b Z =
      (correlationReadout k).weight (if r≤1/2 then b else 1-b) Z := by
  have hb : b=0 ∨ b=1 := by fin_cases b <;> norm_num
  by_cases h : r≤1/2
  · rw [if_pos h]
    rcases hb with rfl | rfl
    · rw [(symmetricReadout_weights r k Z).1,correlationReadout_weight_zero]
      simp only [symmetricEffect,if_pos h]
    · rw [(symmetricReadout_weights r k Z).2,correlationReadout_weight_one]
      simp only [symmetricEffect,if_pos h]
  · rw [if_neg h]
    rcases hb with rfl | rfl
    · simp only [sub_zero]
      rw [(symmetricReadout_weights r k Z).1,correlationReadout_weight_one]
      simp only [symmetricEffect,if_neg h]
    · simp only [sub_self]
      rw [(symmetricReadout_weights r k Z).2,correlationReadout_weight_zero]
      simp only [symmetricEffect,if_neg h,sub_sub_cancel]

section NormalizedWrapper
variable {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E] {o l : ℕ}
theorem wrapStep_branch_normalized (D : Step S E o) (L : Fin l → Matrix (S × E) (S × E) ℂ)
    (hL : IsKrausChannel L) (J : FiniteInstrument S o) (r : NoiseRates) (Z : Matrix (S × E) (S × E) ℂ) :
    (∑ a, ((wrapStep D L hL J r).branch S E o a Z).trace)=Z.trace :=
  Step.sum_trace S E o _ Z

theorem wrapStep_branch_positive (D : Step S E o) (L : Fin l → Matrix (S × E) (S × E) ℂ)
    (hL : IsKrausChannel L) (J : FiniteInstrument S o) (r : NoiseRates) (a : Fin o)
    {Z : Matrix (S × E) (S × E) ℂ} (hZ : Z.PosSemidef) :
    ((wrapStep D L hL J r).branch S E o a Z).PosSemidef :=
  Step.branch_posSemidef S E o _ a hZ
end NormalizedWrapper

/-- Actual separate comparison budgets also support arbitrary non-mixture perturbations. -/
theorem correlation_budget_advantage (U V : Tree Qubit Qubit 2 2)
    {Y Z : Matrix Joint Joint ℂ} (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z)
    (βA βB : ℝ)
    (hA : outputDistance Qubit Qubit 2 correlationKeep U correlatedInput Y ≤ βA)
    (hB : outputDistance Qubit Qubit 2 correlationFlip V correlatedInput Z ≤ βB)
    (a : History 2 2 → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0:ℝ) 1) :
    1/2-βA-βB ≤ historyError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) a -
      instrumentError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) correlationReadout := by
  have h := readout_advantage_conservative (run_family correlationKeep correlatedInput_density)
    (run_family correlationFlip correlatedInput_density) (run_family U hY) (run_family V hZ)
    correlationEffect (fun h => isBinaryPOVM_of_projection (correlationEffect_hermitian h)
      (correlationEffect_idem h)) (1/2) (fun a ha => le_of_eq (correlation_history_only a ha).symm) a ha
  rw [correlation_effect_error_zero,sub_zero,tree_branchDistance,tree_branchDistance] at h
  rw [correlationReadout_realizes]; linarith

theorem memory_budget_advantage (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (U V : Tree Qubit Qubit 2 1) {Y Z : Matrix Joint Joint ℂ}
    (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z) (βA βB : ℝ)
    (hA : outputDistance Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) U memoryInput Y ≤ βA)
    (hB : outputDistance Qubit Qubit 2 memoryIdentityTree V memoryInput Z ≤ βB)
    (a : History 2 1 → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0:ℝ) 1) :
    p*(1-q)/2-βA-βB ≤ historyError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) a -
      instrumentError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) memoryReadout := by
  have h := readout_advantage_conservative
    (run_family (memoryMixedTree p q hp hp1 hq hq1) memoryInput_density)
    (run_family memoryIdentityTree memoryInput_density) (run_family U hY) (run_family V hZ)
    memoryEffect (fun h => isBinaryPOVM_of_projection (memoryEffect_hermitian h)
      (memoryEffect_idem h)) ((1-q)/2) (fun a ha => memory_history_lower p q hp hp1 hq hq1 a ha) a ha
  rw [memoryReadout_optimal_effect,tree_branchDistance,tree_branchDistance] at h
  rw [memoryReadout_realizes]; nlinarith

theorem correlation_budget_strict (U V : Tree Qubit Qubit 2 2)
    {Y Z : Matrix Joint Joint ℂ} (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z)
    (βA βB : ℝ)
    (hA : outputDistance Qubit Qubit 2 correlationKeep U correlatedInput Y ≤ βA)
    (hB : outputDistance Qubit Qubit 2 correlationFlip V correlatedInput Z ≤ βB)
    (hsmall : βA+βB<1/2) (a : History 2 2 → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0:ℝ) 1) :
    instrumentError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) correlationReadout <
      historyError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) a := by
  have h := correlation_budget_advantage U V hY hZ βA βB hA hB a ha; linarith

theorem memory_budget_strict (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (U V : Tree Qubit Qubit 2 1) {Y Z : Matrix Joint Joint ℂ}
    (hY : IsDensityOperator Y) (hZ : IsDensityOperator Z) (βA βB : ℝ)
    (hA : outputDistance Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) U memoryInput Y ≤ βA)
    (hB : outputDistance Qubit Qubit 2 memoryIdentityTree V memoryInput Z ≤ βB)
    (hsmall : βA+βB<p*(1-q)/2) (a : History 2 1 → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0:ℝ) 1) :
    instrumentError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) memoryReadout <
      historyError (fun h => run Qubit Qubit 2 U h Y) (fun h => run Qubit Qubit 2 V h Z) a := by
  have h := memory_budget_advantage p q hp hp1 hq hq1 U V hY hZ βA βB hA hB a ha; linarith
end
end SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness

namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
open Matrix FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open FiniteAdaptiveMixtureSurvival FiniteAdaptiveReadoutDiscrimination FiniteMemoryProcess
open scoped BigOperators ComplexOrder Kronecker
noncomputable section

/-- Nominal feedback optimization is obtained from the existing all-effect theorem. -/
theorem feedback_nominal_optimum_physical (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    IsLeast {x : ℝ | ∃ F : History 2 (m+1) → Matrix Joint Joint ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧ readoutError
        (fun h => run Qubit Qubit 2 (idealFeedback m) h correlatedInput)
        (fun h => run Qubit Qubit 2 (noisyFeedback p hp hp1 m) h correlatedInput) F=x}
      ((1-p)^m/2) ∧
    instrumentError (fun h => run Qubit Qubit 2 (idealFeedback m) h correlatedInput)
      (fun h => run Qubit Qubit 2 (noisyFeedback p hp hp1 m) h correlatedInput)
      (feedbackReadout p hp hp1 m)=(1-p)^m/2 :=
  ⟨feedback_error_isLeast p hp hp1 m,feedbackReadout_attains p hp hp1 m⟩
end
end SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
