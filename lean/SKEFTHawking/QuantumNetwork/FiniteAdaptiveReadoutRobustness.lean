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
