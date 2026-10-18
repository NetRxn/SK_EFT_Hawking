import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic
import SKEFTHawking.QuantumNetwork.FiniteMemoryPartialInteraction

/-! Fixed-sample concentration and statistical exclusion of a common system channel.
The sampling law describes independent complete trials within each history; it imposes
no independence between histories. Physical preparation and calibration remain hypotheses. -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

namespace SKEFTHawking.QuantumNetwork.BinaryMemorySampling

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Independent bounded observations with a common mean. Binary IID trials are a special
case; concentration requires only these weaker assumptions. Sample size is fixed. -/
structure BoundedTrials (μ : Measure Ω) (n : ℕ) (q : ℝ) where
  positive : 0 < n
  observation : Fin n → Ω → ℝ
  measurable : ∀ i, Measurable (observation i)
  bounded : ∀ i, ∀ᵐ ω ∂μ, observation i ω ∈ Set.Icc (0 : ℝ) 1
  independent : iIndepFun observation μ
  mean : ∀ i, ∫ ω, observation i ω ∂μ = q

/-- Empirical proportion (or average for general bounded observations). -/
noncomputable def BoundedTrials.empirical {n : ℕ} {q : ℝ}
    (T : BoundedTrials μ n q) (ω : Ω) : ℝ :=
  (∑ i, T.observation i ω) / n

omit [IsProbabilityMeasure μ] in
theorem BoundedTrials.empirical_measurable {n : ℕ} {q : ℝ}
    (T : BoundedTrials μ n q) : Measurable T.empirical := by
  exact (Finset.measurable_sum _ (fun i _ => T.measurable i)).div_const _

private theorem centered_subgaussian {n : ℕ} {q : ℝ}
    (T : BoundedTrials μ n q) (i : Fin n) :
    HasSubgaussianMGF (fun ω => T.observation i ω - q) (1 / 4) μ := by
  have h := hasSubgaussianMGF_of_mem_Icc (T.measurable i).aemeasurable (T.bounded i)
  norm_num [T.mean i] at h ⊢
  exact h

private theorem sum_subgaussian {n : ℕ} {q : ℝ}
    (T : BoundedTrials μ n q) :
    HasSubgaussianMGF (fun ω => ∑ i, (T.observation i ω - q)) (n / 4) μ := by
  have hi := T.independent.comp (fun (_ : Fin n) (x : ℝ) => x - q)
    (fun _ => measurable_id.sub_const q)
  have h := HasSubgaussianMGF.sum_of_iIndepFun hi
    (s := Finset.univ) (c := fun _ => (1 / 4 : ℝ≥0))
    (fun i _ => centered_subgaussian T i)
  simpa [div_eq_mul_inv] using h

/-- Hoeffding's two-sided bound derived from bounded independent observations. -/
theorem BoundedTrials.empirical_tail {n : ℕ} {q ρ : ℝ}
    (T : BoundedTrials μ n q) (hρ : 0 < ρ) :
    μ.real {ω | ρ < |T.empirical ω - q|} ≤ 2 * Real.exp (-2 * n * ρ ^ 2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast T.positive
  have hs := sum_subgaussian T
  have hp := hs.measure_ge_le (ε := n * ρ) (by positivity)
  have hm := hs.neg.measure_ge_le (ε := n * ρ) (by positivity)
  have he : -(n * ρ) ^ 2 / (2 * ((n / 4 : ℝ≥0) : ℝ)) = -2 * n * ρ ^ 2 := by
    push_cast
    field_simp
    ring
  rw [he] at hp hm
  have hsum (ω : Ω) : (∑ i, (T.observation i ω - q)) = n * (T.empirical ω - q) := by
    simp only [BoundedTrials.empirical, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hsub : {ω | ρ < |T.empirical ω - q|} ⊆
      {ω | n * ρ ≤ ∑ i, (T.observation i ω - q)} ∪
      {ω | n * ρ ≤ -(∑ i, (T.observation i ω - q))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, hsum]
    change ρ < |T.empirical ω - q| at hω
    rcases lt_abs.mp hω with h | h
    · left
      nlinarith [mul_lt_mul_of_pos_left h hn]
    · right
      nlinarith [mul_lt_mul_of_pos_left h hn]
  have hu := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  exact hu.trans (by simpa [Pi.neg_apply, two_mul] using add_le_add hp hm)

/-- Exact dyadic certificate, justified by `2 ≤ exp 1`. -/
theorem exp_tail_dyadic {x : ℝ} (j : ℕ) (hj : (j : ℝ) ≤ x) :
    2 * Real.exp (-x) ≤ 2 / (2 : ℝ) ^ j := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hp : (2 : ℝ) ^ j ≤ Real.exp (j : ℝ) := by
    calc
      (2 : ℝ) ^ j ≤ (Real.exp 1) ^ j := pow_le_pow_left₀ (by norm_num) he j
      _ = Real.exp (j : ℝ) := by rw [← Real.exp_nat_mul]; simp
  have hx := hp.trans (Real.exp_le_exp.mpr hj)
  have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ j) hx
  simpa [Real.exp_neg, div_eq_mul_inv] using mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)

theorem BoundedTrials.empirical_tail_dyadic {n : ℕ} {q ρ : ℝ}
    (T : BoundedTrials μ n q) (hρ : 0 < ρ) (j : ℕ)
    (hj : (j : ℝ) ≤ 2 * n * ρ ^ 2) :
    μ.real {ω | ρ < |T.empirical ω - q|} ≤ 2 / (2 : ℝ) ^ j := by
  exact T.empirical_tail hρ |>.trans (by
    simpa only [neg_mul] using exp_tail_dyadic j hj)

/-- Total simultaneous failure bound, capped at one. -/
noncomputable def failureBound (j₀ j₁ : ℕ) : ℝ :=
  min 1 (2 / (2 : ℝ) ^ j₀ + 2 / (2 : ℝ) ^ j₁)

/-- No independence between history groups is used. -/
theorem joint_failure_dyadic {n₀ n₁ : ℕ} {q₀ q₁ ρ₀ ρ₁ : ℝ}
    (T₀ : BoundedTrials μ n₀ q₀) (T₁ : BoundedTrials μ n₁ q₁)
    (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (j₀ j₁ : ℕ)
    (hj₀ : (j₀ : ℝ) ≤ 2 * n₀ * ρ₀ ^ 2) (hj₁ : (j₁ : ℝ) ≤ 2 * n₁ * ρ₁ ^ 2) :
    μ.real {ω | ρ₀ < |T₀.empirical ω - q₀| ∨ ρ₁ < |T₁.empirical ω - q₁|} ≤
      failureBound j₀ j₁ := by
  apply le_min measureReal_le_one
  exact (measureReal_union_le _ _).trans
    (add_le_add (T₀.empirical_tail_dyadic hρ₀ j₀ hj₀)
      (T₁.empirical_tail_dyadic hρ₁ j₁ hj₁))

/-- Simultaneous coverage is a conclusion of the trial model. -/
theorem joint_coverage_dyadic {n₀ n₁ : ℕ} {q₀ q₁ ρ₀ ρ₁ : ℝ}
    (T₀ : BoundedTrials μ n₀ q₀) (T₁ : BoundedTrials μ n₁ q₁)
    (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (j₀ j₁ : ℕ)
    (hj₀ : (j₀ : ℝ) ≤ 2 * n₀ * ρ₀ ^ 2) (hj₁ : (j₁ : ℝ) ≤ 2 * n₁ * ρ₁ ^ 2) :
    1 - failureBound j₀ j₁ ≤
      μ.real {ω | |T₀.empirical ω - q₀| ≤ ρ₀ ∧ |T₁.empirical ω - q₁| ≤ ρ₁} := by
  have hm : MeasurableSet {ω | ρ₀ < |T₀.empirical ω - q₀| ∨
      ρ₁ < |T₁.empirical ω - q₁|} :=
    (measurableSet_lt measurable_const (T₀.empirical_measurable.sub_const q₀).abs).union
      (measurableSet_lt measurable_const (T₁.empirical_measurable.sub_const q₁).abs)
  have hc := measureReal_compl (μ := μ) hm
  have hb := joint_failure_dyadic T₀ T₁ hρ₀ hρ₁ j₀ j₁ hj₀ hj₁
  simp only [Set.compl_setOf, not_or, not_lt, probReal_univ] at hc
  linarith

/-- Strict, predeclared empirical rejection event. -/
def rejection {n₀ n₁ : ℕ} {q₀ q₁ : ℝ}
    (T₀ : BoundedTrials μ n₀ q₀) (T₁ : BoundedTrials μ n₁ q₁)
    (B ρ₀ ρ₁ : ℝ) : Set Ω :=
  {ω | B + ρ₀ + ρ₁ < |T₀.empirical ω - T₁.empirical ω|}

private theorem abs_gap_transfer {a b c d u v B : ℝ}
    (hu : |a - c| ≤ u) (hv : |b - d| ≤ v) (hB : |c - d| ≤ B) :
    |a - b| ≤ B + u + v := by
  rcases abs_le.mp hu with ⟨hu₁, hu₂⟩
  rcases abs_le.mp hv with ⟨hv₁, hv₂⟩
  rcases abs_le.mp hB with ⟨hB₁, hB₂⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A null gap bound and fixed trials give a false-positive guarantee. -/
theorem false_positive {n₀ n₁ : ℕ} {q₀ q₁ ρ₀ ρ₁ B : ℝ}
    (T₀ : BoundedTrials μ n₀ q₀) (T₁ : BoundedTrials μ n₁ q₁)
    (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (j₀ j₁ : ℕ)
    (hj₀ : (j₀ : ℝ) ≤ 2 * n₀ * ρ₀ ^ 2) (hj₁ : (j₁ : ℝ) ≤ 2 * n₁ * ρ₁ ^ 2)
    (hB : |q₀ - q₁| ≤ B) :
    μ.real (rejection T₀ T₁ B ρ₀ ρ₁) ≤ failureBound j₀ j₁ := by
  apply le_trans (measureReal_mono (μ := μ) (show rejection T₀ T₁ B ρ₀ ρ₁ ⊆
    {ω | ρ₀ < |T₀.empirical ω - q₀| ∨ ρ₁ < |T₁.empirical ω - q₁|} from ?_))
    (joint_failure_dyadic T₀ T₁ hρ₀ hρ₁ j₀ j₁ hj₀ hj₁)
  intro ω hω
  change B + ρ₀ + ρ₁ < |T₀.empirical ω - T₁.empirical ω| at hω
  by_contra h
  simp only [Set.mem_setOf_eq, not_or, not_lt] at h
  exact (not_lt_of_ge (abs_gap_transfer h.1 h.2 hB)) hω

/-- Common normalized channel and common effect, with valid preparation and bias budgets.
The budget premises imply nonnegativity; any calibration failure is additional to this bound. -/
theorem common_channel_false_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k n₀ n₁ : ℕ} {q₀ q₁ ρ₀ ρ₁ ε₀ ε₁ δ₀ δ₁ : ℝ}
    (T₀ : BoundedTrials μ n₀ q₀) (T₁ : BoundedTrials μ n₁ q₁)
    (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (j₀ j₁ : ℕ)
    (hj₀ : (j₀ : ℝ) ≤ 2 * n₀ * ρ₀ ^ 2) (hj₁ : (j₁ : ℝ) ≤ 2 * n₁ * ρ₁ ^ 2)
    {σ₀ σ₁ τ E : Matrix ι ι ℂ} {K : Fin k → Matrix ι ι ℂ}
    (hσ₀ : IsDensityOperator σ₀) (hσ₁ : IsDensityOperator σ₁)
    (hτ : IsDensityOperator τ) (hK : IsKrausChannel K) (hE : IsBinaryPOVM E)
    (hε₀ : traceDist σ₀ τ ≤ ε₀) (hε₁ : traceDist σ₁ τ ≤ ε₁)
    (hδ₀ : |q₀ - binaryOutcomeProb E (krausMap K σ₀)| ≤ δ₀)
    (hδ₁ : |q₁ - binaryOutcomeProb E (krausMap K σ₁)| ≤ δ₁) :
    μ.real (rejection T₀ T₁ (min 1 (ε₀ + ε₁) + δ₀ + δ₁) ρ₀ ρ₁) ≤
      failureBound j₀ j₁ := by
  apply false_positive T₀ T₁ hρ₀ hρ₁ j₀ j₁ hj₀ hj₁
  exact abs_gap_transfer hδ₀ hδ₁
    (binary_memoryless_separation_le hσ₀ hσ₁ hτ hK hE hε₀ hε₁)

/-- Confidence gating is fixed independently of outcomes. -/
def certifiedRejection {n₀ n₁ : ℕ} {q₀ q₁ : ℝ}
    (T₀ : BoundedTrials μ n₀ q₀) (T₁ : BoundedTrials μ n₁ q₁)
    (B ρ₀ ρ₁ α : ℝ) (j₀ j₁ : ℕ) : Set Ω :=
  {ω | 0 < α ∧ α < 1 ∧ failureBound j₀ j₁ ≤ α ∧ ω ∈ rejection T₀ T₁ B ρ₀ ρ₁}

theorem certified_false_positive {n₀ n₁ : ℕ} {q₀ q₁ ρ₀ ρ₁ B α : ℝ}
    (T₀ : BoundedTrials μ n₀ q₀) (T₁ : BoundedTrials μ n₁ q₁)
    (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (j₀ j₁ : ℕ)
    (hj₀ : (j₀ : ℝ) ≤ 2 * n₀ * ρ₀ ^ 2) (hj₁ : (j₁ : ℝ) ≤ 2 * n₁ * ρ₁ ^ 2)
    (hα : 0 < α) (hB : |q₀ - q₁| ≤ B) :
    μ.real (certifiedRejection T₀ T₁ B ρ₀ ρ₁ α j₀ j₁) ≤ α := by
  by_cases hc : failureBound j₀ j₁ ≤ α
  · exact (measureReal_mono (μ := μ) (fun _ h => h.2.2.2)).trans
      ((false_positive T₀ T₁ hρ₀ hρ₁ j₀ j₁ hj₀ hj₁ hB).trans hc)
  · have he : certifiedRejection T₀ T₁ B ρ₀ ρ₁ α j₀ j₁ = ∅ := by
      ext ω
      simp [certifiedRejection, hc]
    rw [he, measureReal_empty]
    exact hα.le

/-- A gap exceeding the null allowance by twice the radii gives quantified power. -/
theorem power {n₀ n₁ : ℕ} {q₀ q₁ ρ₀ ρ₁ B : ℝ}
    (T₀ : BoundedTrials μ n₀ q₀) (T₁ : BoundedTrials μ n₁ q₁)
    (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (j₀ j₁ : ℕ)
    (hj₀ : (j₀ : ℝ) ≤ 2 * n₀ * ρ₀ ^ 2) (hj₁ : (j₁ : ℝ) ≤ 2 * n₁ * ρ₁ ^ 2)
    (hgap : B + 2 * (ρ₀ + ρ₁) < |q₀ - q₁|) :
    1 - failureBound j₀ j₁ ≤ μ.real (rejection T₀ T₁ B ρ₀ ρ₁) := by
  apply (joint_coverage_dyadic T₀ T₁ hρ₀ hρ₁ j₀ j₁ hj₀ hj₁).trans
  refine measureReal_mono (μ := μ) ?_ (measure_ne_top _ _)
  intro ω hω
  change B + ρ₀ + ρ₁ < |T₀.empirical ω - T₁.empirical ω|
  have h := abs_gap_transfer
    (by simpa [abs_sub_comm] using hω.1)
    (by simpa [abs_sub_comm] using hω.2)
    (le_refl |T₀.empirical ω - T₁.empirical ω|)
  linarith

open FiniteMemoryProcess Matrix

/-- Actual Born probability of the accepted retained-environment trajectory. -/
noncomputable def partialMean (b : Qubit) : ℝ :=
  systemProbability 1 (partialRetainedRun (1 / 2) (1 / 4)
    (Matrix.kronecker (basisState b) (basisState 0)))

/-- Allowance from the actual two post-reset system marginals. -/
noncomputable def partialBudget : ℝ :=
  min 1 (traceDist (systemMarginal (partialPostReset (1 / 2) (1 / 4)
    (Matrix.kronecker (basisState 0) (basisState 0)))) (binaryDiagonalState 0) +
    traceDist (systemMarginal (partialPostReset (1 / 2) (1 / 4)
    (Matrix.kronecker (basisState 1) (basisState 0)))) (binaryDiagonalState 0))

theorem partial_parameters :
    partialMean 0 = 0 ∧ partialMean 1 = 5 / 16 ∧ partialBudget = 1 / 8 := by
  have h₀ := partialRetained_probability (1 / 2) (1 / 4) 0
  have h₁ := partial_interior_example
  have hε₀ := partialPostReset_traceDist (t := 1 / 2) (p := 1 / 4)
    (by norm_num) (by norm_num) 0
  dsimp [partialMean, partialBudget]
  norm_num at h₀ hε₀
  rw [h₀, h₁.1, hε₀, h₁.2.2]
  norm_num

/-- The accepted physical model is detected with probability at least 63/64.
The means and reset allowance are the actual trajectories, not free numeric parameters. -/
theorem partial_model_power
    (T₀ : BoundedTrials μ 4096 (partialMean 0))
    (T₁ : BoundedTrials μ 4096 (partialMean 1)) :
    (63 / 64 : ℝ) ≤ μ.real (rejection T₀ T₁ partialBudget (1 / 32) (1 / 32)) := by
  have h := power T₀ T₁ (ρ₀ := 1 / 32) (ρ₁ := 1 / 32)
    (by norm_num) (by norm_num) 8 8 (by norm_num) (by norm_num)
    (B := partialBudget) (by rw [partial_parameters.1, partial_parameters.2.1,
      partial_parameters.2.2]; norm_num)
  norm_num [failureBound] at h
  exact h

/-- The same fixed test has false-positive probability at most 1/64 under its null. -/
theorem partial_test_false_positive {q₀ q₁ : ℝ}
    (T₀ : BoundedTrials μ 4096 q₀) (T₁ : BoundedTrials μ 4096 q₁)
    (hnull : |q₀ - q₁| ≤ partialBudget) :
    μ.real (rejection T₀ T₁ partialBudget (1 / 32) (1 / 32)) ≤ (1 / 64 : ℝ) := by
  have h := false_positive T₀ T₁ (ρ₀ := 1 / 32) (ρ₁ := 1 / 32)
    (by norm_num) (by norm_num) 8 8 (by norm_num) (by norm_num) hnull
  norm_num [failureBound] at h
  exact h

/-- The concrete power statement also satisfies the requested confidence gate. -/
theorem partial_model_certified_power
    (T₀ : BoundedTrials μ 4096 (partialMean 0))
    (T₁ : BoundedTrials μ 4096 (partialMean 1)) :
    (63 / 64 : ℝ) ≤ μ.real (certifiedRejection T₀ T₁ partialBudget
      (1 / 32) (1 / 32) (1 / 64) 8 8) := by
  have he : certifiedRejection T₀ T₁ partialBudget (1 / 32) (1 / 32) (1 / 64) 8 8 =
      rejection T₀ T₁ partialBudget (1 / 32) (1 / 32) := by
    ext ω
    norm_num [certifiedRejection, failureBound]
  rw [he]
  exact partial_model_power T₀ T₁

/-- A finite product of genuine Bernoulli trials. -/
noncomputable def bernoulliLaw (n : ℕ) (p : unitInterval) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ => bernoulliMeasure true false p)

instance (n : ℕ) (p : unitInterval) : IsProbabilityMeasure (bernoulliLaw n p) := by
  unfold bernoulliLaw
  infer_instance

private def boolValue (b : Bool) : ℝ := if b then 1 else 0

/-- Explicit binary IID construction, proving compatibility of the sampling hypotheses. -/
noncomputable def bernoulliTrials (n : ℕ) (hn : 0 < n) (p : unitInterval) :
    BoundedTrials (bernoulliLaw n p) n (p : ℝ) where
  positive := hn
  observation i ω := boolValue (ω i)
  measurable i := (Measurable.of_discrete (f := boolValue)).comp (measurable_pi_apply i)
  bounded i := Eventually.of_forall (fun ω => by cases h : ω i <;> norm_num [boolValue, h])
  independent := iIndepFun_pi (fun _ => Measurable.of_discrete.aemeasurable)
  mean i := by
    have hm := measurePreserving_eval (fun _ : Fin n => bernoulliMeasure true false p) i
    have hi := integral_map (μ := bernoulliLaw n p) hm.measurable.aemeasurable
      (Measurable.of_discrete.aestronglyMeasurable (f := boolValue))
    change MeasurePreserving (Function.eval i) (bernoulliLaw n p) _ at hm
    rw [hm.map_eq] at hi
    rw [← hi, integral_bernoulliMeasure]
    simp [boolValue]

private noncomputable def zeroTrials (n : ℕ) (hn : 0 < n) (p : unitInterval) :
    BoundedTrials (bernoulliLaw n p) n 0 where
  positive := hn
  observation _ _ := 0
  measurable _ := measurable_const
  bounded _ := Eventually.of_forall (fun _ => by norm_num)
  independent := iIndepFun_pi (X := fun _ (_ : Bool) => (0 : ℝ))
    (fun _ => measurable_const.aemeasurable)
  mean _ := by simp

/-- A non-vacuous binary law realizes both actual means and the certified power bound.
History zero is the degenerate Bernoulli(0); history one consists of IID Bernoulli(5/16). -/
theorem partial_binary_witness :
    ∃ ν : Measure (Fin 4096 → Bool), IsProbabilityMeasure ν ∧
      ∃ (T₀ : BoundedTrials ν 4096 (partialMean 0))
        (T₁ : BoundedTrials ν 4096 (partialMean 1)),
        (∀ i ω, T₀.observation i ω = 0 ∨ T₀.observation i ω = 1) ∧
        (∀ i ω, T₁.observation i ω = 0 ∨ T₁.observation i ω = 1) ∧
        (63 / 64 : ℝ) ≤ ν.real (certifiedRejection T₀ T₁ partialBudget
          (1 / 32) (1 / 32) (1 / 64) 8 8) := by
  let p : unitInterval := ⟨5 / 16, by norm_num⟩
  let ν := bernoulliLaw 4096 p
  let T₀ : BoundedTrials ν 4096 (partialMean 0) :=
    { zeroTrials 4096 (by norm_num) p with
      mean := fun i => by rw [partial_parameters.1]; exact (zeroTrials 4096 (by norm_num) p).mean i }
  let T₁ : BoundedTrials ν 4096 (partialMean 1) :=
    { bernoulliTrials 4096 (by norm_num) p with
      mean := fun i => by rw [partial_parameters.2.1]; exact (bernoulliTrials 4096 (by norm_num) p).mean i }
  refine ⟨ν, inferInstance, T₀, T₁, ?_, ?_, partial_model_certified_power T₀ T₁⟩
  · intro i ω
    left
    simp [T₀, zeroTrials]
  · intro i ω
    change boolValue (ω i) = 0 ∨ boolValue (ω i) = 1
    cases ω i <;> simp [boolValue]

end SKEFTHawking.QuantumNetwork.BinaryMemorySampling
