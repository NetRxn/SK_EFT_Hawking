import SKEFTHawking.QuantumNetwork.BinaryMemorySampling

/-! Fixed-protocol calibration of diagonal reset states and stable binary readout.
Calibration and main groups may be dependent; independence is required within each group.
The comparison budget is random and is justified on simultaneous coverage. -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace SKEFTHawking.QuantumNetwork.BinaryMemoryCalibration
open BinaryMemorySampling

/-- Stable classical readout confusion law. -/
def readout (a b x : ℝ) : ℝ := a * (1 - x) + (1 - b) * x

theorem readout_mem {a b x : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    readout a b x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact add_nonneg (mul_nonneg ha.1 (sub_nonneg.mpr hx.2))
      (mul_nonneg (sub_nonneg.mpr hb.2) hx.1)
  · dsimp [readout]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hx.2), mul_nonneg hb.1 hx.1]

theorem readout_bias {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |readout a b x - x| ≤ max a b := by
  apply abs_le.mpr
  constructor
  · dsimp [readout]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2), mul_nonneg hb (sub_nonneg.mpr hx.2), le_max_right a b]
  · dsimp [readout]
    nlinarith [mul_nonneg hb hx.1, mul_nonneg ha hx.1, le_max_left a b]

theorem population_le_readout {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : x ≤ readout a b x + b := by
  dsimp [readout]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2), mul_nonneg hb (sub_nonneg.mpr hx.2)]

noncomputable def upper (f s : ℝ) : ℝ := min 1 (f + s)
noncomputable def resetUpper (f s ub : ℝ) : ℝ := min 1 (f + s + ub)
noncomputable def budget (f s : Fin 6 → ℝ) : ℝ :=
  min 1 (resetUpper (f 2) (s 2) (upper (f 1) (s 1)) +
    resetUpper (f 3) (s 3) (upper (f 1) (s 1))) +
    2 * max (upper (f 0) (s 0)) (upper (f 1) (s 1))

theorem upper_valid {x f s : ℝ} (hx : x ≤ 1) (hc : |f - x| ≤ s) :
    x ≤ upper f s := le_min hx (by have := (abs_le.mp hc).1; linarith)

theorem reset_upper_valid {a b x f s ub : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hcov : |f - readout a b x| ≤ s) (hub : b ≤ ub) :
    traceDist (binaryDiagonalState x) (binaryDiagonalState 0) ≤ resetUpper f s ub := by
  rw [binaryDiagonalState_traceDist, sub_zero, abs_of_nonneg hx.1]
  apply le_min hx.2
  have := population_le_readout ha hb hx
  have := (abs_le.mp hcov).1
  linarith

private theorem gap_transfer {a b c d u v B : ℝ}
    (hu : |a-c| ≤ u) (hv : |b-d| ≤ v) (hB : |c-d| ≤ B) :
    |a-b| ≤ B+u+v := by
  rcases abs_le.mp hu with ⟨hu₁,hu₂⟩
  rcases abs_le.mp hv with ⟨hv₁,hv₂⟩
  rcases abs_le.mp hB with ⟨hB₁,hB₂⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The six groups share one probability space; no cross-group independence premise. -/
noncomputable def totalFailure (j : Fin 6 → ℕ) : ℝ :=
  min 1 (∑ i, 2 / (2 : ℝ) ^ j i)

def coverage {n : Fin 6 → ℕ} {q : Fin 6 → ℝ}
    (T : ∀ i, BoundedTrials μ (n i) (q i)) (s : Fin 6 → ℝ) : Set Ω :=
  {ω | ∀ i, |(T i).empirical ω - q i| ≤ s i}

theorem six_failure {n : Fin 6 → ℕ} {q s : Fin 6 → ℝ}
    (T : ∀ i, BoundedTrials μ (n i) (q i)) (hs : ∀ i, 0 < s i)
    (j : Fin 6 → ℕ) (hj : ∀ i, (j i : ℝ) ≤ 2 * n i * (s i)^2) :
    μ.real (coverage T s)ᶜ ≤ totalFailure j := by
  apply le_min measureReal_le_one
  have he : (coverage T s)ᶜ = ⋃ i, {ω | s i < |(T i).empirical ω - q i|} := by
    ext ω
    simp [coverage]
  rw [he]
  exact (measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum (fun i _ => (T i).empirical_tail_dyadic (hs i) (j i) (hj i)))

theorem six_coverage {n : Fin 6 → ℕ} {q s : Fin 6 → ℝ}
    (T : ∀ i, BoundedTrials μ (n i) (q i)) (hs : ∀ i, 0 < s i)
    (j : Fin 6 → ℕ) (hj : ∀ i, (j i : ℝ) ≤ 2 * n i * (s i)^2) :
    1-totalFailure j ≤ μ.real (coverage T s) := by
  have hm : MeasurableSet (coverage T s) :=
    by simpa only [coverage, Set.setOf_forall] using
      MeasurableSet.iInter (fun i => measurableSet_le ((T i).empirical_measurable.sub_const (q i)).abs (measurable_const (a := s i)))
  have hc := measureReal_compl (μ := μ) hm
  have hb := six_failure T hs j hj
  simp only [probReal_univ] at hc
  linarith

/-- This event uses the calibration observations themselves in its threshold. -/
def calibratedRejection {n : Fin 6 → ℕ} {q : Fin 6 → ℝ}
    (T : ∀ i, BoundedTrials μ (n i) (q i)) (s : Fin 6 → ℝ) : Set Ω :=
  {ω | budget (fun i => (T i).empirical ω) s + s 4 + s 5 <
    |(T 4).empirical ω - (T 5).empirical ω|}

theorem random_budget_false_positive {n : Fin 6 → ℕ} {q s : Fin 6 → ℝ}
    (T : ∀ i, BoundedTrials μ (n i) (q i)) (hs : ∀ i, 0 < s i)
    (j : Fin 6 → ℕ) (hj : ∀ i, (j i : ℝ) ≤ 2*n i*(s i)^2)
    (hnull : ∀ ω ∈ coverage T s, |q 4-q 5| ≤ budget (fun i => (T i).empirical ω) s) :
    μ.real (calibratedRejection T s) ≤ totalFailure j := by
  apply (measureReal_mono (μ := μ) (show calibratedRejection T s ⊆ (coverage T s)ᶜ from ?_)).trans
    (six_failure T hs j hj)
  intro ω hr hc
  exact (not_lt_of_ge (gap_transfer (hc 4) (hc 5) (hnull ω hc))) hr

theorem random_budget_power {n : Fin 6 → ℕ} {q s : Fin 6 → ℝ}
    (T : ∀ i, BoundedTrials μ (n i) (q i)) (hs : ∀ i, 0 < s i)
    (j : Fin 6 → ℕ) (hj : ∀ i, (j i : ℝ) ≤ 2*n i*(s i)^2) {B : ℝ}
    (hB : ∀ ω ∈ coverage T s, budget (fun i => (T i).empirical ω) s ≤ B)
    (hgap : B+2*(s 4+s 5) < |q 4-q 5|) :
    1-totalFailure j ≤ μ.real (calibratedRejection T s) := by
  apply (six_coverage T hs j hj).trans
  apply measureReal_mono (μ := μ) _ (measure_ne_top _ _)
  intro ω hc
  have hg := gap_transfer (by simpa [abs_sub_comm] using hc 4)
    (by simpa [abs_sub_comm] using hc 5) (le_refl |(T 4).empirical ω-(T 5).empirical ω|)
  have hb := hB ω hc
  change budget (fun i => (T i).empirical ω) s + s 4+s 5 < _
  linarith


/-- The six means under a common physical continuation. Group one records errors on
the trusted one standard, so its mean is the false-negative rate `b`, not `1-b`. -/
noncomputable def nullMeans {k : ℕ} (a b r₀ r₁ : ℝ)
    (K : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (E : Matrix (Fin 2) (Fin 2) ℂ) : Fin 6 → ℝ :=
  ![a, b, readout a b r₀, readout a b r₁,
    readout a b (binaryOutcomeProb E (krausMap K (binaryDiagonalState r₀))),
    readout a b (binaryOutcomeProb E (krausMap K (binaryDiagonalState r₁)))]

theorem physical_budget {k : ℕ} {a b r₀ r₁ : ℝ}
    {K : Fin k → Matrix (Fin 2) (Fin 2) ℂ} {E : Matrix (Fin 2) (Fin 2) ℂ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hr₀ : r₀ ∈ Set.Icc (0 : ℝ) 1) (hr₁ : r₁ ∈ Set.Icc (0 : ℝ) 1)
    (hK : IsKrausChannel K) (hE : IsBinaryPOVM E) (f s : Fin 6 → ℝ)
    (hc : ∀ i, |f i-nullMeans a b r₀ r₁ K E i| ≤ s i) :
    |nullMeans a b r₀ r₁ K E 4-nullMeans a b r₀ r₁ K E 5| ≤ budget f s := by
  have hA : a ≤ upper (f 0) (s 0) := upper_valid ha.2 (by simpa [nullMeans] using hc 0)
  have hB : b ≤ upper (f 1) (s 1) := upper_valid hb.2 (by simpa [nullMeans] using hc 1)
  have he₀ := reset_upper_valid ha.1 hb.1 hr₀ (by simpa [nullMeans] using hc 2) hB
  have he₁ := reset_upper_valid ha.1 hb.1 hr₁ (by simpa [nullMeans] using hc 3) hB
  have hphys := binary_memoryless_separation_le
    (binaryDiagonalState_density hr₀) (binaryDiagonalState_density hr₁)
    (binaryDiagonalState_density (r := 0) (by norm_num)) hK hE he₀ he₁
  have hd := max_le_max hA hB
  have hd₀ := (readout_bias ha.1 hb.1
    (binaryOutcomeProb_mem_Icc hE (krausMap_isDensityOperator hK (binaryDiagonalState_density hr₀)))).trans hd
  have hd₁ := (readout_bias ha.1 hb.1
    (binaryOutcomeProb_mem_Icc hE (krausMap_isDensityOperator hK (binaryDiagonalState_density hr₁)))).trans hd
  simpa [nullMeans, budget, two_mul, add_assoc] using gap_transfer hd₀ hd₁ hphys

/-- Calibration and main sampling failure are accounted for together, for the actual common channel.
No independence between calibration and main observations is required. -/
theorem calibrated_common_channel_false_positive {k : ℕ} {a b r₀ r₁ : ℝ}
    {K : Fin k → Matrix (Fin 2) (Fin 2) ℂ} {E : Matrix (Fin 2) (Fin 2) ℂ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hr₀ : r₀ ∈ Set.Icc (0 : ℝ) 1) (hr₁ : r₁ ∈ Set.Icc (0 : ℝ) 1)
    (hK : IsKrausChannel K) (hE : IsBinaryPOVM E)
    {n : Fin 6 → ℕ} {s : Fin 6 → ℝ}
    (T : ∀ i, BoundedTrials μ (n i) (nullMeans a b r₀ r₁ K E i))
    (hs : ∀ i, 0 < s i) (j : Fin 6 → ℕ)
    (hj : ∀ i, (j i : ℝ) ≤ 2*n i*(s i)^2) :
    μ.real (calibratedRejection T s) ≤ totalFailure j :=
  random_budget_false_positive T hs j hj
    (fun _ hc => physical_budget ha hb hr₀ hr₁ hK hE _ s hc)

def certifiedRejection {n : Fin 6 → ℕ} {q : Fin 6 → ℝ}
    (T : ∀ i, BoundedTrials μ (n i) (q i)) (s : Fin 6 → ℝ)
    (j : Fin 6 → ℕ) (α : ℝ) : Set Ω :=
  {ω | 0 < α ∧ α < 1 ∧ totalFailure j ≤ α ∧ ω ∈ calibratedRejection T s}

theorem certified_false_positive {n : Fin 6 → ℕ} {q s : Fin 6 → ℝ}
    (T : ∀ i, BoundedTrials μ (n i) (q i)) (hs : ∀ i, 0 < s i)
    (j : Fin 6 → ℕ) (hj : ∀ i, (j i : ℝ) ≤ 2*n i*(s i)^2)
    {α : ℝ} (hα : 0 < α)
    (hnull : ∀ ω ∈ coverage T s, |q 4-q 5| ≤ budget (fun i => (T i).empirical ω) s) :
    μ.real (certifiedRejection T s j α) ≤ α := by
  by_cases hjα : totalFailure j ≤ α
  · exact (measureReal_mono (μ := μ) (fun _ h => h.2.2.2)).trans
      ((random_budget_false_positive T hs j hj hnull).trans hjα)
  · have he : certifiedRejection T s j α = ∅ := by ext ω; simp [certifiedRejection, hjα]
    rw [he, measureReal_empty]
    exact hα.le


open FiniteMemoryProcess

/-- Population of the actual post-reset marginal. Diagonality is established by the trajectory. -/
noncomputable def modelReset (b : Qubit) : ℝ :=
  binaryOutcomeProb binaryOneEffect (systemMarginal (partialPostReset (1/2) (1/4)
    (Matrix.kronecker (basisState b) (basisState 0))))

theorem model_reset_parameters : modelReset 0 = 0 ∧ modelReset 1 = 1/8 := by
  simp [modelReset, partialPostReset_marginal, binaryOneEffect_probability]
  norm_num

noncomputable def modelMeans : Fin 6 → ℝ :=
  ![1/256, 1/256, readout (1/256) (1/256) (modelReset 0),
    readout (1/256) (1/256) (modelReset 1),
    readout (1/256) (1/256) (partialMean 0), readout (1/256) (1/256) (partialMean 1)]

def modelSizes : Fin 6 → ℕ := ![81920,81920,81920,81920,20480,20480]
noncomputable def modelRadii : Fin 6 → ℝ := ![1/128,1/128,1/128,1/128,1/64,1/64]

theorem model_means_exact : modelMeans = ![1/256,1/256,1/256,131/1024,1/256,643/2048] := by
  unfold modelMeans
  rw [model_reset_parameters.1, model_reset_parameters.2, partial_parameters.1, partial_parameters.2.1]
  norm_num [readout]

theorem model_design : (∀ i, 0 < modelSizes i) ∧ (∀ i, 0 < modelRadii i) ∧
    (∀ i, (10 : ℝ) ≤ 2*modelSizes i*(modelRadii i)^2) ∧
    totalFailure (fun _ => 10) = 3/256 := by
  constructor
  · intro i; fin_cases i <;> norm_num [modelSizes]
  constructor
  · intro i; fin_cases i <;> norm_num [modelRadii, Matrix.cons_val_succ]
  constructor
  · intro i; fin_cases i <;> norm_num [modelSizes, modelRadii]
  · norm_num [totalFailure]

/-- Uniform threshold control on coverage, not just a favorable observed count vector. -/
theorem model_budget_on_coverage (f : Fin 6 → ℝ)
    (hc : ∀ i, |f i-modelMeans i| ≤ modelRadii i) :
    budget f modelRadii ≤ 247/1024 := by
  have h0 := (abs_le.mp (hc 0)).2
  have h1 := (abs_le.mp (hc 1)).2
  have h2 := (abs_le.mp (hc 2)).2
  have h3 := (abs_le.mp (hc 3)).2
  rw [model_means_exact] at h0 h1 h2 h3
  norm_num [modelRadii, Matrix.cons_val_succ] at h0 h1 h2 h3
  change f 2 ≤ 1/128+1/256 at h2
  change f 3 ≤ 1/128+131/1024 at h3
  have ha : upper (f 0) (modelRadii 0) ≤ 5/256 := by
    apply (min_le_right _ _).trans
    change f 0 + 1/128 ≤ 5/256
    linarith
  have hb : upper (f 1) (modelRadii 1) ≤ 5/256 := by
    apply (min_le_right _ _).trans
    change f 1 + 1/128 ≤ 5/256
    linarith
  have hb' : upper (f 1) (1/128) ≤ 5/256 := hb
  have he0 : resetUpper (f 2) (modelRadii 2) (upper (f 1) (modelRadii 1)) ≤ 5/128 := by
    apply (min_le_right _ _).trans
    change f 2 + 1/128 + upper (f 1) (1/128) ≤ 5/128
    linarith
  have he1 : resetUpper (f 3) (modelRadii 3) (upper (f 1) (modelRadii 1)) ≤ 167/1024 := by
    apply (min_le_right _ _).trans
    change f 3 + 1/128 + upper (f 1) (1/128) ≤ 167/1024
    linarith
  have hd := max_le ha hb
  have he := min_le_right 1 (resetUpper (f 2) (modelRadii 2) (upper (f 1) (modelRadii 1)) +
    resetUpper (f 3) (modelRadii 3) (upper (f 1) (modelRadii 1)))
  dsimp [budget]
  linarith

/-- A sampled, noisy-readout partial-interaction model is detected with probability at least 253/256. -/
theorem model_power (T : ∀ i, BoundedTrials μ (modelSizes i) (modelMeans i)) :
    (253/256 : ℝ) ≤ μ.real (calibratedRejection T modelRadii) := by
  have h := random_budget_power T model_design.2.1 (fun _ => 10) model_design.2.2.1
    (fun ω hc => model_budget_on_coverage (fun i => (T i).empirical ω) hc)
    (by rw [model_means_exact]; change (247/1024 : ℝ)+2*(1/64+1/64) < |1/256-643/2048|; norm_num)
  rw [model_design.2.2.2] at h
  norm_num at h ⊢
  exact h

theorem model_certified_power (T : ∀ i, BoundedTrials μ (modelSizes i) (modelMeans i)) :
    (253/256 : ℝ) ≤ μ.real (certifiedRejection T modelRadii (fun _ => 10) (1/64)) := by
  have he : certifiedRejection T modelRadii (fun _ => 10) (1/64) = calibratedRejection T modelRadii := by
    ext ω
    simp only [certifiedRejection, Set.mem_setOf_eq, model_design.2.2.2]
    norm_num
  rw [he]
  exact model_power T

/-- Explicit finite Bernoulli sample space for all six groups. -/
noncomputable def sixLaw (n : Fin 6 → ℕ) (p : Fin 6 → unitInterval) :
    Measure ((Σ i, Fin (n i)) → Bool) :=
  Measure.pi (fun z => bernoulliMeasure true false (p z.1))

instance (n : Fin 6 → ℕ) (p : Fin 6 → unitInterval) : IsProbabilityMeasure (sixLaw n p) := by
  unfold sixLaw
  infer_instance

private def bit (b : Bool) : ℝ := if b then 1 else 0

noncomputable def sixTrials (n : Fin 6 → ℕ) (hn : ∀ i, 0 < n i)
    (p : Fin 6 → unitInterval) (i : Fin 6) : BoundedTrials (sixLaw n p) (n i) (p i : ℝ) where
  positive := hn i
  observation j ω := bit (ω ⟨i,j⟩)
  measurable j := (Measurable.of_discrete (f := bit)).comp (measurable_pi_apply (⟨i,j⟩ : Σ i, Fin (n i)))
  bounded j := Eventually.of_forall (fun ω => by cases h : ω ⟨i,j⟩ <;> norm_num [bit,h])
  independent := (iIndepFun_pi (μ := fun z : Σ i, Fin (n i) => bernoulliMeasure true false (p z.1))
    (fun _ => Measurable.of_discrete.aemeasurable (f := bit))).precomp
      (show Function.Injective (fun j : Fin (n i) => (⟨i,j⟩ : Σ i, Fin (n i))) from fun _ _ h => by cases h; rfl)
  mean j := by
    have hm := measurePreserving_eval (fun z : Σ i, Fin (n i) => bernoulliMeasure true false (p z.1)) ⟨i,j⟩
    have hi := integral_map (μ := sixLaw n p) hm.measurable.aemeasurable
      (Measurable.of_discrete.aestronglyMeasurable (f := bit))
    change MeasurePreserving (Function.eval ⟨i,j⟩) (sixLaw n p) _ at hm
    rw [hm.map_eq] at hi
    rw [← hi, integral_bernoulliMeasure]
    simp [bit]

theorem model_binary_witness :
    ∃ ν : Measure ((Σ i, Fin (modelSizes i)) → Bool), IsProbabilityMeasure ν ∧
      ∃ T : ∀ i, BoundedTrials ν (modelSizes i) (modelMeans i),
        (∀ i j ω, (T i).observation j ω = 0 ∨ (T i).observation j ω = 1) ∧
        (253/256 : ℝ) ≤ ν.real (certifiedRejection T modelRadii (fun _ => 10) (1/64)) := by
  have hp : ∀ i, modelMeans i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    rw [model_means_exact]
    fin_cases i <;> norm_num
  let p : Fin 6 → unitInterval := fun i => ⟨modelMeans i, hp i⟩
  let T := sixTrials modelSizes model_design.1 p
  refine ⟨sixLaw modelSizes p, inferInstance, T, ?_, model_certified_power T⟩
  intro i j ω
  change bit (ω ⟨i,j⟩) = 0 ∨ bit (ω ⟨i,j⟩) = 1
  cases ω ⟨i,j⟩ <;> simp [bit]


/-- End-to-end confidence-gated guarantee with budgets inferred from the same six groups. -/
theorem certified_common_channel_false_positive {k : ℕ} {a b r₀ r₁ : ℝ}
    {K : Fin k → Matrix (Fin 2) (Fin 2) ℂ} {E : Matrix (Fin 2) (Fin 2) ℂ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hr₀ : r₀ ∈ Set.Icc (0 : ℝ) 1) (hr₁ : r₁ ∈ Set.Icc (0 : ℝ) 1)
    (hK : IsKrausChannel K) (hE : IsBinaryPOVM E)
    {n : Fin 6 → ℕ} {s : Fin 6 → ℝ}
    (T : ∀ i, BoundedTrials μ (n i) (nullMeans a b r₀ r₁ K E i))
    (hs : ∀ i, 0 < s i) (j : Fin 6 → ℕ)
    (hj : ∀ i, (j i : ℝ) ≤ 2*n i*(s i)^2) {α : ℝ} (hα : 0 < α) :
    μ.real (certifiedRejection T s j α) ≤ α :=
  certified_false_positive T hs j hj hα
    (fun _ hc => physical_budget ha hb hr₀ hr₁ hK hE _ s hc)

/-- The concrete power margin remains positive at the worst simultaneous-coverage threshold. -/
theorem model_power_margin :
    |modelMeans 4-modelMeans 5|-(247/1024+2*(modelRadii 4+modelRadii 5)) = 13/2048 := by
  rw [model_means_exact]
  change |(1/256 : ℝ)-643/2048|-(247/1024+2*(1/64+1/64)) = 13/2048
  norm_num

end SKEFTHawking.QuantumNetwork.BinaryMemoryCalibration
