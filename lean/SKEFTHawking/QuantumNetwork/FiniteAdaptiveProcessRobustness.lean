import SKEFTHawking.QuantumNetwork.FiniteInterventionProcess
import SKEFTHawking.QuantumNetwork.FiniteMemoryCoarseGraining
import SKEFTHawking.QuantumNetwork.LogNegativity

/-!
# Robustness of finite adaptive intervention processes

A backward binary effect is constructed from the actual Kraus evolution and lifted
local instrument at each node. It represents every score in `[0,1]`, including
history events. The full outcome-law total variation is bounded by initial trace
distance with constant one, independent of depth and outcome count.

Both compared inputs use the same complete realized strategy. Its later nodes may
depend on recorded outcomes; impossible branches remain unnormalized zero matrices.
The collision-model suffix budget therefore controls arbitrary adaptive continuation,
and an actual SWAP/measurement/feedback strategy attains it. There is no postselected,
sampling, runtime or physical-clock identification claim.
-/
namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveProcessRobustness
open Matrix FiniteInterventionProcess
open scoped BigOperators ComplexOrder Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def dual {k : ℕ} (K : Fin k → Matrix ι ι ℂ)
    (B : Matrix ι ι ℂ) : Matrix ι ι ℂ := ∑ j, (K j)ᴴ * B * K j

omit [DecidableEq ι] in
theorem dual_pos {k : ℕ} (K : Fin k → Matrix ι ι ℂ)
    {B : Matrix ι ι ℂ} (hB : B.PosSemidef) : (dual K B).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j _
  exact hB.conjTranspose_mul_mul_same _

omit [DecidableEq ι] in
theorem dual_trace {k : ℕ} (K : Fin k → Matrix ι ι ℂ)
    (B X : Matrix ι ι ℂ) : (dual K B * X).trace = (B * krausMap K X).trace := by
  simp only [dual, krausMap, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.trace_mul_comm ((K j)ᴴ * B * K j) X]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle']
  simp only [Matrix.mul_assoc]

theorem dual_one {k : ℕ} (K : Fin k → Matrix ι ι ℂ) (hK : IsKrausChannel K) :
    dual K 1 = 1 := by simpa [dual, IsKrausChannel] using hK

omit [DecidableEq ι] in
theorem dual_sub {k : ℕ} (K : Fin k → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ) :
    dual K (B-C) = dual K B-dual K C := by
  simp [dual, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

variable {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E] {o : ℕ}

/-- Reverse the actual forward order: lifted intervention, then joint evolution. -/
noncomputable def nodeEffect (D : Step S E o)
    (B : Fin o → Matrix (S × E) (S × E) ℂ) : Matrix (S × E) (S × E) ℂ :=
  dual D.evolution (∑ a, dual ((D.instrument.lift E).operators a) (B a))

theorem nodeEffect_pos (D : Step S E o) (B : Fin o → Matrix (S × E) (S × E) ℂ)
    (hB : ∀ a, (B a).PosSemidef) : (nodeEffect D B).PosSemidef := by
  apply dual_pos
  apply Matrix.posSemidef_sum
  intro a _
  exact dual_pos _ (hB a)

theorem nodeEffect_one (D : Step S E o) : nodeEffect D (fun _ => 1) = 1 := by
  unfold nodeEffect
  have h : (∑ a, dual ((D.instrument.lift E).operators a) 1) = 1 := by
    simpa [dual] using (D.instrument.lift E).normalized
  rw [h, dual_one _ D.normalized]

theorem nodeEffect_complement (D : Step S E o)
    (B : Fin o → Matrix (S × E) (S × E) ℂ) :
    nodeEffect D (fun a => 1-B a) = 1-nodeEffect D B := by
  unfold nodeEffect
  simp_rw [dual_sub, Finset.sum_sub_distrib, dual_sub]
  rw [show dual D.evolution (∑ a, dual ((D.instrument.lift E).operators a) 1) = 1
    from nodeEffect_one D]

theorem nodeEffect_binary (D : Step S E o)
    (B : Fin o → Matrix (S × E) (S × E) ℂ) (hB : ∀ a, IsBinaryPOVM (B a)) :
    IsBinaryPOVM (nodeEffect D B) := by
  refine ⟨nodeEffect_pos D B (fun a => (hB a).1), ?_⟩
  rw [← nodeEffect_complement]
  exact nodeEffect_pos D _ (fun a => (hB a).2)

theorem nodeEffect_trace (D : Step S E o)
    (B : Fin o → Matrix (S × E) (S × E) ℂ) (X : Matrix (S × E) (S × E) ℂ) :
    (nodeEffect D B * X).trace = ∑ a, (B a * D.branch S E o a X).trace := by
  rw [nodeEffect, dual_trace]
  simp only [Finset.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact dual_trace _ _ _

noncomputable def effect : {n : ℕ} → Tree S E o n →
    (History o n → ℝ) → Matrix (S × E) (S × E) ℂ
  | 0, .done, f => (f () : ℂ) • 1
  | _+1, .node D F, f => nodeEffect D (fun a => effect (F a) (fun h => f (a,h)))

theorem effect_binary {n : ℕ} (T : Tree S E o n) (f : History o n → ℝ)
    (hf : ∀ h, f h ∈ Set.Icc (0 : ℝ) 1) : IsBinaryPOVM (effect T f) := by
  induction T with
  | done =>
    change IsBinaryPOVM ((f () : ℂ) • (1 : Matrix (S × E) (S × E) ℂ))
    constructor
    · exact Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ (f () : ℂ) by exact_mod_cast (hf ()).1)
    · have he : (1 : Matrix (S × E) (S × E) ℂ) - (f () : ℂ) • 1 =
          ((1-f () : ℝ) : ℂ) • 1 := by simp [Complex.ofReal_sub, sub_smul]
      rw [he]
      exact Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ ((1-f () : ℝ) : ℂ) by
        exact_mod_cast sub_nonneg.mpr (hf ()).2)
  | node D F ih => exact nodeEffect_binary D _ (fun a => ih a _ (fun h => hf (a,h)))

noncomputable def score {n : ℕ} (T : Tree S E o n) (f : History o n → ℝ)
    (X : Matrix (S × E) (S × E) ℂ) : ℝ := ∑ h, f h * weight S E o T h X

theorem effect_trace {n : ℕ} (T : Tree S E o n) (f : History o n → ℝ)
    (X : Matrix (S × E) (S × E) ℂ) : (effect T f * X).trace.re = score T f X := by
  induction T generalizing X with
  | done => simp [effect, score, History, weight, run]
  | node D F ih =>
    change (nodeEffect D (fun a => effect (F a) (fun h => f (a,h))) * X).trace.re = _
    rw [nodeEffect_trace, Complex.re_sum]
    simp_rw [ih]
    change (∑ a, ∑ h, f (a,h) * weight S E o (F a) h (D.branch S E o a X)) =
      ∑ h : Fin o × History o _, f h * weight S E o (.node D F) h X
    rw [Fintype.sum_prod_type]
    rfl

/-- Finite normalized laws reduce total variation to their positive-difference event. -/
theorem totalVariation_positive_event {H : Type*} [Fintype H] (p q : H → ℝ)
    (hs : ∑ h, p h = ∑ h, q h) :
    (∑ h, |p h-q h|)/2 = ∑ h, if 0 ≤ p h-q h then p h-q h else 0 := by
  classical
  have hz : ∑ h, (p h-q h) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
  have he : ∀ h, |p h-q h| = 2*(if 0 ≤ p h-q h then p h-q h else 0)-(p h-q h) := by
    intro h
    by_cases hd : 0 ≤ p h-q h
    · rw [if_pos hd, abs_of_nonneg hd]; ring
    · rw [if_neg hd, abs_of_neg (lt_of_not_ge hd)]; ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz]
  ring

/-- The actual two-level feedback example gives its diagonal event probability. -/
theorem feedback_event_score :
    score feedbackExample (fun h => if h.1 = 1 ∧ h.2.1 = 1 then 1 else 0) feedbackInput = 1/2 := by
  classical
  unfold score
  change (∑ h : Fin 2 × (Fin 2 × Unit), _) = _
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique]
  norm_num
  exact feedback_example_weights 1 1

/-- A common density spectator preserves trace distance, in arbitrary finite dimensions. -/
theorem traceDist_tensor_left {A : Matrix S S ℂ} (hA : IsDensityOperator A)
    (X Y : Matrix E E ℂ) : traceDist (A ⊗ₖ X) (A ⊗ₖ Y) = traceDist X Y := by
  have he : A ⊗ₖ X - A ⊗ₖ Y = A ⊗ₖ (X-Y) := by
    ext i j
    simp [mul_sub]
  unfold traceDist
  rw [he, traceNorm_kronecker, traceNorm_posSemidef hA.1, hA.2, Complex.one_re, one_mul]

/-- The common density factor can also be placed on the right. -/
theorem traceDist_tensor_right {A : Matrix E E ℂ} (hA : IsDensityOperator A)
    (X Y : Matrix S S ℂ) : traceDist (X ⊗ₖ A) (Y ⊗ₖ A) = traceDist X Y := by
  have he : X ⊗ₖ A - Y ⊗ₖ A = (X-Y) ⊗ₖ A := by
    ext i j
    simp [sub_mul]
  unfold traceDist
  rw [he, traceNorm_kronecker, traceNorm_posSemidef hA.1, hA.2, Complex.one_re, mul_one]

theorem effect_one {n : ℕ} (T : Tree S E o n) : effect T (fun _ => 1) = 1 := by
  induction T with
  | done => simp [effect]
  | node D F ih => simpa only [effect, ih] using nodeEffect_one D

theorem effect_complement {n : ℕ} (T : Tree S E o n) (f : History o n → ℝ) :
    effect T (fun h => 1-f h) = 1-effect T f := by
  induction T with
  | done => simp [effect, Complex.ofReal_sub, sub_smul]
  | node D F ih => simpa only [effect, ih] using
      nodeEffect_complement D (fun a => effect (F a) (fun h => f (a,h)))

theorem effect_zero {n : ℕ} (T : Tree S E o n) : effect T (fun _ => 0) = 0 := by
  simpa [effect_one] using effect_complement T (fun _ => 1)

/-- Arbitrary bounded scores under one common realized adaptive strategy. -/
theorem score_difference_bound {n : ℕ} (T : Tree S E o n) (f : History o n → ℝ)
    (hf : ∀ h, f h ∈ Set.Icc (0 : ℝ) 1)
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    |score T f X-score T f Y| ≤ traceDist X Y := by
  rw [← effect_trace, ← effect_trace]
  exact abs_binaryOutcomeProb_sub_le_traceDist (effect_binary T f hf) hX hY

noncomputable def eventProbability {n : ℕ} (T : Tree S E o n) (A : Finset (History o n))
    (X : Matrix (S × E) (S × E) ℂ) : ℝ := ∑ h ∈ A, weight S E o T h X

theorem eventProbability_score {n : ℕ} [DecidableEq (History o n)] (T : Tree S E o n) (A : Finset (History o n))
    (X : Matrix (S × E) (S × E) ℂ) :
    eventProbability T A X = score T (fun h => if h ∈ A then 1 else 0) X := by
  classical
  simp [eventProbability, score, Finset.sum_ite_mem]

theorem event_difference_bound {n : ℕ} (T : Tree S E o n) (A : Finset (History o n))
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    |eventProbability T A X-eventProbability T A Y| ≤ traceDist X Y := by
  classical
  rw [eventProbability_score, eventProbability_score]
  exact score_difference_bound T _ (fun h => by split <;> norm_num) hX hY

noncomputable def totalVariation {n : ℕ} (T : Tree S E o n)
    (X Y : Matrix (S × E) (S × E) ℂ) : ℝ :=
  (∑ h, |weight S E o T h X-weight S E o T h Y|)/2

/-- Full history error has no factor depending on depth or number of outcomes. -/
theorem totalVariation_bound {n : ℕ} (T : Tree S E o n)
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    totalVariation T X Y ≤ traceDist X Y := by
  classical
  let f : History o n → ℝ := fun h => if 0 ≤ weight S E o T h X-weight S E o T h Y then 1 else 0
  have hf : ∀ h, f h ∈ Set.Icc (0 : ℝ) 1 := fun h => by dsimp [f]; split <;> norm_num
  have he : totalVariation T X Y = score T f X-score T f Y := by
    unfold totalVariation
    rw [totalVariation_positive_event _ _ ((normalized_weights S E o T hX).2.trans
      (normalized_weights S E o T hY).2.symm)]
    unfold score
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro h _
    dsimp [f]
    split <;> simp_all
  rw [he]
  exact (le_abs_self _).trans (score_difference_bound T f hf hX hY)

open FiniteMemoryProcess

/-- Tensor inputs in the collision consumer are actual normalized density operators. -/
theorem basis_tensor_density (b : Qubit) {X : Matrix Qubit Qubit ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (basisState b ⊗ₖ X) := by
  exact ⟨(basisState_density b).1.kronecker hX.1, by
    rw [Matrix.trace_kronecker, (basisState_density b).2, hX.2, one_mul]⟩

/-- The entire adaptive continuation law inherits the collision suffix budget. -/
theorem adaptive_suffix_bound {n : ℕ} (T : Tree Qubit Qubit o n)
    (b : Qubit) (pre suffix : List FiniteMemoryCoarseGraining.Step)
    {ρ τ : Matrix Qubit Qubit ℂ} (hρ : IsDensityOperator ρ) (hτ : IsDensityOperator τ) :
    totalVariation T (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run (pre++suffix) ρ)
      (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run suffix τ) ≤
      FiniteMemoryCoarseGraining.retentionProduct suffix := by
  have h := totalVariation_bound T
    (basis_tensor_density b (FiniteMemoryCoarseGraining.run_density (pre++suffix) hρ))
    (basis_tensor_density b (FiniteMemoryCoarseGraining.run_density suffix hτ))
  rw [traceDist_tensor_left (basisState_density b)] at h
  exact h.trans (FiniteMemoryCoarseGraining.suffix_prediction_bound pre suffix hρ hτ)


noncomputable def swapMeasure : FiniteInterventionProcess.Step Qubit Qubit 2 where
  count := 1
  evolution := swapKraus
  normalized := swapKraus_normalized
  instrument := FiniteInstrument.computational

theorem swapMeasure_trace (a : Qubit) (X : Matrix Joint Joint ℂ) :
    (swapMeasure.branch Qubit Qubit 2 a X).trace.re = systemProbability a (swapJoint X) := by
  change (((FiniteInstrument.computational.lift Qubit).branch a (swapJoint X)).trace.re) = _
  fin_cases a <;>
    simp [FiniteInstrument.branch, FiniteInstrument.lift, FiniteInstrument.computational,
      krausMap, systemProbability, basisState, Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

theorem swap_feedback_one (b : Qubit) (X : Matrix Qubit Qubit ℂ) :
    weight Qubit Qubit 2 (feedback Qubit swapMeasure) (1,1,()) (basisState b ⊗ₖ X) =
      binaryOutcomeProb binaryOneEffect X := by
  rw [feedback_weights]
  simp only [ite_true]
  rw [swapMeasure_trace, FiniteMemoryCoarseGraining.finalSwap_readout]

noncomputable def halfCollision : FiniteMemoryCoarseGraining.Step := ⟨1/2, 0, by norm_num⟩

/-- Two actual collisions retain precisely one quarter of the basis-one population. -/
theorem two_half_collisions (c : Qubit) :
    FiniteMemoryCoarseGraining.run [halfCollision, halfCollision] (basisState c) =
      if c=0 then basisState 0 else (3/4 : ℂ) • basisState 0 + (1/4 : ℂ) • basisState 1 := by
  simp only [FiniteMemoryCoarseGraining.run]
  rw [FiniteMemoryCoarseGraining.collision_on_density _ _
    (FiniteMemoryCoarseGraining.collision_density halfCollision.admissible _ (basisState_density c)),
    FiniteMemoryCoarseGraining.collision_on_density _ _ (basisState_density c)]
  fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [halfCollision, basisState]

/-- The same realized feedback strategy, with reachable and impossible histories retained. -/
theorem swap_feedback_quarter_table (b c a d : Qubit) :
    weight Qubit Qubit 2 (feedback Qubit swapMeasure) (a,d,())
      (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run [halfCollision,halfCollision] (basisState c)) =
    if d=a then (if c=0 then (if a=0 then 1 else 0) else (if a=0 then 3/4 else 1/4)) else 0 := by
  rw [feedback_weights, swapMeasure_trace, two_half_collisions]
  rw [FiniteMemoryCoarseGraining.swap_tensor]
  fin_cases b <;> fin_cases c <;> fin_cases a <;> fin_cases d <;>
    norm_num [systemProbability, basisState, Matrix.trace, Matrix.mul_apply,
      Matrix.kronecker_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

theorem swap_feedback_quarter_tv (b : Qubit) :
    (∑ h : History 2 2,
      |weight Qubit Qubit 2 (feedback Qubit swapMeasure) h
        (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run [halfCollision,halfCollision] (basisState 0)) -
       weight Qubit Qubit 2 (feedback Qubit swapMeasure) h
        (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run [halfCollision,halfCollision] (basisState 1))|)/2 = 1/4 := by
  have ht (c : Qubit) (h : History 2 2) :
      weight Qubit Qubit 2 (feedback Qubit swapMeasure) h
        (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run [halfCollision,halfCollision] (basisState c)) =
      if h.2.1=h.1 then (if c=0 then (if h.1=0 then 1 else 0) else
        (if h.1=0 then 3/4 else 1/4)) else 0 := by
    rcases h with ⟨a,d,u⟩
    cases u
    exact swap_feedback_quarter_table b c a d
  simp_rw [ht]
  change (∑ h : Fin 2 × (Fin 2 × Unit), _)/2 = _
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]

/-- A two-stage feedback law retains exactly the first binary separation. -/
theorem feedback_totalVariation (D : FiniteInterventionProcess.Step Qubit E 2)
    {X Y : Matrix (Qubit × E) (Qubit × E) ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    totalVariation (feedback E D) X Y =
      |(D.branch Qubit E 2 1 X).trace.re-(D.branch Qubit E 2 1 Y).trace.re| := by
  have ht (Z : Matrix (Qubit × E) (Qubit × E) ℂ) (h : History 2 2) :
      weight Qubit E 2 (feedback E D) h Z =
        if h.2.1=h.1 then (D.branch Qubit E 2 h.1 Z).trace.re else 0 := by
    rcases h with ⟨a,b,u⟩
    cases u
    exact feedback_weights E D a b Z
  have hx := congrArg Complex.re (D.sum_trace Qubit E 2 X)
  have hy := congrArg Complex.re (D.sum_trace Qubit E 2 Y)
  simp only [Fin.sum_univ_two, Complex.add_re, hX.2, hY.2, Complex.one_re] at hx hy
  have hz : (D.branch Qubit E 2 0 X).trace.re-(D.branch Qubit E 2 0 Y).trace.re =
      -((D.branch Qubit E 2 1 X).trace.re-(D.branch Qubit E 2 1 Y).trace.re) := by linarith
  unfold totalVariation
  simp_rw [ht]
  change (∑ h : Fin 2 × (Fin 2 × Unit), _)/2 = _
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, hz]
  rw [abs_sub_comm (D.branch Qubit E 2 1 Y).trace.re]
  ring

/-- Actual feedback histories have diagonal support for every retained density state. -/
theorem swap_feedback_table (b a d : Qubit) {X : Matrix Qubit Qubit ℂ}
    (hX : IsDensityOperator X) :
    weight Qubit Qubit 2 (feedback Qubit swapMeasure) (a,d,()) (basisState b ⊗ₖ X) =
      if d=a then (if a=1 then binaryOutcomeProb binaryOneEffect X else
        1-binaryOutcomeProb binaryOneEffect X) else 0 := by
  have hn := congrArg Complex.re (swapMeasure.sum_trace Qubit Qubit 2 (basisState b ⊗ₖ X))
  rw [(basis_tensor_density b hX).2] at hn
  simp only [Fin.sum_univ_two, Complex.add_re, Complex.one_re] at hn
  have h1 : (swapMeasure.branch Qubit Qubit 2 1 (basisState b ⊗ₖ X)).trace.re =
      binaryOutcomeProb binaryOneEffect X := by
    rw [swapMeasure_trace, FiniteMemoryCoarseGraining.finalSwap_readout]
  have h0 : (swapMeasure.branch Qubit Qubit 2 0 (basisState b ⊗ₖ X)).trace.re =
      1-binaryOutcomeProb binaryOneEffect X := by linarith
  rw [feedback_weights]
  fin_cases a <;> simp [h0, h1]

/-- Sharpness is attained by the same SWAP-feedback strategy after every admissible suffix. -/
theorem swap_feedback_sharp (b : Qubit) (suffix : List FiniteMemoryCoarseGraining.Step) :
    totalVariation (feedback Qubit swapMeasure)
      (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run suffix (basisState 0))
      (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run suffix (basisState 1)) =
      FiniteMemoryCoarseGraining.retentionProduct suffix := by
  rw [feedback_totalVariation swapMeasure
    (basis_tensor_density b (FiniteMemoryCoarseGraining.run_density suffix (basisState_density 0)))
    (basis_tensor_density b (FiniteMemoryCoarseGraining.run_density suffix (basisState_density 1)))]
  rw [swapMeasure_trace, swapMeasure_trace, FiniteMemoryCoarseGraining.finalSwap_readout,
    FiniteMemoryCoarseGraining.finalSwap_readout, FiniteMemoryCoarseGraining.run_binary_separation]

/-- A zero retention product makes all common adaptive laws identical in total variation. -/
theorem adaptive_suffix_zero {n : ℕ} (T : Tree Qubit Qubit o n)
    (b : Qubit) (pre suffix : List FiniteMemoryCoarseGraining.Step)
    (hs : FiniteMemoryCoarseGraining.retentionProduct suffix = 0)
    {ρ τ : Matrix Qubit Qubit ℂ} (hρ : IsDensityOperator ρ) (hτ : IsDensityOperator τ) :
    totalVariation T (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run (pre++suffix) ρ)
      (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run suffix τ) = 0 := by
  apply le_antisymm
  · simpa [hs] using adaptive_suffix_bound T b pre suffix hρ hτ
  · exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

theorem swap_feedback_retention_one (b : Qubit) (suffix : List FiniteMemoryCoarseGraining.Step)
    (hs : FiniteMemoryCoarseGraining.retentionProduct suffix = 1) :
    totalVariation (feedback Qubit swapMeasure)
      (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run suffix (basisState 0))
      (basisState b ⊗ₖ FiniteMemoryCoarseGraining.run suffix (basisState 1)) = 1 := by
  rw [swap_feedback_sharp, hs]

theorem swap_feedback_empty (b : Qubit) :
    totalVariation (feedback Qubit swapMeasure) (basisState b ⊗ₖ basisState 0)
      (basisState b ⊗ₖ basisState 1) = 1 := by
  exact swap_feedback_sharp b []

/-- No interventions produce the single empty history with probability one. -/
theorem depth_zero_score (f : History o 0 → ℝ)
    {X : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) :
    score (Tree.done : Tree S E o 0) f X = f () := by
  simp [score, History, weight, run, hX.2]

theorem depth_zero_totalVariation {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    totalVariation (Tree.done : Tree S E o 0) X Y = 0 := by
  simp [totalVariation, History, weight, run, hX.2, hY.2]

end SKEFTHawking.QuantumNetwork.FiniteAdaptiveProcessRobustness
