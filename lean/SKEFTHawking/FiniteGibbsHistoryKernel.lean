import SKEFTHawking.FiniteGibbsTwoTimeProcess
import SKEFTHawking.FinitePositiveKernel

/-! Finite computational Gibbs histories and their centered covariance reconstruction.
All probabilities are actual intervention-tree weights. Intermediate measurements
are eliminated by summing their outcomes, not by assuming independent transitions. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.GibbsHistoryKernel
open Matrix FiniteInterventionProcess GibbsRelaxationProcess GibbsTwoTimeProcess
open FinitePositiveKernel.DiagonalLindblad
open scoped ComplexOrder InnerProductSpace

def transition (β Δ γ t : ℝ) (a b : Qubit) : ℝ :=
  (1-Real.exp (-γ*t))*weights β Δ b+Real.exp (-γ*t)*(if b=a then 1 else 0)

theorem transition_zero (β Δ γ : ℝ) (a b : Qubit) :
    transition β Δ γ 0 a b=if b=a then 1 else 0 := by simp [transition]

theorem transition_sum (β Δ γ t : ℝ) (a : Qubit) : ∑ b,transition β Δ γ t a b=1 := by
  have hn := weights_sum β Δ
  simp only [Fin.sum_univ_two] at hn ⊢
  fin_cases a <;> norm_num [transition] <;> linear_combination (1-Real.exp (-(γ*t)))*hn

theorem transition_stationary (β Δ γ t : ℝ) (b : Qubit) :
    ∑ a,weights β Δ a*transition β Δ γ t a b=weights β Δ b := by
  have hn := weights_sum β Δ
  simp only [Fin.sum_univ_two] at hn ⊢
  have hw : weights β Δ 1=1-weights β Δ 0 := by linarith
  fin_cases b <;> norm_num [transition] <;> rw [hw] <;> ring

theorem chapman_kolmogorov (β Δ γ s t : ℝ) (a c : Qubit) :
    ∑ b,transition β Δ γ s a b*transition β Δ γ t b c=transition β Δ γ (s+t) a c := by
  have hn := weights_sum β Δ
  have he : Real.exp (-(γ*(s+t)))=Real.exp (-(γ*s))*Real.exp (-(γ*t)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [Fin.sum_univ_two] at hn ⊢
  have hw : weights β Δ 1=1-weights β Δ 0 := by linarith
  fin_cases a <;> fin_cases c <;> norm_num [transition] <;> rw [he,hw] <;> ring

/-- Computational measurement closes on the actual unnormalized basis state. -/
theorem computational_branch (X : Matrix Qubit Qubit ℂ) (b : Qubit) :
    FiniteInstrument.computational.branch b X=X b b • FiniteMemoryProcess.basisState b := by
  simp only [FiniteInstrument.branch,FiniteInstrument.computational,krausMap]
  ext i j
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [FiniteMemoryProcess.basisState,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]

theorem transition_branch (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (a b : Qubit) :
    (step FiniteInstrument.computational β Δ γ η t hγ hη ht).branch Qubit Unit 2 b
      (joint (FiniteMemoryProcess.basisState a)) =
    (transition β Δ γ t a b:ℂ) • joint (FiniteMemoryProcess.basisState b) := by
  rw [step_branch,computational_branch,channel_diagonal β Δ γ η t hγ hη ht,
    (FiniteMemoryProcess.basisState_density a).2,joint_smul]
  congr 1
  fin_cases a <;> fin_cases b <;> norm_num [transition,FiniteMemoryProcess.basisState]

/-- Outcomes are read only at indices within the finite history length. -/
def outcome : {n : ℕ} → History 2 n → ℕ → Qubit
  | 0,_,_ => 0
  | _+1,h,0 => h.1
  | _+1,h,i+1 => outcome h.2 i

def later (τ : ℕ → ℝ) : ℕ → ℝ := fun i => τ (i+1)

def tailMass (β Δ γ : ℝ) : (n : ℕ) → (ℕ → ℝ) → Qubit → History 2 n → ℝ
  | 0,_,_,_ => 1
  | n+1,τ,a,h => transition β Δ γ (τ 1-τ 0) a h.1 * tailMass β Δ γ n (later τ) h.1 h.2

def historyMass (β Δ γ : ℝ) (n : ℕ) (τ : ℕ → ℝ) (h : History 2 (n+1)) : ℝ :=
  weights β Δ h.1 * tailMass β Δ γ n τ h.1 h.2

theorem tailMass_sum (β Δ γ : ℝ) (n : ℕ) (τ : ℕ → ℝ) (a : Qubit) :
    ∑ h,tailMass β Δ γ n τ a h=1 := by
  induction n generalizing τ a with
  | zero => simp [tailMass,History]
  | succ n ih =>
    change (∑ h : Qubit × History 2 n, _)=1
    simp only [Fintype.sum_prod_type,tailMass,← Finset.mul_sum,ih,mul_one,transition_sum]

/-- Summing every intervening outcome composes the actual computational transitions. -/
theorem endpoint_expectation (β Δ γ : ℝ) (n : ℕ) (τ : ℕ → ℝ) (a : Qubit)
    (j : ℕ) (hj : j<n) (F : Qubit → ℝ) :
    (∑ h,tailMass β Δ γ n τ a h*F (outcome h j)) =
      ∑ b,transition β Δ γ (τ (j+1)-τ 0) a b*F b := by
  induction n generalizing τ a j with
  | zero => omega
  | succ n ih =>
    change (∑ h : Qubit × History 2 n, _)=_
    rw [Fintype.sum_prod_type]
    cases j with
    | zero =>
      simp only [tailMass,outcome]
      simp_rw [mul_right_comm (transition _ _ _ _ _ _) _ (F _)]
      simp only [← Finset.mul_sum,tailMass_sum,mul_one]
    | succ j =>
      simp only [tailMass,outcome,mul_assoc,← Finset.mul_sum]
      simp_rw [ih (later τ) _ j (by omega)]
      simp_rw [Finset.mul_sum,← mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul,chapman_kolmogorov,later]
      congr 1
      funext b
      congr 2
      ring

theorem later_monotone {τ : ℕ → ℝ} (hτ : Monotone τ) : Monotone (later τ) :=
  fun _ _ h => hτ (Nat.add_le_add_right h 1)

/-- Finite lag process; schedule values beyond the selected horizon are unused. -/
def tailTree (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    (n : ℕ) → (τ : ℕ → ℝ) → Monotone τ → Tree Qubit Unit 2 n
  | 0,_,_ => .done
  | n+1,τ,hτ => .node
      (step FiniteInstrument.computational β Δ γ η (τ 1-τ 0) hγ hη (sub_nonneg.mpr (hτ (by omega))))
      (fun _ => tailTree β Δ γ η hγ hη n (later τ) (later_monotone hτ))

def historyTree (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : Monotone τ) : Tree Qubit Unit 2 (n+1) :=
  .node (step FiniteInstrument.computational β Δ γ η 0 hγ hη (by norm_num))
    (fun _ => tailTree β Δ γ η hγ hη n τ hτ)

theorem tail_weight (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : Monotone τ) (a : Qubit) (h : History 2 n) :
    weight Qubit Unit 2 (tailTree β Δ γ η hγ hη n τ hτ) h
      (joint (FiniteMemoryProcess.basisState a))=tailMass β Δ γ n τ a h := by
  induction n generalizing τ a with
  | zero =>
    change (joint (FiniteMemoryProcess.basisState a)).trace.re=1
    rw [joint_trace,(FiniteMemoryProcess.basisState_density a).2]
    rfl
  | succ n ih =>
    change weight Qubit Unit 2 (tailTree β Δ γ η hγ hη n (later τ) (later_monotone hτ)) h.2
      ((step FiniteInstrument.computational β Δ γ η (τ 1-τ 0) hγ hη _).branch Qubit Unit 2 h.1
        (joint (FiniteMemoryProcess.basisState a)))=_
    rw [transition_branch,weight_real_smul,ih]
    rfl

/-- Actual history weights are the Gibbs mass times the conditional transition product. -/
theorem history_weight (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : Monotone τ) (h : History 2 (n+1)) :
    weight Qubit Unit 2 (historyTree β Δ γ η hγ hη n τ hτ) h (joint (equilibrium β Δ)) =
      historyMass β Δ γ n τ h := by
  change weight Qubit Unit 2 (tailTree β Δ γ η hγ hη n τ hτ) h.2
    ((step FiniteInstrument.computational β Δ γ η 0 hγ hη _).branch Qubit Unit 2 h.1
      (joint (equilibrium β Δ)))=_
  rw [initial_branch,computational_collapse,joint_smul,weight_real_smul,tail_weight]
  rfl

theorem tailMass_product (β Δ γ : ℝ) (n : ℕ) (τ : ℕ → ℝ) (a : Qubit) (h : History 2 n) :
    tailMass β Δ γ n τ a h =
      ∏ j : Fin n, transition β Δ γ (τ (j.val+1)-τ j.val)
        (outcome (n := n+1) (a,h) j.val) (outcome (n := n+1) (a,h) (j.val+1)) := by
  induction n generalizing τ a with
  | zero => simp [tailMass]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    simp only [tailMass,outcome,Fin.val_zero,Fin.val_succ,zero_add]
    rw [ih]
    rfl

/-- Selected pairs are marginals of the same full history, including all intermediate observations. -/
theorem pair_expectation (β Δ γ : ℝ) (n : ℕ) (τ : ℕ → ℝ) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ n) (F : Qubit → Qubit → ℝ) :
    (∑ h,historyMass β Δ γ n τ h*F (outcome h i) (outcome h j)) =
      ∑ a,∑ b,weights β Δ a*transition β Δ γ (τ j-τ i) a b*F a b := by
  induction n generalizing τ i j with
  | zero =>
    have hi : i=0 := by omega
    have hj : j=0 := by omega
    subst i; subst j
    change (∑ h : Qubit × Unit,_)=_
    simp [Fintype.sum_prod_type,historyMass,tailMass,outcome,transition_zero]
  | succ n ih =>
    change (∑ h : Qubit × History 2 (n+1),_)=_
    rw [Fintype.sum_prod_type]
    cases i with
    | zero =>
      cases j with
      | zero =>
        simp only [historyMass,outcome,sub_self,transition_zero]
        simp_rw [mul_right_comm (weights _ _ _) _ (F _ _)]
        simp only [← Finset.mul_sum,tailMass_sum,mul_one]
        simp
      | succ j =>
        simp only [historyMass,outcome,mul_assoc,← Finset.mul_sum]
        simp_rw [endpoint_expectation β Δ γ (n+1) τ _ j (by omega)]
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [historyMass,tailMass,outcome,mul_assoc]
        rw [Finset.sum_comm]
        have he : ∀ h : History 2 (n+1),
            (∑ a,weights β Δ a*(transition β Δ γ (τ 1-τ 0) a h.1*
              (tailMass β Δ γ n (later τ) h.1 h.2*F (outcome h i) (outcome h j)))) =
            historyMass β Δ γ n (later τ) h*F (outcome h i) (outcome h j) := by
          intro h
          simp only [← mul_assoc,← Finset.sum_mul,transition_stationary,historyMass]
        simp_rw [he]
        simpa only [later,mul_assoc] using ih (later τ) i j (by omega) (by omega)

def centered (β Δ : ℝ) (a : Qubit) : ℝ := sign a-meanZ β Δ

theorem transition_covariance (β Δ γ t : ℝ) :
    (∑ a,∑ b,weights β Δ a*transition β Δ γ t a b*(centered β Δ a*centered β Δ b)) =
      (1-meanZ β Δ^2)*Real.exp (-γ*t) := by
  have hn : weights β Δ 0+weights β Δ 1=1 := by simpa [Fin.sum_univ_two] using weights_sum β Δ
  have hw : weights β Δ 1=1-weights β Δ 0 := by linarith
  norm_num [Fin.sum_univ_two,transition,centered,sign,meanZ]
  rw [hw]
  ring

/-- Centered covariance is defined directly by the actual full-history distribution. -/
def covariance (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : Monotone τ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := fun i j =>
  ((∑ h,weight Qubit Unit 2 (historyTree β Δ γ η hγ hη n τ hτ) h (joint (equilibrium β Δ))*
    (centered β Δ (outcome h i.val)*centered β Δ (outcome h j.val)) : ℝ):ℂ)

theorem covariance_symm (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : Monotone τ) (i j : Fin (n+1)) :
    covariance β Δ γ η hγ hη n τ hτ i j=covariance β Δ γ η hγ hη n τ hτ j i := by
  unfold covariance
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Every selected covariance pair belongs to one and the same repeatedly measured history. -/
theorem covariance_eq (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : Monotone τ) (i j : Fin (n+1)) :
    covariance β Δ γ η hγ hη n τ hτ i j =
      (((1-meanZ β Δ^2)*Real.exp (-γ*|τ i.val-τ j.val|):ℝ):ℂ) := by
  have he (i j : Fin (n+1)) (hij : i.val ≤ j.val) :
      covariance β Δ γ η hγ hη n τ hτ i j=
        (((1-meanZ β Δ^2)*Real.exp (-γ*(τ j.val-τ i.val)):ℝ):ℂ) := by
    unfold covariance
    simp only [history_weight]
    rw [pair_expectation β Δ γ n τ i.val j.val hij (by omega) (fun a b => centered β Δ a*centered β Δ b),transition_covariance]
  by_cases hij : i.val ≤ j.val
  · rw [he i j hij,abs_of_nonpos (sub_nonpos.mpr (hτ hij)),neg_sub]
  · rw [covariance_symm,he j i (by omega),abs_of_nonneg (sub_nonneg.mpr (hτ (by omega)))]

/-- Weighted real features of actual measurement histories. -/
def gramFeatures (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : Monotone τ) : Matrix (History 2 (n+1)) (Fin (n+1)) ℂ := fun h i =>
  ((Real.sqrt (weight Qubit Unit 2 (historyTree β Δ γ η hγ hη n τ hτ) h (joint (equilibrium β Δ)))*
    centered β Δ (outcome h i.val):ℝ):ℂ)

theorem covariance_gram (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : Monotone τ) :
    covariance β Δ γ η hγ hη n τ hτ =
      (gramFeatures β Δ γ η hγ hη n τ hτ)ᴴ*gramFeatures β Δ γ η hγ hη n τ hτ := by
  ext i j
  simp only [covariance,Matrix.mul_apply,Matrix.conjTranspose_apply,gramFeatures]
  push_cast
  apply Finset.sum_congr rfl
  intro h _
  have hp := weight_nonneg Qubit Unit 2 (historyTree β Δ γ η hγ hη n τ hτ) h
    (joint_density _ (equilibrium_density β Δ)).1
  have hs := Real.sq_sqrt hp
  simp
  norm_cast
  linear_combination -(centered β Δ (outcome h i.val)*centered β Δ (outcome h j.val))*hs

/-- Positive semidefiniteness comes from the actual nonnegative history probabilities. -/
theorem covariance_positive (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : Monotone τ) : (covariance β Δ γ η hγ hη n τ hτ).PosSemidef := by
  rw [covariance_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Every finite ordered schedule extends constantly after its last observation. -/
def extendSchedule {n : ℕ} (τ : Fin (n+1) → ℝ) : ℕ → ℝ := fun k => τ ⟨min k n,by omega⟩

theorem extendSchedule_monotone {n : ℕ} {τ : Fin (n+1) → ℝ} (hτ : Monotone τ) :
    Monotone (extendSchedule τ) := by
  intro a b hab
  apply hτ
  exact min_le_min_right n hab

theorem extendSchedule_eval {n : ℕ} (τ : Fin (n+1) → ℝ) (i : Fin (n+1)) : extendSchedule τ i.val=τ i := by
  unfold extendSchedule
  congr 1
  apply Fin.ext
  exact min_eq_left (by omega)

/-- Actual finite-history covariance; no assumptions about times beyond the finite schedule. -/
def finiteCovariance (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  covariance β Δ γ η hγ hη n (extendSchedule τ) (extendSchedule_monotone hτ)

theorem finiteCovariance_eq (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (i j : Fin (n+1)) :
    finiteCovariance β Δ γ η hγ hη n τ hτ i j=
      (((1-meanZ β Δ^2)*Real.exp (-γ*|τ i-τ j|):ℝ):ℂ) := by
  unfold finiteCovariance
  rw [covariance_eq,extendSchedule_eval,extendSchedule_eval]

theorem finiteCovariance_positive (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) :
    (finiteCovariance β Δ γ η hγ hη n τ hτ).PosSemidef := covariance_positive _ _ _ _ _ _ _ _ _

/-- Existing positive-kernel reconstruction applied to this actual history covariance. -/
def reconstructedFeature (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (i : Fin (n+1)) :=
  FinitePositiveKernel.feature (finiteCovariance β Δ γ η hγ hη n τ hτ)
    (finiteCovariance_positive β Δ γ η hγ hη n τ hτ) i

theorem inner_reconstructed (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (i j : Fin (n+1)) :
    ⟪reconstructedFeature β Δ γ η hγ hη n τ hτ i,reconstructedFeature β Δ γ η hγ hη n τ hτ j⟫_ℂ =
      (((1-meanZ β Δ^2)*Real.exp (-γ*|τ i-τ j|):ℝ):ℂ) := by
  rw [reconstructedFeature,reconstructedFeature,FinitePositiveKernel.inner_feature,finiteCovariance_eq]

/-- The full history has the same selected-pair law after summing all other observations. -/
theorem pair_marginal (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : Monotone τ) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) (a b : Qubit) :
    (∑ h : History 2 (n+1), if outcome h i=a ∧ outcome h j=b then
      weight Qubit Unit 2 (historyTree β Δ γ η hγ hη n τ hτ) h (joint (equilibrium β Δ)) else 0) =
    weights β Δ a*transition β Δ γ (τ j-τ i) a b := by
  classical
  have he := pair_expectation β Δ γ n τ i j hij hj (fun x y => if x=a ∧ y=b then 1 else 0)
  fin_cases a <;> fin_cases b <;> simpa [history_weight,mul_ite] using he

/-- Product formula includes every actual transition of the measurement history. -/
theorem history_product (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : Monotone τ) (h : History 2 (n+1)) :
    weight Qubit Unit 2 (historyTree β Δ γ η hγ hη n τ hτ) h (joint (equilibrium β Δ)) =
      weights β Δ h.1 * ∏ j : Fin n, transition β Δ γ (τ (j.val+1)-τ j.val)
        (outcome h j.val) (outcome h (j.val+1)) := by
  rw [history_weight,historyMass,tailMass_product]
  rfl

/-- Zero reset leaves all computational populations correlated at every lag. -/
theorem zero_rate (β Δ η : ℝ) (hη : 0 ≤ η)
    (n : ℕ) (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (i j : Fin (n+1)) :
    finiteCovariance β Δ 0 η (by norm_num) hη n τ hτ i j=((1-meanZ β Δ^2:ℝ):ℂ) := by
  rw [finiteCovariance_eq]
  norm_num

theorem repeated_time (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (n : ℕ) (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (i j : Fin (n+1)) (hij : τ i=τ j) :
    finiteCovariance β Δ γ η hγ hη n τ hτ i j=((1-meanZ β Δ^2:ℝ):ℂ) := by
  rw [finiteCovariance_eq,hij]
  norm_num

def threeTimes (i : Fin 3) : ℝ := i.val

theorem threeTimes_monotone : Monotone threeTimes := by
  intro i j hij
  change (i.val:ℝ) ≤ (j.val:ℝ)
  exact_mod_cast (show i.val ≤ j.val from hij)

def exampleKernel : Matrix (Fin 3) (Fin 3) ℂ :=
  finiteCovariance 1 1 1 0 (by norm_num) (by norm_num) 2 threeTimes threeTimes_monotone

theorem example_matrix :
    exampleKernel =
      let v : ℂ := ((1-meanZ 1 1^2:ℝ):ℂ)
      !![v,v*(Real.exp (-1):ℂ),v*(Real.exp (-2):ℂ);
         v*(Real.exp (-1):ℂ),v,v*(Real.exp (-1):ℂ);
         v*(Real.exp (-2):ℂ),v*(Real.exp (-1):ℂ),v] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [exampleKernel,finiteCovariance_eq,threeTimes]

theorem example_minor :
    (exampleKernel 0 0).re*(exampleKernel 1 1).re-(exampleKernel 0 1).re*(exampleKernel 1 0).re =
      (1-meanZ 1 1^2)^2*(1-Real.exp (-2)) := by
  have he : Real.exp (-2)=Real.exp (-1)*Real.exp (-1) := by rw [← Real.exp_add]; norm_num
  simp only [exampleKernel,finiteCovariance_eq,Complex.ofReal_re]
  norm_num [threeTimes]
  rw [he]
  ring

theorem example_minor_pos :
    0 < (exampleKernel 0 0).re*(exampleKernel 1 1).re-(exampleKernel 0 1).re*(exampleKernel 1 0).re := by
  rw [example_minor]
  exact mul_pos (sq_pos_of_pos (stationary_variance_pos 1 1))
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))

end SKEFTHawking.QuantumNetwork.GibbsHistoryKernel
