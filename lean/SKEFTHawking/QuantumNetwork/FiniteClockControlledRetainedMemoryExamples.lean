import SKEFTHawking.QuantumNetwork.FiniteClockControlledRetainedMemory

/-!
# Recorded controlled-clock experiments

Every original setting and outcome is retained, including dynamically zero leaves.
The terminal event measures the qutrit projector and leaves both clocks untouched.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteClockControlledRetainedMemoryExamples
open Matrix FiniteInterventionProcess FiniteClockControlledRetainedMemory
open FiniteQutritPhysicalMemory
open scoped BigOperators ComplexOrder Kronecker

def unitQutrit (X : Mat) : Matrix (Q × Unit) (Q × Unit) ℂ := X ⊗ₖ (1 : Matrix Unit Unit ℂ)
def prepareData (c : A) (X : Mat) : ReducedMat Unit :=
  FiniteQutritRetainedClock.amplifiedPreparation Unit c (unitQutrit X)
def input (σ : FiniteClockHandReadout.Mat) : FullMat Unit :=
  insert Unit (prepareData 0 FiniteQutritRetainedClock.rho0) σ
def afterFirst : FullMat Unit :=
  insert Unit (prepareData 1 FiniteQutritRetainedClock.rho0) (FiniteClockHandReadout.Q 0)

theorem unitQutrit_density {X : Mat} (hX : IsDensityOperator X) : IsDensityOperator (unitQutrit X) := by
  refine ⟨hX.1.kronecker Matrix.PosSemidef.one, ?_⟩
  rw [unitQutrit, Matrix.trace_kronecker, hX.2]
  norm_num [Matrix.trace]

theorem prepareData_density (c : A) {X : Mat} (hX : IsDensityOperator X) :
    IsDensityOperator (prepareData c X) :=
  FiniteQutritRetainedClock.preparation_density Unit c (unitQutrit_density hX)

theorem input_density {σ : FiniteClockHandReadout.Mat} (hσ : IsDensityOperator σ) :
    IsDensityOperator (input σ) := by
  have hD := prepareData_density 0 FiniteQutritRetainedClock.rho0_density
  exact ⟨insert_positive Unit hD.1 hσ.1, by rw [input, insert_trace, hD.2, hσ.2, mul_one]⟩

theorem afterFirst_density : IsDensityOperator afterFirst := by
  have hD := prepareData_density 1 FiniteQutritRetainedClock.rho0_density
  exact ⟨insert_positive Unit hD.1 (FiniteClockHandReadout.Q_density 0).1,
    by rw [afterFirst, insert_trace, hD.2, FiniteClockHandReadout.Q_trace, mul_one]⟩

theorem old_reduce_prepare (c : A) (X : Mat) :
    FiniteQutritRetainedClock.amplifiedReduction Unit (prepareData c X) = unitQutrit X := by
  ext ⟨s,f⟩ ⟨t,g⟩
  rw [FiniteQutritRetainedClock.reduction_entry]
  simp only [prepareData, FiniteQutritRetainedClock.preparation_entry, Fin.sum_univ_two]
  fin_cases c <;> simp [FiniteQutritRetainedClock.P, FiniteQutritRetainedClock.e, Matrix.single]

theorem insert_zero (Q : FiniteClockHandReadout.Mat) : insert Unit 0 Q = 0 := by
  ext x y
  simp [FiniteClockControlledRetainedMemory.insert]

theorem first_branch {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) (a : A) (i : Fin 11) :
    (step Unit ω ℏ (Real.pi/ω) hℏ).branch S Unit 22 (outcomeEquiv (a,i)) (input σ) =
      if a=0 ∧ i=FiniteQutritRetainedClock.noneLabel then afterFirst else 0 := by
  rw [keep_branch Unit hω hℏ]
  rcases (show a=0 ∨ a=1 by fin_cases a <;> simp) with rfl | rfl
  · simp only [if_pos rfl, ite_true, input, handTrace_insert, hσ, one_smul, prepareData]
    rcases FiniteQutritRetainedClock.label_cases i with rfl | ⟨k,rfl⟩
    · rw [FiniteQutritRetainedClock.none_zero_branch]
      simp [afterFirst, prepareData]
    · rw [FiniteQutritRetainedClock.some_zero_branch]
      simp [insert_zero, Ne.symm (FiniteQutritRetainedClock.none_ne_some k)]
  · simp

def micro (k : Fin 10) : Mat :=
  FiniteQutritAveragedTransfer.krausOperator k * FiniteQutritRetainedClock.rho0 *
    (FiniteQutritAveragedTransfer.krausOperator k)ᴴ

theorem ten_branch (k : Fin 10) :
    (localStep Q Unit 10 FiniteQutritAveragedTransfer.instrument).branch Q Unit 10 k
      (unitQutrit FiniteQutritRetainedClock.rho0) = unitQutrit (micro k) := by
  unfold unitQutrit
  rw [localStep_branch]
  rw [FiniteAdaptiveMapPerturbation.lift_branch_tensor]
  simp [micro, unitQutrit, FiniteQutritAveragedTransfer.instrument, FiniteInstrument.branch, krausMap]

def secondState (ω t : ℝ) (a : A) (i : Fin 11) : FullMat Unit :=
  if a=0 then
    match FiniteQutritRetainedClock.labelEquiv.symm i with
    | none => 0
    | some k => (FiniteClockHandReadout.p ω t : ℂ) •
        insert Unit (prepareData 0 (micro k)) (FiniteClockHandReadout.Q 0)
  else if i=FiniteQutritRetainedClock.noneLabel then
    ((1-FiniteClockHandReadout.p ω t : ℝ) : ℂ) •
      insert Unit (prepareData 1 FiniteQutritRetainedClock.rho0) (FiniteClockHandReadout.Q 1)
  else 0

theorem second_branch {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) (i : Fin 11) :
    (step Unit ω ℏ t hℏ).branch S Unit 22 (outcomeEquiv (a,i)) afterFirst = secondState ω t a i := by
  rw [branch_action, afterFirst, handTrace_insert, FiniteClockHandReadout.Q_trace, one_smul]
  rcases (show a=0 ∨ a=1 by fin_cases a <;> simp) with rfl | rfl
  · rw [dataBranch_keep]
    simp only [prepareData]
    rcases FiniteQutritRetainedClock.label_cases i with rfl | ⟨k,rfl⟩
    · rw [FiniteQutritRetainedClock.none_one_branch]
      simp [secondState, insert_zero, FiniteQutritRetainedClock.noneLabel]
    · rw [FiniteQutritRetainedClock.some_one_branch, ten_branch]
      simp [secondState, prepareData, FiniteClockHandReadout.mass, FiniteQutritRetainedClock.someLabel]
  · rw [dataBranch_reset, FiniteQutritRetainedClock.reset_amplified_action, old_reduce_prepare]
    rcases FiniteQutritRetainedClock.label_cases i with rfl | ⟨k,rfl⟩
    · rw [FiniteQutritRetainedClock.none_zero_branch]
      simp [secondState, prepareData, FiniteClockHandReadout.mass]
    · rw [FiniteQutritRetainedClock.some_zero_branch]
      simp [secondState, insert_zero, Ne.symm (FiniteQutritRetainedClock.none_ne_some k)]

def keepDuration {ω : ℝ} (hω : 0 < ω) : Duration := ⟨Real.pi/ω, by positivity⟩
def leftDuration {ω : ℝ} (hω : 0 < ω) : Duration := ⟨Real.pi/(3*ω), by positivity⟩
def rightDuration {ω : ℝ} (hω : 0 < ω) : Duration := ⟨2*Real.pi/(3*ω), by positivity⟩
def twoPolicy {ω : ℝ} (hω : 0 < ω) (t : Duration) : Policy 2 :=
  .node (keepDuration hω) (fun _ => .node t (fun _ => .done))

theorem two_round_table {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (t : Duration)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) (a b : A) (i j : Fin 11) :
    run S Unit 22 (policyTree Unit ω ℏ hℏ (twoPolicy hω t))
      (outcomeEquiv (a,i), outcomeEquiv (b,j),()) (input σ) =
      if a=0 ∧ i=FiniteQutritRetainedClock.noneLabel then secondState ω t b j else 0 := by
  change (step Unit ω ℏ t hℏ).branch S Unit 22 (outcomeEquiv (b,j))
    ((step Unit ω ℏ (Real.pi/ω) hℏ).branch S Unit 22 (outcomeEquiv (a,i)) (input σ)) = _
  rw [first_branch hω.ne' hℏ hσ]
  split
  · exact second_branch hℏ ω t b j
  · exact Step.branch_zero S Unit 22 _ _

def microPair (j : Setting) (a : A) : Mat :=
  if j.val=0 then (if a.val=0 then (1/5:ℂ) • FiniteQutritRetainedClock.rho0 else 0)
  else if j.val=1 ∨ j.val=2 then (if a.val=0 then 0 else (1/5:ℂ) • FiniteQutritRetainedClock.rho0)
  else if j.val=3 then (1/20:ℂ) • !![1,(if a.val=0 then 1 else -1),0;
    (if a.val=0 then 1 else -1),1,0;0,0,0]
  else (1/20:ℂ) • !![1,0,(if a.val=0 then 1 else -1);0,0,0;
    (if a.val=0 then 1 else -1),0,1]

theorem rho0_sandwich (T : Mat) :
    T * FiniteQutritRetainedClock.rho0 * Tᴴ = Matrix.of (fun s t => T s 0 * star (T t 0)) := by
  ext s t
  simp [FiniteQutritRetainedClock.rho0, projector, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_three]

private theorem vec3_last {α : Type*} (a b c : α) : ![a,b,c] (2 : Fin 3) = c := rfl

private theorem setting_cases (j : Setting) : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by
  fin_cases j <;> decide
private theorem qutrit_cases (j : Q) : j=0 ∨ j=1 ∨ j=2 := by
  fin_cases j <;> decide
private theorem bit_cases (a : A) : a=0 ∨ a=1 := by
  fin_cases a <;> decide

private theorem micro_pair_0 (a : A) :
    micro (finProdFinEquiv ((0:Setting),a)) = microPair 0 a := by
  rw [micro, FiniteQutritAveragedTransfer.kraus_pair,
    FiniteQutritAveragedTransfer.scaled_sandwich, rho0_sandwich]
  rcases bit_cases a with rfl | rfl <;> ext s t <;>
    rcases qutrit_cases s with rfl | rfl | rfl <;>
    rcases qutrit_cases t with rfl | rfl | rfl <;>
    norm_num [microPair, outcomeOperator, FiniteQutritRetainedClock.rho0, projector,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail,
      Matrix.one_apply, map_ofNat, Complex.star_def, show (2:Q) ≠ 0 by decide]

private theorem micro_pair_1 (a : A) :
    micro (finProdFinEquiv ((1:Setting),a)) = microPair 1 a := by
  rw [micro, FiniteQutritAveragedTransfer.kraus_pair,
    FiniteQutritAveragedTransfer.scaled_sandwich, rho0_sandwich]
  rcases bit_cases a with rfl | rfl <;> ext s t <;>
    rcases qutrit_cases s with rfl | rfl | rfl <;>
    rcases qutrit_cases t with rfl | rfl | rfl <;>
    norm_num [microPair, outcomeOperator, FiniteQutritRetainedClock.rho0, projector,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail,
      Matrix.one_apply, map_ofNat, Complex.star_def, show (2:Q) ≠ 0 by decide]

private theorem micro_pair_2 (a : A) :
    micro (finProdFinEquiv ((2:Setting),a)) = microPair 2 a := by
  rw [micro, FiniteQutritAveragedTransfer.kraus_pair,
    FiniteQutritAveragedTransfer.scaled_sandwich, rho0_sandwich]
  rcases bit_cases a with rfl | rfl <;> ext s t <;>
    rcases qutrit_cases s with rfl | rfl | rfl <;>
    rcases qutrit_cases t with rfl | rfl | rfl <;>
    norm_num [microPair, outcomeOperator, FiniteQutritRetainedClock.rho0, projector,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail,
      Matrix.one_apply, map_ofNat, Complex.star_def, show (2:Q) ≠ 0 by decide]

private theorem micro_pair_3 (a : A) :
    micro (finProdFinEquiv ((3:Setting),a)) = microPair 3 a := by
  rw [micro, FiniteQutritAveragedTransfer.kraus_pair,
    FiniteQutritAveragedTransfer.scaled_sandwich, rho0_sandwich]
  rcases bit_cases a with rfl | rfl <;> ext s t <;>
    rcases qutrit_cases s with rfl | rfl | rfl <;>
    rcases qutrit_cases t with rfl | rfl | rfl <;>
    norm_num [microPair, outcomeOperator, FiniteQutritRetainedClock.rho0, projector,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail,
      Matrix.one_apply, map_ofNat, Complex.star_def, show (2:Q) ≠ 0 by decide]

private theorem micro_pair_4 (a : A) :
    micro (finProdFinEquiv ((4:Setting),a)) = microPair 4 a := by
  rw [micro, FiniteQutritAveragedTransfer.kraus_pair,
    FiniteQutritAveragedTransfer.scaled_sandwich, rho0_sandwich]
  rcases bit_cases a with rfl | rfl <;> ext s t <;>
    rcases qutrit_cases s with rfl | rfl | rfl <;>
    rcases qutrit_cases t with rfl | rfl | rfl <;>
    norm_num [microPair, outcomeOperator, FiniteQutritRetainedClock.rho0, projector,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail,
      Matrix.one_apply, map_ofNat, Complex.star_def, show (2:Q) ≠ 0 by decide]

theorem micro_pair (j : Setting) (a : A) :
    micro (finProdFinEquiv (j,a)) = microPair j a := by
  rcases setting_cases j with rfl | rfl | rfl | rfl | rfl
  · exact micro_pair_0 a
  · exact micro_pair_1 a
  · exact micro_pair_2 a
  · exact micro_pair_3 a
  · exact micro_pair_4 a

def microWeight (j : Setting) (a : A) : ℝ :=
  if j.val=0 then (if a.val=0 then 1/5 else 0)
  else if j.val=1 ∨ j.val=2 then (if a.val=0 then 0 else 1/5)
  else 1/10

theorem micro_weight (j : Setting) (a : A) :
    (micro (finProdFinEquiv (j,a))).trace.re = microWeight j a := by
  rw [micro_pair]
  rcases setting_cases j with rfl | rfl | rfl | rfl | rfl <;>
    rcases bit_cases a with rfl | rfl <;> norm_num [microPair, microWeight,
    FiniteQutritRetainedClock.rho0, projector, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail,
      Matrix.one_apply, map_ofNat, Complex.star_def, show (2:Q) ≠ 0 by decide]

theorem micro_positive (k : Fin 10) : (micro k).PosSemidef := by
  simpa [micro] using (FiniteQutritRetainedClock.rho0_density.1.conjTranspose_mul_mul_same
    (FiniteQutritAveragedTransfer.krausOperator k)ᴴ)

theorem micro_sum : (∑ k : Fin 10, micro k) =
    Matrix.diagonal ![(4/5:ℂ),1/10,1/10] := by
  change krausMap FiniteQutritAveragedTransfer.krausOperator FiniteQutritRetainedClock.rho0 = _
  rw [FiniteQutritAveragedTransfer.kraus_action, FiniteQutritRetainedClock.transfer_rho0]

theorem prepareData_entry (c : A) (X : Mat) (s t : Q) (a b : A) (f g : Unit) :
    prepareData c X ((s,a),f) ((t,b),g) = X s t * FiniteQutritRetainedClock.P c a b := by
  rw [prepareData, FiniteQutritRetainedClock.preparation_entry]
  cases f; cases g
  simp [unitQutrit]

theorem prepareData_sum {I : Type*} [Fintype I] (c : A) (X : I → Mat) :
    (∑ i, prepareData c (X i)) = prepareData c (∑ i, X i) := by
  ext ⟨⟨s,a⟩,f⟩ ⟨⟨t,b⟩,g⟩
  simp [Matrix.sum_apply, prepareData_entry, Finset.sum_mul]

theorem insert_smul (c : ℂ) (Y : ReducedMat Unit) (Q : FiniteClockHandReadout.Mat) :
    insert Unit (c • Y) Q = c • insert Unit Y Q := by
  ext x y
  simp [FiniteClockControlledRetainedMemory.insert, mul_assoc]

theorem insert_add (Y Z : ReducedMat Unit) (Q : FiniteClockHandReadout.Mat) :
    insert Unit (Y+Z) Q = insert Unit Y Q+insert Unit Z Q := by
  ext x y
  simp [FiniteClockControlledRetainedMemory.insert, add_mul]

def event : FullMat Unit :=
  ((projector 0 ⊗ₖ (1 : Matrix A A ℂ)) ⊗ₖ (1 : Matrix A A ℂ)) ⊗ₖ (1 : Matrix Unit Unit ℂ)

theorem event_hermitian : event.IsHermitian := by
  unfold Matrix.IsHermitian
  simp [event, Matrix.conjTranspose_kronecker, (projector_hermitian 0).eq]

theorem event_idempotent : event*event=event := by
  simp only [event, ← Matrix.mul_kronecker_mul, Matrix.one_mul, projector_idempotent]

theorem event_effect : IsBinaryPOVM event :=
  isBinaryPOVM_of_projection event_hermitian event_idempotent

def eventValue (Z : FullMat Unit) : ℝ := (event*Z).trace.re

theorem event0_entry (X : Mat) : FiniteQutritRetainedClock.event0 X = (X 0 0).re := by
  unfold FiniteQutritRetainedClock.event0
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
  norm_num [projector, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem event_prepare_complex (c : A) (X : Mat) (Q : FiniteClockHandReadout.Mat) :
    (event * insert Unit (prepareData c X) Q).trace = X 0 0 * Q.trace := by
  rcases (show c=0 ∨ c=1 by fin_cases c <;> simp) with rfl | rfl <;>
    simp [event, FiniteClockControlledRetainedMemory.insert, prepareData_entry,
      Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, projector, Matrix.one_apply, FiniteQutritRetainedClock.P,
      FiniteQutritRetainedClock.e, Matrix.single] <;> ring

theorem event_prepare (c : A) (X : Mat) (Q : FiniteClockHandReadout.Mat) (hQ : Q.trace = 1) :
    eventValue (insert Unit (prepareData c X) Q) = FiniteQutritRetainedClock.event0 X := by
  rw [eventValue, event_prepare_complex, hQ, mul_one, event0_entry]


def finalState (ω t : ℝ) : FullMat Unit :=
  (FiniteClockHandReadout.p ω t : ℂ) •
    insert Unit (prepareData 0 (FiniteQutritAveragedTransfer.transfer FiniteQutritRetainedClock.rho0))
      (FiniteClockHandReadout.Q 0) +
  ((1-FiniteClockHandReadout.p ω t : ℝ) : ℂ) •
    insert Unit (prepareData 1 FiniteQutritRetainedClock.rho0) (FiniteClockHandReadout.Q 1)

theorem secondState_sum (ω t : ℝ) :
    (∑ k : Fin 22, secondState ω t (outcomeEquiv.symm k).1 (outcomeEquiv.symm k).2) =
      finalState ω t := by
  rw [← outcomeEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [FiniteQutritRetainedClock.sum_labels, FiniteQutritRetainedClock.sum_labels]
  simp only [secondState, Equiv.symm_apply_apply, show (1:A) ≠ 0 by decide,
    if_pos rfl, if_false, zero_add]
  have hn (k : Fin 10) : FiniteQutritRetainedClock.labelEquiv (some k) ≠
      FiniteQutritRetainedClock.noneLabel :=
    Ne.symm (FiniteQutritRetainedClock.none_ne_some k)
  simp only [hn, ite_false, Finset.sum_const_zero, add_zero, if_pos rfl]
  simp only [ite_true, show FiniteQutritRetainedClock.labelEquiv none = FiniteQutritRetainedClock.noneLabel from rfl, if_pos rfl, zero_add]
  rw [← Finset.smul_sum, ← insert_sum, prepareData_sum]
  have hm : (∑ k, micro k) = FiniteQutritAveragedTransfer.transfer FiniteQutritRetainedClock.rho0 := by
    change krausMap FiniteQutritAveragedTransfer.krausOperator _ = _
    exact FiniteQutritAveragedTransfer.kraus_action _
  rw [hm]
  rfl

theorem two_round_sum {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (t : Duration)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) :
    (∑ h, run S Unit 22 (policyTree Unit ω ℏ hℏ (twoPolicy hω t)) h (input σ)) =
      finalState ω t := by
  change (∑ h : Fin 22 × (Fin 22 × Unit),
    (step Unit ω ℏ t hℏ).branch S Unit 22 h.2.1
      ((step Unit ω ℏ (Real.pi/ω) hℏ).branch S Unit 22 h.1 (input σ))) = _
  rw [Fintype.sum_prod_type, ← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  simp_rw [first_branch hω.ne' hℏ hσ]
  simp only [Fin.sum_univ_two, show (1:A) ≠ 0 by decide, false_and, if_false,
    Step.branch_zero, Finset.sum_const_zero, add_zero, true_and]
  have hx (i : Fin 11) :
      (∑ k, (step Unit ω ℏ t hℏ).branch S Unit 22 k
        (if i=FiniteQutritRetainedClock.noneLabel then afterFirst else 0)) =
      if i=FiniteQutritRetainedClock.noneLabel then
        ∑ k, secondState ω t (outcomeEquiv.symm k).1 (outcomeEquiv.symm k).2 else 0 := by
    split
    · apply Finset.sum_congr rfl
      intro k _
      obtain ⟨⟨a,j⟩,rfl⟩ := outcomeEquiv.surjective k
      simpa only [Equiv.symm_apply_apply] using second_branch hℏ ω t a j
    · simp only [Step.branch_zero, Finset.sum_const_zero]
  simp_rw [hx]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  exact secondState_sum ω t

theorem eventValue_add (X Y : FullMat Unit) : eventValue (X+Y) = eventValue X+eventValue Y := by
  simp [eventValue, Matrix.mul_add, Matrix.trace_add]

theorem eventValue_real_smul (c : ℝ) (X : FullMat Unit) :
    eventValue ((c:ℂ) • X) = c*eventValue X := by
  simp [eventValue, Matrix.mul_smul, Matrix.trace_smul, Complex.mul_re]

theorem finalState_event (ω t : ℝ) : eventValue (finalState ω t) = 1-FiniteClockHandReadout.p ω t/5 := by
  rw [finalState, eventValue_add, eventValue_real_smul, eventValue_real_smul,
    event_prepare 0 _ _ (FiniteClockHandReadout.Q_trace 0),
    event_prepare 1 _ _ (FiniteClockHandReadout.Q_trace 1)]
  rw [event0_entry, event0_entry, FiniteQutritRetainedClock.transfer_rho0]
  norm_num [FiniteQutritRetainedClock.rho0, projector]
  ring

theorem two_round_event {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (t : Duration)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) :
    terminalProbability Unit ω ℏ hℏ (twoPolicy hω t) (fun _ => event) (input σ) =
      1-FiniteClockHandReadout.p ω t/5 := by
  rw [terminalProbability, ← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum,
    two_round_sum hω hℏ t hσ]
  exact finalState_event ω t

theorem attained_left {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) :
    terminalProbability Unit ω ℏ hℏ (twoPolicy hω (leftDuration hω)) (fun _ => event) (input σ) = 19/20 := by
  rw [two_round_event hω hℏ _ hσ]
  change 1-FiniteClockHandReadout.p ω (Real.pi/(3*ω))/5 = _
  rw [FiniteClockHandReadout.p_left hω.ne']
  norm_num

theorem attained_right {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) :
    terminalProbability Unit ω ℏ hℏ (twoPolicy hω (rightDuration hω)) (fun _ => event) (input σ) = 17/20 := by
  rw [two_round_event hω hℏ _ hσ]
  change 1-FiniteClockHandReadout.p ω (2*Real.pi/(3*ω))/5 = _
  rw [FiniteClockHandReadout.p_right hω.ne']
  norm_num

theorem attained_gap {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) :
    terminalProbability Unit ω ℏ hℏ (twoPolicy hω (leftDuration hω)) (fun _ => event) (input σ) -
    terminalProbability Unit ω ℏ hℏ (twoPolicy hω (rightDuration hω)) (fun _ => event) (input σ) = 1/10 := by
  rw [attained_left hω hℏ hσ, attained_right hω hℏ hσ]
  norm_num

theorem event_distance {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (t s : Duration)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) :
    |terminalProbability Unit ω ℏ hℏ (twoPolicy hω t) (fun _ => event) (input σ) -
    terminalProbability Unit ω ℏ hℏ (twoPolicy hω s) (fun _ => event) (input σ)| =
      |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s|/5 := by
  rw [two_round_event hω hℏ _ hσ, two_round_event hω hℏ _ hσ]
  have he : (1-FiniteClockHandReadout.p ω t/5)-(1-FiniteClockHandReadout.p ω s/5) =
      -(FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s)/5 := by ring
  rw [he, abs_div, abs_neg]
  norm_num

theorem twoPolicy_errors {ω : ℝ} (hω : 0 < ω) (t s : Duration) {e : ℝ}
    (he : |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s| ≤ e) :
    PolicyErrors ω (twoPolicy hω t) (twoPolicy hω s) [0,e] := by
  apply PolicyErrors.node
  · simp
  · rfl
  · intro k
    exact .node he rfl (fun _ => .done)

theorem duration_error {ω : ℝ} (hω : 0 < ω) (t s : Duration)
    (ht : |(t:ℝ)-(s:ℝ)| ≤ 1/(100*ω)) :
    |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s| ≤ 1/200 := by
  have hb := FiniteClockHandReadout.calibration_upper hω.le (t:ℝ) (s:ℝ)
  have he : ω*(1/(100*ω))/2 = (1/200:ℝ) := by field_simp; ring
  exact hb.trans (he ▸ (mul_le_mul_of_nonneg_left ht hω.le |> fun h => div_le_div_of_nonneg_right h (by norm_num)))

theorem twoPolicy_event_error {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (t s : Duration) {e : ℝ} (he : |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s| ≤ e)
    {σ : FiniteClockHandReadout.Mat} (hσ : IsDensityOperator σ) :
    |terminalProbability Unit ω ℏ hℏ (twoPolicy hω t) (fun _ => event) (input σ) -
    terminalProbability Unit ω ℏ hℏ (twoPolicy hω s) (fun _ => event) (input σ)| ≤ e := by
  have hb := policy_event_error Unit hℏ (twoPolicy_errors hω t s he)
    (input_density hσ) (input_density hσ) (fun _ => event) (fun _ => event_effect)
  simp only [traceDist_self, List.sum_cons, List.sum_nil, add_zero, zero_add] at hb
  exact hb.trans (min_le_right _ _)

theorem noisy_gap {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (sL sR : Duration)
    (hL : |(leftDuration hω:ℝ)-(sL:ℝ)| ≤ 1/(100*ω))
    (hR : |(rightDuration hω:ℝ)-(sR:ℝ)| ≤ 1/(100*ω))
    {σ : FiniteClockHandReadout.Mat} (hσ : IsDensityOperator σ) :
    9/100 ≤ terminalProbability Unit ω ℏ hℏ (twoPolicy hω sL) (fun _ => event) (input σ) -
      terminalProbability Unit ω ℏ hℏ (twoPolicy hω sR) (fun _ => event) (input σ) := by
  have hleft := twoPolicy_event_error hω hℏ (leftDuration hω) sL (duration_error hω _ _ hL) hσ
  have hright := twoPolicy_event_error hω hℏ (rightDuration hω) sR (duration_error hω _ _ hR) hσ
  rw [attained_left hω hℏ hσ.2] at hleft
  rw [attained_right hω hℏ hσ.2] at hright
  have hl := (abs_le.mp hleft).2
  have hr := (abs_le.mp hright).1
  linarith

theorem noisy_order {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (sL sR : Duration)
    {eL eR : ℝ}
    (hL : |FiniteClockHandReadout.p ω (leftDuration hω)-FiniteClockHandReadout.p ω sL| ≤ eL)
    (hR : |FiniteClockHandReadout.p ω (rightDuration hω)-FiniteClockHandReadout.p ω sR| ≤ eR)
    (he : eL+eR < 1/10) {σ : FiniteClockHandReadout.Mat} (hσ : IsDensityOperator σ) :
    terminalProbability Unit ω ℏ hℏ (twoPolicy hω sR) (fun _ => event) (input σ) <
      terminalProbability Unit ω ℏ hℏ (twoPolicy hω sL) (fun _ => event) (input σ) := by
  have hleft := twoPolicy_event_error hω hℏ _ _ hL hσ
  have hright := twoPolicy_event_error hω hℏ _ _ hR hσ
  rw [attained_left hω hℏ hσ.2] at hleft
  rw [attained_right hω hℏ hσ.2] at hright
  have hl := (abs_le.mp hleft).2
  have hr := (abs_le.mp hright).1
  linarith

def feedbackDuration {ω : ℝ} (hω : 0 < ω) (previous : A) : Duration :=
  if previous=0 then leftDuration hω else rightDuration hω

def feedbackPolicy {ω : ℝ} (hω : 0 < ω) : (n : ℕ) → A → Policy n
  | 0, _ => .done
  | n+1, previous => .node (feedbackDuration hω previous)
      (fun k => feedbackPolicy hω n (outcomeEquiv.symm k).1)

def adaptivePolicy {ω : ℝ} (hω : 0 < ω) (n : ℕ) : Policy (n+1) :=
  .node (keepDuration hω) (fun k => feedbackPolicy hω n (outcomeEquiv.symm k).1)

def firstRecord : Fin 22 := outcomeEquiv (0,FiniteQutritRetainedClock.noneLabel)
def secondLeftRecord : Fin 22 := outcomeEquiv
  (0,FiniteQutritRetainedClock.someLabel (finProdFinEquiv ((0:Setting),(0:A))))
def secondRightRecord : Fin 22 := outcomeEquiv (1,FiniteQutritRetainedClock.noneLabel)

theorem adaptive_third_left {ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    durationAt (adaptivePolicy hω (n+2)) ((0 : Fin (n+1)).succ.succ) (firstRecord,secondLeftRecord,()) =
      leftDuration hω := by
  simp only [adaptivePolicy, durationAt, Fin.cases_succ, feedbackPolicy, Fin.cases_zero]
  simp [feedbackDuration, secondLeftRecord]

theorem adaptive_third_right {ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    durationAt (adaptivePolicy hω (n+2)) ((0 : Fin (n+1)).succ.succ) (firstRecord,secondRightRecord,()) =
      rightDuration hω := by
  simp only [adaptivePolicy, durationAt, Fin.cases_succ, feedbackPolicy, Fin.cases_zero]
  simp [feedbackDuration, secondRightRecord]

theorem adaptive_third_distinct {ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    durationAt (adaptivePolicy hω (n+2)) ((0 : Fin (n+1)).succ.succ) (firstRecord,secondLeftRecord,()) ≠
    durationAt (adaptivePolicy hω (n+2)) ((0 : Fin (n+1)).succ.succ) (firstRecord,secondRightRecord,()) := by
  rw [adaptive_third_left, adaptive_third_right]
  intro he
  have hv := congrArg Subtype.val he
  change Real.pi/(3*ω) = 2*Real.pi/(3*ω) at hv
  have hd : 0 < 3*ω := by positivity
  have hh := (div_lt_div_iff_of_pos_right hd).2 (show Real.pi < 2*Real.pi by linarith [Real.pi_pos])
  exact (ne_of_lt hh) hv

theorem adaptive_second_prefix {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) (k : Fin 22) :
    run S Unit 22 (policyTree Unit ω ℏ hℏ (adaptivePolicy hω 1))
      (firstRecord,k,()) (input σ) =
      secondState ω (leftDuration hω) (outcomeEquiv.symm k).1 (outcomeEquiv.symm k).2 := by
  obtain ⟨⟨a,i⟩,rfl⟩ := outcomeEquiv.surjective k
  change (step Unit ω ℏ (leftDuration hω) hℏ).branch S Unit 22 (outcomeEquiv (a,i))
    ((step Unit ω ℏ (Real.pi/ω) hℏ).branch S Unit 22 firstRecord (input σ)) = _
  rw [firstRecord, first_branch hω.ne' hℏ hσ, if_pos ⟨rfl,rfl⟩, second_branch]
  simp only [Equiv.symm_apply_apply]

theorem adaptive_prefix_weights {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) :
    (run S Unit 22 (policyTree Unit ω ℏ hℏ (adaptivePolicy hω 1))
      (firstRecord,secondLeftRecord,()) (input σ)).trace.re = 1/20 ∧
    (run S Unit 22 (policyTree Unit ω ℏ hℏ (adaptivePolicy hω 1))
      (firstRecord,secondRightRecord,()) (input σ)).trace.re = 3/4 := by
  rw [adaptive_second_prefix hω hℏ hσ, adaptive_second_prefix hω hℏ hσ]
  simp only [secondLeftRecord, secondRightRecord, Equiv.symm_apply_apply, secondState,
    if_pos rfl, FiniteQutritRetainedClock.someLabel, Equiv.symm_apply_apply,
    show (1:A) ≠ 0 by decide, if_false]
  simp only [ite_true]
  rw [Matrix.trace_smul, Matrix.trace_smul, insert_trace, insert_trace,
    FiniteClockHandReadout.Q_trace, FiniteClockHandReadout.Q_trace, mul_one, mul_one]
  simp only [prepareData, FiniteQutritRetainedClock.preparation_trace, unitQutrit,
    Matrix.trace_kronecker]
  rw [micro_pair]
  simp only [leftDuration, Subtype.coe_mk, FiniteClockHandReadout.p_left hω.ne']
  norm_num [microPair, FiniteQutritRetainedClock.rho0, projector, Matrix.trace,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.vecHead, Matrix.vecTail, show (2:Q) ≠ 0 by decide]

def implementedFeedback (left right : Duration) : (n : ℕ) → A → Policy n
  | 0, _ => .done
  | n+1, previous => .node (if previous=0 then left else right)
      (fun k => implementedFeedback left right n (outcomeEquiv.symm k).1)

def implementedAdaptive {ω : ℝ} (hω : 0 < ω) (left right : Duration) (n : ℕ) : Policy (n+1) :=
  .node (keepDuration hω) (fun k => implementedFeedback left right n (outcomeEquiv.symm k).1)

theorem feedback_errors {ω : ℝ} (hω : 0 < ω) (left right : Duration) {e : ℝ}
    (hL : |FiniteClockHandReadout.p ω (leftDuration hω)-FiniteClockHandReadout.p ω left| ≤ e)
    (hR : |FiniteClockHandReadout.p ω (rightDuration hω)-FiniteClockHandReadout.p ω right| ≤ e)
    (n : ℕ) (previous : A) :
    PolicyErrors ω (feedbackPolicy hω n previous) (implementedFeedback left right n previous)
      (List.replicate n e) := by
  induction n generalizing previous with
  | zero => exact .done
  | succ n ih =>
    apply PolicyErrors.node
    · unfold feedbackDuration
      split <;> assumption
    · simp
    · exact fun k => ih _

theorem adaptive_errors {ω : ℝ} (hω : 0 < ω) (left right : Duration) {e : ℝ}
    (hL : |FiniteClockHandReadout.p ω (leftDuration hω)-FiniteClockHandReadout.p ω left| ≤ e)
    (hR : |FiniteClockHandReadout.p ω (rightDuration hω)-FiniteClockHandReadout.p ω right| ≤ e)
    (n : ℕ) : PolicyErrors ω (adaptivePolicy hω n) (implementedAdaptive hω left right n)
      (0::List.replicate n e) :=
  .node (by simp) (by simp) (fun _ => feedback_errors hω left right hL hR n _)

theorem adaptive_same_event_error {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (left right : Duration) {e : ℝ}
    (hL : |FiniteClockHandReadout.p ω (leftDuration hω)-FiniteClockHandReadout.p ω left| ≤ e)
    (hR : |FiniteClockHandReadout.p ω (rightDuration hω)-FiniteClockHandReadout.p ω right| ≤ e)
    (n : ℕ) {σ : FiniteClockHandReadout.Mat} (hσ : IsDensityOperator σ) :
    |terminalProbability Unit ω ℏ hℏ (adaptivePolicy hω n) (fun _ => event) (input σ) -
      terminalProbability Unit ω ℏ hℏ (implementedAdaptive hω left right n) (fun _ => event) (input σ)| ≤
      min 1 (n*e) := by
  have hh := policy_event_error Unit hℏ (adaptive_errors hω left right hL hR n)
    (input_density hσ) (input_density hσ) (fun _ => event) (fun _ => event_effect)
  simpa only [traceDist_self, List.sum_cons, List.sum_replicate, nsmul_eq_mul, zero_add] using hh

theorem second_arm_trace {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) :
    (∑ i : Fin 11, (secondState ω t a i).trace.re) = FiniteClockHandReadout.mass ω t a := by
  simp_rw [← second_branch hℏ ω t a]
  simp_rw [branch_action, Matrix.trace_smul, insert_trace, FiniteClockHandReadout.Q_trace, mul_one]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    ← Finset.mul_sum, ← Complex.re_sum, dataBranch_sum_trace, handTrace_trace,
    afterFirst_density.2, Complex.one_re, mul_one]

theorem adaptive_second_marginals {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) :
    (∑ i : Fin 11, (run S Unit 22 (policyTree Unit ω ℏ hℏ (adaptivePolicy hω 1))
      (firstRecord,outcomeEquiv (0,i),()) (input σ)).trace.re) = 1/4 ∧
    (∑ i : Fin 11, (run S Unit 22 (policyTree Unit ω ℏ hℏ (adaptivePolicy hω 1))
      (firstRecord,outcomeEquiv (1,i),()) (input σ)).trace.re) = 3/4 := by
  simp_rw [adaptive_second_prefix hω hℏ hσ]
  simp only [Equiv.symm_apply_apply]
  rw [second_arm_trace hℏ, second_arm_trace hℏ]
  simp only [FiniteClockHandReadout.mass, if_pos rfl, show (1:A) ≠ 0 by decide, if_false,
    leftDuration, Subtype.coe_mk, FiniteClockHandReadout.p_left hω.ne']
  norm_num

theorem two_round_normalized {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (t : Duration)
    {σ : FiniteClockHandReadout.Mat} (hσ : IsDensityOperator σ) :
    (∀ h, 0 ≤ weight S Unit 22 (policyTree Unit ω ℏ hℏ (twoPolicy hω t)) h (input σ)) ∧
    (∑ h, weight S Unit 22 (policyTree Unit ω ℏ hℏ (twoPolicy hω t)) h (input σ)) = 1 :=
  normalized_weights S Unit 22 _ (input_density hσ)

private theorem output_zero {n : ℕ} (T U : Tree S Unit 22 n) :
    FiniteAdaptiveMapPerturbation.outputDistance S Unit 22 T U 0 0 = 0 := by
  simp [FiniteAdaptiveMapPerturbation.outputDistance, run_zero, traceNorm_zero]

theorem recorded_distance {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (t s : Duration)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) :
    FiniteAdaptiveMapPerturbation.outputDistance S Unit 22
      (policyTree Unit ω ℏ hℏ (twoPolicy hω t)) (policyTree Unit ω ℏ hℏ (twoPolicy hω s))
      (input σ) (input σ) = |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s| := by
  change FiniteAdaptiveMapPerturbation.outputDistance S Unit 22
    (.node (step Unit ω ℏ (Real.pi/ω) hℏ) (fun _ => .node (step Unit ω ℏ t hℏ) (fun _ => .done)))
    (.node (step Unit ω ℏ (Real.pi/ω) hℏ) (fun _ => .node (step Unit ω ℏ s hℏ) (fun _ => .done)))
    (input σ) (input σ) = _
  rw [FiniteAdaptiveMapPerturbation.outputDistance_node, ← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [first_branch hω.ne' hℏ hσ]
  have hx (a : A) (i : Fin 11) :
      FiniteAdaptiveMapPerturbation.outputDistance S Unit 22
        (.node (step Unit ω ℏ t hℏ) (fun _ => .done))
        (.node (step Unit ω ℏ s hℏ) (fun _ => .done))
        (if a=0 ∧ i=FiniteQutritRetainedClock.noneLabel then afterFirst else 0)
        (if a=0 ∧ i=FiniteQutritRetainedClock.noneLabel then afterFirst else 0) =
      if a=0 ∧ i=FiniteQutritRetainedClock.noneLabel then
        |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s| else 0 := by
    split
    · rw [FiniteAdaptiveMapPerturbation.outputDistance_one, stepDistance_exact Unit hℏ _ _ _ afterFirst_density.1,
        afterFirst_density.2, Complex.one_re, mul_one]
    · exact output_zero _ _
  simp_rw [hx]
  simp [Fin.sum_univ_two]

theorem first_marginal {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (t : Duration)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace = 1) (a : A) (i : Fin 11) :
    (∑ k : Fin 22, (run S Unit 22 (policyTree Unit ω ℏ hℏ (twoPolicy hω t))
      (outcomeEquiv (a,i),k,()) (input σ)).trace.re) =
      if a=0 ∧ i=FiniteQutritRetainedClock.noneLabel then 1 else 0 := by
  change (∑ k, ((step Unit ω ℏ t hℏ).branch S Unit 22 k
    ((step Unit ω ℏ (Real.pi/ω) hℏ).branch S Unit 22 (outcomeEquiv (a,i)) (input σ))).trace.re) = _
  rw [← Complex.re_sum, branches_trace, first_branch hω.ne' hℏ hσ]
  split <;> simp [afterFirst_density.2]

def dataChannel (p : ℝ) (X : DataMat) : DataMat :=
  (p:ℂ) • FiniteQutritRetainedClock.J X +
    ((1-p:ℝ):ℂ) • FiniteQutritRetainedClock.J (FiniteQutritRetainedClock.resetClock X)

theorem dataChannel_actual (p : ℝ) (X : DataMat) :
    (p:ℂ) • (∑ i, krausMap (dataKraus 0 i) X) +
      ((1-p:ℝ):ℂ) • (∑ i, krausMap (dataKraus 1 i) X) = dataChannel p X := by
  rw [data_action_keep, data_action_reset]
  rfl

theorem dataChannel_one (p : ℝ) : dataChannel p 1 =
    (p:ℂ) • 1 + (2*(1-p):ℂ) • ((1:Mat) ⊗ₖ FiniteQutritRetainedClock.P 1) := by
  rw [dataChannel, FiniteQutritRetainedClock.J_one, FiniteQutritRetainedClock.reset_one,
    map_smul]
  have he : FiniteQutritRetainedClock.J ((1:Mat) ⊗ₖ FiniteQutritRetainedClock.P 0) =
      (1:Mat) ⊗ₖ FiniteQutritRetainedClock.P 1 := FiniteQutritRetainedClock.J_embed_zero 1
  rw [he, smul_smul]
  congr 1
  push_cast
  ring

theorem dataChannel_not_unital {p : ℝ} (hp : p < 1) : dataChannel p 1 ≠ 1 := by
  intro he
  have hh := congrFun (congrFun he ((0:Q),(0:A))) ((0:Q),(0:A))
  rw [dataChannel_one] at hh
  have he' : (p:ℂ)=1 := by
    simpa [Matrix.one_apply, FiniteQutritRetainedClock.P, FiniteQutritRetainedClock.e, Matrix.single] using hh
  have := congrArg Complex.re he'
  norm_num at this
  linarith

variable (F : Type*) [Fintype F] [DecidableEq F]

theorem unit_mass_branch {ω ℏ t : ℝ} (hℏ : ℏ ≠ 0) (hp : FiniteClockHandReadout.p ω t=1)
    (a : A) (i : Fin 11) (Z : FullMat F) :
    (step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z =
      if a=0 then insert F
        ((localStep B F 11 FiniteQutritRetainedClock.instrument).branch B F 11 i (handTrace F Z))
        (FiniteClockHandReadout.Q 0) else 0 := by
  rw [branch_action]
  rcases bit_cases a with rfl | rfl <;>
    simp [FiniteClockHandReadout.mass, hp, dataBranch_keep]

theorem unit_mass_run {ω ℏ t : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (ht : 0 ≤ t) (hp : FiniteClockHandReadout.p ω t=1) (n : ℕ) (h : History 22 n) (Z : FullMat F) :
    run S F 22 (policyTree F ω ℏ hℏ (constantPolicy ⟨t,ht⟩ n)) h Z =
      run S F 22 (keepTree F ω ℏ hℏ n) h Z := by
  induction n generalizing Z with
  | zero => rfl
  | succ n ih =>
    rcases h with ⟨k,h⟩
    obtain ⟨⟨a,i⟩,rfl⟩ := outcomeEquiv.surjective k
    change run S F 22 (policyTree F ω ℏ hℏ (constantPolicy ⟨t,ht⟩ n)) h
      ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z) =
      run S F 22 (keepTree F ω ℏ hℏ n) h
        ((step F ω ℏ (Real.pi/ω) hℏ).branch S F 22 (outcomeEquiv (a,i)) Z)
    rw [ih, unit_mass_branch F hℏ hp, keep_branch F hω hℏ]

def aliasTime (ω : ℝ) (k : ℕ) : ℝ := Real.pi/ω + k*(2*Real.pi/ω)

theorem aliasTime_nonneg {ω : ℝ} (hω : 0 < ω) (k : ℕ) : 0 ≤ aliasTime ω k := by
  unfold aliasTime
  positivity

theorem alias_injected_run {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (k n : ℕ) (h : History 11 (n+1)) (Z : FullMat F) :
    run S F 22 (policyTree F ω ℏ hℏ
      (constantPolicy ⟨aliasTime ω k,aliasTime_nonneg hω k⟩ (n+1))) (injectRecord (n+1) h) Z =
      insert F (run B F 11 (FiniteQutritRetainedClock.recordTree F (n+1)) h (handTrace F Z))
        (FiniteClockHandReadout.Q 0) := by
  rw [unit_mass_run F (t:=aliasTime ω k) hω.ne' hℏ (aliasTime_nonneg hω k) (FiniteClockHandReadout.keep_alias hω.ne' k)]
  exact injected_run F hω.ne' hℏ n h Z

theorem alias_forbidden_run {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (k n : ℕ) (h : History 22 n) (hn : h ∉ Set.range (injectRecord n)) (Z : FullMat F) :
    run S F 22 (policyTree F ω ℏ hℏ
      (constantPolicy ⟨aliasTime ω k,aliasTime_nonneg hω k⟩ n)) h Z = 0 := by
  rw [unit_mass_run F (t:=aliasTime ω k) hω.ne' hℏ (aliasTime_nonneg hω k) (FiniteClockHandReadout.keep_alias hω.ne' k)]
  exact forbidden_run F hω.ne' hℏ n h hn Z

theorem alias_recovery {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (k n : ℕ) (Z : FullMat F) :
    handTrace F (∑ h, run S F 22 (policyTree F ω ℏ hℏ
      (constantPolicy ⟨aliasTime ω k,aliasTime_nonneg hω k⟩ (n+1))) h Z) =
      FiniteQutritRetainedClock.amplifiedJointIterate F (n+1) (handTrace F Z) := by
  simp_rw [unit_mass_run F (t:=aliasTime ω k) hω.ne' hℏ (aliasTime_nonneg hω k) (FiniteClockHandReadout.keep_alias hω.ne' k)]
  exact keep_reduced_records F hω.ne' hℏ n Z

def cycle (ω ℏ t : ℝ) (hℏ : ℏ ≠ 0) (Z : FullMat F) : FullMat F :=
  ∑ k : Fin 22, (step F ω ℏ t hℏ).branch S F 22 k Z

theorem dataBranch_keep_sum (Y : ReducedMat F) :
    (∑ i, dataBranch F 0 i Y) = FiniteQutritRetainedClock.amplified F Y := by
  simp only [dataBranch_keep, FiniteQutritRetainedClock.record_branch]
  rfl

theorem dataBranch_reset_sum (Y : ReducedMat F) :
    (∑ i, dataBranch F 1 i Y) = FiniteQutritRetainedClock.amplified F
      (krausMap (fun c => FiniteQutritRetainedClock.L c ⊗ₖ (1 : Matrix F F ℂ)) Y) := by
  simp only [dataBranch_reset, FiniteQutritRetainedClock.record_branch]
  rfl

theorem cycle_insert {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (Y : ReducedMat F)
    (σ : FiniteClockHandReadout.Mat) (hσ : σ.trace=1) :
    cycle F ω ℏ t hℏ (insert F Y σ) =
      (FiniteClockHandReadout.p ω t:ℂ) • insert F (FiniteQutritRetainedClock.amplified F Y)
        (FiniteClockHandReadout.Q 0) +
      ((1-FiniteClockHandReadout.p ω t:ℝ):ℂ) • insert F
        (FiniteQutritRetainedClock.amplified F
          (krausMap (fun c => FiniteQutritRetainedClock.L c ⊗ₖ (1 : Matrix F F ℂ)) Y))
        (FiniteClockHandReadout.Q 1) := by
  rw [cycle, ← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, branch_action, handTrace_insert, hσ, one_smul,
    Fin.sum_univ_two, FiniteClockHandReadout.mass, if_pos rfl,
    show (1:A) ≠ 0 by decide, if_false]
  rw [← Finset.smul_sum, ← Finset.smul_sum, ← insert_sum, ← insert_sum,
    dataBranch_keep_sum, dataBranch_reset_sum]
  simp only [ite_true]

theorem cycle_add {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (X Y : FullMat F) :
    cycle F ω ℏ t hℏ (X+Y) = cycle F ω ℏ t hℏ X+cycle F ω ℏ t hℏ Y := by
  simp [cycle, Step.branch_add, Finset.sum_add_distrib]

theorem cycle_smul {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (c : ℂ) (X : FullMat F) :
    cycle F ω ℏ t hℏ (c • X) = c • cycle F ω ℏ t hℏ X := by
  simp [cycle, Step.branch_smul, Finset.smul_sum]

omit [Fintype F] [DecidableEq F] in
 theorem prepareData_tensor (c : A) (X : Mat) : prepareData c X =
    FiniteQutritRetainedClock.embedClock c X ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
  ext ⟨⟨s,a⟩,f⟩ ⟨⟨t,b⟩,g⟩
  cases f; cases g
  simp [prepareData_entry, FiniteQutritRetainedClock.embedClock]

theorem amplified_prepare_zero (X : Mat) :
    FiniteQutritRetainedClock.amplified Unit (prepareData 0 X) = prepareData 1 X := by
  rw [prepareData_tensor, FiniteQutritRetainedClock.amplified_product,
    show FiniteQutritRetainedClock.J (FiniteQutritRetainedClock.embedClock 0 X) =
      FiniteQutritRetainedClock.embedClock 1 X from FiniteQutritRetainedClock.J_embed_zero X,
    prepareData_tensor]

theorem amplified_prepare_one (X : Mat) :
    FiniteQutritRetainedClock.amplified Unit (prepareData 1 X) =
      prepareData 0 (FiniteQutritAveragedTransfer.transfer X) := by
  rw [prepareData_tensor, FiniteQutritRetainedClock.amplified_product,
    FiniteQutritRetainedClock.J_embed_one, prepareData_tensor]
  rfl

theorem cycle_prepare_zero {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) (t : ℝ) (X : Mat)
    (σ : FiniteClockHandReadout.Mat) (hσ : σ.trace=1) :
    cycle Unit ω ℏ t hℏ (insert Unit (prepareData 0 X) σ) =
      (FiniteClockHandReadout.p ω t:ℂ) • insert Unit (prepareData 1 X) (FiniteClockHandReadout.Q 0) +
      ((1-FiniteClockHandReadout.p ω t:ℝ):ℂ) • insert Unit (prepareData 1 X) (FiniteClockHandReadout.Q 1) := by
  rw [cycle_insert Unit hℏ _ _ _ _ hσ, FiniteQutritRetainedClock.reset_amplified_action,
    old_reduce_prepare]
  change _ = _
  rw [show FiniteQutritRetainedClock.amplifiedPreparation Unit 0 (unitQutrit X) =
      prepareData 0 X from rfl, amplified_prepare_zero]

theorem cycle_prepare_one {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) (t : ℝ) (X : Mat)
    (σ : FiniteClockHandReadout.Mat) (hσ : σ.trace=1) :
    cycle Unit ω ℏ t hℏ (insert Unit (prepareData 1 X) σ) =
      (FiniteClockHandReadout.p ω t:ℂ) •
        insert Unit (prepareData 0 (FiniteQutritAveragedTransfer.transfer X)) (FiniteClockHandReadout.Q 0) +
      ((1-FiniteClockHandReadout.p ω t:ℝ):ℂ) • insert Unit (prepareData 1 X) (FiniteClockHandReadout.Q 1) := by
  rw [cycle_insert Unit hℏ _ _ _ _ hσ, FiniteQutritRetainedClock.reset_amplified_action,
    old_reduce_prepare]
  rw [show FiniteQutritRetainedClock.amplifiedPreparation Unit 0 (unitQutrit X) =
      prepareData 0 X from rfl, amplified_prepare_zero, amplified_prepare_one]


theorem first_controlled_event {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) (t : ℝ)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace=1) :
    eventValue (cycle Unit ω ℏ t hℏ (input σ)) = 1 := by
  rw [input, cycle_prepare_zero hℏ _ _ _ hσ, eventValue_add,
    eventValue_real_smul, eventValue_real_smul,
    event_prepare 1 _ _ (FiniteClockHandReadout.Q_trace 0),
    event_prepare 1 _ _ (FiniteClockHandReadout.Q_trace 1), event0_entry]
  norm_num [FiniteQutritRetainedClock.rho0, projector]

theorem keep_then_controlled {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (t : ℝ)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace=1) :
    cycle Unit ω ℏ t hℏ (cycle Unit ω ℏ (Real.pi/ω) hℏ (input σ)) = finalState ω t := by
  rw [input, cycle_prepare_zero hℏ _ _ _ hσ]
  simp only [FiniteClockHandReadout.p_keep hω, Complex.ofReal_one, one_smul,
    sub_self, Complex.ofReal_zero, zero_smul, add_zero]
  rw [cycle_prepare_one hℏ _ _ _ (FiniteClockHandReadout.Q_trace 0)]
  rfl

theorem controlled_then_keep {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (t : ℝ)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace=1) :
    cycle Unit ω ℏ (Real.pi/ω) hℏ (cycle Unit ω ℏ t hℏ (input σ)) =
      insert Unit (prepareData 0 (FiniteQutritAveragedTransfer.transfer FiniteQutritRetainedClock.rho0))
        (FiniteClockHandReadout.Q 0) := by
  rw [input, cycle_prepare_zero hℏ _ _ _ hσ, cycle_add, cycle_smul, cycle_smul,
    cycle_prepare_one hℏ _ _ _ (FiniteClockHandReadout.Q_trace 0),
    cycle_prepare_one hℏ _ _ _ (FiniteClockHandReadout.Q_trace 1)]
  simp only [FiniteClockHandReadout.p_keep hω, Complex.ofReal_one, one_smul,
    sub_self, Complex.ofReal_zero, zero_smul, add_zero]
  rw [← add_smul]
  norm_num

theorem controlled_then_keep_event {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (t : ℝ)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace=1) :
    eventValue (cycle Unit ω ℏ (Real.pi/ω) hℏ (cycle Unit ω ℏ t hℏ (input σ))) = 4/5 := by
  rw [controlled_then_keep hω hℏ t hσ, event_prepare 0 _ _ (FiniteClockHandReadout.Q_trace 0),
    event0_entry, FiniteQutritRetainedClock.transfer_rho0]
  norm_num

theorem full_turn_zero {ω : ℝ} (hω : ω ≠ 0) : FiniteClockHandReadout.p ω (2*Real.pi/ω)=0 := by
  simpa only [zero_add, FiniteClockHandReadout.p_zero] using FiniteClockHandReadout.p_periodic hω 0

theorem zero_mass_two_cycles {ω ℏ t : ℝ} (hℏ : ℏ ≠ 0) (hp : FiniteClockHandReadout.p ω t=0)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace=1) :
    cycle Unit ω ℏ t hℏ (cycle Unit ω ℏ t hℏ (input σ)) =
      insert Unit (prepareData 1 FiniteQutritRetainedClock.rho0) (FiniteClockHandReadout.Q 1) := by
  rw [input, cycle_prepare_zero hℏ _ _ _ hσ]
  simp only [hp, Complex.ofReal_zero, zero_smul, sub_zero, Complex.ofReal_one, one_smul, zero_add]
  rw [cycle_prepare_one hℏ _ _ _ (FiniteClockHandReadout.Q_trace 1)]
  simp only [hp, Complex.ofReal_zero, zero_smul, sub_zero, Complex.ofReal_one, one_smul, zero_add]

theorem zero_mass_not_free {ω ℏ t : ℝ} (hℏ : ℏ ≠ 0) (hp : FiniteClockHandReadout.p ω t=0)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace=1) :
    cycle Unit ω ℏ t hℏ (cycle Unit ω ℏ t hℏ (input σ)) ≠
      insert Unit (prepareData 0 (FiniteQutritAveragedTransfer.transfer FiniteQutritRetainedClock.rho0))
        (FiniteClockHandReadout.Q 0) := by
  intro he
  have hh := congrArg eventValue he
  rw [zero_mass_two_cycles hℏ hp hσ,
    event_prepare 1 _ _ (FiniteClockHandReadout.Q_trace 1),
    event_prepare 0 _ _ (FiniteClockHandReadout.Q_trace 0),
    event0_entry, event0_entry, FiniteQutritRetainedClock.transfer_rho0] at hh
  norm_num [FiniteQutritRetainedClock.rho0, projector] at hh

theorem insert_tensor (X : DataMat) (σ : FiniteClockHandReadout.Mat) :
    insert Unit (X ⊗ₖ (1 : Matrix Unit Unit ℂ)) σ =
      (X ⊗ₖ σ) ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
  ext ⟨⟨b,u⟩,f⟩ ⟨⟨d,w⟩,g⟩
  cases f; cases g
  simp [FiniteClockControlledRetainedMemory.insert]

def resetOld (Z : FullMat Unit) : FullMat Unit :=
  krausMap (fun c : A => (FiniteQutritRetainedClock.L c ⊗ₖ (1 : Matrix A A ℂ)) ⊗ₖ
    (1 : Matrix Unit Unit ℂ)) Z

theorem resetOld_tensor (X : DataMat) (σ : FiniteClockHandReadout.Mat) :
    resetOld ((X ⊗ₖ σ) ⊗ₖ (1 : Matrix Unit Unit ℂ)) =
      (FiniteQutritRetainedClock.resetClock X ⊗ₖ σ) ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
  rw [← FiniteQutritRetainedClock.reset_kraus_action]
  simp only [resetOld, krausMap, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  ext ⟨⟨b,u⟩,f⟩ ⟨⟨d,w⟩,g⟩
  simp [Matrix.sum_apply, Finset.sum_mul]
  ring

theorem resetOld_prepare (c : A) (X : Mat) (σ : FiniteClockHandReadout.Mat) :
    resetOld (insert Unit (prepareData c X) σ) = insert Unit (prepareData 0 X) σ := by
  rw [prepareData_tensor, insert_tensor, resetOld_tensor, prepareData_tensor, insert_tensor]
  change ((FiniteQutritRetainedClock.E0
    (FiniteQutritRetainedClock.D (FiniteQutritRetainedClock.embedClock c X))) ⊗ₖ σ) ⊗ₖ 1 = _
  rw [FiniteQutritRetainedClock.D_embed]
  rfl

theorem resetOld_add (X Y : FullMat Unit) : resetOld (X+Y)=resetOld X+resetOld Y := krausMap_add _ _ _
theorem resetOld_smul (c : ℂ) (X : FullMat Unit) : resetOld (c • X)=c • resetOld X := krausMap_smul _ _ _

theorem reset_before_both_event {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) (t s : ℝ)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace=1) :
    eventValue (cycle Unit ω ℏ s hℏ (resetOld (cycle Unit ω ℏ t hℏ (resetOld (input σ))))) = 1 := by
  rw [input, resetOld_prepare, cycle_prepare_zero hℏ _ _ _ hσ,
    resetOld_add, resetOld_smul, resetOld_smul, resetOld_prepare, resetOld_prepare,
    cycle_add, cycle_smul, cycle_smul]
  rw [show (insert Unit (prepareData 0 FiniteQutritRetainedClock.rho0) (FiniteClockHandReadout.Q 0)) =
      input (FiniteClockHandReadout.Q 0) from rfl,
    show (insert Unit (prepareData 0 FiniteQutritRetainedClock.rho0) (FiniteClockHandReadout.Q 1)) =
      input (FiniteClockHandReadout.Q 1) from rfl]
  rw [eventValue_add, eventValue_real_smul, eventValue_real_smul,
    first_controlled_event hℏ s (FiniteClockHandReadout.Q_trace 0),
    first_controlled_event hℏ s (FiniteClockHandReadout.Q_trace 1)]
  ring

def keptData (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) (n : ℕ) (Y : ReducedMat F) : ReducedMat F :=
  handTrace F (∑ h, run S F 22 (keepTree F ω ℏ hℏ n) h
    (insert F Y FiniteClockHandReadout.rhoPlus))

theorem keptData_old {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (n : ℕ) (Y : ReducedMat F) :
    keptData F ω ℏ hℏ n Y = FiniteQutritRetainedClock.amplifiedJointIterate F n Y := by
  cases n with
  | zero =>
    simp [keptData, keepTree, run, history_card, handTrace_insert, FiniteClockHandReadout.rhoPlus_density.2,
      FiniteQutritRetainedClock.amplifiedJointIterate]
  | succ n =>
    rw [keptData, keep_reduced_records F hω hℏ, handTrace_insert,
      FiniteClockHandReadout.rhoPlus_density.2, one_smul]

theorem recovered_even {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (n : ℕ)
    (Y : Matrix (Q × F) (Q × F) ℂ) :
    FiniteQutritRetainedClock.amplifiedReduction F
      (keptData F ω ℏ hℏ (2*n) (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y)) =
      FiniteQutritAveragedTransfer.amplifiedIterate F n Y := by
  rw [keptData_old F hω hℏ, FiniteQutritRetainedClock.spectator_reduced_even]

theorem recovered_odd {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (n : ℕ)
    (Y : Matrix (Q × F) (Q × F) ℂ) :
    FiniteQutritRetainedClock.amplifiedReduction F
      (keptData F ω ℏ hℏ (2*n+1) (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y)) =
      FiniteQutritAveragedTransfer.amplifiedIterate F n Y := by
  rw [keptData_old F hω hℏ, FiniteQutritRetainedClock.spectator_reduced_odd]

theorem positive_injected_run {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (h : History 11 m) (Z : FullMat F) :
    run S F 22 (keepTree F ω ℏ hℏ m) (injectRecord m h) Z =
      insert F (run B F 11 (FiniteQutritRetainedClock.recordTree F m) h (handTrace F Z))
        (FiniteClockHandReadout.Q 0) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  exact injected_run F hω hℏ n h Z

theorem recovered_even_record {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (h : History 10 n) (Y : Matrix (Q × F) (Q × F) ℂ)
    (σ : FiniteClockHandReadout.Mat) (hσ : σ.trace=1) :
    run S F 22 (keepTree F ω ℏ hℏ (2*n))
      (injectRecord (2*n) (FiniteQutritRetainedClock.evenRecord n h))
      (insert F (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y) σ) =
    insert F (FiniteQutritRetainedClock.amplifiedPreparation F 0
      (run Q F 10 (FiniteQutritAveragedTransfer.recordTree F n) h Y)) (FiniteClockHandReadout.Q 0) := by
  rw [positive_injected_run F hω hℏ _ (by omega), handTrace_insert, hσ, one_smul,
    FiniteQutritRetainedClock.permitted_even_branch]

theorem recovered_odd_record {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (n : ℕ) (h : History 10 n) (Y : Matrix (Q × F) (Q × F) ℂ)
    (σ : FiniteClockHandReadout.Mat) (hσ : σ.trace=1) :
    run S F 22 (keepTree F ω ℏ hℏ (2*n+1))
      (injectRecord (2*n+1) (FiniteQutritRetainedClock.oddRecord n h))
      (insert F (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y) σ) =
    insert F (FiniteQutritRetainedClock.amplifiedPreparation F 1
      (run Q F 10 (FiniteQutritAveragedTransfer.recordTree F n) h Y)) (FiniteClockHandReadout.Q 0) := by
  rw [positive_injected_run F hω hℏ _ (by omega), handTrace_insert, hσ, one_smul,
    FiniteQutritRetainedClock.permitted_odd_branch]

theorem recovered_forbidden_even {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (h : History 11 (2*n)) (hh : h ∉ Set.range (FiniteQutritRetainedClock.evenRecord n))
    (Y : Matrix (Q × F) (Q × F) ℂ) (σ : FiniteClockHandReadout.Mat) (hσ : σ.trace=1) :
    run S F 22 (keepTree F ω ℏ hℏ (2*n)) (injectRecord (2*n) h)
      (insert F (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y) σ) = 0 := by
  rw [positive_injected_run F hω hℏ _ (by omega), handTrace_insert, hσ, one_smul,
    FiniteQutritRetainedClock.forbidden_even_branch F n h hh]
  ext x y
  simp [FiniteClockControlledRetainedMemory.insert]

theorem recovered_forbidden_odd {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (n : ℕ) (h : History 11 (2*n+1)) (hh : h ∉ Set.range (FiniteQutritRetainedClock.oddRecord n))
    (Y : Matrix (Q × F) (Q × F) ℂ) (σ : FiniteClockHandReadout.Mat) (hσ : σ.trace=1) :
    run S F 22 (keepTree F ω ℏ hℏ (2*n+1)) (injectRecord (2*n+1) h)
      (insert F (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y) σ) = 0 := by
  rw [positive_injected_run F hω hℏ _ (by omega), handTrace_insert, hσ, one_smul,
    FiniteQutritRetainedClock.forbidden_odd_branch F n h hh]
  ext x y
  simp [FiniteClockControlledRetainedMemory.insert]

def recoveredJoint (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) (n : ℕ) (X : DataMat) : DataMat :=
  Matrix.of (fun b d => keptData Unit ω ℏ hℏ n (X ⊗ₖ (1 : Matrix Unit Unit ℂ)) (b,()) (d,()))

theorem recoveredJoint_old {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (n : ℕ) (X : DataMat) :
    recoveredJoint ω ℏ hℏ n X = FiniteQutritRetainedClock.jointIterate n X := by
  unfold recoveredJoint
  rw [keptData_old Unit hω hℏ, FiniteQutritRetainedClock.amplified_iterate_product]
  ext b d
  simp

theorem recovered_quotient_even {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (n : ℕ) (q : FiniteQutritInvariantReconstruction.FeatureSpace) :
    FiniteQutritRetainedClock.D (recoveredJoint ω ℏ hℏ (2*n)
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q))) =
      FiniteQutritInvariantReconstruction.U (FiniteQutritAveragedTransfer.quotientIterate n q) := by
  rw [recoveredJoint_old hω hℏ, FiniteQutritRetainedClock.quotient_even]

theorem recovered_quotient_odd {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (n : ℕ) (q : FiniteQutritInvariantReconstruction.FeatureSpace) :
    FiniteQutritRetainedClock.D (recoveredJoint ω ℏ hℏ (2*n+1)
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q))) =
      FiniteQutritInvariantReconstruction.U (FiniteQutritAveragedTransfer.quotientIterate n q) := by
  rw [recoveredJoint_old hω hℏ, FiniteQutritRetainedClock.quotient_odd]

theorem recovered_quotient_physical {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (n : ℕ) {q : FiniteQutritInvariantReconstruction.FeatureSpace}
    (hq : q ∈ FiniteQutritInvariantReconstruction.density) :
    IsDensityOperator (recoveredJoint ω ℏ hℏ (2*n)
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q))) ∧
    FiniteQutritRetainedClock.clockMarginal (recoveredJoint ω ℏ hℏ (2*n)
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q))) = FiniteQutritRetainedClock.P 0 ∧
    IsDensityOperator (recoveredJoint ω ℏ hℏ (2*n+1)
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q))) ∧
    FiniteQutritRetainedClock.clockMarginal (recoveredJoint ω ℏ hℏ (2*n+1)
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q))) = FiniteQutritRetainedClock.P 1 := by
  rw [recoveredJoint_old hω hℏ, recoveredJoint_old hω hℏ]
  exact ⟨(FiniteQutritRetainedClock.quotient_physical_even n hq).1,
    (FiniteQutritRetainedClock.quotient_physical_even n hq).2,
    (FiniteQutritRetainedClock.quotient_physical_odd n hq).1,
    (FiniteQutritRetainedClock.quotient_physical_odd n hq).2⟩

theorem recovered_arbitrary_even {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (X : DataMat) :
    recoveredJoint ω ℏ hℏ (2*n) X =
      FiniteQutritRetainedClock.E0 (FiniteQutritAveragedTransfer.iterate n (FiniteQutritRetainedClock.block X 0 0)) +
      FiniteQutritRetainedClock.embedClock 1
        (FiniteQutritAveragedTransfer.iterate n (FiniteQutritRetainedClock.block X 1 1)) := by
  rw [recoveredJoint_old hω hℏ, FiniteQutritRetainedClock.arbitrary_even n hn]

theorem recovered_arbitrary_odd {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (n : ℕ) (X : DataMat) :
    recoveredJoint ω ℏ hℏ (2*n+1) X =
      FiniteQutritRetainedClock.embedClock 1
        (FiniteQutritAveragedTransfer.iterate n (FiniteQutritRetainedClock.block X 0 0)) +
      FiniteQutritRetainedClock.E0
        (FiniteQutritAveragedTransfer.iterate (n+1) (FiniteQutritRetainedClock.block X 1 1)) := by
  rw [recoveredJoint_old hω hℏ, FiniteQutritRetainedClock.arbitrary_odd]

theorem recovered_reset_gap {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) :
    |FiniteQutritRetainedClock.event0 (FiniteQutritRetainedClock.D
      (recoveredJoint ω ℏ hℏ 2 (FiniteQutritRetainedClock.E0 FiniteQutritRetainedClock.rho0))) -
      FiniteQutritRetainedClock.event0 (FiniteQutritRetainedClock.D
        (recoveredJoint ω ℏ hℏ 1 (FiniteQutritRetainedClock.resetClock
          (recoveredJoint ω ℏ hℏ 1 (FiniteQutritRetainedClock.E0 FiniteQutritRetainedClock.rho0)))))| = 1/5 := by
  simp only [recoveredJoint_old hω hℏ]
  exact FiniteQutritRetainedClock.attained_gap

theorem recovered_nine_probe_defect {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) :
    ∃ k : FiniteQutritRetainedClock.ProbeLabel,
      IsDensityOperator (FiniteQutritRetainedClock.densityProbe k) ∧
      IsDensityOperator (insert Unit (prepareData 0 (FiniteQutritRetainedClock.densityProbe k))
        FiniteClockHandReadout.rhoPlus) ∧
      FiniteQutritRetainedClock.E0 (FiniteQutritRetainedClock.D
        (recoveredJoint ω ℏ hℏ 1 (FiniteQutritRetainedClock.E0 (FiniteQutritRetainedClock.densityProbe k)))) ≠
      recoveredJoint ω ℏ hℏ 1 (FiniteQutritRetainedClock.E0 (FiniteQutritRetainedClock.densityProbe k)) := by
  have ht : FiniteQutritRetainedClock.D.comp (FiniteQutritRetainedClock.J.comp
      (FiniteQutritRetainedClock.J.comp FiniteQutritRetainedClock.E0)) = FiniteQutritAveragedTransfer.transfer := by
    ext X s t
    have h := FiniteQutritRetainedClock.reduced_even 1 X
    exact congrFun (congrFun h s) t
  obtain ⟨k,hk,hd⟩ := FiniteQutritRetainedClock.generic_density_defect
    FiniteQutritRetainedClock.J FiniteQutritRetainedClock.E0 FiniteQutritRetainedClock.D
    (fun _ h => FiniteQutritRetainedClock.J_positive h)
    (fun _ h => FiniteQutritRetainedClock.embed_positive 0 h)
    (fun _ h => FiniteQutritRetainedClock.D_positive h) ht
  refine ⟨k,hk,?_,?_⟩
  · have hD := prepareData_density 0 hk
    exact ⟨insert_positive Unit hD.1 FiniteClockHandReadout.rhoPlus_density.1,
      by rw [insert_trace, hD.2, FiniteClockHandReadout.rhoPlus_density.2, one_mul]⟩
  · rw [recoveredJoint_old hω hℏ]
    exact hd

def truncatePolicy : {n : ℕ} → Policy n → (k : ℕ) → k ≤ n → Policy k
  | _, _, 0, _ => .done
  | 0, .done, k+1, h => False.elim (Nat.not_succ_le_zero k h)
  | _+1, .node t next, k+1, h => .node t
      (fun a => truncatePolicy (next a) k (Nat.le_of_succ_le_succ h))

theorem adaptive_prefix_truncation {ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    truncatePolicy (adaptivePolicy hω (n+2)) 2 (by omega) = adaptivePolicy hω 1 := by
  rfl

theorem adaptive_full_reachable {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (n : ℕ)
    {σ : FiniteClockHandReadout.Mat} (hσ : σ.trace=1) :
    0 < (run S Unit 22 (policyTree Unit ω ℏ hℏ
      (truncatePolicy (adaptivePolicy hω (n+2)) 2 (by omega)))
      (firstRecord,secondLeftRecord,()) (input σ)).trace.re ∧
    0 < (run S Unit 22 (policyTree Unit ω ℏ hℏ
      (truncatePolicy (adaptivePolicy hω (n+2)) 2 (by omega)))
      (firstRecord,secondRightRecord,()) (input σ)).trace.re ∧
    durationAt (adaptivePolicy hω (n+2)) ((0 : Fin (n+1)).succ.succ)
      (firstRecord,secondLeftRecord,()) ≠
    durationAt (adaptivePolicy hω (n+2)) ((0 : Fin (n+1)).succ.succ)
      (firstRecord,secondRightRecord,()) := by
  rw [adaptive_prefix_truncation]
  have hh := adaptive_prefix_weights hω hℏ hσ
  exact ⟨by rw [hh.1]; norm_num, by rw [hh.2]; norm_num, adaptive_third_distinct hω n⟩

def newEvenRecord (n : ℕ) (h : History 10 n) : History 22 (2*n) :=
  injectRecord (2*n) (FiniteQutritRetainedClock.evenRecord n h)
def newOddRecord (n : ℕ) (h : History 10 n) : History 22 (2*n+1) :=
  injectRecord (2*n+1) (FiniteQutritRetainedClock.oddRecord n h)

def newEvenPatternEquiv (n : ℕ) : History 10 n ≃ Set.range (newEvenRecord n) :=
  Equiv.ofInjective _ ((injectRecord_injective (2*n)).comp
    (FiniteQutritRetainedClock.evenRecord_injective n))
def newOddPatternEquiv (n : ℕ) : History 10 n ≃ Set.range (newOddRecord n) :=
  Equiv.ofInjective _ ((injectRecord_injective (2*n+1)).comp
    (FiniteQutritRetainedClock.oddRecord_injective n))

instance newEvenPatternFintype (n : ℕ) : Fintype (Set.range (newEvenRecord n)) :=
  Fintype.ofEquiv _ (newEvenPatternEquiv n)
instance newOddPatternFintype (n : ℕ) : Fintype (Set.range (newOddRecord n)) :=
  Fintype.ofEquiv _ (newOddPatternEquiv n)

theorem new_even_pattern_card (n : ℕ) : Fintype.card (Set.range (newEvenRecord n)) = 10^n := by
  rw [← Fintype.card_congr (newEvenPatternEquiv n)]
  exact history_card 10 n

theorem new_odd_pattern_card (n : ℕ) : Fintype.card (Set.range (newOddRecord n)) = 10^n := by
  rw [← Fintype.card_congr (newOddPatternEquiv n)]
  exact history_card 10 n

theorem policy_aggregate_density {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} (P : Policy n)
    {Z : FullMat F} (hZ : IsDensityOperator Z) :
    IsDensityOperator (∑ h, run S F 22 (policyTree F ω ℏ hℏ P) h Z) := by
  refine ⟨Matrix.posSemidef_sum _ (fun h _ => run_posSemidef S F 22 _ h hZ.1), ?_⟩
  rw [Matrix.trace_sum, sum_trace, hZ.2]

theorem finalState_density {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (t : Duration) :
    IsDensityOperator (finalState ω t) := by
  rw [← two_round_sum hω hℏ t FiniteClockHandReadout.rhoPlus_density.2]
  exact policy_aggregate_density Unit hℏ _ (input_density FiniteClockHandReadout.rhoPlus_density)

theorem empty_spectator_no_density (Z : FullMat Empty) : ¬IsDensityOperator Z := by
  intro hz
  have ht : Z.trace=0 := by simp [Matrix.trace]
  have hh := hz.2
  rw [ht] at hh
  exact zero_ne_one hh

theorem identical_policy_error {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} (P : Policy n)
    {Z : FullMat F} (hZ : IsDensityOperator Z) (e : History 22 n → FullMat F) :
    FiniteAdaptiveReadoutDiscrimination.readoutError
      (fun h => run S F 22 (policyTree F ω ℏ hℏ P) h Z)
      (fun h => run S F 22 (policyTree F ω ℏ hℏ P) h Z) e = 1/2 :=
  FiniteAdaptiveReadoutRobustness.identical_family_error
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ P) hZ) e

theorem handTrace_sum {I : Type*} [Fintype I] (Z : I → FullMat F) :
    handTrace F (∑ i, Z i) = ∑ i, handTrace F (Z i) := by
  ext ⟨b,f⟩ ⟨d,g⟩
  simp [handTrace, Matrix.sum_apply, Finset.sum_comm]

theorem handTrace_smul (c : ℂ) (Z : FullMat F) :
    handTrace F (c • Z) = c • handTrace F Z := by
  ext ⟨b,f⟩ ⟨d,g⟩
  simp [handTrace, Finset.mul_sum]
  ring

theorem cycle_handTrace {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (Z : FullMat F) :
    handTrace F (cycle F ω ℏ t hℏ Z) =
      (FiniteClockHandReadout.p ω t:ℂ) • FiniteQutritRetainedClock.amplified F (handTrace F Z) +
      ((1-FiniteClockHandReadout.p ω t:ℝ):ℂ) • FiniteQutritRetainedClock.amplified F
        (krausMap (fun c => FiniteQutritRetainedClock.L c ⊗ₖ (1 : Matrix F F ℂ)) (handTrace F Z)) := by
  rw [cycle, handTrace_sum, ← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, branch_action, handTrace_smul, handTrace_insert,
    FiniteClockHandReadout.Q_trace, one_smul, Fin.sum_univ_two, FiniteClockHandReadout.mass,
    show (1:A) ≠ 0 by decide, if_false, if_pos rfl, ite_true]
  rw [← Finset.smul_sum, ← Finset.smul_sum, dataBranch_keep_sum, dataBranch_reset_sum]

theorem reset_product (X : DataMat) (σ : Matrix F F ℂ) :
    krausMap (fun c => FiniteQutritRetainedClock.L c ⊗ₖ (1 : Matrix F F ℂ)) (X ⊗ₖ σ) =
      FiniteQutritRetainedClock.resetClock X ⊗ₖ σ := by
  rw [← FiniteQutritRetainedClock.reset_kraus_action]
  simp only [krausMap, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  ext ⟨b,f⟩ ⟨d,g⟩
  simp [Matrix.sum_apply, Finset.sum_mul]
  ring

theorem actual_dataChannel_reduction {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ)
    (Z : FullMat Unit) (X : DataMat) (hX : handTrace Unit Z = X ⊗ₖ (1 : Matrix Unit Unit ℂ)) :
    handTrace Unit (cycle Unit ω ℏ t hℏ Z) =
      dataChannel (FiniteClockHandReadout.p ω t) X ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
  rw [cycle_handTrace Unit hℏ, hX, reset_product, FiniteQutritRetainedClock.amplified_product,
    FiniteQutritRetainedClock.amplified_product]
  simp only [dataChannel, Matrix.add_kronecker, Matrix.smul_kronecker]

theorem resetOld_normalized : IsKrausChannel (fun c : A =>
    (FiniteQutritRetainedClock.L c ⊗ₖ (1 : Matrix A A ℂ)) ⊗ₖ (1 : Matrix Unit Unit ℂ)) := by
  unfold IsKrausChannel
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hs : (∑ c : A, (((FiniteQutritRetainedClock.L c)ᴴ * FiniteQutritRetainedClock.L c) ⊗ₖ
      (1 : Matrix A A ℂ)) ⊗ₖ (1 : Matrix Unit Unit ℂ)) =
      ((∑ c : A, (FiniteQutritRetainedClock.L c)ᴴ * FiniteQutritRetainedClock.L c) ⊗ₖ
        (1 : Matrix A A ℂ)) ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
    ext ⟨⟨b,u⟩,f⟩ ⟨⟨d,w⟩,g⟩
    simp [Matrix.sum_apply, Finset.sum_mul]
    ring
  rw [hs, FiniteQutritRetainedClock.L_normalized, Matrix.one_kronecker_one, Matrix.one_kronecker_one]

theorem resetOld_density {Z : FullMat Unit} (hZ : IsDensityOperator Z) :
    IsDensityOperator (resetOld Z) :=
  ⟨krausMap_posSemidef _ hZ.1, (trace_krausMap resetOld_normalized Z).trans hZ.2⟩

def dataMarginal (Z : FullMat Unit) : DataMat :=
  Matrix.of (fun b d => handTrace Unit Z (b,()) (d,()))

theorem dataMarginal_reindex (Z : FullMat Unit) :
    handTrace Unit Z = dataMarginal Z ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
  ext ⟨b,f⟩ ⟨d,g⟩
  cases f; cases g
  simp [dataMarginal]

theorem actual_dataChannel {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (Z : FullMat Unit) :
    dataMarginal (cycle Unit ω ℏ t hℏ Z) =
      dataChannel (FiniteClockHandReadout.p ω t) (dataMarginal Z) := by
  have hh := actual_dataChannel_reduction hℏ ω t Z (dataMarginal Z) (dataMarginal_reindex Z)
  ext b d
  have he := congrFun (congrFun hh (b,())) (d,())
  simpa [dataMarginal] using he

theorem dataMarginal_density {Z : FullMat Unit} (hZ : IsDensityOperator Z) :
    IsDensityOperator (dataMarginal Z) := by
  refine ⟨(handTrace_positive Unit hZ.1).submatrix (fun b => (b,())), ?_⟩
  have hh := (handTrace_trace Unit Z).trans hZ.2
  rw [dataMarginal_reindex, Matrix.trace_kronecker] at hh
  simpa [Matrix.trace] using hh

theorem actual_dataChannel_density {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ)
    {Z : FullMat Unit} (hZ : IsDensityOperator Z) :
    IsDensityOperator (dataChannel (FiniteClockHandReadout.p ω t) (dataMarginal Z)) := by
  rw [← actual_dataChannel hℏ ω t Z]
  exact dataMarginal_density (branches_density Unit hℏ ω t hZ)

theorem recovered_even_word {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (h : History 10 n) (Y : Matrix (Q × F) (Q × F) ℂ)
    (σ : FiniteClockHandReadout.Mat) (hσ : σ.trace=1) :
    run S F 22 (keepTree F ω ℏ hℏ (2*n)) (newEvenRecord n h)
      (insert F (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y) σ) =
    insert F (FiniteQutritRetainedClock.amplifiedPreparation F 0
      ((FiniteQutritRetainedClock.tenWord n h ⊗ₖ (1 : Matrix F F ℂ)) * Y *
        (FiniteQutritRetainedClock.tenWord n h ⊗ₖ (1 : Matrix F F ℂ))ᴴ)) (FiniteClockHandReadout.Q 0) := by
  rw [newEvenRecord, recovered_even_record F hω hℏ n hn h Y σ hσ,
    FiniteQutritRetainedClock.ten_history_word]

theorem recovered_odd_word {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0)
    (n : ℕ) (h : History 10 n) (Y : Matrix (Q × F) (Q × F) ℂ)
    (σ : FiniteClockHandReadout.Mat) (hσ : σ.trace=1) :
    run S F 22 (keepTree F ω ℏ hℏ (2*n+1)) (newOddRecord n h)
      (insert F (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y) σ) =
    insert F (FiniteQutritRetainedClock.amplifiedPreparation F 1
      ((FiniteQutritRetainedClock.tenWord n h ⊗ₖ (1 : Matrix F F ℂ)) * Y *
        (FiniteQutritRetainedClock.tenWord n h ⊗ₖ (1 : Matrix F F ℂ))ᴴ)) (FiniteClockHandReadout.Q 0) := by
  rw [newOddRecord, recovered_odd_record F hω hℏ n h Y σ hσ,
    FiniteQutritRetainedClock.ten_history_word]

end SKEFTHawking.QuantumNetwork.FiniteClockControlledRetainedMemoryExamples
