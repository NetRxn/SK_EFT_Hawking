import SKEFTHawking.QuantumNetwork.FiniteInterventionProcess

/-! Coherent partial-SWAP interventions evaluated by the finite realized process framework.
Interference and reset-memory contrasts are different witnesses; neither excludes every classical model. -/
namespace SKEFTHawking.QuantumNetwork.CoherentMemoryProcess
open Matrix FiniteMemoryProcess FiniteInterventionProcess
open scoped BigOperators Kronecker ComplexOrder

noncomputable def U : Matrix Joint Joint ℂ := (3/5 : ℂ) • 1 - (Complex.I * (4/5)) • swapMat 2

theorem coherentUnitary : Uᴴ * U = 1 := by
  ext ⟨i,e⟩ ⟨j,f⟩
  fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
    norm_num [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, swapMat, Fintype.sum_prod_type, Fin.sum_univ_two,
      map_ofNat, Complex.ext_iff, Complex.mul_re, Complex.mul_im]

noncomputable def unitaryStep (I : FiniteInstrument Qubit 1) : Step Qubit Qubit 1 where
  count := 1
  evolution _ := U
  normalized := by simpa [IsKrausChannel] using coherentUnitary
  instrument := I

noncomputable def measuredStep : Step Qubit Qubit 2 where
  count := 1
  evolution _ := U
  normalized := by simpa [IsKrausChannel] using coherentUnitary
  instrument := FiniteInstrument.computational

noncomputable def input (b : Qubit) : Matrix Joint Joint ℂ := basisState b ⊗ₖ basisState 0
noncomputable def evolution (X : Matrix Joint Joint ℂ) := U * X * Uᴴ

noncomputable def coherentTree : Tree Qubit Qubit 1 2 :=
  .node (unitaryStep FiniteInstrument.identity)
    (fun _ => .node (unitaryStep FiniteInstrument.identity) (fun _ => .done))

noncomputable def measuredTree : Tree Qubit Qubit 2 2 :=
  .node measuredStep (fun _ => .node measuredStep (fun _ => .done))

noncomputable def resetTree : Tree Qubit Qubit 1 2 :=
  .node (unitaryStep FiniteInstrument.reset)
    (fun _ => .node (unitaryStep FiniteInstrument.identity) (fun _ => .done))

theorem identity_step (X : Matrix Joint Joint ℂ) :
    (unitaryStep FiniteInstrument.identity).branch Qubit Qubit 1 0 X = evolution X := by
  simp [unitaryStep, Step.branch, FiniteInstrument.identity, FiniteInstrument.singleton,
    FiniteInstrument.lift, FiniteInstrument.branch, krausMap, evolution]

theorem reset_step (X : Matrix Joint Joint ℂ) :
    (unitaryStep FiniteInstrument.reset).branch Qubit Qubit 1 0 X = resetSystem (evolution X) := by
  change (FiniteInstrument.reset.lift Qubit).branch 0 (krausMap (fun _ : Fin 1 => U) X) = _
  rw [FiniteInstrument.lifted_reset_eq]
  simp [krausMap, evolution]

/-- Five entries describe the invariant vacuum/one-excitation sector. -/
noncomputable def sector (z a b c d : ℂ) : Matrix Joint Joint ℂ :=
  fun i j => if i=(0,0) ∧ j=(0,0) then z else
    if i=(0,1) ∧ j=(0,1) then a else if i=(0,1) ∧ j=(1,0) then b else
    if i=(1,0) ∧ j=(0,1) then c else if i=(1,0) ∧ j=(1,0) then d else 0

theorem input_sector : input 0 = sector 1 0 0 0 0 ∧ input 1 = sector 0 0 0 0 1 := by
  constructor <;> ext ⟨i,e⟩ ⟨j,f⟩ <;>
    fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
      norm_num [input, sector, basisState, Matrix.kronecker_apply]

theorem evolution_sector (z a b c d : ℂ) :
    evolution (sector z a b c d) = sector z
      ((9*a+12*Complex.I*b-12*Complex.I*c+16*d)/25)
      ((12*Complex.I*a+9*b+16*c-12*Complex.I*d)/25)
      ((-12*Complex.I*a+16*b+9*c+12*Complex.I*d)/25)
      ((16*a-12*Complex.I*b+12*Complex.I*c+9*d)/25) := by
  ext ⟨i,e⟩ ⟨j,f⟩
  fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
    norm_num [evolution, sector, U, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, swapMat, Fintype.sum_prod_type, Fin.sum_univ_two, map_ofNat] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring


theorem sector_probability (z a b c d : ℂ) : systemProbability 1 (sector z a b c d) = d.re := by
  simp [systemProbability, sector, basisState, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]

theorem sector_trace (z a b c d : ℂ) : (sector z a b c d).trace = z+a+d := by
  simp [sector, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem sector_reset (z a b c d : ℂ) : resetSystem (sector z a b c d) = sector (z+d) a 0 0 0 := by
  rw [resetSystem_eq]
  ext ⟨i,e⟩ ⟨j,f⟩
  fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
    simp [sector, basisState, ptrace1, Fin.sum_univ_two]

/-- Intermediate projective branches, including their off-diagonal removal. -/
theorem sector_measure (a₀ : Qubit) (z a b c d : ℂ) :
    (FiniteInstrument.computational.lift Qubit).branch a₀ (sector z a b c d) =
      if a₀=0 then sector z a 0 0 0 else sector 0 0 0 0 d := by
  simp only [FiniteInstrument.branch, FiniteInstrument.lift, FiniteInstrument.computational]
  ext ⟨i,e⟩ ⟨j,f⟩
  fin_cases a₀ <;> fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
    simp [sector, krausMap, basisState, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

theorem measured_step (a : Qubit) (X : Matrix Joint Joint ℂ) :
    measuredStep.branch Qubit Qubit 2 a X =
      (FiniteInstrument.computational.lift Qubit).branch a (evolution X) := by
  simp [measuredStep, Step.branch, krausMap, evolution]

theorem first_state : evolution (input 1) = sector 0 (16/25) (-12*Complex.I/25) (12*Complex.I/25) (9/25) := by
  rw [input_sector.2, evolution_sector]
  norm_num

/-- Two coherent steps are evaluated through the singleton-instrument tree. -/
theorem coherent_probability :
    systemProbability 1 (run Qubit Qubit 1 coherentTree (0,0,()) (input 1)) = 49/625 := by
  change systemProbability 1 ((unitaryStep FiniteInstrument.identity).branch Qubit Qubit 1 0
    ((unitaryStep FiniteInstrument.identity).branch Qubit Qubit 1 0 (input 1))) = _
  rw [identity_step, identity_step, first_state, evolution_sector, sector_probability]
  norm_num [Complex.mul_re, Complex.mul_im]

/-- Each row is the intermediate outcome and each column the later outcome. -/
theorem measured_table (a b : Qubit) :
    weight Qubit Qubit 2 measuredTree (a,b,()) (input 1) =
      if a=0 then (if b=0 then 144/625 else 256/625) else (if b=0 then 144/625 else 81/625) := by
  change (measuredStep.branch Qubit Qubit 2 b (measuredStep.branch Qubit Qubit 2 a (input 1))).trace.re = _
  rw [measured_step, measured_step, first_state, sector_measure]
  fin_cases a <;> fin_cases b <;>
    norm_num [evolution_sector, sector_measure, sector_trace, Complex.mul_re, Complex.mul_im]

theorem measured_probability :
    (∑ a : Qubit, weight Qubit Qubit 2 measuredTree (a,1,()) (input 1)) = 337/625 := by
  simp [Fin.sum_univ_two, measured_table]
  norm_num

theorem interference_contrast :
    (∑ a : Qubit, weight Qubit Qubit 2 measuredTree (a,1,()) (input 1)) -
      systemProbability 1 (run Qubit Qubit 1 coherentTree (0,0,()) (input 1)) = 288/625 := by
  rw [measured_probability, coherent_probability]
  norm_num


noncomputable def prefixTree : Tree Qubit Qubit 2 1 := .node measuredStep (fun _ => .done)
noncomputable def idleMeasured : Tree Qubit Qubit 2 1 :=
  .node (localStep Qubit Qubit 2 FiniteInstrument.computational) (fun _ => .done)
noncomputable def futureMeasured : Tree Qubit Qubit 2 1 := .node measuredStep (fun _ => .done)

/-- Same initial state and prefix, every future outcome summed, even when later dynamics change. -/
theorem earlier_marginals (a : Qubit) :
    (∑ h, weight Qubit Qubit 2 futureMeasured h (run Qubit Qubit 2 prefixTree (a,()) (input 1))) =
      (if a=0 then 16/25 else 9/25) ∧
    (∑ h, weight Qubit Qubit 2 idleMeasured h (run Qubit Qubit 2 prefixTree (a,()) (input 1))) =
      (if a=0 then 16/25 else 9/25) := by
  rw [prefix_marginal, prefix_marginal]
  have hp : weight Qubit Qubit 2 prefixTree (a,()) (input 1) = (if a=0 then 16/25 else 9/25) := by
    change (measuredStep.branch Qubit Qubit 2 a (input 1)).trace.re = _
    rw [measured_step, first_state, sector_measure]
    fin_cases a <;> norm_num [sector_trace]
  exact ⟨hp,hp⟩

noncomputable def resetPrefix : Tree Qubit Qubit 1 1 := .node (unitaryStep FiniteInstrument.reset) (fun _ => .done)

private theorem vacuum_evolution : evolution (input 0) = sector 1 0 0 0 0 := by
  rw [input_sector.1, evolution_sector]
  norm_num

theorem reset_probability (b : Qubit) :
    systemProbability 1 (run Qubit Qubit 1 resetTree (0,0,()) (input b)) = if b=0 then 0 else 256/625 := by
  change systemProbability 1 ((unitaryStep FiniteInstrument.identity).branch Qubit Qubit 1 0
    ((unitaryStep FiniteInstrument.reset).branch Qubit Qubit 1 0 (input b))) = _
  rw [identity_step, reset_step]
  fin_cases b
  · erw [vacuum_evolution, sector_reset, evolution_sector, sector_probability]
    norm_num
  · erw [first_state, sector_reset, evolution_sector, sector_probability]
    norm_num

theorem sector_marginal (z a b c d : ℂ) :
    systemMarginal (sector z a b c d) = fun i j => if i=0 ∧ j=0 then z+a else if i=1 ∧ j=1 then d else 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [systemMarginal, swapJoint_eq, sector, swapMat, ptrace1, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

theorem reset_marginal (b : Qubit) :
    systemMarginal (run Qubit Qubit 1 resetPrefix (0,()) (input b)) = basisState 0 := by
  change systemMarginal ((unitaryStep FiniteInstrument.reset).branch Qubit Qubit 1 0 (input b)) = _
  rw [reset_step]
  fin_cases b
  · erw [vacuum_evolution, sector_reset, sector_marginal]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [basisState]
  · erw [first_state, sector_reset, sector_marginal]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [basisState]

noncomputable def environmentKraus (k : Fin 2) : Matrix Joint Joint ℂ :=
  (1 : Matrix Qubit Qubit ℂ) ⊗ₖ resetKraus k

theorem environment_normalized : IsKrausChannel environmentKraus := by
  ext ⟨i,e⟩ ⟨j,f⟩
  fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
    norm_num [IsKrausChannel, environmentKraus, resetKraus, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

noncomputable def environmentStep : Step Qubit Qubit 1 :=
  channelStep Qubit Qubit environmentKraus environment_normalized

noncomputable def controlTree : Tree Qubit Qubit 1 3 :=
  .node (unitaryStep FiniteInstrument.reset) (fun _ => .node environmentStep
    (fun _ => .node (unitaryStep FiniteInstrument.identity) (fun _ => .done)))

theorem sector_environment_reset (z a b c d : ℂ) :
    krausMap environmentKraus (sector z a b c d) = sector (z+a) 0 0 0 d := by
  ext ⟨i,e⟩ ⟨j,f⟩
  fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
    simp [krausMap, environmentKraus, resetKraus, sector, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem control_probability (b : Qubit) :
    systemProbability 1 (run Qubit Qubit 1 controlTree (0,0,0,()) (input b)) = 0 := by
  change systemProbability 1 ((unitaryStep FiniteInstrument.identity).branch Qubit Qubit 1 0
    (environmentStep.branch Qubit Qubit 1 0 ((unitaryStep FiniteInstrument.reset).branch Qubit Qubit 1 0 (input b)))) = _
  rw [identity_step, reset_step]
  change systemProbability 1 (evolution ((channelStep Qubit Qubit environmentKraus environment_normalized).branch Qubit Qubit 1 0 _)) = _
  rw [channelStep_branch]
  fin_cases b
  · erw [vacuum_evolution, sector_reset, sector_environment_reset, evolution_sector, sector_probability]
    norm_num
  · erw [first_state, sector_reset, sector_environment_reset, evolution_sector, sector_probability]
    norm_num

/-- No common normalized system-only continuation can reproduce both reset histories. -/
theorem no_common_system_model {k : ℕ} (K : Fin k → Matrix Qubit Qubit ℂ)
    (hK : IsKrausChannel K) (E : Matrix Qubit Qubit ℂ) (hE : IsBinaryPOVM E) :
    ¬ (∀ b : Qubit, binaryOutcomeProb E (krausMap K
      (systemMarginal (run Qubit Qubit 1 resetPrefix (0,()) (input b)))) =
      systemProbability 1 (run Qubit Qubit 1 resetTree (0,0,()) (input b))) := by
  intro h
  have hs (b : Qubit) : IsDensityOperator (systemMarginal (run Qubit Qubit 1 resetPrefix (0,()) (input b))) := by
    rw [reset_marginal]
    exact basisState_density 0
  have he (b : Qubit) : traceDist (systemMarginal (run Qubit Qubit 1 resetPrefix (0,()) (input b))) (basisState 0) ≤ 0 := by
    rw [reset_marginal, traceDist_self]
  have hbound := binary_memoryless_separation_le (hs 0) (hs 1) (basisState_density 0) hK hE (he 0) (he 1)
  rw [h 0, h 1, reset_probability, reset_probability] at hbound
  norm_num at hbound

/-- Pad a singleton intervention with an explicitly impossible second outcome. -/
noncomputable def padSingleton (I : FiniteInstrument Qubit 1) : FiniteInstrument Qubit 2 where
  count := I.count
  operators a k := if a=0 then I.operators 0 k else 0
  normalized := by
    have h := I.normalized
    simpa [Fin.sum_univ_two] using h

noncomputable def paddedStep (I : FiniteInstrument Qubit 1) : Step Qubit Qubit 2 where
  count := 1
  evolution _ := U
  normalized := by simpa [IsKrausChannel] using coherentUnitary
  instrument := padSingleton I

theorem padded_branch_zero (I : FiniteInstrument Qubit 1) (X : Matrix Joint Joint ℂ) :
    (paddedStep I).branch Qubit Qubit 2 0 X = (unitaryStep I).branch Qubit Qubit 1 0 X := by
  simp [paddedStep, unitaryStep, Step.branch, FiniteInstrument.branch, FiniteInstrument.lift, padSingleton]

theorem padded_impossible (I : FiniteInstrument Qubit 1) (X : Matrix Joint Joint ℂ) :
    (paddedStep I).branch Qubit Qubit 2 1 X = 0 := by
  change ((padSingleton I).lift Qubit).branch 1 _ = 0
  apply FiniteInstrument.zero_outcome
  intro k
  simp [FiniteInstrument.lift, padSingleton]

noncomputable def coherentReadoutTree : Tree Qubit Qubit 2 2 :=
  .node (paddedStep FiniteInstrument.identity) (fun _ => .node measuredStep (fun _ => .done))

noncomputable def resetReadoutTree : Tree Qubit Qubit 2 2 :=
  .node (paddedStep FiniteInstrument.reset) (fun _ => .node measuredStep (fun _ => .done))

/-- Final binary readout is the branch trace of the actual final instrument. -/
theorem measured_weight (a : Qubit) (X : Matrix Joint Joint ℂ) :
    (measuredStep.branch Qubit Qubit 2 a X).trace.re = systemProbability a (evolution X) := by
  rw [measured_step]
  simp only [FiniteInstrument.branch, FiniteInstrument.lift, FiniteInstrument.computational]
  fin_cases a <;>
    simp [krausMap, systemProbability, basisState, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

/-- The padded evaluator and external-readout singleton evaluator give the same probability. -/
theorem coherent_readout_equivalence :
    (∑ a : Qubit, weight Qubit Qubit 2 coherentReadoutTree (a,1,()) (input 1)) =
      systemProbability 1 (run Qubit Qubit 1 coherentTree (0,0,()) (input 1)) := by
  rw [Fin.sum_univ_two]
  change (measuredStep.branch Qubit Qubit 2 1 ((paddedStep FiniteInstrument.identity).branch Qubit Qubit 2 0 (input 1))).trace.re +
    (measuredStep.branch Qubit Qubit 2 1 ((paddedStep FiniteInstrument.identity).branch Qubit Qubit 2 1 (input 1))).trace.re = _
  rw [padded_branch_zero, padded_impossible, Step.branch_zero, Matrix.trace_zero, Complex.zero_re, add_zero,
    measured_weight, identity_step]
  change _ = systemProbability 1 ((unitaryStep FiniteInstrument.identity).branch Qubit Qubit 1 0
    ((unitaryStep FiniteInstrument.identity).branch Qubit Qubit 1 0 (input 1)))
  rw [identity_step, identity_step]

theorem reset_readout_equivalence (b : Qubit) :
    (∑ a : Qubit, weight Qubit Qubit 2 resetReadoutTree (a,1,()) (input b)) =
      systemProbability 1 (run Qubit Qubit 1 resetTree (0,0,()) (input b)) := by
  rw [Fin.sum_univ_two]
  change (measuredStep.branch Qubit Qubit 2 1 ((paddedStep FiniteInstrument.reset).branch Qubit Qubit 2 0 (input b))).trace.re +
    (measuredStep.branch Qubit Qubit 2 1 ((paddedStep FiniteInstrument.reset).branch Qubit Qubit 2 1 (input b))).trace.re = _
  rw [padded_branch_zero, padded_impossible, Step.branch_zero, Matrix.trace_zero, Complex.zero_re, add_zero, measured_weight]
  change _ = systemProbability 1 ((unitaryStep FiniteInstrument.identity).branch Qubit Qubit 1 0
    ((unitaryStep FiniteInstrument.reset).branch Qubit Qubit 1 0 (input b)))
  rw [identity_step]

theorem coherentUnitary_right : U * Uᴴ = 1 := mul_eq_one_comm.mp coherentUnitary

theorem input_density (b : Qubit) : IsDensityOperator (input b) := basisJoint_density b 0

/-- Actual realized-tree normalization is inherited by this coherent consumer. -/
theorem coherent_normalized :
    (∀ h, 0 ≤ weight Qubit Qubit 2 coherentReadoutTree h (input 1)) ∧
    (∑ h, weight Qubit Qubit 2 coherentReadoutTree h (input 1)) = 1 :=
  normalized_weights Qubit Qubit 2 coherentReadoutTree (input_density 1)

/-- Reuse the framework's reachable outcome-dependent preparations and impossible cross-branch. -/
theorem feedback_acceptance :
    weight (Fin 2) Unit 2 feedbackExample (0,0,()) feedbackInput = 1/2 ∧
    weight (Fin 2) Unit 2 feedbackExample (1,1,()) feedbackInput = 1/2 ∧
    weight (Fin 2) Unit 2 feedbackExample (0,1,()) feedbackInput = 0 := by
  norm_num [feedback_example_weights]

end SKEFTHawking.QuantumNetwork.CoherentMemoryProcess
