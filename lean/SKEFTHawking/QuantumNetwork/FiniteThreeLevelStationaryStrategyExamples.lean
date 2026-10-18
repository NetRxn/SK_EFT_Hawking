import SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyReflection

/-! Actual feedback, reset-ended strategies, and guards for stationary strategy reflection. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyExamples
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteThreeLevelStationaryStrategyReflection
open FiniteThreeLevelPositiveHistory (Q MatQ rhoN R Rinv Gamma Phi Psi)
open scoped BigOperators ComplexOrder Kronecker

def idleInstrument (o : ℕ) (ho : 0 < o) : FiniteInstrument Q o where
  count := 1
  operators a _ := if a = ⟨0,ho⟩ then 1 else 0
  normalized := by simp

theorem idleInstrument_branch (o : ℕ) (ho : 0 < o) (a : Fin o) (X : MatQ) :
    (idleInstrument o ho).branch a X = if a = ⟨0,ho⟩ then X else 0 := by
  by_cases ha : a = ⟨0,ho⟩ <;> simp [FiniteInstrument.branch, krausMap, idleInstrument, ha]

def resetOnlyStep (o : ℕ) (ho : 0 < o) : Step Q Unit o where
  count := _
  evolution k := GibbsMultilevelReflection.joint (FiniteThreeLevelPositiveHistory.channel 0 k)
  normalized := GibbsMultilevelReflection.joint_normalized _
    (FiniteThreeLevelPositiveHistory.channel_normalized (by norm_num) (by norm_num))
  instrument := idleInstrument o ho

theorem resetOnlyStep_branch (o : ℕ) (ho : 0 < o) (a : Fin o) (X : MatQ) :
    (resetOnlyStep o ho).branch Q Unit o a (joint X) =
      joint (if a = ⟨0,ho⟩ then X.trace • rhoN else 0) := by
  change ((idleInstrument o ho).lift Unit).branch a
    (krausMap (fun k => GibbsMultilevelReflection.joint (FiniteThreeLevelPositiveHistory.channel 0 k))
      (GibbsMultilevelReflection.joint X)) = _
  rw [GibbsMultilevelReflection.joint_kraus,
    FiniteThreeLevelPositiveHistory.channel_state (by norm_num) (by norm_num)]
  change krausMap (fun k => GibbsMultilevelReflection.joint ((idleInstrument o ho).operators a k))
    (GibbsMultilevelReflection.joint (Phi 0 X)) = _
  rw [GibbsMultilevelReflection.joint_kraus]
  change joint ((idleInstrument o ho).branch a (Phi 0 X)) = _
  rw [idleInstrument_branch, FiniteThreeLevelPositiveHistory.Phi_zero]

def resetTail : Tree Q Unit 15 1 := .node (resetOnlyStep 15 (by norm_num)) (fun _ => .done)

/-- Arbitrary normalized prefix-dependent continuations, followed by an unconditional reset. -/
def adaptiveFamily {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k) : Tree Q Unit 15 (1+k+1) :=
  .node (localStep Q Unit 15 FiniteThreeLevelPositiveHistory.instrument)
    (fun a => appendTree (U a) (fun _ => resetTail))

def familyHistory {k : ℕ} (a : Fin 15) (h : History 15 k) (c : Fin 15) : History 15 (1+k+1) :=
  (a, appendHistory h (c,()))

theorem family_depth (k : ℕ) : 1+k+1 = k+2 := by omega

theorem adaptiveFamily_branch {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (a : Fin 15) (h : History 15 k) (c : Fin 15) (X : MatQ) :
    branch (adaptiveFamily U) (familyHistory a h c) X =
      if c = 0 then (branch (U a) h (FiniteThreeLevelPositiveHistory.instrument.branch a X)).trace • rhoN
      else 0 := by
  unfold branch adaptiveFamily familyHistory
  simp only [run, localStep_joint]
  rw [append_run]
  change unJoint ((resetOnlyStep 15 (by norm_num)).branch Q Unit 15 c
    (run Q Unit 15 (U a) h (joint (FiniteThreeLevelPositiveHistory.instrument.branch a X)))) = _
  rw [← joint_unJoint (run Q Unit 15 (U a) h (joint _)), resetOnlyStep_branch, unJoint_joint]
  simp only [unJoint_joint]
  rfl

theorem family_sum {k : ℕ} (_U : Fin 15 → Tree Q Unit 15 k)
    (f : History 15 (1+k+1) → MatQ) :
    ∑ g, f g = ∑ a, ∑ h, ∑ c, f (familyHistory a h c) := by
  change (∑ g : Fin 15 × History 15 (1+k), f g) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← (appendEquiv 15 k 1).sum_comp (fun g => f (a,g)), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  change (∑ g : Fin 15 × Unit, f (a,appendHistory h g)) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, familyHistory]
  rfl

theorem branch_sum_trace {o n : ℕ} (T : Tree Q Unit o n) (X : MatQ) :
    (∑ h, (branch T h X).trace) = X.trace := by
  simp only [branch, unJoint_trace]
  rw [sum_trace, joint_trace]

theorem adaptiveFamily_aggregate {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k) (X : MatQ) :
    (∑ g, branch (adaptiveFamily U) g X) = X.trace • rhoN := by
  rw [family_sum U]
  simp_rw [adaptiveFamily_branch]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [← Finset.sum_smul, branch_sum_trace]
  rw [FiniteInstrument.sum_trace]

theorem adaptiveFamily_stationary {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k) :
    Stationary (adaptiveFamily U) := by
  unfold Stationary
  rw [adaptiveFamily_aggregate, FiniteThreeLevelPositiveHistory.rhoN_trace, one_smul]

theorem adaptiveFamily_prefix_effect {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k) (a : Fin 15) :
    (∑ h, ∑ c, effect (adaptiveFamily U) (familyHistory a h c)) =
      FiniteThreeLevelPositiveHistory.effect a := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  simp only [Matrix.sum_mul, Matrix.trace_sum]
  simp_rw [← branch_trace, adaptiveFamily_branch]
  simp only [apply_ite Matrix.trace, Matrix.trace_smul,
    FiniteThreeLevelPositiveHistory.rhoN_trace, smul_eq_mul, mul_one, Matrix.trace_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [branch_sum_trace, FiniteThreeLevelPositiveHistory.branch_trace]

theorem adaptiveFamily_full_span {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k) :
    effectSpan (adaptiveFamily U) = ⊤ := by
  apply top_unique
  intro A _
  rw [← FiniteThreeLevelPositiveHistory.frame_right_inverse A]
  change (∑ a, FiniteThreeLevelPositiveHistory.frameCoeff A a •
    FiniteThreeLevelPositiveHistory.effect a) ∈ effectSpan (adaptiveFamily U)
  apply Submodule.sum_mem
  intro a _
  apply Submodule.smul_mem
  rw [← adaptiveFamily_prefix_effect U a]
  apply Submodule.sum_mem
  intro h _
  apply Submodule.sum_mem
  intro c _
  exact Submodule.subset_span ⟨familyHistory a h c,rfl⟩

/-- Prefix-constant coefficients are an explicit finite witness for every matrix. -/
theorem adaptiveFamily_synthesis {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (p : ℝ) (hpos : 0 < p) (A : MatQ) :
    synthesis (adaptiveFamily U) p (fun g =>
      FiniteThreeLevelPositiveHistory.frameCoeff (FiniteThreeLevelPositiveHistory.inversePsi p A) g.1) = A := by
  unfold synthesis
  rw [family_sum U]
  change (∑ a, ∑ h, ∑ c, FiniteThreeLevelPositiveHistory.frameCoeff
    (FiniteThreeLevelPositiveHistory.inversePsi p A) a •
    Psi p (effect (adaptiveFamily U) (familyHistory a h c))) = A
  simp_rw [← Finset.smul_sum, ← FiniteThreeLevelPositiveHistory.Psi_sum,
    adaptiveFamily_prefix_effect, ← FiniteThreeLevelPositiveHistory.Psi_smul]
  rw [← FiniteThreeLevelPositiveHistory.Psi_sum]
  change Psi p (FiniteThreeLevelPositiveHistory.frameSynthesis
    (FiniteThreeLevelPositiveHistory.frameCoeff (FiniteThreeLevelPositiveHistory.inversePsi p A))) = A
  rw [FiniteThreeLevelPositiveHistory.frame_right_inverse, FiniteThreeLevelPositiveHistory.Psi_inverse hpos]

def feedbackContinuation (a : Fin 15) : Tree Q Unit 15 1 :=
  .node (localStep Q Unit 15 (if a = 0 then idleInstrument 15 (by norm_num)
    else FiniteThreeLevelPositiveHistory.instrument)) (fun _ => .done)

def adaptiveExample : Tree Q Unit 15 3 := adaptiveFamily feedbackContinuation

theorem adaptiveExample_stationary : Stationary adaptiveExample :=
  adaptiveFamily_stationary feedbackContinuation

theorem adaptiveExample_full_span : effectSpan adaptiveExample = ⊤ :=
  adaptiveFamily_full_span feedbackContinuation

theorem feedbackContinuation_branch (a b : Fin 15) (X : MatQ) :
    branch (feedbackContinuation a) (b,()) X =
      if a = 0 then (if b = 0 then X else 0)
      else FiniteThreeLevelPositiveHistory.instrument.branch b X := by
  unfold branch feedbackContinuation
  simp only [run, localStep_joint, unJoint_joint]
  by_cases ha : a = 0 <;> simp [ha, idleInstrument_branch]

theorem adaptiveExample_branch (a b c : Fin 15) (X : MatQ) :
    branch adaptiveExample (a,b,c,()) X =
      if c = 0 then
        (if a = 0 then (if b = 0 then (FiniteThreeLevelPositiveHistory.instrument.branch a X).trace else 0)
          else (FiniteThreeLevelPositiveHistory.instrument.branch b
            (FiniteThreeLevelPositiveHistory.instrument.branch a X)).trace) • rhoN
      else 0 := by
  change branch (adaptiveFamily feedbackContinuation) (familyHistory a (b,()) c) X = _
  rw [adaptiveFamily_branch, feedbackContinuation_branch]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha,hb]

theorem adaptiveExample_effect (a b c : Fin 15) :
    effect adaptiveExample (a,b,c,()) =
      if c = 0 then (if a = 0 then (if b = 0 then FiniteThreeLevelPositiveHistory.effect a else 0)
        else FiniteThreeLevelPositiveHistory.J a (FiniteThreeLevelPositiveHistory.effect b)) else 0 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [← branch_trace, adaptiveExample_branch]
  by_cases hc : c = 0 <;> by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [hc,ha,hb, Matrix.trace_smul, FiniteThreeLevelPositiveHistory.rhoN_trace,
      FiniteThreeLevelPositiveHistory.branch_trace, FiniteThreeLevelPositiveHistory.trace_duality]

theorem overlap_five_zero : FiniteThreeLevelPositiveHistory.overlap 5 0 = 1/4 := by
  have h5 : FiniteThreeLevelPositiveHistory.projector 5 =
      !![1/2, -Complex.I/2, 0; Complex.I/2, 1/2, 0; 0, 0, 0] := rfl
  have h0 : FiniteThreeLevelPositiveHistory.projector 0 =
      !![1, 0, 0; 0, 0, 0; 0, 0, 0] := rfl
  unfold FiniteThreeLevelPositiveHistory.overlap
  rw [h5, h0]
  norm_num [Gamma, R, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace,
    Fin.sum_univ_succ]
  have h := FiniteThreeLevelPositiveHistory.rdiag_square 0
  change FiniteThreeLevelPositiveHistory.rdiag 0 * FiniteThreeLevelPositiveHistory.rdiag 0 = 1/2 at h
  nlinarith

theorem imaginary_leaf_effect : effect adaptiveExample (5,0,0,()) =
    (3/125 : ℂ) • FiniteThreeLevelPositiveHistory.projector 5 := by
  rw [adaptiveExample_effect]
  have h50 : (5 : Fin 15) ≠ 0 := by decide
  simp only [h50, if_false, if_true]
  have hd : FiniteThreeLevelPositiveHistory.d 5 = 5/12 := by
    rw [FiniteThreeLevelPositiveHistory.d_values]
    rfl
  rw [FiniteThreeLevelPositiveHistory.J_effect, overlap_five_zero, hd]
  norm_num

theorem imaginary_leaf_entry : effect adaptiveExample (5,0,0,()) 0 1 = -3*Complex.I/250 := by
  rw [imaginary_leaf_effect]
  change (3/125 : ℂ) * (-Complex.I/2) = _
  ring

theorem imaginary_leaf_mass : mass adaptiveExample (5,0,0,()) = 1/100 := by
  unfold mass
  have hd : FiniteThreeLevelPositiveHistory.d 5 = 5/12 := by
    rw [FiniteThreeLevelPositiveHistory.d_values]
    rfl
  rw [imaginary_leaf_effect, mul_smul_comm, Matrix.trace_smul,
    Matrix.trace_mul_comm rhoN, ← FiniteThreeLevelPositiveHistory.d_trace, hd]
  norm_num

theorem identity_arm_mass : mass adaptiveExample (0,0,0,()) = 1/10 := by
  unfold mass
  rw [adaptiveExample_effect]
  norm_num only [ite_true]
  rw [FiniteThreeLevelPositiveHistory.mean_effect, FiniteThreeLevelPositiveHistory.d_values]
  norm_num

theorem feedback_instruments_differ : idleInstrument 15 (by norm_num) ≠
    FiniteThreeLevelPositiveHistory.instrument := by
  intro he
  have h := congrArg (fun I : FiniteInstrument Q 15 => (I.branch 1 rhoN).trace) he
  rw [idleInstrument_branch, FiniteThreeLevelPositiveHistory.branch_trace,
    Matrix.trace_mul_comm, FiniteThreeLevelPositiveHistory.mean_effect,
    FiniteThreeLevelPositiveHistory.d_values] at h
  norm_num at h

theorem imaginary_leaf_nonzero : effect adaptiveExample (5,0,0,()) 0 1 ≠ 0 := by
  rw [imaginary_leaf_entry]
  norm_num


/-- The arbitrary-depth adaptive family has full rank for positive retention. -/
theorem adaptiveFamily_rank {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    Module.finrank ℂ (Reconstructed (adaptiveFamily U) (by norm_num)
      (adaptiveFamily_stationary U) p hp hp1) = 9 :=
  (full_finrank_iff _ (by norm_num) (adaptiveFamily_stationary U) p hp hp1 hpos).mpr
    (adaptiveFamily_full_span U)

theorem adaptiveFamily_reset_rank {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k) :
    Module.finrank ℂ (Reconstructed (adaptiveFamily U) (by norm_num)
      (adaptiveFamily_stationary U) 0 (by norm_num) (by norm_num)) = 1 :=
  reset_finrank _ (by norm_num) (adaptiveFamily_stationary U)

def familyCoeff {k : ℕ} (_U : Fin 15 → Tree Q Unit 15 k) (p : ℝ) (A : MatQ)
    (g : History 15 (1+k+1)) : ℂ :=
  FiniteThreeLevelPositiveHistory.frameCoeff (FiniteThreeLevelPositiveHistory.inversePsi p A) g.1

theorem familyCoeff_pairing {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) (A B : MatQ) :
    FinitePositiveKernel.pairing (kernel (adaptiveFamily U) (by norm_num)
      (adaptiveFamily_stationary U) p hp hp1) (familyCoeff U p A) (familyCoeff U p B) =
      FiniteThreeLevelPositiveHistory.form A B := by
  rw [pairing_synthesis]
  rw [show synthesis (adaptiveFamily U) p (familyCoeff U p A) = A from
    adaptiveFamily_synthesis U p hpos A,
    show synthesis (adaptiveFamily U) p (familyCoeff U p B) = B from
    adaptiveFamily_synthesis U p hpos B]

theorem matrixUnit_imaginary_form :
    FiniteThreeLevelPositiveHistory.form (FiniteThreeLevelPositiveHistory.E 0 1)
      (Complex.I • FiniteThreeLevelPositiveHistory.E 0 1) = Complex.I / (Real.sqrt 6 : ℂ) := by
  rw [FiniteThreeLevelHistoryTransfer.form_smul_right,
    FiniteThreeLevelPositiveHistory.matrixUnit_form,
    FiniteThreeLevelPositiveHistory.metricWeight_sqrt]
  have hw : FiniteThreeLevelPositiveHistory.weights 0 *
      FiniteThreeLevelPositiveHistory.weights 1 = (6 : ℝ)⁻¹ := by
    change (1/2 : ℝ) * (1/3) = (6 : ℝ)⁻¹
    norm_num
  rw [hw, Real.sqrt_inv, Complex.ofReal_inv]
  rfl

theorem familyCoeff_imaginary_pairing {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    FinitePositiveKernel.pairing (kernel (adaptiveFamily U) (by norm_num)
      (adaptiveFamily_stationary U) p hp hp1)
      (familyCoeff U p (FiniteThreeLevelPositiveHistory.E 0 1))
      (familyCoeff U p (Complex.I • FiniteThreeLevelPositiveHistory.E 0 1)) =
      Complex.I / (Real.sqrt 6 : ℂ) := by
  rw [familyCoeff_pairing U p hp hp1 hpos, matrixUnit_imaginary_form]

theorem familyCoeff_swapped_pairing {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    FinitePositiveKernel.pairing (kernel (adaptiveFamily U) (by norm_num)
      (adaptiveFamily_stationary U) p hp hp1)
      (familyCoeff U p (Complex.I • FiniteThreeLevelPositiveHistory.E 0 1))
      (familyCoeff U p (FiniteThreeLevelPositiveHistory.E 0 1)) =
      -Complex.I / (Real.sqrt 6 : ℂ) := by
  rw [familyCoeff_pairing U p hp hp1 hpos,
    ← FiniteThreeLevelHistoryTransfer.form_conj, matrixUnit_imaginary_form]
  simp

open scoped InnerProductSpace in
theorem family_imaginary_readout {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    ⟪(fullCoordinateEquiv (adaptiveFamily U) (by norm_num) (adaptiveFamily_stationary U)
        p hp hp1 hpos (adaptiveFamily_full_span U)).symm
        (FiniteThreeLevelHistoryReadout.dualState (Complex.I • FiniteThreeLevelPositiveHistory.E 0 1)),
      (fullCoordinateEquiv (adaptiveFamily U) (by norm_num) (adaptiveFamily_stationary U)
        p hp hp1 hpos (adaptiveFamily_full_span U)).symm
        (FiniteThreeLevelPositiveHistory.E 1 0)⟫_ℂ = Complex.I := by
  rw [full_trace_evaluation]
  simp [FiniteThreeLevelPositiveHistory.E]

/-- The old two-step strategy is recovered on its actual chronological leaves. -/
theorem fixture_branch (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (a b : Fin 15) (X : MatQ) :
    branch (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) (a,b,()) X =
      FiniteThreeLevelPositiveHistory.instrument.branch b
        (Phi r (FiniteThreeLevelPositiveHistory.instrument.branch a X)) := by
  change unJoint ((FiniteThreeLevelPositiveHistory.step r hr hr1).branch Q Unit 15 b
    ((FiniteThreeLevelPositiveHistory.step 1 (by norm_num) (by norm_num)).branch Q Unit 15 a
      (GibbsMultilevelReflection.joint X))) = _
  rw [FiniteThreeLevelPositiveHistory.step_branch, FiniteThreeLevelPositiveHistory.step_branch,
    FiniteThreeLevelPositiveHistory.Phi_one]
  exact unJoint_joint _

theorem fixture_effect (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (a b : Fin 15) :
    effect (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) (a,b,()) =
      FiniteThreeLevelPositiveHistory.halfEffect r (a,b) := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [← branch_trace, fixture_branch, FiniteThreeLevelPositiveHistory.branch_trace,
    FiniteThreeLevelPositiveHistory.Phi_Psi_duality,
    FiniteThreeLevelPositiveHistory.trace_duality]
  rfl

theorem fixture_stationary (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    Stationary (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) := by
  change (∑ h : Fin 15 × Fin 15 × Unit, _) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  simp only [show (default : Unit) = () from rfl]
  change (∑ a : Fin 15, ∑ b : Fin 15,
    branch (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) (a,b,()) rhoN) = rhoN
  simp_rw [fixture_branch, FiniteThreeLevelPositiveHistory.branch_rhoN,
    FiniteThreeLevelPositiveHistory.Phi_Gamma,
    FiniteThreeLevelPositiveHistory.branch_Gamma]
  simp_rw [← FiniteThreeLevelPositiveHistory.Gamma_sum]
  have hs : (∑ a, ∑ b, FiniteThreeLevelPositiveHistory.J b
      (Psi r (FiniteThreeLevelPositiveHistory.effect a))) = 1 := by
    rw [Finset.sum_comm]
    change (∑ b, ∑ a, FiniteThreeLevelPositiveHistory.JLinear b
      (FiniteThreeLevelPositiveHistory.PsiLinear r (FiniteThreeLevelPositiveHistory.effect a))) = 1
    simp only [← map_sum, FiniteThreeLevelPositiveHistory.effect_sum]
    change (∑ b, FiniteThreeLevelPositiveHistory.J b (Psi r 1)) = 1
    simp only [FiniteThreeLevelPositiveHistory.Psi_unital, FiniteThreeLevelPositiveHistory.J_one]
    exact FiniteThreeLevelPositiveHistory.effect_sum
  rw [hs, FiniteThreeLevelPositiveHistory.Gamma_one]

theorem fixture_reverse_rho (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (a b : Fin 15) :
    joint (reverseBranch (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) (a,b,()) rhoN) =
      run Q Unit 15 (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) (b,a,()) (joint rhoN) := by
  rw [reverseBranch_rho, fixture_effect]
  exact (FiniteThreeLevelPositiveHistory.negative_run r hr hr1 (a,b)).symm

theorem fixture_kernel (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (a b c d : Fin 15) :
    kernel (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) (by norm_num)
      (fixture_stationary r hr hr1) p hp hp1 (a,b,()) (c,d,()) =
      FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1 (a,b) (c,d) := by
  rw [kernel_form, fixture_effect, fixture_effect,
    FiniteThreeLevelPositiveHistory.kernel_form]
  rfl

theorem done_effect (h : History 1 0) : effect (Tree.done : Tree Q Unit 1 0) h = 1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [← branch_trace]
  simp [branch, run, unJoint_joint]

theorem done_stationary : Stationary (Tree.done : Tree Q Unit 1 0) := by
  simp [Stationary, branch, History, run, unJoint_joint]

theorem done_kernel (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (u v : History 1 0) :
    kernel (Tree.done : Tree Q Unit 1 0) (by norm_num) done_stationary p hp hp1 u v = 1 := by
  rw [kernel_form, done_effect, done_effect, FiniteThreeLevelPositiveHistory.Psi_unital,
    FiniteThreeLevelPositiveHistory.form_one]

theorem done_rank (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Module.finrank ℂ (Reconstructed (Tree.done : Tree Q Unit 1 0) (by norm_num)
      done_stationary p hp hp1) = 1 := by
  rw [reconstructed_finrank]
  have he : accessible (Tree.done : Tree Q Unit 1 0) p = Submodule.span ℂ {(1 : MatQ)} := by
    unfold accessible
    simp only [done_effect, FiniteThreeLevelPositiveHistory.Psi_unital]
    congr 1
    ext A
    constructor
    · rintro ⟨h,rfl⟩; exact Set.mem_singleton _
    · intro hA
      exact ⟨(), (Set.mem_singleton_iff.mp hA).symm⟩
  rw [he]
  exact finrank_span_singleton (one_ne_zero : (1 : MatQ) ≠ 0)


open FiniteThreeLevelPositiveHistory (E D weights)

/-- The physical computational instrument, with identity evolution. -/
def computationalTree : Tree Q Unit 3 1 :=
  .node (localStep Q Unit 3 (GibbsMultilevelReflection.instrument 3)) (fun _ => .done)

theorem computational_projector (a : Q) : GibbsMultilevelReflection.projector a = D a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [GibbsMultilevelReflection.projector, D, E, Matrix.single, Matrix.diagonal_apply]

theorem computational_branch (a : Q) (X : MatQ) :
    branch computationalTree (a,()) X = X a a • D a := by
  unfold branch computationalTree
  rw [run, run, localStep_joint, unJoint_joint,
    GibbsMultilevelReflection.instrument_branch, computational_projector]

theorem computational_effect (a : Q) : effect computationalTree (a,()) = D a := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [← branch_trace, computational_branch, Matrix.trace_smul]
  simp [D, E, Matrix.trace_single_mul]

theorem rho_diagonal (i j : Q) : rhoN i j = if i=j then (weights i : ℂ) else 0 := rfl

theorem diagonal_expansion (x : Q → ℂ) : Matrix.diagonal x = ∑ a, x a • D a := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [D, E, Matrix.single, Matrix.sum_apply]
  · simp [D, E, Matrix.single, Matrix.sum_apply, ite_and, hij]

theorem computational_stationary : Stationary computationalTree := by
  change (∑ h : Q × Unit, branch computationalTree h rhoN) = rhoN
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  change (∑ a : Q, branch computationalTree (a,()) rhoN) = rhoN
  simp_rw [computational_branch, rho_diagonal, if_true]
  exact (diagonal_expansion (fun i => (weights i : ℂ))).symm

def diagonalLinear : (Q → ℂ) →ₗ[ℂ] MatQ where
  toFun := Matrix.diagonal
  map_add' x y := (Matrix.diagonal_add x y).symm
  map_smul' c x := by simp

/-- The accessible diagonal subspace, with its actual three-coordinate dimension. -/
def diagonalSpace : Submodule ℂ MatQ := diagonalLinear.range

theorem diagonalLinear_injective : Function.Injective diagonalLinear := by
  intro x y h
  funext i
  simpa [diagonalLinear] using congrArg (fun A : MatQ => A i i) h

theorem computational_span : effectSpan computationalTree = diagonalSpace := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro A ⟨⟨a,h⟩,rfl⟩
    cases h
    rw [computational_effect]
    refine ⟨fun i => if i=a then 1 else 0, ?_⟩
    exact computational_projector a
  · rintro A ⟨x,rfl⟩
    change Matrix.diagonal x ∈ effectSpan computationalTree
    rw [diagonal_expansion]
    apply Submodule.sum_mem
    intro a _
    apply Submodule.smul_mem
    rw [← computational_effect]
    exact Submodule.subset_span ⟨(a,()),rfl⟩

theorem diagonalSpace_finrank : Module.finrank ℂ diagonalSpace = 3 := by
  rw [diagonalSpace, LinearMap.finrank_range_of_inj diagonalLinear_injective]
  simp [Q]

theorem computational_midpoint (p : ℝ) (a : Q) :
    Psi p (effect computationalTree (a,())) =
      (p : ℂ) • D a + (1-p : ℂ) • ((weights a : ℂ) • (1 : MatQ)) := by
  rw [computational_effect, Psi]
  have hm : (rhoN * D a).trace = (weights a : ℂ) := by
    rw [Matrix.trace_mul_comm]
    simp [D, E, Matrix.trace_single_mul, rho_diagonal]
  rw [hm]

theorem computational_range (p : ℝ) (hp : 0 < p) :
    accessible computationalTree p = diagonalSpace := by
  rw [range_positive_eq_effect_span computationalTree p hp, computational_span]

theorem computational_rank (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    Module.finrank ℂ (Reconstructed computationalTree (by norm_num)
      computational_stationary p hp hp1) = 3 := by
  rw [reconstructed_finrank, computational_range p hpos, diagonalSpace_finrank]

theorem computational_reset_rank :
    Module.finrank ℂ (Reconstructed computationalTree (by norm_num)
      computational_stationary 0 (by norm_num) (by norm_num)) = 1 :=
  reset_finrank _ (by norm_num) computational_stationary

/-- Actual normalized preparation of D0; its raw reverse need not be normalized. -/
def preparationInstrument : FiniteInstrument Q 1 where
  count := 3
  operators _ j := E 0 j
  normalized := by
    simp only [Fin.sum_univ_one]
    ext i j
    by_cases hij : i = j
    · subst j; simp [E, Matrix.conjTranspose_single, Matrix.sum_apply, Matrix.single_apply]
    · simp [E, Matrix.conjTranspose_single, Matrix.sum_apply, Matrix.single_apply, ite_and, hij]

def preparationTree : Tree Q Unit 1 1 :=
  .node (localStep Q Unit 1 preparationInstrument) (fun _ => .done)

theorem preparation_branch (a : Fin 1) (X : MatQ) :
    branch preparationTree (a,()) X = X.trace • D 0 := by
  unfold branch preparationTree
  rw [run, run, localStep_joint, unJoint_joint]
  change (∑ j : Q, E 0 j * X * (E 0 j)ᴴ) = X.trace • D 0
  ext i k
  simp [E, D, Matrix.conjTranspose_single, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.single_apply, Matrix.trace]

theorem preparation_aggregate :
    (∑ h, branch preparationTree h rhoN) = D 0 := by
  change (∑ h : Fin 1 × Unit, branch preparationTree h rhoN) = D 0
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  change branch preparationTree (0,()) rhoN = D 0
  rw [preparation_branch, FiniteThreeLevelPositiveHistory.rhoN_trace, one_smul]

theorem preparation_not_stationary : ¬ Stationary preparationTree := by
  intro h
  change (∑ h, branch preparationTree h rhoN) = rhoN at h
  rw [preparation_aggregate] at h
  have hc := congrArg (fun A : MatQ => A 0 0) h
  norm_num [D, E, rho_diagonal] at hc
  rw [show weights 0 = 1/2 from rfl] at hc
  norm_num at hc

theorem inverseGamma_D (a : Q) :
    Rinv * D a * Rinv = ((weights a : ℂ)⁻¹) • D a := by
  have hs : (FiniteThreeLevelPositiveHistory.rdiag a : ℂ) *
      (FiniteThreeLevelPositiveHistory.rdiag a : ℂ) = (weights a : ℂ) := by
    exact_mod_cast FiniteThreeLevelPositiveHistory.rdiag_square a
  ext i j
  simp only [Rinv, Matrix.diagonal_mul, Matrix.mul_diagonal, D, E, Matrix.single_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs with hi
  · rcases hi with ⟨rfl,rfl⟩
    simp only [mul_one]
    rw [← mul_inv, hs]
  all_goals simp

theorem preparation_reverse_complete :
    (∑ h, ∑ z, (reverseKraus preparationTree h z)ᴴ * reverseKraus preparationTree h z) =
      (2 : ℂ) • D 0 := by
  rw [reverse_complete_formula, preparation_aggregate, inverseGamma_D]
  have hw : weights 0 = 1/2 := rfl
  rw [hw]
  norm_num

theorem preparation_reverse_not_complete :
    (∑ h, ∑ z, (reverseKraus preparationTree h z)ᴴ * reverseKraus preparationTree h z) ≠ 1 := by
  rw [preparation_reverse_complete]
  intro h
  have hc := congrArg (fun A : MatQ => A 0 0) h
  norm_num [D, E, Matrix.smul_apply] at hc

theorem preparation_reverse_trace_D1 :
    (∑ h, reverseBranch preparationTree h (D 1)).trace = 0 := by
  have ht (h : History 1 1) :
      (reverseBranch preparationTree h (D 1)).trace =
      ((∑ z, (reverseKraus preparationTree h z)ᴴ * reverseKraus preparationTree h z) * D 1).trace := by
    simp only [reverseBranch, Matrix.trace_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    rw [Matrix.trace_mul_cycle]
  simp only [Matrix.trace_sum]
  simp_rw [ht]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, preparation_reverse_complete]
  simp [D, E]


theorem preparation_path (j : Q) :
    systemPathKraus preparationTree (0,()) ((j,⟨0,by decide⟩),()) = E 0 j := by
  simp only [systemPathKraus, preparationTree, pathKraus, stepKraus,
    localStep, preparationInstrument, FiniteInstrument.lift, one_mul, mul_one]
  exact unJoint_joint _

theorem preparation_reverse_operator (j : Q) :
    reverseKraus preparationTree (0,()) ((j,⟨0,by decide⟩),()) =
      ((FiniteThreeLevelPositiveHistory.rdiag j : ℂ) /
        (FiniteThreeLevelPositiveHistory.rdiag 0 : ℂ)) • E j 0 := by
  rw [reverseKraus, preparation_path]
  ext i k
  simp only [E, Matrix.conjTranspose_single, star_one, R, Rinv, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩
    simp [div_eq_mul_inv]
  · simp

/-- Each continuation is separately stationary, with a common padded arity. -/
def stationaryContinuation (a : Q) : Tree Q Unit 3 1 :=
  if a = 0 then .node (localStep Q Unit 3 (idleInstrument 3 (by norm_num))) (fun _ => .done)
  else .node (resetOnlyStep 3 (by norm_num)) (fun _ => .done)

theorem stationaryContinuation_branch (a b : Q) (X : MatQ) :
    branch (stationaryContinuation a) (b,()) X =
      if b = 0 then (if a = 0 then X else X.trace • rhoN) else 0 := by
  by_cases ha : a = 0
  · simp only [stationaryContinuation, ha, if_true, branch, run, localStep_joint,
      unJoint_joint, idleInstrument_branch]
    rfl
  · simp only [stationaryContinuation, ha, if_false, branch, run, resetOnlyStep_branch,
      unJoint_joint]
    rfl

theorem stationaryContinuation_stationary (a : Q) : Stationary (stationaryContinuation a) := by
  change (∑ h : Q × Unit, branch (stationaryContinuation a) h rhoN) = rhoN
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  change (∑ b : Q, branch (stationaryContinuation a) (b,()) rhoN) = rhoN
  simp [stationaryContinuation_branch, FiniteThreeLevelPositiveHistory.rhoN_trace]

def stationaryFeedback : Tree Q Unit 3 2 :=
  .node (localStep Q Unit 3 (GibbsMultilevelReflection.instrument 3)) stationaryContinuation

theorem stationaryFeedback_branch (a b : Q) (X : MatQ) :
    branch stationaryFeedback (a,b,()) X =
      if b = 0 then (if a = 0 then X a a • D a else X a a • rhoN) else 0 := by
  change unJoint (run Q Unit 3 (stationaryContinuation a) (b,())
    ((localStep Q Unit 3 (GibbsMultilevelReflection.instrument 3)).branch Q Unit 3 a (joint X))) = _
  rw [localStep_joint, GibbsMultilevelReflection.instrument_branch, computational_projector]
  change branch (stationaryContinuation a) (b,()) (X a a • D a) = _
  rw [stationaryContinuation_branch]
  simp [D, E]

theorem stationaryFeedback_aggregate :
    (∑ h, branch stationaryFeedback h rhoN) =
      (1/2 : ℂ) • D 0 + (1/2 : ℂ) • rhoN := by
  change (∑ h : Q × Q × Unit, branch stationaryFeedback h rhoN) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  change (∑ a : Q, ∑ b : Q, branch stationaryFeedback (a,b,()) rhoN) = _
  simp_rw [stationaryFeedback_branch]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h0 : rhoN 0 0 = (1/2 : ℂ) := by
    norm_num [rho_diagonal, weights, GibbsMultilevelReflection.three,
      FinitePositiveKernel.GibbsReset.threeWeights]
  have h1 : rhoN 1 1 = (1/3 : ℂ) := by
    norm_num [rho_diagonal, weights, GibbsMultilevelReflection.three,
      FinitePositiveKernel.GibbsReset.threeWeights]
  have h2 : rhoN 2 2 = (1/6 : ℂ) := by
    change ((1/6 : ℝ) : ℂ) = 1/6
    norm_num
  have h20 : (2 : Q) ≠ 0 := by decide
  norm_num [h0,h1,h2,h20]
  module

theorem stationaryFeedback_output :
    (∑ h, branch stationaryFeedback h rhoN) =
      Matrix.diagonal ![(3/4 : ℂ),1/6,1/12] := by
  rw [stationaryFeedback_aggregate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, E, rho_diagonal, weights, GibbsMultilevelReflection.three,
      FinitePositiveKernel.GibbsReset.threeWeights]

theorem stationaryFeedback_not_stationary : ¬ Stationary stationaryFeedback := by
  intro h
  change (∑ h, branch stationaryFeedback h rhoN) = rhoN at h
  rw [stationaryFeedback_output] at h
  have hc := congrArg (fun A : MatQ => A 0 0) h
  norm_num [rho_diagonal, weights, GibbsMultilevelReflection.three,
    FinitePositiveKernel.GibbsReset.threeWeights] at hc

theorem stationaryFeedback_reverse_complete :
    (∑ h, ∑ z, (reverseKraus stationaryFeedback h z)ᴴ * reverseKraus stationaryFeedback h z) =
      Matrix.diagonal ![(3/2 : ℂ),1/2,1/2] := by
  rw [reverse_complete_formula, stationaryFeedback_aggregate, Matrix.mul_add, Matrix.add_mul]
  simp only [mul_smul_comm, smul_mul_assoc]
  rw [inverseGamma_D, show Rinv * rhoN * Rinv = 1 from inverseGamma_rho,
    show weights 0 = 1/2 from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [D, E]

theorem stationaryFeedback_reverse_not_complete :
    (∑ h, ∑ z, (reverseKraus stationaryFeedback h z)ᴴ * reverseKraus stationaryFeedback h z) ≠ 1 :=
  fun h => stationaryFeedback_not_stationary ((reverse_normalized_iff stationaryFeedback).mp h)

/-- The old frame coefficients still synthesize all observables in the actual fixture. -/
theorem fixture_coefficients (p r : ℝ) (hpos : 0 < p) (hr : 0 ≤ r) (hr1 : r ≤ 1) (A : MatQ) :
    synthesis (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) p
      (fun h => FiniteThreeLevelPositiveHistory.coefficients p A (h.1,h.2.1)) = A := by
  unfold synthesis
  change (∑ h : Fin 15 × Fin 15 × Unit, _) = A
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  change (∑ a : Fin 15, ∑ b : Fin 15,
    FiniteThreeLevelPositiveHistory.coefficients p A (a,b) •
      Psi p (effect (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) (a,b,()))) = A
  simp_rw [fixture_effect]
  have he := FiniteThreeLevelPositiveHistory.synthesis_coefficients hpos r A
  simpa only [FiniteThreeLevelPositiveHistory.synthesis, Fintype.sum_prod_type,
    FiniteThreeLevelPositiveHistory.midpoint] using he

theorem fixture_central_reset (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (f : FiniteThreeLevelPositiveHistory.HalfHistory → ℂ) :
    synthesis (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) 0
      (fun h => f (h.1,h.2.1)) = FiniteThreeLevelPositiveHistory.resetMean r f • (1 : MatQ) := by
  unfold synthesis
  change (∑ h : Fin 15 × Fin 15 × Unit, _) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  change (∑ a : Fin 15, ∑ b : Fin 15, f (a,b) •
    Psi 0 (effect (FiniteThreeLevelPositiveHistory.negativeTree r hr hr1) (a,b,()))) = _
  simp_rw [fixture_effect]
  have he := FiniteThreeLevelPositiveHistory.synthesis_full_reset r f
  simpa only [FiniteThreeLevelPositiveHistory.synthesis, Fintype.sum_prod_type,
    FiniteThreeLevelPositiveHistory.midpoint] using he

/-- Same effects do not justify substituting a different selected-state instrument. -/
theorem luders_controls :
    FiniteThreeLevelPositiveHistory.instrument.branch 3 rhoN 0 0 = 1/20 ∧
    FiniteThreeLevelPositiveHistory.luders.branch 3 rhoN 0 0 = 1/24 ∧
    FiniteThreeLevelPositiveHistory.instrument.branch 3 rhoN ≠
      FiniteThreeLevelPositiveHistory.luders.branch 3 rhoN ∧
    FiniteThreeLevelPositiveHistory.ludersKernel 0 3 -
      FiniteThreeLevelPositiveHistory.ludersKernel 3 0 = 1/600 ∧
    ¬ Matrix.IsHermitian FiniteThreeLevelPositiveHistory.ludersKernel ∧
    ¬ Matrix.PosSemidef FiniteThreeLevelPositiveHistory.ludersKernel ∧
    (∀ h, 0 ≤ weight Q Unit 15 FiniteThreeLevelPositiveHistory.ludersTree h (joint rhoN)) ∧
    (∑ h, weight Q Unit 15 FiniteThreeLevelPositiveHistory.ludersTree h (joint rhoN)) = 1 :=
  ⟨FiniteThreeLevelPositiveHistory.replacement_selected_output,
   FiniteThreeLevelPositiveHistory.luders_selected_output,
   FiniteThreeLevelPositiveHistory.selected_output_differs,
   FiniteThreeLevelPositiveHistory.luders_asymmetry,
   FiniteThreeLevelPositiveHistory.luders_not_hermitian,
   FiniteThreeLevelPositiveHistory.luders_not_posSemidef,
   FiniteThreeLevelPositiveHistory.luders_actual_probabilities⟩

open FiniteThreeLevelHistoryTransfer in
theorem timed_controls (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hp0 : 0 < p) {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ¬ (thermalKernel p r hp hp1 hr hr1 b ℏ γ (quarterTime b ℏ) hγ
      (quarterTime_positive hb hℏ).le).IsHermitian ∧
    (FinitePositiveKernel.pairing (thermalKernel p r hp hp1 hr hr1 b ℏ γ (halfTime b ℏ) hγ
      (halfTime_positive hb hℏ).le) (FiniteThreeLevelPositiveHistory.innerMode 2)
      (FiniteThreeLevelPositiveHistory.innerMode 2)).re =
        -Real.exp (-γ*halfTime b ℏ)*p^2*Real.sqrt 6/3 ∧
    (FinitePositiveKernel.pairing (thermalKernel p r hp hp1 hr hr1 b ℏ γ (halfTime b ℏ) hγ
      (halfTime_positive hb hℏ).le) (FiniteThreeLevelPositiveHistory.innerMode 2)
      (FiniteThreeLevelPositiveHistory.innerMode 2)).re < 0 :=
  ⟨timed_quarter_not_hermitian p r hp hp1 hr hr1 hp0 hb hℏ γ hγ,
    timed_half_negative p r hp hp1 hr hr1 hp0 hb hℏ γ hγ⟩

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyExamples

#check Nat
