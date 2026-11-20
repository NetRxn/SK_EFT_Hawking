import SKEFTHawking.QuantumNetwork.FiniteThreeLevelCoherentReadout
import SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness

/-! Physical qutrit controls and full-prefix adaptive readout policies.
The environment is the Unit spectator. Durations, measurement frames, control
pulses and dimensionless mixture rates have separate roles. Branch matrices
retain their mass, including impossible histories. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelAdaptiveReadout
open Matrix FinitePositiveKernel DiagonalLindblad GibbsObservable OpenSystems
open FiniteInterventionProcess GibbsMultilevelReflection GibbsMultilevelProcess
open FiniteThreeLevelThermalPhase FiniteThreeLevelCoherentReadout
open FiniteAdaptiveMapPerturbation FiniteAdaptiveMixtureSurvival
open FiniteAdaptiveReadoutDiscrimination FiniteAdaptiveReadoutRobustness
open scoped ComplexOrder Kronecker BigOperators

abbrev Q := Fin 3
abbrev MatQ := Matrix Q Q ℂ
abbrev J := Q × Unit
abbrev MatJ := Matrix J J ℂ

/-- External phase-flip pulse, independent of the waiting Hamiltonian. -/
def Z : MatQ := Matrix.diagonal ![1,-1,1]
def control (c : Bool) : MatQ := if c then Z else 1

theorem Z_adjoint : Zᴴ=Z := by
  simp [Z]
  intro i
  fin_cases i <;> norm_num
theorem Z_square : Z*Z=1 := by
  simp only [Z, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num
theorem control_adjoint (c : Bool) : (control c)ᴴ=control c := by
  cases c <;> simp [control, Z_adjoint]
theorem control_square (c : Bool) : control c*control c=1 := by
  cases c <;> simp [control, Z_square]
theorem control_unitary (c : Bool) : control c ∈ Matrix.unitaryGroup Q ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change control c*(control c)ᴴ=1
  rw [control_adjoint, control_square]

def exchange (a : Q) : Q := if a=0 then 1 else if a=1 then 0 else 2
theorem Z_projection (φ : ℝ) (a : Q) :
    Z*readProjection φ a*Zᴴ=readProjection φ (exchange a) := by
  rw [Z_adjoint]
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl
  · change Z*readProjection φ 0*Z=readProjection φ 1
    simp only [projection_zero_entries, projection_one_entries]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Z, Matrix.diagonal_mul, Matrix.mul_diagonal] <;> ring
  · change Z*readProjection φ 1*Z=readProjection φ 0
    simp only [projection_zero_entries, projection_one_entries]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Z, Matrix.diagonal_mul, Matrix.mul_diagonal] <;> ring
  · change Z*readProjection φ 2*Z=readProjection φ 2
    rw [projection_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Z, projector, Matrix.diagonal_mul, Matrix.mul_diagonal, Fin.ext_iff]
theorem control_equilibrium (c : Bool) :
    control c*equilibrium*(control c)ᴴ=equilibrium := by
  cases c
  · simp [control]
  · simp only [control, if_true, Z_adjoint]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Z, equilibrium, density, three, GibbsReset.threeWeights,
        Matrix.diagonal_mul, Matrix.mul_diagonal]
theorem control_projection_two (c : Bool) (φ : ℝ) :
    control c*readProjection φ 2*(control c)ᴴ=readProjection φ 2 := by
  cases c
  · simp [control]
  · simpa [control, exchange] using Z_projection φ 2

theorem C_compose (φ ψ : ℝ) (X : MatQ) : C φ (C ψ X)=C (φ+ψ) X := by
  ext i j
  simp only [C_entry, ← mul_assoc, ← Complex.exp_add, Complex.ofReal_add]
  congr 2
  ring
theorem phase_C (b ℏ t φ : ℝ) (X : MatQ) :
    phase b ℏ t (C φ X)=C φ (phase b ℏ t X) := by
  ext i j
  simp only [phase_entry, C_entry]
  ring
/-- Covariance at every readout frame, with the physical signed state phase. -/
theorem phase_projection (b ℏ t φ : ℝ) (a : Q) :
    phase b ℏ t (readProjection φ a)=readProjection (φ+theta b ℏ t) a := by
  rw [readProjection, phase_C, phase_on_base, readProjection, C_compose]
  rfl

/-- Right composition puts the control before the actual full Hamiltonian channel. -/
def controlledKraus (b ℏ γ t : ℝ) (c : Bool) :=
  fun k => joint (channelKraus b ℏ γ t k * control c)

theorem right_control_normalized {k : ℕ} (K : Fin k → MatQ)
    (hK : IsKrausChannel K) (c : Bool) :
    IsKrausChannel (fun k => K k*control c) := by
  unfold IsKrausChannel at hK ⊢
  calc
    _ = ∑ k, (control c)ᴴ*((K k)ᴴ*K k)*control c := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = (control c)ᴴ*(∑ k, (K k)ᴴ*K k)*control c := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = 1 := by rw [hK, Matrix.mul_one, control_adjoint, control_square]
theorem controlled_normalized (b ℏ γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t) (c : Bool) :
    IsKrausChannel (controlledKraus b ℏ γ t c) :=
  joint_normalized _ (right_control_normalized _ (channel_normalized b ℏ γ t hγ ht) c)

theorem right_control_action {k : ℕ} (K : Fin k → MatQ) (c : Bool) (X : MatQ) :
    krausMap (fun k => K k*control c) X =
      krausMap K (control c*X*(control c)ᴴ) := by
  unfold krausMap
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.conjTranspose_mul]
  noncomm_ring
theorem controlled_action (b ℏ γ t : ℝ) (c : Bool) (X : MatJ) :
    krausMap (controlledKraus b ℏ γ t c) X =
      joint (krausMap (channelKraus b ℏ γ t) (control c*unjoint X*(control c)ᴴ)) := by
  conv_lhs => arg 2; rw [← joint_unjoint X]
  change krausMap (fun k => joint (channelKraus b ℏ γ t k*control c))
    (joint (unjoint X))=_
  rw [joint_kraus, right_control_action]

structure Background where
  b : ℝ
  hbar : ℝ
  b_pos : 0<b
  hbar_pos : 0<hbar

/-- Node parameters may depend on every earlier outcome. -/
structure Setting where
  rate : ℝ
  duration : ℝ
  pulse : Bool
  frame : ℝ
  rate_nonneg : 0≤rate
  duration_nonneg : 0≤duration

def physicalStep (B : Background) (v : Setting) : Step Q Unit 3 :=
  realizedStep Q Unit 3 (controlledKraus B.b B.hbar v.rate v.duration v.pulse)
    (controlled_normalized _ _ _ _ v.rate_nonneg v.duration_nonneg _) (readout v.frame)

theorem physicalStep_action (B : Background) (v : Setting) (a : Q) (X : MatJ) :
    (physicalStep B v).branch Q Unit 3 a X = joint ((readout v.frame).branch a
      (krausMap (channelKraus B.b B.hbar v.rate v.duration)
        (control v.pulse*unjoint X*(control v.pulse)ᴴ))) := by
  change ((readout v.frame).lift Unit).branch a
    (krausMap (controlledKraus B.b B.hbar v.rate v.duration v.pulse) X)=_
  rw [controlled_action]
  exact joint_kraus _ _

theorem physicalStep_GKSL (B : Background) (v : Setting) (a : Q) (X : MatJ) :
    (physicalStep B v).branch Q Unit 3 a X = joint ((readout v.frame).branch a
      (lindbladPropagatorAction (scaledH B.b B.hbar) (jumps v.rate) v.duration
        (control v.pulse*unjoint X*(control v.pulse)ᴴ))) := by
  rw [physicalStep_action, channel_propagator _ _ _ _ v.rate_nonneg v.duration_nonneg]

def noisyStep (B : Background) (v w : Setting) (r : NoiseRates) : Step Q Unit 3 :=
  mixedStep Q Unit 3
    (controlledKraus B.b B.hbar v.rate v.duration v.pulse)
    (controlledKraus B.b B.hbar w.rate w.duration w.pulse)
    (controlled_normalized _ _ _ _ v.rate_nonneg v.duration_nonneg _)
    (controlled_normalized _ _ _ _ w.rate_nonneg w.duration_nonneg _)
    (readout v.frame) (readout w.frame) r.p r.q r.hp r.hp1 r.hq r.hq1

def physicalRealization (B : Background) (v w : Setting) (r : NoiseRates) :
    RealizesMixture Q Unit 3 (physicalStep B v) (noisyStep B v w r) r.p r.q where
  k := _
  l := _
  K := controlledKraus B.b B.hbar v.rate v.duration v.pulse
  L := controlledKraus B.b B.hbar w.rate w.duration w.pulse
  hK := controlled_normalized _ _ _ _ v.rate_nonneg v.duration_nonneg _
  hL := controlled_normalized _ _ _ _ w.rate_nonneg w.duration_nonneg _
  D := readout v.frame
  D' := readout w.frame
  hp := r.hp
  hp1 := r.hp1
  hq := r.hq
  hq1 := r.hq1
  ideal_action _ _ := rfl
  mixed_action _ _ := rfl

/-- Each subtree can differ at every full prefix; rates alone are depthwise uniform. -/
inductive Policy : ℕ → Type
  | done : Policy 0
  | node {n : ℕ} (nominal alternative : Setting) (next : Q → Policy n) : Policy (n+1)

def ideal (B : Background) : {n : ℕ} → Policy n → Tree Q Unit 3 n
  | _, .done => .done
  | _, .node v _ next => .node (physicalStep B v) (fun a => ideal B (next a))

def noisy (B : Background) : {n : ℕ} → Policy n →
    (rs : List NoiseRates) → rs.length=n → Tree Q Unit 3 n
  | _, .done, _, _ => .done
  | _, .node v w next, r::rs, h =>
      .node (noisyStep B v w r) (fun a => noisy B (next a) rs (Nat.succ.inj h))

theorem compiler_mixture (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (h : rs.length=n) :
    PairedMixture Q Unit 3 (ideal B P) (noisy B P rs h) rs := by
  induction P generalizing rs with
  | done =>
    have he : rs=[] := by simpa using h
    subst rs
    exact .done
  | @node n v w next ih =>
    cases rs with
    | nil => simp at h
    | cons r rs =>
      exact .node (physicalRealization B v w r) (Nat.succ.inj h)
        (fun a => ih a rs (Nat.succ.inj h))

/-- The additive certificate has the mixed-then-ideal orientation. -/
theorem compiler_errors (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (h : rs.length=n) :
    PairedErrors Q Unit 3 (noisy B P rs h) (ideal B P) (rs.map (fun r => r.p+r.q)) := by
  induction P generalizing rs with
  | done =>
    have he : rs=[] := by simpa using h
    subst rs
    exact .done
  | @node n v w next ih =>
    cases rs with
    | nil => simp at h
    | cons r rs =>
      apply PairedErrors.node
      · exact mixed_both_localError Q Unit 3 _ _
          (controlled_normalized _ _ _ _ v.rate_nonneg v.duration_nonneg _)
          (controlled_normalized _ _ _ _ w.rate_nonneg w.duration_nonneg _)
          _ _ _ _ r.hp r.hp1 r.hq r.hq1
      · simpa using Nat.succ.inj h
      · exact fun a => ih a rs (Nat.succ.inj h)

/-- Both cross terms remain actual physical branches with independently chosen frames. -/
theorem noisyStep_four (B : Background) (v w : Setting) (r : NoiseRates)
    (a : Q) (X : MatJ) :
    (noisyStep B v w r).branch Q Unit 3 a X =
      ((1-r.p)*(1-r.q)) • (physicalStep B v).branch Q Unit 3 a X +
      (r.p*(1-r.q)) • (physicalStep B {w with frame := v.frame}).branch Q Unit 3 a X +
      ((1-r.p)*r.q) • (physicalStep B {v with frame := w.frame}).branch Q Unit 3 a X +
      (r.p*r.q) • (physicalStep B w).branch Q Unit 3 a X :=
  mixedStep_branch Q Unit 3 _ _ _ _ _ _ _ _ _ _ _ _ a X

theorem compiled_distance (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (h : rs.length=n) {X Y : MatJ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance Q Unit 3 (ideal B P) (noisy B P rs h) X Y ≤
      survival rs*traceDist X Y+1-survival rs :=
  pairedMixture_changed_input Q Unit 3 (compiler_mixture B P rs h) hX hY

theorem compiled_additive (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (h : rs.length=n) {X Y : MatJ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance Q Unit 3 (ideal B P) (noisy B P rs h) X Y ≤
      min 1 (traceDist X Y+(rs.map (fun r => r.p+r.q)).sum) := by
  rw [outputDistance_comm]
  simpa only [traceDist_comm Y X] using
    pairedErrors_capped Q Unit 3 (compiler_errors B P rs h) hY hX

theorem compiled_history (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (h : rs.length=n) {X Y : MatJ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    historyVariation Q Unit 3 (ideal B P) (noisy B P rs h) X Y ≤
      survival rs*traceDist X Y+1-survival rs :=
  pairedMixture_history Q Unit 3 (compiler_mixture B P rs h) hX hY

theorem compiled_terminal (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (h : rs.length=n) {X Y : MatJ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    traceDist (terminalState Q Unit 3 (ideal B P) X)
      (terminalState Q Unit 3 (noisy B P rs h) Y) ≤
      survival rs*traceDist X Y+1-survival rs :=
  pairedMixture_terminal Q Unit 3 (compiler_mixture B P rs h) hX hY

theorem compiled_remainder (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (hlen : rs.length=n) (h : History 3 n)
    {X : MatJ} (hX : X.PosSemidef) :
    (run Q Unit 3 (noisy B P rs hlen) h X-
      survival rs • run Q Unit 3 (ideal B P) h X).PosSemidef :=
  pairedMixture_remainder Q Unit 3 (compiler_mixture B P rs hlen) h hX

theorem compiled_remainder_mass (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (hlen : rs.length=n) (X : MatJ) :
    (∑ h, (run Q Unit 3 (noisy B P rs hlen) h X-
      survival rs • run Q Unit 3 (ideal B P) h X).trace.re) =
      (1-survival rs)*X.trace.re :=
  pairedMixture_remainder_mass Q Unit 3 _ _ rs X

theorem compiled_zero_noise (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (hlen : rs.length=n)
    (hz : ∀ r∈rs, r.p=0 ∧ r.q=0) (h : History 3 n) (X : MatJ) :
    run Q Unit 3 (noisy B P rs hlen) h X=run Q Unit 3 (ideal B P) h X :=
  pairedMixture_zero_action Q Unit 3 (compiler_mixture B P rs hlen) hz h X

def equilibriumWeight : Q → ℝ := ![5/12,5/12,1/6]
def row (η : ℝ) (a j : Q) : ℝ :=
  η*(if j=a then 1 else 0)+(1-η)*equilibriumWeight j

theorem readout_equilibrium (φ : ℝ) (a : Q) :
    (readout φ).branch a equilibrium=(equilibriumWeight a:ℂ) • readProjection φ a := by
  rw [readout_branch]
  have h := trace_probability 0 φ φ false a
  simp only [mixture, Complex.ofReal_zero, Complex.ofReal_one,
    sub_zero, one_smul, zero_smul, add_zero] at h
  rw [h]
  congr 2
  fin_cases a <;> norm_num [probability, equilibriumWeight]

theorem readout_projection (φ : ℝ) (a j : Q) :
    (readout φ).branch j (readProjection φ a) =
      (if j=a then (1:ℂ) else 0) • readProjection φ j := by
  rw [readout_branch]
  by_cases h : j=a
  · subst j
    rw [projection_square, (projection_density φ a).2]
    simp
  · rw [projection_orthogonal φ j a h]
    simp [h]

theorem channel_projection (B : Background) (γ d φ : ℝ) (hγ : 0≤γ) (hd : 0≤d)
    (a : Q) :
    krausMap (channelKraus B.b B.hbar γ d) (readProjection φ a) =
      (Real.exp (-γ*d):ℂ) • readProjection (φ+theta B.b B.hbar d) a +
      ((1-Real.exp (-γ*d):ℝ):ℂ) • equilibrium := by
  rw [channel_action _ _ _ _ hγ hd, reset_action _ _ hγ hd,
    (projection_density φ a).2, one_smul, phase_add, phase_smul, phase_smul,
    phase_projection, show phase B.b B.hbar d equilibrium=equilibrium from phase_diagonal _ _ _ _]

theorem transition_branch (B : Background) (γ d φ : ℝ) (hγ : 0≤γ) (hd : 0≤d)
    (a j : Q) :
    (readout (φ+theta B.b B.hbar d)).branch j
      (krausMap (channelKraus B.b B.hbar γ d) (readProjection φ a)) =
      (row (Real.exp (-γ*d)) a j:ℂ) • readProjection (φ+theta B.b B.hbar d) j := by
  rw [channel_projection _ _ _ _ hγ hd, FiniteInstrument.branch_add,
    FiniteInstrument.branch_smul, FiniteInstrument.branch_smul,
    readout_projection, readout_equilibrium]
  simp only [smul_smul, ← add_smul, row]
  congr 1
  split_ifs <;> push_cast <;> ring

theorem projection_pi (φ : ℝ) (a : Q) :
    readProjection (φ+Real.pi) a=readProjection φ (exchange a) := by
  have hp : Complex.exp (Complex.I*(φ+Real.pi:ℝ)) = -Complex.exp (Complex.I*φ) := by
    push_cast
    rw [mul_add, Complex.exp_add, mul_comm Complex.I (Real.pi:ℂ), Complex.exp_pi_mul_I]
    ring
  have hm : Complex.exp (-Complex.I*(φ+Real.pi:ℝ)) = -Complex.exp (-Complex.I*φ) := by
    have e : -Complex.I*((φ:ℂ)+(Real.pi:ℂ)) =
      -Complex.I*φ+-(Real.pi*Complex.I) := by ring
    push_cast
    rw [e, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl
  · change readProjection (φ+Real.pi) 0=readProjection φ 1
    rw [projection_zero_entries, projection_one_entries, hp, hm]
  · change readProjection (φ+Real.pi) 1=readProjection φ 0
    rw [projection_one_entries, projection_zero_entries, hp, hm]
    simp
  · change readProjection (φ+Real.pi) 2=readProjection φ 2
    simp only [projection_two]

theorem readout_pi (φ : ℝ) (a : Q) (X : MatQ) :
    (readout (φ+Real.pi)).branch a X=(readout φ).branch (exchange a) X := by
  simp only [readout_branch, projection_pi]

theorem unjoint_joint (X : MatQ) : unjoint (joint X)=X := by
  ext i j
  simp [unjoint, joint]

theorem physicalStep_joint (B : Background) (v : Setting) (a : Q) (X : MatQ) :
    (physicalStep B v).branch Q Unit 3 a (joint X) = joint ((readout v.frame).branch a
      (krausMap (channelKraus B.b B.hbar v.rate v.duration)
        (control v.pulse*X*(control v.pulse)ᴴ))) := by
  rw [physicalStep_action, unjoint_joint]

theorem control_projection (c : Bool) (φ : ℝ) (a : Q) :
    control c*readProjection φ a*(control c)ᴴ =
      readProjection φ (if c then exchange a else a) := by
  cases c
  · simp [control]
  · simpa [control] using Z_projection φ a

def rootSetting (_φ : ℝ) (c : Bool) (ψ : ℝ) : Setting :=
  ⟨0,0,c,ψ,le_rfl,le_rfl⟩

structure Experiment where
  background : Background
  rate : ℝ
  duration : ℝ
  frame : ℝ
  rate_nonneg : 0≤rate
  duration_nonneg : 0≤duration

def Experiment.decay (E : Experiment) : ℝ := Real.exp (-E.rate*E.duration)
def Experiment.finalFrame (E : Experiment) : ℝ :=
  E.frame+theta E.background.b E.background.hbar E.duration
def Experiment.tail (E : Experiment) (c : Bool) : Setting :=
  ⟨E.rate,E.duration,c,E.finalFrame,E.rate_nonneg,E.duration_nonneg⟩

theorem tail_projection (E : Experiment) (c : Bool) (a j : Q) :
    (physicalStep E.background (E.tail c)).branch Q Unit 3 j (joint (readProjection E.frame a)) =
      (row E.decay (if c then exchange a else a) j:ℂ) •
        joint (readProjection E.finalFrame j) := by
  rw [physicalStep_joint]
  change joint ((readout E.finalFrame).branch j
    (krausMap (channelKraus E.background.b E.background.hbar E.rate E.duration)
      (control c*readProjection E.frame a*(control c)ᴴ)))=_
  rw [control_projection]
  dsimp only [Experiment.finalFrame, Experiment.decay]
  rw [transition_branch E.background E.rate E.duration E.frame E.rate_nonneg E.duration_nonneg]
  simp only [joint, Matrix.smul_kronecker]

def alignedInput (s φ : ℝ) (hyp : Bool) : MatQ :=
  mixture s (readProjection φ (if hyp then 1 else 0))
def rootWeight (s : ℝ) (hyp : Bool) (a : Q) : ℝ :=
  probability s 0 0 hyp a
def feedbackIndex (a : Q) : Q := if a=2 then 2 else 0

theorem aligned_readout (s φ : ℝ) (hyp : Bool) (a : Q) :
    (readout φ).branch a (alignedInput s φ hyp)=
      (rootWeight s hyp a:ℂ) • readProjection φ a := by
  rw [readout_branch, alignedInput, trace_probability]
  congr 2
  simp [rootWeight, probability]

def experimentPolicy (E : Experiment) (feedback : Bool) : Policy 2 :=
  .node (rootSetting E.frame false E.frame) (rootSetting E.frame true (E.frame+Real.pi))
    (fun a => .node (E.tail (feedback && decide (a=1)))
      (E.tail (feedback && decide (a=1))) (fun _ => .done))

def idealFamily (E : Experiment) (feedback : Bool) (s : ℝ) (hyp : Bool) : History 3 2 → MatJ :=
  fun h => run Q Unit 3 (ideal E.background (experimentPolicy E feedback)) h
    (joint (alignedInput s E.frame hyp))

theorem root_branch (E : Experiment) (s : ℝ) (hyp : Bool) (a : Q) :
    (physicalStep E.background (rootSetting E.frame false E.frame)).branch Q Unit 3 a
      (joint (alignedInput s E.frame hyp)) =
      (rootWeight s hyp a:ℂ) • joint (readProjection E.frame a) := by
  rw [physicalStep_joint]
  simp only [rootSetting, control, Bool.false_eq_true, if_false,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  rw [channel_zero_time _ _ _ le_rfl, aligned_readout]
  simp only [joint, Matrix.smul_kronecker]

/-- All nine matrices, before any branch is traced or normalized. -/
theorem ideal_nine (E : Experiment) (feedback : Bool) (s : ℝ) (hyp : Bool) (a j : Q) :
    idealFamily E feedback s hyp (a,j,()) =
      (rootWeight s hyp a * row E.decay (if feedback then feedbackIndex a else a) j:ℂ) •
        joint (readProjection E.finalFrame j) := by
  change (physicalStep E.background (E.tail (feedback && decide (a=1)))).branch Q Unit 3 j
    ((physicalStep E.background (rootSetting E.frame false E.frame)).branch Q Unit 3 a
      (joint (alignedInput s E.frame hyp)))=_
  have hi : (if feedback && decide (a=1) then exchange a else a) =
      (if feedback then feedbackIndex a else a) := by
    cases feedback
    · simp
    · have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
      rcases ha with rfl | rfl | rfl <;> norm_num [exchange, feedbackIndex, Fin.ext_iff]
  rw [root_branch, Step.branch_smul, tail_projection, hi, smul_smul]

theorem control_mixture (c : Bool) (s : ℝ) (X : MatQ) :
    control c*mixture s X*(control c)ᴴ = mixture s (control c*X*(control c)ᴴ) := by
  simp only [mixture, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    control_equilibrium]

theorem control_aligned (c : Bool) (s φ : ℝ) (hyp : Bool) :
    control c*alignedInput s φ hyp*(control c)ᴴ =
      alignedInput s φ (if c then !hyp else hyp) := by
  rw [alignedInput, control_mixture, control_projection]
  cases c <;> cases hyp <;> rfl

theorem physical_root_action (B : Background) (c : Bool) (s φ ψ : ℝ)
    (hyp : Bool) (a : Q) :
    (physicalStep B (rootSetting φ c ψ)).branch Q Unit 3 a (joint (alignedInput s φ hyp)) =
      joint ((readout ψ).branch a (alignedInput s φ (if c then !hyp else hyp))) := by
  rw [physicalStep_joint]
  change joint ((readout ψ).branch a
    (krausMap (channelKraus B.b B.hbar 0 0)
      (control c*alignedInput s φ hyp*(control c)ᴴ)))=_
  rw [channel_zero_time _ _ _ le_rfl, control_aligned]

def noisyWeight (s p : ℝ) (hyp : Bool) (a : Q) : ℝ :=
  (1-p)*rootWeight s hyp a+p*rootWeight s (!hyp) a

theorem noisyWeight_formula (s p : ℝ) (hyp : Bool) (a : Q) :
    noisyWeight s p hyp a =
      if a=0 then (5+s)/12+(if hyp then -1 else 1)*(1-2*p)*s/2
      else if a=1 then (5+s)/12-(if hyp then -1 else 1)*(1-2*p)*s/2
      else (1-s)/6 := by
  cases hyp <;> simp [noisyWeight, rootWeight, probability]
  all_goals split_ifs <;> ring

theorem noisy_root (E : Experiment) (r : NoiseRates) (s : ℝ) (hyp : Bool) (a : Q) :
    (noisyStep E.background (rootSetting E.frame false E.frame)
      (rootSetting E.frame true (E.frame+Real.pi)) r).branch Q Unit 3 a
        (joint (alignedInput s E.frame hyp)) =
      ((1-r.q)*noisyWeight s r.p hyp a:ℂ) • joint (readProjection E.frame a) +
      (r.q*noisyWeight s r.p hyp (exchange a):ℂ) •
        joint (readProjection E.frame (exchange a)) := by
  rw [noisyStep_four]
  change ((1-r.p)*(1-r.q)) •
      (physicalStep E.background (rootSetting E.frame false E.frame)).branch Q Unit 3 a _ +
    (r.p*(1-r.q)) •
      (physicalStep E.background (rootSetting E.frame true E.frame)).branch Q Unit 3 a _ +
    ((1-r.p)*r.q) •
      (physicalStep E.background (rootSetting E.frame false (E.frame+Real.pi))).branch Q Unit 3 a _ +
    (r.p*r.q) •
      (physicalStep E.background (rootSetting E.frame true (E.frame+Real.pi))).branch Q Unit 3 a _ = _
  rw [physical_root_action E.background false s E.frame E.frame hyp a,
    physical_root_action E.background true s E.frame E.frame hyp a,
    physical_root_action E.background false s E.frame (E.frame+Real.pi) hyp a,
    physical_root_action E.background true s E.frame (E.frame+Real.pi) hyp a]
  simp only [Bool.false_eq_true, if_false, if_true,
    readout_pi, aligned_readout, joint, Matrix.smul_kronecker]
  have hr (x : ℝ) (X : MatJ) : x • X=(x:ℂ) • X := by
    ext i j
    simp [Complex.real_smul]
  simp only [hr, smul_smul, noisyWeight, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_mul]
  module

def noisyFamily (E : Experiment) (feedback : Bool) (r : NoiseRates)
    (s : ℝ) (hyp : Bool) : History 3 2 → MatJ :=
  fun h => run Q Unit 3
    (noisy E.background (experimentPolicy E feedback) [r,zeroRates] rfl) h
    (joint (alignedInput s E.frame hyp))

theorem noisy_step_zero (B : Background) (v w : Setting) (a : Q) (X : MatJ) :
    (noisyStep B v w zeroRates).branch Q Unit 3 a X =
      (physicalStep B v).branch Q Unit 3 a X := by
  rw [noisyStep_four]
  simp [zeroRates]

/-- The exact noisy experiment, including both independent fields and their cross terms. -/
theorem noisy_nine (E : Experiment) (feedback : Bool) (r : NoiseRates)
    (s : ℝ) (hyp : Bool) (a j : Q) :
    noisyFamily E feedback r s hyp (a,j,()) =
      (((1-r.q)*noisyWeight s r.p hyp a*
          row E.decay (if feedback && decide (a=1) then exchange a else a) j +
        r.q*noisyWeight s r.p hyp (exchange a)*
          row E.decay (if feedback && decide (a=1) then exchange (exchange a) else exchange a) j:ℝ):ℂ) •
        joint (readProjection E.finalFrame j) := by
  change (noisyStep E.background (E.tail (feedback && decide (a=1)))
    (E.tail (feedback && decide (a=1))) zeroRates).branch Q Unit 3 j
    ((noisyStep E.background (rootSetting E.frame false E.frame)
      (rootSetting E.frame true (E.frame+Real.pi)) r).branch Q Unit 3 a
        (joint (alignedInput s E.frame hyp)))=_
  rw [noisy_step_zero, noisy_root, Step.branch_add, Step.branch_smul,
    Step.branch_smul, tail_projection, tail_projection]
  simp only [smul_smul, ← add_smul, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one]

def idealCoefficient (feedback : Bool) (s η : ℝ) (hyp : Bool) (a j : Q) : ℝ :=
  rootWeight s hyp a*row η (if feedback then feedbackIndex a else a) j
def noisyCoefficient (feedback : Bool) (s η p q : ℝ) (hyp : Bool) (a j : Q) : ℝ :=
  (1-q)*noisyWeight s p hyp a*
    row η (if feedback && decide (a=1) then exchange a else a) j +
  q*noisyWeight s p hyp (exchange a)*
    row η (if feedback && decide (a=1) then exchange (exchange a) else exchange a) j

theorem ideal_matrix (E : Experiment) (feedback : Bool) (s : ℝ) (hyp : Bool) (h : History 3 2) :
    idealFamily E feedback s hyp h =
      (idealCoefficient feedback s E.decay hyp h.1 h.2.1:ℂ) •
        joint (readProjection E.finalFrame h.2.1) := by
  rcases h with ⟨a,j,⟨⟩⟩
  simpa only [idealCoefficient, Complex.ofReal_mul] using ideal_nine E feedback s hyp a j
theorem noisy_matrix (E : Experiment) (feedback : Bool) (r : NoiseRates) (s : ℝ)
    (hyp : Bool) (h : History 3 2) :
    noisyFamily E feedback r s hyp h =
      (noisyCoefficient feedback s E.decay r.p r.q hyp h.1 h.2.1:ℂ) •
        joint (readProjection E.finalFrame h.2.1) := by
  rcases h with ⟨a,j,⟨⟩⟩
  exact noisy_nine E feedback r s hyp a j

theorem row_sum (η : ℝ) (a : Q) : ∑ j, row η a j=1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change row η a 0+(row η a 1+row η a 2)=1
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl <;>
    norm_num [row, equilibriumWeight, Matrix.cons_val_two, Fin.ext_iff] <;> ring
theorem row_nonneg {η : ℝ} (hη : 0≤η) (hη1 : η≤1) (a j : Q) : 0≤row η a j := by
  have he : 0≤equilibriumWeight j := by fin_cases j <;> norm_num [equilibriumWeight]
  unfold row
  positivity
theorem row_pos {η : ℝ} (hη : 0≤η) (hη1 : η<1) (a j : Q) : 0<row η a j := by
  have he : 0<equilibriumWeight j := by fin_cases j <;> norm_num [equilibriumWeight]
  unfold row
  positivity

theorem decay_mem (E : Experiment) : E.decay∈Set.Ioc (0:ℝ) 1 :=
  ⟨Real.exp_pos _, GibbsReset.exp_rate_le_one _ _ E.rate_nonneg E.duration_nonneg⟩
theorem rootWeight_pos {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (hyp : Bool) (a : Q) :
    0<rootWeight s hyp a := by
  cases hyp <;> fin_cases a <;> norm_num [rootWeight, probability, Fin.ext_iff] <;> linarith
theorem noisyWeight_pos {s p : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (hp : 0≤p) (hp1 : p≤1)
    (hyp : Bool) (a : Q) : 0<noisyWeight s p hyp a := by
  have h0 := rootWeight_pos hs hs1 hyp a
  have h1 := rootWeight_pos hs hs1 (!hyp) a
  unfold noisyWeight
  have hx := mul_nonneg (sub_nonneg.mpr hp1) h0.le
  have hy := mul_nonneg hp h1.le
  by_cases hz : p=0
  · simp [hz, h0]
  · have ht := mul_pos (lt_of_le_of_ne hp (Ne.symm hz)) h1
    linarith

def signWeight (s : ℝ) (a : Q) : ℝ := if a=0 then s else if a=1 then -s else 0
def contrast (η q : ℝ) (j : Q) : ℝ := (1-q)*row η 0 j-q*row η 1 j

theorem ideal_signed (s η : ℝ) (a j : Q) :
    idealCoefficient true s η false a j-idealCoefficient true s η true a j =
      signWeight s a*row η 0 j := by
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl <;>
    norm_num [idealCoefficient, rootWeight, probability, feedbackIndex, signWeight, Fin.ext_iff] <;> ring

theorem noisy_signed (s η p q : ℝ) (a j : Q) :
    noisyCoefficient true s η p q false a j-noisyCoefficient true s η p q true a j =
      signWeight s a*(1-2*p)*contrast η q j := by
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl <;>
    norm_num [noisyCoefficient, noisyWeight, rootWeight, probability,
      exchange, signWeight, contrast, Fin.ext_iff] <;> ring

theorem scalar_projection_trace (u φ : ℝ) (j : Q) :
    ((u:ℂ) • joint (readProjection φ j)).trace.re=u := by
  rw [Matrix.trace_smul, joint_trace, (projection_density φ j).2]
  simp
theorem scalar_projection_distance (u v φ : ℝ) (j : Q) :
    traceDist ((u:ℂ) • joint (readProjection φ j))
      ((v:ℂ) • joint (readProjection φ j)) = |u-v|/2 := by
  unfold traceDist
  rw [← sub_smul, ← Complex.ofReal_sub, traceNorm_eq_physlib, Matrix.traceNorm_smul,
    ← traceNorm_eq_physlib, traceNorm_density_eq_one (joint_density (projection_density φ j)),
    Complex.norm_real, Real.norm_eq_abs]
  ring

theorem ideal_distance (E : Experiment) {s : ℝ} (hs : 0 ≤ s) :
    branchDistance (idealFamily E true s false) (idealFamily E true s true)=s := by
  unfold branchDistance
  simp only [ideal_matrix, scalar_projection_distance, ideal_signed]
  change (∑ h : Q × Q × Unit, |signWeight s h.1*row E.decay 0 h.2.1|/2)=s
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, abs_mul,
    abs_of_nonneg (row_nonneg (decay_mem E).1.le (decay_mem E).2 0 _)]
  simp_rw [← Finset.sum_div, ← Finset.mul_sum, row_sum, mul_one]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (|signWeight s 0|+(|signWeight s 1|+|signWeight s 2|))/2=s
  norm_num [signWeight, Fin.ext_iff, abs_of_nonneg hs]

theorem noisy_distance (E : Experiment) (r : NoiseRates) {s : ℝ} (hs : 0 ≤ s) :
    branchDistance (noisyFamily E true r s false) (noisyFamily E true r s true)=
      s * |1-2*r.p| * ∑ j, |contrast E.decay r.q j| := by
  unfold branchDistance
  simp only [noisy_matrix, scalar_projection_distance, noisy_signed]
  change (∑ h : Q × Q × Unit, |signWeight s h.1*(1-2*r.p)*contrast E.decay r.q h.2.1|/2)=_
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, abs_mul]
  simp_rw [← Finset.sum_div, ← Finset.mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [signWeight, Matrix.cons_val_two, Fin.ext_iff, abs_of_nonneg hs]

theorem ideal_valid (E : Experiment) (feedback : Bool) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hyp : Bool) : IsBranchFamily (idealFamily E feedback s hyp) :=
  run_family _ (joint_density (mixture_density hs hs1 (projection_density _ _)))
theorem noisy_valid (E : Experiment) (feedback : Bool) (r : NoiseRates)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hyp : Bool) :
    IsBranchFamily (noisyFamily E feedback r s hyp) :=
  run_family _ (joint_density (mixture_density hs hs1 (projection_density _ _)))

theorem ideal_variation_distance (E : Experiment) (feedback : Bool) (s : ℝ) :
    familyHistoryVariation (idealFamily E feedback s false) (idealFamily E feedback s true) =
      branchDistance (idealFamily E feedback s false) (idealFamily E feedback s true) := by
  unfold familyHistoryVariation branchDistance
  simp only [ideal_matrix, scalar_projection_trace, scalar_projection_distance, Finset.sum_div]
theorem noisy_variation_distance (E : Experiment) (feedback : Bool) (r : NoiseRates) (s : ℝ) :
    familyHistoryVariation (noisyFamily E feedback r s false) (noisyFamily E feedback r s true) =
      branchDistance (noisyFamily E feedback r s false) (noisyFamily E feedback r s true) := by
  unfold familyHistoryVariation branchDistance
  simp only [noisy_matrix, scalar_projection_trace, scalar_projection_distance, Finset.sum_div]

theorem ideal_signed_matrix (E : Experiment) (s : ℝ) (a j : Q) :
    idealFamily E true s false (a,j,())-idealFamily E true s true (a,j,()) =
      (signWeight s a*row E.decay 0 j:ℂ) • joint (readProjection E.finalFrame j) := by
  rw [ideal_matrix, ideal_matrix, ← sub_smul, ← Complex.ofReal_sub, ideal_signed]
  simp only [Complex.ofReal_mul]
theorem noisy_signed_matrix (E : Experiment) (r : NoiseRates) (s : ℝ) (a j : Q) :
    noisyFamily E true r s false (a,j,())-noisyFamily E true r s true (a,j,()) =
      (signWeight s a*(1-2*r.p)*contrast E.decay r.q j:ℂ) •
        joint (readProjection E.finalFrame j) := by
  rw [noisy_matrix, noisy_matrix, ← sub_smul, ← Complex.ofReal_sub, noisy_signed]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]

theorem sum_signed_support (s c φ : ℝ) (j : Q) :
    (∑ a, (signWeight s a*c:ℂ) • joint (readProjection φ j))=0 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (signWeight s 0*c:ℂ) • joint (readProjection φ j) +
    ((signWeight s 1*c:ℂ) • joint (readProjection φ j)+
    (signWeight s 2*c:ℂ) • joint (readProjection φ j))=0
  norm_num [signWeight, Fin.ext_iff]

theorem ideal_terminal_equal (E : Experiment) (s : ℝ) :
    (∑ h, idealFamily E true s false h)=(∑ h, idealFamily E true s true h) := by
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  change (∑ h : Q × Q × Unit, (idealFamily E true s false h-idealFamily E true s true h))=0
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  change (∑ a : Q, ∑ j : Q, (idealFamily E true s false (a,j,())-
    idealFamily E true s true (a,j,())))=0
  simp only [ideal_signed_matrix]
  rw [Finset.sum_comm]
  simp only [sum_signed_support, Finset.sum_const_zero]

theorem noisy_terminal_equal (E : Experiment) (r : NoiseRates) (s : ℝ) :
    (∑ h, noisyFamily E true r s false h)=(∑ h, noisyFamily E true r s true h) := by
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  change (∑ h : Q × Q × Unit, (noisyFamily E true r s false h-noisyFamily E true r s true h))=0
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  change (∑ a : Q, ∑ j : Q, (noisyFamily E true r s false (a,j,())-
    noisyFamily E true r s true (a,j,())))=0
  simp only [noisy_signed_matrix]
  have hc : (1-2*(r.p:ℂ))=((1-2*r.p:ℝ):ℂ) := by push_cast; rfl
  simp only [hc, mul_assoc, ← Complex.ofReal_mul]
  rw [Finset.sum_comm]
  have hz (j : Q) := sum_signed_support s ((1-2*r.p)*contrast E.decay r.q j) E.finalFrame j
  simp only [← Complex.ofReal_mul] at hz
  simp only [hz, Finset.sum_const_zero]

theorem ideal_all_effect_optimum (E : Experiment) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IsLeast {x : ℝ | ∃ F : History 3 2 → MatJ, (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (idealFamily E true s false) (idealFamily E true s true) F=x}
      ((1-s)/2) := by
  simpa only [ideal_distance E hs] using
    readoutError_isLeast (ideal_valid E true hs hs1 false) (ideal_valid E true hs hs1 true)
theorem noisy_all_effect_optimum (E : Experiment) (r : NoiseRates) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IsLeast {x : ℝ | ∃ F : History 3 2 → MatJ, (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (noisyFamily E true r s false) (noisyFamily E true r s true) F=x}
      ((1-s * |1-2*r.p| * ∑ j, |contrast E.decay r.q j|)/2) := by
  simpa only [noisy_distance E r hs] using
    readoutError_isLeast (noisy_valid E true r hs hs1 false) (noisy_valid E true r hs hs1 true)

theorem ideal_history_optimum (E : Experiment) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IsLeast {x : ℝ | ∃ f : History 3 2 → ℝ, (∀ h, f h∈Set.Icc (0:ℝ) 1) ∧
      historyError (idealFamily E true s false) (idealFamily E true s true) f=x}
      ((1-s)/2) := by
  simpa only [ideal_variation_distance, ideal_distance E hs] using
    historyError_isLeast (ideal_valid E true hs hs1 false) (ideal_valid E true hs hs1 true)
theorem noisy_history_optimum (E : Experiment) (r : NoiseRates) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IsLeast {x : ℝ | ∃ f : History 3 2 → ℝ, (∀ h, f h∈Set.Icc (0:ℝ) 1) ∧
      historyError (noisyFamily E true r s false) (noisyFamily E true r s true) f=x}
      ((1-s * |1-2*r.p| * ∑ j, |contrast E.decay r.q j|)/2) := by
  simpa only [noisy_variation_distance, noisy_distance E r hs] using
    historyError_isLeast (noisy_valid E true r hs hs1 false) (noisy_valid E true r hs hs1 true)

theorem ideal_nonfeedback_difference (E : Experiment) (s : ℝ) :
    (∑ h, idealFamily E false s false h)-(∑ h, idealFamily E false s true h) =
      ((s*E.decay:ℝ):ℂ) •
        (joint (readProjection E.finalFrame 0)-joint (readProjection E.finalFrame 1)) := by
  simp only [ideal_matrix]
  change (∑ h : Q × Q × Unit, (idealCoefficient false s E.decay false h.1 h.2.1:ℂ) •
    joint (readProjection E.finalFrame h.2.1)) -
    (∑ h : Q × Q × Unit, (idealCoefficient false s E.decay true h.1 h.2.1:ℂ) •
    joint (readProjection E.finalFrame h.2.1))=_
  simp only [Fintype.sum_prod_type, Fintype.sum_unique,
    Fin.sum_univ_succ]
  norm_num [idealCoefficient, rootWeight, probability, row, equilibriumWeight,
    Matrix.cons_val_two, Fin.ext_iff]
  module

theorem noisy_nonfeedback_difference (E : Experiment) (r : NoiseRates) (s : ℝ) :
    (∑ h, noisyFamily E false r s false h)-(∑ h, noisyFamily E false r s true h) =
      ((s*(1-2*r.p)*E.decay:ℝ):ℂ) •
        (joint (readProjection E.finalFrame 0)-joint (readProjection E.finalFrame 1)) := by
  simp only [noisy_matrix]
  change (∑ h : Q × Q × Unit, (noisyCoefficient false s E.decay r.p r.q false h.1 h.2.1:ℂ) •
    joint (readProjection E.finalFrame h.2.1)) -
    (∑ h : Q × Q × Unit, (noisyCoefficient false s E.decay r.p r.q true h.1 h.2.1:ℂ) •
    joint (readProjection E.finalFrame h.2.1))=_
  simp only [Fintype.sum_prod_type, Fintype.sum_unique,
    Fin.sum_univ_succ]
  norm_num [noisyCoefficient, noisyWeight, rootWeight, probability, row, equilibriumWeight,
    exchange, Matrix.cons_val_two, Fin.ext_iff]
  module

theorem frame_distance (φ : ℝ) : traceDist (readProjection φ 0) (readProjection φ 1)=1 := by
  have hU : GibbsHamiltonianRelaxation.unitary measurementE φ ∈ Matrix.unitaryGroup Q ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    change _*(GibbsHamiltonianRelaxation.unitary measurementE φ)ᴴ=1
    rw [GibbsHamiltonianRelaxation.unitary_adjoint, GibbsHamiltonianRelaxation.unitary_cancel]
  simp only [readProjection, C, GibbsHamiltonianRelaxation.rotation_sandwich]
  change traceDist (conjugate (GibbsHamiltonianRelaxation.unitary measurementE φ) (baseProjection 0))
    (conjugate (GibbsHamiltonianRelaxation.unitary measurementE φ) (baseProjection 1))=1
  rw [conjugate_distance hU (base_density 0).1.isHermitian (base_density 1).1.isHermitian]
  exact projector_distance

theorem frame_difference_norm (φ : ℝ) :
    traceNorm (joint (readProjection φ 0)-joint (readProjection φ 1))=2 := by
  have hd : traceDist (joint (readProjection φ 0)) (joint (readProjection φ 1))=1 := by
    rw [GibbsHistoryPreparationBounds.joint_traceDist, frame_distance]
  unfold traceDist at hd
  linarith

theorem ideal_nonfeedback_distance (E : Experiment) {s : ℝ} (hs : 0 ≤ s) :
    traceDist (∑ h, idealFamily E false s false h) (∑ h, idealFamily E false s true h)=s*E.decay := by
  unfold traceDist
  rw [ideal_nonfeedback_difference, traceNorm_smul_nonneg (mul_nonneg hs (decay_mem E).1.le),
    frame_difference_norm]
  ring
theorem noisy_nonfeedback_distance (E : Experiment) (r : NoiseRates) {s : ℝ} (hs : 0 ≤ s) :
    traceDist (∑ h, noisyFamily E false r s false h) (∑ h, noisyFamily E false r s true h)=
      s * |1-2*r.p| * E.decay := by
  unfold traceDist
  rw [noisy_nonfeedback_difference, traceNorm_eq_physlib, Matrix.traceNorm_smul,
    ← traceNorm_eq_physlib, frame_difference_norm, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_pos (decay_mem E).1]
  ring

theorem feedback_event_change (E : Experiment) (s : ℝ) (hyp : Bool) :
    (idealFamily E true s hyp (1,0,())).trace.re-
      (idealFamily E false s hyp (1,0,())).trace.re=rootWeight s hyp 1*E.decay := by
  simp only [ideal_matrix, scalar_projection_trace]
  norm_num [idealCoefficient, feedbackIndex, row, equilibriumWeight, Fin.ext_iff]
  ring
theorem feedback_event_strict (E : Experiment) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (hyp : Bool) :
    0<(idealFamily E true s hyp (1,0,())).trace.re-
      (idealFamily E false s hyp (1,0,())).trace.re := by
  rw [feedback_event_change]
  exact mul_pos (rootWeight_pos hs hs1 hyp 1) (decay_mem E).1


theorem compiled_stability (B : Background) {n : ℕ} (PA PB : Policy n)
    (rsA rsB : List NoiseRates) (lenA : rsA.length=n) (lenB : rsB.length=n)
    {X_A X_B Y_A Y_B : MatJ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B)
    (F : History 3 n → MatJ) (hF : ∀ h, IsBinaryPOVM (F h))
    (a : History 3 n → ℝ) (ha : ∀ h, a h∈Set.Icc (0:ℝ) 1) :
    let βA := survival rsA * traceDist X_A Y_A + 1 - survival rsA
    let βB := survival rsB * traceDist X_B Y_B + 1 - survival rsB
    (|(1-outputDistance Q Unit 3 (ideal B PA) (ideal B PB) X_A X_B)/2 -
       (1-outputDistance Q Unit 3 (noisy B PA rsA lenA) (noisy B PB rsB lenB) Y_A Y_B)/2| ≤ (βA+βB)/2) ∧
    (|readoutError (fun h => run Q Unit 3 (ideal B PA) h X_A) (fun h => run Q Unit 3 (ideal B PB) h X_B) F - readoutError (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B) F| ≤ (βA+βB)/2) ∧
    (|instrumentError (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B)
      (optimalReadout (run_family (ideal B PA) hXA) (run_family (ideal B PB) hXB)) -
      (1-outputDistance Q Unit 3 (ideal B PA) (ideal B PB) X_A X_B)/2| ≤ (βA+βB)/2) ∧
    (|historyError (fun h => run Q Unit 3 (ideal B PA) h X_A) (fun h => run Q Unit 3 (ideal B PB) h X_B) a - historyError (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B) a| ≤ (βA+βB)/2) :=
  tree_paired_mixture_stability _ _ _ _ hXA hXB hYA hYB
    (compiler_mixture B PA rsA lenA) (compiler_mixture B PB rsB lenB) F hF a ha

theorem compiled_additive_stability (B : Background) {n : ℕ} (PA PB : Policy n)
    (rsA rsB : List NoiseRates) (lenA : rsA.length=n) (lenB : rsB.length=n)
    {X_A X_B Y_A Y_B : MatJ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B)
    (F : History 3 n → MatJ) (hF : ∀ h, IsBinaryPOVM (F h))
    (a : History 3 n → ℝ) (ha : ∀ h, a h∈Set.Icc (0:ℝ) 1) :
    let βA := min 1 (traceDist X_A Y_A + (rsA.map (fun r => r.p+r.q)).sum)
    let βB := min 1 (traceDist X_B Y_B + (rsB.map (fun r => r.p+r.q)).sum)
    (|(1-outputDistance Q Unit 3 (ideal B PA) (ideal B PB) X_A X_B)/2 -
       (1-outputDistance Q Unit 3 (noisy B PA rsA lenA) (noisy B PB rsB lenB) Y_A Y_B)/2| ≤ (βA+βB)/2) ∧
    (|readoutError (fun h => run Q Unit 3 (ideal B PA) h X_A) (fun h => run Q Unit 3 (ideal B PB) h X_B) F - readoutError (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B) F| ≤ (βA+βB)/2) ∧
    (|instrumentError (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B)
      (optimalReadout (run_family (ideal B PA) hXA) (run_family (ideal B PB) hXB)) -
      (1-outputDistance Q Unit 3 (ideal B PA) (ideal B PB) X_A X_B)/2| ≤ (βA+βB)/2) ∧
    (|historyError (fun h => run Q Unit 3 (ideal B PA) h X_A) (fun h => run Q Unit 3 (ideal B PB) h X_B) a - historyError (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B) a| ≤ (βA+βB)/2) :=
  tree_budget_stability _ _ _ _ hXA hXB hYA hYB _ _
    (compiled_additive B PA rsA lenA hXA hYA) (compiled_additive B PB rsB lenB hXB hYB) F hF a ha

theorem compiled_attained_optima (B : Background) {n : ℕ} (PA PB : Policy n)
    (rsA rsB : List NoiseRates) (lenA : rsA.length=n) (lenB : rsB.length=n)
    {X_A X_B Y_A Y_B : MatJ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B) :
    IsLeast {x : ℝ | ∃ F : History 3 n → MatJ,
      (∀ h, IsBinaryPOVM (F h)) ∧ readoutError (fun h => run Q Unit 3 (ideal B PA) h X_A) (fun h => run Q Unit 3 (ideal B PB) h X_B) F = x}
      ((1 - outputDistance Q Unit 3 (ideal B PA) (ideal B PB) X_A X_B)/2) ∧
    IsLeast {x : ℝ | ∃ F : History 3 n → MatJ,
      (∀ h, IsBinaryPOVM (F h)) ∧ readoutError (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B) F = x}
      ((1 - outputDistance Q Unit 3 (noisy B PA rsA lenA) (noisy B PB rsB lenB) Y_A Y_B)/2) ∧
    instrumentError (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B)
      (optimalReadout (run_family (noisy B PA rsA lenA) hYA) (run_family (noisy B PB rsB lenB) hYB)) =
      (1 - outputDistance Q Unit 3 (noisy B PA rsA lenA) (noisy B PB rsB lenB) Y_A Y_B)/2 :=
  tree_attained_optima _ _ _ _ hXA hXB hYA hYB

theorem compiled_six_tables (B : Background) {n : ℕ} (PA PB : Policy n)
    (rsA rsB : List NoiseRates) (lenA : rsA.length=n) (lenB : rsB.length=n)
    {X_A X_B Y_A Y_B : MatJ}
    (hXA : IsDensityOperator X_A) (hXB : IsDensityOperator X_B)
    (hYA : IsDensityOperator Y_A) (hYB : IsDensityOperator Y_B) :
    let I := optimalReadout (run_family (ideal B PA) hXA) (run_family (ideal B PB) hXB)
    let J := optimalReadout (run_family (noisy B PA rsA lenA) hYA) (run_family (noisy B PB rsB lenB) hYB)
    ((∀ h a, 0 ≤ readoutTable I (fun h => run Q Unit 3 (ideal B PA) h X_A) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run Q Unit 3 (ideal B PA) h X_A) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable I (fun h => run Q Unit 3 (ideal B PB) h X_B) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run Q Unit 3 (ideal B PB) h X_B) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable I (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable I (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable J (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) h a) ∧ (∑ h, ∑ a, readoutTable J (fun h => run Q Unit 3 (noisy B PA rsA lenA) h Y_A) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable J (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B) h a) ∧ (∑ h, ∑ a, readoutTable J (fun h => run Q Unit 3 (noisy B PB rsB lenB) h Y_B) h a) = 1) :=
  tree_physical_probabilities _ _ _ _ hXA hXB hYA hYB

/-- Arbitrary finite binary Kraus readouts induce admissible effects at every history. -/
theorem arbitrary_readout_effect {H : Type*} [Fintype H] (A B : H → MatJ)
    (I : H → FiniteInstrument J 2) :
    instrumentError A B I=readoutError A B (fun h => inducedEffect (I h) 0) := by
  simp only [instrumentError, readoutTable, inducedEffect_weight, readoutError,
    inducedEffect_complement]

theorem physical_family_optimum {H : Type*} [Fintype H] {A B : H → MatJ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    IsLeast {x : ℝ | ∃ I : H → FiniteInstrument J 2, instrumentError A B I=x}
      ((1-branchDistance A B)/2) := by
  refine ⟨⟨optimalReadout hA hB, optimalReadout_error hA hB⟩, ?_⟩
  rintro x ⟨I,rfl⟩
  rw [arbitrary_readout_effect]
  exact readoutError_lower hA hB (fun h => inducedEffect_admissible (I h))

def choiceProjection {H : Type*} (f : H → Bool) (h : H) : MatJ := if f h then 1 else 0
theorem choice_hermitian {H : Type*} (f : H → Bool) (h : H) :
    (choiceProjection f h).IsHermitian := by unfold choiceProjection; split <;> simp
theorem choice_square {H : Type*} (f : H → Bool) (h : H) :
    choiceProjection f h*choiceProjection f h=choiceProjection f h := by
  unfold choiceProjection; split <;> simp
def choiceReadout {H : Type*} (f : H → Bool) (h : H) : FiniteInstrument J 2 :=
  projectiveReadout (choiceProjection f h) (choice_hermitian f h) (choice_square f h)
def choiceWeight {H : Type*} (f : H → Bool) (h : H) (a : Fin 2) : ℝ :=
  if a=0 then (if f h then 1 else 0) else (if f h then 0 else 1)

theorem choice_weight {H : Type*} (f : H → Bool) (h : H) (a : Fin 2) (X : MatJ) :
    (choiceReadout f h).weight a X=choiceWeight f h a*X.trace.re := by
  have ha : a=0 ∨ a=1 := by fin_cases a <;> decide
  rcases ha with rfl | rfl
  all_goals simp only [choiceReadout, projectiveReadout_weight_zero, projectiveReadout_weight_one]
  all_goals unfold choiceProjection choiceWeight; split_ifs <;> simp_all

def nominalChoice (h : History 3 2) : Bool := decide (h.1=0)
def quarterChoice (h : History 3 2) : Bool :=
  decide ((h.1=0 ∧ h.2.1≠1) ∨ (h.1=1 ∧ h.2.1=1))
def quarterRates : NoiseRates := ⟨1/4,1/4,by norm_num,by norm_num,by norm_num,by norm_num⟩

theorem ideal_decision_cells (E : Experiment) (feedback : Bool) (s : ℝ) (hyp : Bool)
    (f : History 3 2 → Bool) (h : History 3 2) (a : Fin 2) :
    readoutTable (choiceReadout f) (idealFamily E feedback s hyp) h a =
      choiceWeight f h a*idealCoefficient feedback s E.decay hyp h.1 h.2.1 := by
  rw [readoutTable, choice_weight, ideal_matrix, scalar_projection_trace]
theorem noisy_decision_cells (E : Experiment) (feedback : Bool) (r : NoiseRates) (s : ℝ)
    (hyp : Bool) (f : History 3 2 → Bool) (h : History 3 2) (a : Fin 2) :
    readoutTable (choiceReadout f) (noisyFamily E feedback r s hyp) h a =
      choiceWeight f h a*noisyCoefficient feedback s E.decay r.p r.q hyp h.1 h.2.1 := by
  rw [readoutTable, choice_weight, noisy_matrix, scalar_projection_trace]

theorem choice_tables_normalized {H : Type*} [Fintype H] (f : H → Bool)
    {A : H → MatJ} (hA : IsBranchFamily A) :
    (∀ h a, 0≤readoutTable (choiceReadout f) A h a) ∧
      (∑ h, ∑ a, readoutTable (choiceReadout f) A h a)=1 :=
  ⟨readoutTable_nonneg _ hA, readoutTable_total _ hA⟩

theorem nominal_error (E : Experiment) (s : ℝ) :
    instrumentError (idealFamily E true s false) (idealFamily E true s true)
      (choiceReadout nominalChoice)=(1-s)/2 := by
  unfold instrumentError
  simp only [ideal_decision_cells]
  change ((∑ h : Q × Q × Unit, choiceWeight nominalChoice h 0*
    idealCoefficient true s E.decay true h.1 h.2.1)+
    (∑ h : Q × Q × Unit, choiceWeight nominalChoice h 1*
    idealCoefficient true s E.decay false h.1 h.2.1))/2=_
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_succ]
  norm_num [choiceWeight, nominalChoice, idealCoefficient, rootWeight, probability,
    row, equilibriumWeight, feedbackIndex, Matrix.cons_val_two, Fin.ext_iff]
  ring

theorem quarter_contrast : contrast (1/2) (1/4)=![23/48,-1/48,2/48] := by
  ext j
  fin_cases j <;> norm_num [contrast, row, equilibriumWeight, Fin.ext_iff]
theorem quarter_distance (E : Experiment) (hE : E.decay=1/2) {s : ℝ} (hs : 0 ≤ s) :
    branchDistance (noisyFamily E true quarterRates s false)
      (noisyFamily E true quarterRates s true)=13*s/48 := by
  rw [noisy_distance E quarterRates hs, hE]
  norm_num [quarterRates, quarter_contrast, Fin.sum_univ_succ, Matrix.cons_val_two]
  ring

theorem quarter_transported_error (E : Experiment) (hE : E.decay=1/2) (s : ℝ) :
    instrumentError (noisyFamily E true quarterRates s false)
      (noisyFamily E true quarterRates s true) (choiceReadout nominalChoice)=(1-s/4)/2 := by
  unfold instrumentError
  simp only [noisy_decision_cells, hE]
  change ((∑ h : Q × Q × Unit, choiceWeight nominalChoice h 0*
    noisyCoefficient true s (1/2) (1/4) (1/4) true h.1 h.2.1)+
    (∑ h : Q × Q × Unit, choiceWeight nominalChoice h 1*
    noisyCoefficient true s (1/2) (1/4) (1/4) false h.1 h.2.1))/2=_
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_succ]
  norm_num [choiceWeight, nominalChoice, noisyCoefficient, noisyWeight, rootWeight, probability,
    row, equilibriumWeight, exchange, Matrix.cons_val_two, Fin.ext_iff]
  ring

theorem quarter_sign_error (E : Experiment) (hE : E.decay=1/2) (s : ℝ) :
    instrumentError (noisyFamily E true quarterRates s false)
      (noisyFamily E true quarterRates s true) (choiceReadout quarterChoice)=(1-13*s/48)/2 := by
  unfold instrumentError
  simp only [noisy_decision_cells, hE]
  change ((∑ h : Q × Q × Unit, choiceWeight quarterChoice h 0*
    noisyCoefficient true s (1/2) (1/4) (1/4) true h.1 h.2.1)+
    (∑ h : Q × Q × Unit, choiceWeight quarterChoice h 1*
    noisyCoefficient true s (1/2) (1/4) (1/4) false h.1 h.2.1))/2=_
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_succ]
  norm_num [choiceWeight, quarterChoice, noisyCoefficient, noisyWeight, rootWeight, probability,
    row, equilibriumWeight, exchange, Matrix.cons_val_two, Fin.ext_iff]
  ring

theorem quarter_physical_optimum (E : Experiment) (hE : E.decay=1/2) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IsLeast {x : ℝ | ∃ I : History 3 2 → FiniteInstrument J 2,
      instrumentError (noisyFamily E true quarterRates s false)
        (noisyFamily E true quarterRates s true) I=x} ((1-13*s/48)/2) := by
  simpa only [quarter_distance E hE hs] using
    physical_family_optimum (noisy_valid E true quarterRates hs hs1 false)
      (noisy_valid E true quarterRates hs hs1 true)

theorem quarter_strict_history_gain (E : Experiment) (hE : E.decay=1/2) {s : ℝ} (hs : 0<s) :
    instrumentError (noisyFamily E true quarterRates s false) (noisyFamily E true quarterRates s true)
      (choiceReadout nominalChoice)-
    instrumentError (noisyFamily E true quarterRates s false) (noisyFamily E true quarterRates s true)
      (choiceReadout quarterChoice)=s/96 ∧ 0<s/96 := by
  rw [quarter_transported_error E hE, quarter_sign_error E hE]
  constructor
  · ring
  · positivity

def rootMarginal (A : History 3 2 → MatJ) (a : Q) : ℝ := ∑ j, (A (a,j,())).trace.re
def rootVariation (A B : History 3 2 → MatJ) : ℝ :=
  (∑ a, |rootMarginal A a-rootMarginal B a|)/2

theorem ideal_root_marginal (E : Experiment) (feedback : Bool) (s : ℝ) (hyp : Bool) (a : Q) :
    rootMarginal (idealFamily E feedback s hyp) a=rootWeight s hyp a := by
  unfold rootMarginal
  simp only [ideal_matrix, scalar_projection_trace, idealCoefficient]
  rw [← Finset.mul_sum, row_sum, mul_one]

theorem noisy_root_marginal (E : Experiment) (feedback : Bool) (r : NoiseRates)
    (s : ℝ) (hyp : Bool) (a : Q) :
    rootMarginal (noisyFamily E feedback r s hyp) a =
      (1-r.q)*noisyWeight s r.p hyp a+r.q*noisyWeight s r.p hyp (exchange a) := by
  unfold rootMarginal
  simp only [noisy_matrix, scalar_projection_trace, noisyCoefficient]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change (1-r.q)*noisyWeight s r.p hyp a*
      (∑ j : Q, row E.decay (if feedback && decide (a=1) then exchange a else a) j)+
    r.q*noisyWeight s r.p hyp (exchange a)*
      (∑ j : Q, row E.decay (if feedback && decide (a=1) then exchange (exchange a) else exchange a) j)=_
  rw [row_sum, row_sum]
  ring

theorem noisy_root_difference (E : Experiment) (feedback : Bool) (r : NoiseRates)
    (s : ℝ) (a : Q) :
    rootMarginal (noisyFamily E feedback r s false) a-
      rootMarginal (noisyFamily E feedback r s true) a =
      signWeight s a*((1-2*r.p)*(1-2*r.q)) := by
  rw [noisy_root_marginal, noisy_root_marginal]
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl <;>
    norm_num [noisyWeight, rootWeight, probability, exchange, signWeight, Fin.ext_iff] <;> ring

theorem noisy_root_variation (E : Experiment) (feedback : Bool) (r : NoiseRates)
    {s : ℝ} (hs : 0 ≤ s) :
    rootVariation (noisyFamily E feedback r s false) (noisyFamily E feedback r s true) =
      s * |(1-2*r.p)*(1-2*r.q)| := by
  unfold rootVariation
  simp only [noisy_root_difference, abs_mul, ← Finset.sum_mul]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((|signWeight s 0|+(|signWeight s 1|+|signWeight s 2|))*
    (|1-2*r.p| * |1-2*r.q|))/2=_
  norm_num [signWeight, Fin.ext_iff, abs_of_nonneg hs]
  ring

theorem half_readout_contrast (η : ℝ) : contrast η (1/2)=![η/2,-η/2,0] := by
  ext j
  fin_cases j <;> norm_num [contrast, row, equilibriumWeight, Fin.ext_iff] <;> ring
theorem half_readout_distances (E : Experiment) (r : NoiseRates) (hq : r.q=1/2)
    {s : ℝ} (hs : 0 ≤ s) :
    rootVariation (noisyFamily E true r s false) (noisyFamily E true r s true)=0 ∧
    branchDistance (noisyFamily E true r s false) (noisyFamily E true r s true)=
      s * |1-2*r.p| * E.decay := by
  constructor
  · rw [noisy_root_variation E true r hs, hq]
    norm_num
  · rw [noisy_distance E r hs, hq, half_readout_contrast]
    norm_num [Fin.sum_univ_succ, Matrix.cons_val_two, abs_div, abs_of_pos (decay_mem E).1]

theorem half_evolution_erases (E : Experiment) (r : NoiseRates) (hp : r.p=1/2)
    (s : ℝ) (h : History 3 2) :
    noisyFamily E true r s false h=noisyFamily E true r s true h := by
  rcases h with ⟨a,j,⟨⟩⟩
  apply sub_eq_zero.mp
  rw [noisy_signed_matrix, hp]
  norm_num

theorem compiled_physical_inputs (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (hlen : rs.length=n) (γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    outputDistance Q Unit 3 (ideal B P) (noisy B P rs hlen)
      (joint (evolved B.b B.hbar γ t r false)) (joint (evolved B.b B.hbar γ t r true)) ≤
      survival rs*FiniteThreeLevelThermalPhase.retention r γ t+1-survival rs := by
  have hd := compiled_distance B P rs hlen
    (joint_density (evolved_density B.b B.hbar γ t hγ ht hr hr1 false))
    (joint_density (evolved_density B.b B.hbar γ t hγ ht hr hr1 true))
  have he : traceDist (joint (evolved B.b B.hbar γ t r false))
      (joint (evolved B.b B.hbar γ t r true))=FiniteThreeLevelThermalPhase.retention r γ t :=
    evolved_joint_distance B.b B.hbar γ t hγ ht hr
  simpa only [he] using hd

def witnessBackground : Background := ⟨1,1,by norm_num,by norm_num⟩
def witnessExperiment : Experiment :=
  ⟨witnessBackground,1,Real.log 2,theta 1 1 (Real.log 2),by norm_num,
    (Real.log_pos (by norm_num)).le⟩

theorem witness_decay : witnessExperiment.decay=1/2 := by
  norm_num [Experiment.decay, witnessExperiment, Real.exp_neg, Real.exp_log]
theorem witness_actual_input (hyp : Bool) :
    joint (evolved 1 1 1 (Real.log 2) (1/2) hyp)=
      joint (alignedInput (1/4) witnessExperiment.frame hyp) := by
  rw [evolved_formula _ _ _ _ _ (by norm_num) (Real.log_pos (by norm_num)).le]
  congr 1
  norm_num [alignedInput, witnessExperiment, FiniteThreeLevelThermalPhase.retention,
    Real.exp_neg, Real.exp_log]
theorem witness_positive_times : 0<Real.log 2 ∧ 0<witnessExperiment.duration :=
  ⟨Real.log_pos (by norm_num),Real.log_pos (by norm_num)⟩

theorem witness_values :
    branchDistance (idealFamily witnessExperiment true (1/4) false)
      (idealFamily witnessExperiment true (1/4) true)=1/4 ∧
    branchDistance (noisyFamily witnessExperiment true quarterRates (1/4) false)
      (noisyFamily witnessExperiment true quarterRates (1/4) true)=13/192 ∧
    rootVariation (noisyFamily witnessExperiment true quarterRates (1/4) false)
      (noisyFamily witnessExperiment true quarterRates (1/4) true)=1/16 ∧
    instrumentError (idealFamily witnessExperiment true (1/4) false)
      (idealFamily witnessExperiment true (1/4) true) (choiceReadout nominalChoice)=3/8 ∧
    instrumentError (noisyFamily witnessExperiment true quarterRates (1/4) false)
      (noisyFamily witnessExperiment true quarterRates (1/4) true) (choiceReadout quarterChoice)=179/384 ∧
    instrumentError (noisyFamily witnessExperiment true quarterRates (1/4) false)
      (noisyFamily witnessExperiment true quarterRates (1/4) true) (choiceReadout nominalChoice)=15/32 := by
  rw [ideal_distance _ (by norm_num), quarter_distance _ witness_decay (by norm_num),
    noisy_root_variation _ _ _ (by norm_num), nominal_error,
    quarter_sign_error _ witness_decay, quarter_transported_error _ witness_decay]
  norm_num [quarterRates]


def witnessIdealMass (hyp : Bool) : Q → Q → ℝ :=
  if hyp then ![![85/384,25/384,5/192],![51/128,15/128,3/64],![5/192,5/192,7/96]]
  else ![![51/128,15/128,3/64],![85/384,25/384,5/192],![5/192,5/192,7/96]]

def witnessNoisyMass (hyp : Bool) : Q → Q → ℝ :=
  if hyp then ![![173/768,113/768,13/384],![73/256,37/256,5/128],![5/192,5/192,7/96]]
  else ![![73/256,37/256,5/128],![173/768,113/768,13/384],![5/192,5/192,7/96]]

theorem witness_ideal_matrices (hyp : Bool) (a j : Q) :
    idealFamily witnessExperiment true (1/4) hyp (a,j,()) =
      (witnessIdealMass hyp a j:ℂ) • joint (readProjection witnessExperiment.finalFrame j) := by
  rw [ideal_matrix, witness_decay]
  congr 1
  cases hyp <;> fin_cases a <;> fin_cases j <;>
    norm_num [witnessIdealMass, idealCoefficient, feedbackIndex, rootWeight, probability, row,
      equilibriumWeight, quarterRates, Matrix.cons_val_two, Fin.ext_iff]

theorem witness_noisy_matrices (hyp : Bool) (a j : Q) :
    noisyFamily witnessExperiment true quarterRates (1/4) hyp (a,j,()) =
      (witnessNoisyMass hyp a j:ℂ) • joint (readProjection witnessExperiment.finalFrame j) := by
  rw [noisy_matrix, witness_decay]
  congr 1
  cases hyp <;> fin_cases a <;> fin_cases j <;>
    norm_num [witnessNoisyMass, noisyCoefficient, noisyWeight, exchange, rootWeight, probability, row,
      equilibriumWeight, quarterRates, Matrix.cons_val_two, Fin.ext_iff]

def witnessNominalIdeal (hyp : Bool) : Q → Q → Fin 2 → ℝ :=
  if hyp then ![![![85/384,0],![25/384,0],![5/192,0]],![![0,51/128],![0,15/128],![0,3/64]],![![0,5/192],![0,5/192],![0,7/96]]]
  else ![![![51/128,0],![15/128,0],![3/64,0]],![![0,85/384],![0,25/384],![0,5/192]],![![0,5/192],![0,5/192],![0,7/96]]]

def witnessNominalNoisy (hyp : Bool) : Q → Q → Fin 2 → ℝ :=
  if hyp then ![![![173/768,0],![113/768,0],![13/384,0]],![![0,73/256],![0,37/256],![0,5/128]],![![0,5/192],![0,5/192],![0,7/96]]]
  else ![![![73/256,0],![37/256,0],![5/128,0]],![![0,173/768],![0,113/768],![0,13/384]],![![0,5/192],![0,5/192],![0,7/96]]]

def witnessSignNoisy (hyp : Bool) : Q → Q → Fin 2 → ℝ :=
  if hyp then ![![![173/768,0],![0,113/768],![13/384,0]],![![0,73/256],![37/256,0],![0,5/128]],![![0,5/192],![0,5/192],![0,7/96]]]
  else ![![![73/256,0],![0,37/256],![5/128,0]],![![0,173/768],![113/768,0],![0,13/384]],![![0,5/192],![0,5/192],![0,7/96]]]

theorem witness_nominal_ideal_tables (hyp : Bool) (a j : Q) (d : Fin 2) :
    readoutTable (choiceReadout nominalChoice) (idealFamily witnessExperiment true (1/4) hyp) (a,j,()) d =
      witnessNominalIdeal hyp a j d := by
  rw [readoutTable, choice_weight, witness_ideal_matrices, scalar_projection_trace]
  cases hyp <;> fin_cases a <;> fin_cases j <;> fin_cases d <;>
    norm_num [witnessNominalIdeal, witnessIdealMass, choiceWeight, nominalChoice, Matrix.cons_val_two, Fin.ext_iff]

theorem witness_nominal_noisy_tables (hyp : Bool) (a j : Q) (d : Fin 2) :
    readoutTable (choiceReadout nominalChoice) (noisyFamily witnessExperiment true quarterRates (1/4) hyp) (a,j,()) d =
      witnessNominalNoisy hyp a j d := by
  rw [readoutTable, choice_weight, witness_noisy_matrices, scalar_projection_trace]
  cases hyp <;> fin_cases a <;> fin_cases j <;> fin_cases d <;>
    norm_num [witnessNominalNoisy, witnessNoisyMass, choiceWeight, nominalChoice, Matrix.cons_val_two, Fin.ext_iff]

theorem witness_sign_noisy_tables (hyp : Bool) (a j : Q) (d : Fin 2) :
    readoutTable (choiceReadout quarterChoice) (noisyFamily witnessExperiment true quarterRates (1/4) hyp) (a,j,()) d =
      witnessSignNoisy hyp a j d := by
  rw [readoutTable, choice_weight, witness_noisy_matrices, scalar_projection_trace]
  cases hyp <;> fin_cases a <;> fin_cases j <;> fin_cases d <;>
    norm_num [witnessSignNoisy, witnessNoisyMass, choiceWeight, quarterChoice, Matrix.cons_val_two, Fin.ext_iff]

/-! Reachability and the physical fixture, without conditioning on branch mass. -/
theorem decay_lt_one (E : Experiment) (h : 0 < E.rate*E.duration) : E.decay < 1 := by
  apply Real.exp_lt_one_iff.mpr
  nlinarith

theorem ideal_cells_positive (E : Experiment) (feedback : Bool) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) (ht : 0 < E.rate*E.duration) (hyp : Bool) (a j : Q) :
    0 < (idealFamily E feedback s hyp (a,j,())).trace.re := by
  rw [ideal_matrix, scalar_projection_trace]
  exact mul_pos (rootWeight_pos hs hs1 hyp a)
    (row_pos (decay_mem E).1.le (decay_lt_one E ht) _ j)

theorem noisy_cells_positive (E : Experiment) (feedback : Bool) (r : NoiseRates) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) (ht : 0 < E.rate*E.duration) (hyp : Bool) (a j : Q) :
    0 < (noisyFamily E feedback r s hyp (a,j,())).trace.re := by
  rw [noisy_matrix, scalar_projection_trace]
  have h0 := noisyWeight_pos hs hs1 r.hp r.hp1 hyp a
  have h1 := noisyWeight_pos hs hs1 r.hp r.hp1 hyp (exchange a)
  have hx := row_pos (decay_mem E).1.le (decay_lt_one E ht)
    (if feedback && decide (a=1) then exchange a else a) j
  have hy := row_pos (decay_mem E).1.le (decay_lt_one E ht)
    (if feedback && decide (a=1) then exchange (exchange a) else exchange a) j
  unfold noisyCoefficient
  have hn := mul_nonneg (mul_nonneg (sub_nonneg.mpr r.hq1) h0.le) hx.le
  by_cases hz : r.q=0
  · simp only [hz, sub_zero, one_mul, zero_mul, add_zero]
    exact mul_pos h0 hx
  · have hp := mul_pos (mul_pos (lt_of_le_of_ne r.hq (Ne.symm hz)) h1) hy
    linarith

theorem witness_cells_positive (hyp : Bool) (a j : Q) :
    0 < witnessIdealMass hyp a j ∧ 0 < witnessNoisyMass hyp a j := by
  cases hyp <;> fin_cases a <;> fin_cases j <;>
    norm_num [witnessIdealMass, witnessNoisyMass, Matrix.cons_val_two]

theorem witness_tables_normalized (hyp : Bool) :
    ((∀ a j d, 0 ≤ witnessNominalIdeal hyp a j d) ∧
      (∑ a, ∑ j, ∑ d, witnessNominalIdeal hyp a j d)=1) ∧
    ((∀ a j d, 0 ≤ witnessNominalNoisy hyp a j d) ∧
      (∑ a, ∑ j, ∑ d, witnessNominalNoisy hyp a j d)=1) ∧
    ((∀ a j d, 0 ≤ witnessSignNoisy hyp a j d) ∧
      (∑ a, ∑ j, ∑ d, witnessSignNoisy hyp a j d)=1) := by
  cases hyp <;> constructor
  all_goals first
    | constructor
      · intro a j d
        fin_cases a <;> fin_cases j <;> fin_cases d <;>
          norm_num [witnessNominalIdeal, Matrix.cons_val_two]
      · norm_num [witnessNominalIdeal, Fin.sum_univ_succ]
    | constructor <;> constructor
      all_goals first
        | intro a j d
          fin_cases a <;> fin_cases j <;> fin_cases d <;>
            norm_num [witnessNominalNoisy, witnessSignNoisy, Matrix.cons_val_two]
        | norm_num [witnessNominalNoisy, witnessSignNoisy, Fin.sum_univ_succ]

theorem nominal_physical_optimum (E : Experiment) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IsLeast {x : ℝ | ∃ I : History 3 2 → FiniteInstrument J 2,
      instrumentError (idealFamily E true s false) (idealFamily E true s true) I=x}
      ((1-s)/2) := by
  simpa only [ideal_distance E hs] using
    physical_family_optimum (ideal_valid E true hs hs1 false) (ideal_valid E true hs hs1 true)

theorem quarter_budgets : survival [quarterRates,zeroRates]=9/16 ∧
    1-survival [quarterRates,zeroRates]=7/16 ∧
    (([quarterRates,zeroRates].map (fun r => r.p+r.q)).sum)=1/2 ∧
    (7/16:ℝ)<1/2 := by
  norm_num [survival, FiniteAdaptiveMixtureSurvival.retention, quarterRates, zeroRates]

/-- The actual physical policy invokes the generic certificate with identical inputs. -/
theorem quarter_compiler_stability (E : Experiment) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |(1-branchDistance (idealFamily E true s false) (idealFamily E true s true))/2-
      (1-branchDistance (noisyFamily E true quarterRates s false)
        (noisyFamily E true quarterRates s true))/2| ≤ 7/16 ∧
    |instrumentError (idealFamily E true s false) (idealFamily E true s true)
        (choiceReadout nominalChoice)-
      instrumentError (noisyFamily E true quarterRates s false)
        (noisyFamily E true quarterRates s true) (choiceReadout nominalChoice)| ≤ 7/16 := by
  have hA : IsDensityOperator (joint (alignedInput s E.frame false)) :=
    joint_density (mixture_density hs hs1 (projection_density _ _))
  have hB : IsDensityOperator (joint (alignedInput s E.frame true)) :=
    joint_density (mixture_density hs hs1 (projection_density _ _))
  have h := compiled_stability E.background (experimentPolicy E true) (experimentPolicy E true)
    [quarterRates,zeroRates] [quarterRates,zeroRates] rfl rfl hA hB hA hB
    (fun h => inducedEffect (choiceReadout nominalChoice h) 0)
    (fun h => inducedEffect_admissible (choiceReadout nominalChoice h))
    (fun _ => 0) (fun _ => by norm_num)
  simp only [traceDist_self, mul_zero, zero_add, quarter_budgets.1] at h
  norm_num only [show ((1-(9:ℝ)/16)+(1-9/16))/2=7/16 by norm_num] at h
  constructor
  · simpa only [idealFamily, noisyFamily, branchDistance, outputDistance, traceDist,
      div_eq_mul_inv, Finset.mul_sum, mul_comm, one_mul] using h.1
  · rw [arbitrary_readout_effect, arbitrary_readout_effect]
    exact h.2.1

theorem quarter_exact_perturbations (E : Experiment) (hE : E.decay=1/2) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |instrumentError (noisyFamily E true quarterRates s false)
        (noisyFamily E true quarterRates s true) (choiceReadout quarterChoice)-
      instrumentError (idealFamily E true s false) (idealFamily E true s true)
        (choiceReadout nominalChoice)|=35*s/96 ∧
    |instrumentError (noisyFamily E true quarterRates s false)
        (noisyFamily E true quarterRates s true) (choiceReadout nominalChoice)-
      instrumentError (idealFamily E true s false) (idealFamily E true s true)
        (choiceReadout nominalChoice)|=3*s/8 ∧
    35*s/96 ≤ 7/16 ∧ 3*s/8 ≤ 7/16 := by
  have h := quarter_compiler_stability E hs hs1
  rw [ideal_distance E hs, quarter_distance E hE hs] at h
  rw [nominal_error, quarter_transported_error E hE] at h
  rw [nominal_error, quarter_sign_error E hE, quarter_transported_error E hE]
  have h0 : (1-13*s/48)/2-(1-s)/2=35*s/96 := by ring
  have h1 : (1-s/4)/2-(1-s)/2=3*s/8 := by ring
  rw [h0, h1, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  rw [abs_sub_comm, h0, abs_of_nonneg (by positivity)] at h
  rw [abs_sub_comm ((1-s)/2), h1, abs_of_nonneg (by positivity)] at h
  exact ⟨rfl,rfl,h.1,h.2⟩

def rootEvolution (B : Background) (p : ℝ) :=
  mixKraus (controlledKraus B.b B.hbar 0 0 false)
    (controlledKraus B.b B.hbar 0 0 true) p

theorem root_evolution_action (B : Background) (r : NoiseRates) (s φ : ℝ) (hyp : Bool) :
    krausMap (rootEvolution B r.p) (joint (alignedInput s φ hyp)) =
      joint (((1-r.p:ℝ):ℂ) • alignedInput s φ hyp+
        (r.p:ℂ) • alignedInput s φ (!hyp)) := by
  rw [rootEvolution, mixKraus_action _ _ r.hp r.hp1]
  simp only [controlled_action, unjoint_joint, channel_zero_time _ _ _ le_rfl,
    control_aligned, Bool.false_eq_true, if_false, if_true]
  ext ⟨i,u⟩ ⟨j,v⟩
  cases u; cases v
  simp [joint, Matrix.kroneckerMap_apply]

theorem evolution_noise_changes_action (B : Background) (r : NoiseRates)
    {s : ℝ} (hs : 0 < s) (hp : 0 < r.p) (φ : ℝ) :
    krausMap (rootEvolution B r.p) (joint (alignedInput s φ false)) ≠
      joint (alignedInput s φ false) := by
  rw [root_evolution_action]
  intro he
  have h := congrArg (fun X : MatJ => ((readout φ).branch 0 (unjoint X)).trace.re) he
  rw [unjoint_joint, unjoint_joint, FiniteInstrument.branch_add,
    FiniteInstrument.branch_smul, FiniteInstrument.branch_smul,
    aligned_readout, aligned_readout] at h
  simp only [Matrix.trace_add, Matrix.trace_smul, (projection_density φ 0).2,
    smul_eq_mul, mul_one, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Bool.not_false] at h
  norm_num [rootWeight, probability, Fin.ext_iff] at h
  nlinarith [mul_pos hs hp]

theorem instrument_noise_action (φ : ℝ) (r : NoiseRates) :
    (mixInstrument (readout φ) (readout (φ+Real.pi)) r.q r.hq r.hq1).branch 0
      (readProjection φ 0)=((1-r.q:ℝ):ℂ) • readProjection φ 0 := by
  rw [mixInstrument_branch, readout_pi, readout_projection, readout_projection]
  norm_num [exchange, Fin.ext_iff]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

theorem instrument_noise_changes_action (φ : ℝ) (r : NoiseRates) (hq : 0 < r.q) :
    (mixInstrument (readout φ) (readout (φ+Real.pi)) r.q r.hq r.hq1).branch 0
      (readProjection φ 0) ≠ (readout φ).branch 0 (readProjection φ 0) := by
  rw [instrument_noise_action, readout_projection]
  norm_num only [ite_true, one_smul]
  intro he
  have h := congrArg (fun X : MatQ => X.trace.re) he
  simp only [Matrix.trace_smul, (projection_density φ 0).2, smul_eq_mul, mul_one,
    Complex.ofReal_re, Complex.one_re] at h
  linarith

theorem compiled_zero_depth (B : Background) (X Y : MatJ)
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    survival []=1 ∧
    outputDistance Q Unit 3 (ideal B .done) (noisy B .done [] rfl) X Y=traceDist X Y ∧
    terminalState Q Unit 3 (ideal B .done) X=X ∧
    historyVariation Q Unit 3 (ideal B .done) (noisy B .done [] rfl) X Y=0 := by
  refine ⟨rfl,outputDistance_done Q Unit 3 X Y,?_,?_⟩
  · simp [terminalState,ideal,run,history_card]
  · simp [historyVariation,ideal,noisy,weight,run,hX.2,hY.2]

theorem compiled_zero_noise_distance (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (hlen : rs.length=n)
    (hz : ∀ r∈rs, r.p=0 ∧ r.q=0) (X : MatJ) :
    outputDistance Q Unit 3 (ideal B P) (noisy B P rs hlen) X X=0 := by
  simp [outputDistance,compiled_zero_noise B P rs hlen hz,traceNorm_zero]

theorem psd_zero_trace_input {X : MatJ} (hX : X.PosSemidef) (ht : X.trace=0) : X=0 :=
  hX.trace_eq_zero_iff.mp ht

theorem compiled_zero_trace_branches (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (hlen : rs.length=n) {X : MatJ}
    (hX : X.PosSemidef) (ht : X.trace=0) (h : History 3 n) :
    run Q Unit 3 (ideal B P) h X=0 ∧ run Q Unit 3 (noisy B P rs hlen) h X=0 := by
  rw [psd_zero_trace_input hX ht]
  simp only [run_zero, and_self]

theorem same_policy_equilibrium (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (hlen : rs.length=n) (φ : ℝ) (h : History 3 n) :
    run Q Unit 3 (ideal B P) h (joint (alignedInput 0 φ false))=
      run Q Unit 3 (ideal B P) h (joint (alignedInput 0 φ true)) ∧
    run Q Unit 3 (noisy B P rs hlen) h (joint (alignedInput 0 φ false))=
      run Q Unit 3 (noisy B P rs hlen) h (joint (alignedInput 0 φ true)) := by
  simp [alignedInput, mixture]

theorem pure_initial_projection (φ : ℝ) (hyp : Bool) :
    alignedInput 1 φ hyp=readProjection φ (if hyp then 1 else 0) ∧
      rootWeight 1 hyp 2=0 := by
  cases hyp <;> simp [alignedInput,mixture,rootWeight,probability,Fin.ext_iff]

/-- Positive dose restores faithfulness even when the initial mixing parameter is one. -/
theorem pure_initial_evolved_faithful (B : Background) (γ t : ℝ)
    (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hdose : 0 < γ*t) (hyp : Bool) :
    (evolved B.b B.hbar γ t 1 hyp).PosDef ∧
    0 < rootWeight (Real.exp (-γ*t)) hyp 2 := by
  have hs : 0 ≤ Real.exp (-γ*t) := (Real.exp_pos _).le
  have hs1 : Real.exp (-γ*t)<1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  constructor
  · rw [evolved_formula _ _ _ _ _ hγ ht]
    simp only [FiniteThreeLevelThermalPhase.retention, one_mul]
    exact mixture_faithful hs hs1 (projection_density _ _).1
  · exact rootWeight_pos hs hs1 hyp 2

theorem pure_initial_evolved_endpoint (γ t : ℝ) :
    Real.exp (-γ*t)=1 ↔ γ*t=0 := by
  rw [Real.exp_eq_one_iff]
  constructor <;> intro h <;> nlinarith

theorem decay_finite (E : Experiment) : E.decay≠0 ∧
    (E.decay=1 ↔ E.rate*E.duration=0) :=
  ⟨ne_of_gt (decay_mem E).1,pure_initial_evolved_endpoint E.rate E.duration⟩

theorem explicit_pulse_at_zero_wait (B : Background) (s φ : ℝ) (hyp : Bool) :
    krausMap (controlledKraus B.b B.hbar 0 0 true) (joint (alignedInput s φ hyp))=
      joint (alignedInput s φ (!hyp)) := by
  rw [controlled_action,unjoint_joint,channel_zero_time _ _ _ le_rfl,control_aligned]
  rfl

theorem compiled_history_optima (B : Background) {n : ℕ} (PA PB : Policy n)
    (rsA rsB : List NoiseRates) (lenA : rsA.length=n) (lenB : rsB.length=n)
    {XA XB YA YB : MatJ} (hXA : IsDensityOperator XA) (hXB : IsDensityOperator XB)
    (hYA : IsDensityOperator YA) (hYB : IsDensityOperator YB) :
    IsLeast {x : ℝ | ∃ f : History 3 n → ℝ, (∀ h, f h∈Set.Icc (0:ℝ) 1) ∧
      historyError (fun h => run Q Unit 3 (ideal B PA) h XA)
        (fun h => run Q Unit 3 (ideal B PB) h XB) f=x}
      ((1-historyVariation Q Unit 3 (ideal B PA) (ideal B PB) XA XB)/2) ∧
    IsLeast {x : ℝ | ∃ f : History 3 n → ℝ, (∀ h, f h∈Set.Icc (0:ℝ) 1) ∧
      historyError (fun h => run Q Unit 3 (noisy B PA rsA lenA) h YA)
        (fun h => run Q Unit 3 (noisy B PB rsB lenB) h YB) f=x}
      ((1-historyVariation Q Unit 3 (noisy B PA rsA lenA) (noisy B PB rsB lenB) YA YB)/2) :=
  ⟨tree_history_isLeast _ _ hXA hXB,tree_history_isLeast _ _ hYA hYB⟩

theorem compiled_hermitian_contraction (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (hlen : rs.length=n) {X Y : MatJ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    outputDistance Q Unit 3 (ideal B P) (ideal B P) X Y ≤ traceDist X Y ∧
    outputDistance Q Unit 3 (noisy B P rs hlen) (noisy B P rs hlen) X Y ≤ traceDist X Y :=
  ⟨outputDistance_common Q Unit 3 _ hX hY,outputDistance_common Q Unit 3 _ hX hY⟩

theorem compiled_budget_domains (rs : List NoiseRates) {X Y : MatJ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    survival rs∈Set.Icc (0:ℝ) 1 ∧
    1-survival rs ≤ (rs.map (fun r => r.p+r.q)).sum ∧
    survival rs*traceDist X Y+1-survival rs ≤ 1 :=
  ⟨survival_mem rs,survival_additive rs,survival_bound_cap Q Unit rs hX hY⟩

theorem evolved_aligned (B : Background) (γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hyp : Bool) : evolved B.b B.hbar γ t r hyp=
      alignedInput (FiniteThreeLevelThermalPhase.retention r γ t) (theta B.b B.hbar t) hyp :=
  evolved_formula _ _ _ _ _ hγ ht _

theorem experiment_physical_inputs (E : Experiment) (γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hframe : E.frame=theta E.background.b E.background.hbar t) (hyp : Bool) (h : History 3 2)
    (noise : NoiseRates) :
    run Q Unit 3 (ideal E.background (experimentPolicy E true)) h
        (joint (evolved E.background.b E.background.hbar γ t r hyp))=
      idealFamily E true (FiniteThreeLevelThermalPhase.retention r γ t) hyp h ∧
    run Q Unit 3 (noisy E.background (experimentPolicy E true) [noise,zeroRates] rfl) h
        (joint (evolved E.background.b E.background.hbar γ t r hyp))=
      noisyFamily E true noise (FiniteThreeLevelThermalPhase.retention r γ t) hyp h := by
  rw [evolved_aligned _ _ _ _ hγ ht,←hframe]
  exact ⟨rfl,rfl⟩

theorem equal_terminal_error {A B : History 3 2 → MatJ} (hA : IsBranchFamily A)
    (he : (∑ h,A h)=(∑ h,B h)) (F : MatJ) :
    povmAvgError (∑ h,A h) (∑ h,B h) F=1/2 := by
  rw [←he]
  unfold povmAvgError
  simp only [Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,Complex.sub_re]
  have ht : (∑ h,A h).trace.re=1 := by
    simpa only [Matrix.trace_sum,Complex.re_sum] using hA.2
  rw [ht]
  ring

theorem feedback_terminal_every_effect (E : Experiment) (r : NoiseRates) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (F : MatJ) (_hF : IsBinaryPOVM F) :
    povmAvgError (∑ h,idealFamily E true s false h) (∑ h,idealFamily E true s true h) F=1/2 ∧
    povmAvgError (∑ h,noisyFamily E true r s false h) (∑ h,noisyFamily E true r s true h) F=1/2 :=
  ⟨equal_terminal_error (ideal_valid E true hs hs1 false) (ideal_terminal_equal E s) F,
    equal_terminal_error (noisy_valid E true r hs hs1 false) (noisy_terminal_equal E r s) F⟩

theorem full_evolution_reversal (E : Experiment) (r : NoiseRates) (hp : r.p=1) (hq : r.q=0)
    (s : ℝ) (hyp : Bool) : noisyFamily E true r s hyp=idealFamily E true s (!hyp) := by
  funext h
  rcases h with ⟨a,j,⟨⟩⟩
  rw [noisy_matrix,ideal_matrix,hp,hq]
  congr 1
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl <;>
    norm_num [noisyCoefficient,idealCoefficient,noisyWeight,exchange,feedbackIndex,Fin.ext_iff]

theorem full_instrument_relabels (φ : ℝ) (r : NoiseRates) (hq : r.q=1) (a : Q) (X : MatQ) :
    (mixInstrument (readout φ) (readout (φ+Real.pi)) r.q r.hq r.hq1).branch a X=
      (readout φ).branch (exchange a) X := by
  rw [mixInstrument_branch,hq,readout_pi]
  simp

theorem half_readout_retains_history (E : Experiment) (r : NoiseRates) (hq : r.q=1/2)
    {s : ℝ} (hs : 0 < s) (hc : 1-2*r.p≠0) :
    rootVariation (noisyFamily E true r s false) (noisyFamily E true r s true)=0 ∧
    0 < branchDistance (noisyFamily E true r s false) (noisyFamily E true r s true) := by
  have h := half_readout_distances E r hq hs.le
  refine ⟨h.1,?_⟩
  rw [h.2]
  exact mul_pos (mul_pos hs (abs_pos.mpr hc)) (decay_mem E).1

theorem full_rate_compiler_bound (B : Background) {n : ℕ} (P : Policy n)
    (rs : List NoiseRates) (hlen : rs.length=n) (r : NoiseRates) (hr : r∈rs)
    (hfull : r.p=1 ∨ r.q=1) {X Y : MatJ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    survival rs=0 ∧ outputDistance Q Unit 3 (ideal B P) (noisy B P rs hlen) X Y ≤ 1 := by
  have hz := survival_full_rate rs r hr hfull
  exact ⟨hz,by simpa only [hz,zero_mul,zero_add,sub_zero] using compiled_distance B P rs hlen hX hY⟩

theorem impossible_histories_retained (E : Experiment) (r : NoiseRates) (hyp : Bool) (j : Q) :
    idealFamily E true 1 hyp (2,j,())=0 ∧
    noisyFamily E true r 1 hyp (2,j,())=0 := by
  rw [ideal_matrix,noisy_matrix]
  cases hyp <;> norm_num [idealCoefficient,noisyCoefficient,noisyWeight,rootWeight,
    probability,exchange,Fin.ext_iff]

theorem noise_populates_zero_cell (E : Experiment) (ht : 0 < E.rate*E.duration) :
    idealFamily E true 1 false (1,0,())=0 ∧
    0 < (noisyFamily E true quarterRates 1 false (1,0,())).trace.re := by
  rw [ideal_matrix,noisy_matrix,scalar_projection_trace]
  have h0 := row_pos (decay_mem E).1.le (decay_lt_one E ht) 0 0
  have h1 := row_pos (decay_mem E).1.le (decay_lt_one E ht) 1 0
  norm_num [idealCoefficient,noisyCoefficient,noisyWeight,rootWeight,probability,
    exchange,feedbackIndex,quarterRates,Fin.ext_iff]
  positivity

/-- Classical root marginal, retaining its unnormalized aggregate matrices. -/
def rootFamily (A : History 3 2 → MatJ) (a : Q) : MatJ := ∑ j,A (a,j,())

theorem root_family_valid {A : History 3 2 → MatJ} (hA : IsBranchFamily A) :
    IsBranchFamily (rootFamily A) := by
  constructor
  · intro a
    exact Matrix.posSemidef_sum _ (fun j _ => hA.1 (a,j,()))
  · have ht := hA.2
    change (∑ h : Q × Q × Unit,(A h).trace.re)=1 at ht
    simp only [Fintype.sum_prod_type,Fintype.sum_unique] at ht
    simp only [rootFamily,Matrix.trace_sum,Complex.re_sum]
    convert ht using 1
    rfl

theorem root_family_variation (A B : History 3 2 → MatJ) :
    familyHistoryVariation (rootFamily A) (rootFamily B)=rootVariation A B := by
  simp only [familyHistoryVariation,rootFamily,rootVariation,rootMarginal,
    Matrix.trace_sum,Complex.re_sum]

theorem root_family_history_error (A B : History 3 2 → MatJ) (f : Q → ℝ) :
    historyError (rootFamily A) (rootFamily B) f=
      historyError A B (fun h => f h.1) := by
  unfold historyError rootFamily
  simp only [Matrix.trace_sum,Complex.re_sum,Finset.mul_sum]
  change _ = ((∑ h : Q × Q × Unit,f h.1*(B h).trace.re)+
    (∑ h : Q × Q × Unit,(1-f h.1)*(A h).trace.re))/2
  simp only [Fintype.sum_prod_type,Fintype.sum_unique]
  rfl

theorem first_label_optimum (E : Experiment) (r : NoiseRates) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IsLeast {x : ℝ | ∃ f : Q → ℝ, (∀ a, f a∈Set.Icc (0:ℝ) 1) ∧
      historyError (noisyFamily E true r s false) (noisyFamily E true r s true)
        (fun h => f h.1)=x} ((1-s * |(1-2*r.p)*(1-2*r.q)|)/2) := by
  simpa only [root_family_variation,root_family_history_error,noisy_root_variation E true r hs] using
    historyError_isLeast (root_family_valid (noisy_valid E true r hs hs1 false))
      (root_family_valid (noisy_valid E true r hs hs1 true))

theorem quarter_compiler_additive (E : Experiment) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |(1-branchDistance (idealFamily E true s false) (idealFamily E true s true))/2-
      (1-branchDistance (noisyFamily E true quarterRates s false)
        (noisyFamily E true quarterRates s true))/2| ≤ 1/2 ∧
    |instrumentError (idealFamily E true s false) (idealFamily E true s true)
        (choiceReadout nominalChoice)-
      instrumentError (noisyFamily E true quarterRates s false)
        (noisyFamily E true quarterRates s true) (choiceReadout nominalChoice)| ≤ 1/2 := by
  have hA : IsDensityOperator (joint (alignedInput s E.frame false)) :=
    joint_density (mixture_density hs hs1 (projection_density _ _))
  have hB : IsDensityOperator (joint (alignedInput s E.frame true)) :=
    joint_density (mixture_density hs hs1 (projection_density _ _))
  have h := compiled_additive_stability E.background (experimentPolicy E true) (experimentPolicy E true)
    [quarterRates,zeroRates] [quarterRates,zeroRates] rfl rfl hA hB hA hB
    (fun h => inducedEffect (choiceReadout nominalChoice h) 0)
    (fun h => inducedEffect_admissible (choiceReadout nominalChoice h))
    (fun _ => 0) (fun _ => by norm_num)
  norm_num only [traceDist_self,zero_add,quarter_budgets.2.2.1,
    show min (1:ℝ) (1/2)=1/2 by norm_num,show ((1:ℝ)/2+1/2)/2=1/2 by norm_num] at h
  constructor
  · simpa only [idealFamily,noisyFamily,branchDistance,outputDistance,traceDist,
      div_eq_mul_inv,Finset.mul_sum,mul_comm,one_mul] using h.1
  · rw [arbitrary_readout_effect,arbitrary_readout_effect]
    exact h.2.1

theorem witness_terminal_and_comparator :
    traceDist (∑ h,idealFamily witnessExperiment true (1/4) false h)
      (∑ h,idealFamily witnessExperiment true (1/4) true h)=0 ∧
    traceDist (∑ h,noisyFamily witnessExperiment true quarterRates (1/4) false h)
      (∑ h,noisyFamily witnessExperiment true quarterRates (1/4) true h)=0 ∧
    traceDist (∑ h,idealFamily witnessExperiment false (1/4) false h)
      (∑ h,idealFamily witnessExperiment false (1/4) true h)=1/8 ∧
    traceDist (∑ h,noisyFamily witnessExperiment false quarterRates (1/4) false h)
      (∑ h,noisyFamily witnessExperiment false quarterRates (1/4) true h)=1/16 := by
  rw [ideal_terminal_equal,noisy_terminal_equal,traceDist_self,traceDist_self,
    ideal_nonfeedback_distance _ (by norm_num),noisy_nonfeedback_distance _ _ (by norm_num),witness_decay]
  norm_num [quarterRates]

theorem witness_error_changes :
    instrumentError (noisyFamily witnessExperiment true quarterRates (1/4) false)
        (noisyFamily witnessExperiment true quarterRates (1/4) true) (choiceReadout nominalChoice)-
      instrumentError (noisyFamily witnessExperiment true quarterRates (1/4) false)
        (noisyFamily witnessExperiment true quarterRates (1/4) true) (choiceReadout quarterChoice)=1/384 ∧
    |instrumentError (noisyFamily witnessExperiment true quarterRates (1/4) false)
        (noisyFamily witnessExperiment true quarterRates (1/4) true) (choiceReadout quarterChoice)-
      instrumentError (idealFamily witnessExperiment true (1/4) false)
        (idealFamily witnessExperiment true (1/4) true) (choiceReadout nominalChoice)|=35/384 ∧
    |instrumentError (noisyFamily witnessExperiment true quarterRates (1/4) false)
        (noisyFamily witnessExperiment true quarterRates (1/4) true) (choiceReadout nominalChoice)-
      instrumentError (idealFamily witnessExperiment true (1/4) false)
        (idealFamily witnessExperiment true (1/4) true) (choiceReadout nominalChoice)|=3/32 := by
  rw [quarter_transported_error _ witness_decay,quarter_sign_error _ witness_decay,nominal_error]
  norm_num

theorem witness_physical_H : thermalH witnessBackground.b≠0 ∧
    ∀ z : ℂ,thermalH witnessBackground.b≠z • (1:MatQ) :=
  ⟨thermalH_ne_zero witnessBackground.b_pos,thermalH_not_scalar witnessBackground.b_pos⟩

theorem full_noise_distinguishes (E : Experiment) (r : NoiseRates) (hp : r.p=1) (hq : r.q=0)
    {s : ℝ} (hs : 0 < s) :
    survival [r,zeroRates]=0 ∧
    branchDistance (noisyFamily E true r s false) (noisyFamily E true r s true)=s := by
  constructor
  · exact survival_full_rate _ r (by simp) (Or.inl hp)
  · rw [full_evolution_reversal E r hp hq,full_evolution_reversal E r hp hq]
    simpa only [Bool.not_false,Bool.not_true,branchDistance_comm] using ideal_distance E hs.le

theorem psd_real_trace_zero {X : MatJ} (hX : X.PosSemidef) (ht : X.trace.re=0) : X=0 := by
  apply hX.trace_eq_zero_iff.mp
  have hc : star X.trace=X.trace := by
    rw [←Matrix.trace_conjTranspose,hX.isHermitian.eq]
  apply Complex.ext
  · exact ht
  · exact Complex.conj_eq_iff_im.mp hc

theorem pure_initial_rank_one (φ : ℝ) (hyp : Bool) :
    alignedInput 1 φ hyp=Matrix.vecMulVec (readVector φ (if hyp then 1 else 0))
      (star (readVector φ (if hyp then 1 else 0))) := by
  rw [(pure_initial_projection φ hyp).1,projection_rank_one]

theorem aligned_third (s φ : ℝ) (hyp : Bool) :
    alignedInput s φ hyp 2 2=((1-s)/6:ℝ) := by
  cases hyp <;>
    norm_num [alignedInput,mixture,equilibrium,three,density,projection_zero_entries,
      projection_one_entries,Matrix.cons_val_two,GibbsReset.threeWeights] <;> ring

theorem pure_initial_not_faithful (φ : ℝ) (hyp : Bool) :
    ¬(alignedInput 1 φ hyp).PosDef := by
  intro h
  have hp := h.diag_pos (i:=2)
  rw [aligned_third] at hp
  norm_num at hp

theorem evolved_pure_third_and_endpoint (B : Background) (γ t : ℝ)
    (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hyp : Bool) :
    evolved B.b B.hbar γ t 1 hyp 2 2=((1-Real.exp (-γ*t))/6:ℝ) ∧
    (evolved B.b B.hbar γ t 1 hyp 2 2=0 ↔ γ*t=0) ∧
    (¬(evolved B.b B.hbar γ t 1 hyp).PosDef ↔ γ*t=0) := by
  have he := evolved_aligned B γ t 1 hγ ht hyp
  simp only [FiniteThreeLevelThermalPhase.retention,one_mul] at he
  have hz : (((1-Real.exp (-γ*t))/6:ℝ):ℂ)=0 ↔ γ*t=0 := by
    rw [Complex.ofReal_eq_zero]
    constructor
    · intro h
      apply (pure_initial_evolved_endpoint γ t).mp
      linarith
    · intro h
      rw [(pure_initial_evolved_endpoint γ t).mpr h]
      norm_num
  refine ⟨by rw [he,aligned_third],by rw [he,aligned_third]; exact hz,?_⟩
  constructor
  · intro hn
    by_contra hz
    exact hn (pure_initial_evolved_faithful B γ t hγ ht
      (lt_of_le_of_ne (mul_nonneg hγ ht) (Ne.symm hz)) hyp).1
  · intro hd
    rw [he,(pure_initial_evolved_endpoint γ t).mpr hd]
    exact pure_initial_not_faithful _ hyp

theorem zero_attenuation_controls (E : Experiment) (h : E.rate=0 ∨ E.duration=0) : E.decay=1 :=
  (decay_finite E).2.mpr (by rcases h with h|h <;> simp [h])

/-- Both coherences involving the third level stay in the actual full channel. -/
theorem full_channel_third_gaps (B : Background) (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    krausMap (channelKraus B.b B.hbar γ t) (Matrix.single 0 2 1)=
      (Real.exp (-γ*t):ℂ) • (Complex.exp (Complex.I*t*(Real.log 3/B.b/B.hbar:ℝ)) •
        (Matrix.single 0 2 1:MatQ)) ∧
    krausMap (channelKraus B.b B.hbar γ t) (Matrix.single 1 2 1)=
      (Real.exp (-γ*t):ℂ) •
        (Complex.exp (-Complex.I*t*((delta/B.b/B.hbar:ℝ)-(Real.log 3/B.b/B.hbar:ℝ))) •
          (Matrix.single 1 2 1:MatQ)) := by
  have h02 : (Matrix.single 0 2 1:MatQ).trace=0 := by
    norm_num [Matrix.trace,Fin.sum_univ_succ,Matrix.single_apply,Fin.ext_iff]
  have h12 : (Matrix.single 1 2 1:MatQ).trace=0 := by
    norm_num [Matrix.trace,Fin.sum_univ_succ,Matrix.single_apply,Fin.ext_iff]
  constructor <;>
    rw [channel_action _ _ _ _ hγ ht,reset_action _ _ hγ ht]
  · rw [h02,zero_smul,smul_zero,add_zero,phase_smul,phase_E02]
  · rw [h12,zero_smul,smul_zero,add_zero,phase_smul,phase_E12]

theorem zero_rate_preserves_physical_phase (B : Background) (t : ℝ) (ht : 0 ≤ t) (X : MatQ) :
    krausMap (channelKraus B.b B.hbar 0 t) X=phase B.b B.hbar t X :=
  channel_zero_rate _ _ _ ht X

theorem compiled_physical_optima (B : Background) {n : ℕ} (PA PB : Policy n)
    (rsA rsB : List NoiseRates) (lenA : rsA.length=n) (lenB : rsB.length=n)
    {XA XB YA YB : MatJ} (hXA : IsDensityOperator XA) (hXB : IsDensityOperator XB)
    (hYA : IsDensityOperator YA) (hYB : IsDensityOperator YB) :
    IsLeast {x : ℝ | ∃ I : History 3 n → FiniteInstrument J 2,
      instrumentError (fun h => run Q Unit 3 (ideal B PA) h XA)
        (fun h => run Q Unit 3 (ideal B PB) h XB) I=x}
      ((1-outputDistance Q Unit 3 (ideal B PA) (ideal B PB) XA XB)/2) ∧
    IsLeast {x : ℝ | ∃ I : History 3 n → FiniteInstrument J 2,
      instrumentError (fun h => run Q Unit 3 (noisy B PA rsA lenA) h YA)
        (fun h => run Q Unit 3 (noisy B PB rsB lenB) h YB) I=x}
      ((1-outputDistance Q Unit 3 (noisy B PA rsA lenA) (noisy B PB rsB lenB) YA YB)/2) := by
  constructor
  · simpa only [tree_branchDistance] using
      physical_family_optimum (run_family _ hXA) (run_family _ hXB)
  · simpa only [tree_branchDistance] using
      physical_family_optimum (run_family _ hYA) (run_family _ hYB)

theorem witness_prepared_distance :
    traceDist (joint (evolved 1 1 1 (Real.log 2) (1/2) false))
      (joint (evolved 1 1 1 (Real.log 2) (1/2) true))=1/4 := by
  have he : traceDist (joint (evolved 1 1 1 (Real.log 2) (1/2) false))
      (joint (evolved 1 1 1 (Real.log 2) (1/2) true))=
      FiniteThreeLevelThermalPhase.retention (1/2) 1 (Real.log 2) :=
    evolved_joint_distance 1 1 1 (Real.log 2) (by norm_num)
      (Real.log_pos (by norm_num)).le (by norm_num)
  rw [he]
  norm_num [FiniteThreeLevelThermalPhase.retention,Real.exp_neg,Real.exp_log]

theorem quarter_signed_matrices (E : Experiment) (hE : E.decay=1/2) (s : ℝ) (a j : Q) :
    noisyFamily E true quarterRates s false (a,j,())-
      noisyFamily E true quarterRates s true (a,j,())=
      ((signWeight s a/2 * (![23/48,-1/48,2/48] j):ℝ):ℂ) •
        joint (readProjection E.finalFrame j) := by
  rw [noisy_signed_matrix,hE]
  simp only [quarterRates]
  rw [quarter_contrast]
  norm_num
  congr 1
  push_cast
  ring

theorem choice_history_error {H : Type*} [Fintype H] (A B : H → MatJ) (f : H → Bool) :
    instrumentError A B (choiceReadout f)=historyError A B (fun h => if f h then 1 else 0) := by
  simp only [instrumentError,readoutTable,choice_weight,historyError,choiceWeight]
  congr 2
  apply Finset.sum_congr rfl
  intro h _
  cases f h <;> simp

/-- Strict positivity chooses hypothesis zero; exact ties choose one. -/
def strictChoice {H : Type*} (A B : H → MatJ) (h : H) : Bool :=
  decide (0 < (A h).trace.re-(B h).trace.re)

theorem strict_choice_attains {H : Type*} [Fintype H] {A B : H → MatJ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    instrumentError A B (choiceReadout (strictChoice A B))=(1-familyHistoryVariation A B)/2 := by
  rw [choice_history_error,historyError_eq hA,←signClassifier_score hA hB]
  congr 2
  apply Finset.sum_congr rfl
  intro h _
  unfold strictChoice signClassifier
  by_cases hp : 0 < (A h).trace.re-(B h).trace.re
  · simp [hp,le_of_lt hp]
  · by_cases hz : (A h).trace.re-(B h).trace.re=0
    · simp [hz]
    · have hn : ¬0 ≤ (A h).trace.re-(B h).trace.re := by intro hge; exact hz (le_antisymm (le_of_not_gt hp) hge)
      simp [hp,hn]

def signalChoice (s η p q : ℝ) (h : History 3 2) : Bool :=
  decide (0 < signWeight s h.1*(1-2*p)*contrast η q h.2.1)

theorem signal_choice_is_strict (E : Experiment) (r : NoiseRates) (s : ℝ) :
    signalChoice s E.decay r.p r.q=
      strictChoice (noisyFamily E true r s false) (noisyFamily E true r s true) := by
  funext h
  unfold signalChoice strictChoice
  rw [noisy_matrix,noisy_matrix,scalar_projection_trace,scalar_projection_trace,noisy_signed]

theorem signal_choice_optimal (E : Experiment) (r : NoiseRates) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    instrumentError (noisyFamily E true r s false) (noisyFamily E true r s true)
      (choiceReadout (signalChoice s E.decay r.p r.q))=
      (1-s * |1-2*r.p| * ∑ j,|contrast E.decay r.q j|)/2 := by
  rw [signal_choice_is_strict,strict_choice_attains (noisy_valid E true r hs hs1 false)
    (noisy_valid E true r hs hs1 true),noisy_variation_distance,noisy_distance E r hs]

theorem signal_decision_cells (E : Experiment) (r : NoiseRates) (s : ℝ) (hyp : Bool)
    (a j : Q) (d : Fin 2) :
    readoutTable (choiceReadout (signalChoice s E.decay r.p r.q)) (noisyFamily E true r s hyp)
      (a,j,()) d =
      (if d=0 then
        (if 0 < signWeight s a*(1-2*r.p)*contrast E.decay r.q j then 1 else 0)
      else (if 0 < signWeight s a*(1-2*r.p)*contrast E.decay r.q j then 0 else 1)) *
        noisyCoefficient true s E.decay r.p r.q hyp a j := by
  rw [noisy_decision_cells]
  simp only [choiceWeight,signalChoice,decide_eq_true_eq]

/-- Six independent normalized tables, including every zero cell and every tie. -/
theorem concrete_six_tables (E : Experiment) (r : NoiseRates) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ hyp : Bool,
    ((∀ h d,0 ≤ readoutTable (choiceReadout nominalChoice) (idealFamily E true s hyp) h d) ∧
      (∑ h,∑ d,readoutTable (choiceReadout nominalChoice) (idealFamily E true s hyp) h d)=1) ∧
    ((∀ h d,0 ≤ readoutTable (choiceReadout nominalChoice) (noisyFamily E true r s hyp) h d) ∧
      (∑ h,∑ d,readoutTable (choiceReadout nominalChoice) (noisyFamily E true r s hyp) h d)=1) ∧
    ((∀ h d,0 ≤ readoutTable (choiceReadout (signalChoice s E.decay r.p r.q))
        (noisyFamily E true r s hyp) h d) ∧
      (∑ h,∑ d,readoutTable (choiceReadout (signalChoice s E.decay r.p r.q))
        (noisyFamily E true r s hyp) h d)=1) := by
  intro hyp
  exact ⟨choice_tables_normalized _ (ideal_valid E true hs hs1 hyp),
    choice_tables_normalized _ (noisy_valid E true r hs hs1 hyp),
    choice_tables_normalized _ (noisy_valid E true r hs hs1 hyp)⟩

theorem quarter_signal_choice {s : ℝ} (hs : 0 < s) :
    signalChoice s (1/2) (1/4) (1/4)=quarterChoice := by
  funext ⟨a,j,u⟩
  cases u
  fin_cases a <;> fin_cases j <;>
    norm_num [signalChoice,quarterChoice,signWeight,quarter_contrast,Matrix.cons_val_two,Fin.ext_iff] <;>
    positivity

theorem witness_feedback_events :
    (idealFamily witnessExperiment true (1/4) false (1,0,())).trace.re-
      (idealFamily witnessExperiment false (1/4) false (1,0,())).trace.re=5/32 ∧
    (idealFamily witnessExperiment true (1/4) true (1,0,())).trace.re-
      (idealFamily witnessExperiment false (1/4) true (1,0,())).trace.re=9/32 := by
  rw [feedback_event_change,feedback_event_change,witness_decay]
  norm_num [rootWeight,probability,Fin.ext_iff]

/-! The environment in every theorem is exactly `Unit`. These are finite ordinary
trace-norm and classical-history statements, with no extra-ancilla/diamond or
weighted-history metric claim. The inherited positive quotients, carriers and
failure examples are unchanged. In particular `GibbsHistoryPreparationBounds`
warm-up obstructions and `NontracialPhaseHistoryTransfer` quarter/half-kernel
obstructions are not repaired by the positive ordinary branch remainders here.
`FiniteGibbsClock.modular_eq_heisenberg` retains its faithful-state domain and
signed time `-β*ℏ*s`; none of these policies infer a unique physical clock.
No environment-memory, calibration, continuum, spectral-gap, quantum advantage,
publication or whole-project acceptance follows from this finite construction. -/

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelAdaptiveReadout
