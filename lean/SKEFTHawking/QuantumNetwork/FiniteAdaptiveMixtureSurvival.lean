import SKEFTHawking.QuantumNetwork.FiniteAdaptiveMapPerturbation
import SKEFTHawking.QuantumNetwork.CoherentMemoryProcess

/-! Actual independent evolution/instrument mixtures with retained finite memory.
The four-term branch identity includes both cross terms. Positivity is proved for
ordinary branch-matrix remainders; no reflected-kernel positivity or physical-time
identification is asserted. Actual paired trees preserve a positive component of
weight equal to the depthwise survival product. The resulting changed-input bound
retains complete histories and the joint quantum memory; all rates are dimensionless.
No extra-ancilla norm, postselection, or unrestricted coherent-channel dominance is claimed. -/
namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveMixtureSurvival
open Matrix FiniteInterventionProcess FiniteAdaptiveMapPerturbation FiniteMemoryProcess
open scoped BigOperators ComplexOrder Kronecker

variable (S E : Type*) [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E] (o : ℕ)

noncomputable def mixedStep {k l : ℕ}
    (K : Fin k → Matrix (S × E) (S × E) ℂ) (L : Fin l → Matrix (S × E) (S × E) ℂ)
    (hK : IsKrausChannel K) (hL : IsKrausChannel L) (D D' : FiniteInstrument S o)
    (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) : Step S E o :=
  realizedStep S E o (mixKraus K L p) (mixKraus_channel hK hL hp hp1)
    (mixInstrument D D' q hq hq1)

theorem branch_real_smul (D : FiniteInstrument S o) (a : Fin o) (r : ℝ)
    (Z : Matrix S S ℂ) : D.branch a (r • Z)=r • D.branch a Z := by
  have he (A : Matrix S S ℂ) : r • A=(r:ℂ) • A := by ext i j; simp [Complex.real_smul]
  rw [he,FiniteInstrument.branch_smul,he]

/-- Exact arbitrary-complex input identity, with evolution before the instrument. -/
theorem mixedStep_branch {k l : ℕ}
    (K : Fin k → Matrix (S × E) (S × E) ℂ) (L : Fin l → Matrix (S × E) (S × E) ℂ)
    (hK : IsKrausChannel K) (hL : IsKrausChannel L) (D D' : FiniteInstrument S o)
    (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (a : Fin o) (Z : Matrix (S × E) (S × E) ℂ) :
    (mixedStep S E o K L hK hL D D' p q hp hp1 hq hq1).branch S E o a Z =
      ((1-p)*(1-q)) • (D.lift E).branch a (krausMap K Z) +
      (p*(1-q)) • (D.lift E).branch a (krausMap L Z) +
      ((1-p)*q) • (D'.lift E).branch a (krausMap K Z) +
      (p*q) • (D'.lift E).branch a (krausMap L Z) := by
  change (mixInstrument D D' q hq hq1 |>.lift E).branch a (krausMap (mixKraus K L p) Z)=_
  rw [mixInstrument_lift_branch,mixKraus_action K L hp hp1]
  simp only [FiniteInstrument.branch_add,branch_real_smul,smul_add,smul_smul]
  module

theorem mixedStep_positive_remainder {k l : ℕ}
    (K : Fin k → Matrix (S × E) (S × E) ℂ) (L : Fin l → Matrix (S × E) (S × E) ℂ)
    (hK : IsKrausChannel K) (hL : IsKrausChannel L) (D D' : FiniteInstrument S o)
    (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (a : Fin o) {Z : Matrix (S × E) (S × E) ℂ} (hZ : Z.PosSemidef) :
    ((mixedStep S E o K L hK hL D D' p q hp hp1 hq hq1).branch S E o a Z -
      ((1-p)*(1-q)) • (realizedStep S E o K hK D).branch S E o a Z).PosSemidef := by
  rw [mixedStep_branch]
  change (_ + _ + _ + _ - ((1-p)*(1-q)) • (D.lift E).branch a (krausMap K Z)).PosSemidef
  have hs : ∀ (r : ℝ) (A : Matrix (S × E) (S × E) ℂ), 0≤r → A.PosSemidef → (r • A).PosSemidef := by
    intro r A hr hA
    have he : r • A=(r:ℂ) • A := by ext i j; simp [Complex.real_smul]
    rw [he]
    exact hA.smul (Complex.zero_le_real.mpr hr)
  convert ((hs (p*(1-q)) _ (mul_nonneg hp (sub_nonneg.mpr hq1))
    ((D.lift E).branch_posSemidef a (krausMap_posSemidef L hZ))).add
    (hs ((1-p)*q) _ (mul_nonneg (sub_nonneg.mpr hp1) hq)
      ((D'.lift E).branch_posSemidef a (krausMap_posSemidef K hZ)))).add
    (hs (p*q) _ (mul_nonneg hp hq)
      ((D'.lift E).branch_posSemidef a (krausMap_posSemidef L hZ))) using 1
  abel

noncomputable def identityKraus : Fin 1 → Matrix Joint Joint ℂ := fun _ => 1

theorem identityKraus_normalized : IsKrausChannel identityKraus := by
  simp [identityKraus,IsKrausChannel]

noncomputable def memoryMixed (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    Step Qubit Qubit 2 :=
  mixedStep Qubit Qubit 2 identityKraus swapKraus identityKraus_normalized swapKraus_normalized
    (FiniteInstrument.prepare 0) (FiniteInstrument.prepare 1) p q hp hp1 hq hq1

noncomputable def memoryMixedTree (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    Tree Qubit Qubit 2 1 := .node (memoryMixed p q hp hp1 hq hq1) (fun _ => .done)

theorem memory_evolutions :
    krausMap identityKraus memoryInput=basisState 1 ⊗ₖ basisState 0 ∧
    krausMap swapKraus memoryInput=basisState 0 ⊗ₖ basisState 1 := by
  constructor
  · simp [krausMap,identityKraus,memoryInput]
  · exact swapJoint_basis 1 0

theorem memoryMixed_branch_zero (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    (memoryMixed p q hp hp1 hq hq1).branch Qubit Qubit 2 0 memoryInput =
      ((1-p)*(1-q)) • (basisState 0 ⊗ₖ basisState 0) +
      (p*(1-q)) • (basisState 0 ⊗ₖ basisState 1) := by
  rw [memoryMixed,mixedStep_branch]
  simp [memory_evolutions.1,memory_evolutions.2,lift_branch_tensor,prepare_basis]

theorem memoryMixed_branch_one (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    (memoryMixed p q hp hp1 hq hq1).branch Qubit Qubit 2 1 memoryInput =
      ((1-p)*q) • (basisState 1 ⊗ₖ basisState 0) +
      (p*q) • (basisState 1 ⊗ₖ basisState 1) := by
  rw [memoryMixed,mixedStep_branch]
  simp [memory_evolutions.1,memory_evolutions.2,lift_branch_tensor,prepare_basis]

/-- A real diagonal matrix has the sum of absolute diagonal entries as trace norm. -/
theorem traceNorm_real_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    traceNorm (Matrix.diagonal (fun i => (d i:ℂ))) = ∑ i, |d i| := by
  have ha : absOp (Matrix.diagonal (fun i => (d i:ℂ))) =
      Matrix.diagonal (fun i => ((|d i|:ℝ):ℂ)) := by
    refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _) ?_ ?_
    · exact Matrix.PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (abs_nonneg _))
    · rw [absOp_mul_self]
      simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      change star (d i:ℂ) * (d i:ℂ) = ((|d i|:ℝ):ℂ) * ((|d i|:ℝ):ℂ)
      simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul]
      congr 1
      nlinarith [sq_abs (d i)]
  rw [traceNorm_eq_trace_absOp,ha,Matrix.trace_diagonal,Complex.re_sum]
  rfl

noncomputable def quarterStep : Step Qubit Qubit 2 :=
  memoryMixed (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
noncomputable def quarterTree : Tree Qubit Qubit 2 1 := .node quarterStep (fun _ => .done)

theorem quarter_branch_zero : quarterStep.branch Qubit Qubit 2 0 memoryInput =
    (9/16:ℝ) • (basisState 0 ⊗ₖ basisState 0) + (3/16:ℝ) • (basisState 0 ⊗ₖ basisState 1) := by
  rw [quarterStep,memoryMixed_branch_zero]
  norm_num

theorem quarter_branch_one : quarterStep.branch Qubit Qubit 2 1 memoryInput =
    (3/16:ℝ) • (basisState 1 ⊗ₖ basisState 0) + (1/16:ℝ) • (basisState 1 ⊗ₖ basisState 1) := by
  rw [quarterStep,memoryMixed_branch_one]
  norm_num

noncomputable def quarterDelta (a : Qubit) (i : Joint) : ℝ :=
  if i.1=a then (if a=0 ∧ i.2=0 then -7/16 else if a=1 ∧ i.2=1 then 1/16 else 3/16) else 0

theorem quarter_difference (a : Qubit) :
    quarterStep.branch Qubit Qubit 2 a memoryInput - identityPrepare.branch Qubit Qubit 2 a memoryInput =
      Matrix.diagonal (fun i => (quarterDelta a i:ℂ)) := by
  have ha : a=0 ∨ a=1 := by fin_cases a <;> norm_num
  rcases ha with rfl | rfl <;> rw [memory_identity_branch]
  · rw [quarter_branch_zero]
    ext ⟨i,e⟩ ⟨j,f⟩
    fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
      norm_num [quarterDelta,basisState,Matrix.kronecker_apply,Matrix.diagonal_apply,Complex.real_smul]
  · rw [quarter_branch_one]
    ext ⟨i,e⟩ ⟨j,f⟩
    fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
      norm_num [quarterDelta,basisState,Matrix.kronecker_apply,Matrix.diagonal_apply,Complex.real_smul]

theorem quarter_outputDistance :
    outputDistance Qubit Qubit 2 quarterTree memoryIdentityTree memoryInput memoryInput=7/16 := by
  rw [quarterTree,memoryIdentityTree,outputDistance_one]
  simp only [stepDistance,quarter_difference,traceNorm_real_diagonal]
  norm_num [Fin.sum_univ_two,Fintype.sum_prod_type,quarterDelta]

theorem quarter_weights (a : Qubit) :
    (quarterStep.branch Qubit Qubit 2 a memoryInput).trace.re = if a=0 then 3/4 else 1/4 := by
  have ha : a=0 ∨ a=1 := by fin_cases a <;> norm_num
  rcases ha with rfl | rfl
  · rw [quarter_branch_zero]
    norm_num [Matrix.trace,Fin.sum_univ_two,Fintype.sum_prod_type,basisState,Matrix.kronecker_apply,Complex.real_smul]
  · rw [quarter_branch_one]
    norm_num [Matrix.trace,Fin.sum_univ_two,Fintype.sum_prod_type,basisState,Matrix.kronecker_apply,Complex.real_smul]

theorem quarter_historyVariation :
    historyVariation Qubit Qubit 2 quarterTree memoryIdentityTree memoryInput memoryInput=1/4 := by
  have hh : ∀ h : History 2 1,
      |weight Qubit Qubit 2 quarterTree h memoryInput - weight Qubit Qubit 2 memoryIdentityTree h memoryInput|=1/4 := by
    rintro ⟨a,u⟩; cases u
    change |(quarterStep.branch Qubit Qubit 2 a memoryInput).trace.re -
      (identityPrepare.branch Qubit Qubit 2 a memoryInput).trace.re|=1/4
    rw [quarter_weights,memory_identity_branch]
    fin_cases a <;> norm_num [(basisJoint_density 0 0).2]
  simp only [historyVariation,hh]
  change (∑ _ : Qubit × Unit, (1/4:ℝ))/2=1/4
  norm_num

theorem terminal_one (D : Step S E o) (X : Matrix (S × E) (S × E) ℂ) :
    terminalState S E o (.node D (fun _ => .done)) X=∑ a,D.branch S E o a X := by
  change (∑ h : Fin o × Unit,D.branch S E o h.1 X)=_
  simp [Fintype.sum_prod_type]

theorem quarter_terminal_difference :
    terminalState Qubit Qubit 2 quarterTree memoryInput -
      terminalState Qubit Qubit 2 memoryIdentityTree memoryInput =
      Matrix.diagonal (fun i => ((quarterDelta 0 i+quarterDelta 1 i:ℝ):ℂ)) := by
  rw [quarterTree,memoryIdentityTree,terminal_one,terminal_one,← Finset.sum_sub_distrib]
  simp only [quarter_difference,Fin.sum_univ_two]
  ext i j
  by_cases h : i=j
  · subst j; simp
  · simp [h]

theorem quarter_terminal_distance :
    traceDist (terminalState Qubit Qubit 2 quarterTree memoryInput)
      (terminalState Qubit Qubit 2 memoryIdentityTree memoryInput)=7/16 := by
  rw [traceDist,quarter_terminal_difference,traceNorm_real_diagonal]
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_two,quarterDelta]

/-- The independent-field pq branch is nonzero; all four basis coefficients survive. -/
theorem quarter_cross_term :
    (quarterStep.branch Qubit Qubit 2 1 memoryInput) (1,1) (1,1)=(1/16:ℂ) ∧
    (0:ℝ)<9/16 ∧ (0:ℝ)<3/16 ∧ (0:ℝ)<1/16 := by
  rw [quarter_branch_one]
  norm_num [basisState,Matrix.kronecker_apply,Complex.real_smul]

theorem quarter_strict_bounds :
    historyVariation Qubit Qubit 2 quarterTree memoryIdentityTree memoryInput memoryInput <
      outputDistance Qubit Qubit 2 quarterTree memoryIdentityTree memoryInput memoryInput ∧
    outputDistance Qubit Qubit 2 quarterTree memoryIdentityTree memoryInput memoryInput < (1/4:ℝ)+(1/4) := by
  rw [quarter_historyVariation,quarter_outputDistance]
  norm_num

theorem quarter_cross_nonzero :
    (quarterStep.branch Qubit Qubit 2 1 memoryInput) (1,1) (1,1)≠0 := by
  rw [quarter_cross_term.1]
  norm_num

/-- Constructive node data, with realization on every complex joint matrix.
No positivity or distance conclusion is a field of this witness. -/
structure RealizesMixture (I N : Step S E o) (p q : ℝ) where
  k : ℕ
  l : ℕ
  K : Fin k → Matrix (S × E) (S × E) ℂ
  L : Fin l → Matrix (S × E) (S × E) ℂ
  hK : IsKrausChannel K
  hL : IsKrausChannel L
  D : FiniteInstrument S o
  D' : FiniteInstrument S o
  hp : 0≤p
  hp1 : p≤1
  hq : 0≤q
  hq1 : q≤1
  ideal_action : ∀ a Z, I.branch S E o a Z=(realizedStep S E o K hK D).branch S E o a Z
  mixed_action : ∀ a Z, N.branch S E o a Z=
    (mixedStep S E o K L hK hL D D' p q hp hp1 hq hq1).branch S E o a Z

/-- Zero evolution noise still has two Kraus entries, but its action is identity. -/
theorem mixed_identity_evolution_action (D D' : FiniteInstrument Qubit 2)
    (q : ℝ) (hq : 0≤q) (hq1 : q≤1) (a : Qubit) (Z : Matrix Joint Joint ℂ) :
    (mixedStep Qubit Qubit 2 identityKraus identityKraus identityKraus_normalized
      identityKraus_normalized D D' 0 q le_rfl (by norm_num) hq hq1).branch Qubit Qubit 2 a Z =
      ((mixInstrument D D' q hq hq1).lift Qubit).branch a Z := by
  change ((mixInstrument D D' q hq hq1).lift Qubit).branch a
    (krausMap (mixKraus identityKraus identityKraus 0) Z)=_
  rw [mixKraus_action identityKraus identityKraus le_rfl (by norm_num)]
  simp [identityKraus,krausMap]

theorem read_ideal_action (a : Qubit) (Z : Matrix Joint Joint ℂ) :
    readStep.branch Qubit Qubit 2 a Z =
      (realizedStep Qubit Qubit 2 identityKraus identityKraus_normalized
        FiniteInstrument.computational).branch Qubit Qubit 2 a Z := rfl

theorem read_mixed_action (a : Qubit) (Z : Matrix Joint Joint ℂ) :
    readStep.branch Qubit Qubit 2 a Z =
      (mixedStep Qubit Qubit 2 identityKraus identityKraus identityKraus_normalized
        identityKraus_normalized FiniteInstrument.computational FiniteInstrument.computational
        0 0 le_rfl (by norm_num) le_rfl (by norm_num)).branch Qubit Qubit 2 a Z := by
  rw [mixed_identity_evolution_action,mixInstrument_lift_branch]
  simp [readStep,localStep_branch]

noncomputable def read_realization : RealizesMixture Qubit Qubit 2 readStep readStep 0 0 where
  k := 1
  l := 1
  K := identityKraus
  L := identityKraus
  hK := identityKraus_normalized
  hL := identityKraus_normalized
  D := FiniteInstrument.computational
  D' := FiniteInstrument.computational
  hp := le_rfl
  hp1 := by norm_num
  hq := le_rfl
  hq1 := by norm_num
  ideal_action := read_ideal_action
  mixed_action := read_mixed_action

theorem feedback_ideal_action (b a : Qubit) (Z : Matrix Joint Joint ℂ) :
    (idealStep b).branch Qubit Qubit 2 a Z =
      (realizedStep Qubit Qubit 2 identityKraus identityKraus_normalized
        (FiniteInstrument.prepare b)).branch Qubit Qubit 2 a Z := rfl

theorem feedback_mixed_action (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (b a : Qubit)
    (Z : Matrix Joint Joint ℂ) :
    (noisyStepAt p hp hp1 b).branch Qubit Qubit 2 a Z =
      (mixedStep Qubit Qubit 2 identityKraus identityKraus identityKraus_normalized
        identityKraus_normalized (FiniteInstrument.prepare b) (FiniteInstrument.prepare (1-b))
        0 p le_rfl (by norm_num) hp hp1).branch Qubit Qubit 2 a Z := by
  rw [mixed_identity_evolution_action]
  exact localStep_branch Qubit Qubit 2 _ a Z

noncomputable def feedback_realization (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (b : Qubit) :
    RealizesMixture Qubit Qubit 2 (idealStep b) (noisyStepAt p hp hp1 b) 0 p where
  k := 1
  l := 1
  K := identityKraus
  L := identityKraus
  hK := identityKraus_normalized
  hL := identityKraus_normalized
  D := FiniteInstrument.prepare b
  D' := FiniteInstrument.prepare (1-b)
  hp := le_rfl
  hp1 := by norm_num
  hq := hp
  hq1 := hp1
  ideal_action := feedback_ideal_action b
  mixed_action := feedback_mixed_action p hp hp1 b

/-- Record counts differ even though every branch action above agrees. -/
theorem read_count_mismatch :
    readStep.count=1 ∧
      (mixedStep Qubit Qubit 2 identityKraus identityKraus identityKraus_normalized
        identityKraus_normalized FiniteInstrument.computational FiniteInstrument.computational
        0 0 le_rfl (by norm_num) le_rfl (by norm_num)).count=2 := ⟨rfl,rfl⟩

theorem feedback_count_mismatch (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (b : Qubit) :
    (noisyStepAt p hp hp1 b).count=1 ∧
      (mixedStep Qubit Qubit 2 identityKraus identityKraus identityKraus_normalized
        identityKraus_normalized (FiniteInstrument.prepare b) (FiniteInstrument.prepare (1-b))
        0 p le_rfl (by norm_num) hp hp1).count=2 := ⟨rfl,rfl⟩

theorem read_records_ne :
    readStep ≠ mixedStep Qubit Qubit 2 identityKraus identityKraus identityKraus_normalized
      identityKraus_normalized FiniteInstrument.computational FiniteInstrument.computational
      0 0 le_rfl (by norm_num) le_rfl (by norm_num) := by
  intro h
  have hc := congrArg Step.count h
  change (1:ℕ)=2 at hc
  omega

/-- Dimensionless depthwise rates. Bounds live in the rate data even when the
outcome type is empty, so no vacuous continuation premise can hide invalid rates. -/
structure NoiseRates where
  p : ℝ
  q : ℝ
  hp : 0≤p
  hp1 : p≤1
  hq : 0≤q
  hq1 : q≤1

noncomputable def retention (r : NoiseRates) : ℝ := (1-r.p)*(1-r.q)
noncomputable def survival (rs : List NoiseRates) : ℝ := (rs.map retention).prod

theorem retention_mem (r : NoiseRates) : retention r ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact mul_nonneg (sub_nonneg.mpr r.hp1) (sub_nonneg.mpr r.hq1)
  · exact mul_le_one₀ (by linarith [r.hp]) (sub_nonneg.mpr r.hq1) (by linarith [r.hq])

theorem survival_mem (rs : List NoiseRates) : survival rs ∈ Set.Icc (0:ℝ) 1 := by
  induction rs with
  | nil => norm_num [survival]
  | cons r rs ih =>
    change retention r * survival rs ∈ Set.Icc (0:ℝ) 1
    exact ⟨mul_nonneg (retention_mem r).1 ih.1,mul_le_one₀ (retention_mem r).2 ih.1 ih.2⟩

/-- The same rate list indexes the actual trees and every actual continuation. -/
inductive PairedMixture : {n : ℕ} → Tree S E o n → Tree S E o n → List NoiseRates → Prop
  | done : PairedMixture .done .done []
  | node {n : ℕ} {I N : Step S E o} {T U : Fin o → Tree S E o n}
      {r : NoiseRates} {rs : List NoiseRates}
      (realization : RealizesMixture S E o I N r.p r.q) (length : rs.length=n)
      (next : ∀ a,PairedMixture (T a) (U a) rs) :
      PairedMixture (.node I T) (.node N U) (r::rs)

theorem pairedMixture_length {n : ℕ} {T U : Tree S E o n} {rs : List NoiseRates}
    (h : PairedMixture S E o T U rs) : rs.length=n := by
  cases h with
  | done => rfl
  | node hr hn ht => simpa using congrArg Nat.succ hn

theorem real_smul_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {r : ℝ} (hr : 0≤r) : (r • A).PosSemidef := by
  have he : r • A=(r:ℂ) • A := by ext i j; simp [Complex.real_smul]
  rw [he]
  exact hA.smul (Complex.zero_le_real.mpr hr)

theorem run_real_smul {n : ℕ} (T : Tree S E o n) (h : History o n)
    (r : ℝ) (Z : Matrix (S × E) (S × E) ℂ) : run S E o T h (r • Z)=r • run S E o T h Z := by
  have he (A : Matrix (S × E) (S × E) ℂ) : r • A=(r:ℂ) • A := by ext i j; simp [Complex.real_smul]
  rw [he,run_smul,he]

theorem realization_positive_remainder {I N : Step S E o} {r : NoiseRates}
    (R : RealizesMixture S E o I N r.p r.q) (a : Fin o)
    {Z : Matrix (S × E) (S × E) ℂ} (hZ : Z.PosSemidef) :
    (N.branch S E o a Z-retention r • I.branch S E o a Z).PosSemidef := by
  rw [R.mixed_action,R.ideal_action]
  exact mixedStep_positive_remainder S E o R.K R.L R.hK R.hL R.D R.D'
    r.p r.q R.hp R.hp1 R.hq R.hq1 a hZ

/-- Positive remainder on every complete actual history, with no outcome selection. -/
theorem pairedMixture_remainder {n : ℕ} {T U : Tree S E o n} {rs : List NoiseRates}
    (H : PairedMixture S E o T U rs) (h : History o n)
    {Z : Matrix (S × E) (S × E) ℂ} (hZ : Z.PosSemidef) :
    (run S E o U h Z-survival rs • run S E o T h Z).PosSemidef := by
  induction H generalizing Z with
  | done => simpa [run,survival] using (Matrix.PosSemidef.zero : (0 : Matrix (S × E) (S × E) ℂ).PosSemidef)
  | @node n I N T U r rs R hlen next ih =>
    rcases h with ⟨a,h⟩
    have hfirst := ih a h (N.branch_posSemidef S E o a hZ)
    have hsecond := real_smul_posSemidef
      (run_posSemidef S E o (T a) h (realization_positive_remainder S E o R a hZ))
      (survival_mem rs).1
    convert hfirst.add hsecond using 1
    simp only [run,run_sub,run_real_smul,survival,List.map_cons,List.prod_cons]
    module

/-- Exact total remainder mass follows from actual normalization, not from a
postselected or normalized remainder channel. -/
theorem pairedMixture_remainder_mass {n : ℕ} (T U : Tree S E o n) (rs : List NoiseRates)
    (Z : Matrix (S × E) (S × E) ℂ) :
    (∑ h,(run S E o U h Z-survival rs • run S E o T h Z).trace.re)=
      (1-survival rs)*Z.trace.re := by
  simp only [Matrix.trace_sub,Matrix.trace_smul,Complex.sub_re,
    Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Complex.re_sum,← Complex.re_sum,sum_trace,sum_trace]
  ring

theorem traceNorm_real_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 0≤r) (A : Matrix ι ι ℂ) : traceNorm (r • A)=r*traceNorm A := by
  have he : r • A=(r:ℂ) • A := by ext i j; simp [Complex.real_smul]
  rw [he,traceNorm_smul_nonneg hr]

theorem surviving_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C : Matrix ι ι ℂ) (w : ℝ) (hw : w ∈ Set.Icc (0:ℝ) 1)
    (hA : A.PosSemidef) (hR : (C-w • B).PosSemidef) :
    traceNorm (A-C) ≤ w*traceNorm (A-B)+(1-w)*A.trace.re+(C-w • B).trace.re := by
  have he : A-C=(w • (A-B)+(1-w) • A)-(C-w • B) := by module
  rw [he]
  have h₁ := traceNorm_sub_le (w • (A-B)+(1-w) • A) (C-w • B)
  have h₂ := traceNorm_triangle (w • (A-B)) ((1-w) • A)
  rw [traceNorm_real_smul w hw.1,traceNorm_real_smul (1-w) (sub_nonneg.mpr hw.2),
    traceNorm_posSemidef hA] at h₂
  rw [traceNorm_posSemidef hR] at h₁
  linarith

/-- The surviving ideal component also contracts a changed input.  The positive
remainder is never divided by its mass, including at survival zero or one. -/
theorem pairedMixture_changed_input {n : ℕ} {T U : Tree S E o n} {rs : List NoiseRates}
    (H : PairedMixture S E o T U rs) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance S E o T U X Y ≤ survival rs*traceDist X Y+1-survival rs := by
  have hw := survival_mem rs
  have hpoint (h : History o n) := surviving_norm_bound
    (run S E o T h X) (run S E o T h Y) (run S E o U h Y) (survival rs) hw
    (run_posSemidef S E o T h hX.1) (pairedMixture_remainder S E o H h hY.1)
  have hs := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => hpoint h)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  rw [← Complex.re_sum,sum_trace,pairedMixture_remainder_mass,hX.2,hY.2] at hs
  have hc := outputDistance_common S E o T hX.1.isHermitian hY.1.isHermitian
  unfold outputDistance at hc ⊢
  simp only [Complex.one_re] at hs
  have hcscale := mul_le_mul_of_nonneg_left hc hw.1
  linarith


theorem pairedMixture_history {n : ℕ} {T U : Tree S E o n} {rs : List NoiseRates}
    (H : PairedMixture S E o T U rs) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    historyVariation S E o T U X Y ≤ survival rs*traceDist X Y+1-survival rs :=
  (historyVariation_le_outputDistance S E o T U hX.1.isHermitian hY.1.isHermitian).trans
    (pairedMixture_changed_input S E o H hX hY)

theorem pairedMixture_terminal {n : ℕ} {T U : Tree S E o n} {rs : List NoiseRates}
    (H : PairedMixture S E o T U rs) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    traceDist (terminalState S E o T X) (terminalState S E o U Y) ≤
      survival rs*traceDist X Y+1-survival rs :=
  (terminalState_distance S E o T U X Y).trans (pairedMixture_changed_input S E o H hX hY)

theorem survival_bound_cap (rs : List NoiseRates) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    survival rs*traceDist X Y+1-survival rs ≤ 1 := by
  have h := outputDistance_mass S E 0 (.done) (.done) hX.1 hY.1
  rw [outputDistance_done,hX.2,hY.2] at h
  norm_num at h
  have hs := mul_le_mul_of_nonneg_left h (survival_mem rs).1
  linarith

theorem survival_additive (rs : List NoiseRates) :
    1-survival rs ≤ (rs.map (fun r => r.p+r.q)).sum := by
  induction rs with
  | nil => simp [survival]
  | cons r rs ih =>
    change 1-retention r*survival rs ≤ (r.p+r.q)+(rs.map (fun r => r.p+r.q)).sum
    have hprod := mul_nonneg r.hp r.hq
    have hr := retention_mem r
    have hs := survival_mem rs
    have hcross := mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr hs.2)
    dsimp [retention] at *
    nlinarith

theorem pairedMixture_identical_input {n : ℕ} {T U : Tree S E o n} {rs : List NoiseRates}
    (H : PairedMixture S E o T U rs) {X : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) :
    outputDistance S E o T U X X ≤ 1-survival rs := by
  simpa [traceDist_self] using pairedMixture_changed_input S E o H hX hX

def zeroRates : NoiseRates := ⟨0,0,le_rfl,by norm_num,le_rfl,by norm_num⟩
def feedbackRate (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : NoiseRates :=
  ⟨0,p,le_rfl,by norm_num,hp,hp1⟩

theorem feedback_suffix_paired (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) (a : Qubit) :
    PairedMixture Qubit Qubit 2 (idealSuffix m a) (noisySuffix p hp hp1 m a)
      (List.replicate m (feedbackRate p hp hp1)) := by
  induction m generalizing a with
  | zero => exact .done
  | succ m ih =>
    exact .node (feedback_realization p hp hp1 a) (List.length_replicate ..) ih

theorem feedback_paired (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    PairedMixture Qubit Qubit 2 (idealFeedback m) (noisyFeedback p hp hp1 m)
      (zeroRates :: List.replicate m (feedbackRate p hp hp1)) :=
  .node read_realization (List.length_replicate ..) (feedback_suffix_paired p hp hp1 m)

theorem feedback_survival (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    survival (zeroRates :: List.replicate m (feedbackRate p hp hp1))=(1-p)^m := by
  simp [survival,retention,zeroRates,feedbackRate]

theorem feedback_changed_input (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    {X Y : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance Qubit Qubit 2 (idealFeedback m) (noisyFeedback p hp hp1 m) X Y ≤
      (1-p)^m*traceDist X Y+1-(1-p)^m := by
  simpa only [feedback_survival] using
    pairedMixture_changed_input Qubit Qubit 2 (feedback_paired p hp hp1 m) hX hY

/-- Exact accepted adaptive dynamics saturate the newly derived generic bound. -/
theorem feedback_survival_sharp (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    outputDistance Qubit Qubit 2 (idealFeedback m) (noisyFeedback p hp hp1 m)
      correlatedInput correlatedInput =
      1-survival (zeroRates :: List.replicate m (feedbackRate p hp hp1)) ∧
    historyVariation Qubit Qubit 2 (idealFeedback m) (noisyFeedback p hp hp1 m)
      correlatedInput correlatedInput =
      1-survival (zeroRates :: List.replicate m (feedbackRate p hp hp1)) := by
  rw [feedback_survival]
  exact ⟨(noisyFeedback_exact p hp hp1 m).1,(noisyFeedback_exact p hp hp1 m).2.1⟩


noncomputable def memoryDelta (p q : ℝ) (a : Qubit) (i : Joint) : ℝ :=
  if i.1=a then
    if a=0 then (if i.2=0 then (1-p)*(1-q)-1 else p*(1-q))
    else (if i.2=0 then (1-p)*q else p*q)
  else 0

theorem memory_difference (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (a : Qubit) :
    (memoryMixed p q hp hp1 hq hq1).branch Qubit Qubit 2 a memoryInput -
      identityPrepare.branch Qubit Qubit 2 a memoryInput =
      Matrix.diagonal (fun i => (memoryDelta p q a i:ℂ)) := by
  have ha : a=0 ∨ a=1 := by fin_cases a <;> norm_num
  rcases ha with rfl | rfl <;> rw [memory_identity_branch]
  · rw [memoryMixed_branch_zero]
    ext ⟨i,e⟩ ⟨j,f⟩
    fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
      simp [memoryDelta,basisState,Complex.real_smul]
  · rw [memoryMixed_branch_one]
    ext ⟨i,e⟩ ⟨j,f⟩
    fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
      simp [memoryDelta,basisState,Complex.real_smul]

theorem memory_abs_sum (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    (∑ a : Qubit,∑ i : Joint,|memoryDelta p q a i|)=2*(p+q-p*q) := by
  have h00 : (1-p)*(1-q)-1≤0 :=
    sub_nonpos.mpr (mul_le_one₀ (by linarith) (by linarith) (by linarith))
  simp [Fin.sum_univ_two,Fintype.sum_prod_type,memoryDelta,abs_of_nonpos h00,
    abs_of_nonneg (mul_nonneg hp (sub_nonneg.mpr hq1)),
    abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hp1) hq),
    abs_of_nonneg (mul_nonneg hp hq)]
  ring

theorem memory_output_exact (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    outputDistance Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1)
      memoryIdentityTree memoryInput memoryInput=p+q-p*q := by
  rw [memoryMixedTree,memoryIdentityTree,outputDistance_one]
  simp only [stepDistance,memory_difference,traceNorm_real_diagonal]
  rw [memory_abs_sum p q hp hp1 hq hq1]
  ring

theorem memory_terminal_difference (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    terminalState Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) memoryInput -
      terminalState Qubit Qubit 2 memoryIdentityTree memoryInput =
      Matrix.diagonal (fun i => ((memoryDelta p q 0 i+memoryDelta p q 1 i:ℝ):ℂ)) := by
  rw [memoryMixedTree,memoryIdentityTree,terminal_one,terminal_one,← Finset.sum_sub_distrib]
  simp only [memory_difference,Fin.sum_univ_two]
  ext i j
  by_cases h : i=j
  · subst j; simp
  · simp [h]

theorem memory_terminal_exact (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    traceDist (terminalState Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) memoryInput)
      (terminalState Qubit Qubit 2 memoryIdentityTree memoryInput)=p+q-p*q := by
  rw [traceDist,memory_terminal_difference,traceNorm_real_diagonal]
  have he : (∑ i : Joint,|memoryDelta p q 0 i+memoryDelta p q 1 i|)=
      ∑ a : Qubit,∑ i : Joint,|memoryDelta p q a i| := by
    simp [Fintype.sum_prod_type,Fin.sum_univ_two,memoryDelta]
  rw [he,memory_abs_sum p q hp hp1 hq hq1]
  ring

theorem memory_weights (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) (a : Qubit) :
    ((memoryMixed p q hp hp1 hq hq1).branch Qubit Qubit 2 a memoryInput).trace.re =
      if a=0 then 1-q else q := by
  have ha : a=0 ∨ a=1 := by fin_cases a <;> norm_num
  rcases ha with rfl | rfl
  · rw [memoryMixed_branch_zero]
    simp [Matrix.trace,Fin.sum_univ_two,Fintype.sum_prod_type,basisState,Complex.real_smul]
    ring
  · rw [memoryMixed_branch_one]
    simp [Matrix.trace,Fin.sum_univ_two,Fintype.sum_prod_type,basisState,Complex.real_smul]
    ring

theorem memory_history_exact (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    historyVariation Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1)
      memoryIdentityTree memoryInput memoryInput=q := by
  have hh : ∀ h : History 2 1,
      |weight Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) h memoryInput -
        weight Qubit Qubit 2 memoryIdentityTree h memoryInput|=q := by
    rintro ⟨a,u⟩; cases u
    change |((memoryMixed p q hp hp1 hq hq1).branch Qubit Qubit 2 a memoryInput).trace.re -
      (identityPrepare.branch Qubit Qubit 2 a memoryInput).trace.re|=q
    rw [memory_weights,memory_identity_branch]
    fin_cases a <;> simp [(basisJoint_density 0 0).2,abs_of_nonneg hq]
  simp only [historyVariation,hh]
  change (∑ _ : Qubit × Unit,q)/2=q
  simp


/-- A concrete test vector for the actual coherent partial-SWAP channel. -/
noncomputable def coherentTest : Joint → ℂ :=
  fun i => if i=(1,0) then 4/5 else if i=(0,1) then 3*Complex.I/5 else 0

theorem coherent_quadratic (r : ℝ) :
    star coherentTest ⬝ᵥ
      ((CoherentMemoryProcess.evolution (CoherentMemoryProcess.input 1) -
        r • CoherentMemoryProcess.input 1) *ᵥ coherentTest) = (-16*r/25:ℂ) := by
  rw [CoherentMemoryProcess.first_state,CoherentMemoryProcess.input_sector.2]
  simp [dotProduct,Matrix.mulVec,coherentTest,CoherentMemoryProcess.sector,
    Fintype.sum_prod_type,Fin.sum_univ_two,Complex.real_smul]
  ring_nf
  norm_num [Complex.I_sq,map_ofNat]
  ring

theorem coherent_no_positive_component (r : ℝ) (hr : 0<r) :
    ¬ (CoherentMemoryProcess.evolution (CoherentMemoryProcess.input 1) -
      r • CoherentMemoryProcess.input 1).PosSemidef := by
  intro h
  have hn := h.dotProduct_mulVec_nonneg coherentTest
  rw [coherent_quadratic] at hn
  have hre := (Complex.nonneg_iff.mp hn).1
  norm_num at hre
  linarith

theorem memory_error_gap (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    outputDistance Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1)
      memoryIdentityTree memoryInput memoryInput -
      historyVariation Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1)
        memoryIdentityTree memoryInput memoryInput = p*(1-q) := by
  rw [memory_output_exact,memory_history_exact]
  ring

theorem memory_strict_gap (p q : ℝ) (hp : 0<p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q<1) :
    historyVariation Qubit Qubit 2 (memoryMixedTree p q hp.le hp1 hq hq1.le)
      memoryIdentityTree memoryInput memoryInput <
      outputDistance Qubit Qubit 2 (memoryMixedTree p q hp.le hp1 hq hq1.le)
        memoryIdentityTree memoryInput memoryInput := by
  have h := memory_error_gap p q hp.le hp1 hq hq1.le
  have hpos := mul_pos hp (sub_pos.mpr hq1)
  linarith

theorem memory_q_zero (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    outputDistance Qubit Qubit 2 (memoryMixedTree p 0 hp hp1 le_rfl (by norm_num))
      memoryIdentityTree memoryInput memoryInput = p ∧
    historyVariation Qubit Qubit 2 (memoryMixedTree p 0 hp hp1 le_rfl (by norm_num))
      memoryIdentityTree memoryInput memoryInput = 0 := by
  simp [memory_output_exact,memory_history_exact]

theorem memory_p_zero (q : ℝ) (hq : 0≤q) (hq1 : q≤1) :
    outputDistance Qubit Qubit 2 (memoryMixedTree 0 q le_rfl (by norm_num) hq hq1)
      memoryIdentityTree memoryInput memoryInput = q ∧
    historyVariation Qubit Qubit 2 (memoryMixedTree 0 q le_rfl (by norm_num) hq hq1)
      memoryIdentityTree memoryInput memoryInput = q := by
  simp [memory_output_exact,memory_history_exact]

theorem memory_unit_separation :
    outputDistance Qubit Qubit 2 (memoryMixedTree 1 0 (by norm_num) le_rfl le_rfl (by norm_num))
      memoryIdentityTree memoryInput memoryInput = 1 ∧
    historyVariation Qubit Qubit 2 (memoryMixedTree 1 0 (by norm_num) le_rfl le_rfl (by norm_num))
      memoryIdentityTree memoryInput memoryInput = 0 := memory_q_zero 1 (by norm_num) le_rfl


theorem realization_zero_action {I N : Step S E o}
    (R : RealizesMixture S E o I N 0 0) (a : Fin o) (Z : Matrix (S × E) (S × E) ℂ) :
    N.branch S E o a Z=I.branch S E o a Z := by
  rw [R.mixed_action,R.ideal_action,mixedStep_branch]
  simp [realizedStep,Step.branch]

/-- Zero noise preserves the full evaluated maps on arbitrary complex inputs. -/
theorem pairedMixture_zero_action {n : ℕ} {T U : Tree S E o n} {rs : List NoiseRates}
    (H : PairedMixture S E o T U rs) (hz : ∀ r ∈ rs,r.p=0 ∧ r.q=0)
    (h : History o n) (Z : Matrix (S × E) (S × E) ℂ) :
    run S E o U h Z=run S E o T h Z := by
  induction H generalizing Z with
  | done => rfl
  | @node n I N T U r rs R hlen next ih =>
    rcases h with ⟨a,h⟩
    have hr := hz r (by simp)
    have R0 : RealizesMixture S E o I N 0 0 := by simpa only [hr.1,hr.2] using R
    change run S E o (U a) h (N.branch S E o a Z)=run S E o (T a) h (I.branch S E o a Z)
    rw [realization_zero_action S E o R0]
    exact ih a (fun r hr => hz r (List.mem_cons_of_mem _ hr)) h _

theorem survival_zero_rates (rs : List NoiseRates) (hz : ∀ r ∈ rs,r.p=0 ∧ r.q=0) :
    survival rs=1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr := hz r (by simp)
    change retention r * survival rs=1
    rw [ih (fun r hr => hz r (List.mem_cons_of_mem _ hr))]
    simp [retention,hr.1,hr.2]

theorem survival_full_rate (rs : List NoiseRates) (r : NoiseRates) (hr : r ∈ rs)
    (hfull : r.p=1 ∨ r.q=1) : survival rs=0 := by
  have he : retention r=0 := by
    rcases hfull with hp | hq
    · simp [retention,hp]
    · simp [retention,hq]
  unfold survival
  apply List.prod_eq_zero (List.mem_map.mpr ⟨r,hr,he⟩)

theorem pairedMixture_full_noise {n : ℕ} {T U : Tree S E o n} {rs : List NoiseRates}
    (H : PairedMixture S E o T U rs) (r : NoiseRates) (hr : r ∈ rs)
    (hfull : r.p=1 ∨ r.q=1) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance S E o T U X Y≤1 := by
  simpa [survival_full_rate rs r hr hfull] using pairedMixture_changed_input S E o H hX hY

theorem zero_positive_remainder {n : ℕ} (T U : Tree S E o n) (rs : List NoiseRates)
    (h : History o n) :
    run S E o U h 0-survival rs • run S E o T h 0=0 := by simp [run_zero]

theorem depth_zero_guard (X Y : Matrix (S × E) (S × E) ℂ) :
    survival []=1 ∧ outputDistance S E o .done .done X Y=traceDist X Y :=
  ⟨rfl,outputDistance_done S E o X Y⟩

theorem impossible_ideal_remainder {n : ℕ} (T U : Tree S E o n) (rs : List NoiseRates)
    (h : History o n) (Z : Matrix (S × E) (S × E) ℂ) (hz : run S E o T h Z=0) :
    run S E o U h Z-survival rs • run S E o T h Z=run S E o U h Z := by simp [hz]

theorem memory_impossible_outcome (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    run Qubit Qubit 2 (memoryMixedTree p 0 hp hp1 le_rfl (by norm_num)) (1,()) memoryInput=0 := by
  change (memoryMixed p 0 hp hp1 le_rfl (by norm_num)).branch Qubit Qubit 2 1 memoryInput=0
  rw [memoryMixed_branch_one]
  simp

theorem memory_new_outcome_positive (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0<q) (hq1 : q≤1) :
    run Qubit Qubit 2 memoryIdentityTree (1,()) memoryInput=0 ∧
    0<weight Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq.le hq1) (1,()) memoryInput := by
  constructor
  · exact memory_identity_branch 1
  · change 0<((memoryMixed p q hp hp1 hq.le hq1).branch Qubit Qubit 2 1 memoryInput).trace.re
    simpa only [memory_weights,show (1:Qubit)≠0 by decide,ite_false] using hq

def independentRate (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) : NoiseRates :=
  ⟨p,q,hp,hp1,hq,hq1⟩

noncomputable def memory_realization (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    RealizesMixture Qubit Qubit 2 identityPrepare (memoryMixed p q hp hp1 hq hq1) p q where
  k := 1
  l := 1
  K := identityKraus
  L := swapKraus
  hK := identityKraus_normalized
  hL := swapKraus_normalized
  D := FiniteInstrument.prepare 0
  D' := FiniteInstrument.prepare 1
  hp := hp
  hp1 := hp1
  hq := hq
  hq1 := hq1
  ideal_action := by intro a Z; rfl
  mixed_action := by intro a Z; rfl

theorem memory_paired (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    PairedMixture Qubit Qubit 2 memoryIdentityTree (memoryMixedTree p q hp hp1 hq hq1)
      [independentRate p q hp hp1 hq hq1] :=
  .node (memory_realization p q hp hp1 hq hq1) rfl (fun _ => .done)

theorem memory_survival_sharp (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    outputDistance Qubit Qubit 2 memoryIdentityTree (memoryMixedTree p q hp hp1 hq hq1)
      memoryInput memoryInput = 1-survival [independentRate p q hp hp1 hq hq1] := by
  rw [outputDistance_comm,memory_output_exact]
  simp [survival,retention,independentRate]
  ring


theorem survival_bound_additive (rs : List NoiseRates) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    survival rs*traceDist X Y+1-survival rs ≤ traceDist X Y+(rs.map (fun r => r.p+r.q)).sum := by
  have hmul := mul_le_mul_of_nonneg_right (survival_mem rs).2 (traceDist_mem_Icc hX hY).1
  have hs := survival_additive rs
  linarith

theorem pairedMixture_capped {n : ℕ} {T U : Tree S E o n} {rs : List NoiseRates}
    (H : PairedMixture S E o T U rs) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance S E o T U X Y ≤
      min 1 (survival rs*traceDist X Y+1-survival rs) :=
  le_min ((pairedMixture_changed_input S E o H hX hY).trans (survival_bound_cap S E rs hX hY))
    (pairedMixture_changed_input S E o H hX hY)

theorem pairedMixture_additive_capped {n : ℕ} {T U : Tree S E o n} {rs : List NoiseRates}
    (H : PairedMixture S E o T U rs) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance S E o T U X Y ≤ min 1 (traceDist X Y+(rs.map (fun r => r.p+r.q)).sum) :=
  le_min ((pairedMixture_changed_input S E o H hX hY).trans (survival_bound_cap S E rs hX hY))
    ((pairedMixture_changed_input S E o H hX hY).trans (survival_bound_additive S E rs hX hY))

theorem feedback_zero_noise_action (m : ℕ) (h : History 2 (m+1)) (Z : Matrix Joint Joint ℂ) :
    run Qubit Qubit 2 (noisyFeedback 0 le_rfl (by norm_num) m) h Z =
      run Qubit Qubit 2 (idealFeedback m) h Z := by
  apply pairedMixture_zero_action Qubit Qubit 2 (feedback_paired 0 le_rfl (by norm_num) m)
  intro r hr
  simp only [List.mem_cons,List.mem_replicate] at hr
  rcases hr with rfl | ⟨_,rfl⟩ <;> exact ⟨rfl,rfl⟩

theorem feedback_endpoint_survival (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    survival (zeroRates :: List.replicate 0 (feedbackRate p hp hp1))=1 ∧
    survival (zeroRates :: List.replicate m (feedbackRate 0 le_rfl (by norm_num)))=1 ∧
    survival (zeroRates :: List.replicate 1 (feedbackRate p hp hp1))=1-p := by
  simp only [feedback_survival,pow_zero,pow_one,sub_zero,one_pow,and_self]

theorem feedback_full_noise_survival (m : ℕ) (hm : 0<m) :
    survival (zeroRates :: List.replicate m (feedbackRate 1 (by norm_num) le_rfl))=0 ∧
    outputDistance Qubit Qubit 2 (idealFeedback m)
      (noisyFeedback 1 (by norm_num) le_rfl m) correlatedInput correlatedInput=1 := by
  rw [feedback_survival,(noisyFeedback_exact 1 (by norm_num) le_rfl m).1]
  simp [Nat.ne_of_gt hm]

theorem memory_changed_input (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    {X Y : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance Qubit Qubit 2 memoryIdentityTree (memoryMixedTree p q hp hp1 hq hq1) X Y ≤
      (1-p)*(1-q)*traceDist X Y+(p+q-p*q) := by
  have h := pairedMixture_changed_input Qubit Qubit 2 (memory_paired p q hp hp1 hq hq1) hX hY
  simp only [survival,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
    retention,independentRate] at h
  convert h using 1
  ring

theorem coherent_densities :
    IsDensityOperator (CoherentMemoryProcess.input 1) ∧
      IsDensityOperator (CoherentMemoryProcess.evolution (CoherentMemoryProcess.input 1)) := by
  refine ⟨CoherentMemoryProcess.input_density 1,?_⟩
  have hk : IsKrausChannel (fun _ : Fin 1 => CoherentMemoryProcess.U) := by
    simpa [IsKrausChannel] using CoherentMemoryProcess.coherentUnitary
  simpa [krausMap,CoherentMemoryProcess.evolution] using
    krausMap_isDensityOperator hk (CoherentMemoryProcess.input_density 1)

end SKEFTHawking.QuantumNetwork.FiniteAdaptiveMixtureSurvival
