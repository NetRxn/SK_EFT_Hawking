import SKEFTHawking.QuantumNetwork.FiniteThreeLevelThermalPhase

/-! Three-outcome coherent readout on the actual three-level thermal process.
The preparation uses the full Hamiltonian channel. The observation keeps all
unnormalized histories and uses the unchanged computational reset tail. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelCoherentReadout
open Matrix FinitePositiveKernel DiagonalLindblad GibbsObservable
open OpenSystems FiniteInterventionProcess GibbsMultilevelReflection GibbsMultilevelProcess
open FiniteThreeLevelThermalPhase
open FiniteAdaptiveReadoutDiscrimination FiniteAdaptiveReadoutRobustness
open FiniteAdaptiveMapPerturbation
open scoped ComplexOrder Kronecker BigOperators

abbrev Q := Fin 3
abbrev MatQ := Matrix Q Q ℂ
abbrev MatJoint := Matrix (Q × Unit) (Q × Unit) ℂ
abbrev Hist := History 3 2
/-- Measurement rotation; this is not the physical preparation Hamiltonian. -/
def measurementE : Q → ℝ := ![0,1,0]
def C (φ : ℝ) (X : MatQ) : MatQ :=
  GibbsHamiltonianRelaxation.rotation measurementE (-φ) X
theorem C_entry (φ : ℝ) (X : MatQ) (i j : Q) :
    C φ X i j = Complex.exp (-Complex.I*φ*((measurementE i:ℂ)-measurementE j))*X i j := by
  rw [C, GibbsHamiltonianRelaxation.rotation_entry]
  congr 2
  push_cast
  ring
theorem C_mul (φ : ℝ) (X Y : MatQ) : C φ (X*Y)=C φ X*C φ Y :=
  FiniteGibbsClock.heisenberg_mul _ _ _ _ _
theorem C_add (φ : ℝ) (X Y : MatQ) : C φ (X+Y)=C φ X+C φ Y :=
  GibbsHamiltonianRelaxation.rotation_add _ _ _ _
theorem C_smul (φ : ℝ) (z : ℂ) (X : MatQ) : C φ (z • X)=z • C φ X :=
  GibbsHamiltonianRelaxation.rotation_smul _ _ _ _
theorem C_one (φ : ℝ) : C φ 1=1 := FiniteGibbsClock.heisenberg_one _ _ _
theorem C_trace (φ : ℝ) (X : MatQ) : (C φ X).trace=X.trace :=
  GibbsHamiltonianRelaxation.rotation_trace _ _ _
theorem C_adjoint (φ : ℝ) (X : MatQ) : (C φ X)ᴴ=C φ Xᴴ := by
  exact (FiniteGibbsClock.heisenberg_star
    (GibbsHamiltonianRelaxation.density_hermitian measurementE) 1 (-φ) X).symm
theorem C_inverse (φ : ℝ) (X : MatQ) : C φ (C (-φ) X)=X := by
  ext i j
  simp only [C_entry, Complex.ofReal_neg, ← mul_assoc, ← Complex.exp_add]
  rw [show -Complex.I*φ*((measurementE i:ℂ)-measurementE j) +
    -Complex.I*(-(φ:ℂ))*((measurementE i:ℂ)-measurementE j)=0 by ring]
  simp
theorem C_density (φ : ℝ) {X : MatQ} (hX : IsDensityOperator X) :
    IsDensityOperator (C φ X) := by
  have hV : GibbsHamiltonianRelaxation.unitary measurementE φ ∈ Matrix.unitaryGroup Q ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    change _ * (GibbsHamiltonianRelaxation.unitary measurementE φ)ᴴ=1
    rw [GibbsHamiltonianRelaxation.unitary_adjoint,
      GibbsHamiltonianRelaxation.unitary_cancel]
  rw [C, GibbsHamiltonianRelaxation.rotation_sandwich]
  exact conjugate_density hV hX

def baseProjection (a : Q) : MatQ := conjugate hadamard (projector a)
theorem base_zero : baseProjection 0=Pplus := rfl
theorem base_one : baseProjection 1=Pminus := rfl
theorem base_two : baseProjection 2=projector 2 := by
  ext i j
  rw [baseProjection, conjugate_projector_entry]
  fin_cases i <;> fin_cases j <;> simp [FiniteThreeLevelThermalPhase.hadamard, projector]
theorem base_density (a : Q) : IsDensityOperator (baseProjection a) :=
  conjugate_density hadamard_unitary (FiniteAdaptiveGibbsReadout.projector_density a)
theorem hadamard_conjugate_mul (X Y : MatQ) :
    conjugate FiniteThreeLevelThermalPhase.hadamard X *
      conjugate FiniteThreeLevelThermalPhase.hadamard Y =
    conjugate FiniteThreeLevelThermalPhase.hadamard (X*Y) := by
  simp only [conjugate, hadamard_adjoint]
  calc
    _ = FiniteThreeLevelThermalPhase.hadamard * X *
        (FiniteThreeLevelThermalPhase.hadamard * FiniteThreeLevelThermalPhase.hadamard) *
        Y * FiniteThreeLevelThermalPhase.hadamard := by noncomm_ring
    _ = _ := by rw [hadamard_square]; simp [mul_assoc]
theorem base_square (a : Q) : baseProjection a*baseProjection a=baseProjection a := by
  rw [baseProjection, hadamard_conjugate_mul, projector_square]
theorem base_orthogonal (a b : Q) (hab : a≠b) :
    baseProjection a*baseProjection b=0 := by
  have hp : projector a * projector b = 0 := by
    ext i j
    simp only [projector, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [baseProjection, baseProjection, hadamard_conjugate_mul, hp]
  simp [conjugate]
theorem base_sum : ∑ a, baseProjection a=1 := by
  simp only [baseProjection, conjugate, ← Matrix.mul_sum, ← Matrix.sum_mul]
  rw [projector_sum, Matrix.mul_one, hadamard_adjoint, hadamard_square]

def readProjection (φ : ℝ) (a : Q) : MatQ := C φ (baseProjection a)
theorem projection_density (φ : ℝ) (a : Q) : IsDensityOperator (readProjection φ a) :=
  C_density φ (base_density a)
theorem projection_hermitian (φ : ℝ) (a : Q) : (readProjection φ a).IsHermitian :=
  (projection_density φ a).1.isHermitian
theorem projection_square (φ : ℝ) (a : Q) :
    readProjection φ a*readProjection φ a=readProjection φ a := by
  rw [readProjection, ← C_mul, base_square]
theorem projection_orthogonal (φ : ℝ) (a b : Q) (hab : a≠b) :
    readProjection φ a*readProjection φ b=0 := by
  rw [readProjection, readProjection, ← C_mul, base_orthogonal a b hab]
  ext i j
  simp [C_entry]
theorem projection_sum (φ : ℝ) : ∑ a, readProjection φ a=1 := by
  have hb := base_sum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hb ⊢
  rw [readProjection, readProjection, readProjection, ← C_add, ← C_add, hb, C_one]
def readout (φ : ℝ) : FiniteInstrument Q 3 where
  count := 1
  operators a _ := readProjection φ a
  normalized := by
    simp only [Fin.sum_univ_one, (projection_hermitian φ _).eq, projection_square]
    exact projection_sum φ

theorem base_compression (a : Q) (X : MatQ) :
    baseProjection a*X*baseProjection a = (baseProjection a*X).trace • baseProjection a := by
  let H := FiniteThreeLevelThermalPhase.hadamard
  let Y := H*X*H
  have hc : projector a*Y*projector a=Y a a • projector a := by
    have h := instrument_branch a Y
    simpa [instrument, FiniteInstrument.branch, krausMap, projector_adjoint] using h
  have ht : (baseProjection a*X).trace=Y a a := by
    change (H*projector a*Hᴴ*X).trace=_
    rw [show Hᴴ=H from hadamard_adjoint]
    calc
      (H*projector a*H*X).trace = ((H*projector a)*(H*X)).trace := by rw [mul_assoc]
      _ = ((H*X)*(H*projector a)).trace := Matrix.trace_mul_comm _ _
      _ = (Y*projector a).trace := by congr 1; dsimp [Y]; noncomm_ring
      _ = Y a a := by simp [projector, Matrix.trace, Matrix.mul_diagonal]
  rw [ht]
  change (H*projector a*Hᴴ)*X*(H*projector a*Hᴴ)=_ • (H*projector a*Hᴴ)
  rw [show Hᴴ=H from hadamard_adjoint]
  calc
    _ = H*(projector a*Y*projector a)*H := by dsimp [Y]; noncomm_ring
    _ = _ := by rw [hc]; simp [mul_assoc]

theorem compression (φ : ℝ) (a : Q) (X : MatQ) :
    readProjection φ a*X*readProjection φ a =
      (readProjection φ a*X).trace • readProjection φ a := by
  have hi := C_inverse φ X
  conv_lhs => arg 1; arg 2; rw [← hi]
  rw [readProjection, ← C_mul, ← C_mul, base_compression, C_smul]
  congr 1
  rw [← C_trace φ (baseProjection a*C (-φ) X), C_mul, hi]

theorem readout_branch (φ : ℝ) (a : Q) (X : MatQ) :
    (readout φ).branch a X = (readProjection φ a*X).trace • readProjection φ a := by
  change (∑ _ : Fin 1, readProjection φ a*X*(readProjection φ a)ᴴ)=_
  rw [Fin.sum_univ_one, (projection_hermitian φ a).eq]
  exact compression φ a X

theorem projection_zero_entries (φ : ℝ) :
    readProjection φ 0 =
      !![1/2, Complex.exp (Complex.I*φ)/2, 0;
         Complex.exp (-Complex.I*φ)/2, 1/2, 0; 0,0,0] := by
  ext i j
  rw [readProjection, base_zero, Pplus_entries, C_entry]
  fin_cases i <;> fin_cases j <;> norm_num [measurementE] <;> ring

theorem projection_one_entries (φ : ℝ) :
    readProjection φ 1 =
      !![1/2, -Complex.exp (Complex.I*φ)/2, 0;
         -Complex.exp (-Complex.I*φ)/2, 1/2, 0; 0,0,0] := by
  ext i j
  rw [readProjection, base_one, Pminus_entries, C_entry]
  fin_cases i <;> fin_cases j <;> norm_num [measurementE] <;> ring

theorem projection_two (φ : ℝ) : readProjection φ 2=projector 2 := by
  rw [readProjection, base_two]
  exact GibbsHamiltonianRelaxation.rotation_diagonal _ _ _

def readVector (φ : ℝ) (a : Q) : Q → ℂ :=
  if a=0 then ![s,Complex.exp (-Complex.I*φ)*s,0]
  else if a=1 then ![s,-Complex.exp (-Complex.I*φ)*s,0]
  else ![0,0,1]

theorem phase_on_base (b ℏ t : ℝ) (a : Q) :
    phase b ℏ t (baseProjection a) = readProjection (theta b ℏ t) a := by
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl <;> simp only [base_zero, base_one, base_two,
    projection_zero_entries, projection_one_entries, projection_two]
  all_goals ext i j; rw [phase_entry]
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [Pplus_entries, Pminus_entries, projector, frequencies, energies]
  all_goals
    have he : Complex.I*(t:ℂ)*((delta:ℂ)/b/ℏ)=Complex.I*(theta b ℏ t:ℝ) := by
      simp only [theta, Complex.ofReal_div, Complex.ofReal_mul]
      ring
    rw [he]
    ring

def probability (q θ φ : ℝ) (B : Bool) (a : Q) : ℝ :=
  if a=0 then (5+q)/12 + (if B then -1 else 1)*q*Real.cos (θ-φ)/2
  else if a=1 then (5+q)/12 - (if B then -1 else 1)*q*Real.cos (θ-φ)/2
  else (1-q)/6

def preparation (r : ℝ) (B : Bool) : MatQ := if B then sigmaB r else sigmaA r

def evolved (b ℏ γ t r : ℝ) (B : Bool) : MatQ :=
  krausMap (channelKraus b ℏ γ t) (preparation r B)

theorem evolved_formula (b ℏ γ t r : ℝ) (hγ : 0≤γ) (ht : 0≤t) (B : Bool) :
    evolved b ℏ γ t r B = mixture (retention r γ t)
      (readProjection (theta b ℏ t) (if B then 1 else 0)) := by
  cases B
  · change krausMap _ (mixture r Pplus)=_
    rw [evolved_mixture b ℏ γ t r hγ ht Pplus_density]
    exact congrArg (mixture (retention r γ t)) (phase_on_base b ℏ t 0)
  · change krausMap _ (mixture r Pminus)=_
    rw [evolved_mixture b ℏ γ t r hγ ht Pminus_density]
    exact congrArg (mixture (retention r γ t)) (phase_on_base b ℏ t 1)

theorem exp_adjoint (φ : ℝ) : star (Complex.exp (-Complex.I*φ))=Complex.exp (Complex.I*φ) := by
  simp [← Complex.exp_conj]
theorem exp_cancel (φ : ℝ) : Complex.exp (-Complex.I*φ)*Complex.exp (Complex.I*φ)=1 := by
  rw [← Complex.exp_add]
  simp

theorem projection_rank_one (φ : ℝ) (a : Q) :
    readProjection φ a=Matrix.vecMulVec (readVector φ a) (star (readVector φ a)) := by
  have hs : s^2=(1/2:ℂ) := by simpa only [pow_two] using s_square
  have he : (starRingEnd ℂ) (Complex.exp (-Complex.I*φ))=Complex.exp (Complex.I*φ) :=
    exp_adjoint φ
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl <;>
    simp only [projection_zero_entries, projection_one_entries, projection_two]
  all_goals ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [readVector, Matrix.vecMulVec, s_conj, ← neg_mul, he, projector, Fin.ext_iff]
  all_goals ring_nf; simp only [hs] <;> ring_nf
  all_goals simp [← Complex.exp_add]

theorem exp_pos_angle (φ : ℝ) : Complex.exp (Complex.I*φ)=
    (Real.cos φ:ℂ)+(Real.sin φ:ℂ)*Complex.I := by
  rw [mul_comm, Complex.exp_mul_I]
  simp
theorem exp_neg_angle (φ : ℝ) : Complex.exp (-(Complex.I*φ))=
    (Real.cos φ:ℂ)-(Real.sin φ:ℂ)*Complex.I := by
  simpa [sub_eq_add_neg] using exp_pos_angle (-φ)

theorem trace_probability (q θ φ : ℝ) (B : Bool) (a : Q) :
    (readProjection φ a * mixture q (readProjection θ (if B then 1 else 0))).trace =
      (probability q θ φ B a:ℂ) := by
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl <;> cases B <;>
    simp only [Bool.false_eq_true, if_false, if_true,
      projection_zero_entries, projection_one_entries, projection_two]
  all_goals simp only [mixture, equilibrium, density, three, GibbsReset.threeWeights,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero]
  all_goals norm_num [projector, probability, Fin.ext_iff, Matrix.cons_val_two,
    exp_pos_angle, exp_neg_angle, Real.cos_sub]
  all_goals ring_nf <;> norm_num [Complex.I_sq]

theorem first_branch (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t) (B : Bool) (a : Q) :
    (readout φ).branch a (evolved b ℏ γ t r B) =
      (probability (retention r γ t) (theta b ℏ t) φ B a:ℂ) • readProjection φ a := by
  rw [readout_branch, evolved_formula b ℏ γ t r hγ ht, trace_probability]

def diagonalReadout (a j : Q) : ℝ :=
  if a=2 then (if j=2 then 1 else 0) else (if j=2 then 0 else 1/2)
theorem projection_diagonal (φ : ℝ) (a j : Q) :
    readProjection φ a j j = (diagonalReadout a j:ℂ) := by
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl
  all_goals simp only [projection_zero_entries, projection_one_entries, projection_two]
  all_goals fin_cases j <;> norm_num [diagonalReadout, projector, Fin.ext_iff]

def tailRetention : ℝ := Real.exp (-2)
def continuation (a j : Q) : ℝ :=
  tailRetention*diagonalReadout a j + (1-tailRetention)*three.w j

def tree (φ : ℝ) : Tree Q Unit 3 2 :=
  .node (localStep Q Unit 3 (readout φ))
    (fun _ ↦ tailTree three 1 (fun _ ↦ 2) (fun _ ↦ by norm_num))
def family (b ℏ γ t r φ : ℝ) (B : Bool) (h : Hist) : MatJoint :=
  run Q Unit 3 (tree φ) h (joint (evolved b ℏ γ t r B))

theorem local_branch (φ : ℝ) (a : Q) (X : MatQ) :
    (localStep Q Unit 3 (readout φ)).branch Q Unit 3 a (joint X)=
      joint ((readout φ).branch a X) := by
  rw [localStep_branch]
  exact joint_kraus _ _

theorem tail_branch (φ : ℝ) (a j : Q) (z : ℂ) :
    (step three.w three.positive three.normalized 1 2 (by norm_num) (by norm_num)).branch
      Q Unit 3 j (joint (z • readProjection φ a)) =
      (z*(continuation a j:ℂ)) • joint (projector j) := by
  rw [step_branch, GibbsReset.time_state _ (fun i ↦ (three.positive i).le) _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one 1 2 (by norm_num) (by norm_num)),
    instrument_branch]
  rw [Matrix.trace_smul, (projection_density φ a).2, smul_eq_mul, mul_one]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, projection_diagonal]
  simp only [density, Matrix.diagonal_apply_eq, joint, Matrix.smul_kronecker]
  congr 1
  simp only [continuation, tailRetention, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one]
  norm_num
  ring

theorem all_nine_branches (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    (B : Bool) (a j : Q) :
    family b ℏ γ t r φ B (a,j,()) =
      ((probability (retention r γ t) (theta b ℏ t) φ B a * continuation a j:ℝ):ℂ) •
        joint (projector j) := by
  change (step three.w three.positive three.normalized 1 2 _ _).branch Q Unit 3 j
    ((localStep Q Unit 3 (readout φ)).branch Q Unit 3 a (joint (evolved b ℏ γ t r B)))=_
  rw [local_branch, first_branch b ℏ γ t r φ hγ ht, tail_branch, ← Complex.ofReal_mul]

theorem continuation_rows :
    continuation 0 = ![1/2,(2+tailRetention)/6,(1-tailRetention)/6] ∧
    continuation 1 = ![1/2,(2+tailRetention)/6,(1-tailRetention)/6] ∧
    continuation 2 = ![(1-tailRetention)/2,(1-tailRetention)/3,(1+5*tailRetention)/6] := by
  constructor
  · ext j; fin_cases j <;>
      norm_num [continuation, diagonalReadout, three, GibbsReset.threeWeights, Fin.ext_iff] <;> ring
  constructor
  · ext j; fin_cases j <;>
      norm_num [continuation, diagonalReadout, three, GibbsReset.threeWeights, Fin.ext_iff] <;> ring
  · ext j; fin_cases j <;>
      norm_num [continuation, diagonalReadout, three, GibbsReset.threeWeights, Fin.ext_iff] <;> ring

theorem continuation_nonneg (a j : Q) : 0≤continuation a j := by
  have hd : 0≤tailRetention := (Real.exp_pos _).le
  have hd1 : tailRetention≤1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hz : 0≤diagonalReadout a j := by unfold diagonalReadout; split_ifs <;> norm_num
  exact add_nonneg (mul_nonneg hd hz) (mul_nonneg (sub_nonneg.mpr hd1) (three.positive j).le)
theorem continuation_sum (a : Q) : ∑ j, continuation a j=1 := by
  have ha : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl
  all_goals simp only [continuation_rows.1, continuation_rows.2.1, continuation_rows.2.2]
  all_goals norm_num [Fin.sum_univ_succ, Matrix.cons_val_two]; ring

theorem probability_sum (q θ φ : ℝ) (B : Bool) : ∑ a, probability q θ φ B a=1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change probability q θ φ B 0+(probability q θ φ B 1+probability q θ φ B 2)=1
  cases B <;> norm_num [probability, Fin.ext_iff] <;> ring

theorem probability_nonneg {q : ℝ} (hq : 0≤q) (hq1 : q≤1) (θ φ : ℝ) (B : Bool) (a : Q) :
    0≤probability q θ φ B a := by
  have hp := (readout φ).weight_nonneg a
    (mixture_density hq hq1 (projection_density θ (if B then 1 else 0))).1
  simpa only [FiniteInstrument.weight, readout_branch, trace_probability, Matrix.trace_smul,
    (projection_density φ a).2, smul_eq_mul, mul_one, Complex.ofReal_re] using hp

theorem evolved_density (b ℏ γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) (B : Bool) :
    IsDensityOperator (evolved b ℏ γ t r B) := by
  cases B
  · exact evolvedA_density b ℏ γ t hγ ht hr hr1
  · exact evolvedB_density b ℏ γ t hγ ht hr hr1

theorem family_valid (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) (B : Bool) :
    IsBranchFamily (family b ℏ γ t r φ B) :=
  run_family _ (joint_density (evolved_density b ℏ γ t hγ ht hr hr1 B))

theorem family_trace (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t) (B : Bool) (h : Hist) :
    (family b ℏ γ t r φ B h).trace =
      (probability (retention r γ t) (theta b ℏ t) φ B h.1*continuation h.1 h.2.1:ℝ) := by
  rcases h with ⟨a,j,⟨⟩⟩
  rw [all_nine_branches b ℏ γ t r φ hγ ht, Matrix.trace_smul, joint_trace, projector_trace]
  simp

theorem first_marginal (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t) (B : Bool) (a : Q) :
    (∑ j, (family b ℏ γ t r φ B (a,j,())).trace.re)=
      probability (retention r γ t) (theta b ℏ t) φ B a := by
  simp only [family_trace b ℏ γ t r φ hγ ht, Complex.ofReal_re]
  rw [← Finset.mul_sum, continuation_sum, mul_one]

theorem third_mass (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t) (B : Bool) :
    (∑ j, (family b ℏ γ t r φ B (2,j,())).trace.re)=(1-retention r γ t)/6 := by
  rw [first_marginal b ℏ γ t r φ hγ ht]
  norm_num [probability, Fin.ext_iff]
theorem third_mass_positive (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r<1) (B : Bool) :
    0 < ∑ j, (family b ℏ γ t r φ B (2,j,())).trace.re := by
  rw [third_mass b ℏ γ t r φ hγ ht]
  exact div_pos (sub_pos.mpr (retention_lt_one hr hr1 hγ ht)) (by norm_num)

theorem probability_difference (q θ φ : ℝ) (a : Q) :
    probability q θ φ false a-probability q θ φ true a =
      if a=0 then q*Real.cos (θ-φ) else if a=1 then -(q*Real.cos (θ-φ)) else 0 := by
  simp only [probability, Bool.false_eq_true, if_false, if_true]
  split_ifs <;> ring

theorem sum_abs_difference {q : ℝ} (hq : 0≤q) (θ φ : ℝ) :
    (∑ a, |probability q θ φ false a-probability q θ φ true a|)=2*q*|Real.cos (θ-φ)| := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change |probability q θ φ false 0-probability q θ φ true 0|+
    (|probability q θ φ false 1-probability q θ φ true 1|+
    |probability q θ φ false 2-probability q θ φ true 2|)=_
  norm_num [probability_difference, Fin.ext_iff, abs_mul, abs_of_nonneg hq]
  ring

theorem support_norm (j : Q) : traceNorm (joint (projector j))=1 := by
  have hd := joint_density (FiniteAdaptiveGibbsReadout.projector_density j)
  rw [traceNorm_eq_physlib]
  have h := hd.1.traceNorm_eq_trace
  rw [hd.2] at h
  exact_mod_cast congrArg Complex.re h

theorem branch_distance (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t) (a j : Q) :
    traceDist (family b ℏ γ t r φ false (a,j,())) (family b ℏ γ t r φ true (a,j,())) =
      |probability (retention r γ t) (theta b ℏ t) φ false a-
        probability (retention r γ t) (theta b ℏ t) φ true a| * continuation a j / 2 := by
  rw [all_nine_branches b ℏ γ t r φ hγ ht, all_nine_branches b ℏ γ t r φ hγ ht]
  unfold traceDist
  rw [← sub_smul, ← Complex.ofReal_sub, traceNorm_eq_physlib, Matrix.traceNorm_smul, ← traceNorm_eq_physlib,
    support_norm, Complex.norm_real]
  rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (continuation_nonneg a j)]
  ring

theorem branch_distance_history (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t) (h : Hist) :
    traceDist (family b ℏ γ t r φ false h) (family b ℏ γ t r φ true h) =
      |probability (retention r γ t) (theta b ℏ t) φ false h.1-
        probability (retention r γ t) (theta b ℏ t) φ true h.1| * continuation h.1 h.2.1 / 2 := by
  rcases h with ⟨a,j,⟨⟩⟩
  exact branch_distance b ℏ γ t r φ hγ ht a j

theorem observed_distance (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) :
    branchDistance (family b ℏ γ t r φ false) (family b ℏ γ t r φ true)=
      retention r γ t*|Real.cos (theta b ℏ t-φ)| := by
  unfold branchDistance
  simp only [branch_distance_history b ℏ γ t r φ hγ ht]
  change (∑ h : Fin 3 × Fin 3 × Unit,
    |probability (retention r γ t) (theta b ℏ t) φ false h.1-
      probability (retention r γ t) (theta b ℏ t) φ true h.1| * continuation h.1 h.2.1/2)=_
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  simp_rw [← Finset.sum_div, ← Finset.mul_sum, continuation_sum, mul_one]
  rw [sum_abs_difference (retention_nonneg hr γ t)]
  ring

theorem observed_variation (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) :
    familyHistoryVariation (family b ℏ γ t r φ false) (family b ℏ γ t r φ true)=
      retention r γ t*|Real.cos (theta b ℏ t-φ)| := by
  unfold familyHistoryVariation
  simp only [family_trace b ℏ γ t r φ hγ ht, Complex.ofReal_re, ← sub_mul, abs_mul,
    abs_of_nonneg (continuation_nonneg _ _)]
  change (∑ h : Fin 3 × Fin 3 × Unit,
    |probability (retention r γ t) (theta b ℏ t) φ false h.1-
      probability (retention r γ t) (theta b ℏ t) φ true h.1| * continuation h.1 h.2.1)/2=_
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  simp_rw [← Finset.mul_sum, continuation_sum, mul_one]
  rw [sum_abs_difference (retention_nonneg hr γ t)]
  ring


/-- Decision zero means choose A; the third first-label is always assigned tie score zero. -/
def decisionScore (rev : Bool) (h : Hist) : ℝ := if h.1=(if rev then 1 else 0) then 1 else 0
def decisionProjection (rev : Bool) (h : Hist) : MatJoint :=
  if h.1=(if rev then 1 else 0) then 1 else 0
theorem decisionProjection_hermitian (rev : Bool) (h : Hist) :
    (decisionProjection rev h).IsHermitian := by
  unfold decisionProjection; split_ifs <;> simp
theorem decisionProjection_idem (rev : Bool) (h : Hist) :
    decisionProjection rev h*decisionProjection rev h=decisionProjection rev h := by
  unfold decisionProjection; split_ifs <;> simp
def decisionReadout (rev : Bool) (h : Hist) : FiniteInstrument (Q×Unit) 2 :=
  projectiveReadout (decisionProjection rev h)
    (decisionProjection_hermitian rev h) (decisionProjection_idem rev h)
theorem decisionProjection_admissible (rev : Bool) (h : Hist) :
    IsBinaryPOVM (decisionProjection rev h) :=
  isBinaryPOVM_of_projection (decisionProjection_hermitian rev h) (decisionProjection_idem rev h)
theorem decisionScore_admissible (rev : Bool) (h : Hist) :
    decisionScore rev h ∈ Set.Icc (0:ℝ) 1 := by
  unfold decisionScore; split_ifs <;> norm_num
theorem decision_third_tie (rev : Bool) (j : Q) : decisionScore rev (2,j,())=0 := by
  cases rev <;> norm_num [decisionScore, Fin.ext_iff]
theorem decisionReadout_weight (rev : Bool) (h : Hist) (a : Fin 2) (Z : MatJoint) :
    (decisionReadout rev h).weight a Z =
      (if a=0 then decisionScore rev h else 1-decisionScore rev h)*Z.trace.re := by
  have ha : a=0 ∨ a=1 := by fin_cases a <;> decide
  rcases ha with rfl | rfl
  all_goals simp only [decisionReadout, projectiveReadout_weight_zero, projectiveReadout_weight_one]
  all_goals unfold decisionProjection decisionScore
  all_goals split_ifs <;> simp_all
/-- All eighteen physical history/decision probabilities, including every zero. -/
theorem all_eighteen_entries (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    (B rev : Bool) (h : Hist) (a : Fin 2) :
    readoutTable (decisionReadout rev) (family b ℏ γ t r φ B) h a =
      (if a=0 then decisionScore rev h else 1-decisionScore rev h)*
      (probability (retention r γ t) (theta b ℏ t) φ B h.1*continuation h.1 h.2.1) := by
  rw [readoutTable, decisionReadout_weight, family_trace b ℏ γ t r φ hγ ht, Complex.ofReal_re]
theorem decision_laws (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) (B rev : Bool) :
    (∀ h a, 0≤readoutTable (decisionReadout rev) (family b ℏ γ t r φ B) h a) ∧
    (∑ h, ∑ a, readoutTable (decisionReadout rev) (family b ℏ γ t r φ B) h a)=1 :=
  ⟨readoutTable_nonneg _ (family_valid b ℏ γ t φ hγ ht hr hr1 B),
    readoutTable_total _ (family_valid b ℏ γ t φ hγ ht hr hr1 B)⟩
theorem decisionScore_attains (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) (rev : Bool) :
    historyError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true) (decisionScore rev)=
      if rev then (1+retention r γ t*Real.cos (theta b ℏ t-φ))/2
      else (1-retention r γ t*Real.cos (theta b ℏ t-φ))/2 := by
  rw [historyError_eq (family_valid b ℏ γ t φ hγ ht hr hr1 false)]
  simp only [family_trace b ℏ γ t r φ hγ ht, Complex.ofReal_re, ← sub_mul, decisionScore]
  change (1-(∑ h : Fin 3 × Fin 3 × Unit, (if h.1=(if rev then 1 else 0) then 1 else 0)*
    ((probability (retention r γ t) (theta b ℏ t) φ false h.1-
      probability (retention r γ t) (theta b ℏ t) φ true h.1)*continuation h.1 h.2.1)))/2=_
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  change (1 - ∑ a : Q, ∑ j : Q, (if a=(if rev then 1 else 0) then (1:ℝ) else 0) *
    ((probability (retention r γ t) (theta b ℏ t) φ false a-
      probability (retention r γ t) (theta b ℏ t) φ true a)*continuation a j))/2=_
  simp_rw [← Finset.mul_sum, continuation_sum, mul_one, probability_difference]
  cases rev <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  all_goals norm_num [Fin.ext_iff]
theorem decision_effect_realizes (b ℏ γ t r φ : ℝ) (rev : Bool) :
    readoutError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true) (decisionProjection rev)=
    instrumentError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true) (decisionReadout rev) := by
  simp only [readoutError, instrumentError, readoutTable, decisionReadout,
    projectiveReadout_weight_zero, projectiveReadout_weight_one]
theorem decision_score_effect (rev : Bool) :
    (fun h => (decisionScore rev h:ℂ) • (1:MatJoint))=decisionProjection rev := by
  funext h; unfold decisionScore decisionProjection; split_ifs <;> simp
theorem decision_attains (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) (rev : Bool) :
    instrumentError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true) (decisionReadout rev)=
      if rev then (1+retention r γ t*Real.cos (theta b ℏ t-φ))/2
      else (1-retention r γ t*Real.cos (theta b ℏ t-φ))/2 := by
  rw [← decision_effect_realizes, ← decision_score_effect, historyError_scalar_effect]
  exact decisionScore_attains b ℏ γ t φ hγ ht hr hr1 rev
def optimalReversal (θ φ : ℝ) : Bool := decide (Real.cos (θ-φ)<0)
theorem optimal_attains (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    instrumentError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true)
      (decisionReadout (optimalReversal (theta b ℏ t) φ))=
      (1-retention r γ t*|Real.cos (theta b ℏ t-φ)|)/2 := by
  rw [decision_attains b ℏ γ t φ hγ ht hr hr1]
  by_cases hc : Real.cos (theta b ℏ t-φ)<0
  · simp [optimalReversal, hc, abs_of_neg hc]
  · simp [optimalReversal, hc, abs_of_nonneg (le_of_not_gt hc)]
theorem optimalScore_attains (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    historyError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true)
      (decisionScore (optimalReversal (theta b ℏ t) φ))=
      (1-retention r γ t*|Real.cos (theta b ℏ t-φ)|)/2 := by
  rw [← historyError_scalar_effect, decision_score_effect, decision_effect_realizes]
  exact optimal_attains b ℏ γ t φ hγ ht hr hr1
theorem all_effect_isLeast (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    IsLeast {x : ℝ | ∃ E : Hist → MatJoint, (∀ h, IsBinaryPOVM (E h)) ∧
      readoutError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true) E=x}
      ((1-retention r γ t*|Real.cos (theta b ℏ t-φ)|)/2) := by
  simpa only [observed_distance b ℏ γ t φ hγ ht hr] using
    readoutError_isLeast (family_valid b ℏ γ t φ hγ ht hr hr1 false)
      (family_valid b ℏ γ t φ hγ ht hr hr1 true)
theorem randomized_isLeast (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    IsLeast {x : ℝ | ∃ s : Hist → ℝ, (∀ h, s h∈Set.Icc (0:ℝ) 1) ∧
      historyError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true) s=x}
      ((1-retention r γ t*|Real.cos (theta b ℏ t-φ)|)/2) := by
  simpa only [observed_variation b ℏ γ t φ hγ ht hr] using
    historyError_isLeast (family_valid b ℏ γ t φ hγ ht hr hr1 false)
      (family_valid b ℏ γ t φ hγ ht hr hr1 true)


/-- The induced effect of an arbitrary normalized binary Kraus instrument. -/
def inducedEffect (I : FiniteInstrument (Q×Unit) 2) (a : Fin 2) : MatJoint :=
  ∑ k, (I.operators a k)ᴴ*I.operators a k
theorem inducedEffect_positive (I : FiniteInstrument (Q×Unit) 2) (a : Fin 2) :
    (inducedEffect I a).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro k _
  exact Matrix.posSemidef_conjTranspose_mul_self _
theorem inducedEffect_complement (I : FiniteInstrument (Q×Unit) 2) :
    1-inducedEffect I 0=inducedEffect I 1 := by
  have hn := I.normalized
  change (∑ a, inducedEffect I a)=1 at hn
  rw [Fin.sum_univ_two] at hn
  rw [← hn]; abel
theorem inducedEffect_admissible (I : FiniteInstrument (Q×Unit) 2) :
    IsBinaryPOVM (inducedEffect I 0) := by
  exact ⟨inducedEffect_positive I 0, by rw [inducedEffect_complement]; exact inducedEffect_positive I 1⟩
theorem inducedEffect_weight (I : FiniteInstrument (Q×Unit) 2) (a : Fin 2) (Z : MatJoint) :
    I.weight a Z=(inducedEffect I a*Z).trace.re := by
  simp only [FiniteInstrument.weight, FiniteInstrument.branch, krausMap, inducedEffect,
    Finset.sum_mul, Matrix.trace_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact Matrix.trace_mul_cycle _ _ _
theorem arbitrary_instrument_effect (A B : Hist → MatJoint)
    (I : Hist → FiniteInstrument (Q×Unit) 2) :
    instrumentError A B I=readoutError A B (fun h => inducedEffect (I h) 0) := by
  simp only [instrumentError, readoutTable, inducedEffect_weight, readoutError,
    inducedEffect_complement]
theorem physical_isLeast (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    IsLeast {x : ℝ | ∃ I : Hist → FiniteInstrument (Q×Unit) 2,
      instrumentError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true) I=x}
      ((1-retention r γ t*|Real.cos (theta b ℏ t-φ)|)/2) := by
  refine ⟨⟨decisionReadout (optimalReversal (theta b ℏ t) φ),
    optimal_attains b ℏ γ t φ hγ ht hr hr1⟩, ?_⟩
  rintro x ⟨I,rfl⟩
  rw [arbitrary_instrument_effect]
  exact (all_effect_isLeast b ℏ γ t φ hγ ht hr hr1).2
    ⟨_, fun h => inducedEffect_admissible (I h), rfl⟩

theorem tree_output_distance (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) :
    outputDistance Q Unit 3 (tree φ) (tree φ)
      (joint (evolved b ℏ γ t r false)) (joint (evolved b ℏ γ t r true))=
      retention r γ t*|Real.cos (theta b ℏ t-φ)| := by
  rw [← tree_branchDistance]
  exact observed_distance b ℏ γ t φ hγ ht hr

theorem premeasurement_distance (b ℏ γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) :
    traceDist (joint (evolved b ℏ γ t r false)) (joint (evolved b ℏ γ t r true))=
      retention r γ t := evolved_joint_distance b ℏ γ t hγ ht hr

theorem covariant_attains (b ℏ γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    instrumentError (family b ℏ γ t r (theta b ℏ t) false)
      (family b ℏ γ t r (theta b ℏ t) true) (decisionReadout false)=(1-retention r γ t)/2 := by
  simpa only [Bool.false_eq_true, if_false, sub_self, Real.cos_zero, mul_one] using
    decision_attains b ℏ γ t (theta b ℏ t) hγ ht hr hr1 false

theorem old_computational_branches (b ℏ γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    (r : ℝ) (R : Data 3) (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) :
    (fun h => run Q Unit 3 (historyTree R n s hs) h (joint (evolved b ℏ γ t r false)))=
    (fun h => run Q Unit 3 (historyTree R n s hs) h (joint (evolved b ℏ γ t r true))) := by
  funext h; exact old_history_evolved_pair b ℏ γ t hγ ht r R n s hs h

theorem old_computational_distance (b ℏ γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    (r : ℝ) (R : Data 3) (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) :
    outputDistance Q Unit 3 (historyTree R n s hs) (historyTree R n s hs)
      (joint (evolved b ℏ γ t r false)) (joint (evolved b ℏ γ t r true))=0 := by
  rw [← tree_branchDistance, old_computational_branches b ℏ γ t hγ ht]
  exact branchDistance_self _


theorem continuation_first_equal : continuation 0=continuation 1 := by
  rw [continuation_rows.1, continuation_rows.2.1]
theorem sum_first_difference (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t) (j : Q) :
    (∑ a : Q, (family b ℏ γ t r φ false (a,j,())-family b ℏ γ t r φ true (a,j,())))=0 := by
  simp_rw [all_nine_branches b ℏ γ t r φ hγ ht, ← sub_smul, ← Complex.ofReal_sub,
    ← sub_mul, probability_difference]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [Fin.ext_iff, ← continuation_first_equal]

theorem terminal_equal (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t) :
    terminalState Q Unit 3 (tree φ) (joint (evolved b ℏ γ t r false))=
    terminalState Q Unit 3 (tree φ) (joint (evolved b ℏ γ t r true)) := by
  change (∑ h : Hist, family b ℏ γ t r φ false h)=(∑ h : Hist, family b ℏ γ t r φ true h)
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  change (∑ h : Q×Q×Unit, (family b ℏ γ t r φ false (h.1,h.2.1,())-
    family b ℏ γ t r φ true (h.1,h.2.1,())))=0
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  rw [Finset.sum_comm]
  simp only [sum_first_difference b ℏ γ t r φ hγ ht, Finset.sum_const_zero]
theorem terminal_distance_zero (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t) :
    traceDist (terminalState Q Unit 3 (tree φ) (joint (evolved b ℏ γ t r false)))
      (terminalState Q Unit 3 (tree φ) (joint (evolved b ℏ γ t r true)))=0 := by
  rw [terminal_equal b ℏ γ t r φ hγ ht]
  simp [traceDist, traceNorm_zero]

def preProjection (θ : ℝ) : MatJoint := joint (readProjection θ 0)
theorem preProjection_hermitian (θ : ℝ) : (preProjection θ).IsHermitian := by
  exact (joint_density (projection_density θ 0)).1.isHermitian
theorem preProjection_square (θ : ℝ) : preProjection θ*preProjection θ=preProjection θ := by
  simp only [preProjection, joint, ← Matrix.mul_kronecker_mul, Matrix.one_mul, projection_square]
theorem preProjection_admissible (θ : ℝ) : IsBinaryPOVM (preProjection θ) :=
  isBinaryPOVM_of_projection (preProjection_hermitian θ) (preProjection_square θ)
def preReadout (θ : ℝ) : FiniteInstrument (Q×Unit) 2 :=
  projectiveReadout (preProjection θ) (preProjection_hermitian θ) (preProjection_square θ)
theorem preProjection_weight (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t) (B : Bool) :
    (preProjection φ*joint (evolved b ℏ γ t r B)).trace.re=
      probability (retention r γ t) (theta b ℏ t) φ B 0 := by
  simp only [preProjection, joint, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  change (joint (readProjection φ 0*evolved b ℏ γ t r B)).trace.re=_
  rw [joint_trace, evolved_formula b ℏ γ t r hγ ht, trace_probability, Complex.ofReal_re]
theorem pre_effect_attains (b ℏ γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    povmAvgError (joint (evolved b ℏ γ t r false)) (joint (evolved b ℏ γ t r true))
      (preProjection (theta b ℏ t))=(1-retention r γ t)/2 := by
  unfold povmAvgError
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    (joint_density (evolved_density b ℏ γ t hγ ht hr hr1 false)).2]
  simp only [preProjection_weight b ℏ γ t r _ hγ ht]
  norm_num [probability, Fin.ext_iff]
  ring
theorem pre_physical_attains (b ℏ γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    ((preReadout (theta b ℏ t)).weight 0 (joint (evolved b ℏ γ t r true))+
      (preReadout (theta b ℏ t)).weight 1 (joint (evolved b ℏ γ t r false)))/2=
      (1-retention r γ t)/2 := by
  simp only [preReadout, projectiveReadout_weight_zero, projectiveReadout_weight_one]
  exact pre_effect_attains b ℏ γ t hγ ht hr hr1
theorem pre_isLeast (b ℏ γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    IsLeast {x : ℝ | ∃ E : MatJoint, IsBinaryPOVM E ∧
      povmAvgError (joint (evolved b ℏ γ t r false)) (joint (evolved b ℏ γ t r true)) E=x}
      ((1-retention r γ t)/2) := by
  simpa only [premeasurement_distance b ℏ γ t hγ ht hr] using
    helstrom_isLeast_povmAvgError
      (joint_density (evolved_density b ℏ γ t hγ ht hr hr1 false))
      (joint_density (evolved_density b ℏ γ t hγ ht hr hr1 true))

/-- Equality at a measurement tie concerns complete branch matrices. -/
theorem family_tie (b ℏ γ t r φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    (hc : retention r γ t*Real.cos (theta b ℏ t-φ)=0) :
    family b ℏ γ t r φ false=family b ℏ γ t r φ true := by
  funext h
  rcases h with ⟨a,j,⟨⟩⟩
  rw [all_nine_branches b ℏ γ t r φ hγ ht, all_nine_branches b ℏ γ t r φ hγ ht]
  have hp : probability (retention r γ t) (theta b ℏ t) φ false a=
    probability (retention r γ t) (theta b ℏ t) φ true a := by
    apply sub_eq_zero.mp
    rw [probability_difference, hc]
    split_ifs <;> simp
  rw [hp]
theorem tie_every_effect (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1)
    (hc : retention r γ t*Real.cos (theta b ℏ t-φ)=0) (E : Hist → MatJoint) :
    readoutError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true) E=1/2 := by
  rw [← family_tie b ℏ γ t r φ hγ ht hc]
  rw [readoutError_eq _ _ _ (family_valid b ℏ γ t φ hγ ht hr hr1 false).2]
  simp
theorem tie_every_instrument (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1)
    (hc : retention r γ t*Real.cos (theta b ℏ t-φ)=0)
    (I : Hist → FiniteInstrument (Q×Unit) 2) :
    instrumentError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true) I=1/2 := by
  rw [arbitrary_instrument_effect]
  exact tie_every_effect b ℏ γ t φ hγ ht hr hr1 hc _
theorem tie_every_randomized (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1)
    (hc : retention r γ t*Real.cos (theta b ℏ t-φ)=0) (s : Hist → ℝ) :
    historyError (family b ℏ γ t r φ false) (family b ℏ γ t r φ true) s=1/2 := by
  rw [← historyError_scalar_effect]
  exact tie_every_effect b ℏ γ t φ hγ ht hr hr1 hc _


/-- One fixed preparation rate and one fixed nonzero Hamiltonian for all three times. -/
def tStar : ℝ := Real.pi/(2*delta)
def witnessRate : ℝ := 2*delta*Real.log 2/Real.pi
def witnessTime : Q → ℝ := ![0,tStar,2*tStar]
def witnessQ : Q → ℝ := ![1/2,1/4,1/8]
def witnessAngle : Q → ℝ := ![0,Real.pi/2,Real.pi]
theorem tStar_pos : 0<tStar := div_pos Real.pi_pos (mul_pos (by norm_num) delta_pos)
theorem witnessRate_pos : 0<witnessRate :=
  div_pos (mul_pos (mul_pos (by norm_num) delta_pos) (Real.log_pos (by norm_num))) Real.pi_pos
theorem witnessTime_nonneg (k : Q) : 0≤witnessTime k := by
  fin_cases k <;> simp [witnessTime, Matrix.cons_val_two, tStar_pos.le]
theorem witness_rate_time : witnessRate*tStar=Real.log 2 := by
  unfold witnessRate tStar
  field_simp [ne_of_gt delta_pos, ne_of_gt Real.pi_pos]
theorem witness_retention : ∀ k : Q, retention (1/2) witnessRate (witnessTime k)=witnessQ k := by
  have he : Real.exp (-(Real.log 2))=(1/2:ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  intro k
  have hk : k=0 ∨ k=1 ∨ k=2 := by fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl
  · norm_num [witnessTime,witnessQ,retention]
  · change (1/2:ℝ)*Real.exp (-witnessRate*tStar)=1/4
    rw [neg_mul, witness_rate_time, he]; norm_num
  · change (1/2:ℝ)*Real.exp (-witnessRate*(2*tStar))=1/8
    rw [show -witnessRate*(2*tStar)=-(Real.log 2)+(-(Real.log 2)) by
      nlinarith [witness_rate_time], Real.exp_add, he]
    norm_num
theorem witness_theta : ∀ k : Q, theta 1 1 (witnessTime k)=witnessAngle k := by
  intro k
  have hk : k=0 ∨ k=1 ∨ k=2 := by fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl
  · norm_num [witnessTime,witnessAngle,theta]
  · change tStar*delta/(1*1)=Real.pi/2
    unfold tStar; field_simp [ne_of_gt delta_pos]
  · change (2*tStar)*delta/(1*1)=Real.pi
    unfold tStar; field_simp [ne_of_gt delta_pos]
theorem witness_nonzero : thermalH 1≠0 := thermalH_ne_zero (by norm_num)
theorem witness_nonscalar (z : ℂ) : thermalH 1≠z • 1 := thermalH_not_scalar (by norm_num) z
theorem witness_hamiltonian : scaledH 1 1=thermalH 1 := by simp [scaledH_smul]
theorem witness_generator (X : MatQ) :
    lindbladGenerator (scaledH 1 1) (jumps witnessRate) X=
      -Complex.I • (scaledH 1 1*X-X*scaledH 1 1)+
        (witnessRate:ℂ) • (X.trace • equilibrium-X) :=
  actual_generator 1 1 witnessRate witnessRate_pos.le X
theorem witness_propagator (k : Q) (X : MatQ) :
    krausMap (channelKraus 1 1 witnessRate (witnessTime k)) X=
      lindbladPropagatorAction (scaledH 1 1) (jumps witnessRate) (witnessTime k) X :=
  channel_propagator 1 1 witnessRate (witnessTime k) witnessRate_pos.le (witnessTime_nonneg k) X

def fixedRows (B : Bool) (k : Q) : Q → ℝ :=
  if B then (!![5/24,17/24,1/12; 7/16,7/16,1/8; 47/96,35/96,7/48]) k
  else (!![17/24,5/24,1/12; 7/16,7/16,1/8; 35/96,47/96,7/48]) k
def covariantRows (B : Bool) (k : Q) : Q → ℝ :=
  if B then (!![5/24,17/24,1/12; 5/16,9/16,1/8; 35/96,47/96,7/48]) k
  else (!![17/24,5/24,1/12; 9/16,5/16,1/8; 47/96,35/96,7/48]) k
theorem fixed_probability (B : Bool) (k a : Q) :
    probability (witnessQ k) (witnessAngle k) 0 B a=fixedRows B k a := by
  cases B <;> fin_cases k <;> fin_cases a <;>
    norm_num [probability,witnessQ,witnessAngle,fixedRows,Fin.ext_iff,Matrix.cons_val_two]
theorem covariant_probability (B : Bool) (k a : Q) :
    probability (witnessQ k) (witnessAngle k) (witnessAngle k) B a=covariantRows B k a := by
  cases B <;> fin_cases k <;> fin_cases a <;>
    norm_num [probability,witnessQ,witnessAngle,covariantRows,Fin.ext_iff,Matrix.cons_val_two]
/-- These rational rows are derived from actual channel and instrument branches. -/
theorem fixed_first_marginals (B : Bool) (k a : Q) :
    (∑ j, (family 1 1 witnessRate (witnessTime k) (1/2) 0 B (a,j,())).trace.re)=fixedRows B k a := by
  rw [first_marginal 1 1 witnessRate _ _ _ witnessRate_pos.le (witnessTime_nonneg k),
    witness_retention, witness_theta, fixed_probability]
theorem covariant_first_marginals (B : Bool) (k a : Q) :
    (∑ j, (family 1 1 witnessRate (witnessTime k) (1/2) (witnessAngle k) B (a,j,())).trace.re)=
      covariantRows B k a := by
  rw [first_marginal 1 1 witnessRate _ _ _ witnessRate_pos.le (witnessTime_nonneg k),
    witness_retention, witness_theta, covariant_probability]
theorem fixed_nine_branches (B : Bool) (k a j : Q) :
    family 1 1 witnessRate (witnessTime k) (1/2) 0 B (a,j,())=
      ((fixedRows B k a*continuation a j:ℝ):ℂ) • joint (projector j) := by
  rw [all_nine_branches 1 1 witnessRate _ _ _ witnessRate_pos.le (witnessTime_nonneg k),
    witness_retention, witness_theta, fixed_probability]
theorem covariant_nine_branches (B : Bool) (k a j : Q) :
    family 1 1 witnessRate (witnessTime k) (1/2) (witnessAngle k) B (a,j,())=
      ((covariantRows B k a*continuation a j:ℝ):ℂ) • joint (projector j) := by
  rw [all_nine_branches 1 1 witnessRate _ _ _ witnessRate_pos.le (witnessTime_nonneg k),
    witness_retention, witness_theta, covariant_probability]
theorem fixed_eighteen_entries (B rev : Bool) (k : Q) (h : Hist) (a : Fin 2) :
    readoutTable (decisionReadout rev) (family 1 1 witnessRate (witnessTime k) (1/2) 0 B) h a=
      (if a=0 then decisionScore rev h else 1-decisionScore rev h)*
        (fixedRows B k h.1*continuation h.1 h.2.1) := by
  rw [all_eighteen_entries 1 1 witnessRate _ _ _ witnessRate_pos.le (witnessTime_nonneg k),
    witness_retention, witness_theta, fixed_probability]
theorem covariant_eighteen_entries (B rev : Bool) (k : Q) (h : Hist) (a : Fin 2) :
    readoutTable (decisionReadout rev)
      (family 1 1 witnessRate (witnessTime k) (1/2) (witnessAngle k) B) h a=
      (if a=0 then decisionScore rev h else 1-decisionScore rev h)*
        (covariantRows B k h.1*continuation h.1 h.2.1) := by
  rw [all_eighteen_entries 1 1 witnessRate _ _ _ witnessRate_pos.le (witnessTime_nonneg k),
    witness_retention, witness_theta, covariant_probability]
def fixedErrors : Q → ℝ := ![1/4,1/2,9/16]
def bestErrors : Q → ℝ := ![1/4,1/2,7/16]
def covariantErrors : Q → ℝ := ![1/4,3/8,7/16]
theorem witness_fixed_errors (k : Q) :
    instrumentError (family 1 1 witnessRate (witnessTime k) (1/2) 0 false)
      (family 1 1 witnessRate (witnessTime k) (1/2) 0 true) (decisionReadout false)=fixedErrors k := by
  rw [decision_attains 1 1 witnessRate _ _ witnessRate_pos.le (witnessTime_nonneg k)
    (by norm_num) (by norm_num), witness_retention, witness_theta]
  fin_cases k <;> norm_num [witnessQ,witnessAngle,fixedErrors,Matrix.cons_val_two]
theorem witness_best_errors (k : Q) :
    instrumentError (family 1 1 witnessRate (witnessTime k) (1/2) 0 false)
      (family 1 1 witnessRate (witnessTime k) (1/2) 0 true)
      (decisionReadout (optimalReversal (witnessAngle k) 0))=bestErrors k := by
  rw [← witness_theta k, optimal_attains 1 1 witnessRate _ _ witnessRate_pos.le (witnessTime_nonneg k)
    (by norm_num) (by norm_num), witness_retention, witness_theta]
  fin_cases k <;> norm_num [witnessQ,witnessAngle,bestErrors,Matrix.cons_val_two]
theorem witness_covariant_errors (k : Q) :
    instrumentError (family 1 1 witnessRate (witnessTime k) (1/2) (witnessAngle k) false)
      (family 1 1 witnessRate (witnessTime k) (1/2) (witnessAngle k) true)
      (decisionReadout false)=covariantErrors k := by
  rw [← witness_theta k, covariant_attains 1 1 witnessRate _ witnessRate_pos.le (witnessTime_nonneg k)
    (by norm_num) (by norm_num), witness_retention]
  fin_cases k <;> norm_num [witnessQ,covariantErrors,Matrix.cons_val_two]


theorem witness_best_formula (k : Q) :
    (1-witnessQ k*|Real.cos (witnessAngle k-0)|)/2=bestErrors k := by
  fin_cases k <;> norm_num [witnessQ,witnessAngle,bestErrors,Matrix.cons_val_two]
theorem witness_covariant_formula (k : Q) : (1-witnessQ k)/2=covariantErrors k := by
  fin_cases k <;> norm_num [witnessQ,covariantErrors,Matrix.cons_val_two]
theorem witness_effect_isLeast (k : Q) :
    IsLeast {x : ℝ | ∃ E : Hist → MatJoint, (∀ h, IsBinaryPOVM (E h)) ∧
      readoutError (family 1 1 witnessRate (witnessTime k) (1/2) 0 false)
        (family 1 1 witnessRate (witnessTime k) (1/2) 0 true) E=x} (bestErrors k) := by
  simpa only [witness_retention,witness_theta,witness_best_formula] using
    all_effect_isLeast 1 1 witnessRate (witnessTime k) 0 witnessRate_pos.le
      (witnessTime_nonneg k) (r:=1/2) (by norm_num) (by norm_num)
theorem witness_randomized_isLeast (k : Q) :
    IsLeast {x : ℝ | ∃ s : Hist → ℝ, (∀ h, s h∈Set.Icc (0:ℝ) 1) ∧
      historyError (family 1 1 witnessRate (witnessTime k) (1/2) 0 false)
        (family 1 1 witnessRate (witnessTime k) (1/2) 0 true) s=x} (bestErrors k) := by
  simpa only [witness_retention,witness_theta,witness_best_formula] using
    randomized_isLeast 1 1 witnessRate (witnessTime k) 0 witnessRate_pos.le
      (witnessTime_nonneg k) (r:=1/2) (by norm_num) (by norm_num)
theorem witness_physical_isLeast (k : Q) :
    IsLeast {x : ℝ | ∃ I : Hist → FiniteInstrument (Q×Unit) 2,
      instrumentError (family 1 1 witnessRate (witnessTime k) (1/2) 0 false)
        (family 1 1 witnessRate (witnessTime k) (1/2) 0 true) I=x} (bestErrors k) := by
  simpa only [witness_retention,witness_theta,witness_best_formula] using
    physical_isLeast 1 1 witnessRate (witnessTime k) 0 witnessRate_pos.le
      (witnessTime_nonneg k) (r:=1/2) (by norm_num) (by norm_num)
theorem witness_covariant_effect_isLeast (k : Q) :
    IsLeast {x : ℝ | ∃ E : Hist → MatJoint, (∀ h, IsBinaryPOVM (E h)) ∧
      readoutError (family 1 1 witnessRate (witnessTime k) (1/2) (witnessAngle k) false)
        (family 1 1 witnessRate (witnessTime k) (1/2) (witnessAngle k) true) E=x} (covariantErrors k) := by
  simpa only [witness_retention,witness_theta,sub_self,Real.cos_zero,abs_one,mul_one,
    witness_covariant_formula] using
    all_effect_isLeast 1 1 witnessRate (witnessTime k) (witnessAngle k) witnessRate_pos.le
      (witnessTime_nonneg k) (r:=1/2) (by norm_num) (by norm_num)
theorem witness_covariant_randomized_isLeast (k : Q) :
    IsLeast {x : ℝ | ∃ s : Hist → ℝ, (∀ h, s h∈Set.Icc (0:ℝ) 1) ∧
      historyError (family 1 1 witnessRate (witnessTime k) (1/2) (witnessAngle k) false)
        (family 1 1 witnessRate (witnessTime k) (1/2) (witnessAngle k) true) s=x} (covariantErrors k) := by
  simpa only [witness_retention,witness_theta,sub_self,Real.cos_zero,abs_one,mul_one,
    witness_covariant_formula] using
    randomized_isLeast 1 1 witnessRate (witnessTime k) (witnessAngle k) witnessRate_pos.le
      (witnessTime_nonneg k) (r:=1/2) (by norm_num) (by norm_num)
theorem witness_covariant_physical_isLeast (k : Q) :
    IsLeast {x : ℝ | ∃ I : Hist → FiniteInstrument (Q×Unit) 2,
      instrumentError (family 1 1 witnessRate (witnessTime k) (1/2) (witnessAngle k) false)
        (family 1 1 witnessRate (witnessTime k) (1/2) (witnessAngle k) true) I=x} (covariantErrors k) := by
  simpa only [witness_retention,witness_theta,sub_self,Real.cos_zero,abs_one,mul_one,
    witness_covariant_formula] using
    physical_isLeast 1 1 witnessRate (witnessTime k) (witnessAngle k) witnessRate_pos.le
      (witnessTime_nonneg k) (r:=1/2) (by norm_num) (by norm_num)
theorem witness_decision_laws (k : Q) (φ : ℝ) (B rev : Bool) :
    (∀ h a, 0≤readoutTable (decisionReadout rev)
      (family 1 1 witnessRate (witnessTime k) (1/2) φ B) h a) ∧
    (∑ h, ∑ a, readoutTable (decisionReadout rev)
      (family 1 1 witnessRate (witnessTime k) (1/2) φ B) h a)=1 :=
  decision_laws 1 1 witnessRate _ φ witnessRate_pos.le (witnessTime_nonneg k)
    (by norm_num) (by norm_num) B rev
theorem witness_third_mass (k : Q) (φ : ℝ) (B : Bool) :
    (∑ j, (family 1 1 witnessRate (witnessTime k) (1/2) φ B (2,j,())).trace.re)=
      (![1/12,1/8,7/48]:Q → ℝ) k := by
  rw [third_mass 1 1 witnessRate _ _ φ witnessRate_pos.le (witnessTime_nonneg k), witness_retention]
  fin_cases k <;> norm_num [witnessQ, Matrix.cons_val_two]
theorem witness_third_positive (k : Q) (φ : ℝ) (B : Bool) :
    0<(∑ j, (family 1 1 witnessRate (witnessTime k) (1/2) φ B (2,j,())).trace.re) :=
  third_mass_positive 1 1 witnessRate _ φ witnessRate_pos.le (witnessTime_nonneg k)
    (by norm_num) (by norm_num) B

/-- A covariant comparison holds q fixed, rather than identifying distinct physical times. -/
theorem covariant_same_retention (b ℏ γ t r : ℝ) (hγ : 0≤γ) (ht : 0≤t) (B : Bool) :
    family b ℏ γ t r (theta b ℏ t) B=family b ℏ γ 0 (retention r γ t) 0 B := by
  funext h
  rcases h with ⟨a,j,⟨⟩⟩
  rw [all_nine_branches b ℏ γ t r _ hγ ht,
    all_nine_branches b ℏ γ 0 _ _ hγ le_rfl]
  simp only [retention, mul_zero, Real.exp_zero, mul_one, theta, zero_mul, zero_div]
  simp only [probability, sub_self, Real.cos_zero, mul_one]
theorem zero_preparation_equal (b ℏ γ t : ℝ) (B : Bool) :
    evolved b ℏ γ t 0 B=krausMap (channelKraus b ℏ γ t) equilibrium := by
  cases B <;> simp [evolved,preparation,sigmaA,sigmaB,mixture]
theorem zero_preparation_family (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t) :
    family b ℏ γ t 0 φ false=family b ℏ γ t 0 φ true := by
  apply family_tie b ℏ γ t 0 φ hγ ht
  simp [retention]
theorem zero_time_preparation (b ℏ γ r : ℝ) (hγ : 0≤γ) (B : Bool) :
    evolved b ℏ γ 0 r B=preparation r B :=
  channel_zero_time b ℏ γ hγ _
theorem zero_rate_preparation (b ℏ t r : ℝ) (ht : 0≤t) (B : Bool) :
    evolved b ℏ 0 t r B=phase b ℏ t (preparation r B) :=
  channel_zero_rate b ℏ t ht _
theorem pure_zero_third (b ℏ γ φ : ℝ) (hγ : 0≤γ) (B : Bool) (j : Q) :
    family b ℏ γ 0 1 φ B (2,j,())=0 := by
  rw [all_nine_branches b ℏ γ 0 1 φ hγ le_rfl]
  norm_num [probability,retention,Fin.ext_iff]
theorem quarter_erasure :
    family 1 1 witnessRate tStar (1/2) 0 false=family 1 1 witnessRate tStar (1/2) 0 true := by
  apply family_tie 1 1 witnessRate tStar (1/2) 0 witnessRate_pos.le tStar_pos.le
  have ha := witness_theta 1
  change theta 1 1 tStar=Real.pi/2 at ha
  rw [ha,sub_zero,Real.cos_pi_div_two,mul_zero]
theorem half_reversal :
    optimalReversal (theta 1 1 (2*tStar)) 0=true ∧
    instrumentError (family 1 1 witnessRate (2*tStar) (1/2) 0 false)
      (family 1 1 witnessRate (2*tStar) (1/2) 0 true) (decisionReadout false)=9/16 ∧
    instrumentError (family 1 1 witnessRate (2*tStar) (1/2) 0 false)
      (family 1 1 witnessRate (2*tStar) (1/2) 0 true) (decisionReadout true)=7/16 := by
  have ha := witness_theta 2
  change theta 1 1 (2*tStar)=Real.pi at ha
  have hr : optimalReversal (theta 1 1 (2*tStar)) 0=true := by
    simp [ha,optimalReversal]
  refine ⟨hr, ?_, ?_⟩
  · exact witness_fixed_errors 2
  · have h := witness_best_errors 2
    simpa [witnessAngle,witnessTime,bestErrors,optimalReversal,Matrix.cons_val_two] using h
/-- A zero-rate nonidentity witness on an algebraic coordinate, not a density. -/
theorem zero_rate_half_coordinate :
    krausMap (channelKraus 1 1 0 (2*tStar)) (Matrix.single 0 1 1)=
      -(Matrix.single 0 1 1:MatQ) := by
  rw [channel_zero_rate 1 1 _ (mul_nonneg (by norm_num) tStar_pos.le), phase_E01]
  have ha := witness_theta 2
  change theta 1 1 (2*tStar)=Real.pi at ha
  rw [ha,exp_pos_angle]
  norm_num
theorem zero_rate_nonidentity :
    krausMap (channelKraus 1 1 0 (2*tStar)) (Matrix.single 0 1 1)≠(Matrix.single 0 1 1:MatQ) := by
  rw [zero_rate_half_coordinate]
  intro h
  have hc := congrArg (fun X : MatQ => X 0 1) h
  norm_num [Matrix.single] at hc

/-- Full physical domain and full Hamiltonian interpretation for the chosen input channel. -/
theorem physical_preparation_contract {b ℏ γ t r : ℝ}
    (hb : 0<b) (hℏ : 0<ℏ) (hγ : 0≤γ) (ht : 0≤t) (hr : 0≤r) (hr1 : r≤1) (B : Bool) :
    thermalH b≠0 ∧ IsDensityOperator (evolved b ℏ γ t r B) ∧
    phase b ℏ t (preparation r B)=FiniteGibbsClock.heisenberg (thermalH b) ℏ (-t) (preparation r B) ∧
    evolved b ℏ γ t r B=lindbladPropagatorAction (scaledH b ℏ) (jumps γ) t (preparation r B) :=
  ⟨thermalH_ne_zero hb,evolved_density b ℏ γ t hγ ht hr hr1 B,
    phase_physical b ℏ t hℏ _,channel_propagator b ℏ γ t hγ ht _⟩
theorem full_level_two_coordinates (b ℏ t : ℝ) :
    phase b ℏ t (Matrix.single 0 2 1)=
      Complex.exp (Complex.I*t*(Real.log 3/b/ℏ:ℝ)) • (Matrix.single 0 2 1:MatQ) ∧
    phase b ℏ t (Matrix.single 1 2 1)=
      Complex.exp (-Complex.I*t*((delta/b/ℏ:ℝ)-(Real.log 3/b/ℏ:ℝ))) • (Matrix.single 1 2 1:MatQ) :=
  ⟨phase_E02 b ℏ t,phase_E12 b ℏ t⟩


theorem pre_physical_isLeast (b ℏ γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    IsLeast {x : ℝ | ∃ I : FiniteInstrument (Q×Unit) 2,
      (I.weight 0 (joint (evolved b ℏ γ t r true))+
        I.weight 1 (joint (evolved b ℏ γ t r false)))/2=x} ((1-retention r γ t)/2) := by
  refine ⟨⟨preReadout (theta b ℏ t),pre_physical_attains b ℏ γ t hγ ht hr hr1⟩,?_⟩
  rintro x ⟨I,rfl⟩
  simp only [inducedEffect_weight]
  rw [← inducedEffect_complement I]
  exact (pre_isLeast b ℏ γ t hγ ht hr hr1).2 ⟨_,inducedEffect_admissible I,rfl⟩
theorem witness_pre_isLeast (k : Q) :
    IsLeast {x : ℝ | ∃ E : MatJoint, IsBinaryPOVM E ∧
      povmAvgError (joint (evolved 1 1 witnessRate (witnessTime k) (1/2) false))
        (joint (evolved 1 1 witnessRate (witnessTime k) (1/2) true)) E=x} (covariantErrors k) := by
  simpa only [witness_retention,witness_covariant_formula] using
    pre_isLeast 1 1 witnessRate (witnessTime k) witnessRate_pos.le
      (witnessTime_nonneg k) (r:=1/2) (by norm_num) (by norm_num)
theorem witness_pre_physical_isLeast (k : Q) :
    IsLeast {x : ℝ | ∃ I : FiniteInstrument (Q×Unit) 2,
      (I.weight 0 (joint (evolved 1 1 witnessRate (witnessTime k) (1/2) true))+
        I.weight 1 (joint (evolved 1 1 witnessRate (witnessTime k) (1/2) false)))/2=x} (covariantErrors k) := by
  simpa only [witness_retention,witness_covariant_formula] using
    pre_physical_isLeast 1 1 witnessRate (witnessTime k) witnessRate_pos.le
      (witnessTime_nonneg k) (r:=1/2) (by norm_num) (by norm_num)
theorem tree_history_variation (b ℏ γ t φ : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    {r : ℝ} (hr : 0≤r) :
    FiniteAdaptiveMapPerturbation.historyVariation Q Unit 3 (tree φ) (tree φ)
      (joint (evolved b ℏ γ t r false)) (joint (evolved b ℏ γ t r true))=
      retention r γ t*|Real.cos (theta b ℏ t-φ)| := by
  rw [← tree_familyHistoryVariation]
  exact observed_variation b ℏ γ t φ hγ ht hr
theorem quarter_distances :
    traceDist (joint (evolved 1 1 witnessRate tStar (1/2) false))
      (joint (evolved 1 1 witnessRate tStar (1/2) true))=1/4 ∧
    outputDistance Q Unit 3 (tree 0) (tree 0)
      (joint (evolved 1 1 witnessRate tStar (1/2) false))
      (joint (evolved 1 1 witnessRate tStar (1/2) true))=0 := by
  have hq := witness_retention 1
  change retention (1/2) witnessRate tStar=1/4 at hq
  have ha := witness_theta 1
  change theta 1 1 tStar=Real.pi/2 at ha
  constructor
  · rw [premeasurement_distance 1 1 witnessRate tStar witnessRate_pos.le tStar_pos.le (by norm_num),hq]
  · rw [tree_output_distance 1 1 witnessRate tStar 0 witnessRate_pos.le tStar_pos.le (by norm_num),ha]
    simp
theorem quarter_all_effects (E : Hist → MatJoint) :
    readoutError (family 1 1 witnessRate tStar (1/2) 0 false)
      (family 1 1 witnessRate tStar (1/2) 0 true) E=1/2 := by
  apply tie_every_effect 1 1 witnessRate tStar 0 witnessRate_pos.le tStar_pos.le (by norm_num) (by norm_num)
  have ha := witness_theta 1
  change theta 1 1 tStar=Real.pi/2 at ha
  simp [ha]
theorem quarter_all_instruments (I : Hist → FiniteInstrument (Q×Unit) 2) :
    instrumentError (family 1 1 witnessRate tStar (1/2) 0 false)
      (family 1 1 witnessRate tStar (1/2) 0 true) I=1/2 := by
  rw [arbitrary_instrument_effect]
  exact quarter_all_effects _
theorem quarter_all_randomized (s : Hist → ℝ) :
    historyError (family 1 1 witnessRate tStar (1/2) 0 false)
      (family 1 1 witnessRate tStar (1/2) 0 true) s=1/2 := by
  rw [← historyError_scalar_effect]
  exact quarter_all_effects _
theorem zero_preparation_every_effect (b ℏ γ t : ℝ) (E : MatJoint) :
    povmAvgError (joint (evolved b ℏ γ t 0 false)) (joint (evolved b ℏ γ t 0 true)) E=
      (joint (krausMap (channelKraus b ℏ γ t) equilibrium)).trace.re/2 := by
  rw [zero_preparation_equal,zero_preparation_equal]
  simp only [povmAvgError, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,Complex.sub_re]
  ring


theorem zero_preparation_physical_error (b ℏ γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t) (E : MatJoint) :
    povmAvgError (joint (evolved b ℏ γ t 0 false)) (joint (evolved b ℏ γ t 0 true)) E=1/2 := by
  rw [zero_preparation_every_effect,
    (joint_density (channel_density b ℏ γ t hγ ht equilibrium_density)).2]
  norm_num
/-- Even with the same full combined propagator at every old computational step. -/
theorem old_combined_branches (b ℏ γ t r : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) (h : History 3 (n+1)) :
    run Q Unit 3 (combinedHistory b ℏ γ hγ n s hs) h (joint (evolved b ℏ γ t r false))=
    run Q Unit 3 (combinedHistory b ℏ γ hγ n s hs) h (joint (evolved b ℏ γ t r true)) := by
  rw [combinedHistory_all_joint,combinedHistory_all_joint]
  exact old_history_evolved_pair b ℏ γ t hγ ht r (threeRate γ hγ) n s hs h

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelCoherentReadout
