import SKEFTHawking.QuantumNetwork.FiniteThreeLevelEnvironmentLift

/-!
# Two-gap qutrit memory readout

Three rational rank-one projections resolve both coherence arms of a retained
qutrit. Readout phases are independent instrument controls. All recorded
histories retain their unnormalized branch matrices.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelMemoryReadout
open Matrix FinitePositiveKernel DiagonalLindblad GibbsObservable
open OpenSystems FiniteInterventionProcess GibbsMultilevelReflection
open FiniteAdaptiveMapPerturbation
open FiniteAdaptiveReadoutDiscrimination FiniteAdaptiveReadoutRobustness
open scoped ComplexOrder Kronecker BigOperators
abbrev Q := Fin 3
abbrev MatQ := Matrix Q Q ℂ
abbrev Joint := Q × Q
abbrev MatJoint := Matrix Joint Joint ℂ

/-- Outcomes 0, 1 and 2 denote the plus, minus and dark modes. -/
def P (a : Q) : MatQ :=
  if a.val = 0 then !![1/2,3/10,2/5;3/10,9/50,6/25;2/5,6/25,8/25]
  else if a.val = 1 then !![1/2,-3/10,-2/5;-3/10,9/50,6/25;-2/5,6/25,8/25]
  else !![0,0,0;0,16/25,-12/25;0,-12/25,9/25]

theorem P_hermitian (a : Q) : (P a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> norm_num [P]

theorem P_square (a : Q) : P a * P a = P a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, Matrix.mul_apply, Fin.sum_univ_succ]

theorem P_orthogonal (a b : Q) (h : a ≠ b) : P a * P b = 0 := by
  ext i j
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, Matrix.mul_apply, Fin.sum_univ_succ] at *

theorem P_sum : ∑ a, P a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P, Fin.sum_univ_succ, Matrix.one_apply, Fin.reduceEq, Fin.reduceFinMk]

theorem P_trace (a : Q) : (P a).trace = 1 := by
  fin_cases a <;> norm_num [P, Matrix.trace, Fin.sum_univ_succ]

theorem P_positive (a : Q) : (P a).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (P a)
  rwa [(P_hermitian a).eq, P_square] at h

theorem P_density (a : Q) : IsDensityOperator (P a) := ⟨P_positive a, P_trace a⟩

private theorem P_compression_0 (X : MatQ) :
    P 0 * X * P 0 = (P 0 * X).trace • P 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, Matrix.mul_apply, Matrix.trace, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ] <;> ring

private theorem P_compression_1 (X : MatQ) :
    P 1 * X * P 1 = (P 1 * X).trace • P 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, Matrix.mul_apply, Matrix.trace, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ] <;> ring

private theorem P_compression_2 (X : MatQ) :
    P 2 * X * P 2 = (P 2 * X).trace • P 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, Matrix.mul_apply, Matrix.trace, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ] <;> ring

/-- Rank-one compression on arbitrary complex matrices. -/
theorem P_compression (a : Q) (X : MatQ) :
    P a * X * P a = (P a * X).trace • P a := by
  fin_cases a
  · exact P_compression_0 X
  · exact P_compression_1 X
  · exact P_compression_2 X

def frameLevels (φ₁ φ₂ : ℝ) : Q → ℝ := ![0,φ₁,φ₂]
def rotate (φ₁ φ₂ : ℝ) (X : MatQ) : MatQ :=
  GibbsHamiltonianRelaxation.rotation (frameLevels φ₁ φ₂) (-1) X

theorem rotate_entry (φ₁ φ₂ : ℝ) (X : MatQ) (i j : Q) :
    rotate φ₁ φ₂ X i j =
      Complex.exp (-Complex.I * ((frameLevels φ₁ φ₂ i : ℂ) - frameLevels φ₁ φ₂ j)) * X i j := by
  rw [rotate, GibbsHamiltonianRelaxation.rotation_entry]
  congr 2
  push_cast
  ring

theorem rotate_mul (φ₁ φ₂ : ℝ) (X Y : MatQ) :
    rotate φ₁ φ₂ (X*Y) = rotate φ₁ φ₂ X * rotate φ₁ φ₂ Y :=
  FiniteGibbsClock.heisenberg_mul _ _ _ _ _
theorem rotate_add (φ₁ φ₂ : ℝ) (X Y : MatQ) :
    rotate φ₁ φ₂ (X+Y) = rotate φ₁ φ₂ X + rotate φ₁ φ₂ Y :=
  GibbsHamiltonianRelaxation.rotation_add _ _ _ _
theorem rotate_smul (φ₁ φ₂ : ℝ) (z : ℂ) (X : MatQ) :
    rotate φ₁ φ₂ (z • X) = z • rotate φ₁ φ₂ X :=
  GibbsHamiltonianRelaxation.rotation_smul _ _ _ _
theorem rotate_one (φ₁ φ₂ : ℝ) : rotate φ₁ φ₂ 1 = 1 :=
  FiniteGibbsClock.heisenberg_one _ _ _
theorem rotate_trace (φ₁ φ₂ : ℝ) (X : MatQ) : (rotate φ₁ φ₂ X).trace = X.trace :=
  GibbsHamiltonianRelaxation.rotation_trace _ _ _
theorem rotate_adjoint (φ₁ φ₂ : ℝ) (X : MatQ) :
    (rotate φ₁ φ₂ X)ᴴ = rotate φ₁ φ₂ Xᴴ :=
  (FiniteGibbsClock.heisenberg_star
    (GibbsHamiltonianRelaxation.density_hermitian (frameLevels φ₁ φ₂)) 1 (-1) X).symm

theorem rotate_inverse (φ₁ φ₂ : ℝ) (X : MatQ) :
    rotate φ₁ φ₂ (rotate (-φ₁) (-φ₂) X) = X := by
  ext i j
  simp only [rotate_entry, ← mul_assoc, ← Complex.exp_add]
  have hn (i : Q) : frameLevels (-φ₁) (-φ₂) i = -frameLevels φ₁ φ₂ i := by
    fin_cases i <;> simp [frameLevels]
  simp only [hn, Complex.ofReal_neg]
  rw [show -Complex.I * ((frameLevels φ₁ φ₂ i : ℂ) - frameLevels φ₁ φ₂ j) +
    -Complex.I * (-(frameLevels φ₁ φ₂ i : ℂ) - -frameLevels φ₁ φ₂ j) = 0 by ring]
  simp

def R (φ₁ φ₂ : ℝ) (a : Q) : MatQ := rotate φ₁ φ₂ (P a)
theorem R_hermitian (φ₁ φ₂ : ℝ) (a : Q) : (R φ₁ φ₂ a).IsHermitian := by
  change (rotate φ₁ φ₂ (P a))ᴴ = rotate φ₁ φ₂ (P a)
  rw [rotate_adjoint, (P_hermitian a).eq]
theorem R_square (φ₁ φ₂ : ℝ) (a : Q) : R φ₁ φ₂ a * R φ₁ φ₂ a = R φ₁ φ₂ a := by
  rw [R, ← rotate_mul, P_square]
theorem R_trace (φ₁ φ₂ : ℝ) (a : Q) : (R φ₁ φ₂ a).trace = 1 := by
  rw [R, rotate_trace, P_trace]
theorem R_sum (φ₁ φ₂ : ℝ) : ∑ a, R φ₁ φ₂ a = 1 := by
  have hp := P_sum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hp ⊢
  rw [R, R, R, ← rotate_add, ← rotate_add, hp, rotate_one]
theorem R_positive (φ₁ φ₂ : ℝ) (a : Q) : (R φ₁ φ₂ a).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (R φ₁ φ₂ a)
  rwa [(R_hermitian φ₁ φ₂ a).eq, R_square] at h
theorem R_density (φ₁ φ₂ : ℝ) (a : Q) : IsDensityOperator (R φ₁ φ₂ a) :=
  ⟨R_positive φ₁ φ₂ a, R_trace φ₁ φ₂ a⟩

/-- A direct three-outcome, count-one physical instrument. -/
def readout (φ₁ φ₂ : ℝ) : FiniteInstrument Q 3 where
  count := 1
  operators a _ := R φ₁ φ₂ a
  normalized := by
    simp only [Fin.sum_univ_one, (R_hermitian φ₁ φ₂ _).eq, R_square]
    exact R_sum φ₁ φ₂

theorem R_compression (φ₁ φ₂ : ℝ) (a : Q) (X : MatQ) :
    R φ₁ φ₂ a * X * R φ₁ φ₂ a = (R φ₁ φ₂ a * X).trace • R φ₁ φ₂ a := by
  have hi := rotate_inverse φ₁ φ₂ X
  conv_lhs => arg 1; arg 2; rw [← hi]
  rw [R, ← rotate_mul, ← rotate_mul, P_compression, rotate_smul]
  congr 1
  rw [← rotate_trace φ₁ φ₂ (P a * rotate (-φ₁) (-φ₂) X), rotate_mul, hi]

theorem readout_branch (φ₁ φ₂ : ℝ) (a : Q) (X : MatQ) :
    (readout φ₁ φ₂).branch a X = (R φ₁ φ₂ a * X).trace • R φ₁ φ₂ a := by
  change (∑ _ : Fin 1, R φ₁ φ₂ a * X * (R φ₁ φ₂ a)ᴴ) = _
  rw [Fin.sum_univ_one, (R_hermitian φ₁ φ₂ a).eq, R_compression]
theorem readout_weight (φ₁ φ₂ : ℝ) (a : Q) (X : MatQ) :
    (readout φ₁ φ₂).weight a X = (R φ₁ φ₂ a * X).trace.re := by
  rw [FiniteInstrument.weight, readout_branch, Matrix.trace_smul, R_trace, smul_eq_mul, mul_one]

open FiniteThreeLevelThermalPhase (equilibrium mixture retention channelKraus)

/-- Normalized real vectors; sqrt(2)/2 equals the inverse square root. -/
def v (a : Q) : Q → ℂ :=
  if a.val = 0 then ![FiniteThreeLevelThermalPhase.s,
    3/5*FiniteThreeLevelThermalPhase.s,4/5*FiniteThreeLevelThermalPhase.s]
  else if a.val = 1 then ![-FiniteThreeLevelThermalPhase.s,
    3/5*FiniteThreeLevelThermalPhase.s,4/5*FiniteThreeLevelThermalPhase.s]
  else ![0,4/5,-3/5]

theorem v_rank_one (a : Q) : P a = Matrix.vecMulVec (v a) (star (v a)) := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [map_ofNat, P, v, Matrix.vecMulVec, FiniteThreeLevelThermalPhase.s_conj,
      mul_assoc, ← mul_assoc, FiniteThreeLevelThermalPhase.s_square] <;>
    ring_nf <;> norm_num [map_ofNat, show FiniteThreeLevelThermalPhase.s^2 = 1/2 by
      simpa [pow_two] using FiniteThreeLevelThermalPhase.s_square]

theorem v_normalized (a : Q) : ∑ i, star (v a i) * v a i = 1 := by
  have h := P_trace a
  rw [v_rank_one] at h
  simpa [Matrix.trace, Matrix.vecMulVec, mul_comm] using h

theorem R_orthogonal (φ₁ φ₂ : ℝ) (a b : Q) (hab : a ≠ b) :
    R φ₁ φ₂ a * R φ₁ φ₂ b = 0 := by
  rw [R, R, ← rotate_mul, P_orthogonal a b hab]
  ext i j
  simp [rotate_entry]

/-- The dark input is Gibbs; only the two signal labels are mixed with a pure mode. -/
def sigma (r : ℝ) (a : Q) : MatQ := if a.val = 2 then equilibrium else mixture r (P a)
theorem sigma_density {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (a : Q) :
    IsDensityOperator (sigma r a) := by
  unfold sigma
  split_ifs
  · exact FiniteThreeLevelThermalPhase.equilibrium_density
  · exact FiniteThreeLevelThermalPhase.mixture_density hr hr1 (P_density a)
theorem sigma_trace (r : ℝ) (a : Q) : (sigma r a).trace = 1 := by
  unfold sigma
  split_ifs
  · exact FiniteThreeLevelThermalPhase.equilibrium_density.2
  · simp [mixture, Matrix.trace_add, Matrix.trace_smul, P_trace,
      FiniteThreeLevelThermalPhase.equilibrium_density.2]
theorem sigma_faithful {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (a : Q) :
    (sigma r a).PosDef := by
  unfold sigma
  split_ifs
  · exact FiniteThreeLevelThermalPhase.equilibrium_posDef
  · exact FiniteThreeLevelThermalPhase.mixture_faithful hr hr1 (P_positive a)
theorem sigma_zero (a : Q) : sigma 0 a = equilibrium := by
  simp [sigma, mixture]

/-- The pulse flips both 01 and 02 arms simultaneously. -/
def F : MatQ := Matrix.diagonal ![-1,1,1]
theorem F_adjoint : Fᴴ = F := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [F, Matrix.conjTranspose_apply]
theorem F_square : F * F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [F, Matrix.diagonal_mul_diagonal]
theorem F_unitary : F ∈ Matrix.unitaryGroup Q ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change F*Fᴴ=1
  rw [F_adjoint, F_square]
def exchange (a : Q) : Q := if a.val = 0 then 1 else if a.val = 1 then 0 else 2

theorem F_P (a : Q) : F * P a * Fᴴ = P (exchange a) := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [F, P, exchange, Matrix.diagonal_mul, Matrix.mul_diagonal]
theorem F_equilibrium : F * equilibrium * Fᴴ = equilibrium := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [F, equilibrium, density, three, Matrix.diagonal_mul_diagonal]
theorem F_sigma (r : ℝ) (a : Q) : F * sigma r a * Fᴴ = sigma r (exchange a) := by
  fin_cases a <;>
    norm_num [sigma, exchange, show (0 : Q) ≠ 2 by decide, show (1 : Q) ≠ 2 by decide,
      mixture, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, F_P, F_equilibrium]

def prepareOp (a k : Q) : MatQ := if a = 0 then Matrix.single 0 k 1 else 0
private theorem prepareOp_square (a k : Q) :
    (prepareOp a k)ᴴ * prepareOp a k = if a = 0 then projector k else 0 := by
  by_cases ha : a = 0
  · subst a
    ext i j
    simp [prepareOp, Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.single, projector,
      Matrix.diagonal_apply]
    aesop
  · simp [prepareOp, ha]

/-- Erase the physical S register after its classical outcome has been recorded. -/
def prepare : FiniteInstrument Q 3 where
  count := 3
  operators := prepareOp
  normalized := by
    simp_rw [prepareOp_square]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    exact projector_sum

theorem prepare_branch (a : Q) (X : MatQ) :
    prepare.branch a X = if a = 0 then X.trace • projector (0 : Q) else 0 := by
  by_cases ha : a = 0
  · subst a
    change (∑ k : Q, Matrix.single 0 k 1 * X * (Matrix.single 0 k 1)ᴴ) = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.single, Matrix.trace, projector, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceFinMk]
  · simp [prepare, prepareOp, FiniteInstrument.branch, krausMap, ha]

theorem lift_branch_tensor (I : FiniteInstrument Q 3) (a : Q) (A B : MatQ) :
    (I.lift Q).branch a (A ⊗ₖ B) = I.branch a A ⊗ₖ B := by
  simp only [FiniteInstrument.branch, FiniteInstrument.lift, krausMap,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, one_mul, mul_one]
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [Matrix.sum_apply, Finset.sum_mul]
  rfl

def input (r : ℝ) : MatJoint := (1/3:ℂ) • ∑ a : Q, projector a ⊗ₖ sigma r a

theorem input_density {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsDensityOperator (input r) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.PosSemidef.smul _ (by norm_num [Complex.le_def] : (0:ℂ) ≤ 1/3)
    apply Matrix.posSemidef_sum
    intro a _
    exact (FiniteAdaptiveGibbsReadout.projector_density a).1.kronecker (sigma_density hr hr1 a).1
  · norm_num [input, Matrix.trace_smul, Matrix.trace_sum, Matrix.trace_kronecker,
      projector_trace, sigma_trace, Fin.sum_univ_succ]

def recordStep : Step Q Q 3 where
  count := 1
  evolution _ := 1
  normalized := by simp [IsKrausChannel]
  instrument := instrument 3

theorem recordStep_branch (a : Q) (r : ℝ) :
    recordStep.branch Q Q 3 a (input r) = (1/3:ℂ) • (projector a ⊗ₖ sigma r a) := by
  change ((instrument 3).lift Q).branch a (krausMap (fun _ : Fin 1 => 1) (input r)) = _
  simp only [krausMap, Fin.sum_univ_one, Matrix.conjTranspose_one, one_mul, mul_one]
  rw [input, FiniteInstrument.branch_smul]
  congr 1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    FiniteInstrument.branch_add, lift_branch_tensor, instrument_branch]
  fin_cases a <;> simp [projector]

def pulse (flip : Bool) : MatQ := if flip then F else 1
def pulseKraus (flip : Bool) : Fin 1 → MatJoint := fun _ => (1 : MatQ) ⊗ₖ pulse flip

theorem pulse_normalized (flip : Bool) : IsKrausChannel (pulseKraus flip) := by
  cases flip <;> simp [pulseKraus, pulse, IsKrausChannel, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, F_adjoint, F_square]

def evolution (b ℏ γ t : ℝ) (flip : Bool) := fun k =>
  FiniteThreeLevelEnvironmentLift.liftKraus (channelKraus b ℏ γ t) k * pulseKraus flip 0

theorem evolution_normalized (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (flip : Bool) :
    IsKrausChannel (evolution b ℏ γ t flip) := by
  unfold IsKrausChannel evolution
  simp only [Matrix.conjTranspose_mul]
  have hh := FiniteThreeLevelEnvironmentLift.thermal_normalized b ℏ γ t hγ ht
  have hp := pulse_normalized flip
  unfold IsKrausChannel at hh hp
  simp only [Fin.sum_univ_one] at hp
  calc
    _ = (pulseKraus flip 0)ᴴ * (∑ k,
        (FiniteThreeLevelEnvironmentLift.liftKraus (channelKraus b ℏ γ t) k)ᴴ *
        FiniteThreeLevelEnvironmentLift.liftKraus (channelKraus b ℏ γ t) k) * pulseKraus flip 0 := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, mul_assoc]
    _ = 1 := by rw [hh, mul_one, hp]

theorem evolution_action (b ℏ γ t : ℝ) (flip : Bool) (X : MatJoint) :
    krausMap (evolution b ℏ γ t flip) X =
      FiniteThreeLevelEnvironmentLift.liftState (channelKraus b ℏ γ t)
        (krausMap (pulseKraus flip) X) := by
  simp [evolution, FiniteThreeLevelEnvironmentLift.liftState, krausMap,
    Matrix.conjTranspose_mul, mul_assoc]

def memoryStep (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (flip : Bool) : Step Q Q 3 where
  count := _
  evolution := evolution b ℏ γ t flip
  normalized := evolution_normalized b ℏ γ t hγ ht flip
  instrument := prepare

def memoryTree (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (flip : Bool) : Tree Q Q 3 2 :=
  .node recordStep (fun _ => .node (memoryStep b ℏ γ t hγ ht flip) (fun _ => .done))
def memoryFamily (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (flip : Bool)
    (h : History 3 2) : MatJoint := run Q Q 3 (memoryTree b ℏ γ t hγ ht flip) h (input r)

def signalLabel (flip : Bool) (a : Q) : Q := if flip then exchange a else a
def evolved (b ℏ γ t r : ℝ) (a : Q) : MatQ := krausMap (channelKraus b ℏ γ t) (sigma r a)

theorem pulse_tensor (flip : Bool) (A B : MatQ) :
    krausMap (pulseKraus flip) (A ⊗ₖ B) = A ⊗ₖ (pulse flip * B * (pulse flip)ᴴ) := by
  simp [krausMap, pulseKraus, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]

theorem memoryStep_tensor (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (a c : Q) :
    (memoryStep b ℏ γ t hγ ht flip).branch Q Q 3 c (projector a ⊗ₖ sigma r a) =
      if c = 0 then projector (0 : Q) ⊗ₖ evolved b ℏ γ t r (signalLabel flip a) else 0 := by
  change (prepare.lift Q).branch c (krausMap (evolution b ℏ γ t flip) _) = _
  rw [evolution_action, pulse_tensor]
  have hp : pulse flip * sigma r a * (pulse flip)ᴴ = sigma r (signalLabel flip a) := by
    cases flip <;> simp [pulse, signalLabel, F_sigma]
  rw [hp]
  change (prepare.lift Q).branch c
    (FiniteThreeLevelEnvironmentLift.liftState (channelKraus b ℏ γ t) _) = _
  rw [FiniteThreeLevelEnvironmentLift.product_action, lift_branch_tensor,
    prepare_branch, projector_trace]
  split_ifs <;> simp_all [evolved]

/-- Every one of the nine histories, including six impossible branches. -/
theorem memory_run (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (a c : Q) :
    memoryFamily b ℏ γ t r hγ ht flip (a,c,()) =
      if c = 0 then (1/3:ℂ) • (projector (0 : Q) ⊗ₖ
        evolved b ℏ γ t r (signalLabel flip a)) else 0 := by
  change (memoryStep b ℏ γ t hγ ht flip).branch Q Q 3 c
    (recordStep.branch Q Q 3 a (input r)) = _
  rw [recordStep_branch, Step.branch_smul, memoryStep_tensor]
  split_ifs <;> simp

theorem memory_valid (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (flip : Bool) :
    IsBranchFamily (memoryFamily b ℏ γ t r hγ ht flip) :=
  run_family _ (input_density hr hr1)

def readStep (φ₁ φ₂ : ℝ) : Step Q Q 3 where
  count := 1
  evolution := FiniteThreeLevelEnvironmentLift.swapKraus
  normalized := FiniteThreeLevelEnvironmentLift.swap_normalized
  instrument := readout φ₁ φ₂

def measuredTree (b ℏ γ t φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) : Tree Q Q 3 3 :=
  .node recordStep (fun _ => .node (memoryStep b ℏ γ t hγ ht flip)
    (fun _ => .node (readStep φ₁ φ₂) (fun _ => .done)))
def measuredFamily (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (h : History 3 3) : MatJoint :=
  run Q Q 3 (measuredTree b ℏ γ t φ₁ φ₂ hγ ht flip) h (input r)

theorem readStep_tensor (φ₁ φ₂ : ℝ) (a : Q) (X : MatQ) :
    (readStep φ₁ φ₂).branch Q Q 3 a (projector (0 : Q) ⊗ₖ X) =
      (R φ₁ φ₂ a * X).trace • (R φ₁ φ₂ a ⊗ₖ projector (0 : Q)) := by
  change ((readout φ₁ φ₂).lift Q).branch a (FiniteThreeLevelEnvironmentLift.swap _) = _
  rw [FiniteThreeLevelEnvironmentLift.swap_tensor, lift_branch_tensor, readout_branch]
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [mul_assoc]

/-- Every one of the 27 branches is a scalar times its actual rank-one output. -/
theorem measured_run (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (a c j : Q) :
    measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip (a,c,j,()) =
      if c = 0 then ((R φ₁ φ₂ j * evolved b ℏ γ t r (signalLabel flip a)).trace / 3) •
        (R φ₁ φ₂ j ⊗ₖ projector (0 : Q)) else 0 := by
  change (readStep φ₁ φ₂).branch Q Q 3 j
    (memoryFamily b ℏ γ t r hγ ht flip (a,c,())) = _
  rw [memory_run]
  split_ifs
  · rw [Step.branch_smul, readStep_tensor, smul_smul]
    congr 1
    ring
  · simp [Step.branch, krausMap, FiniteInstrument.branch]

theorem measured_valid (b ℏ γ t φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (flip : Bool) :
    IsBranchFamily (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip) :=
  run_family _ (input_density hr hr1)

theorem rotate_comp (φ₁ φ₂ ψ₁ ψ₂ : ℝ) (X : MatQ) :
    rotate φ₁ φ₂ (rotate ψ₁ ψ₂ X) = rotate (φ₁+ψ₁) (φ₂+ψ₂) X := by
  ext i j
  simp only [rotate_entry, ← mul_assoc, ← Complex.exp_add]
  congr 2
  have he (k : Q) : frameLevels (φ₁+ψ₁) (φ₂+ψ₂) k =
      frameLevels φ₁ φ₂ k + frameLevels ψ₁ ψ₂ k := by fin_cases k <;> simp [frameLevels]
  simp only [he, Complex.ofReal_add]
  ring

theorem relative_trace (φ₁ φ₂ θ₁ θ₂ : ℝ) (a j : Q) :
    (R φ₁ φ₂ j * R θ₁ θ₂ a).trace =
      (P j * rotate (θ₁-φ₁) (θ₂-φ₂) (P a)).trace := by
  rw [← rotate_trace φ₁ φ₂ (P j * rotate (θ₁-φ₁) (θ₂-φ₂) (P a)), rotate_mul,
    rotate_comp]
  congr 2; congr 1 <;> ring

def theta₁ (b ℏ t : ℝ) : ℝ := t * (Real.log (3/2) / b / ℏ)
def theta₂ (b ℏ t : ℝ) : ℝ := t * (Real.log 3 / b / ℏ)

theorem phase_rotate (b ℏ t : ℝ) (X : MatQ) :
    FiniteThreeLevelThermalPhase.phase b ℏ t X = rotate (theta₁ b ℏ t) (theta₂ b ℏ t) X := by
  ext i j
  rw [FiniteThreeLevelThermalPhase.phase_entry, rotate_entry]
  congr 2
  have he (k : Q) : frameLevels (theta₁ b ℏ t) (theta₂ b ℏ t) k =
      t * FiniteThreeLevelThermalPhase.frequencies b ℏ k := by
    fin_cases k <;> simp [theta₁, theta₂, frameLevels,
      FiniteThreeLevelThermalPhase.frequencies, FiniteThreeLevelThermalPhase.energies,
      FiniteThreeLevelThermalPhase.delta]
  simp only [he, Complex.ofReal_mul]
  ring

theorem evolved_formula (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (a : Q) :
    evolved b ℏ γ t r a = if a.val = 2 then equilibrium else
      mixture (retention r γ t) (R (theta₁ b ℏ t) (theta₂ b ℏ t) a) := by
  unfold evolved sigma
  split_ifs
  · exact FiniteThreeLevelThermalPhase.channel_stationary b ℏ γ t hγ ht
  · rw [FiniteThreeLevelThermalPhase.evolved_mixture b ℏ γ t r hγ ht (P_density a), phase_rotate]
    rfl

theorem evolved_trace (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (a : Q) :
    (evolved b ℏ γ t r a).trace = 1 := by
  rw [evolved, trace_krausMap (FiniteThreeLevelThermalPhase.channel_normalized b ℏ γ t hγ ht), sigma_trace]

theorem exp_pos_angle (x : ℝ) : Complex.exp (Complex.I*x) =
    (Real.cos x:ℂ) + (Real.sin x:ℂ)*Complex.I := by
  rw [mul_comm, Complex.exp_mul_I]
  simp

theorem exp_neg_angle (x : ℝ) : Complex.exp (-(Complex.I*x)) =
    (Real.cos x:ℂ) - (Real.sin x:ℂ)*Complex.I := by
  simpa [sub_eq_add_neg] using exp_pos_angle (-x)

/-- Signed interference of the distinct physical 01 and 02 gaps. -/
def contrast (d₁ d₂ : ℝ) : ℝ := (9*Real.cos d₁ + 16*Real.cos d₂)/25
def darkOverlap (d₁ d₂ : ℝ) : ℝ := 144/625*(1-Real.cos (d₁-d₂))
def signalOverlap (d₁ d₂ : ℝ) (same : Bool) : ℝ :=
  481/1250 + 72/625*Real.cos (d₁-d₂) + (if same then 1 else -1)*contrast d₁ d₂/2
def gibbsProbability (j : Q) : ℝ := if j.val = 2 then 41/150 else 109/300
def probability (q d₁ d₂ : ℝ) (a j : Q) : ℝ :=
  if a.val = 2 then gibbsProbability j else
    (1-q)*gibbsProbability j + q*(if j.val = 2 then darkOverlap d₁ d₂
      else signalOverlap d₁ d₂ (decide (a.val = j.val)))

theorem rotated_gibbs_trace (φ₁ φ₂ : ℝ) (j : Q) :
    (R φ₁ φ₂ j * equilibrium).trace = (gibbsProbability j:ℂ) := by
  fin_cases j <;>
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, R, rotate_entry]
  all_goals norm_num [P, equilibrium, density, three, GibbsReset.threeWeights,
    gibbsProbability, frameLevels, Matrix.cons_val_two, Matrix.diagonal_apply, Fin.ext_iff]

private theorem overlap_zero (d₁ d₂ : ℝ) (j : Q) :
    (P j * rotate d₁ d₂ (P 0)).trace =
      ((if j.val = 2 then darkOverlap d₁ d₂ else signalOverlap d₁ d₂ (decide (j.val = 0))):ℝ) := by
  fin_cases j <;>
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, rotate_entry]
  all_goals norm_num [P, frameLevels, Matrix.cons_val_two, exp_neg_angle, exp_pos_angle,
    contrast, darkOverlap, signalOverlap, ← Complex.ofReal_sub]
  all_goals push_cast
  all_goals simp only [Complex.cos_sub, Complex.sin_sub]
  all_goals ring

private theorem overlap_one (d₁ d₂ : ℝ) (j : Q) :
    (P j * rotate d₁ d₂ (P 1)).trace =
      ((if j.val = 2 then darkOverlap d₁ d₂ else signalOverlap d₁ d₂ (decide (j.val = 1))):ℝ) := by
  fin_cases j <;>
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, rotate_entry]
  all_goals norm_num [P, frameLevels, Matrix.cons_val_two, exp_neg_angle, exp_pos_angle,
    contrast, darkOverlap, signalOverlap, ← Complex.ofReal_sub]
  all_goals push_cast
  all_goals simp only [Complex.cos_sub, Complex.sin_sub]
  all_goals ring

theorem trace_probability (q θ₁ θ₂ φ₁ φ₂ : ℝ) (a j : Q) :
    (R φ₁ φ₂ j * (if a.val = 2 then equilibrium else mixture q (R θ₁ θ₂ a))).trace =
      (probability q (θ₁-φ₁) (θ₂-φ₂) a j : ℂ) := by
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl
  · simp only [show (0 : Q).val = 0 from rfl, show (0 : ℕ) ≠ 2 by decide, if_false,
      mixture, mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      rotated_gibbs_trace, relative_trace, overlap_zero]
    fin_cases j <;> norm_num [probability, gibbsProbability]
  · simp only [show (1 : Q).val = 1 from rfl, show (1 : ℕ) ≠ 2 by decide, if_false,
      mixture, mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      rotated_gibbs_trace, relative_trace, overlap_one]
    fin_cases j <;> norm_num [probability, gibbsProbability]
  · simpa [probability] using rotated_gibbs_trace φ₁ φ₂ j

theorem evolved_probability (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (a j : Q) :
    (R φ₁ φ₂ j * evolved b ℏ γ t r a).trace =
      (probability (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) a j:ℂ) := by
  rw [evolved_formula b ℏ γ t r hγ ht, trace_probability]

theorem probability_sum (q d₁ d₂ : ℝ) (a : Q) : ∑ j, probability q d₁ d₂ a j = 1 := by
  fin_cases a <;> norm_num [probability, gibbsProbability, signalOverlap, darkOverlap,
    contrast, Fin.sum_univ_succ] <;> ring

/-- The complete physical probability table retains all impossible branches. -/
def mass (q d₁ d₂ : ℝ) (flip : Bool) (a c j : Q) : ℝ :=
  if c = 0 then probability q d₁ d₂ (signalLabel flip a) j / 3 else 0

theorem measured_matrices (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (a c j : Q) :
    measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip (a,c,j,()) =
      (mass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) flip a c j:ℂ) •
        (R φ₁ φ₂ j ⊗ₖ projector (0 : Q)) := by
  rw [measured_run, evolved_probability b ℏ γ t r φ₁ φ₂ hγ ht]
  unfold mass
  split_ifs <;> simp

theorem measured_traces (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (a c j : Q) :
    (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip (a,c,j,())).trace =
      (mass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) flip a c j:ℂ) := by
  rw [measured_matrices, Matrix.trace_smul, Matrix.trace_kronecker, R_trace, projector_trace]
  simp

theorem mass_normalized (q d₁ d₂ : ℝ) (flip : Bool) :
    ∑ a : Q, ∑ c : Q, ∑ j : Q, mass q d₁ d₂ flip a c j = 1 := by
  simp only [mass]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero, ← Finset.sum_div, probability_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  norm_num [Fin.sum_univ_succ]

theorem memory_trace (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (a c : Q) :
    (memoryFamily b ℏ γ t r hγ ht flip (a,c,())).trace = if c = 0 then 1/3 else 0 := by
  rw [memory_run]
  split_ifs <;> simp [Matrix.trace_smul, Matrix.trace_kronecker, projector_trace,
    evolved_trace b ℏ γ t r hγ ht]

theorem memory_same_history (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (h : History 3 2) :
    (memoryFamily b ℏ γ t r hγ ht false h).trace.re =
      (memoryFamily b ℏ γ t r hγ ht true h).trace.re := by
  rcases h with ⟨a,c,⟨⟩⟩
  rw [memory_trace, memory_trace]

theorem memory_history_error (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (rule : History 3 2 → ℝ) :
    historyError (memoryFamily b ℏ γ t r hγ ht false) (memoryFamily b ℏ γ t r hγ ht true) rule = 1/2 :=
  historyError_same_law (memory_valid b ℏ γ t hγ ht hr hr1 false)
    (memory_same_history b ℏ γ t r hγ ht) rule

theorem memory_marginal (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (a c : Q) :
    FiniteThreeLevelEnvironmentLift.ptrace2 (memoryFamily b ℏ γ t r hγ ht flip (a,c,())) =
      if c = 0 then (1/3:ℂ) • projector (0 : Q) else 0 := by
  rw [memory_run]
  split_ifs
  · rw [FiniteThreeLevelEnvironmentLift.ptrace2_smul,
      FiniteThreeLevelEnvironmentLift.ptrace2_kronecker, evolved_trace b ℏ γ t r hγ ht, one_smul]
  · ext i j; simp [FiniteThreeLevelEnvironmentLift.ptrace2]

def basis : MatQ := fun i a => v a i

theorem basis_unitary : basis ∈ Matrix.unitaryGroup Q ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change basisᴴ * basis = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basis, v, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      map_ofNat, FiniteThreeLevelThermalPhase.s_conj, Matrix.one_apply,
      Matrix.cons_val_two] <;>
    ring_nf <;> norm_num [map_ofNat, show FiniteThreeLevelThermalPhase.s^2 = 1/2 by
      simpa [pow_two] using FiniteThreeLevelThermalPhase.s_square]

theorem basis_projector (a : Q) : FiniteThreeLevelThermalPhase.conjugate basis (projector a) = P a := by
  rw [v_rank_one]
  ext i j
  rw [FiniteThreeLevelThermalPhase.conjugate_projector_entry]
  rfl

theorem P_distance : traceDist (P 0) (P 1) = 1 := by
  rw [← basis_projector, ← basis_projector,
    FiniteThreeLevelThermalPhase.conjugate_distance basis_unitary
      (FiniteAdaptiveGibbsReadout.projector_density 0).1.isHermitian
      (FiniteAdaptiveGibbsReadout.projector_density 1).1.isHermitian]
  exact FiniteAdaptiveGibbsReadout.projector_pair_distance

def D : MatQ := P 0 - P 1
theorem D_entries : D = !![0,3/5,4/5;3/5,0,0;4/5,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [D, P]

theorem D_spectral (a : Q) : D * P a = ((if a.val = 0 then 1 else if a.val = 1 then -1 else 0):ℂ) • P a := by
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl <;>
    norm_num [D, sub_mul, P_square, P_orthogonal _ _ (by decide : (0:Q) ≠ 1),
      P_orthogonal _ _ (by decide : (1:Q) ≠ 0),
      P_orthogonal _ _ (by decide : (0:Q) ≠ 2),
      P_orthogonal _ _ (by decide : (1:Q) ≠ 2)]

theorem D_norm : traceNorm D = 2 := by
  have h := P_distance
  unfold traceDist at h
  change 1 / 2 * traceNorm D = 1 at h
  linarith

theorem evolved_signal_distance (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) :
    traceDist (evolved b ℏ γ t r 0) (evolved b ℏ γ t r 1) = retention r γ t := by
  have h0 : sigma r 0 = mixture r (P 0) := by simp [sigma]
  have h1 : sigma r 1 = mixture r (P 1) := by simp [sigma]
  rw [evolved, evolved, h0, h1,
    FiniteThreeLevelThermalPhase.evolved_mixture b ℏ γ t r hγ ht (P_density 0),
    FiniteThreeLevelThermalPhase.evolved_mixture b ℏ γ t r hγ ht (P_density 1),
    FiniteThreeLevelThermalPhase.mixture_distance (FiniteThreeLevelThermalPhase.retention_nonneg hr γ t),
    FiniteThreeLevelThermalPhase.phase_distance b ℏ t (P_hermitian 0) (P_hermitian 1), P_distance, mul_one]

theorem left_tensor_distance (T A B : MatQ) (hT : IsDensityOperator T) :
    traceDist (T ⊗ₖ A) (T ⊗ₖ B) = traceDist A B := by
  unfold traceDist
  have hs : T ⊗ₖ A - T ⊗ₖ B = T ⊗ₖ (A-B) := by
    ext ⟨i,j⟩ ⟨k,l⟩; simp [mul_sub]
  rw [hs, traceNorm_kronecker, traceNorm_density_eq_one hT, one_mul]

theorem third_distance (X Y : MatJoint) : traceDist ((1/3:ℂ) • X) ((1/3:ℂ) • Y) = traceDist X Y / 3 := by
  unfold traceDist
  rw [← smul_sub]
  have h := traceNorm_smul_nonneg (show (0:ℝ) ≤ 1/3 by norm_num) (X-Y)
  norm_num at h
  rw [h]
  ring

theorem memory_run_history (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (h : History 3 2) :
    memoryFamily b ℏ γ t r hγ ht flip h =
      if h.2.1 = 0 then (1/3:ℂ) • (projector (0:Q) ⊗ₖ
        evolved b ℏ γ t r (signalLabel flip h.1)) else 0 := by
  rcases h with ⟨a,c,⟨⟩⟩
  exact memory_run b ℏ γ t r hγ ht flip a c

theorem memory_distance (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) :
    branchDistance (memoryFamily b ℏ γ t r hγ ht false) (memoryFamily b ℏ γ t r hγ ht true) =
      2*retention r γ t/3 := by
  unfold branchDistance
  simp only [memory_run_history]
  change (∑ h : Q × Q × Unit, traceDist
    (if h.2.1 = 0 then (1/3:ℂ) • (projector (0:Q) ⊗ₖ evolved b ℏ γ t r (signalLabel false h.1)) else 0)
    (if h.2.1 = 0 then (1/3:ℂ) • (projector (0:Q) ⊗ₖ evolved b ℏ γ t r (signalLabel true h.1)) else 0)) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  have hc (a : Q) : (∑ c : Q, traceDist
      (if c = 0 then (1/3:ℂ) • (projector (0:Q) ⊗ₖ evolved b ℏ γ t r (signalLabel false a)) else 0)
      (if c = 0 then (1/3:ℂ) • (projector (0:Q) ⊗ₖ evolved b ℏ γ t r (signalLabel true a)) else 0)) =
      traceDist (evolved b ℏ γ t r a) (evolved b ℏ γ t r (exchange a)) / 3 := by
    simp only [signalLabel, Bool.false_eq_true, if_false, if_true]
    simp only [apply_ite₂, traceDist_self]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, third_distance,
      left_tensor_distance _ _ _ (FiniteAdaptiveGibbsReadout.projector_density 0)]
  simp_rw [hc]
  have hd := evolved_signal_distance b ℏ γ t hγ ht hr
  have hd' : traceDist (evolved b ℏ γ t r 1) (evolved b ℏ γ t r 0) = retention r γ t := by
    rw [traceDist_comm]; exact hd
  norm_num [Fin.sum_univ_succ, exchange, traceDist_self, hd, hd']
  ring

theorem memory_physical_isLeast (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsLeast (FiniteThreeLevelEnvironmentLift.PhysicalErrors
      (memoryFamily b ℏ γ t r hγ ht false) (memoryFamily b ℏ γ t r hγ ht true))
      (1/2-retention r γ t/3) := by
  have h := FiniteThreeLevelEnvironmentLift.physical_isLeast
    (memory_valid b ℏ γ t hγ ht hr hr1 false) (memory_valid b ℏ γ t hγ ht hr hr1 true)
  rw [memory_distance b ℏ γ t hγ ht hr] at h
  convert h using 1
  ring

abbrev MemoryHist := History 3 2
abbrev MeasuredHist := History 3 3

theorem mass_difference (q d₁ d₂ : ℝ) (a c j : Q) :
    mass q d₁ d₂ false a c j - mass q d₁ d₂ true a c j =
      if c = 0 ∧ a.val ≠ 2 ∧ j.val ≠ 2 then
        (if a.val = j.val then 1 else -1)*q*contrast d₁ d₂/3 else 0 := by
  fin_cases a <;> fin_cases c <;> fin_cases j <;>
    norm_num [mass, probability, signalLabel, exchange, signalOverlap] <;> ring

theorem mass_abs_sum {q : ℝ} (hq : 0 ≤ q) (d₁ d₂ : ℝ) :
    ∑ a : Q, ∑ c : Q, ∑ j : Q,
      |mass q d₁ d₂ false a c j - mass q d₁ d₂ true a c j| =
        4*q*|contrast d₁ d₂|/3 := by
  simp only [mass_difference]
  norm_num [Fin.sum_univ_succ, abs_div, abs_mul, abs_of_nonneg hq]
  ring

theorem measured_trace_history (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (h : MeasuredHist) :
    (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip h).trace =
      (mass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) flip h.1 h.2.1 h.2.2.1:ℂ) := by
  rcases h with ⟨a,c,j,⟨⟩⟩
  exact measured_traces b ℏ γ t r φ₁ φ₂ hγ ht flip a c j

theorem measured_leaf_distance (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (h : MeasuredHist) :
    traceDist (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false h)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true h) =
      |mass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) false h.1 h.2.1 h.2.2.1 -
       mass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) true h.1 h.2.1 h.2.2.1|/2 := by
  rcases h with ⟨a,c,j,⟨⟩⟩
  rw [measured_matrices, measured_matrices]
  unfold traceDist
  rw [← sub_smul, ← Complex.ofReal_sub, traceNorm_eq_physlib, Matrix.traceNorm_smul,
    ← traceNorm_eq_physlib, traceNorm_kronecker, traceNorm_density_eq_one (R_density φ₁ φ₂ j),
    traceNorm_density_eq_one (FiniteAdaptiveGibbsReadout.projector_density 0), Complex.norm_real,
    Real.norm_eq_abs]
  ring

theorem measured_distance (b ℏ γ t φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) :
    branchDistance (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true) =
      2*retention r γ t*|contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)|/3 := by
  unfold branchDistance
  simp only [measured_leaf_distance]
  change (∑ h : Q × Q × Q × Unit, |mass _ _ _ false h.1 h.2.1 h.2.2.1 -
    mass _ _ _ true h.1 h.2.1 h.2.2.1|/2) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, ← Finset.sum_div]
  rw [mass_abs_sum (FiniteThreeLevelThermalPhase.retention_nonneg hr γ t)]
  ring

theorem measured_variation (b ℏ γ t φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) :
    familyHistoryVariation (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true) =
      2*retention r γ t*|contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)|/3 := by
  unfold familyHistoryVariation
  simp only [measured_trace_history, Complex.ofReal_re]
  change (∑ h : Q × Q × Q × Unit, |mass _ _ _ false h.1 h.2.1 h.2.2.1 -
    mass _ _ _ true h.1 h.2.1 h.2.2.1|)/2 = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  rw [mass_abs_sum (FiniteThreeLevelThermalPhase.retention_nonneg hr γ t)]
  ring

/-- Both dark outcomes and the Gibbs-only initial label choose A on ties. -/
def choosesA (rev : Bool) (a j : Q) : Prop :=
  a.val = 2 ∨ j.val = 2 ∨ (if rev then a.val ≠ j.val else a.val = j.val)
instance (rev : Bool) (a j : Q) : Decidable (choosesA rev a j) := by
  unfold choosesA; infer_instance

def score (rev : Bool) (h : MeasuredHist) : ℝ :=
  if h.2.1 ≠ 0 ∨ choosesA rev h.1 h.2.2.1 then 1 else 0
def decisionProjection (rev : Bool) (h : MeasuredHist) : MatJoint :=
  if h.2.1 ≠ 0 ∨ choosesA rev h.1 h.2.2.1 then 1 else 0

theorem decisionProjection_hermitian (rev : Bool) (h : MeasuredHist) :
    (decisionProjection rev h).IsHermitian := by
  unfold decisionProjection; split_ifs <;> simp

theorem decisionProjection_square (rev : Bool) (h : MeasuredHist) :
    decisionProjection rev h * decisionProjection rev h = decisionProjection rev h := by
  unfold decisionProjection; split_ifs <;> simp

def decisionReadout (rev : Bool) (h : MeasuredHist) : FiniteInstrument Joint 2 :=
  projectiveReadout (decisionProjection rev h) (decisionProjection_hermitian rev h)
    (decisionProjection_square rev h)

theorem decision_weight (rev : Bool) (h : MeasuredHist) (d : Fin 2) (X : MatJoint) :
    (decisionReadout rev h).weight d X = (if d = 0 then score rev h else 1-score rev h)*X.trace.re := by
  have hd : d = 0 ∨ d = 1 := by fin_cases d <;> decide
  rcases hd with rfl | rfl
  all_goals simp only [decisionReadout, projectiveReadout_weight_zero, projectiveReadout_weight_one]
  all_goals unfold decisionProjection score
  all_goals split_ifs <;> simp_all

theorem score_admissible (rev : Bool) (h : MeasuredHist) : score rev h ∈ Set.Icc (0:ℝ) 1 := by
  unfold score; split_ifs <;> norm_num

theorem score_error (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (rev : Bool) :
    historyError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true) (score rev) =
      1/2 - (if rev then -1 else 1)*retention r γ t*
        contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)/3 := by
  rw [historyError_eq (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 false)]
  simp only [measured_trace_history, Complex.ofReal_re, score, mass_difference]
  change (1 - ∑ h : Q × Q × Q × Unit,
    (if h.2.1 ≠ 0 ∨ choosesA rev h.1 h.2.2.1 then 1 else 0) *
    (if h.2.1 = 0 ∧ h.1.val ≠ 2 ∧ h.2.2.1.val ≠ 2 then
      (if h.1.val = h.2.2.1.val then 1 else -1)*retention r γ t*
      contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)/3 else 0))/2 = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  cases rev <;> norm_num [Fin.sum_univ_succ, choosesA] <;> ring

theorem decision_error (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (rev : Bool) :
    instrumentError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true) (decisionReadout rev) =
      1/2 - (if rev then -1 else 1)*retention r γ t*
        contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)/3 := by
  have he : instrumentError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true) (decisionReadout rev) =
      historyError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
        (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true) (score rev) := by
    simp [instrumentError, readoutTable, decision_weight, historyError]
  rw [he, score_error b ℏ γ t r φ₁ φ₂ hγ ht hr hr1]

def optimalReversal (d₁ d₂ : ℝ) : Bool := decide (contrast d₁ d₂ < 0)

/-- The optimal rule sends every equal-mass history to outcome zero. -/
def optimalScore (q d₁ d₂ : ℝ) (h : MeasuredHist) : ℝ :=
  if mass q d₁ d₂ false h.1 h.2.1 h.2.2.1 = mass q d₁ d₂ true h.1 h.2.1 h.2.2.1
  then 1 else score (optimalReversal d₁ d₂) h

def optimalDecisionProjection (q d₁ d₂ : ℝ) (h : MeasuredHist) : MatJoint :=
  if mass q d₁ d₂ false h.1 h.2.1 h.2.2.1 = mass q d₁ d₂ true h.1 h.2.1 h.2.2.1
  then 1 else decisionProjection (optimalReversal d₁ d₂) h

theorem optimalDecisionProjection_hermitian (q d₁ d₂ : ℝ) (h : MeasuredHist) :
    (optimalDecisionProjection q d₁ d₂ h).IsHermitian := by
  unfold optimalDecisionProjection
  split_ifs
  · exact Matrix.isHermitian_one
  · exact decisionProjection_hermitian _ _

theorem optimalDecisionProjection_square (q d₁ d₂ : ℝ) (h : MeasuredHist) :
    optimalDecisionProjection q d₁ d₂ h * optimalDecisionProjection q d₁ d₂ h =
      optimalDecisionProjection q d₁ d₂ h := by
  unfold optimalDecisionProjection
  split_ifs
  · simp
  · exact decisionProjection_square _ _

def optimalDecisionReadout (q d₁ d₂ : ℝ) (h : MeasuredHist) : FiniteInstrument Joint 2 :=
  projectiveReadout (optimalDecisionProjection q d₁ d₂ h)
    (optimalDecisionProjection_hermitian q d₁ d₂ h) (optimalDecisionProjection_square q d₁ d₂ h)

theorem optimal_decision_weight (q d₁ d₂ : ℝ) (h : MeasuredHist) (d : Fin 2) (X : MatJoint) :
    (optimalDecisionReadout q d₁ d₂ h).weight d X =
      (if d = 0 then optimalScore q d₁ d₂ h else 1-optimalScore q d₁ d₂ h)*X.trace.re := by
  have hd : d = 0 ∨ d = 1 := by fin_cases d <;> decide
  rcases hd with rfl | rfl
  all_goals simp only [optimalDecisionReadout, projectiveReadout_weight_zero, projectiveReadout_weight_one]
  all_goals unfold optimalDecisionProjection optimalScore decisionProjection score
  all_goals split_ifs <;> simp_all

theorem optimal_decision_ties_A (q d₁ d₂ : ℝ) (h : MeasuredHist)
    (heq : mass q d₁ d₂ false h.1 h.2.1 h.2.2.1 = mass q d₁ d₂ true h.1 h.2.1 h.2.2.1) :
    optimalDecisionProjection q d₁ d₂ h = 1 ∧ optimalScore q d₁ d₂ h = 1 := by
  simp [optimalDecisionProjection, optimalScore, heq]

theorem optimal_score_error (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    historyError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true)
      (optimalScore (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)) =
    historyError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true)
      (score (optimalReversal (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))) := by
  rw [historyError_eq (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 false),
    historyError_eq (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 false)]
  congr 2
  apply Finset.sum_congr rfl
  intro h _
  simp only [measured_trace_history, Complex.ofReal_re, optimalScore]
  split_ifs with heq
  · simp [heq]
  · rfl

theorem measured_attainer (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    instrumentError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true)
      (optimalDecisionReadout (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)) =
      1/2-retention r γ t*|contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)|/3 := by
  simp only [instrumentError, readoutTable, optimal_decision_weight]
  change historyError _ _ (optimalScore _ _ _) = _
  rw [optimal_score_error b ℏ γ t r φ₁ φ₂ hγ ht hr hr1,
    score_error b ℏ γ t r φ₁ φ₂ hγ ht hr hr1]
  by_cases h : contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) < 0
  · simp [optimalReversal, h, abs_of_neg h]
  · simp [optimalReversal, h, abs_of_nonneg (le_of_not_gt h)]

theorem measured_physical_isLeast (b ℏ γ t φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsLeast (FiniteThreeLevelEnvironmentLift.PhysicalErrors
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true))
      (1/2-retention r γ t*|contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)|/3) := by
  refine ⟨⟨optimalDecisionReadout (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂),
    measured_attainer b ℏ γ t r φ₁ φ₂ hγ ht hr hr1⟩, ?_⟩
  have hh := (FiniteThreeLevelEnvironmentLift.physical_isLeast
    (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 false)
    (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 true)).2
  rw [measured_distance b ℏ γ t φ₁ φ₂ hγ ht hr] at hh
  convert hh using 1
  ring

theorem measured_all_effect_isLeast (b ℏ γ t φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsLeast {x : ℝ | ∃ E : MeasuredHist → MatJoint, (∀ h, IsBinaryPOVM (E h)) ∧
      readoutError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
        (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true) E = x}
      (1/2-retention r γ t*|contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)|/3) := by
  have hh := readoutError_isLeast (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 false)
    (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 true)
  rw [measured_distance b ℏ γ t φ₁ φ₂ hγ ht hr] at hh
  convert hh using 1
  ring

theorem measured_randomized_isLeast (b ℏ γ t φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsLeast {x : ℝ | ∃ f : MeasuredHist → ℝ, (∀ h, f h ∈ Set.Icc (0:ℝ) 1) ∧
      historyError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
        (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true) f = x}
      (1/2-retention r γ t*|contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)|/3) := by
  have hh := historyError_isLeast (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 false)
    (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 true)
  rw [measured_variation b ℏ γ t φ₁ φ₂ hγ ht hr] at hh
  convert hh using 1
  ring

/-- All 54 history/decision entries, including every zero-weight history. -/
theorem decision_table (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip rev : Bool) (h : MeasuredHist) (d : Fin 2) :
    readoutTable (decisionReadout rev) (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip) h d =
      (if d = 0 then score rev h else 1-score rev h)*
      mass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) flip h.1 h.2.1 h.2.2.1 := by
  rw [readoutTable, decision_weight, measured_trace_history, Complex.ofReal_re]

theorem decision_table_laws (b ℏ γ t φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (flip rev : Bool) :
    (∀ h d, 0 ≤ readoutTable (decisionReadout rev)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip) h d) ∧
    (∑ h, ∑ d, readoutTable (decisionReadout rev)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip) h d) = 1 :=
  ⟨readoutTable_nonneg _ (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 flip),
    readoutTable_total _ (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 flip)⟩

/-- Every entry of the optimal binary table, including all degenerate ties. -/
theorem optimal_decision_table (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (h : MeasuredHist) (d : Fin 2) :
    readoutTable (optimalDecisionReadout (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip) h d =
      (if d = 0 then optimalScore (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) h
        else 1-optimalScore (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) h)*
      mass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) flip h.1 h.2.1 h.2.2.1 := by
  rw [readoutTable, optimal_decision_weight, measured_trace_history, Complex.ofReal_re]

theorem optimal_decision_table_laws (b ℏ γ t φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (flip : Bool) :
    (∀ h d, 0 ≤ readoutTable
      (optimalDecisionReadout (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip) h d) ∧
    (∑ h, ∑ d, readoutTable
      (optimalDecisionReadout (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip) h d) = 1 :=
  ⟨readoutTable_nonneg _ (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 flip),
    readoutTable_total _ (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 flip)⟩

theorem optimal_decision_non_tie (q d₁ d₂ : ℝ) (h : MeasuredHist)
    (hne : mass q d₁ d₂ false h.1 h.2.1 h.2.2.1 ≠ mass q d₁ d₂ true h.1 h.2.1 h.2.2.1) :
    optimalDecisionProjection q d₁ d₂ h = decisionProjection (optimalReversal d₁ d₂) h ∧
    optimalScore q d₁ d₂ h = score (optimalReversal d₁ d₂) h := by
  simp [optimalDecisionProjection, optimalScore, hne]

theorem optimal_actual_ties_A (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (h : MeasuredHist)
    (heq : (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false h).trace.re =
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true h).trace.re) :
    optimalDecisionProjection (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) h = 1 ∧
    optimalScore (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) h = 1 := by
  simp only [measured_trace_history, Complex.ofReal_re] at heq
  exact optimal_decision_ties_A _ _ _ _ heq

theorem optimal_zero_signal_ties_A (q d₁ d₂ : ℝ) (hzero : q*contrast d₁ d₂ = 0)
    (h : MeasuredHist) :
    optimalDecisionProjection q d₁ d₂ h = 1 ∧ optimalScore q d₁ d₂ h = 1 := by
  apply optimal_decision_ties_A
  apply sub_eq_zero.mp
  rw [mass_difference]
  split_ifs <;> simp_all

theorem optimal_zero_retention_ties_A (d₁ d₂ : ℝ) (h : MeasuredHist) :
    optimalDecisionProjection 0 d₁ d₂ h = 1 ∧ optimalScore 0 d₁ d₂ h = 1 :=
  optimal_zero_signal_ties_A 0 d₁ d₂ (by simp) h

theorem optimal_zero_contrast_ties_A (q d₁ d₂ : ℝ) (hC : contrast d₁ d₂ = 0)
    (h : MeasuredHist) :
    optimalDecisionProjection q d₁ d₂ h = 1 ∧ optimalScore q d₁ d₂ h = 1 :=
  optimal_zero_signal_ties_A q d₁ d₂ (by rw [hC, mul_zero]) h

theorem optimal_structural_ties_A (q d₁ d₂ : ℝ) (h : MeasuredHist)
    (hstruct : h.2.1 ≠ 0 ∨ h.1.val = 2 ∨ h.2.2.1.val = 2) :
    optimalDecisionProjection q d₁ d₂ h = 1 ∧ optimalScore q d₁ d₂ h = 1 := by
  apply optimal_decision_ties_A
  apply sub_eq_zero.mp
  rw [mass_difference]
  rcases hstruct with hc | ha | hj <;> simp_all

theorem optimal_actual_tie_columns (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (h : MeasuredHist)
    (heq : (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false h).trace.re =
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true h).trace.re) (flip : Bool) :
    readoutTable (optimalDecisionReadout (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip) h 0 =
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip h).trace.re ∧
    readoutTable (optimalDecisionReadout (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip) h 1 = 0 := by
  have hs := (optimal_actual_ties_A b ℏ γ t r φ₁ φ₂ hγ ht h heq).2
  simp [readoutTable, optimal_decision_weight, hs]

theorem optimal_score_admissible (q d₁ d₂ : ℝ) (h : MeasuredHist) :
    optimalScore q d₁ d₂ h ∈ Set.Icc (0:ℝ) 1 := by
  unfold optimalScore
  split_ifs
  · norm_num
  · exact score_admissible _ _

theorem optimal_zero_preparation_ties_A (b ℏ γ t φ₁ φ₂ : ℝ) (h : MeasuredHist) :
    optimalDecisionProjection (retention 0 γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) h = 1 ∧
    optimalScore (retention 0 γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) h = 1 := by
  simpa [retention] using optimal_zero_retention_ties_A (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) h

/-- A zero signal sends every original branch mass to the A column, including zeros. -/
theorem optimal_degenerate_table (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hzero : retention r γ t * contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) = 0)
    (flip : Bool) (h : MeasuredHist) (d : Fin 2) :
    readoutTable (optimalDecisionReadout (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂))
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip) h d =
      if d = 0 then mass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)
        flip h.1 h.2.1 h.2.2.1 else 0 := by
  rw [optimal_decision_table, (optimal_zero_signal_ties_A _ _ _ hzero h).2]
  split_ifs <;> simp

def rejected (rev : Bool) (a : Q) : Q := if rev then a else exchange a
def groupProjection (φ₁ φ₂ : ℝ) (rev : Bool) (a : Q) : MatQ :=
  if a.val = 2 then 1 else 1-R φ₁ φ₂ (rejected rev a)

theorem groupProjection_hermitian (φ₁ φ₂ : ℝ) (rev : Bool) (a : Q) :
    (groupProjection φ₁ φ₂ rev a).IsHermitian := by
  unfold groupProjection
  split_ifs
  · exact Matrix.isHermitian_one
  · exact Matrix.isHermitian_one.sub (R_hermitian _ _ _)

theorem groupProjection_square (φ₁ φ₂ : ℝ) (rev : Bool) (a : Q) :
    groupProjection φ₁ φ₂ rev a * groupProjection φ₁ φ₂ rev a = groupProjection φ₁ φ₂ rev a := by
  unfold groupProjection
  split_ifs
  · simp
  · simp only [sub_mul, mul_sub, one_mul, mul_one, R_square]
    abel

theorem accept_sum (φ₁ φ₂ : ℝ) (rev : Bool) (a : Q) :
    (∑ j, if choosesA rev a j then R φ₁ φ₂ j else 0) = groupProjection φ₁ φ₂ rev a := by
  have hs := R_sum φ₁ φ₂
  norm_num [Fin.sum_univ_succ] at hs
  cases rev <;> fin_cases a <;>
    norm_num [Fin.sum_univ_succ, choosesA, groupProjection, rejected, exchange]
  all_goals rw [← hs]
  all_goals abel

def groupedEffect (φ₁ φ₂ : ℝ) (rev : Bool) (h : MemoryHist) : MatJoint :=
  (1 : MatQ) ⊗ₖ groupProjection φ₁ φ₂ rev h.1

theorem groupedEffect_hermitian (φ₁ φ₂ : ℝ) (rev : Bool) (h : MemoryHist) :
    (groupedEffect φ₁ φ₂ rev h).IsHermitian :=
by
  change (groupedEffect φ₁ φ₂ rev h)ᴴ = groupedEffect φ₁ φ₂ rev h
  simp only [groupedEffect, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    (groupProjection_hermitian φ₁ φ₂ rev h.1).eq]

theorem groupedEffect_square (φ₁ φ₂ : ℝ) (rev : Bool) (h : MemoryHist) :
    groupedEffect φ₁ φ₂ rev h * groupedEffect φ₁ φ₂ rev h = groupedEffect φ₁ φ₂ rev h := by
  simp only [groupedEffect, ← Matrix.mul_kronecker_mul, one_mul, groupProjection_square]

def groupedReadout (φ₁ φ₂ : ℝ) (rev : Bool) (h : MemoryHist) : FiniteInstrument Joint 2 :=
  projectiveReadout (groupedEffect φ₁ φ₂ rev h) (groupedEffect_hermitian _ _ _ _)
    (groupedEffect_square _ _ _ _)

def sequentialOp (φ₁ φ₂ : ℝ) (rev : Bool) (a : Q) (d : Fin 2) (j : Q) : MatJoint :=
  if (choosesA rev a j ↔ d = 0) then (R φ₁ φ₂ j ⊗ₖ (1:MatQ))*swapMat 3 else 0

theorem swap_sandwich (A B : MatQ) :
    swapMat 3 * (A ⊗ₖ B) * swapMat 3 = B ⊗ₖ A := by
  simpa only [FiniteThreeLevelEnvironmentLift.swap, krausMap,
    FiniteThreeLevelEnvironmentLift.swapKraus, Fin.sum_univ_one, swapMat_isHermitian] using
    FiniteThreeLevelEnvironmentLift.swap_tensor A B

theorem sequentialOp_effect (φ₁ φ₂ : ℝ) (rev : Bool) (a : Q) (d : Fin 2) (j : Q) :
    (sequentialOp φ₁ φ₂ rev a d j)ᴴ * sequentialOp φ₁ φ₂ rev a d j =
      if (choosesA rev a j ↔ d = 0) then (1:MatQ) ⊗ₖ R φ₁ φ₂ j else 0 := by
  unfold sequentialOp
  split_ifs
  · simp only [Matrix.conjTranspose_mul, swapMat_isHermitian, Matrix.conjTranspose_kronecker,
      (R_hermitian φ₁ φ₂ j).eq, Matrix.conjTranspose_one]
    rw [mul_assoc, ← mul_assoc (R φ₁ φ₂ j ⊗ₖ (1:MatQ)),
      ← Matrix.mul_kronecker_mul, R_square, mul_one, ← mul_assoc, swap_sandwich]
  · simp

theorem sequential_normalized (φ₁ φ₂ : ℝ) (rev : Bool) (a : Q) :
    (∑ d, ∑ j, (sequentialOp φ₁ φ₂ rev a d j)ᴴ * sequentialOp φ₁ φ₂ rev a d j) = 1 := by
  simp only [sequentialOp_effect]
  rw [Finset.sum_comm]
  have hd (j : Q) : (∑ d : Fin 2,
      if (choosesA rev a j ↔ d = 0) then (1:MatQ) ⊗ₖ R φ₁ φ₂ j else 0) =
      (1:MatQ) ⊗ₖ R φ₁ φ₂ j := by
    by_cases h : choosesA rev a j <;> simp [Fin.sum_univ_two, h]
  simp_rw [hd]
  rw [FiniteThreeLevelEnvironmentLift.sum_kronecker_right, R_sum, Matrix.one_kronecker_one]

def sequentialReadout (φ₁ φ₂ : ℝ) (rev : Bool) (h : MemoryHist) : FiniteInstrument Joint 2 where
  count := 3
  operators := sequentialOp φ₁ φ₂ rev h.1
  normalized := sequential_normalized φ₁ φ₂ rev h.1

theorem sequential_zero_effect (φ₁ φ₂ : ℝ) (rev : Bool) (h : MemoryHist) :
    FiniteThreeLevelEnvironmentLift.inducedEffect (sequentialReadout φ₁ φ₂ rev h) 0 =
      groupedEffect φ₁ φ₂ rev h := by
  simp only [FiniteThreeLevelEnvironmentLift.inducedEffect, sequentialReadout, sequentialOp_effect,
    iff_true]
  unfold groupedEffect
  rw [← accept_sum, ← FiniteThreeLevelEnvironmentLift.sum_kronecker_right]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem sequential_grouped_weights (φ₁ φ₂ : ℝ) (rev : Bool) (h : MemoryHist)
    (d : Fin 2) (X : MatJoint) :
    (sequentialReadout φ₁ φ₂ rev h).weight d X = (groupedReadout φ₁ φ₂ rev h).weight d X := by
  rw [FiniteThreeLevelEnvironmentLift.inducedEffect_weight]
  have hd : d = 0 ∨ d = 1 := by fin_cases d <;> decide
  rcases hd with rfl | rfl
  · rw [sequential_zero_effect, groupedReadout, projectiveReadout_weight_zero]
  · rw [← FiniteThreeLevelEnvironmentLift.inducedEffect_complement, sequential_zero_effect,
      groupedReadout, projectiveReadout_weight_one]

theorem sequential_grouped_error (φ₁ φ₂ : ℝ) (rev : Bool) (A B : MemoryHist → MatJoint) :
    instrumentError A B (sequentialReadout φ₁ φ₂ rev) =
      instrumentError A B (groupedReadout φ₁ φ₂ rev) := by
  simp only [instrumentError, readoutTable, sequential_grouped_weights]

def groupedMass (q d₁ d₂ : ℝ) (flip rev : Bool) (a c : Q) : ℝ :=
  if c = 0 then (if a.val = 2 then 1/3 else
    (1-probability q d₁ d₂ (signalLabel flip a) (rejected rev a))/3) else 0

theorem grouped_memory_trace (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip rev : Bool) (h : MemoryHist) :
    (groupedEffect φ₁ φ₂ rev h * memoryFamily b ℏ γ t r hγ ht flip h).trace.re =
      groupedMass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) flip rev h.1 h.2.1 := by
  rcases h with ⟨a,c,⟨⟩⟩
  rw [memory_run]
  unfold groupedEffect groupedMass
  by_cases hc : c = 0
  · simp only [hc, ite_true, Matrix.mul_smul, Matrix.trace_smul,
      ← Matrix.mul_kronecker_mul, one_mul, Matrix.trace_kronecker, projector_trace, one_mul]
    unfold groupProjection
    split_ifs
    · simp [evolved_trace b ℏ γ t r hγ ht]
    · rw [sub_mul, one_mul, Matrix.trace_sub, evolved_trace b ℏ γ t r hγ ht,
        evolved_probability b ℏ γ t r φ₁ φ₂ hγ ht]
      simp
      ring
  · simp [hc]

theorem grouped_error (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (rev : Bool) :
    instrumentError (memoryFamily b ℏ γ t r hγ ht false)
      (memoryFamily b ℏ γ t r hγ ht true) (groupedReadout φ₁ φ₂ rev) =
      1/2 - (if rev then -1 else 1)*retention r γ t*
        contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)/3 := by
  have he : instrumentError (memoryFamily b ℏ γ t r hγ ht false)
      (memoryFamily b ℏ γ t r hγ ht true) (groupedReadout φ₁ φ₂ rev) =
      readoutError (memoryFamily b ℏ γ t r hγ ht false)
        (memoryFamily b ℏ γ t r hγ ht true) (groupedEffect φ₁ φ₂ rev) := by
    simp only [instrumentError, readoutError, readoutTable, groupedReadout,
      projectiveReadout_weight_zero, projectiveReadout_weight_one]
  rw [he, readoutError_eq _ _ _ (memory_valid b ℏ γ t hγ ht hr hr1 false).2]
  simp only [mul_sub, Matrix.trace_sub, Complex.sub_re, grouped_memory_trace]
  change (1- ∑ h : Q × Q × Unit,
    (groupedMass _ _ _ false rev h.1 h.2.1 - groupedMass _ _ _ true rev h.1 h.2.1))/2 = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  cases rev <;> norm_num [groupedMass, rejected, signalLabel, exchange, probability,
    signalOverlap, Fin.sum_univ_succ] <;> ring

theorem memory_named_attainer (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    instrumentError (memoryFamily b ℏ γ t r hγ ht false)
      (memoryFamily b ℏ γ t r hγ ht true)
      (groupedReadout (theta₁ b ℏ t) (theta₂ b ℏ t) false) =
      1/2-retention r γ t/3 := by
  rw [grouped_error b ℏ γ t r _ _ hγ ht hr hr1]
  norm_num [contrast]

theorem memory_sequential_attainer (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    instrumentError (memoryFamily b ℏ γ t r hγ ht false)
      (memoryFamily b ℏ γ t r hγ ht true)
      (sequentialReadout (theta₁ b ℏ t) (theta₂ b ℏ t) false) =
      1/2-retention r γ t/3 := by
  rw [sequential_grouped_error, memory_named_attainer b ℏ γ t r hγ ht hr hr1]

theorem sequential_branch_tensor (φ₁ φ₂ : ℝ) (rev : Bool) (h : MemoryHist)
    (d : Fin 2) (A B : MatQ) :
    (sequentialReadout φ₁ φ₂ rev h).branch d (A ⊗ₖ B) =
      ∑ j, if (choosesA rev h.1 j ↔ d = 0) then (R φ₁ φ₂ j*B*R φ₁ φ₂ j) ⊗ₖ A else 0 := by
  simp only [FiniteInstrument.branch, krausMap, sequentialReadout, sequentialOp]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
      swapMat_isHermitian, (R_hermitian φ₁ φ₂ j).eq, Matrix.conjTranspose_one]
    calc
      _ = (R φ₁ φ₂ j ⊗ₖ (1:MatQ))*(swapMat 3*(A ⊗ₖ B)*swapMat 3)*
        (R φ₁ φ₂ j ⊗ₖ (1:MatQ)) := by noncomm_ring
      _ = _ := by rw [swap_sandwich]; simp only [← Matrix.mul_kronecker_mul, one_mul, mul_one]
  · simp

theorem R_zero (j : Q) : R 0 0 j = P j := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [R, rotate_entry, frameLevels]

/-- Equal effects do not identify the state updates, even after undoing SWAP. -/
theorem sequential_grouped_state_distinction :
    let X := projector (0:Q) ⊗ₖ projector (0:Q)
    IsDensityOperator X ∧
    (sequentialReadout 0 0 false (2,0,())).weight 0 X = 1 ∧
    (groupedReadout 0 0 false (2,0,())).weight 0 X = 1 ∧
    (sequentialReadout 0 0 false (2,0,())).branch 0 X ≠
      (groupedReadout 0 0 false (2,0,())).branch 0 X ∧
    FiniteThreeLevelEnvironmentLift.swap ((sequentialReadout 0 0 false (2,0,())).branch 0 X) ≠
      (groupedReadout 0 0 false (2,0,())).branch 0 X := by
  dsimp
  have hd : IsDensityOperator (projector (0:Q) ⊗ₖ projector (0:Q)) :=
    ⟨(FiniteAdaptiveGibbsReadout.projector_density 0).1.kronecker
      (FiniteAdaptiveGibbsReadout.projector_density 0).1,
      by simp [Matrix.trace_kronecker, projector_trace]⟩
  have hg : (groupedReadout 0 0 false (2,0,())).branch 0
      (projector (0:Q) ⊗ₖ projector (0:Q)) = projector (0:Q) ⊗ₖ projector (0:Q) := by
    rw [groupedReadout, projectiveReadout_branch_zero]
    simp [groupedEffect, groupProjection]
  have hw : (groupedReadout 0 0 false (2,0,())).weight 0
      (projector (0:Q) ⊗ₖ projector (0:Q)) = 1 := by
    rw [FiniteInstrument.weight, hg, hd.2]; rfl
  have he : ((sequentialReadout 0 0 false (2,0,())).branch 0
      (projector (0:Q) ⊗ₖ projector (0:Q))) (0,0) (0,0) = 1/2 := by
    rw [sequential_branch_tensor]
    simp only [choosesA, show (2:Q).val = 2 from rfl, true_or, ite_true, Matrix.sum_apply,
      Matrix.kroneckerMap_apply, Matrix.mul_apply]
    norm_num [R_zero, Fin.sum_univ_succ, P, projector, Matrix.diagonal_apply]
  refine ⟨hd, by rw [sequential_grouped_weights]; exact hw, hw, ?_, ?_⟩
  · intro e
    have ee := congrArg (fun M : MatJoint => M (0,0) (0,0)) e
    rw [he, hg] at ee
    norm_num [projector, Matrix.single_apply, Matrix.kroneckerMap_apply] at ee
  · intro e
    have ee := congrArg (fun M : MatJoint => M (0,0) (0,0)) e
    rw [FiniteThreeLevelEnvironmentLift.swap_entry, he, hg] at ee
    norm_num [projector, Matrix.single_apply, Matrix.kroneckerMap_apply] at ee

def W (d₁ d₂ : ℝ) : ℂ :=
  (9/25:ℂ)*Complex.exp (-(Complex.I*d₁)) + (16/25:ℂ)*Complex.exp (-(Complex.I*d₂))

theorem W_real (d₁ d₂ : ℝ) : (W d₁ d₂).re = contrast d₁ d₂ := by
  simp [W, exp_neg_angle, contrast, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

theorem W_normSq (d₁ d₂ : ℝ) : Complex.normSq (W d₁ d₂) =
    337/625+288/625*Real.cos (d₁-d₂) := by
  simp [W, exp_neg_angle, Complex.normSq_apply, Real.cos_sub, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq d₁, Real.sin_sq_add_cos_sq d₂]

theorem overlap_W (d₁ d₂ : ℝ) :
    signalOverlap d₁ d₂ true = (1+Complex.normSq (W d₁ d₂)+2*contrast d₁ d₂)/4 ∧
    signalOverlap d₁ d₂ false = (1+Complex.normSq (W d₁ d₂)-2*contrast d₁ d₂)/4 ∧
    darkOverlap d₁ d₂ = (1-Complex.normSq (W d₁ d₂))/2 := by
  rw [W_normSq]
  norm_num [signalOverlap, darkOverlap]
  constructor
  · ring
  constructor <;> ring

def fixtureTime : ℝ := Real.log 2

theorem fixtureTime_positive : 0 < fixtureTime := Real.log_pos (by norm_num)

theorem fixture_retention : retention (1/2) 1 fixtureTime = 1/4 := by
  norm_num [retention, fixtureTime, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)]

def fixtureTable : Matrix Q Q ℝ :=
  !![209/1200,109/1200,41/600;109/1200,209/1200,41/600;109/900,109/900,41/450]

theorem fixture_mass (flip : Bool) (a c j : Q) :
    mass (1/4) 0 0 flip a c j = if c = 0 then fixtureTable (signalLabel flip a) j else 0 := by
  cases flip <;> fin_cases a <;> fin_cases c <;> fin_cases j <;>
    norm_num [mass, probability, signalLabel, exchange, fixtureTable, gibbsProbability,
      signalOverlap, darkOverlap, contrast, Matrix.cons_val_two]

theorem fixture_actual_trace (flip : Bool) (a c j : Q) :
    (measuredFamily 1 1 1 fixtureTime (1/2) (theta₁ 1 1 fixtureTime) (theta₂ 1 1 fixtureTime)
      (by norm_num) fixtureTime_positive.le flip (a,c,j,())).trace.re =
      if c = 0 then fixtureTable (signalLabel flip a) j else 0 := by
  rw [measured_traces, Complex.ofReal_re, fixture_retention, sub_self, sub_self, fixture_mass]

theorem fixture_live_positive (a j : Q) : 0 < fixtureTable a j := by
  fin_cases a <;> fin_cases j <;> norm_num [fixtureTable]

theorem fixture_row_total (a : Q) : ∑ j, fixtureTable a j = 1/3 := by
  fin_cases a <;> norm_num [fixtureTable, Fin.sum_univ_succ]

theorem fixture_distance :
    branchDistance (memoryFamily 1 1 1 fixtureTime (1/2) (by norm_num) fixtureTime_positive.le false)
      (memoryFamily 1 1 1 fixtureTime (1/2) (by norm_num) fixtureTime_positive.le true) = 1/6 ∧
    branchDistance (measuredFamily 1 1 1 fixtureTime (1/2) (theta₁ 1 1 fixtureTime) (theta₂ 1 1 fixtureTime)
        (by norm_num) fixtureTime_positive.le false)
      (measuredFamily 1 1 1 fixtureTime (1/2) (theta₁ 1 1 fixtureTime) (theta₂ 1 1 fixtureTime)
        (by norm_num) fixtureTime_positive.le true) = 1/6 := by
  rw [memory_distance _ _ _ _ _ _ (by norm_num), measured_distance _ _ _ _ _ _ _ _ (by norm_num),
    fixture_retention]
  norm_num [contrast]

theorem fixture_physical_minimum :
    IsLeast (FiniteThreeLevelEnvironmentLift.PhysicalErrors
      (memoryFamily 1 1 1 fixtureTime (1/2) (by norm_num) fixtureTime_positive.le false)
      (memoryFamily 1 1 1 fixtureTime (1/2) (by norm_num) fixtureTime_positive.le true)) (5/12) ∧
    IsLeast (FiniteThreeLevelEnvironmentLift.PhysicalErrors
      (measuredFamily 1 1 1 fixtureTime (1/2) (theta₁ 1 1 fixtureTime) (theta₂ 1 1 fixtureTime)
        (by norm_num) fixtureTime_positive.le false)
      (measuredFamily 1 1 1 fixtureTime (1/2) (theta₁ 1 1 fixtureTime) (theta₂ 1 1 fixtureTime)
        (by norm_num) fixtureTime_positive.le true)) (5/12) := by
  constructor
  · convert memory_physical_isLeast 1 1 1 fixtureTime (by norm_num) fixtureTime_positive.le
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) using 1
    norm_num [fixture_retention]
  · convert measured_physical_isLeast 1 1 1 fixtureTime _ _ (by norm_num) fixtureTime_positive.le
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) using 1
    norm_num [fixture_retention, contrast]

def fixtureBinaryTable (flip : Bool) (a : Q) (d : Fin 2) : ℝ :=
  if a.val = 2 then (if d = 0 then 1/3 else 0)
  else if flip then (if d = 0 then 191/1200 else 209/1200)
  else (if d = 0 then 97/400 else 109/1200)

theorem fixture_binary_table (flip : Bool) (a c : Q) (d : Fin 2) :
    (groupedReadout (theta₁ 1 1 fixtureTime) (theta₂ 1 1 fixtureTime) false (a,c,())).weight d
      (memoryFamily 1 1 1 fixtureTime (1/2) (by norm_num) fixtureTime_positive.le flip (a,c,())) =
      if c = 0 then fixtureBinaryTable flip a d else 0 := by
  have hd : d = 0 ∨ d = 1 := by fin_cases d <;> decide
  rcases hd with rfl | rfl
  · rw [groupedReadout, projectiveReadout_weight_zero, grouped_memory_trace, fixture_retention]
    cases flip <;> fin_cases a <;> fin_cases c <;>
      norm_num [groupedMass, fixtureBinaryTable, probability, signalLabel, exchange,
        rejected, gibbsProbability, signalOverlap, contrast]
  · rw [groupedReadout, projectiveReadout_weight_one, sub_mul, one_mul,
      Matrix.trace_sub, Complex.sub_re, memory_trace, grouped_memory_trace, fixture_retention]
    cases flip <;> fin_cases a <;> fin_cases c <;>
      norm_num [groupedMass, fixtureBinaryTable, probability, signalLabel, exchange,
        rejected, gibbsProbability, signalOverlap, contrast]

theorem destructive_erasure (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hC : contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) = 0) :
    measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false =
      measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true := by
  funext ⟨a,c,j,⟨⟩⟩
  rw [measured_matrices, measured_matrices]
  have hh := mass_difference (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) a c j
  simp only [hC, mul_zero, zero_div, ite_self] at hh
  rw [sub_eq_zero.mp hh]

def fixtureShifted (x y : ℝ) (flip : Bool) : MeasuredHist → MatJoint :=
  measuredFamily 1 1 1 fixtureTime (1/2) (theta₁ 1 1 fixtureTime+x) (theta₂ 1 1 fixtureTime+y)
    (by norm_num) fixtureTime_positive.le flip

theorem fixture_shifted_distance (x y : ℝ) :
    branchDistance (fixtureShifted x y false) (fixtureShifted x y true) =
      |contrast (-x) (-y)|/6 := by
  unfold fixtureShifted
  rw [measured_distance _ _ _ _ _ _ _ _ (by norm_num), fixture_retention]
  simp only [sub_add_cancel_left]
  ring

theorem fixture_shifted_error (x y : ℝ) (rev : Bool) :
    instrumentError (fixtureShifted x y false) (fixtureShifted x y true) (decisionReadout rev) =
      1/2-(if rev then -1 else 1)*contrast (-x) (-y)/12 := by
  unfold fixtureShifted
  rw [decision_error _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), fixture_retention]
  simp only [sub_add_cancel_left]
  ring

theorem fixture_shifted_isLeast (x y : ℝ) :
    IsLeast (FiniteThreeLevelEnvironmentLift.PhysicalErrors (fixtureShifted x y false) (fixtureShifted x y true))
      (1/2-|contrast (-x) (-y)|/12) := by
  unfold fixtureShifted
  have hh := measured_physical_isLeast 1 1 1 fixtureTime
    (theta₁ 1 1 fixtureTime+x) (theta₂ 1 1 fixtureTime+y) (by norm_num) fixtureTime_positive.le
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  rw [fixture_retention] at hh
  simp only [sub_add_cancel_left] at hh
  convert hh using 1
  ring

theorem opposite_quarter_erasure :
    fixtureShifted (Real.pi/2) (Real.pi/2) false = fixtureShifted (Real.pi/2) (Real.pi/2) true ∧
    fixtureShifted (-Real.pi/2) (-Real.pi/2) false = fixtureShifted (-Real.pi/2) (-Real.pi/2) true := by
  constructor <;> apply destructive_erasure <;>
    norm_num [contrast, neg_div, show ∀ x y : ℝ, x-(x+y) = -y by intros; ring]

def quarterTable : Matrix Q Q ℝ :=
  !![53/400,53/400,41/600;53/400,53/400,41/600;109/900,109/900,41/450]

theorem quarter_tables (sign : Bool) (flip : Bool) (a c j : Q) :
    let x := if sign then Real.pi/2 else -Real.pi/2
    ((fixtureShifted x x flip) (a,c,j,())).trace.re =
      if c = 0 then quarterTable a j else 0 := by
  dsimp
  unfold fixtureShifted
  rw [measured_traces, Complex.ofReal_re, fixture_retention]
  cases sign <;> cases flip <;> fin_cases a <;> fin_cases c <;> fin_cases j <;>
    norm_num [mass, probability, signalLabel, exchange, quarterTable, signalOverlap,
      darkOverlap, gibbsProbability, contrast, sub_add_cancel_left, Matrix.cons_val_two, neg_div]

theorem quarter_physical_minima :
    IsLeast (FiniteThreeLevelEnvironmentLift.PhysicalErrors
      (fixtureShifted (Real.pi/2) (Real.pi/2) false) (fixtureShifted (Real.pi/2) (Real.pi/2) true)) (1/2) ∧
    IsLeast (FiniteThreeLevelEnvironmentLift.PhysicalErrors
      (fixtureShifted (-Real.pi/2) (-Real.pi/2) false) (fixtureShifted (-Real.pi/2) (-Real.pi/2) true)) (1/2) := by
  constructor
  · simpa [contrast, neg_div] using fixture_shifted_isLeast (Real.pi/2) (Real.pi/2)
  · simpa [contrast, neg_div] using fixture_shifted_isLeast (-Real.pi/2) (-Real.pi/2)

theorem pi_fixed_and_reoptimized :
    instrumentError (fixtureShifted Real.pi Real.pi false) (fixtureShifted Real.pi Real.pi true)
      (decisionReadout false) = 7/12 ∧
    IsLeast (FiniteThreeLevelEnvironmentLift.PhysicalErrors
      (fixtureShifted Real.pi Real.pi false) (fixtureShifted Real.pi Real.pi true)) (5/12) := by
  constructor
  · rw [fixture_shifted_error]; norm_num [contrast]
  · convert fixture_shifted_isLeast Real.pi Real.pi using 1
    norm_num [contrast]

theorem single_arm_control :
    contrast 0 Real.pi = -7/25 ∧
    branchDistance (fixtureShifted 0 Real.pi false) (fixtureShifted 0 Real.pi true) = 7/150 ∧
    IsLeast (FiniteThreeLevelEnvironmentLift.PhysicalErrors
      (fixtureShifted 0 Real.pi false) (fixtureShifted 0 Real.pi true)) (143/300) := by
  constructor
  · norm_num [contrast]
  constructor
  · rw [fixture_shifted_distance]; norm_num [contrast]
  · convert fixture_shifted_isLeast 0 Real.pi using 1
    norm_num [contrast]

private theorem exp_quarter_pos : Complex.exp (Complex.I * (Real.pi:ℂ) * (1/2)) = Complex.I := by
  rw [show Complex.I * (Real.pi:ℂ) * (1/2) = Complex.I * ((Real.pi/2:ℝ):ℂ) by push_cast; ring,
    exp_pos_angle]
  norm_num

private theorem exp_quarter_neg : Complex.exp (-(Complex.I * (Real.pi:ℂ) * (1/2))) = -Complex.I := by
  rw [show -(Complex.I * (Real.pi:ℂ) * (1/2)) = -(Complex.I * ((Real.pi/2:ℝ):ℂ)) by push_cast; ring,
    exp_neg_angle]
  norm_num

theorem quarter_plus_projectors :
    R (Real.pi/2) (Real.pi/2) 0 =
      !![1/2,3*Complex.I/10,2*Complex.I/5;-3*Complex.I/10,9/50,6/25;-2*Complex.I/5,6/25,8/25] ∧
    R (Real.pi/2) (Real.pi/2) 1 =
      !![1/2,-3*Complex.I/10,-2*Complex.I/5;3*Complex.I/10,9/50,6/25;2*Complex.I/5,6/25,8/25] ∧
    R (Real.pi/2) (Real.pi/2) 2 = P 2 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [R, rotate_entry, frameLevels, P, exp_neg_angle, exp_pos_angle, Matrix.cons_val_two] <;> ring_nf <;> norm_num [exp_quarter_pos, exp_quarter_neg]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [R, rotate_entry, frameLevels, P, exp_neg_angle, exp_pos_angle, Matrix.cons_val_two] <;> ring_nf <;> norm_num [exp_quarter_pos, exp_quarter_neg]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [R, rotate_entry, frameLevels, P, exp_neg_angle, exp_pos_angle, Matrix.cons_val_two]

theorem opposite_quarter_conjugate (a : Q) (i j : Q) :
    R (-Real.pi/2) (-Real.pi/2) a i j = star (R (Real.pi/2) (Real.pi/2) a i j) := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [R, rotate_entry, frameLevels, P, exp_neg_angle, exp_pos_angle, Matrix.cons_val_two] <;> ring_nf <;> norm_num [exp_quarter_pos, exp_quarter_neg]

theorem opposite_quarter_distinct : R (Real.pi/2) (Real.pi/2) 0 ≠ R (-Real.pi/2) (-Real.pi/2) 0 := by
  intro h
  have he := congrArg (fun M : MatQ => (M 0 1).im) h
  rw [opposite_quarter_conjugate, quarter_plus_projectors.1] at he
  norm_num at he

theorem sum_exchange {M : Type*} [AddCommMonoid M] (f : Q → M) :
    ∑ a, f (exchange a) = ∑ a, f a := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 1 + (f 0 + f 2) = f 0 + (f 1 + f 2)
  ac_rfl

theorem memory_terminal_equal (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    (∑ h, memoryFamily b ℏ γ t r hγ ht false h) =
      ∑ h, memoryFamily b ℏ γ t r hγ ht true h := by
  simp only [memory_run_history]
  change (∑ h : Q × Q × Unit, if h.2.1 = 0 then (1/3:ℂ) •
    (projector (0:Q) ⊗ₖ evolved b ℏ γ t r (signalLabel false h.1)) else 0) =
    ∑ h : Q × Q × Unit, if h.2.1 = 0 then (1/3:ℂ) •
    (projector (0:Q) ⊗ₖ evolved b ℏ γ t r (signalLabel true h.1)) else 0
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, signalLabel, Bool.false_eq_true, if_false, if_true]
  exact (sum_exchange (fun a => ∑ c : Q, if c = 0 then (1/3:ℂ) •
    (projector (0:Q) ⊗ₖ evolved b ℏ γ t r a) else 0)).symm

theorem measured_matrices_history (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (h : MeasuredHist) :
    measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip h =
      (mass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) flip h.1 h.2.1 h.2.2.1:ℂ) •
      (R φ₁ φ₂ h.2.2.1 ⊗ₖ projector (0:Q)) := by
  rcases h with ⟨a,c,j,⟨⟩⟩
  exact measured_matrices b ℏ γ t r φ₁ φ₂ hγ ht flip a c j

theorem measured_terminal_equal (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    (∑ h, measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false h) =
      ∑ h, measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true h := by
  simp only [measured_matrices_history]
  change (∑ h : Q × Q × Q × Unit, (mass _ _ _ false h.1 h.2.1 h.2.2.1:ℂ) •
    (R φ₁ φ₂ h.2.2.1 ⊗ₖ projector (0:Q))) =
    ∑ h : Q × Q × Q × Unit, (mass _ _ _ true h.1 h.2.1 h.2.2.1:ℂ) •
    (R φ₁ φ₂ h.2.2.1 ⊗ₖ projector (0:Q))
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, mass, signalLabel,
    Bool.false_eq_true, if_false, if_true]
  exact (sum_exchange (fun a => ∑ c : Q, ∑ j : Q,
    (((if c = 0 then probability (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) a j/3 else 0):ℝ):ℂ) •
    (R φ₁ φ₂ j ⊗ₖ projector (0:Q)))).symm

theorem terminal_error (b ℏ γ t φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (E : MatJoint) :
    readoutError (memoryFamily b ℏ γ t r hγ ht false) (memoryFamily b ℏ γ t r hγ ht true)
      (fun _ => E) = 1/2 ∧
    readoutError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true) (fun _ => E) = 1/2 :=
  ⟨constant_error_same_terminal (memory_valid b ℏ γ t hγ ht hr hr1 false)
    (memory_terminal_equal b ℏ γ t r hγ ht) E,
    constant_error_same_terminal (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 false)
    (measured_terminal_equal b ℏ γ t r φ₁ φ₂ hγ ht) E⟩

theorem marginal_mass_laws (q d₁ d₂ : ℝ) (a j : Q) :
    (∑ c : Q, ∑ j : Q, mass q d₁ d₂ false a c j) = 1/3 ∧
    (∑ c : Q, ∑ j : Q, mass q d₁ d₂ true a c j) = 1/3 ∧
    (∑ a : Q, ∑ c : Q, mass q d₁ d₂ false a c j) =
      ∑ a : Q, ∑ c : Q, mass q d₁ d₂ true a c j := by
  constructor
  · simp only [mass]
    simp_rw [Finset.sum_ite_irrel, ← Finset.sum_div, probability_sum, Finset.sum_const_zero]
    simp
  constructor
  · simp only [mass]
    simp_rw [Finset.sum_ite_irrel, ← Finset.sum_div, probability_sum, Finset.sum_const_zero]
    simp
  · simp only [mass, signalLabel, Bool.false_eq_true, if_false, if_true]
    exact (sum_exchange (fun a => ∑ c : Q, if c = 0 then probability q d₁ d₂ a j/3 else 0)).symm

theorem marginal_rule_error (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (f : Q → ℝ) :
    historyError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true) (fun h => f h.1) = 1/2 ∧
    historyError (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht false)
      (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht true) (fun h => f h.2.2.1) = 1/2 := by
  constructor
  all_goals rw [historyError_eq (measured_valid b ℏ γ t φ₁ φ₂ hγ ht hr hr1 false)]
  all_goals simp only [measured_trace_history, Complex.ofReal_re, mass_difference]
  · change (1-∑ h : Q × Q × Q × Unit, f h.1 *
      (if h.2.1 = 0 ∧ h.1.val ≠ 2 ∧ h.2.2.1.val ≠ 2 then
        (if h.1.val = h.2.2.1.val then 1 else -1)*retention r γ t*
        contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)/3 else 0))/2 = _
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring
  · change (1-∑ h : Q × Q × Q × Unit, f h.2.2.1 *
      (if h.2.1 = 0 ∧ h.1.val ≠ 2 ∧ h.2.2.1.val ≠ 2 then
        (if h.1.val = h.2.2.1.val then 1 else -1)*retention r γ t*
        contrast (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂)/3 else 0))/2 = _
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ]
    ring

theorem actual_E_reset_memory (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (a c : Q) :
    FiniteThreeLevelEnvironmentLift.gibbsReset (memoryFamily b ℏ γ t r hγ ht flip (a,c,())) =
      if c = 0 then (1/3:ℂ) • (projector (0:Q) ⊗ₖ equilibrium) else 0 := by
  rw [FiniteThreeLevelEnvironmentLift.gibbsReset_action, memory_marginal]
  split_ifs <;> ext ⟨i,j⟩ ⟨k,l⟩ <;> simp [mul_assoc]

theorem actual_E_reset_erases (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (h : MemoryHist) :
    FiniteThreeLevelEnvironmentLift.gibbsReset (memoryFamily b ℏ γ t r hγ ht false h) =
      FiniteThreeLevelEnvironmentLift.gibbsReset (memoryFamily b ℏ γ t r hγ ht true h) := by
  rcases h with ⟨a,c,⟨⟩⟩
  rw [actual_E_reset_memory, actual_E_reset_memory]

theorem E_reset_trace (X : MatJoint) : (FiniteThreeLevelEnvironmentLift.gibbsReset X).trace = X.trace :=
  trace_krausMap FiniteThreeLevelEnvironmentLift.gibbsReset_normalized X

theorem E_reset_preserves_recorded_error (A B : MeasuredHist → MatJoint) (f : MeasuredHist → ℝ) :
    historyError (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset (A h))
      (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset (B h)) f = historyError A B f := by
  simp only [historyError, E_reset_trace]

theorem E_reset_after_readout_fixture :
    historyError (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset (fixtureShifted 0 0 false h))
      (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset (fixtureShifted 0 0 true h)) (score false) = 5/12 := by
  rw [E_reset_preserves_recorded_error]
  unfold fixtureShifted
  rw [score_error _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), fixture_retention]
  norm_num [contrast]

def resetSKraus (k : Q) : MatJoint := prepareOp 0 k ⊗ₖ (1:MatQ)
def resetS (X : MatJoint) : MatJoint := krausMap resetSKraus X

theorem resetS_normalized : IsKrausChannel resetSKraus := by
  unfold IsKrausChannel resetSKraus
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, mul_one, prepareOp_square, ite_true]
  have hs : (∑ k : Q, projector k ⊗ₖ (1:MatQ)) = (∑ k : Q, projector k) ⊗ₖ (1:MatQ) := by
    ext ⟨i,j⟩ ⟨k,l⟩; simp [Matrix.sum_apply, Finset.sum_mul]
  rw [hs, projector_sum, Matrix.one_kronecker_one]

theorem resetS_tensor (A B : MatQ) : resetS (A ⊗ₖ B) = A.trace • (projector (0:Q) ⊗ₖ B) := by
  change (prepare.lift Q).branch 0 (A ⊗ₖ B) = _
  rw [lift_branch_tensor, prepare_branch]
  simp
  ext ⟨i,j⟩ ⟨k,l⟩; simp [mul_assoc]

theorem resetS_smul (c : ℂ) (X : MatJoint) : resetS (c • X) = c • resetS X :=
  krausMap_smul resetSKraus c X

theorem S_reset_after_swap (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (a c : Q) :
    resetS (FiniteThreeLevelEnvironmentLift.swap (memoryFamily b ℏ γ t r hγ ht flip (a,c,()))) =
      if c = 0 then (1/3:ℂ) • (projector (0:Q) ⊗ₖ projector (0:Q)) else 0 := by
  rw [memory_run]
  split_ifs
  · simp only [FiniteThreeLevelEnvironmentLift.swap, krausMap_smul, resetS_smul]
    change (1/3:ℂ) • resetS (FiniteThreeLevelEnvironmentLift.swap
      (projector (0:Q) ⊗ₖ evolved b ℏ γ t r (signalLabel flip a))) = _
    rw [FiniteThreeLevelEnvironmentLift.swap_tensor, resetS_tensor,
      evolved_trace b ℏ γ t r hγ ht, one_smul]
  · simp [resetS, FiniteThreeLevelEnvironmentLift.swap, krausMap]

theorem sigma_diagonal_common (r : ℝ) (j : Q) : sigma r 0 j j = sigma r 1 j j := by
  fin_cases j <;> norm_num [sigma, mixture, P]

theorem evolved_diagonal_common (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (j : Q) :
    evolved b ℏ γ t r 0 j j = evolved b ℏ γ t r 1 j j := by
  rw [evolved_formula _ _ _ _ _ hγ ht, evolved_formula _ _ _ _ _ hγ ht]
  fin_cases j <;> norm_num [mixture, R, rotate_entry, P]

def computationalReadStep : Step Q Q 3 where
  count := 1
  evolution := FiniteThreeLevelEnvironmentLift.swapKraus
  normalized := FiniteThreeLevelEnvironmentLift.swap_normalized
  instrument := instrument 3

theorem computational_readout_erases (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (a c j : Q) :
    computationalReadStep.branch Q Q 3 j (memoryFamily b ℏ γ t r hγ ht false (a,c,())) =
      computationalReadStep.branch Q Q 3 j (memoryFamily b ℏ γ t r hγ ht true (a,c,())) := by
  rw [memory_run, memory_run]
  by_cases hc : c = 0
  · simp only [hc, ite_true, Step.branch_smul]
    apply congrArg (fun X : MatJoint => (1/3:ℂ) • X)
    change ((instrument 3).lift Q).branch j (FiniteThreeLevelEnvironmentLift.swap _) =
      ((instrument 3).lift Q).branch j (FiniteThreeLevelEnvironmentLift.swap _)
    rw [FiniteThreeLevelEnvironmentLift.swap_tensor, FiniteThreeLevelEnvironmentLift.swap_tensor,
      lift_branch_tensor, lift_branch_tensor, instrument_branch, instrument_branch]
    have hd := evolved_diagonal_common b ℏ γ t r hγ ht j
    fin_cases a <;> norm_num [signalLabel, exchange, hd]
    rfl
  · simp only [hc, if_false]

theorem sigma_affine (r : ℝ) (a : Q) :
    sigma r a = ((1-r:ℝ):ℂ) • equilibrium + (r:ℂ) • sigma 1 a := by
  unfold sigma
  split_ifs
  · module
  · simp [mixture]

theorem input_entry (r : ℝ) (a b e f : Q) :
    input r (a,e) (b,f) = if a = b then sigma r a e f/3 else 0 := by
  simp [input, Matrix.sum_apply, projector, Matrix.diagonal_apply]
  split_ifs <;> simp_all
  ring

theorem input_zero : input 0 = (1/3:ℂ) • ((1:MatQ) ⊗ₖ equilibrium) := by
  ext ⟨a,e⟩ ⟨b,f⟩
  rw [input_entry, sigma_zero]
  by_cases h : a = b <;> simp [h]
  ring

theorem input_affine (r : ℝ) :
    input r = ((1-r:ℝ):ℂ) • input 0 + (r:ℂ) • input 1 := by
  ext ⟨a,e⟩ ⟨b,f⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, input_entry, sigma_zero, sigma_affine r a]
  split_ifs <;> simp
  ring

theorem input_faithful {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : (input r).PosDef := by
  have h0 : (input 0).PosDef := by
    rw [input_zero]
    exact ((Matrix.PosDef.one : (1:MatQ).PosDef).kronecker
      FiniteThreeLevelThermalPhase.equilibrium_posDef).smul (by norm_num : (0:ℂ)<1/3)
  rw [input_affine]
  exact (h0.smul (by exact_mod_cast sub_pos.mpr hr1)).add_posSemidef
    ((input_density (by norm_num : (0:ℝ) ≤ 1) le_rfl).1.smul (by exact_mod_cast hr))

theorem evolved_faithful (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hq : retention r γ t < 1) (a : Q) :
    (evolved b ℏ γ t r a).PosDef := by
  rw [evolved_formula b ℏ γ t r hγ ht]
  split_ifs
  · exact FiniteThreeLevelThermalPhase.equilibrium_posDef
  · exact FiniteThreeLevelThermalPhase.mixture_faithful
      (FiniteThreeLevelThermalPhase.retention_nonneg hr γ t) hq (R_positive _ _ _)

theorem pure_signal_restored_faithful (b ℏ γ t : ℝ) (hγ : 0 < γ) (ht : 0 < t) (a : Q) :
    (evolved b ℏ γ t 1 a).PosDef := by
  apply evolved_faithful b ℏ γ t hγ.le ht.le (by norm_num)
  simp only [retention, one_mul]
  apply Real.exp_lt_one_iff.mpr
  nlinarith [mul_pos hγ ht]

theorem memory_joint_not_faithful (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (a c : Q) : ¬ (memoryFamily b ℏ γ t r hγ ht flip (a,c,())).PosDef := by
  intro hh
  have hd := hh.diag_pos (i := (1,0))
  rw [memory_run] at hd
  split_ifs at hd <;> norm_num [projector, Matrix.diagonal_apply] at hd

theorem measured_joint_not_faithful (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (a c j : Q) : ¬ (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip (a,c,j,())).PosDef := by
  intro hh
  have hd := hh.diag_pos (i := (0,1))
  rw [measured_matrices] at hd
  norm_num [projector, Matrix.diagonal_apply] at hd

theorem pure_signal (a : Q) (ha : a.val ≠ 2) : sigma 1 a = P a := by
  simp [sigma, ha, mixture]

theorem signal_positive_diagonals (a : Q) (ha : a.val ≠ 2) (j : Q) : 0 < P a j j := by
  fin_cases a <;> fin_cases j <;> norm_num [P] at *

theorem signal_noncommuting {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    sigma r 0*sigma r 1 ≠ sigma r 1*sigma r 0 := by
  intro hh
  have he := congrArg (fun M : MatQ => (M 0 1).re) hh
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at he
  norm_num [sigma, mixture, P, equilibrium, density, three, GibbsReset.threeWeights, Matrix.diagonal_apply, Matrix.cons_val_two, Fin.ext_iff] at he
  nlinarith [mul_pos hr (sub_pos.mpr hr1)]

theorem common_twelve_coherence (r : ℝ) :
    sigma r 0 1 2 = (6*r/25:ℝ) ∧ sigma r 1 1 2 = (6*r/25:ℝ) := by
  norm_num [sigma, mixture, P, equilibrium, density, three, GibbsReset.threeWeights, Matrix.diagonal_apply, Matrix.cons_val_two, Fin.ext_iff]
  ring

theorem impossible_tie_chooses_A (rev : Bool) (h : MeasuredHist) (hc : h.2.1 ≠ 0) :
    score rev h = 1 ∧ decisionProjection rev h = 1 := by simp [score, decisionProjection, hc]

theorem P_not_faithful (a : Q) : ¬ (P a).PosDef := by
  intro hh
  obtain ⟨j, hj⟩ : ∃ j : Q, a ≠ j := by
    by_cases h : a = 0
    · exact ⟨1, by subst a; decide⟩
    · exact ⟨0,h⟩
  have hz : P j = 0 := hh.isUnit.mul_left_cancel (by rw [mul_zero, P_orthogonal a j hj])
  have ht := P_trace j
  rw [hz, Matrix.trace_zero] at ht
  norm_num at ht

theorem pure_signal_not_faithful (a : Q) (ha : a.val ≠ 2) : ¬ (sigma 1 a).PosDef := by
  rw [pure_signal a ha]
  exact P_not_faithful a

theorem P_rank_bound (a : Q) : (Matrix.toLin' (P a)).rank ≤ 1 := by
  rw [v_rank_one]
  exact Matrix.rank_vecMulVec _ _

theorem resetS_input (r : ℝ) :
    resetS (input r) = (1/3:ℂ) • (projector (0:Q) ⊗ₖ ∑ a : Q, sigma r a) := by
  rw [input, resetS_smul]
  have hs : resetS (∑ a : Q, projector a ⊗ₖ sigma r a) =
      ∑ a : Q, projector (0:Q) ⊗ₖ sigma r a := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp only [resetS, krausMap_add]
    change resetS _ + (resetS _ + resetS _) = _
    simp only [resetS_tensor, projector_trace, one_smul]
  rw [hs]
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [Matrix.sum_apply, Finset.mul_sum]

theorem F_average (r : ℝ) : F*(∑ a : Q, sigma r a)*Fᴴ = ∑ a : Q, sigma r a := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, F_sigma]
  exact sum_exchange (sigma r)

theorem record_after_S_reset (r : ℝ) (a : Q) :
    recordStep.branch Q Q 3 a (resetS (input r)) = if a = 0 then resetS (input r) else 0 := by
  rw [resetS_input]
  change ((instrument 3).lift Q).branch a
    (krausMap (fun _ : Fin 1 => (1:MatJoint)) _) = _
  simp only [krausMap, Fin.sum_univ_one, Matrix.conjTranspose_one, one_mul, mul_one]
  rw [FiniteInstrument.branch_smul, lift_branch_tensor, instrument_branch]
  by_cases ha : a = 0
  · subst a; simp [projector]
  · simp [ha, projector]

theorem evolution_after_S_reset (b ℏ γ t r : ℝ) :
    krausMap (evolution b ℏ γ t false) (resetS (input r)) =
      krausMap (evolution b ℏ γ t true) (resetS (input r)) := by
  rw [evolution_action, evolution_action, resetS_input]
  simp only [krausMap_smul, pulse_tensor, pulse, Bool.false_eq_true, if_false, if_true,
    Matrix.conjTranspose_one, one_mul, mul_one, F_average]

theorem S_reset_before_record_erases (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (a c : Q) :
    run Q Q 3 (memoryTree b ℏ γ t hγ ht false) (a,c,()) (resetS (input r)) =
      run Q Q 3 (memoryTree b ℏ γ t hγ ht true) (a,c,()) (resetS (input r)) := by
  change (memoryStep b ℏ γ t hγ ht false).branch Q Q 3 c
    (recordStep.branch Q Q 3 a (resetS (input r))) =
    (memoryStep b ℏ γ t hγ ht true).branch Q Q 3 c
    (recordStep.branch Q Q 3 a (resetS (input r)))
  rw [record_after_S_reset]
  by_cases ha : a = 0
  · simp only [ha, ite_true]
    change (prepare.lift Q).branch c (krausMap (evolution b ℏ γ t false) _) =
      (prepare.lift Q).branch c (krausMap (evolution b ℏ γ t true) _)
    rw [evolution_after_S_reset]
  · simp [ha, Step.branch, krausMap, FiniteInstrument.branch]

open FiniteThreeLevelThermalPhase

theorem traceless_channel (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (X : MatQ) (hX : X.trace = 0) :
    krausMap (channelKraus b ℏ γ t) X = (Real.exp (-γ*t):ℂ) • phase b ℏ t X := by
  rw [channel_action b ℏ γ t hγ ht, reset_action γ t hγ ht, hX]
  simp [phase_smul]

theorem single_off_diagonal_trace (i j : Q) (hij : i ≠ j) :
    (Matrix.single i j (1:ℂ)).trace = 0 := by
  simp [Matrix.trace, Matrix.diag, Matrix.single_apply, Ne.symm hij]

/-- This arbitrary complex scalar includes both the real and imaginary E02 probes. -/
theorem full_H02_probe (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (A : MatQ) (z : ℂ) :
    FiniteThreeLevelEnvironmentLift.thermal b ℏ γ t (A ⊗ₖ (z • Matrix.single 0 2 1)) =
      A ⊗ₖ ((z*(Real.exp (-γ*t):ℂ)*Complex.exp (Complex.I*t*(Real.log 3/b/ℏ:ℝ))) •
        Matrix.single (0:Q) 2 1) := by
  rw [FiniteThreeLevelEnvironmentLift.thermal, FiniteThreeLevelEnvironmentLift.product_action,
    krausMap_smul, traceless_channel b ℏ γ t hγ ht _ (single_off_diagonal_trace 0 2 (by decide)),
    phase_E02, smul_smul, smul_smul]

/-- The distinct 12 gap survives as well; no two-level Hamiltonian replaces it. -/
theorem full_H12_probe (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (A : MatQ) (z : ℂ) :
    FiniteThreeLevelEnvironmentLift.thermal b ℏ γ t (A ⊗ₖ (z • Matrix.single 1 2 1)) =
      A ⊗ₖ ((z*(Real.exp (-γ*t):ℂ)*
        Complex.exp (-Complex.I*t*((delta/b/ℏ:ℝ)-(Real.log 3/b/ℏ:ℝ)))) • Matrix.single (1:Q) 2 1) := by
  rw [FiniteThreeLevelEnvironmentLift.thermal, FiniteThreeLevelEnvironmentLift.product_action,
    krausMap_smul, traceless_channel b ℏ γ t hγ ht _ (single_off_diagonal_trace 1 2 (by decide)),
    phase_E12, smul_smul, smul_smul]

theorem zero_preparation_erases (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    memoryFamily b ℏ γ t 0 hγ ht false = memoryFamily b ℏ γ t 0 hγ ht true := by
  funext ⟨a,c,⟨⟩⟩
  rw [memory_run, memory_run]
  simp only [evolved, sigma_zero]

theorem zero_preparation_readout_erases (b ℏ γ t φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    measuredFamily b ℏ γ t 0 φ₁ φ₂ hγ ht false = measuredFamily b ℏ γ t 0 φ₁ φ₂ hγ ht true := by
  funext ⟨a,c,j,⟨⟩⟩
  rw [measured_run, measured_run]
  simp only [evolved, sigma_zero]

theorem finite_time_and_zero_controls (r γ t : ℝ) :
    0 < Real.exp (-γ*t) ∧ retention 0 γ t = 0 ∧
    retention r γ 0 = r ∧ retention r 0 t = r := by
  exact ⟨Real.exp_pos _, retention_controls r γ t⟩

theorem zero_time_state (b ℏ γ r : ℝ) (hγ : 0 ≤ γ) (a : Q) :
    evolved b ℏ γ 0 r a = sigma r a := channel_zero_time b ℏ γ hγ _

theorem zero_rate_state (b ℏ t r : ℝ) (ht : 0 ≤ t) (a : Q) :
    evolved b ℏ 0 t r a = phase b ℏ t (sigma r a) := channel_zero_rate b ℏ t ht _

theorem physical_two_gap_domain {b ℏ t : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ) (ht : 0 < t) :
    0 < theta₁ b ℏ t ∧ theta₁ b ℏ t < theta₂ b ℏ t ∧
    thermalH b ≠ 0 ∧ (∀ z : ℂ, thermalH b ≠ z • (1:MatQ)) ∧
    FiniteGibbsClock.gibbs (thermalH b) b = equilibrium := by
  have hl : Real.log (3/2) < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  refine ⟨mul_pos ht (div_pos (div_pos (Real.log_pos (by norm_num)) hb) hℏ), ?_,
    thermalH_ne_zero hb, thermalH_not_scalar hb, gibbs_thermal hb⟩
  exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right (div_lt_div_of_pos_right hl hb) hℏ) ht

theorem physical_scale_guards {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (hbc : b ≠ c) :
    FiniteGibbsClock.gibbs (thermalH b) b = FiniteGibbsClock.gibbs (thermalH c) c ∧
    energies b 1 ≠ energies c 1 ∧ FiniteGibbsClock.gibbs (thermalH b) 0 ≠ equilibrium :=
  ⟨gibbs_two_scales hb hc, gap_scales_ne hb hc hbc, gibbs_zero_ne_reference _⟩

theorem one_arm_pulse_is_different :
    Matrix.diagonal (![1,-1,1] : Q → ℂ) * P 0 * Matrix.diagonal (![1,-1,1] : Q → ℂ) ≠ P 1 := by
  intro hh
  have he := congrArg (fun M : MatQ => M 0 2) hh
  norm_num [Matrix.diagonal_mul, Matrix.mul_diagonal, P, Matrix.cons_val_two] at he

theorem full_W_probabilities (d₁ d₂ : ℝ) :
    signalOverlap d₁ d₂ true = Complex.normSq (1+W d₁ d₂)/4 ∧
    signalOverlap d₁ d₂ false = Complex.normSq (1-W d₁ d₂)/4 ∧
    darkOverlap d₁ d₂ = (1-Complex.normSq (W d₁ d₂))/2 := by
  have h := overlap_W d₁ d₂
  have hR := W_real d₁ d₂
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, zero_add, zero_sub] at *
  constructor
  · nlinarith [h.1]
  constructor
  · nlinarith [h.2.1]
  · exact h.2.2

theorem grouped_induced_effect (φ₁ φ₂ : ℝ) (rev : Bool) (h : MemoryHist) :
    FiniteThreeLevelEnvironmentLift.inducedEffect (groupedReadout φ₁ φ₂ rev h) 0 =
      groupedEffect φ₁ φ₂ rev h := by
  change (∑ _ : Fin 1, (groupedEffect φ₁ φ₂ rev h)ᴴ*groupedEffect φ₁ φ₂ rev h) = _
  rw [Fin.sum_univ_one, (groupedEffect_hermitian φ₁ φ₂ rev h).eq, groupedEffect_square]

theorem grouped_table (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip rev : Bool) (h : MemoryHist) (d : Fin 2) :
    readoutTable (groupedReadout φ₁ φ₂ rev) (memoryFamily b ℏ γ t r hγ ht flip) h d =
      if d = 0 then groupedMass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) flip rev h.1 h.2.1
      else (if h.2.1 = 0 then 1/3 else 0) -
        groupedMass (retention r γ t) (theta₁ b ℏ t-φ₁) (theta₂ b ℏ t-φ₂) flip rev h.1 h.2.1 := by
  rcases h with ⟨a,c,⟨⟩⟩
  have hd : d = 0 ∨ d = 1 := by fin_cases d <;> decide
  rcases hd with rfl | rfl
  · simp only [readoutTable, groupedReadout, projectiveReadout_weight_zero, grouped_memory_trace, ite_true]
  · rw [readoutTable, groupedReadout, projectiveReadout_weight_one, sub_mul, one_mul,
      Matrix.trace_sub, Complex.sub_re, grouped_memory_trace, memory_trace]
    norm_num only [show (1:Fin 2) ≠ 0 by decide, if_false]
    split_ifs <;> norm_num

theorem coarse_table_identity (q d₁ d₂ : ℝ) (flip rev : Bool) (a c : Q) (d : Fin 2) :
    (∑ j : Q, (if d = 0 then score rev (a,c,j,()) else 1-score rev (a,c,j,())) *
      mass q d₁ d₂ flip a c j) =
      if d = 0 then groupedMass q d₁ d₂ flip rev a c else
        (if c = 0 then 1/3 else 0)-groupedMass q d₁ d₂ flip rev a c := by
  cases flip <;> cases rev <;> fin_cases a <;> fin_cases c <;> fin_cases d <;>
    norm_num [score, choosesA, mass, groupedMass, probability, signalOverlap, darkOverlap,
      gibbsProbability, signalLabel, exchange, rejected, Fin.sum_univ_succ] <;> ring

theorem sequential_measured_decision_table (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip rev : Bool) (a c : Q) (d : Fin 2) :
    readoutTable (sequentialReadout φ₁ φ₂ rev) (memoryFamily b ℏ γ t r hγ ht flip) (a,c,()) d =
      ∑ j, readoutTable (decisionReadout rev) (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip) (a,c,j,()) d := by
  change (sequentialReadout φ₁ φ₂ rev (a,c,())).weight d _ = _
  rw [sequential_grouped_weights]
  change readoutTable (groupedReadout φ₁ φ₂ rev) _ (a,c,()) d = _
  rw [grouped_table]
  simp only [decision_table]
  exact (coarse_table_identity _ _ _ flip rev a c d).symm

theorem memory_all_effect_isLeast (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsLeast {x : ℝ | ∃ E : MemoryHist → MatJoint, (∀ h, IsBinaryPOVM (E h)) ∧
      readoutError (memoryFamily b ℏ γ t r hγ ht false) (memoryFamily b ℏ γ t r hγ ht true) E = x}
      (1/2-retention r γ t/3) := by
  have hh := readoutError_isLeast (memory_valid b ℏ γ t hγ ht hr hr1 false)
    (memory_valid b ℏ γ t hγ ht hr hr1 true)
  rw [memory_distance b ℏ γ t hγ ht hr] at hh
  convert hh using 1
  ring

theorem memory_randomized_isLeast (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsLeast {x : ℝ | ∃ f : MemoryHist → ℝ, (∀ h, f h ∈ Set.Icc (0:ℝ) 1) ∧
      historyError (memoryFamily b ℏ γ t r hγ ht false) (memoryFamily b ℏ γ t r hγ ht true) f = x} (1/2) := by
  refine ⟨⟨fun _ => 0, by intro h; norm_num, memory_history_error b ℏ γ t hγ ht hr hr1 _⟩, ?_⟩
  rintro x ⟨f,_,rfl⟩
  rw [memory_history_error b ℏ γ t hγ ht hr hr1]

theorem impossible_history_counts :
    Fintype.card {h : MemoryHist // h.2.1 ≠ 0} = 6 ∧
    Fintype.card {h : MeasuredHist // h.2.1 ≠ 0} = 18 := by decide

theorem impossible_memory_zero (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (h : MemoryHist) (hc : h.2.1 ≠ 0) : memoryFamily b ℏ γ t r hγ ht flip h = 0 := by
  rw [memory_run_history]
  simp [hc]

theorem impossible_measured_zero (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (h : MeasuredHist) (hc : h.2.1 ≠ 0) : measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip h = 0 := by
  rw [measured_matrices_history]
  simp [mass, hc]

theorem identical_physical_error {H : Type*} [Fintype H] {A B : H → MatJoint}
    (hA : IsBranchFamily A) (he : A = B) (I : H → FiniteInstrument Joint 2) :
    instrumentError A B I = 1/2 := by
  subst B
  rw [FiniteThreeLevelEnvironmentLift.instrumentError_effect, readoutError_eq _ _ _ hA.2]
  simp

theorem E_reset_memory_valid (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (flip : Bool) :
    IsBranchFamily (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
      (memoryFamily b ℏ γ t r hγ ht flip h)) := by
  have hv := memory_valid b ℏ γ t hγ ht hr hr1 flip
  refine ⟨fun h => FiniteThreeLevelEnvironmentLift.liftState_posSemidef _ (hv.1 h), ?_⟩
  simp only [E_reset_trace]
  exact hv.2

theorem E_reset_all_physical_errors (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (I : MemoryHist → FiniteInstrument Joint 2) :
    branchDistance (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
        (memoryFamily b ℏ γ t r hγ ht false h))
      (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
        (memoryFamily b ℏ γ t r hγ ht true h)) = 0 ∧
    instrumentError (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
        (memoryFamily b ℏ γ t r hγ ht false h))
      (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
        (memoryFamily b ℏ γ t r hγ ht true h)) I = 1/2 := by
  have he : (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
        (memoryFamily b ℏ γ t r hγ ht false h)) =
      (fun h => FiniteThreeLevelEnvironmentLift.gibbsReset
        (memoryFamily b ℏ γ t r hγ ht true h)) := funext (actual_E_reset_erases b ℏ γ t r hγ ht)
  refine ⟨?_, identical_physical_error (E_reset_memory_valid b ℏ γ t hγ ht hr hr1 false) he I⟩
  rw [he]
  simp [branchDistance, traceDist_self]

theorem quarter_all_physical_errors (sign : Bool) (I : MeasuredHist → FiniteInstrument Joint 2) :
    let x := if sign then Real.pi/2 else -Real.pi/2
    instrumentError (fixtureShifted x x false) (fixtureShifted x x true) I = 1/2 := by
  dsimp
  apply identical_physical_error
  · exact measured_valid 1 1 1 fixtureTime _ _ (by norm_num) fixtureTime_positive.le
      (by norm_num) (by norm_num) false
  · cases sign
    · exact opposite_quarter_erasure.2
    · exact opposite_quarter_erasure.1

theorem zero_input_all_physical_errors (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (I : MemoryHist → FiniteInstrument Joint 2) :
    instrumentError (memoryFamily b ℏ γ t 0 hγ ht false) (memoryFamily b ℏ γ t 0 hγ ht true) I = 1/2 :=
  identical_physical_error (memory_valid b ℏ γ t hγ ht le_rfl (by norm_num) false)
    (zero_preparation_erases b ℏ γ t hγ ht) I

def secondGapHalfTurn : ℝ := Real.pi/Real.log 3

theorem secondGapHalfTurn_positive : 0 < secondGapHalfTurn :=
  div_pos Real.pi_pos (Real.log_pos (by norm_num))

theorem zero_rate_still_nonidentity :
    krausMap (channelKraus 1 1 0 secondGapHalfTurn) (Matrix.single 0 2 1) =
      -(Matrix.single 0 2 1:MatQ) ∧
    krausMap (channelKraus 1 1 0 secondGapHalfTurn) (Matrix.single 0 2 1) ≠
      (Matrix.single 0 2 1:MatQ) := by
  have hp : krausMap (channelKraus 1 1 0 secondGapHalfTurn) (Matrix.single 0 2 1) =
      -(Matrix.single 0 2 1:MatQ) := by
    rw [channel_zero_rate 1 1 secondGapHalfTurn secondGapHalfTurn_positive.le, phase_E02]
    have ha : Complex.I*(secondGapHalfTurn:ℂ)*(Real.log 3/1/1:ℝ) = Complex.I*(Real.pi:ℂ) := by
      simp only [div_one, secondGapHalfTurn, Complex.ofReal_div]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<3))]
    rw [ha, exp_pos_angle]
    norm_num
  refine ⟨hp, ?_⟩
  rw [hp]
  intro hh
  have he := congrArg (fun M : MatQ => M 0 2) hh
  norm_num [Matrix.single_apply] at he

theorem R_outer (φ₁ φ₂ : ℝ) (a : Q) :
    ∃ u w : Q → ℂ, R φ₁ φ₂ a = Matrix.vecMulVec u w := by
  rw [R, rotate, GibbsHamiltonianRelaxation.rotation_sandwich, v_rank_one,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  exact ⟨_,_,rfl⟩

theorem R_rank_bound (φ₁ φ₂ : ℝ) (a : Q) : (R φ₁ φ₂ a).rank ≤ 1 := by
  obtain ⟨u,w,hu⟩ := R_outer φ₁ φ₂ a
  rw [hu]
  exact Matrix.rank_vecMulVec_le _ _

theorem measured_support_outer (φ₁ φ₂ : ℝ) (j : Q) :
    ∃ u w : Joint → ℂ, R φ₁ φ₂ j ⊗ₖ projector (0:Q) = Matrix.vecMulVec u w := by
  obtain ⟨u,w,hu⟩ := R_outer φ₁ φ₂ j
  refine ⟨fun x => u x.1 * if x.2 = 0 then 1 else 0,
    fun x => w x.1 * if x.2 = 0 then 1 else 0, ?_⟩
  rw [hu]
  ext ⟨a,e⟩ ⟨b,f⟩
  by_cases he : e = 0 <;> by_cases hf : f = 0 <;>
    simp [Matrix.vecMulVec, projector, Matrix.diagonal_apply, he, hf]
  aesop

theorem measured_branch_rank_bound (b ℏ γ t r φ₁ φ₂ : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (flip : Bool) (h : MeasuredHist) : (measuredFamily b ℏ γ t r φ₁ φ₂ hγ ht flip h).rank ≤ 1 := by
  rw [measured_matrices_history]
  obtain ⟨u,w,hu⟩ := measured_support_outer φ₁ φ₂ h.2.2.1
  rw [hu, ← Matrix.smul_vecMulVec]
  exact Matrix.rank_vecMulVec_le _ _

/-- The same all-complex test also includes the 01 coherence and its imaginary multiple. -/
theorem full_H01_probe (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (A : MatQ) (z : ℂ) :
    FiniteThreeLevelEnvironmentLift.thermal b ℏ γ t (A ⊗ₖ (z • Matrix.single 0 1 1)) =
      A ⊗ₖ ((z*(Real.exp (-γ*t):ℂ)*Complex.exp (Complex.I*(theta b ℏ t:ℝ))) •
        Matrix.single (0:Q) 1 1) := by
  rw [FiniteThreeLevelEnvironmentLift.thermal, FiniteThreeLevelEnvironmentLift.product_action,
    krausMap_smul, traceless_channel b ℏ γ t hγ ht _ (single_off_diagonal_trace 0 1 (by decide)),
    phase_E01, smul_smul, smul_smul]

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelMemoryReadout
