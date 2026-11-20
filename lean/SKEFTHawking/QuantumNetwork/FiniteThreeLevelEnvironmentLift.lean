import SKEFTHawking.QuantumNetwork.FiniteThreeLevelThermalPhase
import SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
import SKEFTHawking.QuantumNetwork.MaxEntNegativity
/-!
# Retained qutrit thermal dynamics

The joint carrier is a qutrit system and a qutrit environment. Actual Kraus
operators act on the environment factor. Block identities hold for arbitrary
complex correlated inputs; positivity and Hermitian norm premises are separate.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelEnvironmentLift
open Matrix
open scoped Kronecker BigOperators ComplexOrder
open FinitePositiveKernel.GibbsObservable
abbrev Q := Fin 3
abbrev MatQ := Matrix Q Q ℂ
abbrev Joint := Q × Q
abbrev MatJoint := Matrix Joint Joint ℂ
/-- Preserve the Kraus index while acting on the second factor. -/
def liftKraus {m : ℕ} (K : Fin m → MatQ) (k : Fin m) : MatJoint := 1 ⊗ₖ K k
def liftState {m : ℕ} (K : Fin m → MatQ) (X : MatJoint) : MatJoint := krausMap (liftKraus K) X
def liftObservable {m : ℕ} (K : Fin m → MatQ) (A : MatJoint) : MatJoint := Channel.heisenberg (liftKraus K) A
/-- The environment matrix at a fixed pair of spectator indices. -/
def block (X : MatJoint) (s t : Q) : MatQ := fun e f => X (s,e) (t,f)
theorem sandwich_block (K : MatQ) (X : MatJoint) (s t e f : Q) :
 (((1 : MatQ) ⊗ₖ K) * X * ((1 : MatQ) ⊗ₖ K)ᴴ) (s,e) (t,f) = (K * block X s t * Kᴴ) e f := by
 simp [Matrix.conjTranspose_kronecker, Matrix.mul_apply, Fintype.sum_prod_type, block, Matrix.one_apply]
theorem liftState_block {m : ℕ} (K : Fin m → MatQ) (X : MatJoint) (s t : Q) :
 block (liftState K X) s t = krausMap K (block X s t) := by
 ext e f
 simp only [block, liftState, krausMap, Matrix.sum_apply, liftKraus, sandwich_block]
theorem sum_kronecker_right {κ : Type*} [Fintype κ] (K : κ → MatQ) :
 (∑ k, (1 : MatQ) ⊗ₖ K k) = (1 : MatQ) ⊗ₖ (∑ k, K k) := by
 ext ⟨s,e⟩ ⟨t,f⟩
 simp [Matrix.sum_apply, Finset.mul_sum]
theorem normalized {m : ℕ} {K : Fin m → MatQ} (hK : IsKrausChannel K) :
 IsKrausChannel (liftKraus K) := by
 unfold IsKrausChannel liftKraus
 simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
   ← Matrix.mul_kronecker_mul, one_mul]
 rw [sum_kronecker_right, hK, Matrix.one_kronecker_one]
theorem product_action {m : ℕ} (K : Fin m → MatQ) (A B : MatQ) :
 liftState K (A ⊗ₖ B) = A ⊗ₖ krausMap K B := by
 unfold liftState krausMap liftKraus
 simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
  ← Matrix.mul_kronecker_mul, one_mul, mul_one]
 ext ⟨s,e⟩ ⟨t,f⟩
 simp [Matrix.sum_apply, Finset.mul_sum]
theorem observable_product_action {m : ℕ} (K : Fin m → MatQ) (A B : MatQ) :
 liftObservable K (A ⊗ₖ B) = A ⊗ₖ Channel.heisenberg K B := by
 unfold liftObservable Channel.heisenberg liftKraus
 simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
  ← Matrix.mul_kronecker_mul, one_mul, mul_one]
 ext ⟨s,e⟩ ⟨t,f⟩
 simp [Matrix.sum_apply, Finset.mul_sum]
theorem liftObservable_block {m : ℕ} (K : Fin m → MatQ) (A : MatJoint) (s t : Q) :
 block (liftObservable K A) s t = Channel.heisenberg K (block A s t) := by
 have h : liftObservable K A = liftState (fun k => (K k)ᴴ) A := by
  simp [liftObservable, liftState, liftKraus, Channel.heisenberg, krausMap,
   Matrix.conjTranspose_kronecker]
 rw [h, liftState_block]
 simp [krausMap, Channel.heisenberg]
theorem trace_duality {m : ℕ} (K : Fin m → MatQ) (A X : MatJoint) :
 (A * liftState K X).trace = (liftObservable K A * X).trace := by
 rw [Matrix.trace_mul_comm, liftState, liftObservable, ← Channel.trace_duality,
  Matrix.trace_mul_comm]
/-- Literal trace over E; this preserves the first-factor S carrier. -/
def ptrace2 (X : MatJoint) : MatQ := fun s t => ∑ e, X (s,e) (t,e)
theorem ptrace2_kronecker (A B : MatQ) : ptrace2 (A ⊗ₖ B) = B.trace • A := by
 ext s t
 simp [ptrace2, Matrix.trace, Finset.mul_sum, mul_comm]
theorem ptrace2_sub (X Y : MatJoint) : ptrace2 (X - Y) = ptrace2 X - ptrace2 Y := by
 ext s t; simp [ptrace2, Finset.sum_sub_distrib]
theorem ptrace2_smul (c : ℂ) (X : MatJoint) : ptrace2 (c • X) = c • ptrace2 X := by
 ext s t; simp [ptrace2, Finset.mul_sum]
theorem ptrace2_block (X : MatJoint) (s t : Q) :
 ptrace2 X s t = (block X s t).trace := rfl
/-- Trace preservation of every environment block proves the arbitrary-joint invariant. -/
theorem spectator {m : ℕ} {K : Fin m → MatQ} (hK : IsKrausChannel K) (X : MatJoint) :
 ptrace2 (liftState K X) = ptrace2 X := by
 ext s t
 rw [ptrace2_block, liftState_block, trace_krausMap hK, ← ptrace2_block]
def localBranch (L : MatQ) (X : MatJoint) : MatJoint :=
 (L ⊗ₖ (1 : MatQ)) * X * (L ⊗ₖ (1 : MatQ))ᴴ
theorem local_environment_commute (L K : MatQ) :
 ((1 : MatQ) ⊗ₖ K) * (L ⊗ₖ (1 : MatQ)) =
 (L ⊗ₖ (1 : MatQ)) * ((1 : MatQ) ⊗ₖ K) := by
 simp only [← Matrix.mul_kronecker_mul, one_mul, mul_one]
theorem sandwich_local_commute (K L : MatQ) (X : MatJoint) :
 ((1 : MatQ) ⊗ₖ K) * localBranch L X * ((1 : MatQ) ⊗ₖ K)ᴴ =
 localBranch L (((1 : MatQ) ⊗ₖ K) * X * ((1 : MatQ) ⊗ₖ K)ᴴ) := by
 have h := local_environment_commute L K
 have hs := congrArg Matrix.conjTranspose h
 simp only [Matrix.conjTranspose_mul] at hs
 unfold localBranch
 calc
  _ = (((1 : MatQ) ⊗ₖ K) * (L ⊗ₖ (1 : MatQ))) * X *
    ((L ⊗ₖ (1 : MatQ))ᴴ * ((1 : MatQ) ⊗ₖ K)ᴴ) := by noncomm_ring
  _ = ((L ⊗ₖ (1 : MatQ)) * ((1 : MatQ) ⊗ₖ K)) * X *
    (((1 : MatQ) ⊗ₖ K)ᴴ * (L ⊗ₖ (1 : MatQ))ᴴ) := by rw [h, hs]
  _ = _ := by noncomm_ring
theorem liftState_localBranch {m : ℕ} (K : Fin m → MatQ) (L : MatQ) (X : MatJoint) :
 liftState K (localBranch L X) = localBranch L (liftState K X) := by
 simp only [liftState, krausMap, liftKraus, sandwich_local_commute]
 simp only [localBranch, Matrix.mul_sum, Matrix.sum_mul]
/-- A single actual S-local branch propagates the marginal without conditioning. -/
theorem ptrace2_localBranch (L : MatQ) (X : MatJoint) :
 ptrace2 (localBranch L X) = L * ptrace2 X * Lᴴ := by
 ext s t
 fin_cases s <;> fin_cases t <;>
  simp [ptrace2, localBranch, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three] <;> ring
theorem liftState_sum {m : ℕ} (K : Fin m → MatQ) {ι : Type*} [Fintype ι]
 (X : ι → MatJoint) : liftState K (∑ i, X i) = ∑ i, liftState K (X i) := by
 simp only [liftState, krausMap, Matrix.mul_sum, Matrix.sum_mul]
 rw [Finset.sum_comm]
theorem ptrace2_sum {ι : Type*} [Fintype ι] (X : ι → MatJoint) :
 ptrace2 (∑ i, X i) = ∑ i, ptrace2 (X i) := by
 ext s t
 simp only [ptrace2, Matrix.sum_apply]
 rw [Finset.sum_comm]
theorem instrument_branch_commute {m o : ℕ} (K : Fin m → MatQ)
 (I : FiniteInstrument Q o) (a : Fin o) (X : MatJoint) :
 liftState K ((I.lift Q).branch a X) = (I.lift Q).branch a (liftState K X) := by
 change liftState K (∑ k, localBranch (I.operators a k) X) =
  ∑ k, localBranch (I.operators a k) (liftState K X)
 rw [liftState_sum]
 simp_rw [liftState_localBranch]
theorem instrument_branch_marginal {o : ℕ} (I : FiniteInstrument Q o)
 (a : Fin o) (X : MatJoint) :
 ptrace2 ((I.lift Q).branch a X) = I.branch a (ptrace2 X) := by
 change ptrace2 (∑ k, localBranch (I.operators a k) X) =
  ∑ k, I.operators a k * ptrace2 X * (I.operators a k)ᴴ
 rw [ptrace2_sum]
 simp_rw [ptrace2_localBranch]
theorem same_marginal_local {o : ℕ} (I : FiniteInstrument Q o) (a : Fin o)
 {X Y : MatJoint} (h : ptrace2 X = ptrace2 Y) :
 ptrace2 ((I.lift Q).branch a X) = ptrace2 ((I.lift Q).branch a Y) := by
 rw [instrument_branch_marginal, instrument_branch_marginal, h]
theorem same_marginal_environment {m : ℕ} {K : Fin m → MatQ}
 (hK : IsKrausChannel K) {X Y : MatJoint} (h : ptrace2 X = ptrace2 Y) :
 ptrace2 (liftState K X) = ptrace2 (liftState K Y) := by
 rw [spectator hK, spectator hK, h]
theorem liftState_trace {m : ℕ} {K : Fin m → MatQ} (hK : IsKrausChannel K) (X : MatJoint) :
 (liftState K X).trace = X.trace := trace_krausMap (normalized hK) X
theorem liftState_posSemidef {m : ℕ} (K : Fin m → MatQ) {X : MatJoint} (hX : X.PosSemidef) :
 (liftState K X).PosSemidef := krausMap_posSemidef (liftKraus K) hX
theorem liftState_isHermitian {m : ℕ} (K : Fin m → MatQ) {X : MatJoint} (hX : X.IsHermitian) :
 (liftState K X).IsHermitian := krausMap_isHermitian (liftKraus K) hX
theorem liftState_density {m : ℕ} {K : Fin m → MatQ} (hK : IsKrausChannel K)
 {X : MatJoint} (hX : IsDensityOperator X) : IsDensityOperator (liftState K X) :=
 krausMap_isDensityOperator (normalized hK) hX

open FiniteThreeLevelThermalPhase (channelKraus equilibrium)
def thermal (b ℏ γ t : ℝ) (X : MatJoint) : MatJoint :=
  liftState (channelKraus b ℏ γ t) X

theorem thermal_normalized (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    IsKrausChannel (liftKraus (channelKraus b ℏ γ t)) :=
  normalized (FiniteThreeLevelThermalPhase.channel_normalized b ℏ γ t hγ ht)

theorem thermal_spectator (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (X : MatJoint) :
    ptrace2 (thermal b ℏ γ t X) = ptrace2 X :=
  spectator (FiniteThreeLevelThermalPhase.channel_normalized b ℏ γ t hγ ht) X

theorem thermal_density (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {X : MatJoint} (hX : IsDensityOperator X) : IsDensityOperator (thermal b ℏ γ t X) :=
  liftState_density (FiniteThreeLevelThermalPhase.channel_normalized b ℏ γ t hγ ht) hX

def phaseUnitary (b ℏ t : ℝ) : MatJoint := 1 ⊗ₖ FiniteThreeLevelThermalPhase.U b ℏ t

theorem thermal_action (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (X : MatJoint) :
    thermal b ℏ γ t X =
      (Real.exp (-γ*t):ℂ) • (phaseUnitary b ℏ t * X * (phaseUnitary b ℏ t)ᴴ) +
      ((1-Real.exp (-γ*t):ℝ):ℂ) • (ptrace2 X ⊗ₖ equilibrium) := by
  ext ⟨s,e⟩ ⟨u,f⟩
  change block (liftState (channelKraus b ℏ γ t) X) s u e f = _
  rw [liftState_block, FiniteThreeLevelThermalPhase.channel_action b ℏ γ t hγ ht,
    FiniteThreeLevelThermalPhase.reset_action γ t hγ ht,
    FiniteThreeLevelThermalPhase.phase_add,
    FiniteThreeLevelThermalPhase.phase_smul,
    FiniteThreeLevelThermalPhase.phase_smul,
    FiniteThreeLevelThermalPhase.phase_smul]
  rw [show FiniteThreeLevelThermalPhase.phase b ℏ t equilibrium = equilibrium from
    FiniteThreeLevelThermalPhase.phase_diagonal b ℏ t _]
  rw [FiniteThreeLevelThermalPhase.phase_sandwich]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, phaseUnitary,
    sandwich_block, Matrix.kroneckerMap_apply, ptrace2_block]


/-- Reset cancellation uses equality of the system marginal at this exact cut. -/
theorem thermal_difference (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {X Y : MatJoint} (h : ptrace2 X = ptrace2 Y) :
    thermal b ℏ γ t X - thermal b ℏ γ t Y =
      (Real.exp (-γ*t):ℂ) • (phaseUnitary b ℏ t * (X-Y) * (phaseUnitary b ℏ t)ᴴ) := by
  rw [thermal_action b ℏ γ t hγ ht, thermal_action b ℏ γ t hγ ht, h]
  simp only [mul_sub, sub_mul, smul_sub]
  abel

theorem phaseUnitary_unitary (b ℏ t : ℝ) : phaseUnitary b ℏ t ∈ Matrix.unitaryGroup Joint ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change phaseUnitary b ℏ t * (phaseUnitary b ℏ t)ᴴ = 1
  simp only [phaseUnitary, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, one_mul]
  rw [show FiniteThreeLevelThermalPhase.U b ℏ t * (FiniteThreeLevelThermalPhase.U b ℏ t)ᴴ = 1 from
    Matrix.mem_unitaryGroup_iff.mp (FiniteThreeLevelThermalPhase.U_unitary b ℏ t),
    Matrix.one_kronecker_one]

/-- The retained distance law is stated on the Hermitian physical domain. -/
theorem thermal_distance (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {X Y : MatJoint} (_hX : X.IsHermitian) (_hY : Y.IsHermitian)
    (h : ptrace2 X = ptrace2 Y) :
    traceDist (thermal b ℏ γ t X) (thermal b ℏ γ t Y) =
      Real.exp (-γ*t) * traceDist X Y := by
  unfold traceDist
  rw [thermal_difference b ℏ γ t hγ ht h,
    traceNorm_smul_nonneg (Real.exp_pos _).le,
    traceNorm_unitary_conj (Matrix.mem_unitaryGroup_iff'.mp (phaseUnitary_unitary b ℏ t))]
  ring

open FiniteAdaptiveReadoutDiscrimination FiniteAdaptiveReadoutRobustness
variable {H : Type*} [Fintype H]

def inducedEffect (I : FiniteInstrument Joint 2) (a : Fin 2) : MatJoint :=
  ∑ k, (I.operators a k)ᴴ * I.operators a k

theorem inducedEffect_positive (I : FiniteInstrument Joint 2) (a : Fin 2) :
    (inducedEffect I a).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro k _
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem inducedEffect_sum (I : FiniteInstrument Joint 2) :
    inducedEffect I 0 + inducedEffect I 1 = 1 := by
  simpa only [Fin.sum_univ_two, inducedEffect] using I.normalized

theorem inducedEffect_complement (I : FiniteInstrument Joint 2) :
    1-inducedEffect I 0 = inducedEffect I 1 := by
  rw [← inducedEffect_sum I]; abel

theorem inducedEffect_admissible (I : FiniteInstrument Joint 2) :
    IsBinaryPOVM (inducedEffect I 0) :=
  ⟨inducedEffect_positive I 0, by
    rw [inducedEffect_complement]; exact inducedEffect_positive I 1⟩

theorem inducedEffect_weight (I : FiniteInstrument Joint 2) (a : Fin 2) (X : MatJoint) :
    I.weight a X = (inducedEffect I a * X).trace.re := by
  simp only [FiniteInstrument.weight, FiniteInstrument.branch, krausMap, inducedEffect,
    Finset.sum_mul, Matrix.trace_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact Matrix.trace_mul_cycle _ _ _

theorem instrumentError_effect (A B : H → MatJoint) (I : H → FiniteInstrument Joint 2) :
    instrumentError A B I = readoutError A B (fun h => inducedEffect (I h) 0) := by
  simp only [instrumentError, readoutTable, inducedEffect_weight, readoutError,
    inducedEffect_complement]

/-- The objective ranges over every finite normalized binary Kraus instrument. -/
def PhysicalErrors (A B : H → MatJoint) : Set ℝ :=
  {x | ∃ I : H → FiniteInstrument Joint 2, instrumentError A B I = x}

theorem physical_isLeast {A B : H → MatJoint}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    IsLeast (PhysicalErrors A B) ((1-branchDistance A B)/2) := by
  refine ⟨⟨optimalReadout hA hB, optimalReadout_error hA hB⟩, ?_⟩
  rintro x ⟨I,rfl⟩
  rw [instrumentError_effect]
  exact readoutError_lower hA hB (fun h => inducedEffect_admissible (I h))

theorem thermal_branchFamily (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {A : H → MatJoint} (hA : IsBranchFamily A) :
    IsBranchFamily (fun h => thermal b ℏ γ t (A h)) := by
  refine ⟨fun h => liftState_posSemidef _ (hA.1 h), ?_⟩
  simp only [thermal, liftState_trace (FiniteThreeLevelThermalPhase.channel_normalized b ℏ γ t hγ ht)]
  exact hA.2

theorem thermal_branchDistance (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {A B : H → MatJoint} (hA : ∀ h, (A h).IsHermitian) (hB : ∀ h, (B h).IsHermitian)
    (hm : ∀ h, ptrace2 (A h) = ptrace2 (B h)) :
    branchDistance (fun h => thermal b ℏ γ t (A h)) (fun h => thermal b ℏ γ t (B h)) =
      Real.exp (-γ*t) * branchDistance A B := by
  simp only [branchDistance, thermal_distance b ℏ γ t hγ ht (hA _) (hB _) (hm _), Finset.mul_sum]

theorem thermal_physical_isLeast (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {A B : H → MatJoint} (hA : IsBranchFamily A) (hB : IsBranchFamily B)
    (hm : ∀ h, ptrace2 (A h) = ptrace2 (B h)) :
    IsLeast (PhysicalErrors (fun h => thermal b ℏ γ t (A h)) (fun h => thermal b ℏ γ t (B h)))
      ((1-Real.exp (-γ*t)*branchDistance A B)/2) := by
  have hd := thermal_branchDistance b ℏ γ t hγ ht
    (fun h => (hA.1 h).isHermitian) (fun h => (hB.1 h).isHermitian) hm
  rw [← hd]
  exact physical_isLeast (thermal_branchFamily b ℏ γ t hγ ht hA)
    (thermal_branchFamily b ℏ γ t hγ ht hB)


open FinitePositiveKernel OpenSystems GibbsMultilevelReflection

theorem block_ext {X Y : MatJoint} (h : ∀ s t, block X s t = block Y s t) : X = Y := by
  ext ⟨s,e⟩ ⟨t,f⟩
  exact congrArg (fun B : MatQ => B e f) (h s t)

def gibbsResetKraus := GibbsReset.resetKraus three.w
def gibbsReset (X : MatJoint) : MatJoint := liftState gibbsResetKraus X

theorem gibbsReset_normalized : IsKrausChannel (liftKraus gibbsResetKraus) :=
  normalized (GibbsReset.reset_normalized three.w (fun i => (three.positive i).le) three.normalized)

theorem gibbsReset_action (X : MatJoint) : gibbsReset X = ptrace2 X ⊗ₖ equilibrium := by
  ext ⟨s,e⟩ ⟨t,f⟩
  change block (liftState gibbsResetKraus X) s t e f = _
  rw [liftState_block]
  unfold gibbsResetKraus
  rw [GibbsReset.reset_state three.w (fun i => (three.positive i).le)]
  rfl

def weightedPartial (A : MatJoint) : MatQ := fun s t =>
  (equilibrium * block A s t).trace

theorem weightedPartial_entries (A : MatJoint) (s t : Q) :
    weightedPartial A s t = ∑ e, equilibrium e e * A (s,e) (t,e) := by
  simp [weightedPartial, equilibrium, DiagonalLindblad.density, Matrix.trace,
    Matrix.diagonal_mul, block]

theorem gibbsReset_observable (A : MatJoint) :
    liftObservable gibbsResetKraus A = weightedPartial A ⊗ₖ (1 : MatQ) := by
  ext ⟨s,e⟩ ⟨t,f⟩
  change block (liftObservable gibbsResetKraus A) s t e f = _
  rw [liftObservable_block, gibbsResetKraus,
    GibbsReset.reset_observable three.w (fun i => (three.positive i).le)]
  rfl

theorem reset_equal_marginal {X Y : MatJoint} (h : ptrace2 X = ptrace2 Y) :
    gibbsReset X = gibbsReset Y := by
  rw [gibbsReset_action, gibbsReset_action, h]

theorem left_block (K : MatQ) (X : MatJoint) (s t : Q) :
    block (((1 : MatQ) ⊗ₖ K) * X) s t = K * block X s t := by
  ext e f
  simp [block, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]

theorem right_block (K : MatQ) (X : MatJoint) (s t : Q) :
    block (X * ((1 : MatQ) ⊗ₖ K)) s t = block X s t * K := by
  ext e f
  simp [block, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]

/-- The actual lifted jump generator, on every environment block. -/
theorem generator_block {κ : Type*} [Fintype κ] (H : MatQ) (L : κ → MatQ)
    (X : MatJoint) (s t : Q) :
    block (lindbladGenerator ((1 : MatQ) ⊗ₖ H) (fun k => (1 : MatQ) ⊗ₖ L k) X) s t =
      lindbladGenerator H L (block X s t) := by
  have hsum : (∑ k, ((1 : MatQ) ⊗ₖ L k)ᴴ * ((1 : MatQ) ⊗ₖ L k)) =
      (1 : MatQ) ⊗ₖ (∑ k, (L k)ᴴ * L k) := by
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, one_mul, sum_kronecker_right]
  simp only [lindbladGenerator, LinearMap.add_apply, lindbladHamPart_apply,
    lindbladJump_apply, lindbladAnticommPart_apply, hsum]
  ext e f
  simp only [block, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    Matrix.sum_apply, sandwich_block]
  have hleft := congrArg (fun M : MatQ => M e f) (left_block H X s t)
  have hright := congrArg (fun M : MatQ => M e f) (right_block H X s t)
  have hleft' := congrArg (fun M : MatQ => M e f) (left_block (∑ k, (L k)ᴴ * L k) X s t)
  have hright' := congrArg (fun M : MatQ => M e f) (right_block (∑ k, (L k)ᴴ * L k) X s t)
  simp only [block] at hleft hright hleft' hright'
  rw [hleft, hright, hleft', hright']

def thermalGenerator (b ℏ γ : ℝ) :=
  lindbladGenerator ((1 : MatQ) ⊗ₖ FiniteThreeLevelThermalPhase.scaledH b ℏ)
    (fun k => (1 : MatQ) ⊗ₖ FiniteThreeLevelThermalPhase.jumps γ k)

theorem actual_generator (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (X : MatJoint) :
    thermalGenerator b ℏ γ X =
      -Complex.I • (((1 : MatQ) ⊗ₖ FiniteThreeLevelThermalPhase.scaledH b ℏ) * X -
        X * ((1 : MatQ) ⊗ₖ FiniteThreeLevelThermalPhase.scaledH b ℏ)) +
      (γ:ℂ) • (ptrace2 X ⊗ₖ equilibrium - X) := by
  apply block_ext
  intro s t
  rw [thermalGenerator, generator_block,
    FiniteThreeLevelThermalPhase.actual_generator b ℏ γ hγ]
  ext e f
  simp only [block, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    Matrix.kroneckerMap_apply, ptrace2_block]
  have hl := congrArg (fun M : MatQ => M e f) (left_block (FiniteThreeLevelThermalPhase.scaledH b ℏ) X s t)
  have hr := congrArg (fun M : MatQ => M e f) (right_block (FiniteThreeLevelThermalPhase.scaledH b ℏ) X s t)
  simp only [block] at hl hr
  rw [hl, hr]


theorem equilibrium_phase_trace (b ℏ t : ℝ) (A : MatQ) :
    (equilibrium * FiniteThreeLevelThermalPhase.phase b ℏ t A).trace =
      (equilibrium * A).trace := by
  simp [equilibrium, DiagonalLindblad.density, Matrix.trace, Matrix.diagonal_mul,
    FiniteThreeLevelThermalPhase.phase_projector_diagonal]

theorem channel_observable_action (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (A : MatQ) :
    Channel.heisenberg (channelKraus b ℏ γ t) A =
      (Real.exp (-γ*t):ℂ) • FiniteThreeLevelThermalPhase.phase b ℏ (-t) A +
      ((1-Real.exp (-γ*t):ℝ):ℂ) • ((equilibrium * A).trace • (1 : MatQ)) := by
  rw [FiniteThreeLevelThermalPhase.channel_observable, GibbsBlockRelaxation.timeKraus]
  obtain ⟨ha,hb,hc⟩ := GibbsBlockRelaxation.time_coefficients_nonneg γ 0 t hγ le_rfl ht
  rw [GibbsBlockRelaxation.mixture_observable _ _ (fun i => (three.positive i).le) _ _ _ ha hb hc]
  simp only [GibbsBlockRelaxation.slow, GibbsBlockRelaxation.fast, add_zero, sub_self,
    Complex.ofReal_zero, zero_smul, add_zero]
  change _ • ((equilibrium * FiniteThreeLevelThermalPhase.phase b ℏ (-t) A).trace • 1) + _ = _
  rw [equilibrium_phase_trace]
  exact add_comm _ _

theorem phaseUnitary_adjoint (b ℏ t : ℝ) : (phaseUnitary b ℏ t)ᴴ = phaseUnitary b ℏ (-t) := by
  simp only [phaseUnitary, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    FiniteThreeLevelThermalPhase.U, GibbsHamiltonianRelaxation.unitary_adjoint]

/-- Full reverse observable action; the unitary phase is the adjoint phase. -/
theorem thermal_observable_action (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (A : MatJoint) :
    liftObservable (channelKraus b ℏ γ t) A =
      (Real.exp (-γ*t):ℂ) • ((phaseUnitary b ℏ t)ᴴ * A * phaseUnitary b ℏ t) +
      ((1-Real.exp (-γ*t):ℝ):ℂ) • (weightedPartial A ⊗ₖ (1 : MatQ)) := by
  have hu := phaseUnitary_adjoint b ℏ (-t)
  simp only [neg_neg] at hu
  rw [phaseUnitary_adjoint, ← hu]
  ext ⟨s,e⟩ ⟨u,f⟩
  change block (liftObservable (channelKraus b ℏ γ t) A) s u e f = _
  rw [liftObservable_block, channel_observable_action b ℏ γ t hγ ht,
    FiniteThreeLevelThermalPhase.phase_sandwich]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, phaseUnitary,
    sandwich_block, Matrix.kroneckerMap_apply, weightedPartial]

theorem thermal_zero_time (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (X : MatJoint) :
    thermal b ℏ γ 0 X = X := by
  apply block_ext
  intro s t
  rw [thermal, liftState_block, FiniteThreeLevelThermalPhase.channel_zero_time b ℏ γ hγ]

theorem thermal_zero_rate (b ℏ t : ℝ) (ht : 0 ≤ t) (X : MatJoint) :
    thermal b ℏ 0 t X = phaseUnitary b ℏ t * X * (phaseUnitary b ℏ t)ᴴ := by
  rw [thermal_action b ℏ 0 t le_rfl ht]
  simp

theorem finite_retention_positive (γ t : ℝ) : 0 < Real.exp (-γ*t) := Real.exp_pos _

theorem stationary_product (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (A : MatQ) :
    thermal b ℏ γ t (A ⊗ₖ equilibrium) = A ⊗ₖ equilibrium := by
  rw [thermal, product_action, FiniteThreeLevelThermalPhase.channel_stationary b ℏ γ t hγ ht]


def spectatorState (a : Q) : MatJoint := projector a ⊗ₖ equilibrium

theorem spectatorState_density (a : Q) : IsDensityOperator (spectatorState a) := by
  exact ⟨(FiniteAdaptiveGibbsReadout.projector_density a).1.kronecker
    FiniteThreeLevelThermalPhase.equilibrium_density.1, by
    rw [spectatorState, Matrix.trace_kronecker, projector_trace,
      FiniteThreeLevelThermalPhase.equilibrium_density.2, one_mul]⟩

theorem tensor_distance (A B T : MatQ) (hT : IsDensityOperator T) :
    traceDist (A ⊗ₖ T) (B ⊗ₖ T) = traceDist A B := by
  unfold traceDist
  have hsub : A ⊗ₖ T - B ⊗ₖ T = (A-B) ⊗ₖ T := by
    ext ⟨i,j⟩ ⟨k,l⟩; simp [sub_mul]
  rw [hsub, traceNorm_kronecker, traceNorm_density_eq_one hT]
  simp

theorem spectatorState_distance : traceDist (spectatorState 0) (spectatorState 1) = 1 := by
  rw [spectatorState, spectatorState, tensor_distance _ _ _ FiniteThreeLevelThermalPhase.equilibrium_density]
  exact FiniteAdaptiveGibbsReadout.projector_pair_distance

/-- Information held only by S survives any amount of E-only thermal evolution. -/
theorem no_global_strict_contraction (b ℏ γ t c : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hc : c < 1) :
    ¬ ∀ X Y : MatJoint, IsDensityOperator X → IsDensityOperator Y →
      traceDist (thermal b ℏ γ t X) (thermal b ℏ γ t Y) ≤ c * traceDist X Y := by
  intro h
  have hh := h (spectatorState 0) (spectatorState 1)
    (spectatorState_density 0) (spectatorState_density 1)
  change traceDist (thermal b ℏ γ t (projector 0 ⊗ₖ equilibrium))
    (thermal b ℏ γ t (projector 1 ⊗ₖ equilibrium)) ≤ _ at hh
  rw [stationary_product b ℏ γ t hγ ht, stationary_product b ℏ γ t hγ ht] at hh
  change traceDist (spectatorState 0) (spectatorState 1) ≤ _ at hh
  rw [spectatorState_distance, mul_one] at hh
  linarith

def swapKraus : Fin 1 → MatJoint := fun _ => swapMat 3

theorem swap_normalized : IsKrausChannel swapKraus := by
  simp [IsKrausChannel, swapKraus, swapMat_isHermitian, swapMat_mul_self]

def swap (X : MatJoint) : MatJoint := krausMap swapKraus X

theorem swap_entry (X : MatJoint) (i j k l : Q) :
    swap X (i,j) (k,l) = X (j,i) (l,k) := by
  simp only [swap, krausMap, swapKraus, Fin.sum_univ_one, swapMat_isHermitian]
  simp [swapMat, Matrix.mul_apply, Fintype.sum_prod_type, Prod.ext_iff, ite_and]

theorem swap_tensor (A B : MatQ) : swap (A ⊗ₖ B) = B ⊗ₖ A := by
  ext ⟨i,j⟩ ⟨k,l⟩
  rw [swap_entry]
  simp [mul_comm]

/-- SWAP can invalidate the required equal-system-marginal premise. -/
theorem swap_breaks_same_marginal :
    ptrace2 (projector 0 ⊗ₖ projector 0) = ptrace2 (projector 0 ⊗ₖ projector 1) ∧
    ptrace2 (swap (projector 0 ⊗ₖ projector 0)) ≠
      ptrace2 (swap (projector 0 ⊗ₖ projector 1)) := by
  simp only [swap_tensor, ptrace2_kronecker, projector_trace, one_smul]
  refine ⟨True.intro, ?_⟩
  intro h
  have hh := congrArg (fun M : MatQ => M 0 0) h
  norm_num [projector] at hh

theorem same_marginal_trace {X Y : MatJoint} (h : ptrace2 X = ptrace2 Y) :
    X.trace = Y.trace := by
  have hh := congrArg Matrix.trace h
  simpa only [Matrix.trace, Matrix.diag, ptrace2, Fintype.sum_prod_type] using hh

omit [Fintype H] in
theorem thermal_history_equal (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {A B : H → MatJoint} (hm : ∀ h, ptrace2 (A h) = ptrace2 (B h)) (h : H) :
    (thermal b ℏ γ t (A h)).trace.re = (thermal b ℏ γ t (B h)).trace.re := by
  rw [thermal, thermal, liftState_trace (FiniteThreeLevelThermalPhase.channel_normalized b ℏ γ t hγ ht),
    liftState_trace (FiniteThreeLevelThermalPhase.channel_normalized b ℏ γ t hγ ht), same_marginal_trace (hm h)]

/-- The original physical propagator acts on each environment block. -/
theorem thermal_block_propagator (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (X : MatJoint) (s u : Q) :
    block (thermal b ℏ γ t X) s u =
      lindbladPropagatorAction (FiniteThreeLevelThermalPhase.scaledH b ℏ)
        (FiniteThreeLevelThermalPhase.jumps γ) t (block X s u) := by
  rw [thermal, liftState_block, FiniteThreeLevelThermalPhase.channel_propagator b ℏ γ t hγ ht]

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelEnvironmentLift
