import SKEFTHawking.FiniteGibbsHamiltonianRelaxation
import SKEFTHawking.QuantumNetwork.FiniteAdaptiveGibbsReadout
import SKEFTHawking.QuantumNetwork.UnitaryDiamond

/-!
# Three-level thermal Hamiltonian and computational histories

The physical energies are independent of the reference state. Both Hamiltonian gaps
are retained by the actual normalized Kraus family and its GKSL propagator.
Computational erasure concerns complete unnormalized branches on arbitrary complex
inputs. Hermitian distance statements retain their separate domain.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelThermalPhase
open Matrix FinitePositiveKernel DiagonalLindblad GibbsObservable
open OpenSystems FiniteInterventionProcess GibbsMultilevelReflection GibbsMultilevelProcess
open scoped ComplexOrder Kronecker Matrix.Norms.L2Operator

abbrev Q := Fin 3
abbrev MatQ := Matrix Q Q ℂ
abbrev MatJoint := Matrix (Q × Unit) (Q × Unit) ℂ
def delta : ℝ := Real.log (3/2)
def energies (b : ℝ) : Q → ℝ := ![0, delta/b, Real.log 3/b]
def thermalH (b : ℝ) : MatQ := density (energies b)
def frequencies (b ℏ : ℝ) : Q → ℝ := fun i ↦ energies b i / ℏ
def scaledH (b ℏ : ℝ) : MatQ := density (frequencies b ℏ)
def equilibrium : MatQ := density three.w
theorem delta_pos : 0 < delta := Real.log_pos (by norm_num)
theorem thermalH_hermitian (b : ℝ) : (thermalH b).IsHermitian :=
  GibbsHamiltonianRelaxation.density_hermitian _
theorem thermalH_not_scalar {b : ℝ} (hb : 0 < b) (z : ℂ) :
    thermalH b ≠ z • (1 : MatQ) := by
  intro he
  have h0 := congrArg (fun A : MatQ ↦ A 0 0) he
  have h1 := congrArg (fun A : MatQ ↦ A 1 1) he
  simp [thermalH, density, energies] at h0 h1
  have hz : delta/b = 0 := by exact_mod_cast h1.trans h0.symm
  exact (ne_of_gt (div_pos delta_pos hb)) hz
theorem thermalH_ne_zero {b : ℝ} (hb : 0 < b) : thermalH b ≠ 0 := by
  simpa using thermalH_not_scalar hb 0
theorem exp_neg_delta : Real.exp (-delta) = 2/3 := by
  rw [Real.exp_neg, delta, Real.exp_log (by norm_num : (0:ℝ) < 3/2)]
  norm_num
theorem boltzmann_thermal {b : ℝ} (hb : 0 < b) :
    FiniteGibbsClock.boltzmann (thermalH b) b =
      Matrix.diagonal (![1,2/3,1/3] : Q → ℂ) := by
  have he : (-b) • thermalH b =
      Matrix.diagonal (![0, (-delta : ℂ), (-Real.log 3 : ℂ)] : Q → ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [thermalH, energies, density, Complex.real_smul] <;> field_simp
  have h1 : Complex.exp (-(delta:ℂ)) = 2/3 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, exp_neg_delta]
    norm_num
  have h2 : Complex.exp (-(Real.log 3:ℂ)) = 1/3 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg,
      Real.exp_log (by norm_num : (0:ℝ)<3)]
    norm_num
  rw [FiniteGibbsClock.boltzmann, he, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [← Complex.exp_eq_exp_ℂ, h1]
  simpa using h2
theorem partition_thermal {b : ℝ} (hb : 0 < b) :
    FiniteGibbsClock.partition (thermalH b) b = 2 := by
  rw [FiniteGibbsClock.partition, boltzmann_thermal hb]
  norm_num [Matrix.trace, Fin.sum_univ_succ]
theorem gibbs_thermal {b : ℝ} (hb : 0 < b) :
    FiniteGibbsClock.gibbs (thermalH b) b = equilibrium := by
  rw [FiniteGibbsClock.gibbs, partition_thermal hb, boltzmann_thermal hb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [equilibrium, density, three, GibbsReset.threeWeights, Complex.real_smul]
theorem equilibrium_density : IsDensityOperator equilibrium := by
  rw [← gibbs_thermal (by norm_num : (0:ℝ)<1)]
  exact FiniteGibbsClock.gibbs_density (thermalH_hermitian 1) 1
theorem equilibrium_posDef : equilibrium.PosDef := density_posDef three.w three.positive
theorem gibbs_shift {b : ℝ} (hb : 0 < b) (e : ℝ) :
    FiniteGibbsClock.gibbs (thermalH b + (e : ℂ) • 1) b = equilibrium := by
  rw [FiniteGibbsClock.gibbs_energy_shift, gibbs_thermal hb]
theorem gibbs_two_scales {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    FiniteGibbsClock.gibbs (thermalH b) b = FiniteGibbsClock.gibbs (thermalH c) c := by
  rw [gibbs_thermal hb, gibbs_thermal hc]
theorem gap_scales_injective {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (he : energies b 1 = energies c 1) : b = c := by
  change delta/b = delta/c at he
  field_simp at he
  nlinarith [delta_pos]
theorem gap_scales_ne {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (hbc : b ≠ c) :
    energies b 1 ≠ energies c 1 := fun h ↦ hbc (gap_scales_injective hb hc h)
theorem gibbs_zero_inverse_scale (H : MatQ) :
    FiniteGibbsClock.gibbs H 0 = (1/3 : ℝ) • (1 : MatQ) := by
  norm_num [FiniteGibbsClock.gibbs, FiniteGibbsClock.partition, FiniteGibbsClock.boltzmann]
theorem gibbs_zero_ne_reference (H : MatQ) :
    FiniteGibbsClock.gibbs H 0 ≠ equilibrium := by
  rw [gibbs_zero_inverse_scale]
  intro he
  have h0 := congrArg (fun A : MatQ ↦ A 0 0) he
  norm_num [equilibrium, density, three, GibbsReset.threeWeights, Complex.real_smul] at h0

/-- No block dephasing is added; its rate is literally zero. -/
def zeroFeature : Unit → Q → ℝ := fun _ _ ↦ 0
def phase (b ℏ t : ℝ) (X : MatQ) : MatQ :=
  GibbsHamiltonianRelaxation.rotation (frequencies b ℏ) (-t) X
def U (b ℏ t : ℝ) : MatQ := GibbsHamiltonianRelaxation.unitary (frequencies b ℏ) t
def channelKraus (b ℏ γ t : ℝ) :=
  GibbsHamiltonianRelaxation.timeKraus (frequencies b ℏ) zeroFeature three.w γ 0 t
def jumps (γ : ℝ) := GibbsBlockRelaxation.jumps zeroFeature three.w γ 0
def reset (γ t : ℝ) (X : MatQ) : MatQ :=
  krausMap (GibbsReset.timeKraus three.w (Real.exp (-γ*t))) X
theorem phase_entry (b ℏ t : ℝ) (X : MatQ) (i j : Q) :
    phase b ℏ t X i j =
      Complex.exp (-Complex.I * t * ((frequencies b ℏ i : ℂ)-frequencies b ℏ j)) *
        X i j := by
  rw [phase, GibbsHamiltonianRelaxation.rotation_entry]
  congr 2
  push_cast
  ring
theorem phase_sandwich (b ℏ t : ℝ) (X : MatQ) :
    phase b ℏ t X = U b ℏ t * X * (U b ℏ t)ᴴ :=
  GibbsHamiltonianRelaxation.rotation_sandwich _ _ _
theorem phase_trace (b ℏ t : ℝ) (X : MatQ) : (phase b ℏ t X).trace = X.trace :=
  GibbsHamiltonianRelaxation.rotation_trace _ _ _
theorem phase_diagonal (b ℏ t : ℝ) (D : Q → ℂ) :
    phase b ℏ t (Matrix.diagonal D) = Matrix.diagonal D :=
  GibbsHamiltonianRelaxation.rotation_diagonal _ _ _
theorem phase_add (b ℏ t : ℝ) (X Y : MatQ) :
    phase b ℏ t (X+Y) = phase b ℏ t X + phase b ℏ t Y :=
  GibbsHamiltonianRelaxation.rotation_add _ _ _ _
theorem phase_smul (b ℏ t : ℝ) (z : ℂ) (X : MatQ) :
    phase b ℏ t (z • X) = z • phase b ℏ t X :=
  GibbsHamiltonianRelaxation.rotation_smul _ _ _ _
theorem phase_zero (b ℏ : ℝ) (X : MatQ) : phase b ℏ 0 X = X := by
  ext i j
  simp [phase_entry]
theorem phase_inverse (b ℏ t : ℝ) (X : MatQ) :
    phase b ℏ (-t) (phase b ℏ t X) = X := by
  ext i j
  simp only [phase_entry, ← mul_assoc, ← Complex.exp_add, Complex.ofReal_neg]
  rw [show -Complex.I * -((t:ℂ)) *
      ((frequencies b ℏ i:ℂ)-frequencies b ℏ j) +
      -Complex.I * t * ((frequencies b ℏ i:ℂ)-frequencies b ℏ j) = 0 by ring]
  simp
theorem channel_normalized (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    IsKrausChannel (channelKraus b ℏ γ t) :=
  GibbsHamiltonianRelaxation.time_normalized _ _ _ (fun i ↦ (three.positive i).le)
    three.normalized _ _ _ hγ le_rfl ht
theorem channel_density (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {X : MatQ} (hX : IsDensityOperator X) :
    IsDensityOperator (krausMap (channelKraus b ℏ γ t) X) :=
  krausMap_isDensityOperator (channel_normalized b ℏ γ t hγ ht) hX
theorem channel_propagator (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (X : MatQ) :
    krausMap (channelKraus b ℏ γ t) X =
      lindbladPropagatorAction (scaledH b ℏ) (jumps γ) t X :=
  GibbsHamiltonianRelaxation.time_state_eq_propagator _ _ _
    (fun i ↦ (three.positive i).le) three.normalized _ _ _ hγ le_rfl ht X
theorem channel_stationary (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    krausMap (channelKraus b ℏ γ t) equilibrium = equilibrium :=
  GibbsHamiltonianRelaxation.time_stationary _ _ _ (fun i ↦ (three.positive i).le)
    three.normalized _ _ _ hγ le_rfl ht
theorem channel_gibbs_stationary {b : ℝ} (hb : 0 < b)
    (ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    krausMap (channelKraus b ℏ γ t) (FiniteGibbsClock.gibbs (thermalH b) b) =
      FiniteGibbsClock.gibbs (thermalH b) b := by
  rw [gibbs_thermal hb]
  exact channel_stationary b ℏ γ t hγ ht
theorem channel_observable (b ℏ γ t : ℝ) (X : MatQ) :
    Channel.heisenberg (channelKraus b ℏ γ t) X =
      Channel.heisenberg (GibbsBlockRelaxation.timeKraus zeroFeature three.w γ 0 t)
        (phase b ℏ (-t) X) := by
  simpa [channelKraus, phase] using
    GibbsHamiltonianRelaxation.time_observable (frequencies b ℏ) zeroFeature three.w γ 0 t X
theorem channel_duality (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (S X : MatQ) :
    (S * Channel.heisenberg (channelKraus b ℏ γ t) X).trace =
      (lindbladPropagatorAction (scaledH b ℏ) (jumps γ) t S * X).trace :=
  GibbsHamiltonianRelaxation.trace_duality _ _ _ (fun i ↦ (three.positive i).le)
    three.normalized _ _ _ hγ le_rfl ht S X
theorem reset_action (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (X : MatQ) :
    reset γ t X = (Real.exp (-γ*t):ℂ) • X +
      ((1-Real.exp (-γ*t):ℝ):ℂ) • (X.trace • equilibrium) := by
  simpa only [reset, equilibrium, Complex.ofReal_sub, Complex.ofReal_one] using
    GibbsReset.time_state _ (fun i ↦ (three.positive i).le) _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one γ t hγ ht) X
theorem channel_action (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (X : MatQ) :
    krausMap (channelKraus b ℏ γ t) X = phase b ℏ t (reset γ t X) := by
  rw [channelKraus, GibbsHamiltonianRelaxation.time_state,
    GibbsBlockRelaxation.time_state_eq_propagator _ _ (fun i ↦ (three.positive i).le)
      three.normalized γ 0 t hγ le_rfl ht,
    GibbsBlockRelaxation.propagator_state _ _ (fun i ↦ (three.positive i).le)
      three.normalized γ 0 t hγ le_rfl, reset_action γ t hγ ht]
  simp only [add_zero]
  congr 1
  change X.trace • equilibrium + _ • (_ - X.trace • equilibrium) +
    _ • (X - _) = _
  push_cast
  module

theorem scaledH_smul (b ℏ : ℝ) : scaledH b ℏ = (ℏ⁻¹:ℝ) • thermalH b := by
  ext i j
  by_cases h : i=j <;> simp [scaledH, thermalH, density, frequencies, h,
    Complex.real_smul, div_eq_mul_inv, mul_comm]
theorem actual_generator (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (X : MatQ) :
    lindbladGenerator (scaledH b ℏ) (jumps γ) X =
      -Complex.I • (scaledH b ℏ * X-X*scaledH b ℏ) +
        (γ:ℂ) • (X.trace • equilibrium-X) := by
  simpa [scaledH, jumps, equilibrium, GibbsHamiltonianRelaxation.ham,
    lindbladHamPart_apply] using
    GibbsHamiltonianRelaxation.generator_state (frequencies b ℏ) zeroFeature three.w
      (fun i ↦ (three.positive i).le) three.normalized γ 0 hγ le_rfl X
theorem phase_single (b ℏ t : ℝ) (i j : Q) :
    phase b ℏ t (Matrix.single i j 1) =
      Complex.exp (-Complex.I*t*((frequencies b ℏ i:ℂ)-frequencies b ℏ j)) •
        Matrix.single i j 1 := by
  simpa [phase, neg_mul, Complex.ofReal_neg, mul_neg] using
    GibbsHamiltonianRelaxation.rotation_single (frequencies b ℏ) (-t) i j
theorem phase_E02 (b ℏ t : ℝ) :
    phase b ℏ t (Matrix.single 0 2 1) =
      Complex.exp (Complex.I*t*(Real.log 3/b/ℏ:ℝ)) • (Matrix.single 0 2 1 : MatQ) := by
  rw [phase_single]
  simp [frequencies, energies]
theorem phase_E12 (b ℏ t : ℝ) :
    phase b ℏ t (Matrix.single 1 2 1) =
      Complex.exp (-Complex.I*t*((delta/b/ℏ:ℝ)-(Real.log 3/b/ℏ:ℝ))) •
        (Matrix.single 1 2 1 : MatQ) := by
  rw [phase_single]
  rfl
theorem channel_zero_time (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (X : MatQ) :
    krausMap (channelKraus b ℏ γ 0) X = X := by
  rw [channel_action b ℏ γ 0 hγ le_rfl, reset_action γ 0 hγ le_rfl]
  simpa using phase_zero b ℏ X
theorem channel_zero_rate (b ℏ t : ℝ) (ht : 0 ≤ t) (X : MatQ) :
    krausMap (channelKraus b ℏ 0 t) X = phase b ℏ t X := by
  rw [channel_action b ℏ 0 t le_rfl ht, reset_action 0 t le_rfl ht]
  simp

/-- Any real diagonal Hamiltonian phase is erased by the actual computational branch. -/
theorem computational_phase {d : ℕ} (E : Fin d → ℝ) (t : ℝ)
    (a : Fin d) (X : Matrix (Fin d) (Fin d) ℂ) :
    (instrument d).branch a (GibbsHamiltonianRelaxation.rotation E t X) =
      (instrument d).branch a X := by
  simp [instrument_branch, GibbsHamiltonianRelaxation.rotation_entry]
theorem first_phase {d : ℕ} (R : Data d) (E : Fin d → ℝ) (t : ℝ)
    (a : Fin d) (X : Matrix (Fin d) (Fin d) ℂ) :
    (step R.w R.positive R.normalized R.γ 0 R.rate_nonneg le_rfl).branch
      (Fin d) Unit d a (joint (GibbsHamiltonianRelaxation.rotation E t X)) =
    (step R.w R.positive R.normalized R.γ 0 R.rate_nonneg le_rfl).branch
      (Fin d) Unit d a (joint X) := by
  rw [step_branch, step_branch]
  simp only [mul_zero, Real.exp_zero]
  rw [GibbsReset.time_state _ (fun i ↦ (R.positive i).le) 1 zero_le_one le_rfl,
    GibbsReset.time_state _ (fun i ↦ (R.positive i).le) 1 zero_le_one le_rfl]
  simp only [Complex.ofReal_one, one_smul, sub_self, zero_smul, add_zero]
  rw [computational_phase]
theorem old_history_phase {d : ℕ} (R : Data d) (E : Fin d → ℝ) (t : ℝ)
    (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) (h : History d (n+1))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    run (Fin d) Unit d (historyTree R n s hs) h
      (joint (GibbsHamiltonianRelaxation.rotation E t X)) =
    run (Fin d) Unit d (historyTree R n s hs) h (joint X) := by
  change run _ _ _ _ h.2 (_ : Matrix (Fin d × Unit) (Fin d × Unit) ℂ) = _
  rw [first_phase]
  cases h
  rfl
theorem old_history_phase_weight {d : ℕ} (R : Data d) (E : Fin d → ℝ) (t : ℝ)
    (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) (h : History d (n+1))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    weight (Fin d) Unit d (historyTree R n s hs) h
      (joint (GibbsHamiltonianRelaxation.rotation E t X)) =
    weight (Fin d) Unit d (historyTree R n s hs) h (joint X) := by
  unfold weight
  rw [old_history_phase]

def combinedStep (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) : Step Q Unit 3 where
  count := _
  evolution k := joint (channelKraus b ℏ γ t k)
  normalized := joint_normalized _ (channel_normalized b ℏ γ t hγ ht)
  instrument := instrument 3
theorem combinedStep_branch (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (a : Q) (X : MatQ) :
    (combinedStep b ℏ γ t hγ ht).branch Q Unit 3 a (joint X) =
      joint ((instrument 3).branch a (krausMap (channelKraus b ℏ γ t) X)) := by
  change ((instrument 3).lift Unit).branch a
    (krausMap (fun k ↦ joint (channelKraus b ℏ γ t k)) (joint X)) = _
  rw [joint_kraus]
  exact joint_kraus _ _
theorem combinedStep_actual (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (X : MatQ) :
    krausMap (combinedStep b ℏ γ t hγ ht).evolution (joint X) =
      joint (lindbladPropagatorAction (scaledH b ℏ) (jumps γ) t X) := by
  change krausMap (fun k ↦ joint (channelKraus b ℏ γ t k)) (joint X) = _
  rw [joint_kraus, channel_propagator b ℏ γ t hγ ht]
theorem combinedStep_eq_reset (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (a : Q) (X : MatQ) :
    (combinedStep b ℏ γ t hγ ht).branch Q Unit 3 a (joint X) =
      (step three.w three.positive three.normalized γ t hγ ht).branch Q Unit 3 a
        (joint X) := by
  rw [combinedStep_branch, step_branch, channel_action b ℏ γ t hγ ht]
  change joint ((instrument 3).branch a
    (GibbsHamiltonianRelaxation.rotation _ _ (reset γ t X))) = _
  rw [computational_phase]
  rfl
def combinedTail (b ℏ γ : ℝ) (hγ : 0 ≤ γ) :
    (n : ℕ) → (s : ℕ → ℝ) → (∀ i, 0 ≤ s i) → Tree Q Unit 3 n
  | 0, _, _ => .done
  | n+1, s, hs => .node (combinedStep b ℏ γ (s 0) hγ (hs 0))
      (fun _ ↦ combinedTail b ℏ γ hγ n (later s) (fun i ↦ hs (i+1)))
def combinedHistory (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ)
    (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) : Tree Q Unit 3 (n+1) :=
  .node (combinedStep b ℏ γ 0 hγ le_rfl) (fun _ ↦ combinedTail b ℏ γ hγ n s hs)
theorem combinedTail_eq_reset (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ)
    (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) (h : History 3 n) (X : MatQ) :
    run Q Unit 3 (combinedTail b ℏ γ hγ n s hs) h (joint X) =
      run Q Unit 3 (tailTree (threeRate γ hγ) n s hs) h (joint X) := by
  induction n generalizing s X with
  | zero => rfl
  | succ n ih =>
    change run Q Unit 3 (combinedTail b ℏ γ hγ n (later s) _) h.2
      ((combinedStep b ℏ γ (s 0) hγ (hs 0)).branch Q Unit 3 h.1 (joint X)) = _
    rw [combinedStep_eq_reset, step_branch, ih]
    cases h
    simp only [tailTree, run, step_branch, threeRate]
theorem combinedHistory_eq_reset (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ)
    (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) (h : History 3 (n+1)) (X : MatQ) :
    run Q Unit 3 (combinedHistory b ℏ γ hγ n s hs) h (joint X) =
      run Q Unit 3 (historyTree (threeRate γ hγ) n s hs) h (joint X) := by
  change run Q Unit 3 (combinedTail b ℏ γ hγ n s hs) h.2
    ((combinedStep b ℏ γ 0 hγ le_rfl).branch Q Unit 3 h.1 (joint X)) = _
  rw [combinedStep_eq_reset, step_branch, combinedTail_eq_reset]
  cases h
  simp only [historyTree, run, step_branch, threeRate]
theorem combinedHistory_weight (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ)
    (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) (h : History 3 (n+1)) (X : MatQ) :
    weight Q Unit 3 (combinedHistory b ℏ γ hγ n s hs) h (joint X) =
      weight Q Unit 3 (historyTree (threeRate γ hγ) n s hs) h (joint X) := by
  unfold weight
  rw [combinedHistory_eq_reset]

/-- A normalized reversible unitary channel, used only on Hermitian distance inputs. -/
def conjugate (V X : MatQ) : MatQ := V*X*Vᴴ
theorem conjugate_action (V X : MatQ) :
    krausMap (unitaryKraus V) X = conjugate V X := by
  simp [krausMap, unitaryKraus, conjugate]
theorem conjugate_density {V : MatQ} (hV : V ∈ Matrix.unitaryGroup Q ℂ)
    {X : MatQ} (hX : IsDensityOperator X) : IsDensityOperator (conjugate V X) := by
  rw [← conjugate_action]
  exact krausMap_isDensityOperator (isKrausChannel_unitaryKraus hV) hX
theorem conjugate_distance {V : MatQ} (hV : V ∈ Matrix.unitaryGroup Q ℂ)
    {X Y : MatQ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    traceDist (conjugate V X) (conjugate V Y) = traceDist X Y := by
  have hVV : V*Vᴴ=1 := Matrix.mem_unitaryGroup_iff.mp hV
  have hVV' : Vᴴ*V=1 := mul_eq_one_comm.mp hVV
  have hv' : Vᴴ ∈ Matrix.unitaryGroup Q ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    change Vᴴ*(Vᴴ)ᴴ=1
    simpa using hVV'
  have inv (Z : MatQ) : conjugate Vᴴ (conjugate V Z) = Z := by
    simp only [conjugate, Matrix.conjTranspose_conjTranspose]
    calc
      Vᴴ * (V*Z*Vᴴ) * V = (Vᴴ*V)*Z*(Vᴴ*V) := by noncomm_ring
      _ = Z := by rw [hVV']; simp
  have h1 := traceDist_krausMap_le (isKrausChannel_unitaryKraus hV) hX hY
  simp only [conjugate_action] at h1
  have hx' : (conjugate V X).IsHermitian := by
    rw [← conjugate_action]; exact krausMap_isHermitian _ hX
  have hy' : (conjugate V Y).IsHermitian := by
    rw [← conjugate_action]; exact krausMap_isHermitian _ hY
  have h2 := traceDist_krausMap_le (isKrausChannel_unitaryKraus hv') hx' hy'
  simp only [conjugate_action, inv] at h2
  exact le_antisymm h1 h2
theorem U_unitary (b ℏ t : ℝ) : U b ℏ t ∈ Matrix.unitaryGroup Q ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change GibbsHamiltonianRelaxation.unitary _ _ *
    (GibbsHamiltonianRelaxation.unitary _ _)ᴴ = _
  rw [GibbsHamiltonianRelaxation.unitary_adjoint,
    GibbsHamiltonianRelaxation.unitary_cancel]
theorem phase_density (b ℏ t : ℝ) {X : MatQ} (hX : IsDensityOperator X) :
    IsDensityOperator (phase b ℏ t X) := by
  rw [phase_sandwich]
  exact conjugate_density (U_unitary b ℏ t) hX
theorem phase_distance (b ℏ t : ℝ) {X Y : MatQ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    traceDist (phase b ℏ t X) (phase b ℏ t Y) = traceDist X Y := by
  simp only [phase_sandwich]
  exact conjugate_distance (U_unitary b ℏ t) hX hY

def s : ℂ := (Real.sqrt 2 : ℂ)/2
def hadamard : MatQ := !![s,s,0; s,-s,0; 0,0,1]
theorem s_real : star s = s := by simp [s]
theorem s_conj : (starRingEnd ℂ) s = s := s_real
theorem s_square : s*s = 1/2 := by
  have h : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 2:ℂ)^2 = 2 := by exact_mod_cast h
  dsimp [s]
  calc
    (Real.sqrt 2:ℂ)/2*((Real.sqrt 2:ℂ)/2) = (Real.sqrt 2:ℂ)^2/4 := by ring
    _ = 1/2 := by rw [hc]; norm_num
theorem hadamard_adjoint : hadamardᴴ = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadamard, Matrix.conjTranspose_apply, s_real]
theorem hadamard_square : hadamard*hadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_succ, s_square] <;> ring
theorem hadamard_unitary : hadamard ∈ Matrix.unitaryGroup Q ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change hadamard*hadamardᴴ=1
  rw [hadamard_adjoint, hadamard_square]
theorem conjugate_projector_entry (V : MatQ) (a i j : Q) :
    conjugate V (projector a) i j = V i a * star (V j a) := by
  simp [conjugate, projector, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply]
/-- These are actual rank-one projectors of the normalized plus/minus vectors. -/
def Pplus : MatQ := conjugate hadamard (projector 0)
def Pminus : MatQ := conjugate hadamard (projector 1)
def vplus : Q → ℂ := ![s,s,0]
def vminus : Q → ℂ := ![s,-s,0]
theorem Pplus_entries : Pplus = !![1/2,1/2,0; 1/2,1/2,0; 0,0,0] := by
  ext i j
  rw [Pplus, conjugate_projector_entry]
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard, s_conj, s_square]
theorem Pminus_entries : Pminus = !![1/2,-1/2,0; -1/2,1/2,0; 0,0,0] := by
  ext i j
  rw [Pminus, conjugate_projector_entry]
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard, s_conj, s_square]
theorem Pplus_rank_one : Pplus = Matrix.vecMulVec vplus (star vplus) := by
  rw [Pplus_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vplus, Matrix.vecMulVec, s_conj, s_square]
theorem Pminus_rank_one : Pminus = Matrix.vecMulVec vminus (star vminus) := by
  rw [Pminus_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [vminus, Matrix.vecMulVec, s_conj, s_square]
theorem Pplus_density : IsDensityOperator Pplus :=
  conjugate_density hadamard_unitary (FiniteAdaptiveGibbsReadout.projector_density 0)
theorem Pminus_density : IsDensityOperator Pminus :=
  conjugate_density hadamard_unitary (FiniteAdaptiveGibbsReadout.projector_density 1)
theorem Pplus_square : Pplus*Pplus = Pplus := by
  rw [Pplus_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
theorem Pminus_square : Pminus*Pminus = Pminus := by
  rw [Pminus_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
theorem projector_distance : traceDist Pplus Pminus = 1 := by
  rw [Pplus, Pminus, conjugate_distance hadamard_unitary
    (FiniteAdaptiveGibbsReadout.projector_density 0).1.isHermitian
    (FiniteAdaptiveGibbsReadout.projector_density 1).1.isHermitian]
  exact FiniteAdaptiveGibbsReadout.projector_pair_distance

def mixture (r : ℝ) (P : MatQ) : MatQ := ((1-r:ℝ):ℂ) • equilibrium + (r:ℂ) • P
def sigmaA (r : ℝ) : MatQ := mixture r Pplus
def sigmaB (r : ℝ) : MatQ := mixture r Pminus
theorem mixture_density {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {P : MatQ} (hP : IsDensityOperator P) : IsDensityOperator (mixture r P) := by
  refine ⟨(equilibrium_density.1.smul (by exact_mod_cast sub_nonneg.mpr hr1)).add
    (hP.1.smul (by exact_mod_cast hr)), ?_⟩
  simp [mixture, Matrix.trace_add, Matrix.trace_smul, equilibrium_density.2, hP.2]
theorem mixture_faithful {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {P : MatQ} (hP : P.PosSemidef) : (mixture r P).PosDef :=
  (equilibrium_posDef.smul (by exact_mod_cast sub_pos.mpr hr1)).add_posSemidef
    (hP.smul (by exact_mod_cast hr))
theorem sigmaA_density {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsDensityOperator (sigmaA r) := mixture_density hr hr1 Pplus_density
theorem sigmaB_density {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsDensityOperator (sigmaB r) := mixture_density hr hr1 Pminus_density
theorem sigmaA_faithful {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (sigmaA r).PosDef := mixture_faithful hr.le hr1 Pplus_density.1
theorem sigmaB_faithful {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (sigmaB r).PosDef := mixture_faithful hr.le hr1 Pminus_density.1
theorem mixture_difference (r : ℝ) (P R : MatQ) :
    mixture r P-mixture r R = (r:ℂ) • (P-R) := by
  unfold mixture
  module
theorem mixture_distance {r : ℝ} (hr : 0 ≤ r) (P R : MatQ) :
    traceDist (mixture r P) (mixture r R) = r*traceDist P R := by
  rw [traceDist, mixture_difference, traceNorm_smul_nonneg hr, traceDist]
  ring
theorem preparation_distance {r : ℝ} (hr : 0 ≤ r) :
    traceDist (sigmaA r) (sigmaB r) = r := by
  rw [sigmaA, sigmaB, mixture_distance hr, projector_distance, mul_one]
theorem preparation_joint_distance {r : ℝ} (hr : 0 ≤ r) :
    traceDist (joint (sigmaA r)) (joint (sigmaB r)) = r := by
  rw [GibbsHistoryPreparationBounds.joint_traceDist, preparation_distance hr]
def retention (r γ t : ℝ) : ℝ := r*Real.exp (-γ*t)
theorem retention_nonneg {r : ℝ} (hr : 0 ≤ r) (γ t : ℝ) : 0 ≤ retention r γ t :=
  mul_nonneg hr (Real.exp_pos _).le
theorem retention_le_one {r γ t : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hγ : 0 ≤ γ) (ht : 0 ≤ t) : retention r γ t ≤ 1 :=
  (mul_le_mul_of_nonneg_left (GibbsReset.exp_rate_le_one γ t hγ ht) hr).trans
    (by simpa using hr1)
theorem retention_lt_one {r γ t : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hγ : 0 ≤ γ) (ht : 0 ≤ t) : retention r γ t < 1 :=
  (mul_le_mul_of_nonneg_left (GibbsReset.exp_rate_le_one γ t hγ ht) hr).trans_lt
    (by simpa using hr1)
theorem evolved_mixture (b ℏ γ t r : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {P : MatQ} (hP : IsDensityOperator P) :
    krausMap (channelKraus b ℏ γ t) (mixture r P) =
      mixture (retention r γ t) (phase b ℏ t P) := by
  rw [channel_action b ℏ γ t hγ ht, reset_action γ t hγ ht]
  have htr : (mixture r P).trace=1 := by
    simp [mixture, Matrix.trace_add, Matrix.trace_smul, equilibrium_density.2, hP.2]
  rw [htr, one_smul, mixture, phase_add, phase_smul, phase_add, phase_smul, phase_smul]
  have hp : phase b ℏ t equilibrium=equilibrium := phase_diagonal b ℏ t _
  simp only [phase_smul, hp]
  unfold mixture retention
  push_cast
  module
theorem evolved_distance (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) :
    traceDist (krausMap (channelKraus b ℏ γ t) (sigmaA r))
      (krausMap (channelKraus b ℏ γ t) (sigmaB r)) = retention r γ t := by
  rw [sigmaA, sigmaB, evolved_mixture b ℏ γ t r hγ ht Pplus_density,
    evolved_mixture b ℏ γ t r hγ ht Pminus_density,
    mixture_distance (retention_nonneg hr γ t),
    phase_distance b ℏ t Pplus_density.1.isHermitian Pminus_density.1.isHermitian,
    projector_distance, mul_one]
theorem evolved_joint_distance (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) :
    traceDist (joint (krausMap (channelKraus b ℏ γ t) (sigmaA r)))
      (joint (krausMap (channelKraus b ℏ γ t) (sigmaB r))) = retention r γ t := by
  rw [GibbsHistoryPreparationBounds.joint_traceDist, evolved_distance b ℏ γ t hγ ht hr]

theorem phase_physical (b ℏ t : ℝ) (_hℏ : 0 < ℏ) (X : MatQ) :
    phase b ℏ t X = FiniteGibbsClock.heisenberg (thermalH b) ℏ (-t) X := by
  ext i j
  rw [phase_entry]
  simp only [FiniteGibbsClock.heisenberg, thermalH, density,
    FiniteGibbsClock.diagonal_conjugate_entry]
  congr 2
  simp only [frequencies, Complex.ofReal_div, Complex.ofReal_neg]
  ring
theorem observable_phase_entry (b ℏ t : ℝ) (X : MatQ) (i j : Q) :
    phase b ℏ (-t) X i j =
      Complex.exp (Complex.I*t*((frequencies b ℏ i:ℂ)-frequencies b ℏ j))*X i j := by
  rw [phase_entry]
  congr 2
  push_cast
  ring
def theta (b ℏ t : ℝ) : ℝ := t*delta/(b*ℏ)
theorem phase_E01 (b ℏ t : ℝ) :
    phase b ℏ t (Matrix.single 0 1 1) =
      Complex.exp (Complex.I*(theta b ℏ t:ℝ)) • (Matrix.single 0 1 1 : MatQ) := by
  rw [phase_single]
  congr 2
  simp only [frequencies, energies, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_div, Complex.ofReal_zero, zero_sub, mul_neg, neg_mul, neg_neg,
    theta, Complex.ofReal_div, Complex.ofReal_mul]
  ring
theorem phase_projector_diagonal (b ℏ t : ℝ) (P : MatQ) (i : Q) :
    phase b ℏ t P i i = P i i := by simp [phase_entry]
theorem evolvedA_density (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsDensityOperator (krausMap (channelKraus b ℏ γ t) (sigmaA r)) :=
  channel_density b ℏ γ t hγ ht (sigmaA_density hr hr1)
theorem evolvedB_density (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsDensityOperator (krausMap (channelKraus b ℏ γ t) (sigmaB r)) :=
  channel_density b ℏ γ t hγ ht (sigmaB_density hr hr1)
theorem evolvedA_faithful (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (krausMap (channelKraus b ℏ γ t) (sigmaA r)).PosDef := by
  rw [sigmaA, evolved_mixture b ℏ γ t r hγ ht Pplus_density]
  exact mixture_faithful (retention_nonneg hr.le γ t) (retention_lt_one hr.le hr1 hγ ht)
    (phase_density b ℏ t Pplus_density).1
theorem evolvedB_faithful (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (krausMap (channelKraus b ℏ γ t) (sigmaB r)).PosDef := by
  rw [sigmaB, evolved_mixture b ℏ γ t r hγ ht Pminus_density]
  exact mixture_faithful (retention_nonneg hr.le γ t) (retention_lt_one hr.le hr1 hγ ht)
    (phase_density b ℏ t Pminus_density).1
theorem preparation_third (r : ℝ) :
    sigmaA r 2 2 = ((1-r)/6:ℝ) ∧ sigmaB r 2 2 = ((1-r)/6:ℝ) := by
  simp [sigmaA, sigmaB, mixture, Pplus_entries, Pminus_entries, equilibrium, density,
    three, GibbsReset.threeWeights]
  constructor
theorem evolved_third (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (r : ℝ) :
    krausMap (channelKraus b ℏ γ t) (sigmaA r) 2 2 = ((1-retention r γ t)/6:ℝ) ∧
    krausMap (channelKraus b ℏ γ t) (sigmaB r) 2 2 = ((1-retention r γ t)/6:ℝ) := by
  rw [sigmaA, sigmaB, evolved_mixture b ℏ γ t r hγ ht Pplus_density,
    evolved_mixture b ℏ γ t r hγ ht Pminus_density]
  simp [mixture, phase_projector_diagonal, Pplus_entries, Pminus_entries, equilibrium,
    density, three, GibbsReset.threeWeights]
  constructor
theorem preparation_third_pos {r : ℝ} (hr1 : r < 1) :
    0 < (sigmaA r 2 2).re ∧ 0 < (sigmaB r 2 2).re := by
  rw [(preparation_third r).1, (preparation_third r).2]
  simp only [Complex.ofReal_re]
  exact ⟨div_pos (sub_pos.mpr hr1) (by norm_num), div_pos (sub_pos.mpr hr1) (by norm_num)⟩
theorem evolved_third_pos (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    0 < (krausMap (channelKraus b ℏ γ t) (sigmaA r) 2 2).re ∧
    0 < (krausMap (channelKraus b ℏ γ t) (sigmaB r) 2 2).re := by
  rw [(evolved_third b ℏ γ t hγ ht r).1, (evolved_third b ℏ γ t hγ ht r).2]
  simp only [Complex.ofReal_re]
  have hq := retention_lt_one hr hr1 hγ ht
  exact ⟨div_pos (sub_pos.mpr hq) (by norm_num), div_pos (sub_pos.mpr hq) (by norm_num)⟩
theorem preparation_zero : sigmaA 0 = equilibrium ∧ sigmaB 0 = equilibrium := by
  simp [sigmaA, sigmaB, mixture]
theorem preparation_one : sigmaA 1 = Pplus ∧ sigmaB 1 = Pminus := by
  simp [sigmaA, sigmaB, mixture]
theorem retention_controls (r γ t : ℝ) :
    retention 0 γ t = 0 ∧ retention r γ 0 = r ∧ retention r 0 t = r := by
  simp [retention]
theorem joint_density {X : MatQ} (hX : IsDensityOperator X) :
    IsDensityOperator (joint X) := by
  refine ⟨hX.1.kronecker Matrix.PosSemidef.one, ?_⟩
  rw [joint_trace, hX.2]
theorem joint_faithful {X : MatQ} (hX : X.PosDef) : (joint X).PosDef :=
  hX.kronecker Matrix.PosDef.one
def unjoint (X : MatJoint) : MatQ := fun i j ↦ X (i,()) (j,())
theorem joint_unjoint (X : MatJoint) : joint (unjoint X) = X := by
  ext ⟨i,u⟩ ⟨j,v⟩
  cases u
  cases v
  simp [joint, unjoint, Matrix.kroneckerMap_apply]
theorem combinedHistory_all_joint (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ)
    (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) (h : History 3 (n+1)) (X : MatJoint) :
    run Q Unit 3 (combinedHistory b ℏ γ hγ n s hs) h X =
      run Q Unit 3 (historyTree (threeRate γ hγ) n s hs) h X := by
  rw [← joint_unjoint X]
  exact combinedHistory_eq_reset b ℏ γ hγ n s hs h _
theorem combinedHistory_probabilities (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ)
    (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) {X : MatJoint} (hX : IsDensityOperator X) :
    (∀ h, 0 ≤ weight Q Unit 3 (combinedHistory b ℏ γ hγ n s hs) h X) ∧
      (∑ h, weight Q Unit 3 (combinedHistory b ℏ γ hγ n s hs) h X) = 1 :=
  normalized_weights Q Unit 3 _ hX

theorem old_history_eq_of_diagonal {d : ℕ} (R : Data d) (n : ℕ)
    (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) (h : History d (n+1))
    (X Y : Matrix (Fin d) (Fin d) ℂ) (hXY : ∀ i, X i i=Y i i) :
    run (Fin d) Unit d (historyTree R n s hs) h (joint X) =
      run (Fin d) Unit d (historyTree R n s hs) h (joint Y) := by
  cases h with
  | mk a h =>
    simp only [historyTree, run, step_branch, mul_zero, Real.exp_zero]
    rw [GibbsReset.time_state _ (fun i ↦ (R.positive i).le) 1 zero_le_one le_rfl,
      GibbsReset.time_state _ (fun i ↦ (R.positive i).le) 1 zero_le_one le_rfl]
    simp only [Complex.ofReal_one, one_smul, sub_self, zero_smul, add_zero, instrument_branch]
    rw [hXY]
theorem evolved_pair_diagonal (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (r : ℝ) (i : Q) :
    krausMap (channelKraus b ℏ γ t) (sigmaA r) i i =
      krausMap (channelKraus b ℏ γ t) (sigmaB r) i i := by
  rw [sigmaA, sigmaB, evolved_mixture b ℏ γ t r hγ ht Pplus_density,
    evolved_mixture b ℏ γ t r hγ ht Pminus_density]
  simp only [mixture, Matrix.add_apply, Matrix.smul_apply, phase_projector_diagonal]
  rw [Pplus_entries, Pminus_entries]
  fin_cases i <;> rfl
theorem old_history_evolved_pair (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (r : ℝ) (R : Data 3) (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (h : History 3 (n+1)) :
    run Q Unit 3 (historyTree R n s hs) h
      (joint (krausMap (channelKraus b ℏ γ t) (sigmaA r))) =
    run Q Unit 3 (historyTree R n s hs) h
      (joint (krausMap (channelKraus b ℏ γ t) (sigmaB r))) :=
  old_history_eq_of_diagonal R n s hs h _ _ (evolved_pair_diagonal b ℏ γ t hγ ht r)

theorem reset_eq_warm (γ t : ℝ) (X : MatQ) :
    reset γ t X = GibbsHistoryPreparationBounds.warm three γ t X := rfl
theorem reset_gibbs_stationary {b : ℝ} (hb : 0 < b)
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    reset γ t (FiniteGibbsClock.gibbs (thermalH b) b) =
      FiniteGibbsClock.gibbs (thermalH b) b := by
  rw [gibbs_thermal hb]
  exact GibbsReset.time_stationary three.w (fun i ↦ (three.positive i).le)
    three.normalized _ (Real.exp_pos _).le (GibbsReset.exp_rate_le_one γ t hγ ht)
theorem U_diagonal (b ℏ t : ℝ) :
    U b ℏ t = Matrix.diagonal (fun i ↦ Complex.exp (-Complex.I*t*(frequencies b ℏ i:ℂ))) := by
  simp only [U, GibbsHamiltonianRelaxation.unitary, FiniteGibbsClock.expCoeff,
    density, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
theorem evolvedA_entries (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (r : ℝ) :
    krausMap (channelKraus b ℏ γ t) (sigmaA r) =
      ((1-retention r γ t:ℝ):ℂ) • equilibrium +
        (retention r γ t:ℂ) • (U b ℏ t*Pplus*(U b ℏ t)ᴴ) := by
  rw [sigmaA, evolved_mixture b ℏ γ t r hγ ht Pplus_density, mixture, phase_sandwich]
theorem evolvedB_entries (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (r : ℝ) :
    krausMap (channelKraus b ℏ γ t) (sigmaB r) =
      ((1-retention r γ t:ℝ):ℂ) • equilibrium +
        (retention r γ t:ℂ) • (U b ℏ t*Pminus*(U b ℏ t)ᴴ) := by
  rw [sigmaB, evolved_mixture b ℏ γ t r hγ ht Pminus_density, mixture, phase_sandwich]
theorem old_three_history_phase (b ℏ t : ℝ) (R : Data 3) (n : ℕ)
    (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) (h : History 3 (n+1)) (X : MatQ) :
    run Q Unit 3 (historyTree R n s hs) h (joint (phase b ℏ t X)) =
      run Q Unit 3 (historyTree R n s hs) h (joint X) :=
  old_history_phase R (frequencies b ℏ) (-t) n s hs h X

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelThermalPhase
