import SKEFTHawking.QuantumNetwork.FiniteGibbsClock
import SKEFTHawking.QuantumNetwork.FiniteNontracialMemoryScheduleControls
import SKEFTHawking.FiniteNontracialOperationalCompatibility
import SKEFTHawking.FiniteGibbsHamiltonianRelaxation
import SKEFTHawking.LindbladCPSemigroup
import SKEFTHawking.QuantumNetwork.UnitaryDiamond
/-!
# Finite nontracial thermal phase: actual Gibbs reference and chronological channels

The Hamiltonian is independently defined by the positive inverse scale b.
Its Gibbs state is the existing faithful rhoN. The physical comparison requires
positive hbar; zero inverse scale is a separate finite-H maximally mixed guard.
Forward states use C(theta), while observables use C(-theta).

The normalized singleton phase is composed after the existing dissipative family.
The full complex action is proved equal to the actual nonzero-H vectorized GKSL
propagator using commuting linear maps, their standard-basis matrices, and
left/right matrix exponentials. An explicit correspondence also specializes the
existing GibbsHamiltonianRelaxation realization with exactly the same jumps.

Timed families retain literal head-first dependent Kraus composition. Their
phase sums the same durations as the noise; free pulses have a separate
parameter. The joint lift acts only on E in S × E and preserves the S marginal
for every complex joint matrix. Norm statements retain Hermitian/density domains.
Positive elapsed time does not imply nonidentity: periodicity is retained, and
the nontrivial zero-rate witness is a concrete positive half-turn.

This is finite algebra. No physical clock calibration, continuum, measured
energy scale, reflected-kernel positivity, or downstream readout/history result
is asserted here.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteNontracialThermalPhase
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator Kronecker
open SKEFTHawking.OpenSystems
abbrev Q := Fin 2
abbrev MatQ := Matrix Q Q ℂ
theorem ham_left_right (H : MatQ) :
    lindbladHamPart H =
      LinearMap.mulLeft ℂ (-Complex.I • H) + LinearMap.mulRight ℂ (Complex.I • H) := by
  ext X i j
  simp [lindbladHamPart_apply, sub_eq_add_neg, neg_smul]
  ring
theorem ham_exp (H X : MatQ) (t : ℝ) :
    Matrix.toLin (Matrix.stdBasis ℂ Q Q) (Matrix.stdBasis ℂ Q Q)
      (NormedSpace.exp ((t : ℂ) • LinearMap.toMatrix
        (Matrix.stdBasis ℂ Q Q) (Matrix.stdBasis ℂ Q Q) (lindbladHamPart H))) X =
    FiniteGibbsClock.conjugate H (-Complex.I * t) X := by
  let b := Matrix.stdBasis ℂ Q Q
  have hc : Commute (LinearMap.toMatrix b b (LinearMap.mulLeft ℂ (-Complex.I • H)))
      (LinearMap.toMatrix b b (LinearMap.mulRight ℂ (Complex.I • H))) :=
    (LinearMap.commute_mulLeft_right _ _).map (LinearMap.toMatrixAlgEquiv b)
  change Matrix.toLin b b (NormedSpace.exp ((t : ℂ) • LinearMap.toMatrix b b
    (lindbladHamPart H))) X = _
  rw [ham_left_right, map_add, smul_add,
    Matrix.exp_add_of_commute _ _ ((hc.smul_left (t : ℂ)).smul_right (t : ℂ)),
    Matrix.toLin_mul b b b, toLin_exp_toMatrix_mulLeft, toLin_exp_toMatrix_mulRight]
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    FiniteGibbsClock.conjugate, FiniteGibbsClock.expCoeff, smul_smul, mul_assoc]
  rw [show (t : ℂ) * -Complex.I = -Complex.I * t by ring,
    show (t : ℂ) * Complex.I = -(-Complex.I * t) by ring]
theorem generator_split {κ : Type*} [Fintype κ] (H : MatQ) (L : κ → MatQ) :
    lindbladGenerator H L = lindbladHamPart H + lindbladGenerator 0 L := by
  simp [lindbladGenerator, lindbladHamPart, add_assoc]
theorem propagator_factor {κ : Type*} [Fintype κ] (H : MatQ) (L : κ → MatQ)
    (hc : Commute (lindbladHamPart H) (lindbladGenerator 0 L)) (t : ℝ) (X : MatQ) :
    lindbladPropagatorAction H L t X =
      FiniteGibbsClock.conjugate H (-Complex.I * t)
        (lindbladPropagatorAction 0 L t X) := by
  let b := Matrix.stdBasis ℂ Q Q
  have hm : Commute (LinearMap.toMatrix b b (lindbladHamPart H))
      (LinearMap.toMatrix b b (lindbladGenerator 0 L)) :=
    hc.map (LinearMap.toMatrixAlgEquiv b)
  unfold lindbladPropagatorAction lindbladPropagator lindbladLiouvillian
  rw [generator_split, map_add, smul_add,
    Matrix.exp_add_of_commute _ _ ((hm.smul_left (t : ℂ)).smul_right (t : ℂ)),
    Matrix.toLin_mul b b b]
  simp only [LinearMap.comp_apply]
  rw [ham_exp]

open NontracialPauliReflection FinitePositiveKernel GibbsObservable
def delta : ℝ := Real.log (16/9)
def gap (b : ℝ) : ℝ := delta / b
def thermalH (b : ℝ) : MatQ := FiniteGibbsClock.twoLevel (gap b)
def scaledH (b ℏ : ℝ) : MatQ := (ℏ⁻¹ : ℝ) • thermalH b
def frequency (b ℏ : ℝ) : ℝ := gap b / ℏ
def phase (b ℏ t : ℝ) : ℝ := frequency b ℏ * t
theorem delta_pos : 0 < delta := Real.log_pos (by norm_num)
theorem gap_pos {b : ℝ} (hb : 0 < b) : 0 < gap b := div_pos delta_pos hb
theorem thermalH_hermitian (b : ℝ) : (thermalH b).IsHermitian :=
  FiniteGibbsClock.twoLevel_hermitian _
theorem scaledH_twoLevel (b ℏ : ℝ) :
    scaledH b ℏ = FiniteGibbsClock.twoLevel (frequency b ℏ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scaledH, thermalH, frequency, FiniteGibbsClock.twoLevel, Complex.real_smul, div_eq_mul_inv, mul_comm]
def jumps (γ η : ℝ) := GibbsBlockRelaxation.jumps
  NontracialReflectionDynamics.signature weights γ η
theorem noise_generator (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (X : MatQ) :
    lindbladGenerator 0 (jumps γ η) X =
      (γ : ℂ) • (X.trace • rhoN - X) +
      (η : ℂ) • (NontracialReflectionDynamics.diagonalPart X - X) := by
  rw [jumps, GibbsBlockRelaxation.generator_state _ _ weights_nonnegative weights_normalized
    γ η hγ hη, weights_density, NontracialReflectionDynamics.singleton_expectation]
theorem actual_generator (b ℏ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (X : MatQ) :
    lindbladGenerator (scaledH b ℏ) (jumps γ η) X =
      -Complex.I • (scaledH b ℏ * X - X * scaledH b ℏ) +
      (γ : ℂ) • (X.trace • rhoN - X) +
      (η : ℂ) • (NontracialReflectionDynamics.diagonalPart X - X) := by
  rw [generator_split, LinearMap.add_apply, lindbladHamPart_apply, noise_generator γ η hγ hη]
  module
theorem ham_noise_commute (b ℏ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    Commute (lindbladHamPart (scaledH b ℏ)) (lindbladGenerator 0 (jumps γ η)) := by
  apply LinearMap.ext
  intro X
  change lindbladHamPart (scaledH b ℏ) (lindbladGenerator 0 (jumps γ η) X) =
    lindbladGenerator 0 (jumps γ η) (lindbladHamPart (scaledH b ℏ) X)
  rw [noise_generator γ η hγ hη, noise_generator γ η hγ hη]
  simp only [lindbladHamPart_apply, scaledH_twoLevel]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FiniteGibbsClock.twoLevel, NontracialReflectionDynamics.diagonalPart, rhoN,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two] <;> ring <;> simp


/-- The phase unitary is a genuine matrix exponential, with explicit diagonal entries. -/
def V (θ : ℝ) : MatQ := FiniteGibbsClock.expCoeff (FiniteGibbsClock.twoLevel 1) (-Complex.I * θ)
theorem V_diagonal (θ : ℝ) :
    V θ = Matrix.diagonal (![1, Complex.exp (-Complex.I * θ)] : Q → ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [V, FiniteGibbsClock.expCoeff, FiniteGibbsClock.twoLevel,
      ← Matrix.diagonal_smul, Matrix.exp_diagonal, ← Complex.exp_eq_exp_ℂ]
theorem V_adjoint (θ : ℝ) : (V θ)ᴴ = V (-θ) := by
  rw [V, FiniteGibbsClock.expCoeff_adjoint (FiniteGibbsClock.twoLevel_hermitian 1)]
  simp [V]
theorem V_mul_neg (θ : ℝ) : V θ * V (-θ) = 1 := by
  convert FiniteGibbsClock.expCoeff_cancel (FiniteGibbsClock.twoLevel 1) (-Complex.I * θ) using 1 <;>
    simp [V]
theorem V_unitary (θ : ℝ) : V θ ∈ Matrix.unitaryGroup Q ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change V θ * (V θ)ᴴ = 1
  rw [V_adjoint, V_mul_neg]
def phaseKraus (θ : ℝ) := unitaryKraus (V θ)
theorem phase_normalized (θ : ℝ) : IsKrausChannel (phaseKraus θ) :=
  isKrausChannel_unitaryKraus (V_unitary θ)
/-- Forward state conjugation. Its observable dual uses the negative phase. -/
def C (θ : ℝ) (X : MatQ) : MatQ :=
  FiniteGibbsClock.conjugate (FiniteGibbsClock.twoLevel 1) (-Complex.I * θ) X
theorem phase_action (θ : ℝ) (X : MatQ) : krausMap (phaseKraus θ) X = C θ X := by
  simp only [phaseKraus, krausMap, unitaryKraus, Fin.sum_univ_one, V_adjoint]
  simp [C, V, FiniteGibbsClock.conjugate]
theorem phase_observable (θ : ℝ) (A : MatQ) :
    Channel.heisenberg (phaseKraus θ) A = C (-θ) A := by
  simp only [phaseKraus, Channel.heisenberg, unitaryKraus, Fin.sum_univ_one, V_adjoint]
  simp [C, V, FiniteGibbsClock.conjugate]
theorem C_entry (θ : ℝ) (X : MatQ) (i j : Q) :
    C θ X i j =
      Complex.exp ((-Complex.I * θ) *
        ((![0,1] : Q → ℂ) i - (![0,1] : Q → ℂ) j)) * X i j := by
  exact FiniteGibbsClock.diagonal_conjugate_entry _ _ X i j
theorem C_zero (X : MatQ) : C 0 X = X := by
  simp [C, FiniteGibbsClock.conjugate_zero]
theorem C_group (θ φ : ℝ) (X : MatQ) : C (θ + φ) X = C θ (C φ X) := by
  simp only [C, Complex.ofReal_add, mul_add, FiniteGibbsClock.conjugate_group]
theorem C_inverse (θ : ℝ) (X : MatQ) : C (-θ) (C θ X) = X := by
  rw [← C_group]; simpa using C_zero X
theorem C_add (θ : ℝ) (X Y : MatQ) : C θ (X+Y) = C θ X+C θ Y :=
  FiniteGibbsClock.conjugate_add _ _ _ _
theorem C_smul (θ : ℝ) (z : ℂ) (X : MatQ) : C θ (z • X) = z • C θ X :=
  FiniteGibbsClock.conjugate_smul _ _ _ _
theorem C_sub (θ : ℝ) (X Y : MatQ) : C θ (X-Y) = C θ X-C θ Y := by
  simp [C, FiniteGibbsClock.conjugate, Matrix.mul_sub, Matrix.sub_mul]
theorem C_one (θ : ℝ) : C θ (1 : MatQ) = 1 :=
  FiniteGibbsClock.conjugate_one _ _
theorem C_trace (θ : ℝ) (X : MatQ) : (C θ X).trace = X.trace := by
  rw [← phase_action]; exact trace_krausMap (phase_normalized θ) X
theorem C_adjoint (θ : ℝ) (X : MatQ) : C θ Xᴴ = (C θ X)ᴴ := by
  change FiniteGibbsClock.conjugate _ (-Complex.I * θ) Xᴴ = _
  convert FiniteGibbsClock.conjugate_star (FiniteGibbsClock.twoLevel_hermitian 1) (-θ) X using 1 <;>
    simp [C]
theorem C_posSemidef (θ : ℝ) {X : MatQ} (hX : X.PosSemidef) : (C θ X).PosSemidef := by
  rw [← phase_action]; exact krausMap_posSemidef _ hX
theorem C_hermitian (θ : ℝ) {X : MatQ} (hX : X.IsHermitian) : (C θ X).IsHermitian := by
  rw [← phase_action]; exact krausMap_isHermitian _ hX
theorem C_density (θ : ℝ) {X : MatQ} (hX : IsDensityOperator X) : IsDensityOperator (C θ X) := by
  rw [← phase_action]; exact krausMap_isDensityOperator (phase_normalized θ) hX
theorem C_dual (θ : ℝ) (A X : MatQ) :
    (A * C θ X).trace = (C (-θ) A * X).trace := by
  rw [← phase_action, ← phase_observable, Matrix.trace_mul_comm,
    ← Channel.trace_duality, Matrix.trace_mul_comm]
theorem scaled_conjugate (b ℏ t : ℝ) (X : MatQ) :
    FiniteGibbsClock.conjugate (scaledH b ℏ) (-Complex.I * t) X = C (phase b ℏ t) X := by
  rw [scaledH_twoLevel]
  ext i j
  simp only [FiniteGibbsClock.twoLevel, FiniteGibbsClock.diagonal_conjugate_entry, C_entry]
  fin_cases i <;> fin_cases j <;> simp [phase] <;> congr 2 <;> push_cast <;> ring <;> simp


theorem exp_neg_delta : Real.exp (-delta) = 9/16 := by
  rw [Real.exp_neg, delta, Real.exp_log (by norm_num : (0:ℝ) < 16/9)]
  norm_num
theorem boltzmann_thermal {b : ℝ} (hb : 0 < b) :
    FiniteGibbsClock.boltzmann (thermalH b) b =
      Matrix.diagonal (![1,9/16] : Q → ℂ) := by
  have he : (-b) • thermalH b = Matrix.diagonal (![0, (-delta : ℂ)] : Q → ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [thermalH, gap, FiniteGibbsClock.twoLevel, Complex.real_smul]
    field_simp
  rw [FiniteGibbsClock.boltzmann, he, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_neg, ← Complex.ofReal_exp, exp_neg_delta]
theorem partition_thermal {b : ℝ} (hb : 0 < b) :
    FiniteGibbsClock.partition (thermalH b) b = 25/16 := by
  rw [FiniteGibbsClock.partition, boltzmann_thermal hb]
  norm_num [Matrix.trace, Fin.sum_univ_two]
theorem gibbs_thermal {b : ℝ} (hb : 0 < b) :
    FiniteGibbsClock.gibbs (thermalH b) b = rhoN := by
  rw [FiniteGibbsClock.gibbs, partition_thermal hb, boltzmann_thermal hb]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rhoN, Complex.real_smul]
theorem gibbs_thermal_posDef (b : ℝ) :
    (FiniteGibbsClock.gibbs (thermalH b) b).PosDef :=
  FiniteGibbsClock.gibbs_posDef (thermalH_hermitian b) b
theorem gibbs_thermal_density (b : ℝ) :
    IsDensityOperator (FiniteGibbsClock.gibbs (thermalH b) b) :=
  FiniteGibbsClock.gibbs_density (thermalH_hermitian b) b
theorem gibbs_thermal_sqrt {b : ℝ} (hb : 0 < b) :
    R * R = FiniteGibbsClock.gibbs (thermalH b) b := by rw [gibbs_thermal hb, R_square]
theorem log_reference (b : ℝ) (hb : 0 < b) :
    matrixLog (gibbs_thermal_posDef b).posSemidef.isHermitian =
      (-b) • thermalH b + (-(Real.log (25/16)) : ℂ) • 1 := by
  rw [FiniteGibbsClock.matrixLog_gibbs (thermalH_hermitian b) b, partition_thermal hb]
theorem log_ratio_first : Real.log (16/25) = -Real.log (25/16) := by
  rw [show (16/25 : ℝ) = (25/16)⁻¹ by norm_num, Real.log_inv]
theorem log_ratio_second : Real.log (9/25) = -delta - Real.log (25/16) := by
  rw [show (9/25 : ℝ) = (16/9)⁻¹ * (25/16)⁻¹ by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_inv, Real.log_inv]
  rfl
theorem log_reference_diagonal (b : ℝ) (hb : 0 < b) :
    matrixLog (gibbs_thermal_posDef b).posSemidef.isHermitian =
      Matrix.diagonal (![Real.log (16/25), Real.log (9/25)] : Q → ℂ) := by
  rw [log_reference b hb, log_ratio_first, log_ratio_second]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thermalH, gap, FiniteGibbsClock.twoLevel, Complex.real_smul]
  push_cast
  field_simp
  ring
theorem thermalH_not_scalar {b : ℝ} (hb : 0 < b) (z : ℂ) : thermalH b ≠ z • (1 : MatQ) := by
  intro he
  have h0 := congrArg (fun A : MatQ => A 0 0) he
  have h1 := congrArg (fun A : MatQ => A 1 1) he
  simp [thermalH, FiniteGibbsClock.twoLevel] at h0 h1
  have hz : gap b = 0 := by exact_mod_cast h1.trans h0.symm
  exact (ne_of_gt (gap_pos hb)) hz
theorem gibbs_shift {b : ℝ} (hb : 0 < b) (e : ℝ) :
    FiniteGibbsClock.gibbs (thermalH b + (e : ℂ) • 1) b = rhoN := by
  rw [FiniteGibbsClock.gibbs_energy_shift, gibbs_thermal hb]
theorem gibbs_two_scales {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    FiniteGibbsClock.gibbs (thermalH b) b = FiniteGibbsClock.gibbs (thermalH c) c := by
  rw [gibbs_thermal hb, gibbs_thermal hc]
theorem thermalH_scales_injective {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (he : thermalH b = thermalH c) : b = c := by
  have h1 := congrArg (fun A : MatQ => (A 1 1).re) he
  simp [thermalH, FiniteGibbsClock.twoLevel, gap] at h1
  field_simp at h1
  nlinarith [delta_pos]
theorem gibbs_zero_inverse_scale (H : MatQ) :
    FiniteGibbsClock.gibbs H 0 = (1/2 : ℝ) • (1 : MatQ) := by
  norm_num [FiniteGibbsClock.gibbs, FiniteGibbsClock.partition, FiniteGibbsClock.boltzmann]
theorem gibbs_zero_ne_reference (H : MatQ) : FiniteGibbsClock.gibbs H 0 ≠ rhoN := by
  rw [gibbs_zero_inverse_scale]
  intro he
  have h0 := congrArg (fun A : MatQ => A 0 0) he
  norm_num [rhoN, Complex.real_smul] at h0
theorem scalar_gibbs (e b : ℝ) :
    FiniteGibbsClock.gibbs ((e : ℂ) • (1 : MatQ)) b = (1/2 : ℝ) • (1 : MatQ) := by
  simpa using (FiniteGibbsClock.gibbs_scalar (ι := Q) e b)
theorem scalar_flow (e ℏ t : ℝ) (X : MatQ) :
    FiniteGibbsClock.heisenberg ((e : ℂ) • 1) ℏ t X = X :=
  FiniteGibbsClock.heisenberg_scalar e ℏ t X


theorem frequency_pos {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ) : 0 < frequency b ℏ :=
  div_pos (gap_pos hb) hℏ
theorem C_heisenberg (b ℏ t : ℝ) (_hℏ : 0 < ℏ) (X : MatQ) :
    C (phase b ℏ t) X = FiniteGibbsClock.heisenberg (thermalH b) ℏ (-t) X := by
  rw [← scaled_conjugate]
  ext i j
  simp only [scaledH_twoLevel, thermalH, FiniteGibbsClock.heisenberg,
    FiniteGibbsClock.twoLevel, FiniteGibbsClock.diagonal_conjugate_entry]
  fin_cases i <;> fin_cases j <;> simp [frequency] <;> congr 2 <;> push_cast <;> ring <;> simp
theorem C_observable_heisenberg (b ℏ t : ℝ) (hℏ : 0 < ℏ) (X : MatQ) :
    C (-phase b ℏ t) X = FiniteGibbsClock.heisenberg (thermalH b) ℏ t X := by
  simpa [phase] using C_heisenberg b ℏ (-t) hℏ X
theorem modular_phase {b : ℝ} (hb : 0 < b) (s : ℝ) (X : MatQ) :
    FiniteGibbsClock.modular (thermalH_hermitian b) b s X = C (delta*s) X := by
  rw [FiniteGibbsClock.modular_conjugate]
  ext i j
  simp only [thermalH, FiniteGibbsClock.twoLevel, FiniteGibbsClock.diagonal_conjugate_entry, C_entry]
  fin_cases i <;> fin_cases j <;> simp [gap] <;> congr 2 <;> push_cast <;> field_simp <;> ring <;> simp
theorem observable_modular {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ) (t : ℝ) (X : MatQ) :
    FiniteGibbsClock.heisenberg (thermalH b) ℏ t X =
      FiniteGibbsClock.modular (thermalH_hermitian b) b (-t/(b*ℏ)) X := by
  rw [modular_phase hb, ← C_observable_heisenberg b ℏ t hℏ]
  congr 1
  simp [phase, frequency, gap]
  ring
theorem C_E01 (θ : ℝ) :
    C θ FiniteGibbsClock.E01 = Complex.exp (Complex.I * θ) • FiniteGibbsClock.E01 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C_entry, FiniteGibbsClock.E01, Matrix.single]
theorem C_iE01 (θ : ℝ) :
    C θ (Complex.I • FiniteGibbsClock.E01) =
      Complex.exp (Complex.I * θ) • (Complex.I • FiniteGibbsClock.E01) := by
  rw [C_smul, C_E01, smul_comm]
theorem C_full_period (X : MatQ) : C (2*Real.pi) X = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C_entry]
  · rw [show Complex.I*(2*Real.pi)=2*Real.pi*Complex.I by ring, Complex.exp_two_pi_mul_I, one_mul]
  · rw [show -(Complex.I*(2*Real.pi))= -(2*Real.pi*Complex.I) by ring,
      Complex.exp_neg, Complex.exp_two_pi_mul_I]; simp
theorem C_periodic (θ : ℝ) (X : MatQ) : C (θ+2*Real.pi) X = C θ X := by
  rw [C_group, C_full_period]
theorem C_half_E01 : C Real.pi FiniteGibbsClock.E01 = -FiniteGibbsClock.E01 := by
  rw [C_E01, mul_comm Complex.I, Complex.exp_pi_mul_I, neg_one_smul]
theorem C_half_nontrivial : C Real.pi FiniteGibbsClock.E01 ≠ FiniteGibbsClock.E01 := by
  rw [C_half_E01]
  intro he
  have h := congrArg (fun A : MatQ => A 0 1) he
  norm_num [FiniteGibbsClock.E01, Matrix.single] at h
theorem C_half_pauliX : C Real.pi pauliX = -pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C_entry, pauliX]
  · rw [mul_comm Complex.I, Complex.exp_pi_mul_I]
  · rw [show -(Complex.I*Real.pi)= -(Real.pi*Complex.I) by ring, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
theorem phase_not_injective : ¬ Function.Injective (fun θ : ℝ => C θ) := by
  intro hi
  have he : C (2*Real.pi) = C 0 := by funext X; rw [C_full_period,C_zero]
  have h := hi he
  nlinarith [Real.pi_pos]
theorem C_diagonal (θ : ℝ) (d : Q → ℂ) : C θ (Matrix.diagonal d) = Matrix.diagonal d := by
  ext i j
  by_cases h : i=j
  · subst j; simp [C_entry]
  · simp [C_entry, h]
theorem C_rho (θ : ℝ) : C θ rhoN = rhoN := by
  have hd : rhoN = Matrix.diagonal (![16/25,9/25] : Q → ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hd,C_diagonal]
theorem C_diagonalPart (θ : ℝ) (X : MatQ) :
    C θ (NontracialReflectionDynamics.diagonalPart X) = NontracialReflectionDynamics.diagonalPart X :=
  C_diagonal θ _
theorem diagonalPart_C (θ : ℝ) (X : MatQ) :
    NontracialReflectionDynamics.diagonalPart (C θ X) = NontracialReflectionDynamics.diagonalPart X := by
  ext i j
  by_cases h : i=j
  · subst j; simp [NontracialReflectionDynamics.diagonalPart, C_entry]
  · simp [NontracialReflectionDynamics.diagonalPart,h]
theorem C_reset (θ : ℝ) (X : MatQ) : C θ (X.trace • rhoN) = X.trace • rhoN := by
  rw [C_smul,C_rho]
theorem C_R (θ : ℝ) : C θ R = R := by
  have hd : R = Matrix.diagonal (![4/5,3/5] : Q → ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hd,C_diagonal]
theorem C_mul (θ : ℝ) (X Y : MatQ) : C θ (X*Y) = C θ X*C θ Y :=
  FiniteGibbsClock.conjugate_mul _ _ _ _
theorem C_Gamma (θ : ℝ) (X : MatQ) : C θ (Gamma X) = Gamma (C θ X) := by
  simp only [Gamma,C_mul,C_R]
theorem C_weighted_trace (θ : ℝ) (X : MatQ) : (rhoN*C θ X).trace=(rhoN*X).trace := by
  rw [← C_rho θ, ← C_mul, C_trace, C_rho]
theorem state_C (γ η t θ : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (X : MatQ) :
    NontracialReflectionDynamics.state γ η t (C θ X) =
      C θ (NontracialReflectionDynamics.state γ η t X) := by
  rw [NontracialReflectionDynamics.state_formula γ η t hγ hη ht,
    NontracialReflectionDynamics.state_formula γ η t hγ hη ht]
  simp only [C_add,C_sub,C_smul,C_trace,C_rho,C_diagonalPart,diagonalPart_C]
theorem observable_C (γ η t θ : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (X : MatQ) :
    NontracialReflectionDynamics.observable γ η t (C θ X) =
      C θ (NontracialReflectionDynamics.observable γ η t X) := by
  rw [NontracialReflectionDynamics.observable_formula γ η t hγ hη ht,
    NontracialReflectionDynamics.observable_formula γ η t hγ hη ht]
  simp only [C_add,C_sub,C_smul,C_weighted_trace,C_one,C_diagonalPart,diagonalPart_C]

def thermalKraus (b ℏ γ η t : ℝ) :=
  composeKraus (phaseKraus (phase b ℏ t)) (NontracialReflectionDynamics.timeKraus γ η t)
def state (b ℏ γ η t : ℝ) (X : MatQ) := krausMap (thermalKraus b ℏ γ η t) X
def observable (b ℏ γ η t : ℝ) (A : MatQ) := Channel.heisenberg (thermalKraus b ℏ γ η t) A
theorem normalized (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    IsKrausChannel (thermalKraus b ℏ γ η t) :=
  isKrausChannel_composeKraus (phase_normalized _) (NontracialReflectionDynamics.normalized γ η t hγ hη ht)
theorem state_factor (b ℏ γ η t : ℝ) (X : MatQ) :
    state b ℏ γ η t X = C (phase b ℏ t) (NontracialReflectionDynamics.state γ η t X) := by
  rw [state,thermalKraus,krausMap_composeKraus,phase_action]; rfl
theorem observable_factor (b ℏ γ η t : ℝ) (A : MatQ) :
    observable b ℏ γ η t A = NontracialReflectionDynamics.observable γ η t (C (-phase b ℏ t) A) := by
  rw [observable,thermalKraus,FiniteNontracialSchedule.heisenberg_compose,phase_observable]; rfl
theorem observable_commuted (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (A : MatQ) :
    observable b ℏ γ η t A = C (-phase b ℏ t) (NontracialReflectionDynamics.observable γ η t A) := by
  rw [observable_factor,observable_C γ η t _ hγ hη ht]
theorem actual_propagator_factor (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (X : MatQ) :
    lindbladPropagatorAction (scaledH b ℏ) (jumps γ η) t X =
      C (phase b ℏ t) (lindbladPropagatorAction 0 (jumps γ η) t X) := by
  rw [propagator_factor _ _ (ham_noise_commute b ℏ γ η hγ hη),scaled_conjugate]
theorem state_eq_propagator (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (X : MatQ) :
    state b ℏ γ η t X = lindbladPropagatorAction (scaledH b ℏ) (jumps γ η) t X := by
  rw [actual_propagator_factor b ℏ γ η t hγ hη,state_factor]
  congr 1
  exact GibbsBlockRelaxation.time_state_eq_propagator _ _ weights_nonnegative weights_normalized γ η t hγ hη ht X
def energies (b ℏ : ℝ) : Q → ℝ := ![0,frequency b ℏ]
theorem scaledH_density (b ℏ : ℝ) : scaledH b ℏ = DiagonalLindblad.density (energies b ℏ) := by
  rw [scaledH_twoLevel]
  ext i j; fin_cases i <;> fin_cases j <;> simp [FiniteGibbsClock.twoLevel,DiagonalLindblad.density,energies]
/-- Explicit correspondence of differently indexed actual families, with identical jumps. -/
theorem existing_realization_correspondence (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (ht : 0 ≤ t) (X : MatQ) :
    krausMap (thermalKraus b ℏ γ η t) X =
      krausMap (GibbsHamiltonianRelaxation.timeKraus (energies b ℏ)
        NontracialReflectionDynamics.signature weights γ η t) X := by
  rw [GibbsHamiltonianRelaxation.time_state_eq_propagator _ _ _ weights_nonnegative
    weights_normalized γ η t hγ hη ht]
  change state b ℏ γ η t X = _
  rw [state_eq_propagator b ℏ γ η t hγ hη ht,scaledH_density]
  rfl
theorem thermal_trace_dual (b ℏ γ η t : ℝ) (A X : MatQ) :
    (A*state b ℏ γ η t X).trace=(observable b ℏ γ η t A*X).trace := by
  rw [state,observable,Matrix.trace_mul_comm,← Channel.trace_duality,Matrix.trace_mul_comm]
theorem stationary (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    state b ℏ γ η t rhoN = rhoN := by
  rw [state_factor,NontracialReflectionDynamics.stationary γ η t hγ hη ht,C_rho]
theorem thermal_density (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    {X : MatQ} (hX : IsDensityOperator X) : IsDensityOperator (state b ℏ γ η t X) :=
  krausMap_isDensityOperator (normalized b ℏ γ η t hγ hη ht) hX


abbrev Slice := FiniteNontracialSchedule.Slice
abbrev Schedule := FiniteNontracialSchedule.Schedule
def freeKraus (θ : ℝ) (s : Schedule) := composeKraus (phaseKraus θ) (FiniteNontracialSchedule.scheduleKraus s)
def freeState (θ : ℝ) (s : Schedule) (X : MatQ) := krausMap (freeKraus θ s) X
def freeObservable (θ : ℝ) (s : Schedule) (A : MatQ) := Channel.heisenberg (freeKraus θ s) A
theorem free_normalized (θ : ℝ) (s : Schedule) : IsKrausChannel (freeKraus θ s) :=
  isKrausChannel_composeKraus (phase_normalized θ) (FiniteNontracialSchedule.normalized s)
theorem free_state (θ : ℝ) (s : Schedule) (X : MatQ) :
    freeState θ s X = C θ (FiniteNontracialSchedule.state s X) := by
  rw [freeState,freeKraus,krausMap_composeKraus,phase_action]; rfl
theorem free_observable (θ : ℝ) (s : Schedule) (A : MatQ) :
    freeObservable θ s A = FiniteNontracialSchedule.observable s (C (-θ) A) := by
  rw [freeObservable,freeKraus,FiniteNontracialSchedule.heisenberg_compose,phase_observable]; rfl
theorem free_empty (θ : ℝ) (X : MatQ) : freeState θ [] X = C θ X := by
  rw [free_state,FiniteNontracialSchedule.state_nil]
theorem free_empty_nontrivial : freeState Real.pi [] FiniteGibbsClock.E01 ≠ FiniteGibbsClock.E01 := by
  rw [free_empty]; exact C_half_nontrivial
def elapsed : Schedule → ℝ
  | [] => 0
  | h::s => h.duration + elapsed s
def totalPhase (b ℏ : ℝ) (s : Schedule) := frequency b ℏ * elapsed s
def stepCount : ℕ := 1 * FiniteNontracialSchedule.primitiveCount
def timedCount : Schedule → ℕ
  | [] => 1
  | _::s => timedCount s * stepCount
def timedKraus (b ℏ : ℝ) : (s : Schedule) → Fin (timedCount s) → MatQ
  | [] => idKrausPad 0 2
  | h::s => composeKraus (timedKraus b ℏ s) (thermalKraus b ℏ h.gamma h.eta h.duration)
def timedState (b ℏ : ℝ) (s : Schedule) (X : MatQ) := krausMap (timedKraus b ℏ s) X
def timedObservable (b ℏ : ℝ) (s : Schedule) (A : MatQ) := Channel.heisenberg (timedKraus b ℏ s) A
theorem timed_normalized (b ℏ : ℝ) (s : Schedule) : IsKrausChannel (timedKraus b ℏ s) := by
  induction s with
  | nil => exact isKrausChannel_idKrausPad 0 2
  | cons h s ih =>
    exact isKrausChannel_composeKraus ih
      (normalized b ℏ h.gamma h.eta h.duration h.gamma_nonneg h.eta_nonneg h.duration_nonneg)
@[simp] theorem timed_nil (b ℏ : ℝ) (X : MatQ) : timedState b ℏ [] X = X :=
  krausMap_idKrausPad 0 2 X
theorem timed_cons (b ℏ : ℝ) (h : Slice) (s : Schedule) (X : MatQ) :
    timedState b ℏ (h::s) X = timedState b ℏ s (state b ℏ h.gamma h.eta h.duration X) :=
  krausMap_composeKraus _ _ X
theorem timed_append (b ℏ : ℝ) (s t : Schedule) (X : MatQ) :
    timedState b ℏ (s++t) X = timedState b ℏ t (timedState b ℏ s X) := by
  induction s generalizing X with
  | nil => simp
  | cons h s ih => simpa only [List.cons_append,timed_cons] using ih (state b ℏ h.gamma h.eta h.duration X)
theorem timed_observable_cons (b ℏ : ℝ) (h : Slice) (s : Schedule) (A : MatQ) :
    timedObservable b ℏ (h::s) A = observable b ℏ h.gamma h.eta h.duration (timedObservable b ℏ s A) :=
  FiniteNontracialSchedule.heisenberg_compose _ _ A
theorem timed_dual (b ℏ : ℝ) (s : Schedule) (A X : MatQ) :
    (A*timedState b ℏ s X).trace = (timedObservable b ℏ s A*X).trace := by
  rw [timedState,timedObservable,Matrix.trace_mul_comm,← Channel.trace_duality,Matrix.trace_mul_comm]
theorem timed_observable_append (b ℏ : ℝ) (s t : Schedule) (A : MatQ) :
    timedObservable b ℏ (s++t) A = timedObservable b ℏ s (timedObservable b ℏ t A) := by
  apply FiniteNontracialSchedule.trace_ext
  intro X
  rw [← timed_dual, timed_append, timed_dual, timed_dual]
theorem elapsed_nonneg (s : Schedule) : 0 ≤ elapsed s := by
  induction s with
  | nil => exact le_rfl
  | cons h s ih => exact add_nonneg h.duration_nonneg ih
theorem elapsed_append (s t : Schedule) : elapsed (s++t) = elapsed s+elapsed t := by
  induction s with
  | nil => simp [elapsed]
  | cons h s ih => simp [elapsed,ih,add_assoc]
theorem schedule_C (θ : ℝ) (s : Schedule) (X : MatQ) :
    FiniteNontracialSchedule.state s (C θ X) = C θ (FiniteNontracialSchedule.state s X) := by
  induction s generalizing X with
  | nil => simp
  | cons h s ih =>
    rw [FiniteNontracialSchedule.state_cons,state_C _ _ _ _ h.gamma_nonneg h.eta_nonneg h.duration_nonneg,
      ih,FiniteNontracialSchedule.state_cons]
theorem timed_factor (b ℏ : ℝ) (s : Schedule) (X : MatQ) :
    timedState b ℏ s X = C (totalPhase b ℏ s) (FiniteNontracialSchedule.state s X) := by
  induction s generalizing X with
  | nil => simp [totalPhase,elapsed,C_zero]
  | cons h s ih =>
    rw [timed_cons,ih,state_factor,schedule_C,← C_group,FiniteNontracialSchedule.state_cons]
    congr 1
    simp [totalPhase,elapsed,phase]
    ring
theorem timed_observable_factor (b ℏ : ℝ) (s : Schedule) (A : MatQ) :
    timedObservable b ℏ s A = FiniteNontracialSchedule.observable s (C (-totalPhase b ℏ s) A) := by
  apply FiniteNontracialSchedule.trace_ext
  intro X
  rw [← timed_dual,timed_factor,C_dual,FiniteNontracialSchedule.trace_dual]
theorem timed_free_correspondence (b ℏ : ℝ) (s : Schedule) (X : MatQ) :
    timedState b ℏ s X = freeState (totalPhase b ℏ s) s X := by rw [timed_factor,free_state]
theorem all_zero_elapsed (s : Schedule) (h : ∀ a ∈ s, a.duration=0) : elapsed s=0 := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    rw [elapsed,h a (by simp),ih (by intro x hx; exact h x (by simp [hx])),zero_add]
theorem all_zero_phase (b ℏ : ℝ) (s : Schedule) (h : ∀ a ∈ s, a.duration=0) :
    totalPhase b ℏ s=0 := by rw [totalPhase,all_zero_elapsed s h,mul_zero]

theorem zero_rates (b ℏ t : ℝ) (ht : 0 ≤ t) (X : MatQ) :
    state b ℏ 0 0 t X = C (phase b ℏ t) X := by
  rw [state_factor,NontracialReflectionDynamics.state_formula 0 0 t (by norm_num) (by norm_num) ht]
  simp
theorem positive_duration_hamiltonian {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ) :
    0 < Real.pi / frequency b ℏ ∧
    state b ℏ 0 0 (Real.pi/frequency b ℏ) FiniteGibbsClock.E01 ≠ FiniteGibbsClock.E01 := by
  have hp := div_pos Real.pi_pos (frequency_pos hb hℏ)
  refine ⟨hp,?_⟩
  rw [zero_rates b ℏ _ hp.le,phase,mul_div_cancel₀ _ (ne_of_gt (frequency_pos hb hℏ))]
  exact C_half_nontrivial
theorem C_traceNorm {X : MatQ} (hX : X.IsHermitian) (θ : ℝ) :
    QuantumNetwork.traceNorm (C θ X) = QuantumNetwork.traceNorm X := by
  apply le_antisymm
  · simpa only [phase_action] using traceNorm_krausMap_le (phase_normalized θ) hX
  · have h := traceNorm_krausMap_le (phase_normalized (-θ)) (C_hermitian θ hX)
    simpa only [phase_action,C_inverse] using h
theorem C_traceDist {X Y : MatQ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (θ : ℝ) :
    traceDist (C θ X) (C θ Y) = traceDist X Y := by
  unfold traceDist
  rw [← C_sub,C_traceNorm (hX.sub hY)]
theorem C_density_distance {X Y : MatQ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y) (θ : ℝ) :
    traceDist (C θ X) (C θ Y) = traceDist X Y :=
  C_traceDist hX.1.isHermitian hY.1.isHermitian θ
theorem free_distance {X Y : MatQ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (θ : ℝ) (s : Schedule) :
    traceDist (freeState θ s X) (freeState θ s Y) =
      traceDist (FiniteNontracialSchedule.state s X) (FiniteNontracialSchedule.state s Y) := by
  rw [free_state,free_state]
  exact C_traceDist (krausMap_isHermitian _ hX) (krausMap_isHermitian _ hY) θ
def timedLiftKraus (b ℏ : ℝ) (s : Schedule) := FiniteNontracialEnvironmentLift.liftKraus (timedKraus b ℏ s)
def timedLiftState (b ℏ : ℝ) (s : Schedule) (X : FiniteNontracialEnvironmentLift.MatJoint) :=
  krausMap (timedLiftKraus b ℏ s) X
def timedLiftObservable (b ℏ : ℝ) (s : Schedule) (A : FiniteNontracialEnvironmentLift.MatJoint) :=
  Channel.heisenberg (timedLiftKraus b ℏ s) A
theorem timed_lift_normalized (b ℏ : ℝ) (s : Schedule) : IsKrausChannel (timedLiftKraus b ℏ s) :=
  FiniteNontracialEnvironmentLift.normalized (timed_normalized b ℏ s)
theorem timed_lift_product (b ℏ : ℝ) (s : Schedule) (A B : MatQ) :
    timedLiftState b ℏ s (A ⊗ₖ B) = A ⊗ₖ timedState b ℏ s B :=
  FiniteNontracialEnvironmentLift.product_action _ A B
theorem timed_lift_observable_product (b ℏ : ℝ) (s : Schedule) (A B : MatQ) :
    timedLiftObservable b ℏ s (A ⊗ₖ B) = A ⊗ₖ timedObservable b ℏ s B :=
  FiniteNontracialEnvironmentLift.observable_product_action _ A B
theorem timed_lift_spectator (b ℏ : ℝ) (s : Schedule) (X : FiniteNontracialEnvironmentLift.MatJoint) :
    FiniteNontracialEnvironmentLift.ptrace2 (timedLiftState b ℏ s X) =
      FiniteNontracialEnvironmentLift.ptrace2 X :=
  FiniteNontracialEnvironmentLift.spectator (timed_normalized b ℏ s) X
theorem timed_lift_dual (b ℏ : ℝ) (s : Schedule) (A X : FiniteNontracialEnvironmentLift.MatJoint) :
    (A*timedLiftState b ℏ s X).trace = (timedLiftObservable b ℏ s A*X).trace := by
  rw [timedLiftState,timedLiftObservable,Matrix.trace_mul_comm,← Channel.trace_duality,Matrix.trace_mul_comm]
theorem timed_lift_hermitian (b ℏ : ℝ) (s : Schedule) {X : FiniteNontracialEnvironmentLift.MatJoint}
    (hX : X.IsHermitian) : (timedLiftState b ℏ s X).IsHermitian :=
  krausMap_isHermitian _ hX
theorem timed_lift_density (b ℏ : ℝ) (s : Schedule) {X : FiniteNontracialEnvironmentLift.MatJoint}
    (hX : IsDensityOperator X) : IsDensityOperator (timedLiftState b ℏ s X) :=
  krausMap_isDensityOperator (timed_lift_normalized b ℏ s) hX
theorem timed_lift_posSemidef (b ℏ : ℝ) (s : Schedule) {X : FiniteNontracialEnvironmentLift.MatJoint}
    (hX : X.PosSemidef) : (timedLiftState b ℏ s X).PosSemidef :=
  krausMap_posSemidef _ hX
theorem timed_lift_trace (b ℏ : ℝ) (s : Schedule) (X : FiniteNontracialEnvironmentLift.MatJoint) :
    (timedLiftState b ℏ s X).trace=X.trace := trace_krausMap (timed_lift_normalized b ℏ s) X

def observableGenerator (b ℏ γ η : ℝ) (A : MatQ) : MatQ :=
  Complex.I • (scaledH b ℏ*A-A*scaledH b ℏ) +
    (γ : ℂ) • ((rhoN*A).trace • (1:MatQ)-A) +
    (η : ℂ) • (NontracialReflectionDynamics.diagonalPart A-A)
theorem generator_dual (b ℏ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (A X : MatQ) :
    (A * lindbladGenerator (scaledH b ℏ) (jumps γ η) X).trace =
      (observableGenerator b ℏ γ η A*X).trace := by
  rw [actual_generator b ℏ γ η hγ hη]
  simp [observableGenerator,scaledH_twoLevel,FiniteGibbsClock.twoLevel,
    NontracialReflectionDynamics.diagonalPart,rhoN,Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,vecHead,vecTail]
  ring
theorem generator_E01 (b ℏ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    lindbladGenerator (scaledH b ℏ) (jumps γ η) FiniteGibbsClock.E01 =
      (-(γ+η : ℂ)+Complex.I*frequency b ℏ) • FiniteGibbsClock.E01 := by
  rw [actual_generator b ℏ γ η hγ hη]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scaledH_twoLevel,FiniteGibbsClock.twoLevel,FiniteGibbsClock.E01,Matrix.single,
      NontracialReflectionDynamics.diagonalPart,rhoN,Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,vecHead,vecTail] <;> ring
theorem observable_generator_E01 (b ℏ γ η : ℝ) :
    observableGenerator b ℏ γ η FiniteGibbsClock.E01 =
      (-(γ+η : ℂ)-Complex.I*frequency b ℏ) • FiniteGibbsClock.E01 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [observableGenerator,scaledH_twoLevel,FiniteGibbsClock.twoLevel,FiniteGibbsClock.E01,Matrix.single,
      NontracialReflectionDynamics.diagonalPart,rhoN,Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,vecHead,vecTail] <;> ring
theorem generator_iE01 (b ℏ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    lindbladGenerator (scaledH b ℏ) (jumps γ η) (Complex.I • FiniteGibbsClock.E01) =
      (-(γ+η : ℂ)+Complex.I*frequency b ℏ) • (Complex.I • FiniteGibbsClock.E01) := by
  rw [map_smul,generator_E01 b ℏ γ η hγ hη,smul_comm]
theorem observableGenerator_smul (b ℏ γ η : ℝ) (z : ℂ) (A : MatQ) :
    observableGenerator b ℏ γ η (z • A)=z • observableGenerator b ℏ γ η A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [observableGenerator,NontracialReflectionDynamics.diagonalPart,Matrix.mul_apply,
    Matrix.trace,Fin.sum_univ_two] <;> ring
theorem observable_generator_iE01 (b ℏ γ η : ℝ) :
    observableGenerator b ℏ γ η (Complex.I • FiniteGibbsClock.E01) =
      (-(γ+η : ℂ)-Complex.I*frequency b ℏ) • (Complex.I • FiniteGibbsClock.E01) := by
  rw [observableGenerator_smul,observable_generator_E01,smul_comm]
theorem noise_E01 (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    NontracialReflectionDynamics.state γ η t FiniteGibbsClock.E01 =
      (Real.exp (-(γ+η)*t) : ℂ) • FiniteGibbsClock.E01 := by
  rw [NontracialReflectionDynamics.state_formula γ η t hγ hη ht]
  have hd : NontracialReflectionDynamics.diagonalPart FiniteGibbsClock.E01=0 := by
    ext i j;fin_cases i <;> fin_cases j <;> simp [NontracialReflectionDynamics.diagonalPart,FiniteGibbsClock.E01,Matrix.single]
  rw [hd]
  simp [FiniteGibbsClock.E01,Matrix.trace,Fin.sum_univ_two,Matrix.single]
theorem noise_observable_E01 (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    NontracialReflectionDynamics.observable γ η t FiniteGibbsClock.E01 =
      (Real.exp (-(γ+η)*t) : ℂ) • FiniteGibbsClock.E01 := by
  rw [NontracialReflectionDynamics.observable_formula γ η t hγ hη ht]
  ext i j;fin_cases i <;> fin_cases j <;>
    simp [NontracialReflectionDynamics.diagonalPart,FiniteGibbsClock.E01,Matrix.single,
      rhoN,Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,vecHead,vecTail]
theorem state_E01 (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    state b ℏ γ η t FiniteGibbsClock.E01 =
      ((Real.exp (-(γ+η)*t) : ℂ)*Complex.exp (Complex.I*phase b ℏ t)) • FiniteGibbsClock.E01 := by
  rw [state_factor,noise_E01 γ η t hγ hη ht,C_smul,C_E01,smul_smul]
theorem observable_E01 (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    observable b ℏ γ η t FiniteGibbsClock.E01 =
      ((Real.exp (-(γ+η)*t) : ℂ)*Complex.exp (-Complex.I*phase b ℏ t)) • FiniteGibbsClock.E01 := by
  rw [observable_commuted b ℏ γ η t hγ hη ht,noise_observable_E01 γ η t hγ hη ht,C_smul,C_E01,smul_smul]
  simp
theorem state_iE01 (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    state b ℏ γ η t (Complex.I • FiniteGibbsClock.E01) =
      ((Real.exp (-(γ+η)*t) : ℂ)*Complex.exp (Complex.I*phase b ℏ t)) • (Complex.I • FiniteGibbsClock.E01) := by
  change krausMap _ (Complex.I • _) = _
  rw [krausMap_smul]
  change Complex.I • state b ℏ γ η t _ = _
  rw [state_E01 b ℏ γ η t hγ hη ht,smul_comm]
theorem observable_iE01 (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    observable b ℏ γ η t (Complex.I • FiniteGibbsClock.E01) =
      ((Real.exp (-(γ+η)*t) : ℂ)*Complex.exp (-Complex.I*phase b ℏ t)) • (Complex.I • FiniteGibbsClock.E01) := by
  have hs : observable b ℏ γ η t (Complex.I • FiniteGibbsClock.E01) =
      Complex.I • observable b ℏ γ η t FiniteGibbsClock.E01 := by
    simp [observable,Channel.heisenberg,Matrix.mul_smul,Matrix.smul_mul,Finset.smul_sum]
  rw [hs,observable_E01 b ℏ γ η t hγ hη ht,smul_comm]
theorem iE01_eq_imaginary : Complex.I • FiniteGibbsClock.E01 = FiniteNontracialMemoryScheduleControls.imaginary := by
  ext i j;fin_cases i <;> fin_cases j <;> simp [FiniteGibbsClock.E01,FiniteNontracialMemoryScheduleControls.imaginary,Matrix.single]
theorem iE01_not_hermitian : ¬(Complex.I • FiniteGibbsClock.E01).IsHermitian := by
  rw [iE01_eq_imaginary]; exact FiniteNontracialMemoryScheduleControls.imaginary_not_hermitian
theorem iE01_not_posSemidef : ¬(Complex.I • FiniteGibbsClock.E01).PosSemidef := by
  rw [iE01_eq_imaginary]; exact FiniteNontracialMemoryScheduleControls.imaginary_not_PSD
theorem iE01_not_density : ¬IsDensityOperator (Complex.I • FiniteGibbsClock.E01) := by
  rw [iE01_eq_imaginary]; exact FiniteNontracialMemoryScheduleControls.imaginary_not_density


theorem modular_E01 {b : ℝ} (hb : 0 < b) (s : ℝ) :
    FiniteGibbsClock.modular (thermalH_hermitian b) b s FiniteGibbsClock.E01 =
      Complex.exp (Complex.I*(delta*s)) • FiniteGibbsClock.E01 := by rw [modular_phase hb,C_E01]; simp only [Complex.ofReal_mul]
theorem modular_iE01 {b : ℝ} (hb : 0 < b) (s : ℝ) :
    FiniteGibbsClock.modular (thermalH_hermitian b) b s (Complex.I • FiniteGibbsClock.E01) =
      Complex.exp (Complex.I*(delta*s)) • (Complex.I • FiniteGibbsClock.E01) := by
  rw [modular_phase hb,C_iE01]
  simp only [Complex.ofReal_mul]
theorem energy_shift_flow (b ℏ e t : ℝ) (_hℏ : 0 < ℏ) (X : MatQ) :
    FiniteGibbsClock.heisenberg (thermalH b+(e:ℂ) • 1) ℏ t X =
      FiniteGibbsClock.heisenberg (thermalH b) ℏ t X :=
  FiniteGibbsClock.heisenberg_energy_shift _ _ _ _ _
theorem shifted_generator (b ℏ e γ η : ℝ) (X : MatQ) :
    lindbladGenerator (scaledH b ℏ + (e:ℂ) • 1) (jumps γ η) X =
      lindbladGenerator (scaledH b ℏ) (jumps γ η) X := by
  have hh : lindbladHamPart (scaledH b ℏ+(e:ℂ) • 1)=lindbladHamPart (scaledH b ℏ) := by
    ext Y i j
    simp [lindbladHamPart_apply,Matrix.add_mul,Matrix.mul_add]
  simp only [lindbladGenerator,hh]
theorem scaledH_nonzero {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ) : scaledH b ℏ ≠ 0 := by
  intro he
  have hh := congrArg (fun A : MatQ => (A 1 1).re) he
  simp [scaledH_twoLevel,FiniteGibbsClock.twoLevel] at hh
  exact (ne_of_gt (frequency_pos hb hℏ)) hh
theorem physical_time_periodic {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ) (t : ℝ) (X : MatQ) :
    C (phase b ℏ (t+2*Real.pi/frequency b ℏ)) X = C (phase b ℏ t) X := by
  have hp : phase b ℏ (t+2*Real.pi/frequency b ℏ)=phase b ℏ t+2*Real.pi := by
    simp only [phase,mul_add]
    rw [mul_div_cancel₀ _ (ne_of_gt (frequency_pos hb hℏ))]
  rw [hp,C_periodic]
theorem physical_time_not_injective {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ) :
    ¬ Function.Injective (fun t : ℝ => C (phase b ℏ t)) := by
  intro hi
  have hp := div_pos (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos) (frequency_pos hb hℏ)
  have he : C (phase b ℏ (2*Real.pi/frequency b ℏ))=C (phase b ℏ 0) := by
    funext X
    simpa using physical_time_periodic hb hℏ 0 X
  have hz := hi he
  exact (ne_of_gt hp) hz
theorem state_one (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    state b ℏ γ η t (1:MatQ) =
      (1-(Real.exp (-γ*t):ℂ)) • ((2:ℂ) • rhoN)+(Real.exp (-γ*t):ℂ) • (1:MatQ) := by
  rw [state_factor,NontracialReflectionDynamics.state_formula γ η t hγ hη ht]
  have hd : NontracialReflectionDynamics.diagonalPart (1:MatQ)=1 := by
    ext i j;fin_cases i <;> fin_cases j <;> simp [NontracialReflectionDynamics.diagonalPart]
  rw [hd]
  norm_num [Matrix.trace,Fin.sum_univ_two,C_add,C_sub,C_smul,C_rho,C_one]
  module
theorem observable_one (b ℏ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    observable b ℏ γ η t (1:MatQ)=1 := by
  change (∑ k, (thermalKraus b ℏ γ η t k)ᴴ*1*thermalKraus b ℏ γ η t k)=1
  simpa [IsKrausChannel] using normalized b ℏ γ η t hγ hη ht
theorem state_observable_one_distinct (b ℏ γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) :
    state b ℏ γ η t (1:MatQ) ≠ observable b ℏ γ η t 1 := by
  rw [state_one b ℏ γ η t hγ.le hη ht.le,observable_one b ℏ γ η t hγ.le hη ht.le]
  intro he
  have hh := congrArg (fun A : MatQ => (A 0 0).re) he
  norm_num [rhoN] at hh
  simp only [← Complex.ofReal_mul,← Complex.ofReal_neg,← Complex.ofReal_exp,Complex.ofReal_re] at hh
  have hl : Real.exp (-(γ*t))<1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  nlinarith
theorem E01_not_hermitian : ¬FiniteGibbsClock.E01.IsHermitian := by
  intro h
  have he := congrArg (fun A : MatQ => A 0 1) h.eq
  norm_num [FiniteGibbsClock.E01,Matrix.single,Matrix.conjTranspose_apply] at he
theorem E01_not_posSemidef : ¬FiniteGibbsClock.E01.PosSemidef := fun h => E01_not_hermitian h.isHermitian
theorem E01_not_density : ¬IsDensityOperator FiniteGibbsClock.E01 := fun h => E01_not_hermitian h.1.isHermitian
theorem timed_zero_durations (b ℏ : ℝ) (s : Schedule) (hz : ∀ a∈s,a.duration=0) (X : MatQ) :
    timedState b ℏ s X=X ∧ timedObservable b ℏ s X=X := by
  have hn := FiniteNontracialSchedule.zero_duration_actions s hz
  constructor
  · rw [timed_factor,all_zero_phase b ℏ s hz,(hn X).1,C_zero]
  · rw [timed_observable_factor,all_zero_phase b ℏ s hz,neg_zero,C_zero,(hn X).2]
theorem timed_zero_rates (b ℏ : ℝ) (s : Schedule) (hz : ∀ a∈s,a.gamma=0 ∧ a.eta=0) (X : MatQ) :
    timedState b ℏ s X=C (totalPhase b ℏ s) X ∧
      timedObservable b ℏ s X=C (-totalPhase b ℏ s) X := by
  constructor
  · rw [timed_factor,(FiniteNontracialSchedule.zero_rate_actions s hz X).1]
  · rw [timed_observable_factor,(FiniteNontracialSchedule.zero_rate_actions s hz _).2]
def halfTurnSlice (b ℏ : ℝ) (hb : 0 < b) (hℏ : 0 < ℏ) : Slice :=
  ⟨0,0,Real.pi/frequency b ℏ,le_rfl,le_rfl,(div_pos Real.pi_pos (frequency_pos hb hℏ)).le⟩
theorem timed_positive_zero_rate_witness (b ℏ : ℝ) (hb : 0 < b) (hℏ : 0 < ℏ) :
    0 < elapsed [halfTurnSlice b ℏ hb hℏ] ∧
    timedState b ℏ [halfTurnSlice b ℏ hb hℏ] FiniteGibbsClock.E01 ≠ FiniteGibbsClock.E01 := by
  constructor
  · simpa [elapsed,halfTurnSlice] using div_pos Real.pi_pos (frequency_pos hb hℏ)
  · rw [timed_cons,timed_nil]
    exact (positive_duration_hamiltonian hb hℏ).2
def freeLiftKraus (θ : ℝ) (s : Schedule) := FiniteNontracialEnvironmentLift.liftKraus (freeKraus θ s)
theorem free_lift_normalized (θ : ℝ) (s : Schedule) : IsKrausChannel (freeLiftKraus θ s) :=
  FiniteNontracialEnvironmentLift.normalized (free_normalized θ s)
theorem free_lift_product (θ : ℝ) (s : Schedule) (A B : MatQ) :
    krausMap (freeLiftKraus θ s) (A ⊗ₖ B)=A ⊗ₖ freeState θ s B :=
  FiniteNontracialEnvironmentLift.product_action _ A B
theorem free_lift_spectator (θ : ℝ) (s : Schedule) (X : FiniteNontracialEnvironmentLift.MatJoint) :
    FiniteNontracialEnvironmentLift.ptrace2 (krausMap (freeLiftKraus θ s) X)=
      FiniteNontracialEnvironmentLift.ptrace2 X :=
  FiniteNontracialEnvironmentLift.spectator (free_normalized θ s) X
theorem free_lift_dual (θ : ℝ) (s : Schedule) (A X : FiniteNontracialEnvironmentLift.MatJoint) :
    (A*krausMap (freeLiftKraus θ s) X).trace=
      (Channel.heisenberg (freeLiftKraus θ s) A*X).trace := by
  rw [Matrix.trace_mul_comm,← Channel.trace_duality,Matrix.trace_mul_comm]


/-- The reference logarithm itself, with its independent faithfulness proof. -/
theorem rhoN_log :
    matrixLog rhoN_posDef.posSemidef.isHermitian =
      Matrix.diagonal (![Real.log (16/25),Real.log (9/25)] : Q → ℂ) := by
  have hc {A B : MatQ} (hA : A.IsHermitian) (hB : B.IsHermitian) (he : A=B) :
      matrixLog hA=matrixLog hB := by subst B; rfl
  rw [← hc _ _ (gibbs_thermal (by norm_num : (0:ℝ)<1))]
  exact log_reference_diagonal 1 (by norm_num)
theorem V_R_commute (θ : ℝ) : Commute (V θ) R := by
  change V θ*R=R*V θ
  rw [V_diagonal]
  ext i j;fin_cases i <;> fin_cases j <;> simp [R,Matrix.mul_apply,Fin.sum_univ_two,mul_comm]
theorem V_rho_commute (θ : ℝ) : Commute (V θ) rhoN := by
  change V θ*rhoN=rhoN*V θ
  rw [V_diagonal]
  ext i j;fin_cases i <;> fin_cases j <;> simp [rhoN,Matrix.mul_apply,Fin.sum_univ_two,mul_comm]
def jointPhase (θ : ℝ) (X : FiniteNontracialEnvironmentLift.MatJoint) :=
  FiniteNontracialEnvironmentLift.liftState (phaseKraus θ) X
theorem jointPhase_inverse (θ : ℝ) (X : FiniteNontracialEnvironmentLift.MatJoint) :
    jointPhase (-θ) (jointPhase θ X)=X := by
  ext ⟨s,e⟩ ⟨t,f⟩
  have h := FiniteNontracialEnvironmentLift.liftState_block (phaseKraus (-θ)) (jointPhase θ X) s t
  rw [phase_action] at h
  have hj := FiniteNontracialEnvironmentLift.liftState_block (phaseKraus θ) X s t
  rw [phase_action] at hj
  change FiniteNontracialEnvironmentLift.block (jointPhase θ X) s t = _ at hj
  rw [hj,C_inverse] at h
  exact congrFun (congrFun h e) f
theorem jointPhase_traceDist (θ : ℝ) {X Y : FiniteNontracialEnvironmentLift.MatJoint}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    traceDist (jointPhase θ X) (jointPhase θ Y)=traceDist X Y := by
  apply le_antisymm
  · exact traceDist_krausMap_le (FiniteNontracialEnvironmentLift.normalized (phase_normalized θ)) hX hY
  · have hx := FiniteNontracialEnvironmentLift.liftState_isHermitian (phaseKraus θ) hX
    have hy := FiniteNontracialEnvironmentLift.liftState_isHermitian (phaseKraus θ) hY
    have h := traceDist_krausMap_le (FiniteNontracialEnvironmentLift.normalized (phase_normalized (-θ))) hx hy
    change traceDist (jointPhase (-θ) (jointPhase θ X)) (jointPhase (-θ) (jointPhase θ Y)) ≤ _ at h
    rw [jointPhase_inverse,jointPhase_inverse] at h
    exact h
theorem jointPhase_density_distance (θ : ℝ) {X Y : FiniteNontracialEnvironmentLift.MatJoint}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    traceDist (jointPhase θ X) (jointPhase θ Y)=traceDist X Y :=
  jointPhase_traceDist θ hX.1.isHermitian hY.1.isHermitian
theorem free_lift_density (θ : ℝ) (s : Schedule) {X : FiniteNontracialEnvironmentLift.MatJoint}
    (hX : IsDensityOperator X) : IsDensityOperator (krausMap (freeLiftKraus θ s) X) :=
  krausMap_isDensityOperator (free_lift_normalized θ s) hX
theorem free_lift_hermitian (θ : ℝ) (s : Schedule) {X : FiniteNontracialEnvironmentLift.MatJoint}
    (hX : X.IsHermitian) : (krausMap (freeLiftKraus θ s) X).IsHermitian :=
  krausMap_isHermitian _ hX
theorem free_lift_observable_product (θ : ℝ) (s : Schedule) (A B : MatQ) :
    Channel.heisenberg (freeLiftKraus θ s) (A ⊗ₖ B)=A ⊗ₖ freeObservable θ s B :=
  FiniteNontracialEnvironmentLift.observable_product_action _ A B

end SKEFTHawking.QuantumNetwork.FiniteNontracialThermalPhase
