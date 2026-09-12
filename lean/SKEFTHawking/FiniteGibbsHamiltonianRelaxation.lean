import SKEFTHawking.FiniteGibbsBlockRelaxation
import SKEFTHawking.QuantumNetwork.FiniteGibbsClock

/-! Actual diagonal Hamiltonian dynamics combined with finite Gibbs relaxation.
State and observable phases have opposite signs, with hbar = 1. The finite
Gibbs state is faithful. Positive reset gives convergence; zero reset can retain
undamped within-block rotation. Hamiltonian evolution is not asserted to be a
positive or self-adjoint operator on the reconstructed Hilbert space. Stationary
operators and fixed points at resonant individual times must not be conflated.
No bath derivation, noncommuting Hamiltonian, or continuum claim is made. -/
noncomputable section
open Matrix Filter
open scoped ComplexOrder InnerProductSpace Topology
namespace SKEFTHawking.FinitePositiveKernel.GibbsHamiltonianRelaxation
open QuantumNetwork OpenSystems GibbsObservable DiagonalLindblad
variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

/-- The actual diagonal Hamiltonian commutator. -/
def ham (E : n → ℝ) := lindbladHamPart (density E)

theorem ham_entry (E : n → ℝ) (X : Matrix n n ℂ) (i j : n) :
    ham E X i j = (-Complex.I * ((E i : ℂ)-E j)) * X i j := by
  simp [ham, lindbladHamPart_apply, density, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem ham_trace (E : n → ℝ) (X : Matrix n n ℂ) : (ham E X).trace=0 := by
  simp [Matrix.trace, ham_entry]

theorem ham_density (E w : n → ℝ) : ham E (density w)=0 := by
  ext i j
  by_cases h : i=j <;> simp [ham_entry, density, h]

theorem ham_block (E : n → ℝ) (ell : κ → n → ℝ) (X : Matrix n n ℂ) :
    ham E (blockExpectation ell X)=blockExpectation ell (ham E X) := by
  ext i j
  by_cases h : rate ell i j=0 <;> simp [ham_entry, blockExpectation, h]

theorem generator_state (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (hn : ∑ i,w i=1) (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (X : Matrix n n ℂ) :
    lindbladGenerator (density E) (GibbsBlockRelaxation.jumps ell w γ η) X =
      ham E X + (γ:ℂ) • (X.trace • density w-X) + (η:ℂ) • (blockExpectation ell X-X) := by
  have h : lindbladGenerator (density E) (GibbsBlockRelaxation.jumps ell w γ η) X =
      ham E X + lindbladGenerator 0 (GibbsBlockRelaxation.jumps ell w γ η) X := by
    simp only [lindbladGenerator, LinearMap.add_apply, ham, lindbladHamPart_apply, zero_mul, mul_zero, sub_self, smul_zero, zero_add, add_assoc]
  rw [h, GibbsBlockRelaxation.generator_state ell w hw hn γ η hγ hη]
  module

theorem generator_commute (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (hn : ∑ i,w i=1) (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    Commute (ham E) (lindbladGenerator 0 (GibbsBlockRelaxation.jumps ell w γ η)) := by
  ext X i j
  simp only [Module.End.mul_apply, GibbsBlockRelaxation.generator_state ell w hw hn γ η hγ hη,
    map_add, map_sub, map_smul, ham_density, ham_trace, ham_block, smul_zero, zero_smul]

/-- Observable rotation, using the existing Gibbs Heisenberg clock with hbar = 1. -/
def rotation (E : n → ℝ) (t : ℝ) (X : Matrix n n ℂ) :=
  FiniteGibbsClock.heisenberg (density E) 1 t X

theorem rotation_entry (E : n → ℝ) (t : ℝ) (X : Matrix n n ℂ) (i j : n) :
    rotation E t X i j = Complex.exp (Complex.I * t * ((E i : ℂ)-E j)) * X i j := by
  simpa [rotation, FiniteGibbsClock.heisenberg, density] using
    FiniteGibbsClock.diagonal_conjugate_entry (fun i => (E i : ℂ)) (Complex.I*t) X i j

theorem rotation_diagonal (E : n → ℝ) (t : ℝ) (d : n → ℂ) :
    rotation E t (diagonal d)=diagonal d := by
  ext i j
  by_cases h : i=j <;> simp [rotation_entry, h]

theorem rotation_trace (E : n → ℝ) (t : ℝ) (X : Matrix n n ℂ) :
    (rotation E t X).trace=X.trace := by simp [Matrix.trace, rotation_entry]

theorem rotation_block (E : n → ℝ) (ell : κ → n → ℝ) (t : ℝ) (X : Matrix n n ℂ) :
    rotation E t (blockExpectation ell X)=blockExpectation ell (rotation E t X) := by
  ext i j
  by_cases h : rate ell i j=0 <;> simp [rotation_entry, blockExpectation, h]

theorem ham_matrix (E : n → ℝ) :
    LinearMap.toMatrix (Matrix.stdBasis ℂ n n) (Matrix.stdBasis ℂ n n) (ham E) =
      diagonal (fun p : n × n => -Complex.I*((E p.1:ℂ)-E p.2)) := by
  ext p q
  rw [LinearMap.toMatrix_apply]
  change ham E (Matrix.stdBasis ℂ n n q) p.1 p.2 = _
  rw [ham_entry]
  simp [Matrix.stdBasis, Matrix.diagonal_apply, Pi.single_apply, Prod.ext_iff, ite_and, ite_apply]

theorem ham_exp (E : n → ℝ) (t : ℝ) (X : Matrix n n ℂ) :
    Matrix.toLin (Matrix.stdBasis ℂ n n) (Matrix.stdBasis ℂ n n)
      (NormedSpace.exp ((t:ℂ) • LinearMap.toMatrix (Matrix.stdBasis ℂ n n)
        (Matrix.stdBasis ℂ n n) (ham E))) X = rotation E (-t) X := by
  ext i j
  rw [ham_matrix, ← Matrix.diagonal_smul, Matrix.exp_diagonal, toLin_diagonal_entry, rotation_entry]
  simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_neg]
  congr 2
  ring

omit [Fintype κ] in
theorem exp_sum_action (A D : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (hc : Commute A D)
    (t : ℝ) (X : Matrix n n ℂ) :
    Matrix.toLin (Matrix.stdBasis ℂ n n) (Matrix.stdBasis ℂ n n)
      (NormedSpace.exp ((t:ℂ) • LinearMap.toMatrix (Matrix.stdBasis ℂ n n) (Matrix.stdBasis ℂ n n) (A+D))) X =
    Matrix.toLin (Matrix.stdBasis ℂ n n) (Matrix.stdBasis ℂ n n)
      (NormedSpace.exp ((t:ℂ) • LinearMap.toMatrix (Matrix.stdBasis ℂ n n) (Matrix.stdBasis ℂ n n) A))
    (Matrix.toLin (Matrix.stdBasis ℂ n n) (Matrix.stdBasis ℂ n n)
      (NormedSpace.exp ((t:ℂ) • LinearMap.toMatrix (Matrix.stdBasis ℂ n n) (Matrix.stdBasis ℂ n n) D)) X) := by
  let b := Matrix.stdBasis ℂ n n
  have hm : Commute (LinearMap.toMatrix b b A) (LinearMap.toMatrix b b D) := by
    change _*_=_*_
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, hc.eq]
  rw [map_add, smul_add, Matrix.exp_add_of_commute _ _ ((hm.smul_left (t:ℂ)).smul_right (t:ℂ)),
    Matrix.toLin_mul b b b, LinearMap.comp_apply]

theorem propagator_state (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (hn : ∑ i,w i=1) (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (X : Matrix n n ℂ) :
    lindbladPropagatorAction (density E) (GibbsBlockRelaxation.jumps ell w γ η) t X =
      rotation E (-t) (lindbladPropagatorAction 0 (GibbsBlockRelaxation.jumps ell w γ η) t X) := by
  have hg : lindbladGenerator (density E) (GibbsBlockRelaxation.jumps ell w γ η)=
      ham E+lindbladGenerator 0 (GibbsBlockRelaxation.jumps ell w γ η) := by
    ext Y i j
    simp only [lindbladGenerator, LinearMap.add_apply, ham, lindbladHamPart_apply,
      zero_mul, mul_zero, sub_self, smul_zero, zero_add, add_assoc]
  unfold lindbladPropagatorAction lindbladPropagator lindbladLiouvillian
  rw [hg, exp_sum_action _ _ (generator_commute E ell w hw hn γ η hγ hη), ham_exp]

/-- The state unitary uses the negative Hamiltonian phase. -/
def unitary (E : n → ℝ) (t : ℝ) := FiniteGibbsClock.expCoeff (density E) (-Complex.I*t)

omit [Fintype n] in
theorem density_hermitian (E : n → ℝ) : (density E).IsHermitian := by
  rw [density, Matrix.isHermitian_diagonal_iff]
  intro i
  simp [IsSelfAdjoint]

theorem unitary_adjoint (E : n → ℝ) (t : ℝ) : (unitary E t)ᴴ=unitary E (-t) := by
  rw [unitary, FiniteGibbsClock.expCoeff_adjoint (density_hermitian E)]
  simp [unitary]

theorem unitary_cancel (E : n → ℝ) (t : ℝ) : unitary E t * unitary E (-t)=1 := by
  unfold unitary
  simpa using FiniteGibbsClock.expCoeff_cancel (density E) (-Complex.I*t)

theorem rotation_sandwich (E : n → ℝ) (t : ℝ) (X : Matrix n n ℂ) :
    rotation E (-t) X=unitary E t*X*(unitary E t)ᴴ := by
  rw [unitary_adjoint]
  simp [rotation, FiniteGibbsClock.heisenberg, FiniteGibbsClock.conjugate, unitary]

theorem rotation_add (E : n → ℝ) (t : ℝ) (X Y : Matrix n n ℂ) :
    rotation E t (X+Y)=rotation E t X+rotation E t Y := FiniteGibbsClock.heisenberg_add _ _ _ _ _

theorem rotation_smul (E : n → ℝ) (t : ℝ) (c : ℂ) (X : Matrix n n ℂ) :
    rotation E t (c • X)=c • rotation E t X := FiniteGibbsClock.heisenberg_smul _ _ _ _ _

theorem rotation_weighted_trace (E w : n → ℝ) (t : ℝ) (X : Matrix n n ℂ) :
    (density w * rotation E t X).trace=(density w*X).trace := by
  simp [Matrix.trace, density, Matrix.diagonal_mul, rotation_entry]

/-- Multiply the accepted dissipative Kraus operators by the actual state unitary. -/
def timeKraus (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ) (γ η t : ℝ) :=
  fun k => unitary E t * GibbsBlockRelaxation.timeKraus ell w γ η t k

omit [Fintype κ] in
theorem time_state (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ) (γ η t : ℝ) (X : Matrix n n ℂ) :
    krausMap (timeKraus E ell w γ η t) X =
      rotation E (-t) (krausMap (GibbsBlockRelaxation.timeKraus ell w γ η t) X) := by
  rw [rotation_sandwich]
  simp [krausMap, timeKraus, Matrix.conjTranspose_mul, Matrix.sum_mul, Matrix.mul_sum, mul_assoc]

theorem time_normalized (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (hn : ∑ i,w i=1) (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    IsKrausChannel (timeKraus E ell w γ η t) := by
  unfold IsKrausChannel timeKraus
  simp only [Matrix.conjTranspose_mul, mul_assoc]
  have hc : (unitary E t)ᴴ*unitary E t=1 := by
    rw [unitary_adjoint]
    simpa using unitary_cancel E (-t)
  simp only [← mul_assoc (unitary E t)ᴴ, hc, one_mul]
  exact GibbsBlockRelaxation.time_normalized ell w hw hn γ η t hγ hη ht

theorem time_stationary (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (hn : ∑ i,w i=1) (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    krausMap (timeKraus E ell w γ η t) (density w)=density w := by
  rw [time_state, GibbsBlockRelaxation.time_stationary ell w hw hn γ η t hγ hη ht]
  exact rotation_diagonal E (-t) _

theorem time_state_eq_propagator (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (hn : ∑ i,w i=1) (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (X : Matrix n n ℂ) : krausMap (timeKraus E ell w γ η t) X=
      lindbladPropagatorAction (density E) (GibbsBlockRelaxation.jumps ell w γ η) t X := by
  rw [time_state, GibbsBlockRelaxation.time_state_eq_propagator ell w hw hn γ η t hγ hη ht,
    propagator_state E ell w hw hn γ η t hγ hη]

omit [Fintype κ] in
theorem time_observable (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ) (γ η t : ℝ) (X : Matrix n n ℂ) :
    Channel.heisenberg (timeKraus E ell w γ η t) X =
      Channel.heisenberg (GibbsBlockRelaxation.timeKraus ell w γ η t) (rotation E t X) := by
  have hs := rotation_sandwich E (-t) X
  simp only [neg_neg, unitary_adjoint] at hs
  rw [hs]
  simp [Channel.heisenberg, timeKraus, Matrix.conjTranspose_mul, unitary_adjoint, mul_assoc]

theorem observable_commute (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (X : Matrix n n ℂ) :
    Channel.heisenberg (GibbsBlockRelaxation.timeKraus ell w γ η t) (rotation E t X) =
      rotation E t (Channel.heisenberg (GibbsBlockRelaxation.timeKraus ell w γ η t) X) := by
  obtain ⟨ha,hb,hc⟩ := GibbsBlockRelaxation.time_coefficients_nonneg γ η t hγ hη ht
  simp only [GibbsBlockRelaxation.timeKraus, GibbsBlockRelaxation.mixture_observable ell w hw _ _ _ ha hb hc,
    rotation_add, rotation_smul, rotation_weighted_trace, rotation_block]
  rw [show rotation E t (1 : Matrix n n ℂ)=1 from FiniteGibbsClock.heisenberg_one _ _ _]

theorem trace_duality (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (hn : ∑ i,w i=1) (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (S X : Matrix n n ℂ) :
    (S*Channel.heisenberg (timeKraus E ell w γ η t) X).trace =
      (lindbladPropagatorAction (density E) (GibbsBlockRelaxation.jumps ell w γ η) t S*X).trace := by
  rw [Channel.trace_duality, time_state_eq_propagator E ell w hw hn γ η t hγ hη ht]

omit [Fintype n] [DecidableEq n] in
theorem phase_norm (E : n → ℝ) (t : ℝ) (i j : n) :
    ‖Complex.exp (Complex.I*t*((E i:ℂ)-E j))‖=1 := by
  rw [Complex.norm_exp]
  simp

/-- The norm-preserving descent of the actual Heisenberg rotation. -/
def quotientRotation (E w : n → ℝ) (hw : ∀ i,0 < w i) (t : ℝ) :
    WeightedSpace w hw →L[ℂ] WeightedSpace w hw :=
  quotientEntry w hw (fun p => Complex.exp (Complex.I*t*((E p.1:ℂ)-E p.2)))
    (fun p => (phase_norm E t p.1 p.2).le)

theorem quotientRotation_observable (E w : n → ℝ) (hw : ∀ i,0 < w i) (t : ℝ) (X : Matrix n n ℂ) :
    quotientRotation E w hw t (observable (density_posDef w hw).posSemidef X) =
      observable (density_posDef w hw).posSemidef (rotation E t X) := by
  rw [quotientRotation, quotientEntry_observable]
  congr 1
  ext i j
  exact (rotation_entry E t X i j).symm

theorem quotientRotation_norm (E w : n → ℝ) (hw : ∀ i,0 < w i) (t : ℝ) (z : WeightedSpace w hw) :
    ‖quotientRotation E w hw t z‖=‖z‖ := by
  obtain ⟨X,rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [quotientRotation_observable, observable_norm_sq w hw, observable_norm_sq w hw]
  simp [rotation_entry, phase_norm]

theorem quotientRotation_scalar (E w : n → ℝ) (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1)
    (t : ℝ) (z : WeightedSpace w hw) :
    quotientRotation E w hw t (GibbsReset.scalarProjection w hw hn z)=GibbsReset.scalarProjection w hw hn z := by
  obtain ⟨X,rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [GibbsReset.scalarProjection_observable, map_smul, quotientRotation_observable]
  rw [show rotation E t (1 : Matrix n n ℂ)=1 from FiniteGibbsClock.heisenberg_one _ _ _]

theorem scalar_quotientRotation (E w : n → ℝ) (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1)
    (t : ℝ) (z : WeightedSpace w hw) :
    GibbsReset.scalarProjection w hw hn (quotientRotation E w hw t z)=GibbsReset.scalarProjection w hw hn z := by
  obtain ⟨X,rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [quotientRotation_observable, GibbsReset.scalarProjection_observable,
    GibbsReset.scalarProjection_observable, rotation_weighted_trace]

theorem quotientRotation_block (E w : n → ℝ) (hw : ∀ i,0 < w i) (ell : κ → n → ℝ)
    (t : ℝ) (z : WeightedSpace w hw) :
    quotientRotation E w hw t (projection w hw ell z)=projection w hw ell (quotientRotation E w hw t z) := by
  obtain ⟨X,rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [projection_observable, quotientRotation_observable, quotientRotation_observable,
    projection_observable, rotation_block]

section Quotient
variable (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1)
local notation "Q" => GibbsReset.scalarProjection w hw hn
local notation "B" => projection w hw ell

def evolution (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    WeightedSpace w hw →L[ℂ] WeightedSpace w hw :=
  Channel.quotientChannel (density_posDef w hw).posSemidef (timeKraus E ell w γ η t)
    (time_normalized E ell w (fun i => (hw i).le) hn γ η t hγ hη ht)
    (time_stationary E ell w (fun i => (hw i).le) hn γ η t hγ hη ht)

theorem evolution_factor (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    evolution E ell w hw hn γ η t hγ hη ht z =
      quotientRotation E w hw t (GibbsBlockRelaxation.evolution ell w hw hn γ η t hγ hη ht z) := by
  obtain ⟨X,rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [evolution, Channel.quotientChannel_observable, GibbsBlockRelaxation.evolution,
    Channel.quotientChannel_observable, quotientRotation_observable, time_observable,
    observable_commute E ell w (fun i => (hw i).le) γ η t hγ hη ht]

theorem evolution_error_norm (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    ‖evolution E ell w hw hn γ η t hγ hη ht z-Q z‖ =
      ‖GibbsBlockRelaxation.evolution ell w hw hn γ η t hγ hη ht z-Q z‖ := by
  rw [evolution_factor]
  calc
    _ = ‖quotientRotation E w hw t (GibbsBlockRelaxation.evolution ell w hw hn γ η t hγ hη ht z-Q z)‖ := by
      rw [map_sub, quotientRotation_scalar]
    _ = _ := quotientRotation_norm E w hw t _

theorem evolution_two_rate_error (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    ‖evolution E ell w hw hn γ η t hγ hη ht z-Q z‖^2 =
      Real.exp (-2*γ*t)*‖B z-Q z‖^2 + Real.exp (-2*(γ+η)*t)*‖z-B z‖^2 := by
  rw [evolution_error_norm]
  exact GibbsBlockRelaxation.evolution_two_rate_error ell w hw hn γ η t hγ hη ht z

theorem evolution_zero_rates (t : ℝ) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    evolution E ell w hw hn 0 0 t (by norm_num) (by norm_num) ht z=quotientRotation E w hw t z := by
  rw [evolution_factor, GibbsBlockRelaxation.evolution_zero_rates]
  rfl

theorem evolution_tendsto (γ η : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (z : WeightedSpace w hw) :
    Tendsto (fun t : NNReal => evolution E ell w hw hn γ η t hγ.le hη t.coe_nonneg z) atTop (𝓝 (Q z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [evolution_error_norm]
  exact (tendsto_iff_norm_sub_tendsto_zero).mp
    (GibbsBlockRelaxation.evolution_tendsto ell w hw hn γ η hγ hη z)

end Quotient

theorem generator_stationary (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (hn : ∑ i,w i=1) (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    lindbladGenerator (density E) (GibbsBlockRelaxation.jumps ell w γ η) (density w)=0 := by
  rw [generator_state E ell w hw hn γ η hγ hη, ham_density,
    GibbsReset.density_trace, hn, Complex.ofReal_one, one_smul, GibbsBlockRelaxation.block_density]
  simp

theorem stationary_trace_one_iff (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (hn : ∑ i,w i=1) (γ η : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η)
    (X : Matrix n n ℂ) (htr : X.trace=1) :
    lindbladGenerator (density E) (GibbsBlockRelaxation.jumps ell w γ η) X=0 ↔ X=density w := by
  constructor
  · intro h
    rw [generator_state E ell w hw hn γ η hγ.le hη, htr, one_smul] at h
    ext i j
    have hh := congrFun (congrFun h i) j
    by_cases hij : i=j
    · subst j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply,
        ham_entry, sub_self, mul_zero, zero_mul, zero_add, blockExpectation, rate_self, ite_true,
        smul_eq_mul] at hh
      have hg : (γ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
      have he : density w i i-X i i=0 := (mul_eq_zero.mp (by simpa using hh)).resolve_left hg
      exact (sub_eq_zero.mp he).symm
    · have hd : density w i j=0 := by simp [density, hij]
      by_cases hr : rate ell i j=0
      · have he : ((-γ:ℝ):ℂ)-Complex.I*((E i:ℂ)-E j) ≠ 0 := by
          intro hc
          have hh := congrArg Complex.re hc
          simp at hh
          linarith
        have hx : (((-γ:ℝ):ℂ)-Complex.I*((E i:ℂ)-E j))*X i j=0 := by
          simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply,
            ham_entry, blockExpectation, hr, ite_true, hd, smul_eq_mul] at hh
          push_cast
          linear_combination hh
        rw [hd]
        exact (mul_eq_zero.mp hx).resolve_left he
      · have he : ((-(γ+η):ℝ):ℂ)-Complex.I*((E i:ℂ)-E j) ≠ 0 := by
          intro hc
          have hh := congrArg Complex.re hc
          simp at hh
          linarith
        have hx : (((-(γ+η):ℝ):ℂ)-Complex.I*((E i:ℂ)-E j))*X i j=0 := by
          simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply,
            ham_entry, blockExpectation, hr, ite_false, hd, smul_eq_mul] at hh
          push_cast
          linear_combination hh
        rw [hd]
        exact (mul_eq_zero.mp hx).resolve_left he
  · rintro rfl
    exact generator_stationary E ell w hw hn γ η hγ.le hη

/-- The invariant density is the existing matrix Gibbs state, not a separately assumed state. -/
theorem gibbs_stationary [Nonempty n] (E : n → ℝ) (ell : κ → n → ℝ) (β γ η : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    lindbladGenerator (density E) (GibbsBlockRelaxation.jumps ell (GibbsReset.gibbsWeights E β) γ η)
      (FiniteGibbsClock.gibbs (density E) β)=0 := by
  rw [← GibbsReset.density_gibbsWeights]
  exact generator_stationary E ell _ (fun i => (GibbsReset.gibbsWeights_pos E β i).le)
    (GibbsReset.gibbsWeights_normalized E β) γ η hγ hη

/-- Removing both dissipators recovers the actual Gibbs Heisenberg clock. -/
theorem zero_rates_clock (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (t : ℝ) (ht : 0 ≤ t) (X : Matrix n n ℂ) :
    Channel.heisenberg (timeKraus E ell w 0 0 t) X=FiniteGibbsClock.heisenberg (density E) 1 t X := by
  rw [time_observable]
  obtain ⟨ha,hb,hc⟩ := GibbsBlockRelaxation.time_coefficients_nonneg 0 0 t (by norm_num) (by norm_num) ht
  rw [GibbsBlockRelaxation.timeKraus, GibbsBlockRelaxation.mixture_observable ell w hw _ _ _ ha hb hc]
  simp [GibbsBlockRelaxation.slow, GibbsBlockRelaxation.fast, rotation]

theorem propagator_diagonal (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (hn : ∑ i,w i=1) (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (d : n → ℂ) :
    lindbladPropagatorAction (density E) (GibbsBlockRelaxation.jumps ell w γ η) t (diagonal d)=
      lindbladPropagatorAction 0 (GibbsReset.jumps w γ) t (diagonal d) := by
  rw [propagator_state E ell w hw hn γ η t hγ hη,
    GibbsBlockRelaxation.propagator_diagonal ell w hw hn γ η t hγ hη,
    GibbsReset.propagator_state w hw hn γ hγ]
  ext i j
  rw [rotation_entry]
  by_cases h : i=j <;> simp [density, h]

omit [Fintype κ] in
theorem rotation_single (E : n → ℝ) (t : ℝ) (i j : n) :
    rotation E t (Matrix.single i j 1)=Complex.exp (Complex.I*t*((E i:ℂ)-E j)) • Matrix.single i j 1 := by
  ext k l
  by_cases hk : i=k <;> by_cases hl : j=l <;> simp [rotation_entry, Matrix.single, hk, hl]

omit [Fintype κ] in
theorem single_scalar_zero (w : n → ℝ) (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1) (i j : n) (hij : i ≠ j) :
    GibbsReset.scalarProjection w hw hn (observable (density_posDef w hw).posSemidef (Matrix.single i j 1))=0 := by
  rw [GibbsReset.scalarProjection_observable, Matrix.trace_mul_single]
  rw [show density w j i=0 by simp [density, hij.symm]]
  simp

omit [Fintype n] in
theorem block_single (ell : κ → n → ℝ) (i j : n) :
    blockExpectation ell (Matrix.single i j 1)=if rate ell i j=0 then Matrix.single i j 1 else 0 := by
  by_cases hr : rate ell i j=0
  · rw [if_pos hr]
    ext k l
    by_cases hk : i=k <;> by_cases hl : j=l <;> simp_all [blockExpectation, Matrix.single]
  · rw [if_neg hr]
    ext k l
    by_cases hk : i=k <;> by_cases hl : j=l <;> simp_all [blockExpectation, Matrix.single]

theorem evolution_coherence (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1) (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (i j : n) (hij : i ≠ j) :
    evolution E ell w hw hn γ η t hγ hη ht (observable (density_posDef w hw).posSemidef (Matrix.single i j 1))=
      (Complex.exp (Complex.I*t*((E i:ℂ)-E j)) *
        (Real.exp (-(γ+(if rate ell i j=0 then 0 else η))*t):ℂ)) •
      observable (density_posDef w hw).posSemidef (Matrix.single i j 1) := by
  rw [evolution_factor, GibbsBlockRelaxation.evolution_apply, single_scalar_zero w hw hn i j hij,
    projection_observable, block_single]
  by_cases hr : rate ell i j=0
  · simp only [hr, ite_true, sub_zero, sub_self, smul_zero, add_zero, zero_add]
    rw [map_smul, quotientRotation_observable, rotation_single, observable_smul, smul_smul, mul_comm]
    rfl
  · simp only [hr, ite_false, sub_zero]
    rw [show observable (density_posDef w hw).posSemidef (0 : Matrix n n ℂ)=0 from map_zero (observableLinear (density_posDef w hw).posSemidef)]
    simp only [sub_zero, smul_zero, zero_add]
    rw [map_smul, quotientRotation_observable, rotation_single, observable_smul, smul_smul, mul_comm]
    rfl

/-- Three distinct energies; the first two levels still share a noise signature. -/
def threeEnergies : Fin 3 → ℝ := fun i => i.val

def threeWeights (β : ℝ) := GibbsReset.gibbsWeights threeEnergies β

theorem threeWeights_pos (β : ℝ) (i : Fin 3) : 0 < threeWeights β i := GibbsReset.gibbsWeights_pos _ _ _

theorem threeWeights_normalized (β : ℝ) : ∑ i,threeWeights β i=1 := GibbsReset.gibbsWeights_normalized _ _

def threeCoherence (β : ℝ) (i j : Fin 3) : WeightedSpace (threeWeights β) (threeWeights_pos β) :=
  observable (density_posDef (threeWeights β) (threeWeights_pos β)).posSemidef (Matrix.single i j 1)

theorem threeCoherence_norm_pos (β : ℝ) (i j : Fin 3) : 0 < ‖threeCoherence β i j‖ := by
  apply norm_pos_iff.mpr
  exact observable_single_nonzero (threeWeights β) (threeWeights_pos β) i j

theorem three_within_phase (β γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    evolution threeEnergies duplicateJumps (threeWeights β) (threeWeights_pos β) (threeWeights_normalized β)
      γ η t hγ hη ht (threeCoherence β 0 1) =
      (Complex.exp (-Complex.I*t)*(Real.exp (-γ*t):ℂ)) • threeCoherence β 0 1 := by
  rw [threeCoherence, evolution_coherence _ _ _ _ _ γ η t hγ hη ht 0 1 (by decide)]
  norm_num [rate, duplicateJumps, threeEnergies, Fin.sum_univ_succ, Fin.ext_iff]

theorem three_cross_phase (β γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    evolution threeEnergies duplicateJumps (threeWeights β) (threeWeights_pos β) (threeWeights_normalized β)
      γ η t hγ hη ht (threeCoherence β 0 2) =
      (Complex.exp (-2*Complex.I*t)*(Real.exp (-(γ+η)*t):ℂ)) • threeCoherence β 0 2 := by
  rw [threeCoherence, evolution_coherence _ _ _ _ _ γ η t hγ hη ht 0 2 (by decide)]
  norm_num [rate, duplicateJumps, threeEnergies, Fin.sum_univ_succ, Fin.ext_iff]
  congr 3; ring

theorem three_within_norm (β γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    ‖evolution threeEnergies duplicateJumps (threeWeights β) (threeWeights_pos β) (threeWeights_normalized β)
      γ η t hγ hη ht (threeCoherence β 0 1)‖ = Real.exp (-γ*t)*‖threeCoherence β 0 1‖ := by
  rw [three_within_phase, norm_smul, norm_mul, Complex.norm_exp]
  simp [Complex.norm_exp]

theorem three_cross_norm (β γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    ‖evolution threeEnergies duplicateJumps (threeWeights β) (threeWeights_pos β) (threeWeights_normalized β)
      γ η t hγ hη ht (threeCoherence β 0 2)‖ = Real.exp (-(γ+η)*t)*‖threeCoherence β 0 2‖ := by
  rw [three_cross_phase, norm_smul, norm_mul, Complex.norm_exp]
  simp [Complex.norm_exp]

theorem three_zero_reset_norm (β η t : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    ‖evolution threeEnergies duplicateJumps (threeWeights β) (threeWeights_pos β) (threeWeights_normalized β)
      0 η t (by norm_num) hη ht (threeCoherence β 0 1)‖ = ‖threeCoherence β 0 1‖ := by
  rw [three_within_norm]
  simp

theorem three_population (β γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    lindbladPropagatorAction (density threeEnergies)
      (GibbsBlockRelaxation.jumps duplicateJumps (threeWeights β) γ η) t GibbsReset.concentrated 1 1 =
      ((1-Real.exp (-γ*t))*threeWeights β 1 : ℝ) := by
  rw [GibbsReset.concentrated, propagator_diagonal _ _ _ (fun i => (threeWeights_pos β i).le)
    (threeWeights_normalized β) γ η t hγ hη,
    GibbsReset.propagator_state _ (fun i => (threeWeights_pos β i).le) (threeWeights_normalized β) γ hγ]
  norm_num [Matrix.trace, Fin.sum_univ_succ, density]

theorem three_population_pos (β γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) :
    0 < (lindbladPropagatorAction (density threeEnergies)
      (GibbsBlockRelaxation.jumps duplicateJumps (threeWeights β) γ η) t GibbsReset.concentrated 1 1).re := by
  rw [three_population β γ η t hγ.le hη, Complex.ofReal_re]
  exact mul_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))) (threeWeights_pos β 1)

/-- Positive inverse temperature makes this actual Gibbs equilibrium nonuniform. -/
theorem threeWeights_nonuniform (β : ℝ) (hβ : 0 < β) : threeWeights β 1 < threeWeights β 0 := by
  unfold threeWeights GibbsReset.gibbsWeights
  apply (mul_lt_mul_iff_of_pos_left (inv_pos.mpr (FiniteGibbsClock.partition_pos (density_hermitian threeEnergies) β))).mpr
  apply Real.exp_lt_exp.mpr
  norm_num [threeEnergies]
  exact hβ

/-- The surviving within-block orbit is a genuine rotation. -/
theorem three_zero_reset_phase (β η t : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    evolution threeEnergies duplicateJumps (threeWeights β) (threeWeights_pos β) (threeWeights_normalized β)
      0 η t (by norm_num) hη ht (threeCoherence β 0 1)=Complex.exp (-Complex.I*t) • threeCoherence β 0 1 := by
  rw [three_within_phase]
  simp

theorem phase_full_period (k : ℕ) : Complex.exp (-Complex.I*(((k:ℝ)*(2*Real.pi):ℝ):ℂ))=1 := by
  have h : -Complex.I*((k:ℝ)*(2*Real.pi):ℝ)= -((k:ℂ)*(2*Real.pi*Complex.I)) := by push_cast; ring
  rw [h, Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I, inv_one]

theorem phase_half_period (k : ℕ) : Complex.exp (-Complex.I*(((k:ℝ)*(2*Real.pi)+Real.pi : ℝ):ℂ))= -1 := by
  have h : -Complex.I*((k:ℝ)*(2*Real.pi)+Real.pi : ℝ)=
      -Complex.I*((k:ℝ)*(2*Real.pi):ℝ) + -(Real.pi*Complex.I) := by push_cast; ring
  rw [h, Complex.exp_add, phase_full_period, one_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- Nonzero persistent rotation rules out every quotient-space limit at zero reset. -/
theorem three_zero_reset_not_tendsto (β η : ℝ) (hη : 0 ≤ η)
    (z : WeightedSpace (threeWeights β) (threeWeights_pos β)) :
    ¬ Tendsto (fun t : NNReal => evolution threeEnergies duplicateJumps (threeWeights β)
      (threeWeights_pos β) (threeWeights_normalized β) 0 η t (by norm_num) hη t.coe_nonneg
      (threeCoherence β 0 1)) atTop (𝓝 z) := by
  intro h
  let a : ℕ → NNReal := fun k => ⟨(k:ℝ)*(2*Real.pi), by positivity⟩
  let b : ℕ → NNReal := fun k => ⟨(k:ℝ)*(2*Real.pi)+Real.pi, by positivity⟩
  have ha : Tendsto a atTop atTop := NNReal.tendsto_coe_atTop.mp
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity : 0 < 2*Real.pi))
  have hb : Tendsto b atTop atTop := NNReal.tendsto_coe_atTop.mp
    (tendsto_atTop_add_const_right _ Real.pi (NNReal.tendsto_coe_atTop.mpr ha))
  have h₁ := h.comp ha
  have h₂ := h.comp hb
  simp only [Function.comp_def, three_zero_reset_phase] at h₁ h₂
  have hp : Tendsto (fun _ : ℕ => threeCoherence β 0 1) atTop (𝓝 z) := by
    change Tendsto (fun k : ℕ => Complex.exp (-Complex.I*(((k:ℝ)*(2*Real.pi):ℝ):ℂ)) • threeCoherence β 0 1) atTop (𝓝 z) at h₁
    simpa only [phase_full_period, one_smul] using h₁
  have hm : Tendsto (fun _ : ℕ => -threeCoherence β 0 1) atTop (𝓝 z) := by
    change Tendsto (fun k : ℕ => Complex.exp (-Complex.I*(((k:ℝ)*(2*Real.pi)+Real.pi:ℝ):ℂ)) • threeCoherence β 0 1) atTop (𝓝 z) at h₂
    simpa only [phase_half_period, neg_one_smul] using h₂
  have he : threeCoherence β 0 1 = -threeCoherence β 0 1 :=
    (tendsto_nhds_unique tendsto_const_nhds hp).trans (tendsto_nhds_unique tendsto_const_nhds hm).symm
  have hz : threeCoherence β 0 1=0 := by
    have hh : (2:ℂ) • threeCoherence β 0 1=0 := by
      calc
        _ = threeCoherence β 0 1+threeCoherence β 0 1 := by module
        _ = 0 := by nth_rw 1 [he]; exact neg_add_cancel _
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  exact (ne_of_gt (threeCoherence_norm_pos β 0 1)) (by rw [hz, norm_zero])

/-- The trace-dual observable channel uses positive Heisenberg time. -/
theorem time_observable_clock (E : n → ℝ) (ell : κ → n → ℝ) (w : n → ℝ)
    (hw : ∀ i,0 ≤ w i) (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (X : Matrix n n ℂ) :
    Channel.heisenberg (timeKraus E ell w γ η t) X =
      FiniteGibbsClock.heisenberg (density E) 1 t
        (Channel.heisenberg (GibbsBlockRelaxation.timeKraus ell w γ η t) X) := by
  rw [time_observable, observable_commute E ell w hw γ η t hγ hη ht]
  rfl

theorem gibbs_stationary_unique [Nonempty n] (E : n → ℝ) (ell : κ → n → ℝ) (β γ η : ℝ)
    (hγ : 0 < γ) (hη : 0 ≤ η) (X : Matrix n n ℂ) (htr : X.trace=1) :
    lindbladGenerator (density E) (GibbsBlockRelaxation.jumps ell (GibbsReset.gibbsWeights E β) γ η) X=0 ↔
      X=FiniteGibbsClock.gibbs (density E) β := by
  rw [← GibbsReset.density_gibbsWeights]
  exact stationary_trace_one_iff E ell _ (fun i => (GibbsReset.gibbsWeights_pos E β i).le)
    (GibbsReset.gibbsWeights_normalized E β) γ η hγ hη X htr

theorem three_within_strict_decay (β γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) :
    ‖evolution threeEnergies duplicateJumps (threeWeights β) (threeWeights_pos β) (threeWeights_normalized β)
      γ η t hγ.le hη ht.le (threeCoherence β 0 1)‖ < ‖threeCoherence β 0 1‖ := by
  rw [three_within_norm]
  exact mul_lt_of_lt_one_left (threeCoherence_norm_pos β 0 1) (Real.exp_lt_one_iff.mpr (by nlinarith))

theorem three_cross_strict_decay (β γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (hs : 0 < γ+η) (ht : 0 < t) :
    ‖evolution threeEnergies duplicateJumps (threeWeights β) (threeWeights_pos β) (threeWeights_normalized β)
      γ η t hγ hη ht.le (threeCoherence β 0 2)‖ < ‖threeCoherence β 0 2‖ := by
  rw [three_cross_norm]
  exact mul_lt_of_lt_one_left (threeCoherence_norm_pos β 0 2) (Real.exp_lt_one_iff.mpr (by nlinarith))

end SKEFTHawking.FinitePositiveKernel.GibbsHamiltonianRelaxation
