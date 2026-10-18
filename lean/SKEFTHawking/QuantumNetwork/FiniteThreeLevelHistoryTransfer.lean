import SKEFTHawking.QuantumNetwork.FiniteThreeLevelPositiveHistory
import SKEFTHawking.QuantumNetwork.FiniteThreeLevelEnvironmentLift
import SKEFTHawking.QuantumNetwork.DiamondBudget

/-!
# Thermal transfer of finite three-level histories

The original positive history quotient carries the observable dynamics. Coefficient
descent uses the inner frame and remains defined at complete central reset.
State phases and observable phases retain their opposite signs.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelHistoryTransfer
open Matrix FinitePositiveKernel GibbsObservable OpenSystems FiniteInterventionProcess
open FiniteThreeLevelPositiveHistory
open scoped BigOperators ComplexOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator

def mean (A : MatQ) : ℂ := (rhoN*A).trace
def scalarPart (A : MatQ) : MatQ := mean A • 1

def meanLinear : MatQ →ₗ[ℂ] ℂ where
  toFun := mean
  map_add' A B := by simp [mean,mul_add,Matrix.trace_add]
  map_smul' z A := by simp [mean]

def frameLinear : MatQ →ₗ[ℂ] (Outcome → ℂ) where
  toFun := frameCoeff
  map_add' A B := by
    ext o; fin_cases o <;> simp [frameCoeff,Matrix.cons_val] <;> ring
  map_smul' z A := by
    ext o; fin_cases o <;> simp [frameCoeff,Matrix.cons_val] <;> ring

def raw (r : ℝ) (O : MatQ →ₗ[ℂ] MatQ) : (HalfHistory → ℂ) →ₗ[ℂ] (HalfHistory → ℂ) where
  toFun F u := frameLinear (O (synthesisLinear 1 r F)) u.1
  map_add' F G := by ext u; simp
  map_smul' z F := by ext u; simp

theorem synthesis_from_raw (p r : ℝ) (F : HalfHistory → ℂ) :
    synthesis p r F = Psi p (synthesis 1 r F) := by
  simp only [synthesis,FiniteThreeLevelPositiveHistory.midpoint,Psi_one,Psi_sum,Psi_smul]

theorem raw_synthesis (p r : ℝ) (O : MatQ →ₗ[ℂ] MatQ)
    (hO : ∀ A, O (Psi p A) = Psi p (O A)) (F : HalfHistory → ℂ) :
    synthesis p r (raw r O F) = O (synthesis p r F) := by
  change synthesis p r (fun u => frameCoeff (O (synthesis 1 r F)) u.1) = _
  rw [synthesis_inner,frame_right_inverse,← hO,← synthesis_from_raw]

theorem mean_one : mean 1 = 1 := by simp [mean,rhoN_trace]
theorem mean_Psi (q : ℝ) (A : MatQ) : mean (Psi q A) = mean A := Psi_mean q A
theorem scalarPart_eq : scalarPart = Psi 0 := by funext A; simp [scalarPart,mean,Psi]
theorem scalarPart_twice (A : MatQ) : scalarPart (scalarPart A) = scalarPart A := by
  simp [scalarPart,mean,rhoN_trace]
theorem scalarPart_Psi (q : ℝ) (A : MatQ) : scalarPart (Psi q A) = Psi q (scalarPart A) := by
  rw [scalarPart_eq,Psi_comp,Psi_comp,zero_mul,mul_zero]
theorem scalarPart_symmetric (A B : MatQ) : form (scalarPart A) B = form A (scalarPart B) := by
  simpa only [scalarPart_eq] using (form_Psi_symmetric 0 A B).symm

/-- Observable diagonal conjugation; the state channel uses its inverse. -/
def rotate (ω : Q → ℝ) (t : ℝ) : MatQ →ₗ[ℂ] MatQ where
  toFun := GibbsHamiltonianRelaxation.rotation ω t
  map_add' := GibbsHamiltonianRelaxation.rotation_add ω t
  map_smul' := GibbsHamiltonianRelaxation.rotation_smul ω t

theorem rotate_entry (ω : Q → ℝ) (t : ℝ) (A : MatQ) (i j : Q) :
    rotate ω t A i j = Complex.exp (Complex.I*t*((ω i:ℂ)-ω j))*A i j :=
  GibbsHamiltonianRelaxation.rotation_entry ω t A i j
theorem rotate_one (ω : Q → ℝ) (t : ℝ) : rotate ω t 1 = 1 :=
  FiniteGibbsClock.heisenberg_one _ _ _
theorem rotate_diagonal (ω : Q → ℝ) (t : ℝ) (d : Q → ℂ) :
    rotate ω t (Matrix.diagonal d) = Matrix.diagonal d :=
  GibbsHamiltonianRelaxation.rotation_diagonal ω t d
theorem rotate_mean (ω : Q → ℝ) (t : ℝ) (A : MatQ) : mean (rotate ω t A) = mean A :=
  GibbsHamiltonianRelaxation.rotation_weighted_trace ω _ t A
theorem rotate_Psi (ω : Q → ℝ) (t q : ℝ) (A : MatQ) :
    rotate ω t (Psi q A) = Psi q (rotate ω t A) := by
  simp only [Psi,map_add,map_smul,rotate_one]
  have hm := rotate_mean ω t A
  unfold mean at hm
  rw [hm]
theorem rotate_mul (ω : Q → ℝ) (t : ℝ) (A B : MatQ) :
    rotate ω t (A*B) = rotate ω t A * rotate ω t B :=
  FiniteGibbsClock.heisenberg_mul _ _ _ _ _
theorem rotate_adjoint (ω : Q → ℝ) (t : ℝ) (A : MatQ) :
    rotate ω t Aᴴ = (rotate ω t A)ᴴ :=
  FiniteGibbsClock.heisenberg_star (GibbsHamiltonianRelaxation.density_hermitian ω) _ _ _
theorem rotate_trace (ω : Q → ℝ) (t : ℝ) (A : MatQ) :
    (rotate ω t A).trace = A.trace := GibbsHamiltonianRelaxation.rotation_trace ω t A
theorem rotate_zero (ω : Q → ℝ) (A : MatQ) : rotate ω 0 A = A :=
  FiniteGibbsClock.heisenberg_zero _ _ _
theorem rotate_group (ω : Q → ℝ) (s t : ℝ) (A : MatQ) :
    rotate ω s (rotate ω t A) = rotate ω (s+t) A :=
  (FiniteGibbsClock.heisenberg_group _ _ _ _ _).symm
theorem rotate_inverse (ω : Q → ℝ) (t : ℝ) (A : MatQ) :
    rotate ω (-t) (rotate ω t A) = A := by
  rw [rotate_group,neg_add_cancel,rotate_zero]
theorem rotate_form (ω : Q → ℝ) (t : ℝ) (A B : MatQ) :
    form (rotate ω t A) (rotate ω t B) = form A B := by
  have hR : rotate ω t R = R := rotate_diagonal ω t _
  unfold form
  rw [← rotate_adjoint,← hR,← rotate_mul,← rotate_mul,← rotate_mul,rotate_trace]
  rw [hR]


/-- The observable commutator has the positive Hamiltonian sign. -/
def hamLinear (ω : Q → ℝ) : MatQ →ₗ[ℂ] MatQ where
  toFun A i j := Complex.I*((ω i:ℂ)-ω j)*A i j
  map_add' A B := by ext i j; simp only [Matrix.add_apply]; ring
  map_smul' z A := by ext i j; simp only [Matrix.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

theorem ham_commutator (ω : Q → ℝ) (A : MatQ) :
    hamLinear ω A = Complex.I •
      (DiagonalLindblad.density ω*A-A*DiagonalLindblad.density ω) := by
  ext i j
  simp only [hamLinear,LinearMap.coe_mk,AddHom.coe_mk,DiagonalLindblad.density,
    Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring

theorem ham_mean (ω : Q → ℝ) (A : MatQ) : mean (hamLinear ω A) = 0 := by
  simp [mean,rhoN,FiniteThreeLevelThermalPhase.equilibrium,
    DiagonalLindblad.density,hamLinear,Matrix.trace,Matrix.diagonal_mul]

theorem ham_Psi (ω : Q → ℝ) (q : ℝ) (A : MatQ) :
    hamLinear ω (Psi q A) = Psi q (hamLinear ω A) := by
  have hm := ham_mean ω A
  unfold mean at hm
  unfold Psi
  rw [hm]
  ext i j
  by_cases hij : i=j
  · subst j; simp [hamLinear]
  · simp [hamLinear,hij]
    ring

def generatorMatrix (ω : Q → ℝ) (γ : ℝ) : MatQ →ₗ[ℂ] MatQ :=
  hamLinear ω + (γ:ℂ) • (PsiLinear 0-LinearMap.id)

theorem generatorMatrix_apply (ω : Q → ℝ) (γ : ℝ) (A : MatQ) :
    generatorMatrix ω γ A = hamLinear ω A + (γ:ℂ) • (scalarPart A-A) := by
  simp only [generatorMatrix,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,
    LinearMap.id_coe,id_eq,scalarPart_eq]
  rfl

theorem generatorMatrix_Psi (ω : Q → ℝ) (γ q : ℝ) (A : MatQ) :
    generatorMatrix ω γ (Psi q A) = Psi q (generatorMatrix ω γ A) := by
  rw [generatorMatrix_apply,generatorMatrix_apply,ham_Psi,scalarPart_Psi,Psi_add,Psi_smul]
  change _ = Psi q (hamLinear ω A)+(γ:ℂ) • PsiLinear q (scalarPart A-A)
  rw [map_sub]
  rfl

theorem observable_generator_actual (b ℏ γ : ℝ) (A : MatQ) :
    generatorMatrix (FiniteThreeLevelThermalPhase.frequencies b ℏ) γ A =
      Complex.I • (FiniteThreeLevelThermalPhase.scaledH b ℏ*A-
        A*FiniteThreeLevelThermalPhase.scaledH b ℏ) + (γ:ℂ) • (scalarPart A-A) := by
  rw [generatorMatrix_apply,ham_commutator]
  rfl

theorem generator_trace_duality (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (A X : MatQ) :
    (generatorMatrix (FiniteThreeLevelThermalPhase.frequencies b ℏ) γ A*X).trace =
      (A*OpenSystems.lindbladGenerator (FiniteThreeLevelThermalPhase.scaledH b ℏ)
        (FiniteThreeLevelThermalPhase.jumps γ) X).trace := by
  rw [observable_generator_actual,FiniteThreeLevelThermalPhase.actual_generator b ℏ γ hγ]
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,sub_mul,mul_sub,
    Matrix.trace_add,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul,
    scalarPart,mean,one_mul]
  have hc' := Matrix.trace_mul_cycle A X (FiniteThreeLevelThermalPhase.scaledH b ℏ)
  have hm : (A*FiniteThreeLevelThermalPhase.equilibrium).trace=(rhoN*A).trace :=
    Matrix.trace_mul_comm _ _
  rw [hm]
  rw [← hc',Matrix.mul_assoc A (FiniteThreeLevelThermalPhase.scaledH b ℏ) X]
  simp only [Matrix.mul_assoc]
  ring

def matrixOrbit (ω : Q → ℝ) (γ t : ℝ) (A : MatQ) : MatQ :=
  rotate ω t (Psi (Real.exp (-γ*t)) A)

theorem matrixOrbit_mean (ω : Q → ℝ) (γ t : ℝ) (A : MatQ) :
    mean (matrixOrbit ω γ t A) = mean A := by
  rw [matrixOrbit,rotate_mean,mean_Psi]

theorem matrixOrbit_entry (ω : Q → ℝ) (γ t : ℝ) (A : MatQ) (i j : Q) :
    matrixOrbit ω γ t A i j = scalarPart A i j +
      Complex.exp ((Complex.I*((ω i:ℂ)-ω j)-(γ:ℂ))*t)*(A i j-scalarPart A i j) := by
  rw [matrixOrbit,rotate_entry]
  have he : Complex.exp ((Complex.I*((ω i:ℂ)-ω j)-(γ:ℂ))*t) =
      Complex.exp (Complex.I*t*((ω i:ℂ)-ω j))*(Real.exp (-γ*t):ℂ) := by
    rw [show (Complex.I*((ω i:ℂ)-ω j)-(γ:ℂ))*t =
      Complex.I*t*((ω i:ℂ)-ω j)+((-γ*t:ℝ):ℂ) by push_cast; ring,
      Complex.exp_add,← Complex.ofReal_exp]
  rw [he]
  by_cases hij : i=j
  · subst j
    simp [Psi,scalarPart,mean]
    ring
  · simp [Psi,scalarPart,mean,hij]
    ring

theorem generatorMatrix_entry (ω : Q → ℝ) (γ : ℝ) (A : MatQ) (i j : Q) :
    generatorMatrix ω γ A i j =
      (Complex.I*((ω i:ℂ)-ω j)-(γ:ℂ))*(A i j-scalarPart A i j) := by
  rw [generatorMatrix_apply]
  by_cases hij : i=j
  · subst j; simp [hamLinear,scalarPart]; ring
  · simp [hamLinear,scalarPart,hij]; ring

theorem matrixOrbit_hasDerivAt (ω : Q → ℝ) (γ t : ℝ) (A : MatQ) :
    HasDerivAt (fun s : ℝ => matrixOrbit ω γ s A)
      (generatorMatrix ω γ (matrixOrbit ω γ t A)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hd := ((hasDerivAt_id t).ofReal_comp.const_mul
    (Complex.I*((ω i:ℂ)-ω j)-(γ:ℂ))).cexp.mul_const (A i j-scalarPart A i j)
  have he := (hasDerivAt_const t (scalarPart A i j)).add hd
  simp only [matrixOrbit_entry]
  convert he using 1
  · rfl
  · rw [generatorMatrix_entry]
    have hs : scalarPart (matrixOrbit ω γ t A)=scalarPart A := by
      simp only [scalarPart,matrixOrbit_mean]
    rw [hs,matrixOrbit_entry]
    simp only [id_eq,Complex.ofReal_one]
    ring


section Quotient
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
local notation "K₀" => FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1
local notation "hK₀" => FiniteThreeLevelPositiveHistory.kernel_posSemidef p r hp hp1 hr hr1
local notation "H" => Reconstructed p r hp hp1 hr hr1
local notation "coord" => coordinates p r hp hp1 hr hr1

theorem raw_null (O : MatQ →ₗ[ℂ] MatQ) (hO : ∀ A, O (Psi p A) = Psi p (O A)) :
    NullPreserving hK₀ (raw r O) := by
  intro F hF
  apply (mem_nullSpace_iff K₀ hK₀ _).mpr
  apply (mk_eq_zero_iff K₀ hK₀ _).mp
  rw [null_iff]
  erw [raw_synthesis p r O hO]
  have hz := (synthesis_null p r hp hp1 hr hr1) hF
  change synthesis p r F = 0 at hz
  rw [hz,map_zero]

/-- Derived null descent; continuity uses the finite-dimensional actual quotient. -/
def induced (O : MatQ →ₗ[ℂ] MatQ) (hO : ∀ A, O (Psi p A) = Psi p (O A)) :
    H →L[ℂ] H :=
  (descend hK₀ (raw r O) (raw_null p r hp hp1 hr hr1 O hO)).toContinuousLinearMap

theorem induced_mk (O : MatQ →ₗ[ℂ] MatQ) (hO : ∀ A, O (Psi p A) = Psi p (O A))
    (F : HalfHistory → ℂ) :
    induced p r hp hp1 hr hr1 O hO (mk K₀ hK₀ F) = mk K₀ hK₀ (raw r O F) :=
  descend_mk _ _ _ _

theorem induced_coordinates (O : MatQ →ₗ[ℂ] MatQ) (hO : ∀ A, O (Psi p A) = Psi p (O A))
    (z : H) : coord (induced p r hp hp1 hr hr1 O hO z) = O (coord z) := by
  obtain ⟨F,rfl⟩ := mk_surjective K₀ hK₀ z
  rw [induced_mk,coordinates_mk,coordinates_mk,raw_synthesis p r O hO]

theorem coordinates_inner (z w : H) : ⟪z,w⟫_ℂ = form (coord z) (coord w) := by
  obtain ⟨F,rfl⟩ := mk_surjective K₀ hK₀ z
  obtain ⟨G,rfl⟩ := mk_surjective K₀ hK₀ w
  rw [coordinates_mk,coordinates_mk,inner_mk,pairing_synthesis]

def scalarProjection : H →L[ℂ] H :=
  induced p r hp hp1 hr hr1 (PsiLinear 0) (fun A => by
    change Psi 0 (Psi p A) = Psi p (Psi 0 A)
    rw [Psi_comp,Psi_comp,zero_mul,mul_zero])

theorem scalar_coordinates (z : H) : coord (scalarProjection p r hp hp1 hr hr1 z) = scalarPart (coord z) := by
  rw [scalarProjection,induced_coordinates,scalarPart_eq]; rfl

local notation "P₀" => scalarProjection p r hp hp1 hr hr1

theorem scalar_twice (z : H) : P₀ (P₀ z) = P₀ z := by
  apply coordinates_injective p r hp hp1 hr hr1
  simp only [scalar_coordinates,scalarPart_twice]

theorem scalar_symmetric : (P₀).IsSymmetric := by
  intro z w
  change ⟪P₀ z,w⟫_ℂ = ⟪z,P₀ w⟫_ℂ
  rw [coordinates_inner,coordinates_inner,scalar_coordinates,scalar_coordinates,scalarPart_symmetric]

theorem scalar_inner (z : H) : ⟪P₀ z,z⟫_ℂ = ⟪P₀ z,P₀ z⟫_ℂ := by
  have h := scalar_symmetric p r hp hp1 hr hr1 (P₀ z) z
  change ⟪P₀ (P₀ z),z⟫_ℂ = ⟪P₀ z,P₀ z⟫_ℂ at h
  rwa [scalar_twice] at h

theorem scalar_orthogonal (z : H) : ⟪P₀ z,z-P₀ z⟫_ℂ = 0 := by
  rw [inner_sub_right,scalar_inner,sub_self]

theorem scalar_positive : (P₀).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨scalar_symmetric p r hp hp1 hr hr1,?_⟩
  intro z
  change 0 ≤ (⟪P₀ z,z⟫_ℂ).re
  rw [scalar_inner]
  exact inner_self_nonneg (𝕜 := ℂ) (x := P₀ z)

theorem scalar_pythagoras (z : H) : ‖z‖^2 = ‖P₀ z‖^2 + ‖z-P₀ z‖^2 := by
  have h := norm_add_sq (𝕜 := ℂ) (P₀ z) (z-P₀ z)
  rw [scalar_orthogonal] at h
  have hz : P₀ z+(z-P₀ z)=z := by abel
  simpa only [hz,map_zero,mul_zero,add_zero] using h

theorem centered_norm_le (z : H) : ‖z-P₀ z‖ ≤ ‖z‖ := by
  have h := scalar_pythagoras p r hp hp1 hr hr1 z
  nlinarith [sq_nonneg ‖P₀ z‖,norm_nonneg z,norm_nonneg (z-P₀ z)]

def resetTransfer (a : ℝ) : H →L[ℂ] H := P₀ + (a:ℂ) • (1-P₀)

theorem resetTransfer_apply (a : ℝ) (z : H) :
    resetTransfer p r hp hp1 hr hr1 a z = P₀ z+(a:ℂ) • (z-P₀ z) := by
  simp [resetTransfer]

theorem resetTransfer_coordinates (a : ℝ) (z : H) :
    coord (resetTransfer p r hp hp1 hr hr1 a z) = Psi a (coord z) := by
  rw [resetTransfer_apply,map_add,map_smul,map_sub,scalar_coordinates]
  simp only [Psi,scalarPart,mean]
  module

def phaseOperator (ω : Q → ℝ) (t : ℝ) : H →L[ℂ] H :=
  induced p r hp hp1 hr hr1 (rotate ω t) (rotate_Psi ω t p)

theorem phase_coordinates (ω : Q → ℝ) (t : ℝ) (z : H) :
    coord (phaseOperator p r hp hp1 hr hr1 ω t z) = rotate ω t (coord z) :=
  induced_coordinates p r hp hp1 hr hr1 _ _ z

theorem phase_inner (ω : Q → ℝ) (t : ℝ) (z w : H) :
    ⟪phaseOperator p r hp hp1 hr hr1 ω t z,phaseOperator p r hp hp1 hr hr1 ω t w⟫_ℂ = ⟪z,w⟫_ℂ := by
  rw [coordinates_inner,coordinates_inner,phase_coordinates,phase_coordinates,rotate_form]

def phaseIsometry (ω : Q → ℝ) (t : ℝ) : H →ₗᵢ[ℂ] H :=
  (phaseOperator p r hp hp1 hr hr1 ω t).toLinearMap.isometryOfInner
    (phase_inner p r hp hp1 hr hr1 ω t)

theorem phase_norm (ω : Q → ℝ) (t : ℝ) (z : H) :
    ‖phaseOperator p r hp hp1 hr hr1 ω t z‖ = ‖z‖ :=
  (phaseIsometry p r hp hp1 hr hr1 ω t).norm_map z

theorem phase_group (ω : Q → ℝ) (s t : ℝ) (z : H) :
    phaseOperator p r hp hp1 hr hr1 ω s (phaseOperator p r hp hp1 hr hr1 ω t z) =
      phaseOperator p r hp hp1 hr hr1 ω (s+t) z := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [phase_coordinates,phase_coordinates,phase_coordinates,rotate_group]

theorem phase_zero (ω : Q → ℝ) (z : H) : phaseOperator p r hp hp1 hr hr1 ω 0 z = z := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [phase_coordinates,rotate_zero]

theorem phase_inverse (ω : Q → ℝ) (t : ℝ) (z : H) :
    phaseOperator p r hp hp1 hr hr1 ω (-t) (phaseOperator p r hp hp1 hr hr1 ω t z) = z := by
  rw [phase_group,neg_add_cancel,phase_zero]

theorem phase_scalar (ω : Q → ℝ) (t : ℝ) (z : H) :
    phaseOperator p r hp hp1 hr hr1 ω t (P₀ z) = P₀ z := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [phase_coordinates,scalar_coordinates]
  simp [scalarPart,map_smul,rotate_one]

theorem scalar_phase (ω : Q → ℝ) (t : ℝ) (z : H) :
    P₀ (phaseOperator p r hp hp1 hr hr1 ω t z) = P₀ z := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [scalar_coordinates,phase_coordinates,scalar_coordinates]
  simp [scalarPart,rotate_mean]

/-- The adjoint phase reverses t while retaining the same operational damping a. -/
def transfer (a : ℝ) (ω : Q → ℝ) (t : ℝ) : H →L[ℂ] H :=
  (phaseOperator p r hp hp1 hr hr1 ω t).comp (resetTransfer p r hp hp1 hr hr1 a)

theorem transfer_coordinates (a : ℝ) (ω : Q → ℝ) (t : ℝ) (z : H) :
    coord (transfer p r hp hp1 hr hr1 a ω t z) = rotate ω t (Psi a (coord z)) := by
  change coord (phaseOperator p r hp hp1 hr hr1 ω t (resetTransfer p r hp hp1 hr hr1 a z)) = _
  rw [phase_coordinates,resetTransfer_coordinates]

theorem thermal_coordinates (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (z : H) :
    coord (transfer p r hp hp1 hr hr1 (Real.exp (-γ*t))
      (FiniteThreeLevelThermalPhase.frequencies b ℏ) t z) =
    Channel.heisenberg (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) (coord z) := by
  rw [transfer_coordinates,FiniteThreeLevelEnvironmentLift.channel_observable_action b ℏ γ t hγ ht]
  simp only [Psi,map_add,map_smul,rotate_one]
  simp [rotate,FiniteThreeLevelThermalPhase.phase,Complex.ofReal_sub]


theorem reset_symmetric (a : ℝ) : (resetTransfer p r hp hp1 hr hr1 a).IsSymmetric := by
  intro z w
  change ⟪resetTransfer p r hp hp1 hr hr1 a z,w⟫_ℂ =
    ⟪z,resetTransfer p r hp hp1 hr hr1 a w⟫_ℂ
  rw [coordinates_inner,coordinates_inner,resetTransfer_coordinates,resetTransfer_coordinates]
  exact (form_Psi_symmetric a _ _).symm

theorem reset_positive (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (resetTransfer p r hp hp1 hr hr1 a).IsPositive := by
  have he : resetTransfer p r hp hp1 hr hr1 a =
      ((1-a:ℝ):ℂ) • P₀ + (a:ℂ) • (1 : H →L[ℂ] H) := by
    simp only [resetTransfer,Complex.ofReal_sub,Complex.ofReal_one]; module
  rw [he]
  exact ((scalar_positive p r hp hp1 hr hr1).smul_of_nonneg
    (by exact_mod_cast sub_nonneg.mpr ha1)).add
    (ContinuousLinearMap.isPositive_one.smul_of_nonneg (by exact_mod_cast ha))

theorem reset_composition (a b : ℝ) (z : H) :
    resetTransfer p r hp hp1 hr hr1 a (resetTransfer p r hp hp1 hr hr1 b z) =
      resetTransfer p r hp hp1 hr hr1 (a*b) z := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [resetTransfer_coordinates,resetTransfer_coordinates,resetTransfer_coordinates,Psi_comp]

theorem phase_reset_commute (a : ℝ) (ω : Q → ℝ) (t : ℝ) (z : H) :
    phaseOperator p r hp hp1 hr hr1 ω t (resetTransfer p r hp hp1 hr hr1 a z) =
      resetTransfer p r hp hp1 hr hr1 a (phaseOperator p r hp hp1 hr hr1 ω t z) := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [phase_coordinates,resetTransfer_coordinates,resetTransfer_coordinates,phase_coordinates,rotate_Psi]

theorem phase_adjoint_inner (ω : Q → ℝ) (t : ℝ) (z w : H) :
    ⟪phaseOperator p r hp hp1 hr hr1 ω t z,w⟫_ℂ =
      ⟪z,phaseOperator p r hp hp1 hr hr1 ω (-t) w⟫_ℂ := by
  have he := phase_inner p r hp hp1 hr hr1 ω t z
    (phaseOperator p r hp hp1 hr hr1 ω (-t) w)
  rw [phase_group,add_neg_cancel,phase_zero] at he
  exact he

theorem phase_adjoint (ω : Q → ℝ) (t : ℝ) :
    (phaseOperator p r hp hp1 hr hr1 ω t).adjoint =
      phaseOperator p r hp hp1 hr hr1 ω (-t) := by
  ext z
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact phase_adjoint_inner p r hp hp1 hr hr1 ω t w z

theorem transfer_adjoint_inner (a : ℝ) (ω : Q → ℝ) (t : ℝ) (z w : H) :
    ⟪transfer p r hp hp1 hr hr1 a ω t z,w⟫_ℂ =
      ⟪z,transfer p r hp hp1 hr hr1 a ω (-t) w⟫_ℂ := by
  change ⟪phaseOperator p r hp hp1 hr hr1 ω t
    (resetTransfer p r hp hp1 hr hr1 a z),w⟫_ℂ =
    ⟪z,phaseOperator p r hp hp1 hr hr1 ω (-t) (resetTransfer p r hp hp1 hr hr1 a w)⟫_ℂ
  rw [phase_adjoint_inner,phase_reset_commute]
  exact reset_symmetric p r hp hp1 hr hr1 a z _

theorem transfer_adjoint (a : ℝ) (ω : Q → ℝ) (t : ℝ) :
    (transfer p r hp hp1 hr hr1 a ω t).adjoint =
      transfer p r hp hp1 hr hr1 a ω (-t) := by
  ext z
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right,transfer_adjoint_inner]

theorem transfer_composition (a b : ℝ) (ω : Q → ℝ) (s t : ℝ) (z : H) :
    transfer p r hp hp1 hr hr1 a ω s (transfer p r hp hp1 hr hr1 b ω t z) =
      transfer p r hp hp1 hr hr1 (a*b) ω (s+t) z := by
  change phaseOperator p r hp hp1 hr hr1 ω s (resetTransfer p r hp hp1 hr hr1 a
    (phaseOperator p r hp hp1 hr hr1 ω t (resetTransfer p r hp hp1 hr hr1 b z))) = _
  rw [← phase_reset_commute,phase_group,reset_composition]
  rfl

theorem transfer_normal (a : ℝ) (ω : Q → ℝ) (t : ℝ) :
    (transfer p r hp hp1 hr hr1 a ω t).adjoint * transfer p r hp hp1 hr hr1 a ω t =
      P₀+(a^2:ℂ) • (1-P₀) ∧
    transfer p r hp hp1 hr hr1 a ω t * (transfer p r hp hp1 hr hr1 a ω t).adjoint =
      P₀+(a^2:ℂ) • (1-P₀) := by
  rw [transfer_adjoint]
  constructor <;> ext z
  · change transfer p r hp hp1 hr hr1 a ω (-t) (transfer p r hp hp1 hr hr1 a ω t z) = _
    rw [transfer_composition,neg_add_cancel]
    change phaseOperator p r hp hp1 hr hr1 ω 0 (resetTransfer p r hp hp1 hr hr1 (a*a) z) = _
    rw [phase_zero]
    simp [resetTransfer,pow_two,Complex.ofReal_mul]
  · change transfer p r hp hp1 hr hr1 a ω t (transfer p r hp hp1 hr hr1 a ω (-t) z) = _
    rw [transfer_composition,add_neg_cancel]
    change phaseOperator p r hp hp1 hr hr1 ω 0 (resetTransfer p r hp hp1 hr hr1 (a*a) z) = _
    rw [phase_zero]
    simp [resetTransfer,pow_two,Complex.ofReal_mul]

theorem transfer_norm (a : ℝ) (ω : Q → ℝ) (t : ℝ) (z : H) :
    ‖transfer p r hp hp1 hr hr1 a ω t z‖ =
      ‖resetTransfer p r hp hp1 hr hr1 a z‖ := phase_norm p r hp hp1 hr hr1 ω t _

theorem transfer_error_norm (a : ℝ) (ω : Q → ℝ) (t : ℝ) (z : H) :
    ‖transfer p r hp hp1 hr hr1 a ω t z-P₀ z‖ = |a| * ‖z-P₀ z‖ := by
  change ‖phaseOperator p r hp hp1 hr hr1 ω t (resetTransfer p r hp hp1 hr hr1 a z)-P₀ z‖ = _
  rw [← phase_scalar p r hp hp1 hr hr1 ω t z,← map_sub,phase_norm,resetTransfer_apply]
  have he : P₀ z+(a:ℂ) • (z-P₀ z)-P₀ z=(a:ℂ) • (z-P₀ z) := by abel
  rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs,phase_scalar]

def constantVector : H := mk K₀ hK₀ (fun _ => 1)
def centeredVector (i : Fin 8) : H := mk K₀ hK₀ (innerMode i)

theorem constant_coordinates : coord (constantVector p r hp hp1 hr hr1) = 1 := by
  rw [constantVector,coordinates_mk,synthesis_constant]

theorem centered_coordinates (i : Fin 8) :
    coord (centeredVector p r hp hp1 hr hr1 i) = (p:ℂ) • modeMatrix i := by
  rw [centeredVector,coordinates_mk,synthesis_innerMode]

theorem scalar_constant : P₀ (constantVector p r hp hp1 hr hr1) =
    constantVector p r hp hp1 hr hr1 := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [scalar_coordinates,constant_coordinates]
  simp [scalarPart,mean_one]

theorem scalar_centered (i : Fin 8) : P₀ (centeredVector p r hp hp1 hr hr1 i) = 0 := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [scalar_coordinates,centered_coordinates,map_zero]
  simp [scalarPart,mean,mode_mean_zero]

theorem transfer_constant (a : ℝ) (ω : Q → ℝ) (t : ℝ) :
    transfer p r hp hp1 hr hr1 a ω t (constantVector p r hp hp1 hr hr1) =
      constantVector p r hp hp1 hr hr1 := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [transfer_coordinates,constant_coordinates,Psi_unital,rotate_one]

theorem centered_nonzero (hpos : 0 < p) (i : Fin 8) :
    centeredVector p r hp hp1 hr hr1 i ≠ 0 := by
  have h : 0 < ‖centeredVector p r hp hp1 hr hr1 i‖^2 := by
    change 0 < ‖mk K₀ hK₀ (innerMode i)‖^2
    rw [innerMode_norm_sq]
    exact mul_pos (modeNorm_pos i) (sq_pos_of_pos hpos)
  intro hz
  change 0 < ‖centeredVector p r hp hp1 hr hr1 i‖^2 at h
  simp [hz] at h

theorem centered_operator_bound (a : ℝ) (ω : Q → ℝ) (t : ℝ) :
    ‖transfer p r hp hp1 hr hr1 a ω t-P₀‖ ≤ |a| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a)
  intro z
  change ‖transfer p r hp hp1 hr hr1 a ω t z-P₀ z‖ ≤ _
  rw [transfer_error_norm]
  exact mul_le_mul_of_nonneg_left (centered_norm_le p r hp hp1 hr hr1 z) (abs_nonneg a)

theorem centered_operator_norm (hpos : 0 < p) (a : ℝ) (ω : Q → ℝ) (t : ℝ) :
    ‖transfer p r hp hp1 hr hr1 a ω t-P₀‖ = |a| := by
  apply le_antisymm (centered_operator_bound p r hp hp1 hr hr1 a ω t)
  let z := centeredVector p r hp hp1 hr hr1 0
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr (centered_nonzero p r hp hp1 hr hr1 hpos 0)
  have he := (transfer p r hp hp1 hr hr1 a ω t-P₀).le_opNorm z
  change ‖transfer p r hp hp1 hr hr1 a ω t z-P₀ z‖ ≤ _ at he
  rw [transfer_error_norm,scalar_centered,sub_zero] at he
  exact (mul_le_mul_iff_of_pos_right hz).mp he

/-- A genuine unit vector attaining the centered operator norm on the old quotient. -/
def normAttainer : H :=
  ((‖centeredVector p r hp hp1 hr hr1 0‖⁻¹:ℝ):ℂ) • centeredVector p r hp hp1 hr hr1 0

theorem normAttainer_unit (hpos : 0 < p) : ‖normAttainer p r hp hp1 hr hr1‖ = 1 := by
  have hz := norm_pos_iff.mpr (centered_nonzero p r hp hp1 hr hr1 hpos 0)
  simp only [normAttainer,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (ne_of_gt hz)

theorem normAttainer_centered : P₀ (normAttainer p r hp hp1 hr hr1) = 0 := by
  simp [normAttainer,map_smul,scalar_centered]

theorem normAttainer_attains (hpos : 0 < p) (a : ℝ) (ω : Q → ℝ) (t : ℝ) :
    ‖(transfer p r hp hp1 hr hr1 a ω t-P₀) (normAttainer p r hp hp1 hr hr1)‖ = |a| := by
  change ‖transfer p r hp hp1 hr hr1 a ω t (normAttainer p r hp hp1 hr hr1)-
    P₀ (normAttainer p r hp hp1 hr hr1)‖ = _
  rw [transfer_error_norm,normAttainer_centered,sub_zero,normAttainer_unit p r hp hp1 hr hr1 hpos,mul_one]

theorem central_reset_scalar (hz : p=0) (z : H) : P₀ z = z := by
  subst p
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  apply coordinates_injective 0 r hp hp1 hr hr1
  rw [scalar_coordinates,coordinates_mk,synthesis_full_reset]
  simp [scalarPart,mean,rhoN_trace]

theorem central_reset_transfer (hz : p=0) (a : ℝ) (ω : Q → ℝ) (t : ℝ) (z : H) :
    transfer p r hp hp1 hr hr1 a ω t z = z := by
  have he := central_reset_scalar p r hp hp1 hr hr1 hz z
  change phaseOperator p r hp hp1 hr hr1 ω t (resetTransfer p r hp hp1 hr hr1 a z) = z
  rw [resetTransfer_apply,he,sub_self,smul_zero,add_zero]
  rw [← he,phase_scalar]

theorem central_reset_norm (hz : p=0) (a : ℝ) (ω : Q → ℝ) (t : ℝ) :
    ‖transfer p r hp hp1 hr hr1 a ω t-P₀‖ = 0 := by
  have he : transfer p r hp hp1 hr hr1 a ω t=P₀ := by
    ext z
    rw [central_reset_transfer p r hp hp1 hr hr1 hz,
      central_reset_scalar p r hp hp1 hr hr1 hz]
  rw [he,sub_self,norm_zero]

theorem thermal_semigroup (b ℏ γ s t : ℝ) (z : H) :
    transfer p r hp hp1 hr hr1 (Real.exp (-γ*s)) (FiniteThreeLevelThermalPhase.frequencies b ℏ) s
      (transfer p r hp hp1 hr hr1 (Real.exp (-γ*t)) (FiniteThreeLevelThermalPhase.frequencies b ℏ) t z) =
    transfer p r hp hp1 hr hr1 (Real.exp (-γ*(s+t))) (FiniteThreeLevelThermalPhase.frequencies b ℏ) (s+t) z := by
  rw [transfer_composition,← Real.exp_add]
  have he : -γ*s+-γ*t = -γ*(s+t) := by ring
  rw [he]


/-- Inner-frame realization, continuous from finite matrices to the actual quotient. -/
def innerFrame : MatQ →ₗ[ℂ] Coefficients hK₀ where
  toFun A u := frameLinear A u.1
  map_add' A B := by
    change (fun u : HalfHistory => frameLinear (A+B) u.1) =
      (fun u => frameLinear A u.1+frameLinear B u.1)
    funext u
    simp
  map_smul' z A := by
    change (fun u : HalfHistory => frameLinear (z • A) u.1) =
      (fun u => z*frameLinear A u.1)
    funext u
    simp

def representLinear : MatQ →ₗ[ℂ] H := (mkLinear K₀ hK₀).comp (innerFrame p r hp hp1 hr hr1)

def represent : MatQ →L[ℂ] H := (representLinear p r hp hp1 hr hr1).toContinuousLinearMap

theorem represent_coordinates (A : MatQ) :
    coord (represent p r hp hp1 hr hr1 A) = Psi p A := by
  change coord (mk K₀ hK₀ (fun u => frameCoeff A u.1)) = _
  rw [coordinates_mk,synthesis_inner,frame_right_inverse]

def generator (ω : Q → ℝ) (γ : ℝ) : H →L[ℂ] H :=
  induced p r hp hp1 hr hr1 (generatorMatrix ω γ) (generatorMatrix_Psi ω γ p)

theorem generator_coordinates (ω : Q → ℝ) (γ : ℝ) (z : H) :
    coord (generator p r hp hp1 hr hr1 ω γ z) = generatorMatrix ω γ (coord z) :=
  induced_coordinates p r hp hp1 hr hr1 _ _ z

theorem transfer_representative (ω : Q → ℝ) (γ t : ℝ) (F : HalfHistory → ℂ) :
    transfer p r hp hp1 hr hr1 (Real.exp (-γ*t)) ω t (mk K₀ hK₀ F) =
      represent p r hp hp1 hr hr1 (matrixOrbit ω γ t (synthesis 1 r F)) := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [transfer_coordinates,coordinates_mk,represent_coordinates,synthesis_from_raw p r F]
  simp only [matrixOrbit,rotate_Psi,Psi_comp]
  rw [mul_comm p (Real.exp (-γ*t))]

theorem generator_represent (ω : Q → ℝ) (γ : ℝ) (A : MatQ) :
    generator p r hp hp1 hr hr1 ω γ (represent p r hp hp1 hr hr1 A) =
      represent p r hp hp1 hr hr1 (generatorMatrix ω γ A) := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [generator_coordinates,represent_coordinates,represent_coordinates,generatorMatrix_Psi]

/-- The analytic extension differentiates on the same quotient even at central reset. -/
theorem orbit_hasDerivAt (ω : Q → ℝ) (γ t : ℝ) (z : H) :
    HasDerivAt (fun s : ℝ => transfer p r hp hp1 hr hr1 (Real.exp (-γ*s)) ω s z)
      (generator p r hp hp1 hr hr1 ω γ
        (transfer p r hp hp1 hr hr1 (Real.exp (-γ*t)) ω t z)) t := by
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  simp only [transfer_representative,generator_represent]
  exact ((represent p r hp hp1 hr hr1).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (matrixOrbit_hasDerivAt ω γ t (synthesis 1 r F))

/-- The physical channel orbit is differentiated within its nonnegative-time domain. -/
theorem physical_orbit_right_derivative (b ℏ γ : ℝ) (z : H) :
    HasDerivWithinAt
      (fun t : ℝ => transfer p r hp hp1 hr hr1 (Real.exp (-γ*t))
        (FiniteThreeLevelThermalPhase.frequencies b ℏ) t z)
      (generator p r hp hp1 hr hr1 (FiniteThreeLevelThermalPhase.frequencies b ℏ) γ z)
      (Set.Ici 0) 0 := by
  have hd := (orbit_hasDerivAt p r hp hp1 hr hr1
    (FiniteThreeLevelThermalPhase.frequencies b ℏ) γ 0 z).hasDerivWithinAt (s := Set.Ici 0)
  have he : transfer p r hp hp1 hr hr1 (Real.exp (-γ*0))
      (FiniteThreeLevelThermalPhase.frequencies b ℏ) 0 z=z := by
    apply coordinates_injective p r hp hp1 hr hr1
    rw [transfer_coordinates,rotate_zero]
    simp [Psi_one]
  rwa [he] at hd

theorem quotient_propagator_duality (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (z : H) (X : MatQ) :
    (X*coord (transfer p r hp hp1 hr hr1 (Real.exp (-γ*t))
      (FiniteThreeLevelThermalPhase.frequencies b ℏ) t z)).trace =
    (OpenSystems.lindbladPropagatorAction (FiniteThreeLevelThermalPhase.scaledH b ℏ)
      (FiniteThreeLevelThermalPhase.jumps γ) t X*coord z).trace := by
  rw [thermal_coordinates p r hp hp1 hr hr1 b ℏ γ t hγ ht]
  exact FiniteThreeLevelThermalPhase.channel_duality b ℏ γ t hγ ht X (coord z)

theorem central_reset_generator (hz : p=0) (ω : Q → ℝ) (γ : ℝ) (z : H) :
    generator p r hp hp1 hr hr1 ω γ z = 0 := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [generator_coordinates,map_zero]
  have he := congrArg coord (central_reset_scalar p r hp hp1 hr hr1 hz z)
  rw [scalar_coordinates] at he
  rw [← he,generatorMatrix_apply,scalarPart_twice,sub_self,smul_zero,add_zero]
  ext i j
  by_cases hij : i=j
  · subst j; simp [hamLinear]
  · simp [hamLinear,scalarPart,hij]



theorem reset_norm_sq (a : ℝ) (z : H) :
    ‖resetTransfer p r hp hp1 hr hr1 a z‖^2 =
      ‖P₀ z‖^2+a^2*‖z-P₀ z‖^2 := by
  rw [resetTransfer_apply,norm_add_sq (𝕜 := ℂ),inner_smul_right,scalar_orthogonal]
  simp only [mul_zero,map_zero,mul_zero,add_zero,norm_smul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem transfer_norm_sq (a : ℝ) (ω : Q → ℝ) (t : ℝ) (z : H) :
    ‖transfer p r hp hp1 hr hr1 a ω t z‖^2 =
      ‖P₀ z‖^2+a^2*‖z-P₀ z‖^2 := by
  rw [transfer_norm,reset_norm_sq]

theorem transfer_contraction (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ω : Q → ℝ) (t : ℝ) (z : H) :
    ‖transfer p r hp hp1 hr hr1 a ω t z‖ ≤ ‖z‖ := by
  have he := transfer_norm_sq p r hp hp1 hr hr1 a ω t z
  have hpyt := scalar_pythagoras p r hp hp1 hr hr1 z
  have hmul : a^2*‖z-P₀ z‖^2 ≤ ‖z-P₀ z‖^2 :=
    mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
  nlinarith [norm_nonneg (transfer p r hp hp1 hr hr1 a ω t z),norm_nonneg z]

theorem transfer_centered_norm_sq (a : ℝ) (ω : Q → ℝ) (t : ℝ) (i : Fin 8) :
    ‖transfer p r hp hp1 hr hr1 a ω t (centeredVector p r hp hp1 hr hr1 i)‖^2 =
      a^2*modeNorm i*p^2 := by
  rw [transfer_norm_sq,scalar_centered]
  simp only [norm_zero,zero_pow (by decide : 2≠0),sub_zero,zero_add]
  change a^2*‖mk K₀ hK₀ (innerMode i)‖^2=_
  rw [innerMode_norm_sq]
  ring

end Quotient

theorem kraus_sum {m : ℕ} {ι : Type*} [Fintype ι] (V : Fin m → MatQ) (A : ι → MatQ) :
    krausMap V (∑ i,A i)=∑ i,krausMap V (A i) := by
  simp only [krausMap,Matrix.mul_sum,Matrix.sum_mul]
  rw [Finset.sum_comm]

section Evolution
variable {m : ℕ} (V : Fin m → MatQ) (hV : IsKrausChannel V)
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)

/-- Actual product Kraus family: the inserted channel follows the original central reset. -/
def centralKraus := composeKraus V (channel (p*p))

def centralStep : Step Q Unit 15 where
  count := _
  evolution k := GibbsMultilevelReflection.joint (centralKraus V p k)
  normalized := GibbsMultilevelReflection.joint_normalized _
    (isKrausChannel_composeKraus hV (channel_normalized (mul_nonneg hp hp) (by nlinarith)))
  instrument := instrument

theorem centralStep_branch (o : Outcome) (X : MatQ) :
    (centralStep V hV p hp hp1).branch Q Unit 15 o (GibbsMultilevelReflection.joint X) =
      GibbsMultilevelReflection.joint (instrument.branch o (krausMap V (Phi (p*p) X))) := by
  change (instrument.lift Unit).branch o
    (krausMap (fun k => GibbsMultilevelReflection.joint (centralKraus V p k))
      (GibbsMultilevelReflection.joint X)) = _
  rw [GibbsMultilevelReflection.joint_kraus,centralKraus,krausMap_composeKraus,
    channel_state (mul_nonneg hp hp) (by nlinarith)]
  exact GibbsMultilevelReflection.joint_kraus _ _

def evolutionTree : Tree Q Unit 15 4 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step r hr hr1) (fun _ =>
      .node (centralStep V hV p hp hp1) (fun _ =>
        .node (step r hr hr1) (fun _ => .done))))

/-- Chronological probability is defined before any operator or Gram identity. -/
def evolutionKernel (u v : HalfHistory) : ℂ :=
  (weight Q Unit 15 (evolutionTree V hV p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
    (GibbsMultilevelReflection.joint rhoN) : ℂ)

theorem evolution_run (u v : HalfHistory) :
    run Q Unit 15 (evolutionTree V hV p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
      (GibbsMultilevelReflection.joint rhoN) =
    GibbsMultilevelReflection.joint (instrument.branch v.2
      (Phi r (instrument.branch v.1 (krausMap V (Phi (p*p) (Gamma (halfEffect r u))))))) := by
  change (step r hr hr1).branch Q Unit 15 v.2
    ((centralStep V hV p hp hp1).branch Q Unit 15 v.1
      (run Q Unit 15 (negativeTree r hr hr1) (u.2,u.1,())
        (GibbsMultilevelReflection.joint rhoN))) = _
  rw [negative_run,centralStep_branch,step_branch]

theorem evolution_trace (u v : HalfHistory) :
    (run Q Unit 15 (evolutionTree V hV p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
      (GibbsMultilevelReflection.joint rhoN)).trace =
    (halfEffect r v*krausMap V (Phi (p*p) (Gamma (halfEffect r u)))).trace := by
  rw [evolution_run,GibbsMultilevelReflection.joint_trace,branch_trace,Phi_Psi_duality,trace_duality]
  rfl

theorem evolutionKernel_trace (u v : HalfHistory) :
    evolutionKernel V hV p r hp hp1 hr hr1 u v =
      (halfEffect r v*krausMap V (Phi (p*p) (Gamma (halfEffect r u)))).trace := by
  unfold evolutionKernel weight
  rw [evolution_trace]
  apply hermitian_product_real _ _ (halfEffect_adjoint r v)
  have he : (Phi (p*p) (Gamma (halfEffect r u)))ᴴ =
      Phi (p*p) (Gamma (halfEffect r u)) := by
    rw [Phi_Gamma,Gamma_adjoint,Psi_adjoint,halfEffect_adjoint]
  simp only [krausMap,Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,he,Matrix.mul_assoc]

theorem evolution_probabilities :
    (∀ h, 0 ≤ weight Q Unit 15 (evolutionTree V hV p r hp hp1 hr hr1) h
      (GibbsMultilevelReflection.joint rhoN)) ∧
    (∑ h,weight Q Unit 15 (evolutionTree V hV p r hp hp1 hr hr1) h
      (GibbsMultilevelReflection.joint rhoN))=1 :=
  normalized_weights Q Unit 15 _ joint_density

theorem evolutionKernel_nonnegative (u v : HalfHistory) :
    0 ≤ (evolutionKernel V hV p r hp hp1 hr hr1 u v).re :=
  (evolution_probabilities V hV p r hp hp1 hr hr1).1 _

theorem evolutionKernel_real (u v : HalfHistory) :
    (evolutionKernel V hV p r hp hp1 hr hr1 u v).im=0 := rfl

theorem evolutionKernel_form
    (hcomm : ∀ A,Channel.heisenberg V (Psi p A)=Psi p (Channel.heisenberg V A))
    (u v : HalfHistory) :
    evolutionKernel V hV p r hp hp1 hr hr1 u v =
      form (FiniteThreeLevelPositiveHistory.midpoint p r u)
        (Channel.heisenberg V (FiniteThreeLevelPositiveHistory.midpoint p r v)) := by
  rw [evolutionKernel_trace,Matrix.trace_mul_comm,← Channel.trace_duality,Matrix.trace_mul_comm,
    central_split,← hcomm]
  rw [form,midpoint_adjoint]
  simp only [FiniteThreeLevelPositiveHistory.midpoint,Gamma,Matrix.mul_assoc]

/-- The outer marginal is another separately defined actual process. -/
def evolutionTwoTree : Tree Q Unit 15 2 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (centralStep V hV p hp hp1) (fun _ => .done))

def evolutionTwoKernel (i j : Outcome) : ℂ :=
  (weight Q Unit 15 (evolutionTwoTree V hV p hp hp1) (i,j,())
    (GibbsMultilevelReflection.joint rhoN) : ℂ)

theorem evolutionTwoKernel_trace (i j : Outcome) :
    evolutionTwoKernel V hV p hp hp1 i j =
      (effect j*krausMap V (Phi (p*p) (Gamma (effect i)))).trace := by
  unfold evolutionTwoKernel weight
  have he : run Q Unit 15 (evolutionTwoTree V hV p hp hp1) (i,j,())
    (GibbsMultilevelReflection.joint rhoN) =
      GibbsMultilevelReflection.joint (instrument.branch j (krausMap V (Phi (p*p) (Gamma (effect i))))) := by
    change (centralStep V hV p hp hp1).branch Q Unit 15 j
      ((step 1 (by norm_num) le_rfl).branch Q Unit 15 i (GibbsMultilevelReflection.joint rhoN)) = _
    rw [step_branch,centralStep_branch,Phi_one,branch_rhoN]
  rw [he,GibbsMultilevelReflection.joint_trace,branch_trace]
  apply hermitian_product_real _ _ (effect_adjoint j)
  have hA : (Phi (p*p) (Gamma (effect i)))ᴴ = Phi (p*p) (Gamma (effect i)) := by
    rw [Phi_Gamma,Gamma_adjoint,Psi_adjoint,effect_adjoint]
  simp only [krausMap,Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,hA,Matrix.mul_assoc]

theorem evolution_outer_marginal (i j : Outcome) :
    ∑ o,∑ o',evolutionKernel V hV p r hp hp1 hr hr1 (i,o) (j,o') =
      evolutionTwoKernel V hV p hp hp1 i j := by
  simp_rw [evolutionKernel_trace]
  simp only [← Matrix.trace_sum,← Matrix.sum_mul,halfEffect_outer,
    ← Matrix.mul_sum,← kraus_sum,← Phi_sum,← Gamma_sum]
  rw [evolutionTwoKernel_trace]

end Evolution


theorem Phi_comp (a b : ℝ) (X : MatQ) : Phi a (Phi b X)=Phi (a*b) X := by
  simp only [Phi,Matrix.trace_add,Matrix.trace_smul,rhoN_trace,smul_eq_mul,mul_one,
    Complex.ofReal_mul,smul_add,smul_smul]
  module

def insertedKernel (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) : Matrix HalfHistory HalfHistory ℂ :=
  evolutionKernel (channel a) (channel_normalized ha ha1) p r hp hp1 hr hr1

theorem inserted_trace (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (u v : HalfHistory) :
    insertedKernel p r a hp hp1 hr hr1 ha ha1 u v =
      (halfEffect r v*Phi (p*p*a) (Gamma (halfEffect r u))).trace := by
  rw [insertedKernel,evolutionKernel_trace,channel_state ha ha1,Phi_comp]
  rw [mul_comm a (p*p)]

theorem splitRetention_nonnegative (p a : ℝ) (hp : 0 ≤ p) :
    0 ≤ p*Real.sqrt a := mul_nonneg hp (Real.sqrt_nonneg a)
theorem splitRetention_le_one (p a : ℝ) (hp1 : p ≤ 1) (ha1 : a ≤ 1) :
    p*Real.sqrt a ≤ 1 := by
  have hs : Real.sqrt a ≤ 1 := (Real.sqrt_le_one).mpr ha1
  nlinarith [Real.sqrt_nonneg a]
theorem splitRetention_square (p a : ℝ) (ha : 0 ≤ a) :
    (p*Real.sqrt a)*(p*Real.sqrt a) = p*p*a := by
  nlinarith [Real.sq_sqrt ha]

theorem inserted_eq_original (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    insertedKernel p r a hp hp1 hr hr1 ha ha1 =
      FiniteThreeLevelPositiveHistory.kernel (p*Real.sqrt a) r
        (splitRetention_nonnegative p a hp) (splitRetention_le_one p a hp1 ha1) hr hr1 := by
  ext u v
  rw [inserted_trace,kernel_trace,splitRetention_square p a ha]

theorem inserted_positive (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (insertedKernel p r a hp hp1 hr hr1 ha ha1).PosSemidef := by
  rw [inserted_eq_original]
  exact kernel_posSemidef _ _ _ _ _ _

theorem inserted_total (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∑ u,∑ v,insertedKernel p r a hp hp1 hr hr1 ha ha1 u v=1 := by
  simp only [inserted_eq_original]
  exact kernel_total _ _ _ _ _ _

theorem inserted_factored (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (i o j k : Outcome) :
    insertedKernel p r a hp hp1 hr hr1 ha ha1 (i,o) (j,k) =
      ((halfCoefficient r i o*halfCoefficient r j k*
        (p^2*a*overlap i j+(1-p^2*a)*d i*d j):ℝ):ℂ) := by
  rw [inserted_eq_original,kernel_factored]
  have hs : (p*Real.sqrt a)^2=p^2*a := by nlinarith [splitRetention_square p a ha]
  rw [hs]


/-- Equality of operational kernels identifies their constructed dimensions. -/
theorem space_finrank_congr {ι : Type*} [Fintype ι] {K L : Matrix ι ι ℂ}
    (hK : K.PosSemidef) (hL : L.PosSemidef) (he : K=L) :
    Module.finrank ℂ (Space K hK)=Module.finrank ℂ (Space L hL) := by
  subst L
  rfl

def coefficientIdentity {ι : Type*} [Fintype ι] {K L : Matrix ι ι ℂ}
    (hK : K.PosSemidef) (hL : L.PosSemidef) : Coefficients hK →ₗ[ℂ] Coefficients hL where
  toFun F := F
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def quotientTransport {ι : Type*} [Fintype ι] {K L : Matrix ι ι ℂ}
    (hK : K.PosSemidef) (hL : L.PosSemidef)
    (hnull : ∀ F : Coefficients hK,F ∈ nullSpace K hK →
      coefficientIdentity hK hL F ∈ nullSpace L hL) : Space K hK →ₗ[ℂ] Space L hL :=
  (quotientEquiv L hL).toLinearMap.comp
    (((nullSpace K hK).mapQ (nullSpace L hL) (coefficientIdentity hK hL) hnull).comp
      (quotientEquiv K hK).symm.toLinearMap)

theorem quotientTransport_mk {ι : Type*} [Fintype ι] {K L : Matrix ι ι ℂ}
    (hK : K.PosSemidef) (hL : L.PosSemidef)
    (hnull : ∀ F : Coefficients hK,F ∈ nullSpace K hK →
      coefficientIdentity hK hL F ∈ nullSpace L hL) (F : Coefficients hK) :
    quotientTransport hK hL hnull (mk K hK F)=mk L hL F := by
  rw [← quotientEquiv_mk hK F]
  simp only [quotientTransport,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply,Submodule.mapQ_apply]
  exact quotientEquiv_mk hL F


theorem quotientTransport_norm {ι : Type*} [Fintype ι] {K L : Matrix ι ι ℂ}
    (hK : K.PosSemidef) (hL : L.PosSemidef)
    (hnull : ∀ F : Coefficients hK,F ∈ nullSpace K hK →
      coefficientIdentity hK hL F ∈ nullSpace L hL)
    (T : Space K hK →L[ℂ] Space K hK)
    (henergy : ∀ F : Coefficients hK,pairing L F F=⟪T (mk K hK F),T (mk K hK F)⟫_ℂ)
    (z : Space K hK) : ‖quotientTransport hK hL hnull z‖=‖T z‖ := by
  obtain ⟨F,rfl⟩ := mk_surjective K hK z
  rw [quotientTransport_mk]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_mk_sq,henergy,@norm_sq_eq_re_inner ℂ]
  rfl


abbrev InsertedSpace (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) :=
  Space (insertedKernel p r a hp hp1 hr hr1 ha ha1) (inserted_positive p r a hp hp1 hr hr1 ha ha1)

theorem inserted_rank_nine (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hp0 : 0 < p) (ha0 : 0 < a) :
    Module.finrank ℂ (InsertedSpace p r a hp hp1 hr hr1 ha ha1)=9 := by
  rw [space_finrank_congr _ _ (inserted_eq_original p r a hp hp1 hr hr1 ha ha1)]
  exact reconstructed_finrank _ _ _ _ _ _ (mul_pos hp0 (Real.sqrt_pos.mpr ha0))

theorem inserted_rank_one (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hz : p=0 ∨ a=0) :
    Module.finrank ℂ (InsertedSpace p r a hp hp1 hr hr1 ha ha1)=1 := by
  have he : p*p*a=0 := by rcases hz with h|h <;> simp [h]
  have hk : insertedKernel p r a hp hp1 hr hr1 ha ha1 =
      FiniteThreeLevelPositiveHistory.kernel 0 r (by norm_num) (by norm_num) hr hr1 := by
    ext u v
    rw [inserted_trace,kernel_trace,he]
    norm_num
  rw [space_finrank_congr _ _ hk]
  exact reset_finrank _ _ _

theorem inserted_synthesis (p r a : ℝ) (F : HalfHistory → ℂ) :
    synthesis (p*Real.sqrt a) r F = Psi (Real.sqrt a) (synthesis p r F) := by
  simp only [synthesis,FiniteThreeLevelPositiveHistory.midpoint,Psi_sum,Psi_smul,Psi_comp]
  rw [mul_comm p (Real.sqrt a)]

theorem inserted_pairing (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (F G : HalfHistory → ℂ) :
    pairing (insertedKernel p r a hp hp1 hr hr1 ha ha1) F G =
      form (Psi (Real.sqrt a) (synthesis p r F)) (Psi (Real.sqrt a) (synthesis p r G)) := by
  rw [inserted_eq_original,pairing_synthesis,inserted_synthesis,inserted_synthesis]

theorem inserted_operator_pairing (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (F G : HalfHistory → ℂ) :
    pairing (insertedKernel p r a hp hp1 hr hr1 ha ha1) F G =
      form (synthesis p r F) (Psi a (synthesis p r G)) := by
  rw [inserted_pairing,← form_Psi_symmetric,Psi_comp,Real.mul_self_sqrt ha]

section InsertionMap
variable (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
  (ha : 0 ≤ a) (ha1 : a ≤ 1)
local notation "K₀" => FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1
local notation "hK₀" => kernel_posSemidef p r hp hp1 hr hr1
local notation "Kₐ" => insertedKernel p r a hp hp1 hr hr1 ha ha1
local notation "hKₐ" => inserted_positive p r a hp hp1 hr hr1 ha ha1

def sameCoefficients : Coefficients hK₀ →ₗ[ℂ] Coefficients hKₐ := coefficientIdentity hK₀ hKₐ

theorem inserted_null (F : HalfHistory → ℂ) (hF : F ∈ nullSpace K₀ hK₀) :
    sameCoefficients p r a hp hp1 hr hr1 ha ha1 F ∈ nullSpace Kₐ hKₐ := by
  apply (mem_nullSpace_iff Kₐ hKₐ _).mpr
  change pairing Kₐ F F=0
  rw [inserted_pairing]
  have hz := synthesis_null p r hp hp1 hr hr1 hF
  change synthesis p r F=0 at hz
  rw [hz]
  simp [Psi,form]

/-- This map sends the same literal coefficients into the inserted quotient. -/
def sameHistoryLinear : Reconstructed p r hp hp1 hr hr1 →ₗ[ℂ] InsertedSpace p r a hp hp1 hr hr1 ha ha1 :=
  quotientTransport hK₀ hKₐ (fun F hF => inserted_null p r a hp hp1 hr hr1 ha ha1 F hF)

def sameHistory : Reconstructed p r hp hp1 hr hr1 →L[ℂ] InsertedSpace p r a hp hp1 hr hr1 ha ha1 :=
  (sameHistoryLinear p r a hp hp1 hr hr1 ha ha1).toContinuousLinearMap

theorem sameHistory_mk (F : HalfHistory → ℂ) :
    sameHistory p r a hp hp1 hr hr1 ha ha1 (mk K₀ hK₀ F) = mk Kₐ hKₐ F := by
  exact quotientTransport_mk hK₀ hKₐ _ F

theorem sameHistory_norm (z : Reconstructed p r hp hp1 hr hr1) :
    ‖sameHistory p r a hp hp1 hr hr1 ha ha1 z‖ =
      ‖resetTransfer p r hp hp1 hr hr1 (Real.sqrt a) z‖ := by
  apply quotientTransport_norm hK₀ hKₐ _ (resetTransfer p r hp hp1 hr hr1 (Real.sqrt a)) _ z
  intro F
  have he := coordinates_inner p r hp hp1 hr hr1
    (resetTransfer p r hp hp1 hr hr1 (Real.sqrt a) (mk K₀ hK₀ F))
    (resetTransfer p r hp hp1 hr hr1 (Real.sqrt a) (mk K₀ hK₀ F))
  simp only [resetTransfer_coordinates,coordinates_mk] at he
  exact (inserted_pairing p r a hp hp1 hr hr1 ha ha1 F F).trans he.symm


local notation "P₀" => scalarProjection p r hp hp1 hr hr1

theorem sameHistory_norm_sq (z : Reconstructed p r hp hp1 hr hr1) :
    ‖sameHistory p r a hp hp1 hr hr1 ha ha1 z‖^2 =
      ‖P₀ z‖^2+a*‖z-P₀ z‖^2 := by
  rw [sameHistory_norm,reset_norm_sq,Real.sq_sqrt ha]

theorem full_inserted_original (ω : Q → ℝ) (t : ℝ) (z : Reconstructed p r hp hp1 hr hr1) :
    ‖transfer p r hp hp1 hr hr1 a ω t z‖^2 ≤
      ‖sameHistory p r a hp hp1 hr hr1 ha ha1 z‖^2 ∧
    ‖sameHistory p r a hp hp1 hr hr1 ha ha1 z‖^2 ≤ ‖z‖^2 := by
  rw [transfer_norm_sq,sameHistory_norm_sq,scalar_pythagoras p r hp hp1 hr hr1 z]
  constructor
  · have hm := mul_le_mul_of_nonneg_right (by nlinarith : a^2≤a) (sq_nonneg ‖z-P₀ z‖)
    linarith only [hm]
  · have hm := mul_le_of_le_one_left (sq_nonneg ‖z-P₀ z‖) ha1
    linarith only [hm]

/-- Strictness is equivalent to a nonzero centered component, not merely positive dose. -/
theorem full_inserted_strict_iff (ha0 : 0 < a) (ha_lt : a < 1)
    (ω : Q → ℝ) (t : ℝ) (z : Reconstructed p r hp hp1 hr hr1) :
    (‖transfer p r hp hp1 hr hr1 a ω t z‖^2 <
        ‖sameHistory p r a hp hp1 hr hr1 ha ha1 z‖^2 ∧
      ‖sameHistory p r a hp hp1 hr hr1 ha ha1 z‖^2 < ‖z‖^2) ↔ z-P₀ z≠0 := by
  rw [transfer_norm_sq,sameHistory_norm_sq,scalar_pythagoras p r hp hp1 hr hr1 z]
  constructor
  · intro h hz
    simp [hz] at h
  · intro hz
    have hn : 0 < ‖z-P₀ z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    constructor
    · have hm := mul_lt_mul_of_pos_right (by nlinarith : a^2<a) hn
      linarith only [hm]
    · have hm := mul_lt_of_lt_one_left hn ha_lt
      linarith only [hm]

theorem scalar_norms_equal (z : Reconstructed p r hp hp1 hr hr1) (hz : z-P₀ z=0)
    (ω : Q → ℝ) (t : ℝ) :
    ‖transfer p r hp hp1 hr hr1 a ω t z‖^2 = ‖z‖^2 ∧
    ‖sameHistory p r a hp hp1 hr hr1 ha ha1 z‖^2 = ‖z‖^2 := by
  rw [transfer_norm_sq,sameHistory_norm_sq,scalar_pythagoras p r hp hp1 hr hr1 z]
  simp [hz]

theorem all_eight_inserted_norms (i : Fin 8) :
    ‖sameHistory p r a hp hp1 hr hr1 ha ha1 (centeredVector p r hp hp1 hr hr1 i)‖^2 =
      a*modeNorm i*p^2 := by
  rw [sameHistory_norm_sq,scalar_centered]
  simp only [norm_zero,zero_pow (by decide : 2≠0),sub_zero,zero_add]
  change a*‖mk K₀ hK₀ (innerMode i)‖^2=_
  rw [innerMode_norm_sq]
  ring

theorem all_eight_strict (hp0 : 0 < p) (ha0 : 0 < a) (ha_lt : a < 1)
    (ω : Q → ℝ) (t : ℝ) (i : Fin 8) :
    ‖transfer p r hp hp1 hr hr1 a ω t (centeredVector p r hp hp1 hr hr1 i)‖^2 <
      ‖sameHistory p r a hp hp1 hr hr1 ha ha1 (centeredVector p r hp hp1 hr hr1 i)‖^2 ∧
    ‖sameHistory p r a hp hp1 hr hr1 ha ha1 (centeredVector p r hp hp1 hr hr1 i)‖^2 <
      ‖centeredVector p r hp hp1 hr hr1 i‖^2 := by
  apply (full_inserted_strict_iff p r a hp hp1 hr hr1 ha ha1 ha0 ha_lt ω t _).mpr
  rw [scalar_centered,sub_zero]
  exact centered_nonzero p r hp hp1 hr hr1 hp0 i

theorem operational_reset_centered (hz : a=0) (ω : Q → ℝ) (t : ℝ) (i : Fin 8) :
    transfer p r hp hp1 hr hr1 a ω t (centeredVector p r hp hp1 hr hr1 i)=0 ∧
    sameHistory p r a hp hp1 hr hr1 ha ha1 (centeredVector p r hp hp1 hr hr1 i)=0 := by
  subst a
  constructor
  · apply norm_eq_zero.mp
    have h := transfer_centered_norm_sq p r hp hp1 hr hr1 0 ω t i
    nlinarith [sq_nonneg ‖transfer p r hp hp1 hr hr1 0 ω t (centeredVector p r hp hp1 hr hr1 i)‖]
  · apply norm_eq_zero.mp
    have h := all_eight_inserted_norms p r 0 hp hp1 hr hr1 ha ha1 i
    nlinarith [sq_nonneg ‖sameHistory p r 0 hp hp1 hr hr1 ha ha1 (centeredVector p r hp hp1 hr hr1 i)‖]



theorem centered_matrix_norm_sq (A : MatQ) (hA : mean A=0) :
    ‖represent p r hp hp1 hr hr1 A‖^2 = p^2*(form A A).re := by
  rw [@norm_sq_eq_re_inner ℂ,coordinates_inner,represent_coordinates]
  have hm : (rhoN*A).trace=0 := hA
  have he : Psi p A=(p:ℂ) • A := by simp [Psi,hm]
  rw [he,form_smul]
  change (star (p:ℂ)*(p:ℂ)*form A A).re=p^2*(form A A).re
  simp only [Complex.star_def,Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero]
  ring

theorem centered_matrix_scalar (A : MatQ) (hA : mean A=0) :
    P₀ (represent p r hp hp1 hr hr1 A)=0 := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [scalar_coordinates,represent_coordinates,map_zero]
  simp [scalarPart,mean_Psi,hA]

theorem centered_matrix_nonzero (hp0 : 0 < p) (A : MatQ) (hA : mean A=0) (hne : A≠0) :
    represent p r hp hp1 hr hr1 A≠0 := by
  intro hz
  have he := congrArg (coordinates p r hp hp1 hr hr1) hz
  rw [represent_coordinates,map_zero] at he
  have hpC : (p:ℂ)≠0 := by exact_mod_cast ne_of_gt hp0
  have hm : (rhoN*A).trace=0 := hA
  have hs : Psi p A=(p:ℂ) • A := by simp [Psi,hm]
  rw [hs] at he
  exact hne ((smul_eq_zero.mp he).resolve_left hpC)

/-- ER1 for every nonzero centered matrix, beyond the eight named consumers. -/
theorem every_centered_strict (hp0 : 0 < p) (ha0 : 0 < a) (ha_lt : a < 1)
    (A : MatQ) (hA : mean A=0) (hne : A≠0) :
    p^2*a^2*(form A A).re < p^2*a*(form A A).re ∧
    p^2*a*(form A A).re < p^2*(form A A).re := by
  have hn : 0 < ‖represent 1 1 (by norm_num) le_rfl (by norm_num) le_rfl A‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (centered_matrix_nonzero 1 1 (by norm_num) le_rfl
      (by norm_num) le_rfl (by norm_num) A hA hne))
  rw [centered_matrix_norm_sq 1 1 (by norm_num) le_rfl (by norm_num) le_rfl A hA] at hn
  have hpn : 0 < p^2*(form A A).re := mul_pos (sq_pos_of_pos hp0) (by simpa using hn)
  have h1 := mul_lt_mul_of_pos_right (by nlinarith : a^2<a) hpn
  have h2 := mul_lt_of_lt_one_left hpn ha_lt
  constructor <;> nlinarith only [h1,h2]


end InsertionMap


theorem thermal_half_square (γ t : ℝ) :
    Real.exp (-γ*(t/2))^2=Real.exp (-γ*t) := by
  rw [pow_two,← Real.exp_add]
  congr 1
  ring

theorem positive_dose (γ t : ℝ) (hdose : 0 < γ*t) :
    0 < Real.exp (-γ*t) ∧ Real.exp (-γ*t)<1 := by
  refine ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr ?_⟩
  nlinarith

theorem finite_time_not_operational_reset (γ t : ℝ) : Real.exp (-γ*t)≠0 :=
  ne_of_gt (Real.exp_pos _)

theorem zero_dose_retention (γ t : ℝ) (hz : γ=0 ∨ t=0) : Real.exp (-γ*t)=1 := by
  rcases hz with h|h <;> simp [h]

theorem thermal_half_inserted_norm (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (z : Reconstructed p r hp hp1 hr hr1) :
    ‖sameHistory p r (Real.exp (-γ*t)) hp hp1 hr hr1 (Real.exp_pos _).le
      (GibbsReset.exp_rate_le_one γ t hγ ht) z‖ =
    ‖transfer p r hp hp1 hr hr1 (Real.exp (-γ*(t/2)))
      (FiniteThreeLevelThermalPhase.frequencies b ℏ) (t/2) z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [sameHistory_norm_sq,transfer_norm_sq,thermal_half_square]

theorem zero_dose_norms (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hz : γ=0 ∨ t=0) (z : Reconstructed p r hp hp1 hr hr1) :
    ‖transfer p r hp hp1 hr hr1 (Real.exp (-γ*t)) (FiniteThreeLevelThermalPhase.frequencies b ℏ) t z‖^2=‖z‖^2 ∧
    ‖sameHistory p r (Real.exp (-γ*t)) hp hp1 hr hr1 (Real.exp_pos _).le
      (GibbsReset.exp_rate_le_one γ t hγ ht) z‖^2=‖z‖^2 := by
  rw [transfer_norm_sq,sameHistory_norm_sq,zero_dose_retention γ t hz]
  simp only [one_pow,one_mul]
  exact ⟨(scalar_pythagoras p r hp hp1 hr hr1 z).symm,
    (scalar_pythagoras p r hp hp1 hr hr1 z).symm⟩


theorem heisenberg_compose {m n : ℕ} (L : Fin m → MatQ) (K : Fin n → MatQ) (A : MatQ) :
    Channel.heisenberg (composeKraus L K) A =
      Channel.heisenberg K (Channel.heisenberg L A) := by
  unfold Channel.heisenberg composeKraus
  rw [finProdFinEquiv.symm.sum_comp
    (fun q : Fin m × Fin n => (L q.1*K q.2)ᴴ*A*(L q.1*K q.2)),Fintype.sum_prod_type]
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [Finset.sum_comm]

def pulseKraus (ω : Q → ℝ) (t : ℝ) : Fin 1 → MatQ :=
  fun _ => GibbsHamiltonianRelaxation.unitary ω t

theorem pulse_normalized (ω : Q → ℝ) (t : ℝ) : IsKrausChannel (pulseKraus ω t) := by
  simp only [IsKrausChannel,pulseKraus,Fin.sum_univ_one,GibbsHamiltonianRelaxation.unitary_adjoint]
  simpa using GibbsHamiltonianRelaxation.unitary_cancel ω (-t)

theorem pulse_state (ω : Q → ℝ) (t : ℝ) (A : MatQ) :
    krausMap (pulseKraus ω t) A = rotate ω (-t) A := by
  simp only [krausMap,pulseKraus,Fin.sum_univ_one]
  exact (GibbsHamiltonianRelaxation.rotation_sandwich ω t A).symm

theorem pulse_observable (ω : Q → ℝ) (t : ℝ) (A : MatQ) :
    Channel.heisenberg (pulseKraus ω t) A = rotate ω t A := by
  simp only [Channel.heisenberg,pulseKraus,Fin.sum_univ_one,GibbsHamiltonianRelaxation.unitary_adjoint]
  have he := GibbsHamiltonianRelaxation.rotation_sandwich ω (-t) A
  simpa only [neg_neg,GibbsHamiltonianRelaxation.unitary_adjoint,rotate,LinearMap.coe_mk,AddHom.coe_mk] using he.symm

/-- Operational pulse and reset, distinct from a fixed thermal elapsed time. -/
def pulseResetKraus (a : ℝ) (ω : Q → ℝ) (t : ℝ) :=
  composeKraus (pulseKraus ω t) (channel a)

theorem pulseReset_normalized (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    IsKrausChannel (pulseResetKraus a ω t) :=
  isKrausChannel_composeKraus (pulse_normalized ω t) (channel_normalized ha ha1)

theorem pulseReset_state (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) (A : MatQ) :
    krausMap (pulseResetKraus a ω t) A = rotate ω (-t) (Phi a A) := by
  rw [pulseResetKraus,krausMap_composeKraus,channel_state ha ha1,pulse_state]

theorem pulseReset_observable (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) (A : MatQ) :
    Channel.heisenberg (pulseResetKraus a ω t) A = rotate ω t (Psi a A) := by
  rw [pulseResetKraus,heisenberg_compose,pulse_observable,channel_observable ha ha1,rotate_Psi]

theorem pulseReset_commutes (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t q : ℝ) (A : MatQ) :
    Channel.heisenberg (pulseResetKraus a ω t) (Psi q A) =
      Psi q (Channel.heisenberg (pulseResetKraus a ω t) A) := by
  simp only [pulseReset_observable a ha ha1,rotate_Psi,Psi_comp]
  rw [mul_comm a q]

def phaseKernel (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    Matrix HalfHistory HalfHistory ℂ :=
  evolutionKernel (pulseResetKraus a ω t) (pulseReset_normalized a ha ha1 ω t) p r hp hp1 hr hr1

theorem phaseKernel_form (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (u v : HalfHistory) :
    phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t u v =
      form (FiniteThreeLevelPositiveHistory.midpoint p r u)
        (rotate ω t (Psi a (FiniteThreeLevelPositiveHistory.midpoint p r v))) := by
  rw [phaseKernel,evolutionKernel_form _ _ _ _ _ _ _ _ (pulseReset_commutes a ha ha1 ω t p),
    pulseReset_observable a ha ha1]

theorem form_sum_left {ι : Type*} [Fintype ι] (A : ι → MatQ) (B : MatQ) :
    form (∑ i,A i) B=∑ i,form (A i) B := by
  simp [form,Matrix.conjTranspose_sum,Matrix.mul_sum,Matrix.sum_mul,Matrix.trace_sum]
theorem form_sum_right {ι : Type*} [Fintype ι] (A : MatQ) (B : ι → MatQ) :
    form A (∑ i,B i)=∑ i,form A (B i) := by
  simp [form,Matrix.sum_mul,Matrix.trace_sum]

theorem pairing_from_form (K : Matrix HalfHistory HalfHistory ℂ) (M : HalfHistory → MatQ)
    (O : MatQ →ₗ[ℂ] MatQ) (hK : ∀ u v,K u v=form (M u) (O (M v))) (F G : HalfHistory → ℂ) :
    pairing K F G=form (∑ u,F u • M u) (O (∑ v,G v • M v)) := by
  simp only [pairing,dotProduct,Matrix.mulVec,hK,map_sum,map_smul,
    form_sum_left,form_sum_right,form_smul,Finset.mul_sum,Pi.star_apply]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem phaseKernel_pairing (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (F G : HalfHistory → ℂ) :
    pairing (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t) F G =
      form (synthesis p r F) (rotate ω t (Psi a (synthesis p r G))) :=
  pairing_from_form _ _ ((rotate ω t).comp (PsiLinear a))
    (phaseKernel_form p r a hp hp1 hr hr1 ha ha1 ω t) F G

theorem phaseKernel_old_inner (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (F G : HalfHistory → ℂ) :
    pairing (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t) F G =
      ⟪mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1)
          (kernel_posSemidef p r hp hp1 hr hr1) F,
        transfer p r hp hp1 hr hr1 a ω t
          (mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1)
            (kernel_posSemidef p r hp hp1 hr hr1) G)⟫_ℂ := by
  rw [coordinates_inner,transfer_coordinates,coordinates_mk,coordinates_mk,phaseKernel_pairing]

theorem phaseKernel_total (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    ∑ u,∑ v,phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t u v=1 := by
  have he := phaseKernel_pairing p r a hp hp1 hr hr1 ha ha1 ω t (fun _ => 1) (fun _ => 1)
  rw [synthesis_constant,Psi_unital,rotate_one,form_one] at he
  simpa [pairing,dotProduct,Matrix.mulVec] using he


def multiplier (ω : Q → ℝ) (t : ℝ) (i j : Q) : ℂ :=
  Complex.exp (Complex.I*t*((ω i:ℂ)-ω j))

theorem multiplier_diag (ω : Q → ℝ) (t : ℝ) (i : Q) : multiplier ω t i i=1 := by
  simp [multiplier]
theorem multiplier_norm (ω : Q → ℝ) (t : ℝ) (i j : Q) : ‖multiplier ω t i j‖=1 := by
  simp [multiplier,Complex.norm_exp,Complex.mul_re,Complex.sub_re,Complex.mul_im]
theorem multiplier_reverse (ω : Q → ℝ) (t : ℝ) (i j : Q) :
    multiplier ω (-t) i j=star (multiplier ω t i j) := by
  simp only [multiplier,Complex.star_def,← Complex.exp_conj,map_mul,map_sub,
    Complex.conj_I,Complex.conj_ofReal,Complex.ofReal_neg]
  congr 1
  ring

theorem rotate_unit (ω : Q → ℝ) (t : ℝ) (i j : Q) :
    rotate ω t (E i j)=multiplier ω t i j • E i j :=
  GibbsHamiltonianRelaxation.rotation_single ω t i j

theorem observable_unit (a : ℝ) (ω : Q → ℝ) (t : ℝ) (z : ℂ) {i j : Q} (hij : i≠j) :
    rotate ω t (Psi a (z • E i j))=((a:ℂ)*z*multiplier ω t i j) • E i j := by
  rw [Psi_smul]
  have he : Psi a (E i j)=(a:ℂ) • E i j := by simp [Psi,matrixUnit_mean hij]
  rw [he,map_smul,map_smul,rotate_unit,smul_smul,smul_smul]
  congr 1
  ring

theorem phaseKernel_probe (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (z w : ℂ) {i j : Q} (hij : i≠j) :
    pairing (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t) (complexProbe z i j) (complexProbe w i j) =
      star z*w*((a*p^2*metricWeight i j:ℝ):ℂ)*multiplier ω t i j := by
  rw [phaseKernel_pairing,synthesis_complexProbe p r z hij,synthesis_complexProbe p r w hij,
    observable_unit a ω t _ hij,form_smul,matrixUnit_form]
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

theorem hermitian_pairing_conj {ι : Type*} [Fintype ι] {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (F G : ι → ℂ) : star (pairing K G F)=pairing K F G := by
  unfold pairing
  rw [← star_dotProduct,star_mulVec,hK.eq,dotProduct_mulVec]

theorem metricWeight_positive (i j : Q) : 0 < metricWeight i j := by
  rw [← rdiag_product]
  exact mul_pos (rdiag_pos i) (rdiag_pos j)

theorem phaseKernel_hermitian_necessary (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hp0 : 0 < p) (ha0 : 0 < a)
    (hK : (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t).IsHermitian) :
    ∀ i j,(multiplier ω t i j).im=0 := by
  intro i j
  by_cases hij : i=j
  · subst j; simp [multiplier_diag]
  · have he := hermitian_pairing_conj hK (complexProbe 1 i j) (complexProbe 1 i j)
    rw [phaseKernel_probe p r a hp hp1 hr hr1 ha ha1 ω t 1 1 hij] at he
    have hi := congrArg Complex.im he
    simp only [star_one,one_mul,Complex.star_def,Complex.conj_im,Complex.mul_im,
      Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero] at hi
    have hc : 0 < a*p^2*metricWeight i j :=
      mul_pos (mul_pos ha0 (sq_pos_of_pos hp0)) (metricWeight_positive i j)
    nlinarith

theorem form_conj (A B : MatQ) : star (form B A)=form A B := by
  simp only [form,← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,R_adjoint,
    Matrix.conjTranspose_conjTranspose]
  simp only [← Matrix.mul_assoc]
  calc
    (R*B*R*Aᴴ).trace=(R*(B*R*Aᴴ)).trace := by simp only [Matrix.mul_assoc]
    _ = (B*R*Aᴴ*R).trace := Matrix.trace_mul_comm _ _

theorem rotate_form_adjoint (ω : Q → ℝ) (t : ℝ) (A B : MatQ) :
    form (rotate ω t A) B=form A (rotate ω (-t) B) := by
  have he := rotate_form ω t A (rotate ω (-t) B)
  rw [rotate_group,add_neg_cancel,rotate_zero] at he
  exact he

theorem rotate_reverse_of_real (ω : Q → ℝ) (t : ℝ)
    (hreal : ∀ i j,(multiplier ω t i j).im=0) (A : MatQ) :
    rotate ω (-t) A=rotate ω t A := by
  ext i j
  rw [rotate_entry,rotate_entry]
  change multiplier ω (-t) i j*A i j=multiplier ω t i j*A i j
  rw [multiplier_reverse]
  have he : star (multiplier ω t i j)=multiplier ω t i j :=
    Complex.conj_eq_iff_im.mpr (hreal i j)
  rw [he]

theorem phaseKernel_hermitian_sufficient (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hreal : ∀ i j,(multiplier ω t i j).im=0) :
    (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro u v
  rw [phaseKernel_form,phaseKernel_form,form_conj,rotate_form_adjoint,← form_Psi_symmetric,
    ← rotate_Psi,rotate_reverse_of_real ω t hreal]

theorem phaseKernel_hermitian_iff (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hp0 : 0 < p) (ha0 : 0 < a) :
    (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t).IsHermitian ↔
      ∀ i j,(multiplier ω t i j).im=0 :=
  ⟨phaseKernel_hermitian_necessary p r a hp hp1 hr hr1 ha ha1 ω t hp0 ha0,
    phaseKernel_hermitian_sufficient p r a hp hp1 hr hr1 ha ha1 ω t⟩

theorem inserted_form (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (u v : HalfHistory) :
    insertedKernel p r a hp hp1 hr hr1 ha ha1 u v =
      form (FiniteThreeLevelPositiveHistory.midpoint p r u)
        (Psi a (FiniteThreeLevelPositiveHistory.midpoint p r v)) := by
  rw [insertedKernel,evolutionKernel_form]
  · rw [channel_observable ha ha1]
  · intro A
    rw [channel_observable ha ha1,channel_observable ha ha1,Psi_comp,Psi_comp,mul_comm a p]

theorem phaseKernel_positive_sufficient (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hone : ∀ i j,multiplier ω t i j=1) :
    (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t).PosSemidef := by
  have he : ∀ A,rotate ω t A=A := by
    intro A
    ext i j
    rw [rotate_entry]
    change multiplier ω t i j*A i j=A i j
    rw [hone,one_mul]
  have hk : phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t=insertedKernel p r a hp hp1 hr hr1 ha ha1 := by
    ext u v
    rw [phaseKernel_form,inserted_form,he]
  rw [hk]
  exact inserted_positive p r a hp hp1 hr hr1 ha ha1

theorem phaseKernel_positive_necessary (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hp0 : 0 < p) (ha0 : 0 < a)
    (hK : (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t).PosSemidef) :
    ∀ i j,multiplier ω t i j=1 := by
  intro i j
  by_cases hij : i=j
  · subst j; exact multiplier_diag ω t i
  · have hi := phaseKernel_hermitian_necessary p r a hp hp1 hr hr1 ha ha1 ω t hp0 ha0 hK.isHermitian i j
    have hn := hK.dotProduct_mulVec_nonneg (complexProbe 1 i j)
    change 0 ≤ pairing (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t) (complexProbe 1 i j) (complexProbe 1 i j) at hn
    rw [phaseKernel_probe p r a hp hp1 hr hr1 ha ha1 ω t 1 1 hij] at hn
    have hnr := hn.1
    simp only [star_one,one_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,Complex.zero_re] at hnr
    have hc : 0 < a*p^2*metricWeight i j :=
      mul_pos (mul_pos ha0 (sq_pos_of_pos hp0)) (metricWeight_positive i j)
    have hr : 0 ≤ (multiplier ω t i j).re := by nlinarith
    have he : multiplier ω t i j=((multiplier ω t i j).re:ℂ) := by
      apply Complex.ext <;> simp [hi]
    have hm := multiplier_norm ω t i j
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr] at hm
    rw [he,hm,Complex.ofReal_one]

theorem phaseKernel_positive_iff (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hp0 : 0 < p) (ha0 : 0 < a) :
    (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t).PosSemidef ↔
      ∀ i j,multiplier ω t i j=1 :=
  ⟨phaseKernel_positive_necessary p r a hp hp1 hr hr1 ha ha1 ω t hp0 ha0,
    phaseKernel_positive_sufficient p r a hp hp1 hr hr1 ha ha1 ω t⟩


def angle (ω : Q → ℝ) (t : ℝ) (i j : Q) : ℝ := t*(ω j-ω i)

theorem angle_reverse (ω : Q → ℝ) (t : ℝ) (i j : Q) :
    angle ω t j i = -angle ω t i j := by unfold angle; ring

theorem multiplier_euler (ω : Q → ℝ) (t : ℝ) (i j : Q) :
    multiplier ω t i j=(Real.cos (angle ω t i j):ℂ)-Complex.I*(Real.sin (angle ω t i j):ℂ) := by
  rw [multiplier,show Complex.I*t*((ω i:ℂ)-ω j)=((-angle ω t i j:ℝ):ℂ)*Complex.I by
    simp only [angle,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_sub]; ring,
    Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
  ring

theorem phaseKernel_hermitian_sines (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hp0 : 0 < p) (ha0 : 0 < a) :
    (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t).IsHermitian ↔
      ∀ i j,Real.sin (angle ω t i j)=0 := by
  rw [phaseKernel_hermitian_iff p r a hp hp1 hr hr1 ha ha1 ω t hp0 ha0]
  simp only [multiplier_euler,Complex.sub_im,Complex.ofReal_im,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add,zero_sub,neg_eq_zero]

theorem observable_X (a : ℝ) (ω : Q → ℝ) (t : ℝ) {i j : Q} (hij : i≠j) :
    rotate ω t (Psi a (X i j)) = (a:ℂ) •
      ((Real.cos (angle ω t i j):ℂ) • X i j+(Real.sin (angle ω t i j):ℂ) • Y i j) := by
  rw [X,Psi_add,map_add]
  have h1 := observable_unit a ω t 1 hij
  have h2 := observable_unit a ω t 1 hij.symm
  simp only [one_smul,mul_one] at h1 h2
  rw [h1,h2,multiplier_euler,multiplier_euler,angle_reverse]
  simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg,Y]
  module

theorem observable_Y (a : ℝ) (ω : Q → ℝ) (t : ℝ) {i j : Q} (hij : i≠j) :
    rotate ω t (Psi a (Y i j)) = (a:ℂ) •
      (-(Real.sin (angle ω t i j):ℂ) • X i j+(Real.cos (angle ω t i j):ℂ) • Y i j) := by
  rw [Y,Psi_add,map_add]
  rw [observable_unit a ω t (-Complex.I) hij,observable_unit a ω t Complex.I hij.symm,
    multiplier_euler,multiplier_euler,angle_reverse]
  simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg,X]
  ext k l
  simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem observable_centered_diagonal (a : ℝ) (ω : Q → ℝ) (t : ℝ) (i : Fin 2) :
    rotate ω t (Psi a (modeMatrix (i.castLE (by decide : 2 ≤ 8))))=(a:ℂ) • modeMatrix (i.castLE (by decide : 2 ≤ 8)) := by
  have he : Psi a (modeMatrix (i.castLE (by decide : 2 ≤ 8)))=(a:ℂ) • modeMatrix (i.castLE (by decide : 2 ≤ 8)) := by
    simp [Psi,mode_mean_zero]
  rw [he,map_smul]
  congr 1
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [rotate_entry,modeMatrix,Z1,Z2,Matrix.cons_val]

theorem pulseReset_complex_state (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ω : Q → ℝ) (t : ℝ) (z : ℂ) {i j : Q} (hij : i≠j) :
    krausMap (pulseResetKraus a ω t) (z • E i j) =
      ((a:ℂ)*z*star (multiplier ω t i j)) • E i j := by
  rw [pulseReset_state a ha ha1]
  have he : (E i j).trace=0 := by simp [E,Matrix.trace,Matrix.single,hij.symm]
  simp only [Phi,Matrix.trace_smul,he,smul_eq_mul,mul_zero,zero_smul,smul_zero,add_zero]
  rw [map_smul,map_smul,rotate_unit,multiplier_reverse,smul_smul,smul_smul]

theorem thermal_observable_matrix (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (A : MatQ) :
    Channel.heisenberg (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) A =
      rotate (FiniteThreeLevelThermalPhase.frequencies b ℏ) t (Psi (Real.exp (-γ*t)) A) := by
  rw [FiniteThreeLevelEnvironmentLift.channel_observable_action b ℏ γ t hγ ht]
  simp only [Psi,map_add,map_smul,rotate_one]
  simp [rotate,FiniteThreeLevelThermalPhase.phase,Complex.ofReal_sub]

theorem thermal_state_pulse (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (A : MatQ) :
    krausMap (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) A =
      krausMap (pulseResetKraus (Real.exp (-γ*t)) (FiniteThreeLevelThermalPhase.frequencies b ℏ) t) A := by
  rw [FiniteThreeLevelThermalPhase.channel_action b ℏ γ t hγ ht,
    pulseReset_state _ (Real.exp_pos _).le (GibbsReset.exp_rate_le_one γ t hγ ht),
    FiniteThreeLevelThermalPhase.reset_action γ t hγ ht]
  simp only [Phi,rhoN,Complex.ofReal_sub,Complex.ofReal_one]
  rfl

def gap01 (b ℏ t : ℝ) := t*FiniteThreeLevelThermalPhase.delta/(b*ℏ)
def gap02 (b ℏ t : ℝ) := t*Real.log 3/(b*ℏ)
def gap12 (b ℏ t : ℝ) := t*Real.log 2/(b*ℏ)

theorem logarithmic_gap : Real.log 3-FiniteThreeLevelThermalPhase.delta=Real.log 2 := by
  rw [FiniteThreeLevelThermalPhase.delta,Real.log_div (by norm_num) (by norm_num)]
  ring

theorem angle01 (b ℏ t : ℝ) :
    angle (FiniteThreeLevelThermalPhase.frequencies b ℏ) t 0 1=gap01 b ℏ t := by
  simp only [angle,FiniteThreeLevelThermalPhase.frequencies,FiniteThreeLevelThermalPhase.energies,
    Matrix.cons_val,gap01,div_eq_mul_inv,_root_.mul_inv_rev]
  ring
theorem angle02 (b ℏ t : ℝ) :
    angle (FiniteThreeLevelThermalPhase.frequencies b ℏ) t 0 2=gap02 b ℏ t := by
  simp only [angle,FiniteThreeLevelThermalPhase.frequencies,FiniteThreeLevelThermalPhase.energies,
    Matrix.cons_val,gap02,div_eq_mul_inv,_root_.mul_inv_rev]
  ring
theorem angle12 (b ℏ t : ℝ) :
    angle (FiniteThreeLevelThermalPhase.frequencies b ℏ) t 1 2=gap12 b ℏ t := by
  simp only [angle,FiniteThreeLevelThermalPhase.frequencies,FiniteThreeLevelThermalPhase.energies,
    Matrix.cons_val]
  rw [← sub_div,← sub_div,logarithmic_gap]
  simp only [gap12,div_eq_mul_inv,_root_.mul_inv_rev]
  ring
theorem gaps_tied (b ℏ t : ℝ) : gap12 b ℏ t=gap02 b ℏ t-gap01 b ℏ t := by
  unfold gap12 gap02 gap01
  rw [← sub_div,← mul_sub,logarithmic_gap]

theorem multiplier_angle (ω : Q → ℝ) (t : ℝ) (i j : Q) :
    multiplier ω t i j=Complex.exp (-Complex.I*(angle ω t i j:ℂ)) := by
  unfold multiplier angle
  congr 1
  push_cast
  ring

theorem thermal_complex_observable (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (z : ℂ) {i j : Q} (hij : i≠j) :
    Channel.heisenberg (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) (z • E i j) =
      ((Real.exp (-γ*t):ℂ)*z*Complex.exp (-Complex.I*
        (angle (FiniteThreeLevelThermalPhase.frequencies b ℏ) t i j:ℂ))) • E i j := by
  rw [thermal_observable_matrix b ℏ γ t hγ ht,observable_unit _ _ _ z hij,multiplier_angle]

theorem thermal_complex_state (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (z : ℂ) {i j : Q} (hij : i≠j) :
    krausMap (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) (z • E i j) =
      ((Real.exp (-γ*t):ℂ)*z*Complex.exp (Complex.I*
        (angle (FiniteThreeLevelThermalPhase.frequencies b ℏ) t i j:ℂ))) • E i j := by
  rw [thermal_state_pulse b ℏ γ t hγ ht,pulseReset_complex_state _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one γ t hγ ht) _ _ z hij,multiplier_angle]
  simp only [Complex.star_def,← Complex.exp_conj,map_mul,map_neg,Complex.conj_I,
    Complex.conj_ofReal,neg_neg]



theorem quotient_complex_probe (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ω : Q → ℝ) (t : ℝ) (z : ℂ) {i j : Q} (hij : i≠j) :
    transfer p r hp hp1 hr hr1 a ω t
      (mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)
        (complexProbe z i j)) =
    ((a:ℂ)*Complex.exp (-Complex.I*(angle ω t i j:ℂ))) •
      mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)
        (complexProbe z i j) := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [transfer_coordinates,map_smul,coordinates_mk,synthesis_complexProbe p r z hij,
    observable_unit a ω t _ hij,multiplier_angle,smul_smul]
  congr 1
  ring

theorem thermal_observable_01 (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (z : ℂ) :
    Channel.heisenberg (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) (z • E 0 1) =
      ((Real.exp (-γ*t):ℂ)*z*Complex.exp (-Complex.I*(gap01 b ℏ t:ℂ))) • E 0 1 := by
  simpa only [angle01] using thermal_complex_observable b ℏ γ t hγ ht z (by decide : (0:Q)≠1)

theorem thermal_state_01 (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (z : ℂ) :
    krausMap (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) (z • E 0 1) =
      ((Real.exp (-γ*t):ℂ)*z*Complex.exp (Complex.I*(gap01 b ℏ t:ℂ))) • E 0 1 := by
  simpa only [angle01] using thermal_complex_state b ℏ γ t hγ ht z (by decide : (0:Q)≠1)

theorem thermal_quotient_01 (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (b ℏ γ t : ℝ) (z : ℂ) :
    transfer p r hp hp1 hr hr1 (Real.exp (-γ*t)) (FiniteThreeLevelThermalPhase.frequencies b ℏ) t
      (mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)
        (complexProbe z 0 1)) =
    ((Real.exp (-γ*t):ℂ)*Complex.exp (-Complex.I*(gap01 b ℏ t:ℂ))) •
      mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)
        (complexProbe z 0 1) := by
  simpa only [angle01] using quotient_complex_probe p r (Real.exp (-γ*t)) hp hp1 hr hr1
    (FiniteThreeLevelThermalPhase.frequencies b ℏ) t z (by decide : (0:Q)≠1)

theorem thermal_observable_02 (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (z : ℂ) :
    Channel.heisenberg (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) (z • E 0 2) =
      ((Real.exp (-γ*t):ℂ)*z*Complex.exp (-Complex.I*(gap02 b ℏ t:ℂ))) • E 0 2 := by
  simpa only [angle02] using thermal_complex_observable b ℏ γ t hγ ht z (by decide : (0:Q)≠2)

theorem thermal_state_02 (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (z : ℂ) :
    krausMap (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) (z • E 0 2) =
      ((Real.exp (-γ*t):ℂ)*z*Complex.exp (Complex.I*(gap02 b ℏ t:ℂ))) • E 0 2 := by
  simpa only [angle02] using thermal_complex_state b ℏ γ t hγ ht z (by decide : (0:Q)≠2)

theorem thermal_quotient_02 (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (b ℏ γ t : ℝ) (z : ℂ) :
    transfer p r hp hp1 hr hr1 (Real.exp (-γ*t)) (FiniteThreeLevelThermalPhase.frequencies b ℏ) t
      (mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)
        (complexProbe z 0 2)) =
    ((Real.exp (-γ*t):ℂ)*Complex.exp (-Complex.I*(gap02 b ℏ t:ℂ))) •
      mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)
        (complexProbe z 0 2) := by
  simpa only [angle02] using quotient_complex_probe p r (Real.exp (-γ*t)) hp hp1 hr hr1
    (FiniteThreeLevelThermalPhase.frequencies b ℏ) t z (by decide : (0:Q)≠2)

theorem thermal_observable_12 (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (z : ℂ) :
    Channel.heisenberg (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) (z • E 1 2) =
      ((Real.exp (-γ*t):ℂ)*z*Complex.exp (-Complex.I*(gap12 b ℏ t:ℂ))) • E 1 2 := by
  simpa only [angle12] using thermal_complex_observable b ℏ γ t hγ ht z (by decide : (1:Q)≠2)

theorem thermal_state_12 (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (z : ℂ) :
    krausMap (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) (z • E 1 2) =
      ((Real.exp (-γ*t):ℂ)*z*Complex.exp (Complex.I*(gap12 b ℏ t:ℂ))) • E 1 2 := by
  simpa only [angle12] using thermal_complex_state b ℏ γ t hγ ht z (by decide : (1:Q)≠2)

theorem thermal_quotient_12 (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (b ℏ γ t : ℝ) (z : ℂ) :
    transfer p r hp hp1 hr hr1 (Real.exp (-γ*t)) (FiniteThreeLevelThermalPhase.frequencies b ℏ) t
      (mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)
        (complexProbe z 1 2)) =
    ((Real.exp (-γ*t):ℂ)*Complex.exp (-Complex.I*(gap12 b ℏ t:ℂ))) •
      mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)
        (complexProbe z 1 2) := by
  simpa only [angle12] using quotient_complex_probe p r (Real.exp (-γ*t)) hp hp1 hr hr1
    (FiniteThreeLevelThermalPhase.frequencies b ℏ) t z (by decide : (1:Q)≠2)


def thermalKernel (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    Matrix HalfHistory HalfHistory ℂ :=
  evolutionKernel (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t)
    (FiniteThreeLevelThermalPhase.channel_normalized b ℏ γ t hγ ht) p r hp hp1 hr hr1

theorem thermalKernel_eq_phase (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    thermalKernel p r hp hp1 hr hr1 b ℏ γ t hγ ht =
      phaseKernel p r (Real.exp (-γ*t)) hp hp1 hr hr1 (Real.exp_pos _).le
        (GibbsReset.exp_rate_le_one γ t hγ ht) (FiniteThreeLevelThermalPhase.frequencies b ℏ) t := by
  ext u v
  rw [thermalKernel,phaseKernel,evolutionKernel_trace,evolutionKernel_trace,thermal_state_pulse b ℏ γ t hγ ht]

theorem thermalKernel_operator (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (F G : HalfHistory → ℂ) :
    pairing (thermalKernel p r hp hp1 hr hr1 b ℏ γ t hγ ht) F G =
      form (synthesis p r F) (Channel.heisenberg
        (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) (synthesis p r G)) := by
  rw [thermalKernel_eq_phase,phaseKernel_pairing,thermal_observable_matrix b ℏ γ t hγ ht]

theorem rotate_equilibrium (ω : Q → ℝ) (t : ℝ) : rotate ω t rhoN=rhoN := rotate_diagonal ω t _

theorem phaseKernel_factored (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (i o j k : Outcome) :
    phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t (i,o) (j,k) =
      (halfCoefficient r i o:ℂ)*(halfCoefficient r j k:ℂ)*
        (((p^2*a:ℝ):ℂ)*(projector j*
          (GibbsHamiltonianRelaxation.unitary ω t*Gamma (projector i)*
            (GibbsHamiltonianRelaxation.unitary ω t)ᴴ)).trace+
          ((1-p^2*a:ℝ):ℂ)*(d i:ℂ)*(d j:ℂ)) := by
  rw [phaseKernel,evolutionKernel_trace,pulseReset_state a ha ha1,Phi_comp]
  rw [halfEffect_factored,halfEffect_factored,Gamma_smul]
  simp only [Phi,Matrix.trace_smul,Gamma_trace,Matrix.trace_mul_comm rhoN (projector i),
    ← d_trace,map_add,map_smul,rotate_equilibrium,mul_add,mul_smul_comm,smul_mul_assoc,
    Matrix.trace_add,Matrix.trace_smul,Matrix.trace_mul_comm (projector j) rhoN,← d_trace]
  have he := GibbsHamiltonianRelaxation.rotation_sandwich ω t (Gamma (projector i))
  change rotate ω (-t) (Gamma (projector i)) = _ at he
  rw [he]
  rw [Matrix.trace_mul_comm rhoN (projector j),← d_trace]
  push_cast
  simp only [smul_eq_mul]
  ring

theorem phaseKernel_reset (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hz : p=0 ∨ a=0) :
    phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t =
      FiniteThreeLevelPositiveHistory.kernel 0 r (by norm_num) (by norm_num) hr hr1 := by
  have he : a*(p*p)=0 := by rcases hz with h|h <;> simp [h]
  ext u v
  rw [phaseKernel,evolutionKernel_trace,pulseReset_state a ha ha1,Phi_comp,he,Phi_zero,
    map_smul,rotate_equilibrium,kernel_trace]
  norm_num [Phi_zero]

theorem phaseKernel_reset_positive (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hz : p=0 ∨ a=0) :
    (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t).PosSemidef := by
  rw [phaseKernel_reset p r a hp hp1 hr hr1 ha ha1 ω t hz]
  exact kernel_posSemidef _ _ _ _ _ _


theorem form_smul_right (A B : MatQ) (z : ℂ) : form A (z • B)=z*form A B := by
  simpa using form_smul 1 z A B
theorem form_add_right (A B C : MatQ) : form A (B+C)=form A B+form A C := by
  simp [form,add_mul,Matrix.trace_add]

theorem phaseKernel_XY01 (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    pairing (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t) (innerMode 2) (innerMode 3) =
      ((-a*p^2*Real.sin (angle ω t 0 1)*Real.sqrt 6/3:ℝ):ℂ) := by
  simp only [phaseKernel_pairing,synthesis_innerMode]
  change form ((p:ℂ) • X 0 1) (rotate ω t (Psi a ((p:ℂ) • Y 0 1)))=_
  rw [Psi_smul,map_smul,form_smul,observable_Y a ω t (by decide : (0:Q)≠1),
    form_smul_right,form_add_right,form_smul_right,form_smul_right]
  have hxx : form (X 0 1) (X 0 1)=(Real.sqrt 6/3:ℂ) := by
    simpa [modeMatrix,modeNorm] using modeMatrix_form 2 2
  have hxy : form (X 0 1) (Y 0 1)=0 := by
    simpa [modeMatrix] using modeMatrix_form 2 3
  rw [hxx,hxy]
  simp only [Complex.star_def,Complex.conj_ofReal]
  push_cast
  ring

theorem phaseKernel_YX01 (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    pairing (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t) (innerMode 3) (innerMode 2) =
      ((a*p^2*Real.sin (angle ω t 0 1)*Real.sqrt 6/3:ℝ):ℂ) := by
  simp only [phaseKernel_pairing,synthesis_innerMode]
  change form ((p:ℂ) • Y 0 1) (rotate ω t (Psi a ((p:ℂ) • X 0 1)))=_
  rw [Psi_smul,map_smul,form_smul,observable_X a ω t (by decide : (0:Q)≠1),
    form_smul_right,form_add_right,form_smul_right,form_smul_right]
  have hyy : form (Y 0 1) (Y 0 1)=(Real.sqrt 6/3:ℂ) := by
    simpa [modeMatrix,modeNorm] using modeMatrix_form 3 3
  have hyx : form (Y 0 1) (X 0 1)=0 := by
    simpa [modeMatrix] using modeMatrix_form 3 2
  rw [hyy,hyx]
  simp only [Complex.star_def,Complex.conj_ofReal]
  push_cast
  ring

theorem phaseKernel_XX01 (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    pairing (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t) (innerMode 2) (innerMode 2) =
      ((a*p^2*Real.cos (angle ω t 0 1)*Real.sqrt 6/3:ℝ):ℂ) := by
  simp only [phaseKernel_pairing,synthesis_innerMode]
  change form ((p:ℂ) • X 0 1) (rotate ω t (Psi a ((p:ℂ) • X 0 1)))=_
  rw [Psi_smul,map_smul,form_smul,observable_X a ω t (by decide : (0:Q)≠1),
    form_smul_right,form_add_right,form_smul_right,form_smul_right]
  have hxx : form (X 0 1) (X 0 1)=(Real.sqrt 6/3:ℂ) := by
    simpa [modeMatrix,modeNorm] using modeMatrix_form 2 2
  have hxy : form (X 0 1) (Y 0 1)=0 := by
    simpa [modeMatrix] using modeMatrix_form 2 3
  rw [hxx,hxy]
  simp only [Complex.star_def,Complex.conj_ofReal]
  push_cast
  ring

/-- Independent controls; their pair difference determines the third free angle. -/
def freeLevels (φ ψ : ℝ) : Q → ℝ := ![0,φ,ψ]

theorem free_angles (φ ψ : ℝ) :
    angle (freeLevels φ ψ) 1 0 1=φ ∧ angle (freeLevels φ ψ) 1 0 2=ψ ∧
      angle (freeLevels φ ψ) 1 1 2=ψ-φ := by simp [angle,freeLevels]

theorem free_quarter_pairings (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    pairing (phaseKernel p r a hp hp1 hr hr1 ha ha1 (freeLevels (Real.pi/2) (Real.pi/2)) 1)
      (innerMode 2) (innerMode 3)=((-a*p^2*Real.sqrt 6/3:ℝ):ℂ) ∧
    pairing (phaseKernel p r a hp hp1 hr hr1 ha ha1 (freeLevels (Real.pi/2) (Real.pi/2)) 1)
      (innerMode 3) (innerMode 2)=((a*p^2*Real.sqrt 6/3:ℝ):ℂ) := by
  rw [phaseKernel_XY01,phaseKernel_YX01,(free_angles _ _).1,Real.sin_pi_div_two]
  simp only [mul_one,and_self]

theorem free_quarter_not_hermitian (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hp0 : 0 < p) (ha0 : 0 < a) :
    ¬ (phaseKernel p r a hp hp1 hr hr1 ha ha1 (freeLevels (Real.pi/2) (Real.pi/2)) 1).IsHermitian := by
  intro h
  have hs := (phaseKernel_hermitian_sines p r a hp hp1 hr hr1 ha ha1 _ _ hp0 ha0).mp h 0 1
  rw [(free_angles _ _).1,Real.sin_pi_div_two] at hs
  norm_num at hs

theorem free_half_hermitian (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (phaseKernel p r a hp hp1 hr hr1 ha ha1 (freeLevels Real.pi Real.pi) 1).IsHermitian := by
  apply phaseKernel_hermitian_sufficient
  intro i j
  rw [multiplier_euler]
  fin_cases i <;> fin_cases j <;> simp [angle,freeLevels]

theorem free_half_negative (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hp0 : 0 < p) (ha0 : 0 < a) :
    (pairing (phaseKernel p r a hp hp1 hr hr1 ha ha1 (freeLevels Real.pi Real.pi) 1)
      (innerMode 2) (innerMode 2)).re = -a*p^2*Real.sqrt 6/3 ∧
    (pairing (phaseKernel p r a hp hp1 hr hr1 ha ha1 (freeLevels Real.pi Real.pi) 1)
      (innerMode 2) (innerMode 2)).re < 0 := by
  rw [phaseKernel_XX01,(free_angles _ _).1,Real.cos_pi]
  simp only [Complex.ofReal_re]
  constructor
  · ring
  · have hs : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
    have hc := mul_pos (mul_pos ha0 (sq_pos_of_pos hp0)) hs
    nlinarith

def quarterTime (b ℏ : ℝ) : ℝ := b*ℏ*Real.pi/(2*FiniteThreeLevelThermalPhase.delta)
def halfTime (b ℏ : ℝ) : ℝ := b*ℏ*Real.pi/FiniteThreeLevelThermalPhase.delta

theorem quarterTime_positive {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ) : 0 < quarterTime b ℏ :=
  div_pos (mul_pos (mul_pos hb hℏ) Real.pi_pos) (mul_pos (by norm_num) FiniteThreeLevelThermalPhase.delta_pos)
theorem halfTime_positive {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ) : 0 < halfTime b ℏ :=
  div_pos (mul_pos (mul_pos hb hℏ) Real.pi_pos) FiniteThreeLevelThermalPhase.delta_pos

theorem quarterTime_angle {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ) :
    gap01 b ℏ (quarterTime b ℏ)=Real.pi/2 := by
  unfold gap01 quarterTime
  field_simp [ne_of_gt hb,ne_of_gt hℏ,ne_of_gt FiniteThreeLevelThermalPhase.delta_pos]
theorem halfTime_angle {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ) :
    gap01 b ℏ (halfTime b ℏ)=Real.pi := by
  unfold gap01 halfTime
  field_simp [ne_of_gt hb,ne_of_gt hℏ,ne_of_gt FiniteThreeLevelThermalPhase.delta_pos]

theorem timed_quarter_not_hermitian (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hp0 : 0 < p) {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ¬ (thermalKernel p r hp hp1 hr hr1 b ℏ γ (quarterTime b ℏ) hγ
      (quarterTime_positive hb hℏ).le).IsHermitian := by
  rw [thermalKernel_eq_phase]
  intro h
  have hs := (phaseKernel_hermitian_sines p r _ hp hp1 hr hr1 _ _ _ _ hp0 (Real.exp_pos _)).mp h 0 1
  rw [angle01,quarterTime_angle hb hℏ,Real.sin_pi_div_two] at hs
  norm_num at hs

/-- The other timed gaps are left untouched; no timed full-kernel Hermiticity is asserted. -/
theorem timed_half_negative (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hp0 : 0 < p) {b ℏ : ℝ} (hb : 0 < b) (hℏ : 0 < ℏ)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    (pairing (thermalKernel p r hp hp1 hr hr1 b ℏ γ (halfTime b ℏ) hγ
      (halfTime_positive hb hℏ).le) (innerMode 2) (innerMode 2)).re =
      -Real.exp (-γ*halfTime b ℏ)*p^2*Real.sqrt 6/3 ∧
    (pairing (thermalKernel p r hp hp1 hr hr1 b ℏ γ (halfTime b ℏ) hγ
      (halfTime_positive hb hℏ).le) (innerMode 2) (innerMode 2)).re < 0 := by
  rw [thermalKernel_eq_phase,phaseKernel_XX01,angle01,halfTime_angle hb hℏ,Real.cos_pi]
  simp only [Complex.ofReal_re]
  constructor
  · ring
  · have hc := mul_pos (mul_pos (Real.exp_pos (-γ*halfTime b ℏ)) (sq_pos_of_pos hp0))
      (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<6))
    nlinarith



theorem qutrit_effect_complex_trace {n : ℕ} (T : Tree Q Unit 15 n) (f : History 15 n → ℝ)
    (X : Matrix (Q×Unit) (Q×Unit) ℂ) :
    (FiniteAdaptiveProcessRobustness.effect T f*X).trace =
      ∑ h,(f h:ℂ)*(run Q Unit 15 T h X).trace := by
  induction T generalizing X with
  | done => simp [FiniteAdaptiveProcessRobustness.effect,History,run,Matrix.trace_smul]
  | node D next ih =>
    rw [FiniteAdaptiveProcessRobustness.effect,FiniteAdaptiveProcessRobustness.nodeEffect_trace]
    simp_rw [ih]
    change (∑ a,∑ h,(f (a,h):ℂ)*(run Q Unit 15 (next a) h (D.branch Q Unit 15 a X)).trace) =
      ∑ h : Fin 15 × History 15 _,(f h:ℂ)*(run Q Unit 15 (.node D next) h X).trace
    rw [Fintype.sum_prod_type]
    rfl

def branchScore (u : HalfHistory) : History 15 2 → ℝ :=
  by classical exact fun h => if h=(u.1,u.2,()) then 1 else 0

theorem qutrit_joint_surjective : Function.Surjective (GibbsMultilevelReflection.joint (d := 3)) := by
  intro X
  refine ⟨fun i j => X (i,()) (j,()),?_⟩
  ext ⟨i,⟨⟩⟩ ⟨j,⟨⟩⟩
  simp [GibbsMultilevelReflection.joint]

def leadingStep {m : ℕ} (V : Fin m → MatQ) (hV : IsKrausChannel V) : Step Q Unit 15 where
  count := m
  evolution k := GibbsMultilevelReflection.joint (V k)
  normalized := GibbsMultilevelReflection.joint_normalized V hV
  instrument := instrument

theorem leadingStep_branch {m : ℕ} (V : Fin m → MatQ) (hV : IsKrausChannel V)
    (o : Outcome) (X : MatQ) :
    (leadingStep V hV).branch Q Unit 15 o (GibbsMultilevelReflection.joint X)=
      GibbsMultilevelReflection.joint (instrument.branch o (krausMap V X)) := by
  change (instrument.lift Unit).branch o
    (krausMap (fun k => GibbsMultilevelReflection.joint (V k)) (GibbsMultilevelReflection.joint X))=_
  rw [GibbsMultilevelReflection.joint_kraus]
  exact GibbsMultilevelReflection.joint_kraus _ _

def positiveSuffix {m : ℕ} (V : Fin m → MatQ) (hV : IsKrausChannel V)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : Tree Q Unit 15 2 :=
  .node (leadingStep V hV) (fun _ => .node (step r hr hr1) (fun _ => .done))

theorem positiveSuffix_trace {m : ℕ} (V : Fin m → MatQ) (hV : IsKrausChannel V)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (u : HalfHistory) (X : MatQ) :
    (run Q Unit 15 (positiveSuffix V hV r hr hr1) (u.1,u.2,())
      (GibbsMultilevelReflection.joint X)).trace =
      (Channel.heisenberg V (halfEffect r u)*X).trace := by
  change ((step r hr hr1).branch Q Unit 15 u.2
    ((leadingStep V hV).branch Q Unit 15 u.1 (GibbsMultilevelReflection.joint X))).trace=_
  rw [leadingStep_branch,step_branch,GibbsMultilevelReflection.joint_trace,branch_trace,
    Phi_Psi_duality,trace_duality]
  change (halfEffect r u*krausMap V X).trace=_
  rw [Matrix.trace_mul_comm,← Channel.trace_duality,Matrix.trace_mul_comm]

/-- All-complex trace extensionality identifies the independently realized backward effect. -/
theorem positiveSuffix_effect {m : ℕ} (V : Fin m → MatQ) (hV : IsKrausChannel V)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (u : HalfHistory) :
    FiniteAdaptiveProcessRobustness.effect (positiveSuffix V hV r hr hr1) (branchScore u) =
      GibbsMultilevelReflection.joint (Channel.heisenberg V (halfEffect r u)) := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  obtain ⟨A,rfl⟩ := qutrit_joint_surjective X
  rw [qutrit_effect_complex_trace]
  simp only [branchScore,apply_ite,ite_mul,Complex.ofReal_one,Complex.ofReal_zero,
    one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  erw [positiveSuffix_trace V hV r hr hr1 u A]
  rw [GibbsMultilevelReflection.joint,GibbsMultilevelReflection.joint,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.trace_kronecker]
  simp [Matrix.trace]

def ordinaryPositiveTree (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :=
  positiveSuffix (channel p) (channel_normalized hp hp1) r hr hr1

def halfInsertedPositiveTree (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha1 : a ≤ 1) :=
  positiveSuffix (composeKraus (channel (Real.sqrt a)) (channel p))
    (isKrausChannel_composeKraus (channel_normalized (Real.sqrt_nonneg a) (Real.sqrt_le_one.mpr ha1))
      (channel_normalized hp hp1)) r hr hr1

def unsplitPositiveTree (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) :=
  positiveSuffix (centralKraus (channel a) p)
    (isKrausChannel_composeKraus (channel_normalized ha ha1)
      (channel_normalized (mul_nonneg hp hp) (by nlinarith))) r hr hr1

theorem ordinary_positive_effect (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : HalfHistory) :
    FiniteAdaptiveProcessRobustness.effect (ordinaryPositiveTree p r hp hp1 hr hr1) (branchScore u) =
      GibbsMultilevelReflection.joint (Psi p (halfEffect r u)) := by
  rw [ordinaryPositiveTree,positiveSuffix_effect,channel_observable hp hp1]

theorem half_inserted_effect (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha1 : a ≤ 1) (u : HalfHistory) :
    FiniteAdaptiveProcessRobustness.effect (halfInsertedPositiveTree p r a hp hp1 hr hr1 ha1) (branchScore u) =
      GibbsMultilevelReflection.joint (Psi (Real.sqrt a) (Psi p (halfEffect r u))) := by
  rw [halfInsertedPositiveTree,positiveSuffix_effect,heisenberg_compose,
    channel_observable (Real.sqrt_nonneg a) (Real.sqrt_le_one.mpr ha1),channel_observable hp hp1,
    Psi_comp,Psi_comp,mul_comm p (Real.sqrt a)]

theorem unsplit_positive_effect (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (u : HalfHistory) :
    FiniteAdaptiveProcessRobustness.effect (unsplitPositiveTree p r a hp hp1 hr hr1 ha ha1) (branchScore u) =
      GibbsMultilevelReflection.joint (Psi (p*p) (Psi a (halfEffect r u))) := by
  rw [unsplitPositiveTree,positiveSuffix_effect,centralKraus,heisenberg_compose,
    channel_observable ha ha1,channel_observable (mul_nonneg hp hp) (by nlinarith)]



theorem unitary_diagonal (ω : Q → ℝ) (t : ℝ) :
    GibbsHamiltonianRelaxation.unitary ω t =
      Matrix.diagonal (fun i => Complex.exp (-Complex.I*t*(ω i:ℂ))) := by
  simp only [GibbsHamiltonianRelaxation.unitary,FiniteGibbsClock.expCoeff,
    DiagonalLindblad.density,← Matrix.diagonal_smul,Matrix.exp_diagonal]
  congr 1
  funext i
  simp only [Pi.coe_exp,Pi.smul_apply,smul_eq_mul,← Complex.exp_eq_exp_ℂ]

theorem free_quarter_unitary :
    GibbsHamiltonianRelaxation.unitary (freeLevels (Real.pi/2) (Real.pi/2)) 1 =
      Matrix.diagonal (![1,-Complex.I,-Complex.I] : Q → ℂ) := by
  rw [unitary_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [freeLevels]
  all_goals
    convert Complex.exp_neg_pi_div_two_mul_I using 1
    congr 1
    ring

theorem free_half_unitary :
    GibbsHamiltonianRelaxation.unitary (freeLevels Real.pi Real.pi) 1 =
      Matrix.diagonal (![1,-1,-1] : Q → ℂ) := by
  rw [unitary_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [freeLevels]
  all_goals
    convert Complex.exp_neg_pi_mul_I using 1
    congr 1
    ring

theorem phase_exponential_period (x : ℝ) :
    Complex.exp (-Complex.I*((x+2*Real.pi:ℝ):ℂ))=Complex.exp (-Complex.I*(x:ℂ)) := by
  rw [show -Complex.I*((x+2*Real.pi:ℝ):ℂ) =
    -Complex.I*(x:ℂ)+ -(2*(Real.pi:ℂ)*Complex.I) by push_cast; ring,
    Complex.exp_add,Complex.exp_neg,Complex.exp_two_pi_mul_I]
  simp

theorem free_unitary_periods (φ ψ : ℝ) :
    GibbsHamiltonianRelaxation.unitary (freeLevels (φ+2*Real.pi) ψ) 1 =
      GibbsHamiltonianRelaxation.unitary (freeLevels φ ψ) 1 ∧
    GibbsHamiltonianRelaxation.unitary (freeLevels φ (ψ+2*Real.pi)) 1 =
      GibbsHamiltonianRelaxation.unitary (freeLevels φ ψ) 1 := by
  constructor <;> rw [unitary_diagonal,unitary_diagonal] <;> congr 1 <;>
    funext i <;> fin_cases i <;> simp [freeLevels]
  · simpa only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat,neg_mul]
      using phase_exponential_period φ
  · simpa only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat,neg_mul]
      using phase_exponential_period ψ

theorem rotate_unitary (ω : Q → ℝ) (t : ℝ) (A : MatQ) :
    rotate ω t A=(GibbsHamiltonianRelaxation.unitary ω t)ᴴ*A*GibbsHamiltonianRelaxation.unitary ω t := by
  rw [← pulse_observable]
  simp [Channel.heisenberg,pulseKraus]

theorem free_phase_periods (φ ψ : ℝ) (A : MatQ) :
    rotate (freeLevels (φ+2*Real.pi) ψ) 1 A=rotate (freeLevels φ ψ) 1 A ∧
    rotate (freeLevels φ (ψ+2*Real.pi)) 1 A=rotate (freeLevels φ ψ) 1 A := by
  simp only [rotate_unitary,(free_unitary_periods φ ψ).1,(free_unitary_periods φ ψ).2,and_self]

theorem free_phase_group (φ ψ χ ζ : ℝ) (A : MatQ) :
    rotate (freeLevels φ ψ) 1 (rotate (freeLevels χ ζ) 1 A)=
      rotate (freeLevels (φ+χ) (ψ+ζ)) 1 A := by
  ext i j
  rw [rotate_entry,rotate_entry,rotate_entry]
  have he : Complex.I*(1:ℂ)*
      ((freeLevels (φ+χ) (ψ+ζ) i:ℂ)-freeLevels (φ+χ) (ψ+ζ) j) =
    Complex.I*(1:ℂ)*((freeLevels φ ψ i:ℂ)-freeLevels φ ψ j)+
      Complex.I*(1:ℂ)*((freeLevels χ ζ i:ℂ)-freeLevels χ ζ j) := by
    fin_cases i <;> fin_cases j <;> simp [freeLevels] <;> ring
  simp only [Complex.ofReal_one]
  rw [he,Complex.exp_add]
  ring

theorem actual_raw_right_derivative (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (b ℏ γ : ℝ) (hγ : 0 ≤ γ) (F : HalfHistory → ℂ) :
    HasDerivWithinAt
      (fun t : ℝ => represent p r hp hp1 hr hr1
        (Channel.heisenberg (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) (synthesis 1 r F)))
      (generator p r hp hp1 hr hr1 (FiniteThreeLevelThermalPhase.frequencies b ℏ) γ
        (mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1)
          (kernel_posSemidef p r hp hp1 hr hr1) F)) (Set.Ici 0) 0 := by
  apply (physical_orbit_right_derivative p r hp hp1 hr hr1 b ℏ γ
    (mk (FiniteThreeLevelPositiveHistory.kernel p r hp hp1 hr hr1)
      (kernel_posSemidef p r hp hp1 hr hr1) F)).congr_of_mem
  · intro t ht
    rw [thermal_observable_matrix b ℏ γ t hγ ht,transfer_representative]
    rfl
  · exact Set.mem_Ici.mpr (le_refl (0 : ℝ))


/-- The two freely controlled phases characterize identity conjugation. -/
theorem free_multiplier_identity_iff (φ ψ : ℝ) :
    (∀ i j,multiplier (freeLevels φ ψ) 1 i j=1) ↔
      Complex.exp (Complex.I*(φ:ℂ))=1 ∧ Complex.exp (Complex.I*(ψ:ℂ))=1 := by
  constructor
  · intro h
    have hφ := h 0 1
    have hψ := h 0 2
    simpa [multiplier,freeLevels,Complex.exp_neg] using And.intro hφ hψ
  · rintro ⟨hφ,hψ⟩ i j
    have hlevel (k : Q) : Complex.exp (Complex.I*(freeLevels φ ψ k:ℂ))=1 := by
      fin_cases k <;> simp [freeLevels,hφ,hψ]
    unfold multiplier
    simp only [Complex.ofReal_one,mul_one,mul_sub,Complex.exp_sub,hlevel,div_self one_ne_zero]

theorem free_positive_iff (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hp0 : 0 < p) (ha0 : 0 < a) (φ ψ : ℝ) :
    (phaseKernel p r a hp hp1 hr hr1 ha ha1 (freeLevels φ ψ) 1).PosSemidef ↔
      Complex.exp (Complex.I*(φ:ℂ))=1 ∧ Complex.exp (Complex.I*(ψ:ℂ))=1 := by
  rw [phaseKernel_positive_iff p r a hp hp1 hr hr1 ha ha1 _ _ hp0 ha0,
    free_multiplier_identity_iff]

theorem rotate_energy_shift (ω : Q → ℝ) (c t : ℝ) (A : MatQ) :
    rotate (fun i => ω i+c) t A=rotate ω t A := by
  ext i j
  simp only [rotate_entry,Complex.ofReal_add]
  congr 2
  ring

theorem scalar_rotation (c t : ℝ) (A : MatQ) : rotate (fun _ => c) t A=A := by
  ext i j
  simp [rotate_entry]

theorem zero_hbar_rotation (b t : ℝ) (A : MatQ) :
    rotate (FiniteThreeLevelThermalPhase.frequencies b 0) t A=A := by
  have hf : FiniteThreeLevelThermalPhase.frequencies b 0=(fun _ => 0) := by
    funext i
    simp [FiniteThreeLevelThermalPhase.frequencies]
  rw [hf]
  exact scalar_rotation 0 t A

theorem gibbs_scale_guard (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (hbc : b≠c) :
    FiniteGibbsClock.gibbs (FiniteThreeLevelThermalPhase.thermalH b) b =
      FiniteGibbsClock.gibbs (FiniteThreeLevelThermalPhase.thermalH c) c ∧
    FiniteThreeLevelThermalPhase.energies b 1≠FiniteThreeLevelThermalPhase.energies c 1 :=
  ⟨FiniteThreeLevelThermalPhase.gibbs_two_scales hb hc,
    FiniteThreeLevelThermalPhase.gap_scales_ne hb hc hbc⟩

theorem scalar_gibbs_guard (c b : ℝ) :
    FiniteGibbsClock.gibbs ((c:ℂ) • (1:MatQ)) b=(1/3:ℝ) • (1:MatQ) ∧
    FiniteGibbsClock.gibbs ((c:ℂ) • (1:MatQ)) b≠rhoN := by
  have he : FiniteGibbsClock.gibbs ((c:ℂ) • (1:MatQ)) b=(1/3:ℝ) • (1:MatQ) := by
    rw [FiniteGibbsClock.gibbs_scalar]
    norm_num
  refine ⟨he,?_⟩
  rw [he,← FiniteThreeLevelThermalPhase.gibbs_zero_inverse_scale (0:MatQ)]
  exact FiniteThreeLevelThermalPhase.gibbs_zero_ne_reference _

theorem thermal_energy_shift_guard (b ℏ c t : ℝ) (hb : 0 < b) (A : MatQ) :
    FiniteGibbsClock.gibbs (FiniteThreeLevelThermalPhase.thermalH b+(c:ℂ) • 1) b=rhoN ∧
    rotate (fun i => (FiniteThreeLevelThermalPhase.energies b i+c)/ℏ) t A =
      rotate (FiniteThreeLevelThermalPhase.frequencies b ℏ) t A := by
  refine ⟨FiniteThreeLevelThermalPhase.gibbs_shift hb c,?_⟩
  simpa only [add_div,FiniteThreeLevelThermalPhase.frequencies] using
    rotate_energy_shift (FiniteThreeLevelThermalPhase.frequencies b ℏ) (c/ℏ) t A

theorem actual_observable_unital (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    Channel.heisenberg (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) 1=1 := by
  rw [thermal_observable_matrix b ℏ γ t hγ ht,Psi_unital,rotate_one]

theorem actual_state_identity (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    krausMap (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) 1 =
      (Real.exp (-γ*t):ℂ) • (1:MatQ)+(3*(1-(Real.exp (-γ*t):ℂ))) • rhoN := by
  rw [thermal_state_pulse b ℏ γ t hγ ht,
    pulseReset_state _ (Real.exp_pos _).le (GibbsReset.exp_rate_le_one γ t hγ ht),Phi]
  simp only [map_add,map_smul,rotate_one,rotate_equilibrium,Matrix.trace_one,
    Fintype.card_fin,smul_smul]
  congr 1
  congr 1
  ring

theorem actual_state_not_unital (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hdose : 0 < γ*t) :
    krausMap (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t) 1≠1 := by
  rw [actual_state_identity b ℏ γ t hγ ht]
  intro he
  have h0 := congrArg (fun A : MatQ => (A 0 0).re) he
  norm_num [rhoN,FiniteThreeLevelThermalPhase.equilibrium,DiagonalLindblad.density,
    GibbsMultilevelReflection.three,GibbsReset.threeWeights] at h0
  rw [← Complex.ofReal_mul,← Complex.ofReal_neg,← Complex.ofReal_exp,Complex.ofReal_re] at h0
  have ha : Real.exp (-γ*t)<1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  rw [neg_mul] at ha
  linarith

theorem qutrit_branch_binary (T : Tree Q Unit 15 2) (u : HalfHistory) :
    IsBinaryPOVM (FiniteAdaptiveProcessRobustness.effect (S := Q) (E := Unit)
      T (branchScore u)) := by
  apply FiniteAdaptiveProcessRobustness.effect_binary
  intro h
  classical
  by_cases he : h=(u.1,u.2,())
  · simp [branchScore,he]
  · simp [branchScore,he]

theorem phase_reset_rank_one (p r a : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hz : p=0 ∨ a=0) :
    Module.finrank ℂ (Space (phaseKernel p r a hp hp1 hr hr1 ha ha1 ω t)
      (phaseKernel_reset_positive p r a hp hp1 hr hr1 ha ha1 ω t hz))=1 := by
  rw [space_finrank_congr _ _ (phaseKernel_reset p r a hp hp1 hr hr1 ha ha1 ω t hz)]
  exact reset_finrank _ _ _

/-- A selected diagonal entry distinguishes the three separately realized effects. -/
theorem distinct_effect_entries :
    (FiniteAdaptiveProcessRobustness.effect
      (ordinaryPositiveTree (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (branchScore (0,0))) (1,()) (1,())=(1/200:ℂ) ∧
    (FiniteAdaptiveProcessRobustness.effect
      (halfInsertedPositiveTree (1/2) 0 (1/4) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num))
      (branchScore (0,0))) (1,()) (1,())=(3/400:ℂ) ∧
    (FiniteAdaptiveProcessRobustness.effect
      (unsplitPositiveTree (1/2) 0 (1/4) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (branchScore (0,0))) (1,()) (1,())=(15/1600:ℂ) := by
  rw [ordinary_positive_effect,half_inserted_effect,unsplit_positive_effect]
  simp only [halfEffect_factored,Psi_comp]
  norm_num [GibbsMultilevelReflection.joint,halfCoefficient,Psi,d,projector,
    rhoN,FiniteThreeLevelThermalPhase.equilibrium,DiagonalLindblad.density,
    GibbsMultilevelReflection.three,GibbsReset.threeWeights,Matrix.trace,Matrix.mul_apply,
    Fin.sum_univ_succ,Real.sqrt_div,Matrix.vecMul,dotProduct]

theorem zero_rate_phase_survives (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hp0 : 0 < p) (b ℏ : ℝ) (hb : 0 < b) (hℏ : 0 < ℏ) :
    ¬ (thermalKernel p r hp hp1 hr hr1 b ℏ 0 (quarterTime b ℏ)
      (by norm_num) (quarterTime_positive hb hℏ).le).IsHermitian := by
  exact timed_quarter_not_hermitian p r hp hp1 hr hr1 hp0 hb hℏ 0 (by norm_num)

theorem matrixOrbit_analyticAt (ω : Q → ℝ) (γ t : ℝ) (A : MatQ) :
    AnalyticAt ℝ (fun s : ℝ => matrixOrbit ω γ s A) t := by
  have hentry (i j : Q) : AnalyticAt ℝ (fun s : ℝ => matrixOrbit ω γ s A i j) t := by
    simp only [matrixOrbit_entry]
    have hlin : AnalyticAt ℝ
        (fun s : ℝ => (Complex.I*((ω i:ℂ)-ω j)-(γ:ℂ))*(s:ℂ)) t :=
      analyticAt_const.mul (Complex.ofRealCLM.analyticAt t)
    have he : AnalyticAt ℝ
        (fun s : ℝ => Complex.exp ((Complex.I*((ω i:ℂ)-ω j)-(γ:ℂ))*(s:ℂ))) t :=
      analyticAt_cexp.restrictScalars.comp hlin
    exact analyticAt_const.add (he.mul analyticAt_const)
  have hs := Finset.analyticAt_sum Finset.univ (fun i _ =>
    Finset.analyticAt_sum Finset.univ (fun j _ =>
      (hentry i j).smul (analyticAt_const (v := E i j))))
  convert hs using 1
  ext s i j
  simp [Finset.sum_apply,Matrix.sum_apply,E,Matrix.single,Matrix.of_apply,ite_and]

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelHistoryTransfer
