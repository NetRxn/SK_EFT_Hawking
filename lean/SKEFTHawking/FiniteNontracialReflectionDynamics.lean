import SKEFTHawking.FiniteNontracialPauliReflection
import SKEFTHawking.FiniteGibbsBlockRelaxation
import SKEFTHawking.QuantumNetwork.DiamondBudget

/-! Two-rate Kraus dynamics in the square-root-weighted reflection geometry. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.NontracialReflectionDynamics
open Matrix FiniteInterventionProcess NontracialPauliReflection
open FinitePositiveKernel GibbsObservable DiagonalLindblad BlockConditionalExpectation
open scoped BigOperators ComplexOrder

/-- A distinct signature for each computational basis vector. -/
def signature : Unit → Fin 2 → ℝ := fun _ i => i.val
def diagonalPart (A : Mat2) : Mat2 := Matrix.diagonal (fun i => A i i)

theorem singleton_expectation (A : Mat2) :
    blockExpectation signature A = diagonalPart A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [blockExpectation, rate, signature, diagonalPart]

def timeKraus (γ η t : ℝ) := GibbsBlockRelaxation.timeKraus signature weights γ η t

/-- State and observable actions use the same actual Kraus family. -/
def state (γ η t : ℝ) (X : Mat2) : Mat2 := krausMap (timeKraus γ η t) X
def observable (γ η t : ℝ) (A : Mat2) : Mat2 :=
  Channel.heisenberg (timeKraus γ η t) A

theorem normalized (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    IsKrausChannel (timeKraus γ η t) :=
  GibbsBlockRelaxation.time_normalized signature weights weights_nonnegative
    weights_normalized γ η t hγ hη ht

theorem stationary (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    state γ η t rhoN = rhoN := by
  rw [state, ← weights_density]
  exact GibbsBlockRelaxation.time_stationary signature weights weights_nonnegative
    weights_normalized γ η t hγ hη ht

theorem state_formula (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (X : Mat2) :
    state γ η t X = X.trace • rhoN +
      (Real.exp (-γ*t) : ℂ) • (diagonalPart X-X.trace • rhoN) +
      (Real.exp (-(γ+η)*t) : ℂ) • (X-diagonalPart X) := by
  rw [state, timeKraus,
    GibbsBlockRelaxation.time_state_eq_propagator signature weights weights_nonnegative
      weights_normalized γ η t hγ hη ht,
    GibbsBlockRelaxation.propagator_state signature weights weights_nonnegative
      weights_normalized γ η t hγ hη, weights_density, singleton_expectation]

theorem observable_formula (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (A : Mat2) :
    observable γ η t A = (rhoN*A).trace • (1 : Mat2) +
      (Real.exp (-γ*t) : ℂ) • (diagonalPart A-(rhoN*A).trace • 1) +
      (Real.exp (-(γ+η)*t) : ℂ) • (A-diagonalPart A) := by
  obtain ⟨ha,hb,hc⟩ := GibbsBlockRelaxation.time_coefficients_nonneg γ η t hγ hη ht
  rw [observable, timeKraus, GibbsBlockRelaxation.timeKraus,
    GibbsBlockRelaxation.mixture_observable signature weights weights_nonnegative _ _ _ ha hb hc,
    weights_density, singleton_expectation]
  simp only [GibbsBlockRelaxation.slow, GibbsBlockRelaxation.fast,
    Complex.ofReal_sub, Complex.ofReal_one]
  module

theorem diagonalPart_Gamma (A : Mat2) :
    diagonalPart (Gamma A) = Gamma (diagonalPart A) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagonalPart, Gamma, R, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem Gamma_sub (A B : Mat2) : Gamma (A-B) = Gamma A-Gamma B := by
  simp [Gamma, mul_sub, sub_mul]

theorem intertwining (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (A : Mat2) :
    state γ η t (Gamma A) = Gamma (observable γ η t A) := by
  rw [state_formula γ η t hγ hη ht, observable_formula γ η t hγ hη ht]
  simp only [Gamma_trace, Gamma_add, Gamma_sub, Gamma_smul, Gamma_one,
    diagonalPart_Gamma]

theorem trace_dual (γ η t : ℝ) (A X : Mat2) :
    (A * state γ η t X).trace = (observable γ η t A * X).trace := by
  rw [Matrix.trace_mul_comm, state, observable, ← Channel.trace_duality,
    Matrix.trace_mul_comm]

theorem diagonalPart_adjoint (A : Mat2) :
    (diagonalPart A)ᴴ = diagonalPart Aᴴ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagonalPart, Matrix.conjTranspose_apply]

theorem observable_adjoint (γ η t : ℝ) (A : Mat2) :
    (observable γ η t A)ᴴ = observable γ η t Aᴴ := by
  simp [observable, Channel.heisenberg, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem weighted_symmetry (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (A B : Mat2) :
    form A (observable γ η t B) = form (observable γ η t A) B := by
  simp only [form, observable_adjoint]
  have hg (X Y : Mat2) : (X*R*Y*R).trace = (X*Gamma Y).trace := by
    simp only [Gamma, Matrix.mul_assoc]
  rw [hg, hg, ← intertwining γ η t hγ hη ht, trace_dual]

/-- Only the central gap contains the new dynamics, after its original reset. -/
def centralKraus (p γ η t : ℝ) := composeKraus (timeKraus γ η t) (channel (p*p))

def centralStep (p γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : Step (Fin 2) Unit 6 where
  count := _
  evolution k := GibbsMultilevelReflection.joint (centralKraus p γ η t k)
  normalized := GibbsMultilevelReflection.joint_normalized _
    (isKrausChannel_composeKraus (normalized γ η t hγ hη ht)
      (channel_normalized (mul_nonneg hp hp) (by nlinarith)))
  instrument := instrument

theorem centralStep_branch (p γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (o : Fin 6) (X : Mat2) :
    (centralStep p γ η t hp hp1 hγ hη ht).branch (Fin 2) Unit 6 o
      (GibbsMultilevelReflection.joint X) =
    GibbsMultilevelReflection.joint (instrument.branch o (state γ η t (Phi (p*p) X))) := by
  change (instrument.lift Unit).branch o
    (krausMap (fun k => GibbsMultilevelReflection.joint (centralKraus p γ η t k))
      (GibbsMultilevelReflection.joint X)) = _
  rw [GibbsMultilevelReflection.joint_kraus, centralKraus, krausMap_composeKraus,
    channel_state (mul_nonneg hp hp) (by nlinarith)]
  exact GibbsMultilevelReflection.joint_kraus _ _

def tree (p r γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : Tree (Fin 2) Unit 6 4 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step r hr hr1) (fun _ =>
      .node (centralStep p γ η t hp hp1 hγ hη ht) (fun _ =>
        .node (step r hr hr1) (fun _ => .done))))

/-- Operational kernel: the real weight of the actual chronological tree. -/
def kernel (p r γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) : ℂ :=
  (weight (Fin 2) Unit 6 (tree p r γ η t hp hp1 hr hr1 hγ hη ht)
    (u.2,u.1,v.1,v.2,()) (GibbsMultilevelReflection.joint rhoN) : ℂ)

theorem actual_run (p r γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) :
    run (Fin 2) Unit 6 (tree p r γ η t hp hp1 hr hr1 hγ hη ht) (u.2,u.1,v.1,v.2,())
      (GibbsMultilevelReflection.joint rhoN) =
    GibbsMultilevelReflection.joint (instrument.branch v.2
      (Phi r (instrument.branch v.1 (state γ η t (Phi (p*p) (Gamma (halfEffect r u))))))) := by
  change (step r hr hr1).branch (Fin 2) Unit 6 v.2
    ((centralStep p γ η t hp hp1 hγ hη ht).branch (Fin 2) Unit 6 v.1
      (run (Fin 2) Unit 6 (negativeTree r hr hr1) (u.2,u.1,())
        (GibbsMultilevelReflection.joint rhoN))) = _
  rw [negative_run, centralStep_branch, step_branch]

theorem actual_trace (p r γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) :
    (run (Fin 2) Unit 6 (tree p r γ η t hp hp1 hr hr1 hγ hη ht) (u.2,u.1,v.1,v.2,())
      (GibbsMultilevelReflection.joint rhoN)).trace =
    (halfEffect r v * state γ η t (Phi (p*p) (Gamma (halfEffect r u)))).trace := by
  rw [actual_run, GibbsMultilevelReflection.joint_trace, branch_trace,
    Phi_Psi_duality, NontracialPauliReflection.trace_duality]
  rfl

theorem kernel_trace (p r γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) :
    kernel p r γ η t hp hp1 hr hr1 hγ hη ht u v =
    (halfEffect r v * state γ η t (Phi (p*p) (Gamma (halfEffect r u)))).trace := by
  unfold kernel weight
  rw [actual_trace]
  apply hermitian_product_real _ _ (halfEffect_adjoint r v)
  rw [Phi_Gamma, intertwining γ η t hγ hη ht, Gamma_adjoint,
    observable_adjoint, Psi_adjoint, halfEffect_adjoint]

theorem halfEffect_zero_y :
    halfEffect 0 (2,0) = (1/18 : ℂ) • PauliInstrumentReconstruction.projector 2 := by
  have hm : (rhoN * PauliInstrumentReconstruction.effect 0).trace = (1/6 : ℂ) := by
    norm_num [rhoN, PauliInstrumentReconstruction.effect,
      PauliInstrumentReconstruction.projector, PauliInstrumentReconstruction.sign,
      PauliInstrumentReconstruction.outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
      PauliInstrumentReconstruction.sigma, pauliX, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace,
      Fin.sum_univ_two, Matrix.one_apply]
  have hj (z : ℂ) (o : Fin 6) : J o (z • 1) = z • PauliInstrumentReconstruction.effect o := by
    rw [NontracialPauliReflection.J, mul_smul_comm, smul_mul_assoc]
    rw [show (L o)ᴴ * 1 * L o = PauliInstrumentReconstruction.effect o by simpa using L_effect o]
  rw [halfEffect, Psi_zero, hm, hj]
  simp only [PauliInstrumentReconstruction.effect, smul_smul]
  norm_num

/-- Reset is not unital on states at this nontracial density. -/
theorem state_observable_difference (γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) :
    state γ η t 1 ≠ observable γ η t 1 := by
  intro he
  have h := congrArg (fun A : Mat2 => A 0 0) he
  rw [state_formula γ η t hγ.le hη ht.le, observable_formula γ η t hγ.le hη ht.le] at h
  norm_num [diagonalPart, rhoN, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] at h
  have ha : Real.exp (-γ*t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have heq : (Real.exp (-γ*t) : ℂ) = 1 := by
    push_cast
    simp only [neg_mul]
    linear_combination (-25/7 : ℂ) * h
  have : Real.exp (-γ*t) = 1 := Complex.ofReal_injective (by simpa using heq)
  linarith

/-- The subnormalized Y branch, with its off-diagonal amplitude explicit. -/
def yState (q : ℂ) : Mat2 := !![4/225, -q*Complex.I/75; q*Complex.I/75, 1/100]

theorem gamma_y :
    Gamma ((1/18 : ℂ) • PauliInstrumentReconstruction.projector 2) = yState 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Gamma, R, yState, PauliInstrumentReconstruction.projector,
      PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv,
      finProdFinEquiv, Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma, pauliY,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem yState_trace (q : ℂ) : (yState q).trace = 1/36 := by
  norm_num [yState, Matrix.trace, Fin.sum_univ_two]

theorem yState_diagonal (q : ℂ) : diagonalPart (yState q) = (1/36 : ℂ) • rhoN := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [yState, diagonalPart, rhoN]

theorem reset_y (p : ℝ) : Phi (p*p) (yState 1) = yState ((p:ℂ)^2) := by
  rw [Phi, yState_trace]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [yState, rhoN, Complex.ofReal_mul] <;> ring

theorem state_y (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (q : ℂ) :
    state γ η t (yState q) = yState ((Real.exp (-(γ+η)*t) : ℂ)*q) := by
  rw [state_formula γ η t hγ hη ht, yState_trace, yState_diagonal, sub_self,
    smul_zero, add_zero]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [yState, rhoN] <;> ring

theorem y_trace (q : ℂ) :
    (((1/18 : ℂ) • PauliInstrumentReconstruction.projector 2) * yState q).trace =
      1/1296 + q/1350 := by
  norm_num [yState, PauliInstrumentReconstruction.projector,
    PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv,
    finProdFinEquiv, Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma, pauliY,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]
  ring_nf
  norm_num [Complex.I_sq]

/-- A Y-containing actual tree weight detects the fast sector, including r=0. -/
theorem actual_y_weight (p γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    kernel p 0 γ η t hp hp1 (by norm_num) (by norm_num) hγ hη ht (2,0) (2,0) =
      1/1296 + (p:ℂ)^2 * (Real.exp (-(γ+η)*t) : ℂ)/1350 := by
  rw [kernel_trace, halfEffect_zero_y, gamma_y, reset_y, state_y γ η t hγ hη ht, y_trace]
  ring

theorem actual_probabilities (p r γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (∀ h, 0 ≤ weight (Fin 2) Unit 6 (tree p r γ η t hp hp1 hr hr1 hγ hη ht) h
      (GibbsMultilevelReflection.joint rhoN)) ∧
    (∑ h, weight (Fin 2) Unit 6 (tree p r γ η t hp hp1 hr hr1 hγ hη ht) h
      (GibbsMultilevelReflection.joint rhoN)) = 1 :=
  normalized_weights (Fin 2) Unit 6 _ joint_density

open scoped InnerProductSpace
/-- Scalar conditional expectation in the accepted square-root geometry. -/
def scalarPart (A : Mat2) : Mat2 := (rhoN*A).trace • 1

def diagonalLinear : Mat2 →ₗ[ℂ] Mat2 where
  toFun := diagonalPart
  map_add' A B := by ext i j; by_cases h : i=j <;> simp [diagonalPart, h]
  map_smul' z A := by ext i j; by_cases h : i=j <;> simp [diagonalPart, h]

def scalarLinear : Mat2 →ₗ[ℂ] Mat2 where
  toFun := scalarPart
  map_add' A B := by simp [scalarPart, mul_add, Matrix.trace_add, add_smul]
  map_smul' z A := by simp [scalarPart, smul_smul]

theorem diagonal_scalar (A : Mat2) : diagonalPart (scalarPart A) = scalarPart A := by
  ext i j; by_cases h : i=j <;> simp [diagonalPart, scalarPart, h]

theorem scalar_diagonal (A : Mat2) : scalarPart (diagonalPart A) = scalarPart A := by
  simp [scalarPart, diagonalPart, rhoN, Matrix.vecMul, dotProduct,
    Matrix.trace, Fin.sum_univ_two]

theorem scalar_idempotent (A : Mat2) : scalarPart (scalarPart A) = scalarPart A := by
  simp [scalarPart, rhoN_trace]

theorem diagonal_idempotent (A : Mat2) : diagonalPart (diagonalPart A) = diagonalPart A := by
  simp [diagonalPart]

theorem diagonal_Psi (p : ℝ) (A : Mat2) : diagonalPart (Psi p A) = Psi p (diagonalPart A) := by
  change diagonalLinear (Psi p A) = _
  rw [Psi, map_add, map_smul, map_smul]
  change (p:ℂ) • diagonalPart A + (1-(p:ℂ)) • diagonalPart (scalarPart A) = _
  rw [diagonal_scalar]
  change _ = (p:ℂ) • diagonalPart A + (1-(p:ℂ)) • scalarPart (diagonalPart A)
  rw [scalar_diagonal]

theorem synthesis_from_raw (p r : ℝ) (F : HalfHistory → ℂ) :
    synthesis p r F = Psi p (synthesis 1 r F) := by
  simp only [synthesis, NontracialPauliReflection.midpoint, Psi_one, Psi_sum, Psi_smul]

def scalarCoefficients (r : ℝ) : (HalfHistory → ℂ) →ₗ[ℂ] (HalfHistory → ℂ) where
  toFun F _ := (rhoN * synthesis 1 r F).trace
  map_add' F G := by
    change (fun _ => (rhoN * synthesisLinear 1 r (F+G)).trace) = _
    ext u
    simp [map_add, mul_add, Matrix.trace_add]
    rfl
  map_smul' z F := by
    change (fun _ => (rhoN * synthesisLinear 1 r (z • F)).trace) = _
    ext u
    simp [map_smul, synthesisLinear]

def pauliCoefficients : Mat2 →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun := PauliInstrumentReconstruction.coefficients
  map_add' A B := by
    ext o
    simp [PauliInstrumentReconstruction.coefficients, mul_add, Matrix.trace_add]
    ring
  map_smul' z A := by
    ext o
    simp [PauliInstrumentReconstruction.coefficients]
    ring

def diagonalCoefficients (r : ℝ) : (HalfHistory → ℂ) →ₗ[ℂ] (HalfHistory → ℂ) where
  toFun F u := pauliCoefficients (diagonalLinear (synthesisLinear 1 r F)) u.1
  map_add' F G := by ext u; simp
  map_smul' z F := by ext u; simp

theorem scalarCoefficients_synthesis (p r : ℝ) (F : HalfHistory → ℂ) :
    synthesis p r (scalarCoefficients r F) = scalarPart (synthesis p r F) := by
  have hc (z : ℂ) : synthesis p r (fun _ => z) = z • (1 : Mat2) := by
    simp only [synthesis, ← Finset.smul_sum]
    exact congrArg (z • ·) (by simpa [synthesis] using synthesis_constant p r)
  change synthesis p r (fun _ => (rhoN*synthesis 1 r F).trace) = _
  rw [hc, scalarPart]
  conv_rhs => rw [synthesis_from_raw, Psi_mean]

theorem diagonalCoefficients_synthesis (p r : ℝ) (F : HalfHistory → ℂ) :
    synthesis p r (diagonalCoefficients r F) = diagonalPart (synthesis p r F) := by
  change synthesis p r (fun u => PauliInstrumentReconstruction.coefficients
    (diagonalPart (synthesis 1 r F)) u.1) = _
  rw [synthesis_inner, PauliInstrumentReconstruction.synthesis_coefficients]
  conv_rhs => rw [synthesis_from_raw, diagonal_Psi]


theorem form_scalar_symmetric (A B : Mat2) : form (scalarPart A) B = form A (scalarPart B) := by
  simpa only [Psi_zero, scalarPart] using (form_Psi_symmetric 0 A B).symm

theorem form_diagonal_symmetric (A B : Mat2) :
    form (diagonalPart A) B = form A (diagonalPart B) := by
  simp [form_entries, diagonalPart]


def observableLinear (γ η t : ℝ) : Mat2 →ₗ[ℂ] Mat2 :=
  Channel.heisenbergLinear (timeKraus γ η t)

theorem observable_unital (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    observable γ η t 1 = 1 := Channel.heisenberg_one _ (normalized γ η t hγ hη ht)

theorem observable_mean (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (A : Mat2) :
    (rhoN * observable γ η t A).trace = (rhoN*A).trace := by
  rw [Matrix.trace_mul_comm, ← trace_dual, stationary γ η t hγ hη ht, Matrix.trace_mul_comm]

theorem observable_Psi (p γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (A : Mat2) :
    observable γ η t (Psi p A) = Psi p (observable γ η t A) := by
  change observableLinear γ η t (Psi p A) = _
  rw [Psi, map_add, map_smul, map_smul, map_smul]
  change (p:ℂ) • observable γ η t A +
    (1-(p:ℂ)) • ((rhoN*A).trace • observable γ η t 1) = _
  rw [observable_unital γ η t hγ hη ht, Psi, observable_mean γ η t hγ hη ht]

theorem actual_kernel_form (p r γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (u v : HalfHistory) :
    kernel p r γ η t hp hp1 hr hr1 hγ hη ht u v =
      form (NontracialPauliReflection.midpoint p r u)
        (observable γ η t (NontracialPauliReflection.midpoint p r v)) := by
  rw [kernel_trace, trace_dual, central_split, ← observable_Psi p γ η t hγ hη ht]
  rw [form, midpoint_adjoint]
  simp only [NontracialPauliReflection.midpoint, Gamma, Matrix.mul_assoc]

theorem form_sum_left {ι : Type*} [Fintype ι] (A : ι → Mat2) (B : Mat2) :
    form (∑ i,A i) B = ∑ i,form (A i) B := by
  simp [form, Matrix.conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]

theorem form_sum_right {ι : Type*} [Fintype ι] (A : Mat2) (B : ι → Mat2) :
    form A (∑ i,B i) = ∑ i,form A (B i) := by
  simp [form, Matrix.sum_mul, Matrix.trace_sum]

theorem actual_pairing_form (p r γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (F G : HalfHistory → ℂ) :
    pairing (kernel p r γ η t hp hp1 hr hr1 hγ hη ht) F G =
      form (synthesis p r F) (observable γ η t (synthesis p r G)) := by
  change _ = form (synthesis p r F) (observableLinear γ η t (synthesis p r G))
  simp only [synthesis, map_sum, map_smul, form_sum_left, form_sum_right, form_smul]
  simp only [pairing, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
    actual_kernel_form p r γ η t hp hp1 hr hr1 hγ hη ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  change star (F v) * (form _ (observable γ η t _) * G u) =
    star (F v) * G u * form _ (observable γ η t _)
  ring

section Quotient
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
local notation "K₀" => NontracialPauliReflection.kernel p r hp hp1 hr hr1
local notation "hK₀" => NontracialPauliReflection.kernel_posSemidef p r hp hp1 hr hr1
local notation "H" => Reconstructed p r hp hp1 hr hr1
local notation "coord" => coordinates p r hp hp1 hr hr1

theorem scalar_null : NullPreserving hK₀ (scalarCoefficients r) := by
  intro F hF
  apply (mem_nullSpace_iff K₀ hK₀ _).mpr
  apply (mk_eq_zero_iff K₀ hK₀ _).mp
  rw [null_iff]
  erw [scalarCoefficients_synthesis]
  have h := (synthesis_null p r hp hp1 hr hr1) hF
  change synthesis p r F = 0 at h
  simp [h, scalarPart]

theorem diagonal_null : NullPreserving hK₀ (diagonalCoefficients r) := by
  intro F hF
  apply (mem_nullSpace_iff K₀ hK₀ _).mpr
  apply (mk_eq_zero_iff K₀ hK₀ _).mp
  rw [null_iff]
  erw [diagonalCoefficients_synthesis]
  have h := (synthesis_null p r hp hp1 hr hr1) hF
  change synthesis p r F = 0 at h
  simp [h, diagonalPart]

/-- Both maps descend through the original actual kernel null quotient. -/
def scalarProjection : H →L[ℂ] H :=
  (descend hK₀ (scalarCoefficients r) (scalar_null p r hp hp1 hr hr1)).toContinuousLinearMap
def diagonalProjection : H →L[ℂ] H :=
  (descend hK₀ (diagonalCoefficients r) (diagonal_null p r hp hp1 hr hr1)).toContinuousLinearMap

theorem scalar_coordinates (z : H) :
    coord (scalarProjection p r hp hp1 hr hr1 z) = scalarPart (coord z) := by
  obtain ⟨F,rfl⟩ := mk_surjective K₀ hK₀ z
  change coord (descend hK₀ _ _ (mk K₀ hK₀ F)) = _
  rw [descend_mk, coordinates_mk, coordinates_mk]
  exact scalarCoefficients_synthesis p r F

theorem diagonal_coordinates (z : H) :
    coord (diagonalProjection p r hp hp1 hr hr1 z) = diagonalPart (coord z) := by
  obtain ⟨F,rfl⟩ := mk_surjective K₀ hK₀ z
  change coord (descend hK₀ _ _ (mk K₀ hK₀ F)) = _
  rw [descend_mk, coordinates_mk, coordinates_mk]
  exact diagonalCoefficients_synthesis p r F


local notation "C" => scalarProjection p r hp hp1 hr hr1
local notation "B" => diagonalProjection p r hp hp1 hr hr1

theorem coordinates_inner (z w : H) : ⟪z,w⟫_ℂ = form (coord z) (coord w) := by
  obtain ⟨F,rfl⟩ := mk_surjective K₀ hK₀ z
  obtain ⟨G,rfl⟩ := mk_surjective K₀ hK₀ w
  rw [coordinates_mk, coordinates_mk, inner_mk, pairing_synthesis]

theorem scalar_symmetric : (C).IsSymmetric := by
  intro z w
  change ⟪C z,w⟫_ℂ = ⟪z,C w⟫_ℂ
  rw [coordinates_inner, coordinates_inner, scalar_coordinates, scalar_coordinates,
    form_scalar_symmetric]

theorem diagonal_symmetric : (B).IsSymmetric := by
  intro z w
  change ⟪B z,w⟫_ℂ = ⟪z,B w⟫_ℂ
  rw [coordinates_inner, coordinates_inner, diagonal_coordinates, diagonal_coordinates,
    form_diagonal_symmetric]

theorem scalar_twice (z : H) : C (C z) = C z := by
  apply coordinates_injective p r hp hp1 hr hr1
  simp only [scalar_coordinates, scalar_idempotent]

theorem diagonal_twice (z : H) : B (B z) = B z := by
  apply coordinates_injective p r hp hp1 hr hr1
  simp only [diagonal_coordinates, diagonal_idempotent]

theorem scalar_after_diagonal (z : H) : C (B z) = C z := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [scalar_coordinates, diagonal_coordinates, scalar_coordinates, scalar_diagonal]

theorem diagonal_after_scalar (z : H) : B (C z) = C z := by
  apply coordinates_injective p r hp hp1 hr hr1
  simp only [diagonal_coordinates, scalar_coordinates, diagonal_scalar]

theorem scalar_inner (z : H) : ⟪C z,z⟫_ℂ = ⟪C z,C z⟫_ℂ := by
  have h := scalar_symmetric p r hp hp1 hr hr1 (C z) z
  change ⟪C (C z),z⟫_ℂ = ⟪C z,C z⟫_ℂ at h
  rwa [scalar_twice] at h

theorem diagonal_inner (z : H) : ⟪B z,z⟫_ℂ = ⟪B z,B z⟫_ℂ := by
  have h := diagonal_symmetric p r hp hp1 hr hr1 (B z) z
  change ⟪B (B z),z⟫_ℂ = ⟪B z,B z⟫_ℂ at h
  rwa [diagonal_twice] at h

theorem scalar_positive : (C).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨scalar_symmetric p r hp hp1 hr hr1, ?_⟩
  intro z
  change 0 ≤ (⟪C z,z⟫_ℂ).re
  rw [scalar_inner]
  exact inner_self_nonneg (𝕜 := ℂ) (x := C z)

theorem diagonal_positive : (B).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨diagonal_symmetric p r hp hp1 hr hr1, ?_⟩
  intro z
  change 0 ≤ (⟪B z,z⟫_ℂ).re
  rw [diagonal_inner]
  exact inner_self_nonneg (𝕜 := ℂ) (x := B z)

theorem scalar_error_orthogonal (z : H) : ⟪C z,z-C z⟫_ℂ = 0 := by
  rw [inner_sub_right, scalar_inner, sub_self]

theorem diagonal_error_orthogonal (z : H) : ⟪B z,z-B z⟫_ℂ = 0 := by
  rw [inner_sub_right, diagonal_inner, sub_self]

theorem scalar_norm_le (z : H) : ‖C z‖ ≤ ‖z‖ := by
  have h := norm_add_sq (𝕜 := ℂ) (C z) (z-C z)
  rw [scalar_error_orthogonal] at h
  have hz : C z+(z-C z)=z := by abel
  rw [hz] at h
  simp only [map_zero, mul_zero, add_zero] at h
  nlinarith [sq_nonneg ‖z-C z‖, norm_nonneg z, norm_nonneg (C z)]

theorem diagonal_norm_le (z : H) : ‖B z‖ ≤ ‖z‖ := by
  have h := norm_add_sq (𝕜 := ℂ) (B z) (z-B z)
  rw [diagonal_error_orthogonal] at h
  have hz : B z+(z-B z)=z := by abel
  rw [hz] at h
  simp only [map_zero, mul_zero, add_zero] at h
  nlinarith [sq_nonneg ‖z-B z‖, norm_nonneg z, norm_nonneg (B z)]


/-- Two-rate transfer on the original reconstructed space. -/
def transfer (γ η t : ℝ) : H →L[ℂ] H :=
  C + (Real.exp (-γ*t) : ℂ) • (B-C) +
    (Real.exp (-(γ+η)*t) : ℂ) • (1-B)

theorem transfer_apply (γ η t : ℝ) (z : H) :
    transfer p r hp hp1 hr hr1 γ η t z =
    C z + (Real.exp (-γ*t) : ℂ) • (B z-C z) +
      (Real.exp (-(γ+η)*t) : ℂ) • (z-B z) := by
  simp [transfer]

theorem transfer_coordinates (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (z : H) :
    coord (transfer p r hp hp1 hr hr1 γ η t z) = observable γ η t (coord z) := by
  rw [transfer_apply, map_add, map_add, map_smul, map_smul, map_sub, map_sub,
    scalar_coordinates, diagonal_coordinates, observable_formula γ η t hγ hη ht]
  rfl

theorem transfer_convex (γ η t : ℝ) :
    transfer p r hp hp1 hr hr1 γ η t =
    ((1-Real.exp (-γ*t) : ℝ) : ℂ) • C +
      ((Real.exp (-γ*t)-Real.exp (-(γ+η)*t) : ℝ) : ℂ) • B +
      (Real.exp (-(γ+η)*t) : ℂ) • (1 : H →L[ℂ] H) := by
  simp only [transfer, Complex.ofReal_sub, Complex.ofReal_one]
  module

theorem transfer_positive (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (transfer p r hp hp1 hr hr1 γ η t).IsPositive := by
  rw [transfer_convex]
  obtain ⟨ha,hb,hc⟩ := GibbsBlockRelaxation.time_coefficients_nonneg γ η t hγ hη ht
  exact (((scalar_positive p r hp hp1 hr hr1).smul_of_nonneg (by exact_mod_cast ha)).add
    ((diagonal_positive p r hp hp1 hr hr1).smul_of_nonneg (by exact_mod_cast hb))).add
    (ContinuousLinearMap.isPositive_one.smul_of_nonneg (by exact_mod_cast hc))

theorem transfer_selfAdjoint (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    IsSelfAdjoint (transfer p r hp hp1 hr hr1 γ η t) :=
  (transfer_positive p r hp hp1 hr hr1 γ η t hγ hη ht).isSelfAdjoint

theorem transfer_norm_le (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : H) :
    ‖transfer p r hp hp1 hr hr1 γ η t z‖ ≤ ‖z‖ := by
  obtain ⟨ha,hb,hc⟩ := GibbsBlockRelaxation.time_coefficients_nonneg γ η t hγ hη ht
  change 0 ≤ 1-Real.exp (-γ*t) at ha
  change 0 ≤ Real.exp (-γ*t)-Real.exp (-(γ+η)*t) at hb
  change 0 ≤ Real.exp (-(γ+η)*t) at hc
  rw [transfer_convex]
  simp only [_root_.add_apply, _root_.smul_apply,
    one_apply_eq_self]
  calc
    _ ≤ ‖((1-Real.exp (-γ*t):ℝ):ℂ) • C z‖ +
          ‖((Real.exp (-γ*t)-Real.exp (-(γ+η)*t):ℝ):ℂ) • B z‖ +
          ‖(Real.exp (-(γ+η)*t):ℂ) • z‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (1-Real.exp (-γ*t))*‖C z‖ +
          (Real.exp (-γ*t)-Real.exp (-(γ+η)*t))*‖B z‖ +
          Real.exp (-(γ+η)*t)*‖z‖ := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
        abs_of_nonneg hb, abs_of_nonneg hc]
    _ ≤ (1-Real.exp (-γ*t))*‖z‖ +
          (Real.exp (-γ*t)-Real.exp (-(γ+η)*t))*‖z‖ +
          Real.exp (-(γ+η)*t)*‖z‖ := by
      gcongr
      · exact scalar_norm_le p r hp hp1 hr hr1 z
      · exact diagonal_norm_le p r hp hp1 hr hr1 z
    _ = ‖z‖ := by ring

theorem transfer_zero (γ η : ℝ) : transfer p r hp hp1 hr hr1 γ η 0 = 1 := by
  ext z
  simp only [transfer_apply, mul_zero, Real.exp_zero, Complex.ofReal_one, one_smul,
    one_apply_eq_self]
  abel

theorem transfer_comp (γ η s t : ℝ) (z : H) :
    transfer p r hp hp1 hr hr1 γ η (s+t) z =
      transfer p r hp hp1 hr hr1 γ η s (transfer p r hp hp1 hr hr1 γ η t z) := by
  have hs : (Real.exp (-γ*(s+t)):ℂ) = (Real.exp (-γ*s):ℂ)*(Real.exp (-γ*t):ℂ) := by
    rw [mul_add, Real.exp_add, Complex.ofReal_mul]
  have hf : (Real.exp (-(γ+η)*(s+t)):ℂ) =
      (Real.exp (-(γ+η)*s):ℂ)*(Real.exp (-(γ+η)*t):ℂ) := by
    rw [mul_add, Real.exp_add, Complex.ofReal_mul]
  simp only [transfer_apply, map_add, map_sub, map_smul, scalar_twice, diagonal_twice,
    scalar_after_diagonal, diagonal_after_scalar, sub_self, smul_zero, add_zero, hs, hf]
  module

theorem reset_projections (hp0 : p=0) (z : H) : C z=z ∧ B z=z := by
  subst p
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  constructor
  · apply coordinates_injective 0 r hp hp1 hr hr1
    rw [scalar_coordinates, coordinates_mk, synthesis_full_reset]
    simp [scalarPart, rhoN_trace]
  · apply coordinates_injective 0 r hp hp1 hr hr1
    rw [diagonal_coordinates, coordinates_mk, synthesis_full_reset]
    ext i j
    by_cases h : i=j <;> simp [diagonalPart, h]

theorem transfer_reset (hp0 : p=0) (γ η t : ℝ) (z : H) :
    transfer p r hp hp1 hr hr1 γ η t z=z := by
  obtain ⟨hc,hb⟩ := reset_projections p r hp hp1 hr hr1 hp0 z
  rw [transfer_apply, hc, hb]
  simp


theorem actual_pairing_transfer (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (F G : HalfHistory → ℂ) :
    pairing (kernel p r γ η t hp hp1 hr hr1 hγ hη ht) F G =
      ⟪mk K₀ hK₀ F,transfer p r hp hp1 hr hr1 γ η t (mk K₀ hK₀ G)⟫_ℂ := by
  rw [actual_pairing_form, coordinates_inner, transfer_coordinates p r hp hp1 hr hr1 γ η t hγ hη ht,
    coordinates_mk, coordinates_mk]

/-- Canonical single-history vectors of the same null quotient. -/
def historyVector (u : HalfHistory) : H := mk K₀ hK₀ (Pi.single u 1)

theorem history_coordinates (u : HalfHistory) :
    coord (historyVector p r hp hp1 hr hr1 u) = NontracialPauliReflection.midpoint p r u := by
  rw [historyVector, coordinates_mk]
  simp [synthesis, Pi.single_apply]

theorem actual_entry_transfer (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (u v : HalfHistory) :
    kernel p r γ η t hp hp1 hr hr1 hγ hη ht u v =
      ⟪historyVector p r hp hp1 hr hr1 u,
        transfer p r hp hp1 hr hr1 γ η t (historyVector p r hp hp1 hr hr1 v)⟫_ℂ := by
  rw [coordinates_inner, transfer_coordinates p r hp hp1 hr hr1 γ η t hγ hη ht,
    history_coordinates, history_coordinates, actual_kernel_form]

theorem transfer_half_inner (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (z w : H) :
    ⟪z,transfer p r hp hp1 hr hr1 γ η t w⟫_ℂ =
      ⟪transfer p r hp hp1 hr hr1 γ η (t/2) z,
        transfer p r hp hp1 hr hr1 γ η (t/2) w⟫_ℂ := by
  have hc := transfer_comp p r hp hp1 hr hr1 γ η (t/2) (t/2) w
  rw [show t/2+t/2=t by ring] at hc
  rw [hc]
  have hs := (transfer_positive p r hp hp1 hr hr1 γ η (t/2) hγ hη (by positivity)).isSymmetric
  exact (hs z (transfer p r hp hp1 hr hr1 γ η (t/2) w)).symm

/-- Half-time feature factorization is derived from actual chronological weights. -/
theorem kernel_half_gram (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (u v : HalfHistory) :
    kernel p r γ η t hp hp1 hr hr1 hγ hη ht u v =
      (NontracialPauliReflection.feature (observable γ η (t/2) (NontracialPauliReflection.midpoint p r v)) *
        (NontracialPauliReflection.feature (observable γ η (t/2) (NontracialPauliReflection.midpoint p r u)))ᴴ).trace := by
  rw [actual_entry_transfer, transfer_half_inner p r hp hp1 hr hr1 γ η t hγ hη ht,
    coordinates_inner,
    transfer_coordinates p r hp hp1 hr hr1 γ η (t/2) hγ hη (by positivity),
    transfer_coordinates p r hp hp1 hr hr1 γ η (t/2) hγ hη (by positivity),
    history_coordinates, history_coordinates, feature_gram]

theorem actual_kernel_positive (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    Matrix.PosSemidef (kernel p r γ η t hp hp1 hr hr1 hγ hη ht) := by
  letI := Matrix.toMatrixSeminormedAddCommGroup (1 : Mat2) Matrix.PosSemidef.one
  letI := Matrix.toMatrixInnerProductSpace (1 : Mat2) Matrix.PosSemidef.one
  have hk : kernel p r γ η t hp hp1 hr hr1 hγ hη ht =
      Matrix.gram ℂ (fun u => NontracialPauliReflection.feature (observable γ η (t/2) (NontracialPauliReflection.midpoint p r u))) := by
    ext u v
    rw [kernel_half_gram]
    change _ = ((NontracialPauliReflection.feature (observable γ η (t/2)
      (NontracialPauliReflection.midpoint p r v))) * 1 *
      (NontracialPauliReflection.feature (observable γ η (t/2)
      (NontracialPauliReflection.midpoint p r u)))ᴴ).trace
    simp
  rw [hk]
  exact Matrix.posSemidef_gram ℂ _

theorem actual_kernel_zero (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    kernel p r γ η 0 hp hp1 hr hr1 hγ hη (by norm_num) = K₀ := by
  ext u v
  rw [actual_entry_transfer, transfer_zero]
  simp only [one_apply_eq_self]
  rw [coordinates_inner, history_coordinates, history_coordinates,
    NontracialPauliReflection.kernel_form]


/-- The scalar and diagonal sectors are orthogonal in the actual quotient metric. -/
theorem sector_orthogonal (z : H) :
    ⟪C z,B z-C z⟫_ℂ=0 ∧ ⟪C z,z-B z⟫_ℂ=0 ∧ ⟪B z-C z,z-B z⟫_ℂ=0 := by
  have hcb : ⟪C z,B z⟫_ℂ = ⟪C z,z⟫_ℂ := by
    have h := diagonal_symmetric p r hp hp1 hr hr1 (C z) z
    change ⟪B (C z),z⟫_ℂ=⟪C z,B z⟫_ℂ at h
    rw [diagonal_after_scalar] at h
    exact h.symm
  refine ⟨?_,?_,?_⟩
  · rw [inner_sub_right, hcb, scalar_inner, sub_self]
  · rw [inner_sub_right, hcb, sub_self]
  · rw [inner_sub_left, diagonal_error_orthogonal, inner_sub_right, hcb, sub_self, sub_self]

theorem centered_pythagoras (z : H) :
    ‖z-C z‖^2 = ‖B z-C z‖^2+‖z-B z‖^2 := by
  have h := norm_add_sq (𝕜 := ℂ) (B z-C z) (z-B z)
  rw [(sector_orthogonal p r hp hp1 hr hr1 z).2.2] at h
  have he : B z-C z+(z-B z)=z-C z := by abel
  simpa only [he, map_zero, mul_zero, add_zero] using h

theorem transfer_error_sq (γ η t : ℝ) (z : H) :
    ‖transfer p r hp hp1 hr hr1 γ η t z-C z‖^2 =
      Real.exp (-γ*t)^2*‖B z-C z‖^2 +
      Real.exp (-(γ+η)*t)^2*‖z-B z‖^2 := by
  have he : transfer p r hp hp1 hr hr1 γ η t z-C z =
      (Real.exp (-γ*t):ℂ) • (B z-C z) + (Real.exp (-(γ+η)*t):ℂ) • (z-B z) := by
    rw [transfer_apply]; abel
  rw [he, norm_add_sq (𝕜 := ℂ)]
  simp only [inner_smul_left, inner_smul_right,
    (sector_orthogonal p r hp hp1 hr hr1 z).2.2, mul_zero, map_zero, add_zero,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring

theorem transfer_error_bound (γ η t : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : H) :
    ‖transfer p r hp hp1 hr hr1 γ η t z-C z‖ ≤ Real.exp (-γ*t)*‖z-C z‖ := by
  have hf := GibbsBlockRelaxation.fast_le_slow γ η t hη ht
  change Real.exp (-(γ+η)*t) ≤ Real.exp (-γ*t) at hf
  have hs : Real.exp (-(γ+η)*t)^2 ≤ Real.exp (-γ*t)^2 := by
    nlinarith [Real.exp_pos (-(γ+η)*t)]
  have hb := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖z-B z‖)
  have he := transfer_error_sq p r hp hp1 hr hr1 γ η t z
  have hz := centered_pythagoras p r hp hp1 hr hr1 z
  have hn : 0 ≤ Real.exp (-γ*t)*‖z-C z‖ := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  nlinarith [norm_nonneg (transfer p r hp hp1 hr hr1 γ η t z-C z)]

def constantVector : H := mk K₀ hK₀ (fun _ => 1)
def centeredVector (a : Fin 3) : H := mk K₀ hK₀ (innerMode a)

theorem constant_coordinates : coord (constantVector p r hp hp1 hr hr1) = 1 := by
  rw [constantVector, coordinates_mk, synthesis_constant]

theorem centered_coordinates (a : Fin 3) :
    coord (centeredVector p r hp hp1 hr hr1 a) = (p:ℂ) • modeMatrix a := by
  rw [centeredVector, coordinates_mk, synthesis_innerMode]

theorem scalar_constant : C (constantVector p r hp hp1 hr hr1) = constantVector p r hp hp1 hr hr1 := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [scalar_coordinates, constant_coordinates]
  simp [scalarPart, rhoN_trace]

theorem diagonal_constant : B (constantVector p r hp hp1 hr hr1) = constantVector p r hp hp1 hr hr1 := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [diagonal_coordinates, constant_coordinates]
  simp [diagonalPart]

theorem scalar_centered (a : Fin 3) : C (centeredVector p r hp hp1 hr hr1 a) = 0 := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [scalar_coordinates, centered_coordinates, map_zero]
  simp [scalarPart, mode_mean_zero]

theorem diagonal_modeMatrix (a : Fin 3) :
    diagonalPart (modeMatrix a) = if a=2 then modeMatrix a else 0 := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [modeMatrix, diagonalPart, centeredZ_entries, pauliX, pauliY, Fin.ext_iff]

theorem diagonal_centered (a : Fin 3) :
    B (centeredVector p r hp hp1 hr hr1 a) =
      if a=2 then centeredVector p r hp hp1 hr hr1 a else 0 := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [diagonal_coordinates, centered_coordinates]
  change diagonalLinear ((p:ℂ) • modeMatrix a) = _
  rw [map_smul]
  change (p:ℂ) • diagonalPart (modeMatrix a) = _
  rw [diagonal_modeMatrix]
  split_ifs <;> simp [centered_coordinates]

theorem transfer_constant (γ η t : ℝ) :
    transfer p r hp hp1 hr hr1 γ η t (constantVector p r hp hp1 hr hr1) =
      constantVector p r hp hp1 hr hr1 := by
  rw [transfer_apply, scalar_constant, diagonal_constant]
  simp

theorem transfer_centered (γ η t : ℝ) (a : Fin 3) :
    transfer p r hp hp1 hr hr1 γ η t (centeredVector p r hp hp1 hr hr1 a) =
      (Real.exp (-(if a=2 then γ else γ+η)*t):ℂ) • centeredVector p r hp hp1 hr hr1 a := by
  rw [transfer_apply, scalar_centered, diagonal_centered]
  split_ifs <;> simp

theorem quotient_four_modes_span (hpos : 0 < p) (z : H) :
    ∃ c : Fin 4 → ℂ, z = ∑ i,c i • mk K₀ hK₀ (fourMode i) := by
  obtain ⟨c,hc⟩ := fourMode_spans hpos r (coord z)
  refine ⟨c,?_⟩
  apply coordinates_injective p r hp hp1 hr hr1
  simpa only [map_sum, map_smul, coordinates_mk] using hc.symm

theorem centered_norm_sq (a : Fin 3) :
    ‖centeredVector p r hp hp1 hr hr1 a‖^2 = modeNorm a*p^2 :=
  innerMode_norm_sq p r hp hp1 hr hr1 a

theorem centered_nonzero (hpos : 0 < p) (a : Fin 3) :
    centeredVector p r hp hp1 hr hr1 a ≠ 0 := by
  intro hz
  have h := centered_norm_sq p r hp hp1 hr hr1 a
  rw [hz, norm_zero, zero_pow (by decide)] at h
  have hm : 0 < modeNorm a := by fin_cases a <;> norm_num [modeNorm]
  have hpp : 0 < p^2 := sq_pos_of_pos hpos
  nlinarith

theorem constant_nonzero : constantVector p r hp hp1 hr hr1 ≠ 0 := by
  intro h
  have hn := constant_norm_sq p r hp hp1 hr hr1
  change ‖constantVector p r hp hp1 hr hr1‖^2=1 at hn
  simp [h] at hn

theorem transfer_centered_norm_sq (γ η t : ℝ) (a : Fin 3) :
    ‖transfer p r hp hp1 hr hr1 γ η t (centeredVector p r hp hp1 hr hr1 a)‖^2 =
      modeNorm a*p^2 * Real.exp (-(if a=2 then γ else γ+η)*t)^2 := by
  rw [transfer_centered, norm_smul, mul_pow, centered_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring


theorem scalar_complement_norm (z : H) : ‖z-C z‖ ≤ ‖z‖ := by
  have h := norm_add_sq (𝕜 := ℂ) (C z) (z-C z)
  rw [scalar_error_orthogonal] at h
  have hsum : C z+(z-C z)=z := by abel
  rw [hsum] at h
  simp only [map_zero, mul_zero, add_zero] at h
  nlinarith [sq_nonneg ‖C z‖,norm_nonneg z,norm_nonneg (z-C z)]

theorem centered_operator_bound (γ η t : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    ‖transfer p r hp hp1 hr hr1 γ η t-C‖ ≤ Real.exp (-γ*t) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro z
  change ‖transfer p r hp hp1 hr hr1 γ η t z-C z‖ ≤ _
  exact (transfer_error_bound p r hp hp1 hr hr1 γ η t hη ht z).trans
    (mul_le_mul_of_nonneg_left (scalar_complement_norm p r hp hp1 hr hr1 z) (Real.exp_pos _).le)

theorem centered_operator_lower (hpos : 0 < p) (γ η t : ℝ) :
    Real.exp (-γ*t) ≤ ‖transfer p r hp hp1 hr hr1 γ η t-C‖ := by
  let z := centeredVector p r hp hp1 hr hr1 2
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr (centered_nonzero p r hp hp1 hr hr1 hpos 2)
  have he : (transfer p r hp hp1 hr hr1 γ η t-C) z = (Real.exp (-γ*t):ℂ) • z := by
    change transfer p r hp hp1 hr hr1 γ η t z-C z = _
    rw [transfer_centered, scalar_centered]
    simp [z]
  have hn := (transfer p r hp hp1 hr hr1 γ η t-C).le_opNorm z
  rw [he, norm_smul] at hn
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  exact (mul_le_mul_iff_of_pos_right hz).mp hn

theorem centered_operator_norm (hpos : 0 < p) (γ η t : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    ‖transfer p r hp hp1 hr hr1 γ η t-C‖ = Real.exp (-γ*t) :=
  le_antisymm (centered_operator_bound p r hp hp1 hr hr1 γ η t hη ht)
    (centered_operator_lower p r hp hp1 hr hr1 hpos γ η t)

theorem scalar_fixed_iff (z : H) :
    C z=z ↔ ∃ c : ℂ, z=c • constantVector p r hp hp1 hr hr1 := by
  constructor
  · intro hz
    refine ⟨(rhoN*coord z).trace,?_⟩
    apply coordinates_injective p r hp hp1 hr hr1
    rw [map_smul, constant_coordinates]
    have h := scalar_coordinates p r hp hp1 hr hr1 z
    rw [hz] at h
    exact h
  · rintro ⟨c,rfl⟩
    rw [map_smul, scalar_constant]

theorem transfer_fixed_scalar (γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) (z : H) :
    transfer p r hp hp1 hr hr1 γ η t z=z ↔ C z=z := by
  constructor
  · intro hz
    have h := transfer_error_bound p r hp hp1 hr hr1 γ η t hη ht.le z
    rw [hz] at h
    have ha : Real.exp (-γ*t)<1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    have hn : ‖z-C z‖=0 := by nlinarith [norm_nonneg (z-C z)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
  · intro hc
    have hb := diagonal_after_scalar p r hp hp1 hr hr1 z
    rw [hc] at hb
    simp [transfer_apply, hc, hb]

theorem transfer_zero_reset (η t : ℝ) (z : H) :
    transfer p r hp hp1 hr hr1 0 η t z =
      B z + (Real.exp (-η*t):ℂ) • (z-B z) := by
  rw [transfer_apply]
  simp only [neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_smul, zero_add]
  abel

theorem transfer_fixed_diagonal (η t : ℝ) (hη : 0 < η) (ht : 0 < t) (z : H) :
    transfer p r hp hp1 hr hr1 0 η t z=z ↔ B z=z := by
  rw [transfer_zero_reset]
  constructor
  · intro h
    have he : (Real.exp (-η*t):ℂ) • (z-B z) = z-B z := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using h
    have hn := congrArg norm he
    rw [norm_smul] at hn
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
    have ha : Real.exp (-η*t)<1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    have hz : ‖z-B z‖=0 := by nlinarith [norm_nonneg (z-B z)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · intro h
    simp [h]

theorem diagonal_fixed_iff_range (z : H) :
    B z=z ↔ z ∈ (B).range := by
  constructor
  · intro h
    exact ⟨z,h⟩
  · rintro ⟨w,rfl⟩
    exact diagonal_twice p r hp hp1 hr hr1 w

def diagonalRangeCoordinates : (B).range →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun z i := coord z.val i i
  map_add' z w := by ext i; simp
  map_smul' c z := by ext i; simp

theorem range_diagonal_coordinates (z : (B).range) : diagonalPart (coord z.val) = coord z.val := by
  obtain ⟨w,hw⟩ := z.property
  rw [← hw]
  change diagonalPart (coord (B w)) = coord (B w)
  simp only [diagonal_coordinates, diagonal_idempotent]

theorem diagonalRangeCoordinates_injective : Function.Injective (diagonalRangeCoordinates p r hp hp1 hr hr1) := by
  intro z w h
  apply Subtype.ext
  apply coordinates_injective p r hp hp1 hr hr1
  rw [← range_diagonal_coordinates p r hp hp1 hr hr1 z,
    ← range_diagonal_coordinates p r hp hp1 hr hr1 w]
  unfold diagonalPart
  congr 1

theorem diagonalRangeCoordinates_surjective (hpos : 0 < p) :
    Function.Surjective (diagonalRangeCoordinates p r hp hp1 hr hr1) := by
  intro v
  obtain ⟨z,hz⟩ := coordinates_surjective p r hp hp1 hr hr1 hpos (Matrix.diagonal v)
  refine ⟨⟨B z,⟨z,rfl⟩⟩,?_⟩
  ext i
  change coord (B z) i i = v i
  rw [diagonal_coordinates, hz]
  simp [diagonalPart]

theorem diagonal_range_finrank (hpos : 0 < p) : Module.finrank ℂ (B).range = 2 := by
  let e := LinearEquiv.ofBijective (diagonalRangeCoordinates p r hp hp1 hr hr1)
    ⟨diagonalRangeCoordinates_injective p r hp hp1 hr hr1,
      diagonalRangeCoordinates_surjective p r hp hp1 hr hr1 hpos⟩
  rw [e.finrank_eq]
  simp

theorem time_zero_fixed_all (γ η : ℝ) (z : H) : transfer p r hp hp1 hr hr1 γ η 0 z=z := by
  rw [transfer_zero, one_apply_eq_self]

theorem time_zero_fixed_finrank (hpos : 0 < p) :
    Module.finrank ℂ H=4 := reconstructed_finrank p r hp hp1 hr hr1 hpos

theorem rates_zero_identity (t : ℝ) : transfer p r hp hp1 hr hr1 0 0 t=1 := by
  ext z
  rw [transfer_zero_reset]
  simp

/-- Generator of the actual quotient transfer; no physical clock calibration is asserted. -/
def generator (γ η : ℝ) : H →L[ℂ] H := (γ:ℂ) • (1-C)+(η:ℂ) • (1-B)

theorem complementary_positive (P : H →L[ℂ] H) (hs : P.IsSymmetric)
    (hi : ∀ z,P (P z)=P z) : (1-P).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨ContinuousLinearMap.isPositive_one.isSymmetric.sub hs,?_⟩
  intro z
  change 0 ≤ (⟪z-P z,z⟫_ℂ).re
  have hz : P (z-P z)=0 := by rw [map_sub, hi, sub_self]
  have ho := hs (z-P z) z
  change ⟪P (z-P z),z⟫_ℂ = ⟪z-P z,P z⟫_ℂ at ho
  rw [hz, inner_zero_left] at ho
  have he : ⟪z-P z,z⟫_ℂ = ⟪z-P z,z-P z⟫_ℂ := by rw [inner_sub_right, ← ho, sub_zero]
  rw [he]
  exact inner_self_nonneg (𝕜 := ℂ) (x := z-P z)

theorem generator_positive (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    (generator p r hp hp1 hr hr1 γ η).IsPositive := by
  exact ((complementary_positive p r hp hp1 hr hr1 C
    (scalar_symmetric p r hp hp1 hr hr1) (scalar_twice p r hp hp1 hr hr1)).smul_of_nonneg
      (by exact_mod_cast hγ)).add
    ((complementary_positive p r hp hp1 hr hr1 B
    (diagonal_symmetric p r hp hp1 hr hr1) (diagonal_twice p r hp hp1 hr hr1)).smul_of_nonneg
      (by exact_mod_cast hη))

theorem generator_selfAdjoint (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    IsSelfAdjoint (generator p r hp hp1 hr hr1 γ η) :=
  (generator_positive p r hp hp1 hr hr1 γ η hγ hη).isSelfAdjoint

theorem generator_transfer (γ η t : ℝ) (z : H) :
    generator p r hp hp1 hr hr1 γ η (transfer p r hp hp1 hr hr1 γ η t z) =
      ((γ:ℂ)*(Real.exp (-γ*t):ℂ)) • (B z-C z) +
      (((γ+η:ℝ):ℂ)*(Real.exp (-(γ+η)*t):ℂ)) • (z-B z) := by
  simp only [generator, _root_.add_apply, _root_.smul_apply, _root_.sub_apply,
    one_apply_eq_self, transfer_apply, map_add, map_smul, map_sub,
    scalar_twice, diagonal_twice, scalar_after_diagonal, diagonal_after_scalar,
    Complex.ofReal_add]
  module

theorem orbit_hasDerivAt (γ η t : ℝ) (z : H) :
    HasDerivAt (fun s : ℝ => transfer p r hp hp1 hr hr1 γ η s z)
      (-generator p r hp hp1 hr hr1 γ η (transfer p r hp hp1 hr hr1 γ η t z)) t := by
  have hs : HasDerivAt (fun s : ℝ => Real.exp (-γ*s)) (Real.exp (-γ*t)*(-γ)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-γ)).exp
  have hf : HasDerivAt (fun s : ℝ => Real.exp (-(γ+η)*s))
      (Real.exp (-(γ+η)*t)*(-(γ+η))) t := by
    simpa using ((hasDerivAt_id t).const_mul (-(γ+η))).exp
  have hd := ((hasDerivAt_const t (C z)).add
    (hs.ofReal_comp.smul_const (B z-C z))).add (hf.ofReal_comp.smul_const (z-B z))
  simp only [transfer_apply]
  convert hd using 1
  · rfl
  · rw [← transfer_apply, generator_transfer]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, zero_add]
    module

theorem orbit_continuous (γ η : ℝ) (z : H) :
    Continuous (fun t : ℝ => transfer p r hp hp1 hr hr1 γ η t z) :=
  continuous_iff_continuousAt.mpr (fun t => (orbit_hasDerivAt p r hp hp1 hr hr1 γ η t z).continuousAt)

open Filter
open scoped Topology

theorem decay_tendsto (k : ℝ) (hk : 0 < k) :
    Tendsto (fun t : ℝ => (Real.exp (-k*t):ℂ)) atTop (𝓝 0) := by
  have hm := Filter.Tendsto.const_mul_atTop hk (Filter.tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  have he : Tendsto (fun t : ℝ => Real.exp (-k*t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hm)
  simpa only [Function.comp_def, Complex.ofReal_zero] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp he

theorem transfer_tendsto_scalar (γ η : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (z : H) :
    Tendsto (fun t : ℝ => transfer p r hp hp1 hr hr1 γ η t z) atTop (𝓝 (C z)) := by
  have hs := decay_tendsto γ hγ
  have hf := decay_tendsto (γ+η) (by linarith)
  have hC : Tendsto (fun _ : ℝ => C z) atTop (𝓝 (C z)) := tendsto_const_nhds
  have hBC : Tendsto (fun _ : ℝ => B z-C z) atTop (𝓝 (B z-C z)) := tendsto_const_nhds
  have hIB : Tendsto (fun _ : ℝ => z-B z) atTop (𝓝 (z-B z)) := tendsto_const_nhds
  simpa only [transfer_apply, zero_smul, add_zero] using (hC.add (hs.smul hBC)).add (hf.smul hIB)

theorem transfer_tendsto_diagonal (η : ℝ) (hη : 0 < η) (z : H) :
    Tendsto (fun t : ℝ => transfer p r hp hp1 hr hr1 0 η t z) atTop (𝓝 (B z)) := by
  have hB : Tendsto (fun _ : ℝ => B z) atTop (𝓝 (B z)) := tendsto_const_nhds
  have hIB : Tendsto (fun _ : ℝ => z-B z) atTop (𝓝 (z-B z)) := tendsto_const_nhds
  simpa only [transfer_zero_reset, zero_smul, add_zero] using hB.add ((decay_tendsto η hη).smul hIB)

/-- Observable dual of the actual concatenated reset/dephasing jumps. -/
def observableGenerator (γ η : ℝ) (A : Mat2) : Mat2 :=
  (γ:ℂ) • (scalarPart A-A) + (η:ℂ) • (diagonalPart A-A)

theorem generator_coordinates (γ η : ℝ) (z : H) :
    coord (-generator p r hp hp1 hr hr1 γ η z) = observableGenerator γ η (coord z) := by
  simp only [generator, _root_.add_apply, _root_.smul_apply, _root_.sub_apply,
    one_apply_eq_self, map_neg, map_add, map_smul, map_sub,
    scalar_coordinates, diagonal_coordinates, observableGenerator]
  module

theorem diagonal_trace_dual (A X : Mat2) :
    (A*diagonalPart X).trace = (diagonalPart A*X).trace := by
  simp [diagonalPart, Matrix.trace, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem scalar_trace_dual (A X : Mat2) :
    (A*(X.trace • rhoN)).trace = (scalarPart A*X).trace := by
  simp only [scalarPart, mul_smul_comm, smul_mul_assoc, Matrix.trace_smul, one_mul,
    smul_eq_mul]
  rw [Matrix.trace_mul_comm A rhoN]
  ring

theorem actual_generator_duality (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (A X : Mat2) :
    (A*OpenSystems.lindbladGenerator 0 (GibbsBlockRelaxation.jumps signature weights γ η) X).trace =
      (observableGenerator γ η A*X).trace := by
  rw [GibbsBlockRelaxation.generator_state signature weights weights_nonnegative
    weights_normalized γ η hγ hη, weights_density, singleton_expectation]
  simp only [observableGenerator, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_sub, sub_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub,
    diagonal_trace_dual]
  simp only [scalarPart, smul_mul_assoc, one_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Matrix.trace_mul_comm A rhoN]
  ring

theorem quotient_generator_GKSL (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (z : H) (X : Mat2) :
    (coord z*OpenSystems.lindbladGenerator 0 (GibbsBlockRelaxation.jumps signature weights γ η) X).trace =
      (coord (-generator p r hp hp1 hr hr1 γ η z)*X).trace := by
  rw [generator_coordinates, actual_generator_duality γ η hγ hη]

theorem complexVector_decomposition :
    mk K₀ hK₀ complexMode =
      centeredVector p r hp hp1 hr hr1 0 + Complex.I • centeredVector p r hp hp1 hr hr1 1 := by
  apply coordinates_injective p r hp hp1 hr hr1
  rw [map_add, map_smul, coordinates_mk, synthesis_complexMode,
    centered_coordinates, centered_coordinates]
  change (p:ℂ) • (pauliX+Complex.I • pauliY) = (p:ℂ) • pauliX + Complex.I • ((p:ℂ) • pauliY)
  module

theorem transfer_complex (γ η t : ℝ) :
    transfer p r hp hp1 hr hr1 γ η t (mk K₀ hK₀ complexMode) =
      (Real.exp (-(γ+η)*t):ℂ) • mk K₀ hK₀ complexMode := by
  rw [complexVector_decomposition, map_add, map_smul, transfer_centered, transfer_centered]
  simp only [show (0:Fin 3)≠2 by decide, show (1:Fin 3)≠2 by decide, if_false]
  module

theorem transfer_complex_norm_sq (γ η t : ℝ) :
    ‖transfer p r hp hp1 hr hr1 γ η t (mk K₀ hK₀ complexMode)‖^2 =
      (48*p^2/25)*Real.exp (-(γ+η)*t)^2 := by
  rw [transfer_complex, norm_smul, mul_pow, complexMode_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring

theorem transfer_complex_nonzero (hpos : 0 < p) (γ η t : ℝ) :
    transfer p r hp hp1 hr hr1 γ η t (mk K₀ hK₀ complexMode) ≠ 0 := by
  intro hz
  have h := transfer_complex_norm_sq p r hp hp1 hr hr1 γ η t
  rw [hz, norm_zero, zero_pow (by decide)] at h
  have hprod : 0 < (48*p^2/25)*Real.exp (-(γ+η)*t)^2 := by positivity
  linarith

theorem transfer_z_norm_sq (γ η t : ℝ) :
    ‖transfer p r hp hp1 hr hr1 γ η t (centeredVector p r hp hp1 hr hr1 2)‖^2 =
      (576*p^2/625)*Real.exp (-γ*t)^2 := by
  rw [transfer_centered_norm_sq]
  change (576/625:ℝ)*p^2*Real.exp (-γ*t)^2 = _
  ring

theorem transfer_not_scalar (hpos : 0 < p) (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (hrate : 0 < γ ∨ 0 < η) (ht : 0 < t) (c : ℂ) :
    transfer p r hp hp1 hr hr1 γ η t ≠ c • (1 : H →L[ℂ] H) := by
  intro he
  have h0 := congrArg (fun T : H →L[ℂ] H => coord (T (constantVector p r hp hp1 hr hr1)) 0 0) he
  rw [transfer_constant] at h0
  simp only [_root_.smul_apply, one_apply_eq_self, map_smul, constant_coordinates,
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0
  have hc : c=1 := h0.symm
  have hx := congrArg (fun T : H →L[ℂ] H => T (centeredVector p r hp hp1 hr hr1 0)) he
  rw [hc, one_smul, transfer_centered] at hx
  norm_num only [show (0:Fin 3)≠2 by decide, if_false, one_apply_eq_self] at hx
  have hn := congrArg norm hx
  rw [norm_smul] at hn
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  have ha : Real.exp (-(γ+η)*t)<1 := Real.exp_lt_one_iff.mpr (by rcases hrate with h|h <;> nlinarith)
  have hz := norm_pos_iff.mpr (centered_nonzero p r hp hp1 hr hr1 hpos 0)
  nlinarith

theorem transfer_fixed_line (γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) (z : H) :
    transfer p r hp hp1 hr hr1 γ η t z=z ↔
      ∃ c : ℂ,z=c • constantVector p r hp hp1 hr hr1 := by
  rw [transfer_fixed_scalar p r hp hp1 hr hr1 γ η t hγ hη ht, scalar_fixed_iff]

theorem transfer_fixed_diagonal_range (η t : ℝ) (hη : 0 < η) (ht : 0 < t) (z : H) :
    transfer p r hp hp1 hr hr1 0 η t z=z ↔ z ∈ (B).range := by
  rw [transfer_fixed_diagonal p r hp hp1 hr hr1 η t hη ht, diagonal_fixed_iff_range]

end Quotient

/-- Removing the dephasing rate recovers the actual reset channel actions. -/
theorem zero_dephasing_actions (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (A : Mat2) :
    state γ 0 t A = Phi (Real.exp (-γ*t)) A ∧
      observable γ 0 t A = Psi (Real.exp (-γ*t)) A := by
  constructor
  · rw [state_formula γ 0 t hγ (by norm_num) ht]
    simp only [add_zero, Phi]
    module
  · rw [observable_formula γ 0 t hγ (by norm_num) ht]
    simp only [add_zero, Psi]
    module

theorem unit_rates_separate :
    0 < Real.exp (-(1+1:ℝ)*1) ∧
      Real.exp (-(1+1:ℝ)*1) < Real.exp (-(1:ℝ)*1) ∧
      Real.exp (-(1:ℝ)*1) < 1 := by
  refine ⟨Real.exp_pos _, Real.exp_lt_exp.mpr (by norm_num), Real.exp_lt_one_iff.mpr (by norm_num)⟩

theorem side_reset_decay :
    ‖transfer (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 1 1
      (centeredVector (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0)‖^2 =
      (6/25:ℝ)*Real.exp (-4) := by
  rw [transfer_centered_norm_sq]
  have he : Real.exp (-2)^2 = Real.exp (-4) := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  norm_num [modeNorm, he, Fin.ext_iff]

theorem reset_transfer_rank_one (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    Module.finrank ℂ (Reconstructed 0 r (by norm_num) (by norm_num) hr hr1)=1 :=
  reset_finrank r hr hr1

/-- The corresponding two-event process uses exactly the same inserted gap. -/
def insertedTwoTree (p γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : Tree (Fin 2) Unit 6 2 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (centralStep p γ η t hp hp1 hγ hη ht) (fun _ => .done))

def insertedTwoKernel (p γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (i j : Fin 6) : ℂ :=
  (weight (Fin 2) Unit 6 (insertedTwoTree p γ η t hp hp1 hγ hη ht) (i,j,())
    (GibbsMultilevelReflection.joint rhoN) : ℂ)

theorem insertedTwoKernel_trace (p γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (i j : Fin 6) :
    insertedTwoKernel p γ η t hp hp1 hγ hη ht i j =
      (PauliInstrumentReconstruction.effect j *
        state γ η t (Phi (p*p) (Gamma (PauliInstrumentReconstruction.effect i)))).trace := by
  unfold insertedTwoKernel weight
  change (((centralStep p γ η t hp hp1 hγ hη ht).branch (Fin 2) Unit 6 j
    ((step 1 (by norm_num) le_rfl).branch (Fin 2) Unit 6 i
      (GibbsMultilevelReflection.joint rhoN))).trace.re : ℂ) = _
  rw [step_branch, centralStep_branch, Phi_one, branch_rhoN,
    GibbsMultilevelReflection.joint_trace, branch_trace]
  apply hermitian_product_real _ _ (effect_adjoint j)
  rw [Phi_Gamma, intertwining γ η t hγ hη ht, Gamma_adjoint,
    observable_adjoint, Psi_adjoint, effect_adjoint]

theorem state_sum {ι : Type*} [Fintype ι] (γ η t : ℝ) (A : ι → Mat2) :
    state γ η t (∑ i,A i) = ∑ i,state γ η t (A i) := by
  simp only [state, krausMap, Matrix.mul_sum, Matrix.sum_mul]
  rw [Finset.sum_comm]

/-- Literal outer-event marginal, without a replacement of chronology. -/
theorem inserted_outer_marginal (p r γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (i j : Fin 6) :
    ∑ o,∑ o',kernel p r γ η t hp hp1 hr hr1 hγ hη ht (i,o) (j,o') =
      insertedTwoKernel p γ η t hp hp1 hγ hη ht i j := by
  simp_rw [kernel_trace]
  simp only [← Matrix.trace_sum, ← Matrix.sum_mul, halfEffect_outer,
    ← Matrix.mul_sum, ← state_sum, ← Phi_sum, ← Gamma_sum]
  rw [insertedTwoKernel_trace]

/-!
The reconstruction, transfer and generator above refer to the actual four-event
process at the fixed faithful qubit density. The inserted central gap is not a
uniform translation of all measurement times. Rank-one complete reset and both
side endpoints are retained. No arbitrary-state or arbitrary-depth extension,
continuum locality, physical mass gap, external bath, postselection or physical
clock calibration follows.
-/

end SKEFTHawking.QuantumNetwork.NontracialReflectionDynamics
