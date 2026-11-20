import SKEFTHawking.FiniteGibbsMultilevelReflection
import SKEFTHawking.QuantumNetwork.NamedChannels

/-!
# Full matrix reconstruction from a finite Pauli intervention process

The six-outcome Lüders instrument uses the two signs of each actual Pauli matrix.
The kernel is defined from two successive applications of that same instrument
at the maximally mixed state, before deriving its weighted Gram identity. The
null quotient is isometric to all faithful complex two-by-two observables and
has complex dimension four. Explicit null coefficients, orthonormal spanning
modes and a nonzero matrix-image commutator describe this identification.

Equal two-event probabilities need not mean equal output states: the actual
x+/z+ and z+/x+ histories give distinct unnormalized projectors. Impossible
opposite-sign histories remain in the process. No coefficientwise quotient
algebra, generic multitime positivity, continuum reconstruction or physical-clock
identification is asserted.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.PauliInstrumentReconstruction
open Matrix FiniteInterventionProcess
open scoped BigOperators ComplexOrder Kronecker

/-- Outcomes are ordered x+, x-, y+, y-, z+, z-. -/
def outcomeEquiv : Fin 6 ≃ Fin 3 × Fin 2 := (@finProdFinEquiv 3 2).symm

def sigma : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliX, pauliY, pauliZ]
def sign (o : Fin 6) : ℂ := if (outcomeEquiv o).2 = 0 then 1 else -1
def projector (o : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • (1 + sign o • sigma (outcomeEquiv o).1)

theorem projector_adjoint (o : Fin 6) : (projector o)ᴴ = projector o := by
  fin_cases o <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [projector, sign, outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, sigma, pauliX, pauliY, pauliZ,
      Matrix.conjTranspose_apply, Matrix.one_apply]

theorem projector_square (o : Fin 6) : projector o * projector o = projector o := by
  fin_cases o <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [projector, sign, outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, sigma, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      ring_nf <;> norm_num [Complex.I_sq]

theorem projector_trace (o : Fin 6) : (projector o).trace = 1 := by
  fin_cases o <;> norm_num [projector, sign, outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, sigma,
    pauliX, pauliY, pauliZ, Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]

theorem projector_sum : ∑ o, projector o = (3 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, projector, sign, outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, sigma,
      pauliX, pauliY, pauliZ, Matrix.one_apply]

theorem projector_pair (a : Fin 3) :
    ∑ s : Fin 2, projector (outcomeEquiv.symm (a,s)) = 1 := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_two, projector, sign, outcomeEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat, sigma, pauliX, pauliY, pauliZ, Matrix.one_apply]

def amplitude : ℂ := (Real.sqrt 3 : ℂ)⁻¹

theorem amplitude_real : star amplitude = amplitude := by simp [amplitude]

theorem amplitude_square : amplitude * amplitude = 1/3 := by
  rw [amplitude, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

def instrument : FiniteInstrument (Fin 2) 6 where
  count := 1
  operators o _ := amplitude • projector o
  normalized := by
    simp only [Fin.sum_univ_one, Matrix.conjTranspose_smul, projector_adjoint,
      amplitude_real, smul_mul_smul, amplitude_square, projector_square]
    rw [← Finset.smul_sum, projector_sum, smul_smul]
    norm_num

def effect (o : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ := (1/3 : ℂ) • projector o

theorem instrument_effect (o : Fin 6) :
    (instrument.operators o ⟨0, by decide⟩)ᴴ * instrument.operators o ⟨0, by decide⟩ = effect o := by
  simp [instrument, effect, Matrix.conjTranspose_smul, projector_adjoint,
    amplitude_real, smul_smul, amplitude_square, projector_square]

theorem instrument_branch (o : Fin 6) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    instrument.branch o X = (1/3 : ℂ) • (projector o * X * projector o) := by
  simp [FiniteInstrument.branch, instrument, krausMap, Matrix.conjTranspose_smul,
    projector_adjoint, amplitude_real, smul_smul,
    amplitude_square]

def rho : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • 1

def step : Step (Fin 2) Unit 6 := localStep (Fin 2) Unit 6 instrument

def tree : Tree (Fin 2) Unit 6 2 := .node step (fun _ => .node step (fun _ => .done))

/-- Defined from actual chronological history probabilities, before any Gram formula. -/
def kernel (o p : Fin 6) : ℂ :=
  (weight (Fin 2) Unit 6 tree (o,p,()) (GibbsMultilevelReflection.joint rho) : ℂ)

theorem step_branch (o : Fin 6) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    step.branch (Fin 2) Unit 6 o (GibbsMultilevelReflection.joint X) =
      GibbsMultilevelReflection.joint (instrument.branch o X) := by
  rw [step, localStep_branch]
  exact GibbsMultilevelReflection.joint_kraus _ _

theorem actual_run (o p : Fin 6) :
    run (Fin 2) Unit 6 tree (o,p,()) (GibbsMultilevelReflection.joint rho) =
      GibbsMultilevelReflection.joint ((1/18 : ℂ) • (projector p * projector o * projector p)) := by
  change step.branch (Fin 2) Unit 6 p
    (step.branch (Fin 2) Unit 6 o (GibbsMultilevelReflection.joint rho)) = _
  rw [step_branch, step_branch, instrument_branch, instrument_branch]
  congr 1
  norm_num [rho, projector_square, smul_smul]

theorem projector_product_real (o p : Fin 6) :
    (((projector p * projector o).trace.re : ℝ) : ℂ) = (projector p * projector o).trace := by
  have hc : star ((projector p * projector o).trace) = (projector p * projector o).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, projector_adjoint,
      projector_adjoint, Matrix.trace_mul_comm]
  have hi : (projector p * projector o).trace.im = 0 := Complex.conj_eq_iff_im.mp hc
  apply Complex.ext
  · rfl
  · simpa using hi.symm

/-- The real-valued actual path weight is the full complex matrix trace. -/
theorem kernel_trace (o p : Fin 6) : kernel o p = (projector p * projector o).trace / 18 := by
  unfold kernel weight
  rw [actual_run, GibbsMultilevelReflection.joint_trace, Matrix.trace_smul]
  have hc : (projector p * projector o * projector p).trace = (projector p * projector o).trace := by
    rw [Matrix.trace_mul_cycle, projector_square]
  rw [hc]
  simp only [smul_eq_mul, Complex.mul_re]
  norm_num
  rw [projector_product_real]
  ring

/-- Only after constructing the actual process do we identify its central-state Gram. -/
theorem kernel_gram (o p : Fin 6) : kernel o p = (effect p * rho * (effect o)ᴴ).trace := by
  rw [kernel_trace]
  simp [effect, rho, Matrix.conjTranspose_smul, projector_adjoint, smul_smul, Matrix.trace_smul]
  ring

/-- All 36 actual histories, including opposite signs and the imaginary Pauli Y axis. -/
theorem kernel_table (o p : Fin 6) : kernel o p =
    if (outcomeEquiv o).1 = (outcomeEquiv p).1 then (if o=p then 1/18 else 0) else 1/36 := by
  rw [kernel_trace]
  fin_cases o <;> fin_cases p <;>
    norm_num [projector, sign, outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, sigma,
      pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two,
      Matrix.one_apply] <;> ring_nf <;> norm_num [Complex.I_sq]

theorem kernel_row (o : Fin 6) : ∑ p, kernel o p = 1/6 := by
  simp_rw [kernel_table]
  fin_cases o <;> norm_num [Fin.sum_univ_succ, outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.succ]

theorem kernel_total : ∑ o, ∑ p, kernel o p = 1 := by
  simp_rw [kernel_row]
  norm_num

theorem rho_density : IsDensityOperator rho := by
  constructor
  · exact Matrix.PosSemidef.one.smul (show (0:ℂ) ≤ 1/2 by
      norm_num [Complex.le_def])
  · norm_num [rho, Matrix.trace, Fin.sum_univ_two]

theorem initial_density : IsDensityOperator (GibbsMultilevelReflection.joint rho) := by
  refine ⟨rho_density.1.kronecker Matrix.PosSemidef.one, ?_⟩
  rw [GibbsMultilevelReflection.joint_trace, rho_density.2]

open FinitePositiveKernel
open scoped InnerProductSpace

def synthesis (F : Fin 6 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := ∑ o, F o • effect o

def synthesisLinear : (Fin 6 → ℂ) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := synthesis
  map_add' F G := by simp [synthesis, add_smul, Finset.sum_add_distrib]
  map_smul' z F := by simp [synthesis, Finset.smul_sum, smul_smul]

theorem rho_posDef : rho.PosDef := by
  exact Matrix.PosDef.one.smul (show (0:ℂ) < 1/2 by norm_num [Complex.lt_def])

theorem kernel_posSemidef : Matrix.PosSemidef kernel := by
  letI := Matrix.toMatrixSeminormedAddCommGroup rho rho_density.1
  letI := Matrix.toMatrixInnerProductSpace rho rho_density.1
  have hk : kernel = Matrix.gram ℂ effect := by
    ext o p
    exact kernel_gram o p
  rw [hk]
  exact Matrix.posSemidef_gram ℂ effect

/-- The complete complex coefficient pairing has the conjugate-first observable orientation. -/
theorem pairing_synthesis (F G : Fin 6 → ℂ) :
    pairing kernel F G = (synthesis G * rho * (synthesis F)ᴴ).trace := by
  letI := Matrix.toMatrixSeminormedAddCommGroup rho rho_density.1
  letI := Matrix.toMatrixInnerProductSpace rho rho_density.1
  have hk : kernel = Matrix.gram ℂ effect := by
    ext o p
    exact kernel_gram o p
  rw [hk]
  exact Matrix.star_dotProduct_gram_mulVec effect F G

theorem pairing_observable (F G : Fin 6 → ℂ) :
    pairing kernel F G =
      ⟪GibbsObservable.observable rho_density.1 (synthesis F),
        GibbsObservable.observable rho_density.1 (synthesis G)⟫_ℂ := by
  rw [GibbsObservable.inner_observable, pairing_synthesis]

/-- A right inverse for every complex matrix, without a Hermitian restriction. -/
def coefficients (X : Matrix (Fin 2) (Fin 2) ℂ) (o : Fin 6) : ℂ :=
  X.trace/2 + 3 * sign o * (sigma (outcomeEquiv o).1 * X).trace/2

theorem synthesis_coefficients (X : Matrix (Fin 2) (Fin 2) ℂ) :
    synthesis (coefficients X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [synthesis, coefficients, effect, projector, sign, outcomeEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat, Fin.succ, sigma, pauliX, pauliY, pauliZ, Matrix.trace,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

abbrev Reconstructed := Space kernel kernel_posSemidef
abbrev ObservableSpace := Space (GibbsObservable.gram rho) (GibbsObservable.gram_posSemidef rho_density.1)

theorem null_iff (F : Fin 6 → ℂ) : mk kernel kernel_posSemidef F = 0 ↔ synthesis F = 0 := by
  rw [mk_eq_zero_iff, pairing_synthesis]
  constructor
  · exact GibbsObservable.trace_weighted_eq_zero rho_posDef _
  · intro h
    simp [h]

def coefficientSynthesis : Coefficients kernel_posSemidef →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  synthesisLinear

theorem synthesis_null : nullSpace kernel kernel_posSemidef ≤ coefficientSynthesis.ker := by
  intro F hF
  change synthesis F = 0
  apply (null_iff F).mp
  rw [mk_eq_zero_iff]
  exact (mem_nullSpace_iff _ _ F).mp hF

/-- Descend the actual effect synthesis through precisely the zero-energy subspace. -/
def coordinates : Reconstructed →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  ((nullSpace kernel kernel_posSemidef).liftQ coefficientSynthesis synthesis_null).comp
    (quotientEquiv kernel kernel_posSemidef).symm.toLinearMap

theorem coordinates_mk (F : Fin 6 → ℂ) :
    coordinates (mk kernel kernel_posSemidef F) = synthesis F := by
  rw [← quotientEquiv_mk kernel_posSemidef F]
  simp only [coordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  rfl

theorem coordinates_bijective : Function.Bijective coordinates := by
  constructor
  · intro z w h
    obtain ⟨F,rfl⟩ := mk_surjective kernel kernel_posSemidef z
    obtain ⟨G,rfl⟩ := mk_surjective kernel kernel_posSemidef w
    rw [coordinates_mk, coordinates_mk] at h
    apply (mk_eq_mk_iff kernel kernel_posSemidef F G).mpr
    rw [pairing_synthesis]
    have hz : synthesis (F-G) = 0 := by
      change synthesisLinear (F-G) = 0
      exact (synthesisLinear.map_sub (F : Fin 6 → ℂ) G).trans (sub_eq_zero.mpr h)
    simp [hz]
  · intro X
    exact ⟨mk kernel kernel_posSemidef (coefficients X), by rw [coordinates_mk, synthesis_coefficients]⟩

def coordinateEquiv : Reconstructed ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearEquiv.ofBijective coordinates coordinates_bijective

theorem reconstructed_finrank : Module.finrank ℂ Reconstructed = 4 := by
  rw [coordinateEquiv.finrank_eq]
  simpa using Module.finrank_matrix ℂ ℂ (Fin 2) (Fin 2)

def embeddingLinear : Reconstructed →ₗ[ℂ] ObservableSpace :=
  (GibbsObservable.observableLinear rho_density.1).comp coordinates

theorem embeddingLinear_mk (F : Fin 6 → ℂ) :
    embeddingLinear (mk kernel kernel_posSemidef F) =
      GibbsObservable.observable rho_density.1 (synthesis F) := by
  change GibbsObservable.observable rho_density.1 (coordinates (mk kernel kernel_posSemidef F)) = _
  rw [coordinates_mk]

/-- Isometric identification with the full faithful matrix-observable space. -/
def embedding : Reconstructed →ₗᵢ[ℂ] ObservableSpace :=
  embeddingLinear.isometryOfInner (by
    intro z w
    obtain ⟨F,rfl⟩ := mk_surjective kernel kernel_posSemidef z
    obtain ⟨G,rfl⟩ := mk_surjective kernel kernel_posSemidef w
    rw [embeddingLinear_mk, embeddingLinear_mk, inner_mk, pairing_observable])

theorem embedding_mk (F : Fin 6 → ℂ) : embedding (mk kernel kernel_posSemidef F) =
    GibbsObservable.observable rho_density.1 (synthesis F) := embeddingLinear_mk F

theorem embedding_surjective : Function.Surjective embedding := by
  intro z
  obtain ⟨X,rfl⟩ := GibbsObservable.observable_surjective rho_density.1 z
  exact ⟨mk kernel kernel_posSemidef (coefficients X), by rw [embedding_mk, synthesis_coefficients]⟩

def difference (F : Fin 6 → ℂ) (a : Fin 3) : ℂ :=
  F (outcomeEquiv.symm (a,0))-F (outcomeEquiv.symm (a,1))

theorem synthesis_decomposition (F : Fin 6 → ℂ) :
    synthesis F = ((∑ o, F o)/6) • 1 + (difference F 0/6) • pauliX +
      (difference F 1/6) • pauliY + (difference F 2/6) • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [synthesis, difference, effect, projector, sign, outcomeEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat, Fin.succ, sigma, pauliX, pauliY, pauliZ, Fin.sum_univ_succ] <;> ring

theorem trace_synthesis (F : Fin 6 → ℂ) : (synthesis F).trace = (∑ o, F o)/3 := by
  simp [synthesis, effect, Matrix.trace_sum, Matrix.trace_smul, projector_trace,
    ← Finset.sum_mul, div_eq_mul_inv]

theorem trace_axis_synthesis (F : Fin 6 → ℂ) (a : Fin 3) :
    (sigma a * synthesis F).trace = difference F a/3 := by
  rw [synthesis_decomposition]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_one]
  fin_cases a <;>
    norm_num [sigma, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf
  all_goals rfl


/-- Three pair differences and the total coefficient sum describe the entire null space. -/
theorem synthesis_null_criterion (F : Fin 6 → ℂ) : synthesis F = 0 ↔
    (∀ a, difference F a = 0) ∧ (∑ o, F o) = 0 := by
  constructor
  · intro h
    constructor
    · intro a
      have ht := trace_axis_synthesis F a
      rw [h, Matrix.mul_zero, Matrix.trace_zero] at ht
      exact (div_eq_zero_iff.mp ht.symm).resolve_right (by norm_num)
    · have ht := trace_synthesis F
      rw [h, Matrix.trace_zero] at ht
      exact (div_eq_zero_iff.mp ht.symm).resolve_right (by norm_num)
  · rintro ⟨hd,hs⟩
    simp [synthesis_decomposition, hd, hs]

def nullVector : Fin 6 → ℂ := ![1,1,-1,-1,0,0]
def nullVector2 : Fin 6 → ℂ := ![1,1,0,0,-1,-1]

theorem nullVector_witness : nullVector ≠ 0 ∧ synthesis nullVector = 0 ∧
    mk kernel kernel_posSemidef nullVector = 0 := by
  have hs : synthesis nullVector = 0 := by
    apply (synthesis_null_criterion _).mpr
    constructor
    · intro a
      fin_cases a <;> norm_num [difference, nullVector, outcomeEquiv, finProdFinEquiv]
    · norm_num [nullVector, Fin.sum_univ_succ]
  refine ⟨?_, hs, (null_iff _).mpr hs⟩
  intro h
  have := congrFun h 0
  norm_num [nullVector] at this

theorem nullVector2_witness : nullVector2 ≠ 0 ∧ synthesis nullVector2 = 0 ∧
    mk kernel kernel_posSemidef nullVector2 = 0 := by
  have hs : synthesis nullVector2 = 0 := by
    apply (synthesis_null_criterion _).mpr
    constructor
    · intro a
      fin_cases a <;> norm_num [difference, nullVector2, outcomeEquiv, finProdFinEquiv]
    · norm_num [nullVector2, Fin.sum_univ_succ]
  refine ⟨?_, hs, (null_iff _).mpr hs⟩
  intro h
  have := congrFun h 0
  norm_num [nullVector2] at this

def axisMode (a : Fin 3) (o : Fin 6) : ℂ :=
  if (outcomeEquiv o).1=a then 3*sign o else 0

theorem synthesis_constant : synthesis (fun _ => 1) = 1 := by
  simp only [synthesis, effect, ← Finset.smul_sum, projector_sum, smul_smul]
  norm_num

theorem synthesis_axisMode (a : Fin 3) : synthesis (axisMode a) = sigma a := by
  rw [synthesis_decomposition]
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [axisMode, difference, sign, outcomeEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat, Fin.succ, sigma, pauliX, pauliY, pauliZ, Fin.sum_univ_succ]

def mode : Fin 4 → Fin 6 → ℂ := ![fun _ => 1, axisMode 0, axisMode 1, axisMode 2]
def modeMatrix : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![1,pauliX,pauliY,pauliZ]
def modeClass (a : Fin 4) : Reconstructed := mk kernel kernel_posSemidef (mode a)

theorem synthesis_mode (a : Fin 4) : synthesis (mode a) = modeMatrix a := by
  fin_cases a <;> simp [mode, modeMatrix, synthesis_constant, synthesis_axisMode, sigma]

theorem modeMatrix_adjoint (a : Fin 4) : (modeMatrix a)ᴴ = modeMatrix a := by
  fin_cases a <;> simp [modeMatrix, pauliX_conjTranspose, pauliY_conjTranspose, pauliZ_conjTranspose]

theorem modeMatrix_weighted_trace (a b : Fin 4) :
    (modeMatrix b * rho * (modeMatrix a)ᴴ).trace = if a=b then 1 else 0 := by
  rw [modeMatrix_adjoint]
  simp only [rho, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  fin_cases a <;> fin_cases b <;>
    norm_num [modeMatrix, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem modes_orthonormal (a b : Fin 4) :
    ⟪modeClass a, modeClass b⟫_ℂ = if a=b then 1 else 0 := by
  change pairing kernel (mode a) (mode b) = _
  rw [pairing_synthesis, synthesis_mode, synthesis_mode, modeMatrix_weighted_trace]

theorem modeClass_nonzero (a : Fin 4) : modeClass a ≠ 0 := by
  intro h
  have ht := modes_orthonormal a a
  rw [h] at ht
  simp at ht

/-- The four Pauli components reconstruct every complex matrix. -/
theorem matrix_mode_decomposition (X : Matrix (Fin 2) (Fin 2) ℂ) :
    X = ∑ a : Fin 4, ((modeMatrix a * X).trace/2) • modeMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modeMatrix, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- Every reconstructed class is a linear combination of the four orthonormal modes. -/
theorem modeClass_spanning (z : Reconstructed) :
    z = ∑ a : Fin 4, ((modeMatrix a * coordinates z).trace/2) • modeClass a := by
  apply coordinates_bijective.1
  rw [map_sum]
  simp only [map_smul]
  have hm (a : Fin 4) : coordinates (modeClass a) = modeMatrix a := by
    exact (coordinates_mk (mode a)).trans (synthesis_mode a)
  simp_rw [hm]
  exact matrix_mode_decomposition (coordinates z)

/-- Noncommutativity concerns matrix images, not coefficientwise quotient multiplication. -/
theorem matrix_image_commutator :
    synthesis (axisMode 0) * synthesis (axisMode 1) -
      synthesis (axisMode 1) * synthesis (axisMode 0) =
      (2*Complex.I) • synthesis (axisMode 2) := by
  simp only [synthesis_axisMode]
  change pauliX * pauliY - pauliY * pauliX = (2*Complex.I) • pauliZ
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem matrix_image_commutator_nonzero :
    synthesis (axisMode 0) * synthesis (axisMode 1) -
      synthesis (axisMode 1) * synthesis (axisMode 0) ≠ 0 := by
  rw [matrix_image_commutator, synthesis_axisMode]
  change (2*Complex.I) • pauliZ ≠ 0
  intro h
  have he := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => (X 0 0).im) h
  norm_num [pauliZ, Complex.mul_im] at he

/-- The actual order x+ then z+ produces the z+ projector with its path mass. -/
theorem actual_xz_state :
    run (Fin 2) Unit 6 tree (0,4,()) (GibbsMultilevelReflection.joint rho) =
      GibbsMultilevelReflection.joint ((1/36 : ℂ) • projector 4) := by
  rw [actual_run]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projector, sign, outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
      sigma, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Reversing those same interventions produces a different physical state. -/
theorem actual_zx_state :
    run (Fin 2) Unit 6 tree (4,0,()) (GibbsMultilevelReflection.joint rho) =
      GibbsMultilevelReflection.joint ((1/36 : ℂ) • projector 0) := by
  rw [actual_run]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projector, sign, outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
      sigma, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Equal path probabilities do not identify the unnormalized output matrices. -/
theorem actual_order_witness : kernel 0 4 = 1/36 ∧ kernel 4 0 = 1/36 ∧
    run (Fin 2) Unit 6 tree (0,4,()) (GibbsMultilevelReflection.joint rho) ≠
      run (Fin 2) Unit 6 tree (4,0,()) (GibbsMultilevelReflection.joint rho) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [kernel_table, outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat]
  · norm_num [kernel_table, outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat]
  · rw [actual_xz_state, actual_zx_state]
    intro h
    have he := congrArg (fun X : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ => X (0,()) (1,())) h
    norm_num [GibbsMultilevelReflection.joint, projector, sign, outcomeEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat, sigma, pauliX, pauliZ, Matrix.one_apply] at he

/-- The opposite-sign history is retained as an actual zero-probability outcome. -/
theorem opposite_sign_impossible (a : Fin 3) :
    kernel (outcomeEquiv.symm (a,0)) (outcomeEquiv.symm (a,1)) = 0 := by
  rw [kernel_table]
  simp only [Equiv.apply_symm_apply, ite_true]
  have h : outcomeEquiv.symm (a,0) ≠ outcomeEquiv.symm (a,1) := by
    intro he
    have := outcomeEquiv.symm.injective he
    have hs := congrArg Prod.snd this
    norm_num at hs
  simp [h]

end SKEFTHawking.QuantumNetwork.PauliInstrumentReconstruction
