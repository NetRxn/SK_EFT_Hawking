import SKEFTHawking.QuantumNetwork.FiniteQutritAveragedExamples
import SKEFTHawking.QuantumNetwork.FiniteGibbsClock

/-!
# Spectral evolution of the genuine six-feature quotient

The normalized coordinates below use the actual weighted pairing. The raw
symmetric matrix subtype is used only as a linear carrier, never with its
ambient matrix norm as a Hilbert norm.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritEuclideanTransfer
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteQutritPhysicalMemory FiniteQutritInvariantCarrier
open FiniteQutritInvariantReconstruction FiniteQutritAveragedTransfer
open FiniteQutritAveragedMixing
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace
open scoped Matrix.Norms.L2Operator

abbrev Coordinates := EuclideanSpace ℂ Index

private theorem vec6_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

def scale (i : Index) : ℝ := Real.sqrt (eigenNormSq i)

theorem scale_pos (i : Index) : 0 < scale i := Real.sqrt_pos.mpr (eigenNormSq_positive i)

theorem scale_sq (i : Index) : scale i ^ 2 = eigenNormSq i :=
  Real.sq_sqrt (le_of_lt (eigenNormSq_positive i))

def normalizeEquiv : (Index → ℂ) ≃ₗ[ℂ] (Index → ℂ) where
  toFun c i := c i / (scale i : ℂ)
  invFun c i := c i * (scale i : ℂ)
  left_inv c := by ext i; simp [ne_of_gt (scale_pos i)]
  right_inv c := by ext i; simp [ne_of_gt (scale_pos i)]
  map_add' c d := by ext i; simp [add_div]
  map_smul' z c := by ext i; simp [smul_eq_mul, mul_div_assoc]

def JLinear : Coordinates ≃ₗ[ℂ] FeatureSpace :=
  (EuclideanSpace.equiv Index ℂ).toLinearEquiv.trans
    (normalizeEquiv.trans (eigenEquiv.trans U.symm))

theorem U_JLinear (c : Coordinates) :
    (U (JLinear c) : Mat) = synthesis (fun i => c i / (scale i : ℂ)) := by
  change (U (U.symm (eigenEquiv (normalizeEquiv c))) : Mat) = _
  rw [U.apply_symm_apply]
  rfl

theorem JLinear_inner (c d : Coordinates) : ⟪JLinear c,JLinear d⟫_ℂ = ⟪c,d⟫_ℂ := by
  rw [← U_inner, U_JLinear, U_JLinear, ← pairing_trace, pairing_synthesis,
    PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (scale i : ℂ)^2 = (eigenNormSq i : ℂ) := by exact_mod_cast scale_sq i
  simp only [map_div₀, Complex.conj_ofReal, Complex.star_def]
  rw [← hs]
  have hn : (scale i : ℂ) ≠ 0 := by exact_mod_cast (scale_pos i).ne'
  rw [RCLike.inner_apply]
  field_simp

def J : Coordinates ≃ₗᵢ[ℂ] FeatureSpace where
  toLinearEquiv := JLinear
  norm_map' c := by
    have h := JLinear_inner c c
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h
    have hr : ‖JLinear c‖^2 = ‖c‖^2 := by exact_mod_cast h
    nlinarith [norm_nonneg (JLinear c), norm_nonneg c]

theorem J_inverse_coordinates (q : FeatureSpace) (i : Index) :
    J.symm q i = coefficients (U q) i * (scale i : ℂ) := rfl

def normalizedEigenvector (i : Index) : FeatureSpace :=
  U.symm ⟨(scale i : ℂ)⁻¹ • eigenvector i, (eigenvector_mem i).smul _⟩

def multiplier (a : Index → ℂ) : Coordinates →ₗ[ℂ] Coordinates where
  toFun c := WithLp.toLp 2 (fun i => a i * c i)
  map_add' c d := by ext i; simp [mul_add]
  map_smul' z c := by ext i; simp [smul_eq_mul, mul_left_comm]

def spectral (a : Index → ℂ) : FeatureSpace →ₗ[ℂ] FeatureSpace :=
  J.toLinearEquiv.toLinearMap.comp ((multiplier a).comp J.symm.toLinearEquiv.toLinearMap)

theorem spectral_apply (a : Index → ℂ) (q : FeatureSpace) :
    spectral a q = J (multiplier a (J.symm q)) := rfl

theorem spectral_one : spectral (fun _ => 1) = LinearMap.id := by
  ext q
  change J (WithLp.toLp 2 (fun i => 1 * J.symm q i)) = q
  simp

theorem spectral_mul (a b : Index → ℂ) :
    spectral (fun i => a i * b i) = (spectral a).comp (spectral b) := by
  ext q
  simp only [LinearMap.comp_apply, spectral_apply, J.symm_apply_apply]
  congr 1
  ext i
  simp [multiplier, mul_assoc]

def energy (i : Index) : ℝ := -Real.log (eigenvalue i)
def H : FeatureSpace →ₗ[ℂ] FeatureSpace := spectral (fun i => (energy i : ℂ))
def E (t : ℝ) : FeatureSpace →ₗ[ℂ] FeatureSpace :=
  spectral (fun i => (Real.exp (t * Real.log (eigenvalue i)) : ℂ))

theorem E_zero : E 0 = LinearMap.id := by simpa [E] using spectral_one

theorem E_add (s t : ℝ) : E (s+t) = (E s).comp (E t) := by
  unfold E
  rw [← spectral_mul]
  congr 1
  ext i
  simp [add_mul, Real.exp_add]

theorem eigenvalue_pos (i : Index) : 0 < eigenvalue i := by
  fin_cases i <;> norm_num [eigenvalue, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]

theorem E_one : E 1 = quotientTransfer := by
  ext q
  apply U.injective
  apply Subtype.ext
  rw [U_transfer]
  obtain ⟨c,rfl⟩ := J.surjective q
  change (U (J (multiplier _ (J.symm (J c)))) : Mat) = transfer (U (J c))
  rw [J.symm_apply_apply]
  change (U (JLinear (multiplier _ c)) : Mat) = transfer (U (JLinear c))
  rw [U_JLinear, U_JLinear, synthesis_transfer]
  congr 1
  ext i
  change ((Real.exp (1 * Real.log (eigenvalue i)) : ℝ) : ℂ) * c i / (scale i : ℂ) = _
  rw [one_mul, Real.exp_log (eigenvalue_pos i)]
  ring

theorem E_nat (n : ℕ) : E n = quotientIterate n := by
  induction n with
  | zero => simpa only [Nat.cast_zero, quotientIterate] using E_zero
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, E_add, ih, E_one]
    rfl

theorem spectral_inner (a : Index → ℂ) (q r : FeatureSpace) :
    ⟪q,spectral a r⟫_ℂ =
      ∑ i, star (J.symm q i) * a i * J.symm r i := by
  conv_lhs => rw [← J.apply_symm_apply q]
  rw [spectral_apply, J.inner_map_map, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [multiplier, LinearMap.coe_mk, AddHom.coe_mk,
    RCLike.inner_apply, Complex.star_def]
  ring

theorem spectral_selfadjoint (a : Index → ℝ) :
    (spectral (fun i => (a i : ℂ))).IsSymmetric := by
  intro q r
  rw [← inner_conj_symm, spectral_inner, spectral_inner]
  simp only [Complex.star_def, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem spectral_nonneg (a : Index → ℝ) (ha : ∀ i, 0 ≤ a i) (q : FeatureSpace) :
    0 ≤ (⟪q,spectral (fun i => (a i : ℂ)) q⟫_ℂ).re := by
  rw [spectral_inner, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  have h : (star (J.symm q i) * (a i : ℂ) * J.symm q i).re =
      a i * ‖J.symm q i‖^2 := by
    rw [Complex.sq_norm]
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.normSq_apply]
    ring
  rw [h]
  exact mul_nonneg (ha i) (sq_nonneg _)

theorem eigenvalue_le_one (i : Index) : eigenvalue i ≤ 1 := by
  fin_cases i <;> norm_num [eigenvalue, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]

theorem energy_nonneg (i : Index) : 0 ≤ energy i :=
  neg_nonneg.mpr (Real.log_nonpos (eigenvalue_pos i).le (eigenvalue_le_one i))

theorem H_selfadjoint : H.IsSymmetric := spectral_selfadjoint energy
theorem H_nonneg (q : FeatureSpace) : 0 ≤ (⟪q,H q⟫_ℂ).re :=
  spectral_nonneg energy energy_nonneg q
theorem E_selfadjoint (t : ℝ) : (E t).IsSymmetric := spectral_selfadjoint _
theorem E_nonneg (t : ℝ) (q : FeatureSpace) : 0 ≤ (⟪q,E t q⟫_ℂ).re :=
  spectral_nonneg _ (fun _ => (Real.exp_pos _).le) q

theorem U_spectral (a : Index → ℂ) (q : FeatureSpace) :
    (U (spectral a q) : Mat) = synthesis (fun i => a i * coefficients (U q) i) := by
  rw [spectral_apply]
  change (U (JLinear _ ) : Mat) = _
  rw [U_JLinear]
  congr 1
  ext i
  change a i * (coefficients (U q) i * (scale i : ℂ)) / (scale i : ℂ) = _
  have hn : (scale i : ℂ) ≠ 0 := by exact_mod_cast (scale_pos i).ne'
  field_simp

def temporalKernel (sx ty : ℝ × FeatureSpace) : ℂ := ⟪sx.2,E (sx.1+ty.1) ty.2⟫_ℂ

/-- The factorization holds even for negative times; probability consumers below
use only natural times and actual normalized experiments. -/
theorem temporal_factorization (s t : ℝ) (q r : FeatureSpace) :
    temporalKernel (s,q) (t,r) = ⟪E s q,E t r⟫_ℂ := by
  change ⟪q,E (s+t) r⟫_ℂ = _
  rw [E_add]
  exact ((E_selfadjoint s) q (E t r)).symm

theorem temporal_hermitian (sx ty : ℝ × FeatureSpace) :
    star (temporalKernel ty sx) = temporalKernel sx ty := by
  rw [temporal_factorization, temporal_factorization]
  exact inner_conj_symm _ _

theorem temporal_quadratic {A : Type*} [Fintype A] (v : A → ℝ × FeatureSpace)
    (c : A → ℂ) :
    (∑ i, ∑ j, star (c i) * temporalKernel (v i) (v j) * c j) =
      (‖∑ i, c i • E (v i).1 (v i).2‖^2 : ℝ) := by
  rw [Complex.ofReal_pow, ← RCLike.ofReal_eq_complex_ofReal,
    ← inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [temporal_factorization]
  ring

theorem temporal_psd {A : Type*} [Fintype A] (v : A → ℝ × FeatureSpace) :
    Matrix.PosSemidef (fun i j => temporalKernel (v i) (v j) : Matrix A A ℂ) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    exact temporal_hermitian _ _
  · intro c
    change 0 ≤ ∑ i, star (c i) * ∑ j, temporalKernel (v i) (v j) * c j
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [temporal_quadratic]
    exact_mod_cast sq_nonneg ‖∑ i, c i • E (v i).1 (v i).2‖

/-- Actual binary prefix, silent normalized ten-alternative middle channel,
and binary suffix. This retains the impossible silent outcomes. -/
def integerExperiment (i j : Index) (n : ℕ) :
    Tree Q Unit 2 (((suffixWord i).length+n)+(prefixWord j).length) :=
  appendTree (wordTree Unit (prefixWord j)) (fun _ =>
    appendTree (FiniteQutritAveragedExamples.silentTree Unit n)
      (fun _ => wordTree Unit (suffixWord i)))

def integerHistory (i j : Index) (n : ℕ) :
    History 2 (((suffixWord i).length+n)+(prefixWord j).length) :=
  appendHistory (prefixHistory j)
    (appendHistory (FiniteQutritAveragedExamples.silentHistory n) (suffixHistory i))

def integerWeight (i j : Index) (n : ℕ) : ℝ :=
  FiniteInterventionProcess.weight Q Unit 2 (integerExperiment i j n)
    (integerHistory i j n) (joint rho)

theorem integerWeight_trace (i j : Index) (n : ℕ) :
    integerWeight i j n = ((effect i * iterate n ((1/3 : ℂ) • effect j)).trace).re := by
  have ha (Y : Mat) : amplifiedIterate Unit n (joint Y) = joint (iterate n Y) :=
    amplified_iterate_product Unit n Y 1
  unfold integerWeight FiniteInterventionProcess.weight integerExperiment integerHistory
  rw [append_run, append_run, actual_run_joint, prefix_systemState,
    FiniteQutritAveragedExamples.silent_run, ha, actual_run_joint, joint_trace, suffix_trace]

theorem integer_normalized (i j : Index) (n : ℕ) :
    (∀ h, 0 ≤ FiniteInterventionProcess.weight Q Unit 2 (integerExperiment i j n) h (joint rho)) ∧
    (∑ h, FiniteInterventionProcess.weight Q Unit 2 (integerExperiment i j n) h (joint rho)) = 1 :=
  FiniteInterventionProcess.normalized_weights Q Unit 2 _
    FiniteQutritPhysicalMemoryExamples.attainer.density

theorem integerWeight_nonneg (i j : Index) (n : ℕ) : 0 ≤ integerWeight i j n :=
  (integer_normalized i j n).1 _

theorem integer_fine_records (i j : Index) (n : ℕ) :
    integerWeight i j n = ∑ h : History 10 n,
      (run Q Unit 2 (wordTree Unit (suffixWord i)) (suffixHistory i)
        (run Q Unit 10 (recordTree Unit n) h
          (run Q Unit 2 (wordTree Unit (prefixWord j)) (prefixHistory j) (joint rho)))).trace.re := by
  let L : Matrix (Q × Unit) (Q × Unit) ℂ →ₗ[ℂ] Matrix (Q × Unit) (Q × Unit) ℂ :=
    { toFun := run Q Unit 2 (wordTree Unit (suffixWord i)) (suffixHistory i)
      map_add' := run_add Q Unit 2 _ _
      map_smul' := run_smul Q Unit 2 _ _ }
  have hs := congrArg (fun X => (L X).trace.re)
    (discarded_history_system n ((1/3 : ℂ) • effect j))
  rw [map_sum, Matrix.trace_sum, Complex.re_sum] at hs
  rw [integerWeight_trace]
  dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk] at hs
  rw [actual_run_joint, joint_trace, suffix_trace] at hs
  simpa only [actual_run_joint, prefix_systemState] using hs.symm

theorem integer_temporal_trace (i j : Index) (m n : ℕ) :
    temporalKernel (m,feature i) (n,feature j) =
      (effect i * iterate (m+n) (effect j)).trace / 3 := by
  change ⟪feature i,E ((m:ℝ)+n) (feature j)⟫_ℂ = _
  rw [← Nat.cast_add, E_nat, ← U_inner, U_feature, U_iterate, U_feature,
    (effect_hermitian i).eq]

theorem integer_consumer (i j : Index) (m n : ℕ) :
    integerWeight i j (m+n) = (temporalKernel (m,feature i) (n,feature j)).re := by
  rw [integer_temporal_trace, integerWeight_trace, map_smul, Matrix.mul_smul,
    Matrix.trace_smul]
  congr 1
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem integer_zero (i j : Index) : integerWeight i j 0 = commonCut.probability i j := by
  have h := integer_consumer i j 0 0
  rw [integer_temporal_trace] at h
  simpa only [Nat.zero_add, iterate, LinearMap.id_apply, ← commonCut_probability,
    Complex.ofReal_re] using h

def orthonormalBasis : OrthonormalBasis Index ℂ FeatureSpace := .ofRepr J.symm

def matrixOperator : Matrix Index Index ℂ ≃ₐ[ℂ] (FeatureSpace →L[ℂ] FeatureSpace) :=
  Matrix.toEuclideanCLM.toAlgEquiv |>.trans
    (Module.End.toContinuousLinearMap Coordinates).symm |>.trans
    (J.toLinearEquiv.conjAlgEquiv ℂ) |>.trans
    (Module.End.toContinuousLinearMap FeatureSpace)

theorem matrixOperator_apply (A : Matrix Index Index ℂ) (q : FeatureSpace) :
    matrixOperator A q = J (WithLp.toLp 2 (A *ᵥ (J.symm q))) := rfl

theorem matrixOperator_diagonal (a : Index → ℂ) :
    matrixOperator (Matrix.diagonal a) = LinearMap.toContinuousLinearMap (spectral a) := by
  ext q
  rw [matrixOperator_apply]
  change J (WithLp.toLp 2 ((Matrix.diagonal a) *ᵥ (J.symm q))) =
    J (multiplier a (J.symm q))
  congr 1
  ext i
  simp [multiplier, Matrix.mulVec_diagonal]

def HC : FeatureSpace →L[ℂ] FeatureSpace := LinearMap.toContinuousLinearMap H
def EC (t : ℝ) : FeatureSpace →L[ℂ] FeatureSpace := LinearMap.toContinuousLinearMap (E t)

/-- Equality with the operator exponential on the actual quotient endomorphisms. -/
theorem E_operator_exp (t : ℝ) : EC t = NormedSpace.exp ((-t) • HC) := by
  letI : NormedAlgebra ℚ (Matrix Index Index ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  letI : NormedAlgebra ℚ (FeatureSpace →L[ℂ] FeatureSpace) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let A : Matrix Index Index ℂ := Matrix.diagonal (fun i => (energy i : ℂ))
  have hm : matrixOperator A = HC := matrixOperator_diagonal _
  have hcont : Continuous matrixOperator := matrixOperator.toLinearMap.continuous_of_finiteDimensional
  have he := NormedSpace.map_exp matrixOperator hcont ((-t) • A)
  have hsm := (matrixOperator.toLinearMap.restrictScalars ℝ).map_smul (-t) A
  change matrixOperator ((-t) • A) = (-t) • matrixOperator A at hsm
  rw [hsm, hm] at he
  have hd : NormedSpace.exp ((-t) • A) =
      Matrix.diagonal (fun i => (Real.exp (t * Real.log (eigenvalue i)) : ℂ)) := by
    rw [show A = Matrix.diagonal (fun i => (energy i : ℂ)) from rfl,
      ← Matrix.diagonal_smul, Matrix.exp_diagonal]
    congr 1
    ext i
    simp [← Complex.exp_eq_exp_ℂ, Complex.real_smul, energy,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  rw [hd, matrixOperator_diagonal] at he
  exact he

theorem E_hasDerivAt (t : ℝ) :
    HasDerivAt EC (EC t * (-HC)) t := by
  have h := hasDerivAt_exp_smul_const (-HC) t
  have he (u : ℝ) : NormedSpace.exp (u • -HC) = EC u := by
    rw [smul_neg, ← neg_smul, ← E_operator_exp]
  simpa only [he] using h

theorem E_continuous : Continuous EC :=
  continuous_iff_continuousAt.mpr (fun t => (E_hasDerivAt t).continuousAt)

theorem E_differentiable : Differentiable ℝ EC := fun t => (E_hasDerivAt t).differentiableAt

def temporalCoordinates {A : Type*} (v : A → ℝ × FeatureSpace) : Matrix Index A ℂ :=
  fun k i => J.symm (E (v i).1 (v i).2) k

theorem temporal_gram {A : Type*} [Fintype A] (v : A → ℝ × FeatureSpace) :
    (fun i j => temporalKernel (v i) (v j) : Matrix A A ℂ) =
      (temporalCoordinates v)ᴴ * temporalCoordinates v := by
  ext i j
  rw [temporal_factorization, ← J.symm.inner_map_map, PiLp.inner_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, temporalCoordinates,
    RCLike.inner_apply, Complex.star_def]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem temporal_rank_le_six {A : Type*} [Fintype A] (v : A → ℝ × FeatureSpace) :
    Matrix.rank (fun i j => temporalKernel (v i) (v j) : Matrix A A ℂ) ≤ 6 := by
  rw [temporal_gram]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

theorem temporal_rank_attained :
    Matrix.rank (fun i j => temporalKernel (0,feature i) (0,feature j) : Matrix Index Index ℂ) = 6 := by
  have he : (fun i j => temporalKernel (0,feature i) (0,feature j) : Matrix Index Index ℂ) =
      kernel := by
    ext i j
    rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num, integer_temporal_trace]
    simpa only [Nat.zero_add, iterate, LinearMap.id_apply, kernel, Matrix.map_apply]
      using (commonCut_probability i j).symm
  rw [he]
  exact commonCut_rank_complex

theorem coordinates_spectral (a : Index → ℂ) (q : FeatureSpace) (i : Index) :
    J.symm (spectral a q) i = a i * J.symm q i := by
  rw [spectral_apply, J.symm_apply_apply]
  rfl

theorem norm_sq_coordinates (q : FeatureSpace) :
    ‖q‖^2 = ∑ i, ‖J.symm q i‖^2 := by
  rw [← J.symm.norm_map q, EuclideanSpace.norm_sq_eq]

theorem spectral_norm_sq (a : Index → ℂ) (q : FeatureSpace) :
    ‖spectral a q‖^2 = ∑ i, ‖a i‖^2 * ‖J.symm q i‖^2 := by
  rw [norm_sq_coordinates]
  simp_rw [coordinates_spectral, norm_mul, mul_pow]

def P : FeatureSpace →ₗ[ℂ] FeatureSpace := spectral (Pi.single 0 1)

theorem U_P (q : FeatureSpace) : (U (P q) : Mat) = stationary (U q) := by
  rw [P, U_spectral]
  have he : eigenvector 0 = (1 : Mat) := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [eigenvector, eigenCoordinates,
      symmetricMatrix, Matrix.one_apply, Fin.ext_iff, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]
  simp [synthesis, Pi.single_apply, ite_mul, scalar_coefficient, he, stationary]

theorem P_actual (q : FeatureSpace) : P q = quotientStationary q := by
  apply U.injective
  exact Subtype.ext ((U_P q).trans (U_stationary q).symm)

theorem P_trace (q : FeatureSpace) :
    FiniteQutritInvariantReconstruction.trace (P q) =
      FiniteQutritInvariantReconstruction.trace q := by
  change (U (P q) : Mat).trace = _
  rw [U_P, stationary_trace]
  rfl

theorem P_coordinates (q : FeatureSpace) (i : Index) :
    J.symm (P q) i = if i=0 then J.symm q 0 else 0 := by
  rw [P, coordinates_spectral]
  by_cases hi : i=0
  · subst i; simp
  · simp [hi]

theorem P_idempotent (q : FeatureSpace) : P (P q) = P q := by
  apply J.symm.injective
  ext i
  simp only [P_coordinates]
  split_ifs <;> rfl

theorem E_P (t : ℝ) (q : FeatureSpace) : E t (P q) = P q := by
  apply J.symm.injective
  ext i
  rw [E, coordinates_spectral, P_coordinates]
  split_ifs with hi
  · subst i; simp [eigenvalue]
  · simp

theorem E_trace (t : ℝ) (q : FeatureSpace) :
    FiniteQutritInvariantReconstruction.trace (E t q) =
      FiniteQutritInvariantReconstruction.trace q := by
  have hc := congrArg (fun X : Mat => coefficients X 0) (U_spectral
    (fun i => (Real.exp (t * Real.log (eigenvalue i)) : ℂ)) q)
  rw [coefficients_synthesis] at hc
  simp only [eigenvalue, Matrix.cons_val_zero, Real.log_one, mul_zero,
    Real.exp_zero, Complex.ofReal_one, one_mul] at hc
  rw [scalar_coefficient, scalar_coefficient] at hc
  change (U (E t q) : Mat).trace = _
  change (U (E t q) : Mat).trace / 3 = (U q : Mat).trace / 3 at hc
  exact (div_left_inj' (by norm_num : (3 : ℂ) ≠ 0)).mp hc

theorem P_initial : P initial = initial := by
  apply U.injective
  apply Subtype.ext
  rw [U_P, U_initial]
  simp [stationary, rho_density.2]
  ext a b
  simp [rho, Matrix.smul_apply]

theorem E_initial (t : ℝ) : E t initial = initial := by
  rw [← P_initial, E_P, P_initial]

theorem multiplier_contraction (a : Index → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ i : Index, i ≠ 0 → ‖a i‖ ≤ c) (q : FeatureSpace)
    (hq : J.symm q 0 = 0) : ‖spectral a q‖ ≤ c * ‖q‖ := by
  have h : ‖spectral a q‖^2 ≤ (c * ‖q‖)^2 := by
    rw [spectral_norm_sq, mul_pow, norm_sq_coordinates, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i=0
    · subst i; simp [hq]
    · have hb := ha i hi
      exact mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg (a i)]) (sq_nonneg _)
  nlinarith [norm_nonneg (spectral a q), mul_nonneg hc (norm_nonneg q)]

theorem E_relative_contraction (t : ℝ) (ht : 0 ≤ t) (q : FeatureSpace) :
    ‖E t q-P q‖ ≤ (9/10 : ℝ)^t * ‖q-P q‖ := by
  have h := multiplier_contraction
    (fun i => (Real.exp (t * Real.log (eigenvalue i)) : ℂ)) ((9/10 : ℝ)^t)
    (Real.rpow_nonneg (by norm_num) _) ?_ (q-P q) ?_
  · change ‖E t (q-P q)‖ ≤ _ at h
    simpa only [map_sub, E_P] using h
  · intro i hi
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [show t * Real.log (eigenvalue i) = Real.log (eigenvalue i) * t by ring,
      ← Real.rpow_def_of_pos (eigenvalue_pos i)]
    exact Real.rpow_le_rpow (eigenvalue_pos i).le (tracezero_eigenvalue_bound i hi) ht
  · simp [map_sub, P_coordinates]

theorem E_fixed_positive_time (t : ℝ) (ht : 0 < t) (q : FeatureSpace) :
    E t q = q ↔ q = P q := by
  constructor
  · intro hf
    have hc := E_relative_contraction t ht.le q
    rw [hf] at hc
    have hr : (9/10 : ℝ)^t < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ht
    have hz : ‖q-P q‖ = 0 := by nlinarith [norm_nonneg (q-P q)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro hf
    conv_lhs => rw [hf]
    rw [E_P, ← hf]

theorem E_strict_hilbert_positive (t : ℝ) {q : FeatureSpace} (hq : q ≠ 0) :
    0 < (⟪q,E t q⟫_ℂ).re := by
  have he : E (t/2) (E (t/2) q) = E t q := by
    rw [← LinearMap.comp_apply, ← E_add, show t/2+t/2=t by ring]
  have hn : E (t/2) q ≠ 0 := by
    intro hz
    have h := congrArg (fun v => E (-t/2) v) hz
    rw [← LinearMap.comp_apply, ← E_add, show -t/2+t/2=0 by ring,
      E_zero, LinearMap.id_apply, map_zero] at h
    exact hq h
  rw [← he, ← (E_selfadjoint (t/2)) q (E (t/2) q),
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_pos_of_pos (norm_pos_iff.mpr hn)

def rawEigenvector (i : Index) : FeatureSpace := U.symm ⟨eigenvector i,eigenvector_mem i⟩

theorem U_rawEigenvector (i : Index) : (U (rawEigenvector i) : Mat) = eigenvector i := by
  change (U (U.symm _) : Mat) = _
  rw [U.apply_symm_apply]

theorem eigenvector_coefficients (i : Index) : coefficients (eigenvector i) = Pi.single i 1 := by
  have hs : synthesis (Pi.single i 1) = eigenvector i := by simp [synthesis]
  rw [← hs, coefficients_synthesis]

theorem spectral_rawEigenvector (a : Index → ℂ) (i : Index) :
    spectral a (rawEigenvector i) = a i • rawEigenvector i := by
  apply U.injective
  apply Subtype.ext
  rw [U_spectral, U_rawEigenvector, eigenvector_coefficients, map_smul]
  simp [synthesis, U_rawEigenvector, Pi.single_apply, mul_ite]

theorem rawEigenvector_nonzero (i : Index) : rawEigenvector i ≠ 0 := by
  intro hz
  have h := congrArg (fun q => (U q : Mat)) hz
  rw [U_rawEigenvector, map_zero] at h
  exact eigenvector_nonzero i h

theorem E_sharp (t : ℝ) :
    ‖E t (rawEigenvector 1)‖ = (9/10 : ℝ)^t * ‖rawEigenvector 1‖ := by
  rw [E, spectral_rawEigenvector, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  congr 1
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 9/10)]
  congr 1
  norm_num [eigenvalue]
  ring

def gamma : ℝ := Real.log (10/9)
theorem gamma_pos : 0 < gamma := Real.log_pos (by norm_num)

theorem energy_one : energy 1 = gamma := by
  unfold energy gamma
  rw [← Real.log_inv]
  congr 1
  norm_num [eigenvalue]

theorem energy_gap (i : Index) (hi : i ≠ 0) : gamma ≤ energy i := by
  rw [← energy_one]
  unfold energy
  apply neg_le_neg
  apply Real.log_le_log (eigenvalue_pos i)
  simpa [eigenvalue] using tracezero_eigenvalue_bound i hi

theorem spectral_real_energy (a : Index → ℝ) (q : FeatureSpace) :
    (⟪q,spectral (fun i => (a i : ℂ)) q⟫_ℂ).re =
      ∑ i, a i * ‖J.symm q i‖^2 := by
  rw [spectral_inner, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm]
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.normSq_apply]
  ring

theorem tracezero_coordinate {q : FeatureSpace}
    (hq : FiniteQutritInvariantReconstruction.trace q = 0) : J.symm q 0 = 0 := by
  rw [J_inverse_coordinates, scalar_coefficient]
  change (U q : Mat).trace = 0 at hq
  simp [hq]

theorem generator_gap (q : FeatureSpace)
    (hq : FiniteQutritInvariantReconstruction.trace q = 0) :
    gamma * ‖q‖^2 ≤ (⟪q,H q⟫_ℂ).re := by
  rw [H, spectral_real_energy, norm_sq_coordinates, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i=0
  · subst i; simp [tracezero_coordinate hq]
  · exact mul_le_mul_of_nonneg_right (energy_gap i hi) (sq_nonneg _)

theorem H_sharp : H (rawEigenvector 1) = (gamma : ℂ) • rawEigenvector 1 := by
  rw [H, spectral_rawEigenvector, energy_one]

theorem H_kernel (q : FeatureSpace) : H q = 0 ↔ q = P q := by
  constructor
  · intro hz
    apply J.symm.injective
    ext i
    rw [P_coordinates]
    by_cases hi : i=0
    · subst i; simp
    · rw [if_neg hi]
      have h := congrArg (fun v => J.symm v i) hz
      rw [H, coordinates_spectral, map_zero] at h
      have he : energy i ≠ 0 := ne_of_gt (lt_of_lt_of_le gamma_pos (energy_gap i hi))
      have hec : (energy i : ℂ) ≠ 0 := by exact_mod_cast he
      exact (mul_eq_zero.mp h).resolve_left hec
  · intro hf
    apply J.symm.injective
    ext i
    rw [H, coordinates_spectral, hf, P_coordinates]
    split_ifs with hi
    · subst i; simp [energy, eigenvalue]
    · simp

theorem scalar_line (q : FeatureSpace) :
    q = P q ↔ ∃ c : ℂ, (U q : Mat) = c • (1 : Mat) := by
  constructor
  · intro h
    refine ⟨(U q : Mat).trace/3, ?_⟩
    calc
      (U q : Mat) = (U (P q) : Mat) := congrArg (fun v => (U v : Mat)) h
      _ = stationary (U q) := U_P q
  · rintro ⟨c,hc⟩
    apply U.injective
    apply Subtype.ext
    rw [U_P, hc]
    simp [stationary, Matrix.trace_smul, Matrix.trace_one]

theorem kernel_scalar_line (q : FeatureSpace) :
    H q = 0 ↔ ∃ c : ℂ, (U q : Mat) = c • (1 : Mat) := (H_kernel q).trans (scalar_line q)

theorem scalar_is_three_initial : rawEigenvector 0 = (3 : ℂ) • initial := by
  apply U.injective
  apply Subtype.ext
  rw [U_rawEigenvector, map_smul, Submodule.coe_smul, U_initial]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [eigenvector, eigenCoordinates, symmetricMatrix, rho, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, vec6_last, Fin.ext_iff]

theorem scalar_norm_one : ‖rawEigenvector 0‖ = 1 := by
  have h := eigenvector_norm_sq 0
  rw [← U_rawEigenvector, hsNorm_U] at h
  change ‖rawEigenvector 0‖^2 = 1 at h
  nlinarith [norm_nonneg (rawEigenvector 0)]

theorem initial_norm : ‖initial‖ = (1/3 : ℝ) := by
  have h := scalar_norm_one
  rw [scalar_is_three_initial, norm_smul] at h
  norm_num at h
  linarith

/-- Spectral formula on matrix entries. Agreement with feature evolution below
is asserted only on the actual symmetric carrier. -/
def matrixSpectral (a : Index → ℂ) (X : Mat) : Mat :=
  synthesis (fun i => a i * coefficients X i)

theorem matrixSpectral_actual (a : Index → ℂ) (X : symmetricCarrier) :
    matrixSpectral a X = (U (spectral a (U.symm X)) : Mat) := by
  rw [U_spectral, U.apply_symm_apply]
  rfl

theorem matrixSpectral_mem (a : Index → ℂ) (X : Mat) :
    matrixSpectral a X ∈ symmetricCarrier := synthesis_mem _

theorem matrixSpectral_add (a : Index → ℂ) (X Y : Mat) :
    matrixSpectral a (X+Y) = matrixSpectral a X + matrixSpectral a Y := by
  have hc : coefficients (X+Y) = coefficients X+coefficients Y := by
    ext i
    fin_cases i <;> simp [coefficients, Matrix.add_apply, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, vec6_last] <;> ring
  simp only [matrixSpectral, hc, Pi.add_apply, mul_add]
  exact synthesis.map_add _ _

theorem matrixSpectral_smul (a : Index → ℂ) (c : ℂ) (X : Mat) :
    matrixSpectral a (c • X) = c • matrixSpectral a X := by
  have hc : coefficients (c • X) = c • coefficients X := by
    ext i
    fin_cases i <;> simp [coefficients, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last] <;> ring
  unfold matrixSpectral
  rw [hc]
  have he : (fun i => a i * (c • coefficients X) i) = c • (fun i => a i * coefficients X i) := by
    ext i; simp [smul_eq_mul, mul_left_comm]
  rw [he, map_smul]

def matrixSpectralLinear (a : Index → ℂ) : Mat →ₗ[ℂ] Mat where
  toFun := matrixSpectral a
  map_add' := matrixSpectral_add a
  map_smul' := matrixSpectral_smul a

variable (A : Type*) [Fintype A] [DecidableEq A]

def spectatorSpectral (a : Index → ℂ) :
    Matrix (Q × A) (Q × A) ℂ →ₗ[ℂ] Matrix (Q × A) (Q × A) ℂ where
  toFun X u v := matrixSpectral a (FiniteQutritInvariantExamples.block A u.2 v.2 X) u.1 v.1
  map_add' X Y := by
    ext ⟨b,e⟩ ⟨c,f⟩
    change matrixSpectral a (FiniteQutritInvariantExamples.block A e f (X+Y)) b c = _
    rw [map_add, matrixSpectral_add]
    rfl
  map_smul' z X := by
    ext ⟨b,e⟩ ⟨c,f⟩
    change matrixSpectral a (FiniteQutritInvariantExamples.block A e f (z • X)) b c = _
    rw [map_smul, matrixSpectral_smul]
    rfl

omit [Fintype A] [DecidableEq A] in
theorem spectator_block (a : Index → ℂ) (X : Matrix (Q × A) (Q × A) ℂ) (e f : A) :
    FiniteQutritInvariantExamples.block A e f (spectatorSpectral A a X) =
      matrixSpectral a (FiniteQutritInvariantExamples.block A e f X) := rfl

def spectatorE (t : ℝ) := spectatorSpectral A
  (fun i => (Real.exp (t * Real.log (eigenvalue i)) : ℂ))
def spectatorH := spectatorSpectral A (fun i => (energy i : ℂ))

theorem spectator_integer (n : ℕ) (X : Matrix (Q × A) (Q × A) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier A) :
    spectatorE A n X = amplifiedIterate A n X := by
  ext ⟨b,e⟩ ⟨c,f⟩
  have hb : FiniteQutritInvariantExamples.block A e f (spectatorE A n X) =
      FiniteQutritInvariantExamples.block A e f (amplifiedIterate A n X) := by
    rw [spectatorE, spectator_block, amplified_iterate_block]
    rw [matrixSpectral_actual _ ⟨_,hX e f⟩]
    change (U (E n (U.symm ⟨_,hX e f⟩)) : Mat) = _
    rw [E_nat, U_iterate, U.apply_symm_apply]
  exact congrArg (fun Z : Mat => Z b c) hb

theorem matrix_relative_contraction (t : ℝ) (ht : 0 ≤ t) (X : symmetricCarrier) :
    hsNorm (matrixSpectral (fun i => (Real.exp (t*Real.log (eigenvalue i)) : ℂ)) X - stationary X) ≤
      (9/10 : ℝ)^t * hsNorm ((X : Mat)-stationary X) := by
  have h := E_relative_contraction t ht (U.symm X)
  have he (q : FeatureSpace) :
      hsNorm ((U q : Mat)-stationary X) = ‖q-P (U.symm X)‖ := by
    have hp : stationary X = (U (P (U.symm X)) : Mat) := by
      rw [U_P, U.apply_symm_apply]
    rw [hp]
    rw [← Submodule.coe_sub, ← map_sub, hsNorm_U]
  have hx : hsNorm ((X : Mat)-stationary X) = ‖U.symm X-P (U.symm X)‖ := by
    simpa only [U.apply_symm_apply] using he (U.symm X)
  rw [matrixSpectral_actual, he, hx]
  exact h

theorem spectator_relative_contraction (t : ℝ) (ht : 0 ≤ t)
    (X : Matrix (Q × A) (Q × A) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier A) :
    jointNorm A (spectatorE A t X-relativeProjection A X) ≤
      (9/10 : ℝ)^t * jointNorm A (X-relativeProjection A X) := by
  have hh : jointNorm A (spectatorE A t X-relativeProjection A X)^2 ≤
      ((9/10 : ℝ)^t * jointNorm A (X-relativeProjection A X))^2 := by
    rw [mul_pow, jointNorm_sq, jointNorm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro f _
    have hm := matrix_relative_contraction t ht
      ⟨FiniteQutritInvariantExamples.block A e f X,hX e f⟩
    simp only [map_sub, spectatorE, spectator_block, relative_block]
    have h0 := hsNorm_nonneg (matrixSpectral
      (fun i => (Real.exp (t*Real.log (eigenvalue i)) : ℂ))
      (FiniteQutritInvariantExamples.block A e f X)-
        stationary (FiniteQutritInvariantExamples.block A e f X))
    have h1 := hsNorm_nonneg (FiniteQutritInvariantExamples.block A e f X-
      stationary (FiniteQutritInvariantExamples.block A e f X))
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 9/10) t]
  nlinarith [jointNorm_nonneg A (spectatorE A t X-relativeProjection A X),
    mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 9/10) t)
      (jointNorm_nonneg A (X-relativeProjection A X))]

theorem spectator_zero (X : Matrix (Q × A) (Q × A) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier A) : spectatorE A 0 X = X := by
  simpa only [Nat.cast_zero, amplifiedIterate, LinearMap.id_apply] using spectator_integer A 0 X hX

theorem spectator_partialTrace (t : ℝ) (X : Matrix (Q × A) (Q × A) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier A) :
    FiniteQutritAveragedMixing.partialTrace A (spectatorE A t X) =
      FiniteQutritAveragedMixing.partialTrace A X := by
  ext e f
  rw [partialTrace_block, spectatorE, spectator_block,
    matrixSpectral_actual _ ⟨_,hX e f⟩]
  have h := E_trace t (U.symm ⟨_,hX e f⟩)
  change (U (E t (U.symm ⟨_,hX e f⟩)) : Mat).trace =
    (U (U.symm ⟨_,hX e f⟩) : Mat).trace at h
  rw [U.apply_symm_apply] at h
  exact h

omit [Fintype A] [DecidableEq A] in
theorem empty_spectator_evolution [IsEmpty A] (t : ℝ)
    (X : Matrix (Q × A) (Q × A) ℂ) : spectatorE A t X = X := by
  ext ⟨b,e⟩
  exact isEmptyElim e

omit [DecidableEq A] in
theorem empty_no_density [IsEmpty A] (X : Matrix (Q × A) (Q × A) ℂ) :
    ¬ IsDensityOperator X := by
  intro h
  have ht := h.2
  simp [Matrix.trace] at ht

theorem J_basis_normalized (i : Index) :
    J (WithLp.toLp 2 (Pi.single i 1)) = normalizedEigenvector i := by
  apply U.injective
  apply Subtype.ext
  change (U (JLinear _) : Mat) = (U (U.symm _) : Mat)
  rw [U_JLinear, U.apply_symm_apply]
  simp [synthesis, Pi.single_apply, ite_div, ite_smul]

theorem H_E_commute (t : ℝ) (q : FeatureSpace) : H (E t q) = E t (H q) := by
  unfold H E
  rw [← LinearMap.comp_apply, ← spectral_mul, ← LinearMap.comp_apply, ← spectral_mul]
  have he : (fun i => (energy i : ℂ) * (Real.exp (t*Real.log (eigenvalue i)) : ℂ)) =
      (fun i => (Real.exp (t*Real.log (eigenvalue i)) : ℂ) * (energy i : ℂ)) := by
    ext i; ring
  rw [he]

theorem E_generator_derivative (t : ℝ) : HasDerivAt EC ((-HC) * EC t) t := by
  have h := E_hasDerivAt t
  have he : EC t * (-HC) = (-HC) * EC t := by
    ext q
    change E t (-H q) = -H (E t q)
    rw [map_neg, H_E_commute]
  rw [he] at h
  exact h

theorem gap_attained :
    FiniteQutritInvariantReconstruction.trace (rawEigenvector 1) = 0 ∧
    rawEigenvector 1 ≠ 0 ∧
    (⟪rawEigenvector 1,H (rawEigenvector 1)⟫_ℂ).re = gamma * ‖rawEigenvector 1‖^2 := by
  refine ⟨?_,rawEigenvector_nonzero 1,?_⟩
  · change (U (rawEigenvector 1) : Mat).trace = 0
    rw [U_rawEigenvector]
    norm_num [eigenvector, eigenCoordinates, symmetricMatrix, Matrix.trace,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three]
  · rw [H_sharp, inner_smul_right, inner_self_eq_norm_sq_to_K,
      RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]

omit [Fintype A] [DecidableEq A] in
theorem block_tensor (X : Mat) (sigma : Matrix A A ℂ) (e f : A) :
    FiniteQutritInvariantExamples.block A e f (X ⊗ₖ sigma) = sigma e f • X := by
  ext a b
  simp [FiniteQutritInvariantExamples.block,
    Matrix.smul_apply, smul_eq_mul, mul_comm]

omit [Fintype A] [DecidableEq A] in
theorem tensor_mem (X : symmetricCarrier) (sigma : Matrix A A ℂ) :
    (X : Mat) ⊗ₖ sigma ∈ FiniteQutritInvariantExamples.matrixCarrier A := by
  intro e f
  rw [block_tensor]
  exact X.property.smul _

omit [Fintype A] [DecidableEq A] in
theorem spectator_product (a : Index → ℂ) (X : Mat) (sigma : Matrix A A ℂ) :
    spectatorSpectral A a (X ⊗ₖ sigma) = matrixSpectral a X ⊗ₖ sigma := by
  ext ⟨b,e⟩ ⟨c,f⟩
  change matrixSpectral a (FiniteQutritInvariantExamples.block A e f (X ⊗ₖ sigma)) b c = _
  rw [block_tensor, matrixSpectral_smul]
  simp [Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem partialTrace_tensor (X : Mat) (sigma : Matrix A A ℂ) :
    FiniteQutritAveragedMixing.partialTrace A (X ⊗ₖ sigma) = X.trace • sigma := by
  ext e f
  rw [partialTrace_block, block_tensor, Matrix.trace_smul]
  simp [Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem matrix_stationary_fixed (t : ℝ) (X : Mat) :
    matrixSpectral (fun i => (Real.exp (t*Real.log (eigenvalue i)) : ℂ)) (stationary X) = stationary X := by
  let q : FeatureSpace := U.symm ⟨stationary X,stationary_mem X⟩
  have hq : q = P q := (scalar_line q).mpr ⟨X.trace/3, by rw [show (U q : Mat) = stationary X by
    change (U (U.symm _) : Mat) = _; rw [U.apply_symm_apply]]; rfl⟩
  have hf : E t q = q := by rw [hq, E_P, ← hq]
  rw [matrixSpectral_actual _ ⟨_,stationary_mem X⟩]
  change (U (E t q) : Mat) = _
  rw [hf]
  change (U (U.symm _) : Mat) = _
  rw [U.apply_symm_apply]

theorem matrix_stationary_kernel (X : Mat) :
    matrixSpectral (fun i => (energy i : ℂ)) (stationary X) = 0 := by
  rw [matrixSpectral_actual _ ⟨_,stationary_mem X⟩]
  have h := (kernel_scalar_line (U.symm ⟨stationary X,stationary_mem X⟩)).mpr
    ⟨X.trace/3, by rw [U.apply_symm_apply]; rfl⟩
  change H _ = 0 at h
  change (U (H _) : Mat) = 0
  rw [h, map_zero]
  rfl

theorem spectator_relative_fixed (t : ℝ) (X : Matrix (Q × A) (Q × A) ℂ) :
    spectatorE A t (relativeProjection A X) = relativeProjection A X := by
  ext ⟨b,e⟩ ⟨c,f⟩
  have h : FiniteQutritInvariantExamples.block A e f
      (spectatorE A t (relativeProjection A X)) =
      FiniteQutritInvariantExamples.block A e f (relativeProjection A X) := by
    rw [spectatorE, spectator_block, relative_block, matrix_stationary_fixed]
  exact congrArg (fun Z : Mat => Z b c) h

theorem matrix_fixed (t : ℝ) (ht : 0 < t) (X : symmetricCarrier) :
    matrixSpectral (fun i => (Real.exp (t*Real.log (eigenvalue i)) : ℂ)) X = X ↔
      (X : Mat) = stationary X := by
  constructor
  · intro hf
    have hq : E t (U.symm X) = U.symm X := by
      apply U.injective
      apply Subtype.ext
      unfold E
      rw [← matrixSpectral_actual, U.apply_symm_apply]
      exact hf
    have h := congrArg (fun q => (U q : Mat)) ((E_fixed_positive_time t ht _).mp hq)
    rw [U.apply_symm_apply, U_P, U.apply_symm_apply] at h
    exact h
  · intro hf
    rw [hf]
    exact matrix_stationary_fixed t X

theorem spectator_fixed (t : ℝ) (ht : 0 < t)
    (X : Matrix (Q × A) (Q × A) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier A) :
    spectatorE A t X = X ↔ X = relativeProjection A X := by
  constructor
  · intro hf
    ext ⟨b,e⟩ ⟨c,f⟩
    have hb := congrArg (FiniteQutritInvariantExamples.block A e f) hf
    rw [spectatorE, spectator_block] at hb
    have hm := (matrix_fixed t ht ⟨_,hX e f⟩).mp hb
    rw [← relative_block] at hm
    exact congrArg (fun Z : Mat => Z b c) hm
  · intro hf
    conv_lhs => rw [hf]
    rw [spectator_relative_fixed, ← hf]

theorem spectator_fixed_tensors (t : ℝ) (ht : 0 < t)
    (X : Matrix (Q × A) (Q × A) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier A) :
    spectatorE A t X = X ↔ ∃ sigma : Matrix A A ℂ, X = (1 : Mat) ⊗ₖ sigma := by
  rw [spectator_fixed A t ht X hX]
  constructor
  · intro hf
    refine ⟨(1/3 : ℂ) • FiniteQutritAveragedMixing.partialTrace A X, ?_⟩
    calc
      X = relativeProjection A X := hf
      _ = _ := by
        ext ⟨b,e⟩ ⟨c,f⟩
        simp [relativeProjection, Matrix.smul_apply, smul_eq_mul]
        ring
  · rintro ⟨sigma,rfl⟩
    rw [relativeProjection, partialTrace_tensor, Matrix.trace_one]
    ext ⟨b,e⟩ ⟨c,f⟩
    simp [Matrix.smul_apply, smul_eq_mul]
    ring

theorem spectator_generator_kernel (X : Matrix (Q × A) (Q × A) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier A) :
    spectatorH A X = 0 ↔ X = relativeProjection A X := by
  constructor
  · intro hz
    ext ⟨b,e⟩ ⟨c,f⟩
    have hb := congrArg (FiniteQutritInvariantExamples.block A e f) hz
    rw [spectatorH, spectator_block, map_zero] at hb
    have hq : H (U.symm ⟨_,hX e f⟩) = 0 := by
      apply U.injective
      apply Subtype.ext
      unfold H
      rw [← matrixSpectral_actual]
      simpa only [map_zero, Submodule.coe_zero] using hb
    have hm := congrArg (fun q => (U q : Mat)) ((H_kernel _).mp hq)
    rw [U.apply_symm_apply, U_P, U.apply_symm_apply, ← relative_block] at hm
    exact congrArg (fun Z : Mat => Z b c) hm
  · intro hf
    rw [hf]
    ext ⟨b,e⟩ ⟨c,f⟩
    change matrixSpectral (fun i => (energy i : ℂ))
      (FiniteQutritInvariantExamples.block A e f (relativeProjection A X)) b c = 0
    rw [relative_block, matrix_stationary_kernel]
    rfl

theorem jointNorm_smul (z : ℂ) (X : Matrix (Q × A) (Q × A) ℂ) :
    jointNorm A (z • X) = ‖z‖ * jointNorm A X := by
  rw [← jointEmbedding_norm, map_smul, norm_smul, jointEmbedding_norm]

theorem jointNorm_single_tensor (X : Mat) (e : A) :
    jointNorm A (X ⊗ₖ Matrix.single e e 1) = hsNorm X := by
  unfold jointNorm
  simp [block_tensor, Matrix.single, ite_and, apply_ite, hsNorm]

def spectatorSharp (e : A) : Matrix (Q × A) (Q × A) ℂ := eigenvector 1 ⊗ₖ Matrix.single e e 1

omit [Fintype A] in
theorem spectator_sharp_nonzero (e : A) : spectatorSharp A e ≠ 0 := by
  intro h
  have he := congrArg (fun X : Matrix (Q × A) (Q × A) ℂ => X (1,e) (1,e)) h
  norm_num [spectatorSharp, eigenvector, eigenCoordinates, symmetricMatrix, Matrix.single,
    Matrix.kronecker_apply] at he

theorem spectator_sharp_partialTrace (e : A) :
    FiniteQutritAveragedMixing.partialTrace A (spectatorSharp A e) = 0 := by
  rw [spectatorSharp, partialTrace_tensor]
  have h : (eigenvector 1).trace = 0 := by
    norm_num [eigenvector, eigenCoordinates, symmetricMatrix, Matrix.trace,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three]
  rw [h, zero_smul]

theorem spectator_sharp (t : ℝ) (e : A) :
    jointNorm A (spectatorE A t (spectatorSharp A e)) =
      (9/10 : ℝ)^t * jointNorm A (spectatorSharp A e) := by
  have he : matrixSpectral (fun i => (Real.exp (t*Real.log (eigenvalue i)) : ℂ)) (eigenvector 1) =
      (Real.exp (t*Real.log (eigenvalue 1)) : ℂ) • eigenvector 1 := by
    simp [matrixSpectral, eigenvector_coefficients, synthesis, Pi.single_apply, mul_ite]
  rw [spectatorSharp, spectatorE, spectator_product, he, Matrix.smul_kronecker,
    jointNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  congr 1
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 9/10)]
  congr 1
  norm_num [eigenvalue]
  ring

omit [Fintype A] [DecidableEq A] in
theorem empty_no_nonzero_matrix [IsEmpty A] (X : Matrix (Q × A) (Q × A) ℂ) : X = 0 := by
  ext ⟨b,e⟩
  exact isEmptyElim e

omit [Fintype A] in
theorem spectator_sharp_mem (e : A) :
    spectatorSharp A e ∈ FiniteQutritInvariantExamples.matrixCarrier A :=
  tensor_mem A ⟨eigenvector 1,eigenvector_mem 1⟩ _

theorem spectator_relative_sharp (t : ℝ) (e : A) :
    jointNorm A (spectatorE A t (spectatorSharp A e)-relativeProjection A (spectatorSharp A e)) =
      (9/10 : ℝ)^t * jointNorm A (spectatorSharp A e-relativeProjection A (spectatorSharp A e)) := by
  rw [relative_zero_of_partialTrace_zero A _ (spectator_sharp_partialTrace A e)]
  simpa only [sub_zero] using spectator_sharp A t e

theorem nonempty_relative_attainer [Nonempty A] (t : ℝ) :
    ∃ X : Matrix (Q × A) (Q × A) ℂ,
      X ∈ FiniteQutritInvariantExamples.matrixCarrier A ∧ X ≠ 0 ∧
      FiniteQutritAveragedMixing.partialTrace A X = 0 ∧
      jointNorm A (spectatorE A t X-relativeProjection A X) =
        (9/10 : ℝ)^t * jointNorm A (X-relativeProjection A X) := by
  let e : A := Classical.choice (inferInstance : Nonempty A)
  exact ⟨spectatorSharp A e,spectator_sharp_mem A e,spectator_sharp_nonzero A e,
    spectator_sharp_partialTrace A e,spectator_relative_sharp A t e⟩

def tracezeroFixedWitness : Matrix (Q × Fin 2) (Q × Fin 2) ℂ :=
  (1 : Mat) ⊗ₖ Matrix.diagonal ![(1 : ℂ),-1]

theorem tracezero_fixed_witness :
    tracezeroFixedWitness ≠ 0 ∧ tracezeroFixedWitness.trace = 0 ∧
    (∀ t : ℝ, spectatorE (Fin 2) t tracezeroFixedWitness = tracezeroFixedWitness) ∧
    spectatorH (Fin 2) tracezeroFixedWitness = 0 := by
  have hs : stationary (1 : Mat) = 1 := by simp [stationary, Matrix.trace_one]
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    have he := congrArg (fun X : Matrix (Q × Fin 2) (Q × Fin 2) ℂ => X (0,0) (0,0)) h
    norm_num [tracezeroFixedWitness, Matrix.kronecker_apply] at he
  · rw [tracezeroFixedWitness, Matrix.trace_kronecker]
    norm_num [Matrix.trace, Fin.sum_univ_two]
  · intro t
    have h := matrix_stationary_fixed t (1 : Mat)
    rw [hs] at h
    rw [tracezeroFixedWitness, spectatorE, spectator_product, h]
  · have h := matrix_stationary_kernel (1 : Mat)
    rw [hs] at h
    rw [tracezeroFixedWitness, spectatorH, spectator_product, h, Matrix.zero_kronecker]

theorem spectator_tracezero_contraction (t : ℝ) (ht : 0 ≤ t)
    (X : Matrix (Q × A) (Q × A) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier A)
    (htrace : FiniteQutritAveragedMixing.partialTrace A X = 0) :
    jointNorm A (spectatorE A t X) ≤ (9/10 : ℝ)^t * jointNorm A X := by
  have h := spectator_relative_contraction A t ht X hX
  simpa only [relative_zero_of_partialTrace_zero A X htrace, sub_zero] using h

theorem E_negative_expansion (t : ℝ) (ht : 0 < t) :
    ‖rawEigenvector 1‖ < ‖E (-t) (rawEigenvector 1)‖ := by
  rw [E_sharp, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 9/10)]
  have he : 1 < Real.exp (Real.log (9/10 : ℝ) * -t) := by
    rw [Real.one_lt_exp_iff]
    exact mul_pos_of_neg_of_neg (Real.log_neg (by norm_num) (by norm_num)) (neg_neg_of_pos ht)
  have hn := norm_pos_iff.mpr (rawEigenvector_nonzero 1)
  nlinarith

theorem prefix_event_mass (i : Index) :
    FiniteInterventionProcess.weight Q Unit 2 (wordTree Unit (prefixWord i))
      (prefixHistory i) (joint rho) = if i=5 then 1/4 else 1/3 := by
  fin_cases i
  · exact FiniteQutritAveragedExamples.original_prefix_mass 0
  · exact FiniteQutritAveragedExamples.original_prefix_mass 1
  · exact FiniteQutritAveragedExamples.original_prefix_mass 2
  · exact FiniteQutritAveragedExamples.original_prefix_mass 3
  · exact FiniteQutritAveragedExamples.original_prefix_mass 4
  · exact escape_prefix_mass

theorem integer_trace_complex (i j : Index) (n : ℕ) :
    (integerWeight i j n : ℂ) = (effect i * iterate n (effect j)).trace / 3 := by
  have hp : (run Q Unit 2 (integerExperiment i j n) (integerHistory i j n)
      (joint rho)).PosSemidef := run_posSemidef Q Unit 2 _ _
    FiniteQutritPhysicalMemoryExamples.attainer.density.1
  have him := (Complex.le_def.mp hp.trace_nonneg).2
  have he : (run Q Unit 2 (integerExperiment i j n) (integerHistory i j n) (joint rho)).trace =
      (effect i * iterate n (effect j)).trace / 3 := by
    have ha (Y : Mat) : amplifiedIterate Unit n (joint Y) = joint (iterate n Y) :=
      amplified_iterate_product Unit n Y 1
    unfold integerExperiment integerHistory
    rw [append_run, append_run, actual_run_joint, prefix_systemState,
      FiniteQutritAveragedExamples.silent_run, ha, actual_run_joint, joint_trace,
      suffix_trace, map_smul, Matrix.mul_smul, Matrix.trace_smul]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [← he]
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im, Complex.zero_im] using him

theorem integer_temporal_complex (i j : Index) (m n : ℕ) :
    (integerWeight i j (m+n) : ℂ) = temporalKernel (m,feature i) (n,feature j) := by
  rw [integer_trace_complex, integer_temporal_trace]

theorem every_fine_joint_nonnegative (i j : Index) (n : ℕ) (h : History 10 n) :
    0 ≤ (run Q Unit 2 (wordTree Unit (suffixWord i)) (suffixHistory i)
      (run Q Unit 10 (recordTree Unit n) h
        (run Q Unit 2 (wordTree Unit (prefixWord j)) (prefixHistory j) (joint rho)))).trace.re := by
  have hp : (joint rho).PosSemidef := FiniteQutritPhysicalMemoryExamples.attainer.density.1
  have h0 := (run_posSemidef Q Unit 2 (wordTree Unit (suffixWord i)) (suffixHistory i)
    (run_posSemidef Q Unit 10 (recordTree Unit n) h
      (run_posSemidef Q Unit 2 (wordTree Unit (prefixWord j)) (prefixHistory j) hp))).trace_nonneg
  exact (Complex.le_def.mp h0).1

theorem spectator_kernel_tensors (X : Matrix (Q × A) (Q × A) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier A) :
    spectatorH A X = 0 ↔ ∃ sigma : Matrix A A ℂ, X = (1 : Mat) ⊗ₖ sigma := by
  rw [spectator_generator_kernel A X hX, ← spectator_fixed A 1 (by norm_num) X hX]
  exact spectator_fixed_tensors A 1 (by norm_num) X hX

omit [DecidableEq A] in
theorem empty_joint_norm [IsEmpty A] (X : Matrix (Q × A) (Q × A) ℂ) : jointNorm A X = 0 := by
  simp [jointNorm]

theorem empty_relative_bound [IsEmpty A] (t : ℝ) (X : Matrix (Q × A) (Q × A) ℂ) :
    jointNorm A (spectatorE A t X-relativeProjection A X) ≤
      (9/10 : ℝ)^t * jointNorm A (X-relativeProjection A X) := by
  simp only [empty_joint_norm, mul_zero, le_refl]

omit [Fintype A] [DecidableEq A] in
theorem empty_generator [IsEmpty A] (X : Matrix (Q × A) (Q × A) ℂ) : spectatorH A X = 0 :=
  empty_no_nonzero_matrix A _

end SKEFTHawking.QuantumNetwork.FiniteQutritEuclideanTransfer
