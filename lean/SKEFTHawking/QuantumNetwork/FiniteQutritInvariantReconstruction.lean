import SKEFTHawking.QuantumNetwork.FiniteQutritInvariantCarrier

/-!
# The actual separation quotient and reconstructed original dynamics

The matrix carrier has the weighted Hilbert-Schmidt metric through its scaled
Euclidean embedding. Positivity and density are inherited from matrix operators.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritInvariantReconstruction
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteQutritPhysicalMemory FiniteQutritInvariantCarrier
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

private theorem vec6_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

def kernel : Matrix Index Index ℂ := commonCut.probability.map Complex.ofReal
def operatorCoordinates : Matrix (Q × Q) Index ℂ := fun ab i => effect i ab.1 ab.2

theorem kernel_gram :
    kernel = (1/3 : ℝ) • (operatorCoordinatesᴴ * operatorCoordinates) := by
  ext i j
  change (commonCut.probability i j : ℂ) = _
  rw [commonCut_probability]
  fin_cases i <;> fin_cases j <;>
    norm_num [operatorCoordinates, effect, projector, escape_matrix, Matrix.smul_apply,
      Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.trace,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, vec6_last, map_ofNat]

theorem kernel_positive : kernel.PosSemidef := by
  rw [kernel_gram]
  exact (Matrix.posSemidef_conjTranspose_mul_self operatorCoordinates).smul
    (by norm_num : (0 : ℝ) ≤ 1/3)

theorem kernel_det : kernel.det = 1/23328 := by
  change (Complex.ofRealHom.mapMatrix commonCut.probability).det = _
  rw [← Complex.ofRealHom.map_det, commonCut_det]
  norm_num

theorem kernel_mulVec_eq_zero {c : Index → ℂ} (hc : kernel *ᵥ c = 0) : c = 0 := by
  have hd : IsUnit kernel.det := isUnit_iff_ne_zero.mpr (by rw [kernel_det]; norm_num)
  have h := congrArg (fun x => kernel⁻¹ *ᵥ x) hc
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h
  exact h

theorem kernel_nullSpace : FinitePositiveKernel.nullSpace kernel kernel_positive = ⊥ := by
  ext c
  rw [Submodule.mem_bot]
  constructor
  · intro hc
    exact kernel_mulVec_eq_zero
      ((FinitePositiveKernel.null_iff_mulVec_eq_zero kernel kernel_positive c).mp
        ((FinitePositiveKernel.mem_nullSpace_iff kernel kernel_positive c).mp hc))
  · intro hc
    rw [hc]
    exact Submodule.zero_mem _

abbrev FeatureSpace := FinitePositiveKernel.Space kernel kernel_positive

def coefficientEquiv : (Index → ℂ) ≃ₗ[ℂ] FeatureSpace :=
  LinearEquiv.ofBijective (FinitePositiveKernel.mkLinear kernel kernel_positive)
    ⟨LinearMap.ker_eq_bot.mp kernel_nullSpace,
      FinitePositiveKernel.mk_surjective kernel kernel_positive⟩

def feature (i : Index) : FeatureSpace := FinitePositiveKernel.feature kernel kernel_positive i

theorem feature_dimension : Module.finrank ℂ FeatureSpace = 6 := by
  have h := coefficientEquiv.finrank_eq
  rw [Module.finrank_pi] at h
  exact h.symm

def featureBasis : Module.Basis Index ℂ FeatureSpace :=
  (Pi.basisFun ℂ Index).map coefficientEquiv

theorem featureBasis_apply (i : Index) : featureBasis i = feature i := by
  change coefficientEquiv ((Pi.basisFun ℂ Index) i) = _
  rw [Pi.basisFun_apply]
  rfl

theorem features_spanning (q : FeatureSpace) : ∃ c : Index → ℂ, q = ∑ i, c i • feature i :=
  FinitePositiveKernel.exists_feature_sum _ _ q

abbrev operatorEmbedding := FiniteQutritPhysicalMemoryExamples.operatorEmbedding

def operatorMap : (Index → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Q × Q) :=
  operatorEmbedding.comp combination

theorem operator_feature_inner (i j : Index) :
    ⟪operatorEmbedding (effect i), operatorEmbedding (effect j)⟫_ℂ = kernel i j := by
  rw [FiniteQutritPhysicalMemoryExamples.operatorEmbedding_inner, (effect_hermitian i).eq]
  exact (commonCut_probability i j).symm

theorem operatorMap_inner (c d : Index → ℂ) :
    ⟪operatorMap c, operatorMap d⟫_ℂ = FinitePositiveKernel.pairing kernel c d := by
  change ⟪operatorEmbedding (∑ i, c i • effect i),
    operatorEmbedding (∑ j, d j • effect j)⟫_ℂ = _
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, operator_feature_inner]
  simp only [FinitePositiveKernel.pairing, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.star_apply, Complex.star_def]
  ring

theorem operatorMap_injective : Function.Injective operatorMap := by
  apply (LinearMap.ker_eq_bot).mp
  ext c
  rw [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hc
    have hp : FinitePositiveKernel.pairing kernel c c = 0 := by
      rw [← operatorMap_inner, hc, inner_zero_left]
    exact kernel_mulVec_eq_zero
      ((FinitePositiveKernel.null_iff_mulVec_eq_zero kernel kernel_positive c).mp hp)
  · intro hc
    rw [hc, map_zero]

abbrev OperatorSpace := LinearMap.range operatorMap

def operatorEquiv : (Index → ℂ) ≃ₗ[ℂ] OperatorSpace :=
  LinearEquiv.ofInjective operatorMap operatorMap_injective

def reconstructionLinear : FeatureSpace ≃ₗ[ℂ] OperatorSpace :=
  coefficientEquiv.symm.trans operatorEquiv

theorem reconstruction_inner (x y : FeatureSpace) :
    ⟪reconstructionLinear x, reconstructionLinear y⟫_ℂ = ⟪x,y⟫_ℂ := by
  obtain ⟨c,rfl⟩ := FinitePositiveKernel.mk_surjective kernel kernel_positive x
  obtain ⟨d,rfl⟩ := FinitePositiveKernel.mk_surjective kernel kernel_positive y
  change ⟪operatorMap (coefficientEquiv.symm (coefficientEquiv c)),
    operatorMap (coefficientEquiv.symm (coefficientEquiv d))⟫_ℂ = _
  rw [coefficientEquiv.symm_apply_apply, coefficientEquiv.symm_apply_apply,
    operatorMap_inner, FinitePositiveKernel.inner_mk]

def reconstruction : FeatureSpace ≃ₗᵢ[ℂ] OperatorSpace where
  toLinearEquiv := reconstructionLinear
  norm_map' x := by
    have h := reconstruction_inner x x
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (reconstructionLinear x),
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x] at h
    have hr : ‖reconstructionLinear x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
    nlinarith [norm_nonneg (reconstructionLinear x), norm_nonneg x]

/-- Raw operator reconstruction onto all of the symmetric subspace. -/
def U : FeatureSpace ≃ₗ[ℂ] symmetricCarrier := coefficientEquiv.symm.trans effectEquiv

theorem U_coefficient (c : Index → ℂ) : (U (coefficientEquiv c) : Mat) = combination c := by
  change combination (coefficientEquiv.symm (coefficientEquiv c)) = _
  rw [coefficientEquiv.symm_apply_apply]

theorem U_feature (i : Index) : (U (feature i) : Mat) = effect i := by
  change (U (coefficientEquiv (Pi.single i 1)) : Mat) = _
  rw [U_coefficient]
  simp [combination]

theorem U_inner (q r : FeatureSpace) :
    ((U q : Mat)ᴴ * (U r : Mat)).trace / 3 = ⟪q,r⟫_ℂ := by
  obtain ⟨c,rfl⟩ := coefficientEquiv.surjective q
  obtain ⟨d,rfl⟩ := coefficientEquiv.surjective r
  rw [U_coefficient, U_coefficient,
    ← FiniteQutritPhysicalMemoryExamples.operatorEmbedding_inner]
  exact (operatorMap_inner c d).trans (FinitePositiveKernel.inner_mk _ _ c d).symm

def restrictedBranch (j : Setting) (a : Fin 2) : symmetricCarrier →ₗ[ℂ] symmetricCarrier where
  toFun X := ⟨systemBranch j a X, branch_invariant j a X.property⟩
  map_add' X Y := Subtype.ext ((systemBranch j a).map_add X Y)
  map_smul' c X := Subtype.ext ((systemBranch j a).map_smul c X)

/-- This conjugation uses proved invariance of the actual original maps. -/
def branch (j : Setting) (a : Fin 2) : FeatureSpace →ₗ[ℂ] FeatureSpace :=
  U.symm.toLinearMap.comp ((restrictedBranch j a).comp U.toLinearMap)

theorem U_branch (j : Setting) (a : Fin 2) (q : FeatureSpace) :
    (U (branch j a q) : Mat) = systemBranch j a (U q) := by
  change (U (U.symm (restrictedBranch j a (U q))) : Mat) = _
  rw [U.apply_symm_apply]
  rfl

def initial : FeatureSpace := U.symm ⟨rho,rho_mem⟩

theorem U_initial : (U initial : Mat) = rho := by
  change (U (U.symm _) : Mat) = _
  rw [U.apply_symm_apply]

def word : (w : List Setting) → History 2 w.length → FeatureSpace → FeatureSpace
  | [], _, q => q
  | j :: w, (a,h), q => word w h (branch j a q)

theorem U_word (w : List Setting) (h : History 2 w.length) (q : FeatureSpace) :
    (U (word w h q) : Mat) = systemRun w h (U q) := by
  induction w generalizing q with
  | nil => rfl
  | cons j w ih =>
    change (U (word w h.2 (branch j h.1 q)) : Mat) = _
    rw [ih, U_branch]
    rfl

theorem actual_word (w : List Setting) (h : History 2 w.length) (q : FeatureSpace) :
    run Q Unit 2 (wordTree Unit w) h (joint (U q : Mat)) = joint (U (word w h q)) := by
  rw [actual_run_joint, U_word]

def trace : FeatureSpace →ₗ[ℂ] ℂ where
  toFun q := (U q : Mat).trace
  map_add' q r := by simp [map_add, Matrix.trace_add]
  map_smul' c q := by simp [map_smul, Matrix.trace_smul]

def cone : Set FeatureSpace := {q | (U q : Mat).PosSemidef}
def density : Set FeatureSpace := {q | q ∈ cone ∧ trace q = 1}

theorem branch_cone (j : Setting) (a : Fin 2) {q : FeatureSpace} (hq : q ∈ cone) :
    branch j a q ∈ cone := by
  change (U (branch j a q) : Mat).PosSemidef
  rw [U_branch]
  change (outcomeOperator j a * (U q : Mat) * outcomeOperator j a).PosSemidef
  have hp := hq.mul_mul_conjTranspose_same (outcomeOperator j a)
  simpa only [outcomeOperator_hermitian] using hp


def algebraicReconstruction :
    (FinitePositiveKernel.Coefficients kernel_positive ⧸
      FinitePositiveKernel.nullSpace kernel kernel_positive) ≃ₗ[ℂ] symmetricCarrier :=
  (FinitePositiveKernel.quotientEquiv kernel kernel_positive).trans U

theorem initial_features : initial = (1/3 : ℂ) • (feature 0 + feature 1 + feature 2) := by
  apply U.injective
  apply Subtype.ext
  simp only [map_smul, map_add, Submodule.coe_smul, Submodule.coe_add, U_initial, U_feature]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rho, effect, projector, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, vec6_last, Matrix.one_apply, Fin.ext_iff]

theorem prefix_features (i : Index) :
    word (prefixWord i) (prefixHistory i) initial = (1/3 : ℂ) • feature i := by
  apply U.injective
  apply Subtype.ext
  rw [U_word, U_initial, prefix_systemState]
  simp only [map_smul, Submodule.coe_smul, U_feature]

def suffixFunctional (i : Index) : FeatureSpace →ₗ[ℂ] ℂ where
  toFun q := (effect i * (U q : Mat)).trace
  map_add' q r := by simp [map_add, Matrix.mul_add, Matrix.trace_add]
  map_smul' c q := by simp [map_smul, Matrix.trace_smul]

theorem suffix_inner (i : Index) (q : FeatureSpace) :
    suffixFunctional i q = 3 * ⟪feature i,q⟫_ℂ := by
  change (effect i * (U q : Mat)).trace = _
  rw [← U_inner, U_feature, (effect_hermitian i).eq]
  change _ = 3 * ((effect i * (U q : Mat)).trace / 3)
  ring

theorem suffix_selected (i j : Index) :
    suffixFunctional i ((1/3 : ℂ) • feature j) = kernel i j := by
  change (effect i * (U ((1/3 : ℂ) • feature j) : Mat)).trace = (commonCut.probability i j : ℂ)
  simp only [map_smul, Submodule.coe_smul, U_feature, Matrix.mul_smul, Matrix.trace_smul]
  exact (by simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using (commonCut_probability i j).symm)

theorem suffix_word_trace (i : Index) (q : FeatureSpace) :
    trace (word (suffixWord i) (suffixHistory i) q) = suffixFunctional i q := by
  change (U (word _ _ q) : Mat).trace = _
  rw [U_word, suffix_trace]
  rfl

theorem word_zero (w : List Setting) (h : History 2 w.length) : word w h 0 = 0 := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change word w h.2 (branch j h.1 0) = 0
    rw [map_zero, ih]

theorem word_append (u v : List Setting) (h : History 2 u.length)
    (g : History 2 v.length) (q : FeatureSpace) :
    word (u ++ v) (FiniteQutritPhysicalMemoryExamples.wordAppendHistory u v h g) q =
      word v g (word u h q) := by
  apply U.injective
  apply Subtype.ext
  have hr := FiniteQutritPhysicalMemoryExamples.word_run_concatenation u v h g (joint (U q : Mat))
  rw [actual_word, actual_word, actual_word] at hr
  simpa only [unJoint_joint] using congrArg unJoint hr

theorem branch_sum_trace (j : Setting) (q : FeatureSpace) :
    (∑ a, trace (branch j a q)) = trace q := by
  have h : (∑ h : Fin 2 × Unit,
    (run Q Unit 2 (wordTree Unit [j]) h (joint (U q : Mat))).trace) = (joint (U q : Mat)).trace :=
      sum_trace Q Unit 2 (wordTree Unit [j]) (joint (U q : Mat))
  have he (a : Fin 2) :
      (run Q Unit 2 (wordTree Unit [j]) (a,()) (joint (U q : Mat))).trace = trace (branch j a q) := by
    rw [actual_word, joint_trace]
    rfl
  simp only [Fintype.sum_prod_type, Fintype.sum_unique] at h
  change (∑ a : Fin 2,
    (run Q Unit 2 (wordTree Unit [j]) (a,()) (joint (U q : Mat))).trace) = _ at h
  simp_rw [he] at h
  rw [joint_trace] at h
  exact h

theorem branch_trace_nonincreasing (j : Setting) (a : Fin 2) {q : FeatureSpace}
    (hq : q ∈ cone) : (trace (branch j a q)).re ≤ (trace q).re := by
  have h0 := (Complex.le_def.mp (branch_cone j 0 hq).trace_nonneg).1
  have h1 := (Complex.le_def.mp (branch_cone j 1 hq).trace_nonneg).1
  have hs := congrArg Complex.re (branch_sum_trace j q)
  simp only [Fin.sum_univ_two, Complex.add_re] at hs
  change 0 ≤ (trace (branch j 0 q)).re at h0
  change 0 ≤ (trace (branch j 1 q)).re at h1
  fin_cases a
  · change (trace (branch j 0 q)).re ≤ (trace q).re; linarith
  · change (trace (branch j 1 q)).re ≤ (trace q).re; linarith

def weight (w : List Setting) (h : History 2 w.length) (q : FeatureSpace) : ℝ :=
  (trace (word w h q)).re

theorem actual_weight (w : List Setting) (h : History 2 w.length) (q : FeatureSpace) :
    FiniteInterventionProcess.weight Q Unit 2 (wordTree Unit w) h (joint (U q : Mat)) =
      weight w h q := by
  unfold FiniteInterventionProcess.weight
  rw [actual_word, joint_trace]
  rfl

theorem sum_weight (w : List Setting) (q : FeatureSpace) :
    (∑ h, weight w h q) = (trace q).re := by
  have h := FiniteInterventionProcess.sum_weight Q Unit 2 (wordTree Unit w) (joint (U q : Mat))
  simp only [actual_weight, joint_trace] at h
  exact h

theorem normalized_weights (w : List Setting) {q : FeatureSpace} (hq : q ∈ density) :
    (∀ h, 0 ≤ weight w h q) ∧ (∑ h, weight w h q) = 1 := by
  have hd : IsDensityOperator (joint (U q : Mat)) := by
    constructor
    · exact hq.1.kronecker (by simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Matrix Unit Unit ℂ))
    · rw [joint_trace]; exact hq.2
  have h := FiniteInterventionProcess.normalized_weights Q Unit 2 (wordTree Unit w) hd
  simpa only [actual_weight] using h

theorem prefix_marginal (u v : List Setting) (h : History 2 u.length) (q : FeatureSpace) :
    (∑ g, weight v g (word u h q)) = weight u h q := sum_weight v _

theorem no_future_signaling (u v w : List Setting) (h : History 2 u.length)
    (q : FeatureSpace) :
    (∑ g, weight v g (word u h q)) = (∑ g, weight w g (word u h q)) := by
  rw [prefix_marginal, prefix_marginal]

/-- Coefficient zero extension into the genuine larger quotient. -/
def zeroExtend : (Setting → ℂ) →ₗ[ℂ] (Index → ℂ) where
  toFun c := Fin.lastCases 0 c
  map_add' c d := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change (0 : ℂ) = 0 + 0; simp
    · simp [Pi.add_apply, Fin.lastCases_castSucc]
  map_smul' a c := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change (0 : ℂ) = a • 0; simp
    · simp [Pi.smul_apply, Fin.lastCases_castSucc]

theorem zeroExtend_combination (c : Setting → ℂ) :
    combination (zeroExtend c) = FiniteQutritPhysicalMemoryExamples.operatorCombination c := by
  change (∑ i, zeroExtend c i • effect i) = ∑ j, c j • projector j
  rw [Fin.sum_univ_castSucc]
  simp only [zeroExtend, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.lastCases_castSucc, Fin.lastCases_last, zero_smul, add_zero, effect_old]

def oldEmbeddingLinear : FiniteQutritPhysicalMemoryExamples.FeatureSpace →ₗ[ℂ] FeatureSpace :=
  coefficientEquiv.toLinearMap.comp
    (zeroExtend.comp FiniteQutritPhysicalMemoryExamples.coefficientEquiv.symm.toLinearMap)

theorem oldEmbedding_inner (x y : FiniteQutritPhysicalMemoryExamples.FeatureSpace) :
    ⟪oldEmbeddingLinear x,oldEmbeddingLinear y⟫_ℂ = ⟪x,y⟫_ℂ := by
  obtain ⟨c,rfl⟩ := FiniteQutritPhysicalMemoryExamples.coefficientEquiv.surjective x
  obtain ⟨d,rfl⟩ := FiniteQutritPhysicalMemoryExamples.coefficientEquiv.surjective y
  change ⟪coefficientEquiv (zeroExtend
    (FiniteQutritPhysicalMemoryExamples.coefficientEquiv.symm
      (FiniteQutritPhysicalMemoryExamples.coefficientEquiv c))),
    coefficientEquiv (zeroExtend (FiniteQutritPhysicalMemoryExamples.coefficientEquiv.symm
      (FiniteQutritPhysicalMemoryExamples.coefficientEquiv d)))⟫_ℂ = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, ← U_inner,
    U_coefficient, U_coefficient, zeroExtend_combination, zeroExtend_combination,
    ← FiniteQutritPhysicalMemoryExamples.operatorEmbedding_inner]
  exact (FiniteQutritPhysicalMemoryExamples.operatorMap_inner c d).trans
    (FinitePositiveKernel.inner_mk _ _ c d).symm

def oldEmbedding : FiniteQutritPhysicalMemoryExamples.FeatureSpace →ₗᵢ[ℂ] FeatureSpace where
  toLinearMap := oldEmbeddingLinear
  norm_map' x := by
    have h := oldEmbedding_inner x x
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (oldEmbeddingLinear x),
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x] at h
    have hr : ‖oldEmbeddingLinear x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
    nlinarith [norm_nonneg (oldEmbeddingLinear x), norm_nonneg x]


structure Noise where
  e : ℝ
  t : ℝ
  e_nonneg : 0 ≤ e
  e_le_one : e ≤ 1
  t_nonneg : 0 ≤ t
  t_le_one : t ≤ 1

def depolarization (e : ℝ) : Mat →ₗ[ℂ] Mat where
  toFun X := (1-e) • X + e • (X.trace • rho)
  map_add' X Y := by simp [Matrix.trace_add, add_smul, smul_add]; abel
  map_smul' c X := by
    change (1-e) • (c • X) + e • ((c • X).trace • rho) =
      c • ((1-e) • X + e • (X.trace • rho))
    rw [Matrix.trace_smul, smul_add, smul_comm (1-e) c X]
    change c • (1-e) • X + e • ((c * X.trace) • rho) = _
    rw [← smul_smul c X.trace rho, smul_comm e c (X.trace • rho)]

theorem depolarization_invariant (e : ℝ) {X : Mat} (hX : X ∈ symmetricCarrier) :
    depolarization e X ∈ symmetricCarrier :=
  (hX.smul (1-e)).add ((rho_mem.smul X.trace).smul e)

theorem original_readout_branch (j : Setting) (a : Fin 2) (X : Mat) :
    (readout j).branch a X = systemBranch j a X := by
  have hp := (projector_hermitian j).eq
  have hc := (Matrix.isHermitian_one.sub (projector_hermitian j)).eq
  by_cases ha : a = 0 <;>
    simp [readout, FiniteAdaptiveReadoutDiscrimination.projectiveReadout,
      FiniteInstrument.branch, krausMap, outcomeOperator, systemBranch, ha, hp, hc]

def noisySystemBranch (N : Noise) (j : Setting) (a : Fin 2) : Mat →ₗ[ℂ] Mat :=
  (1-N.t) • ((systemBranch j a).comp (depolarization N.e)) +
    (N.t/2) • depolarization N.e

theorem noisy_invariant (N : Noise) (j : Setting) (a : Fin 2) {X : Mat}
    (hX : X ∈ symmetricCarrier) : noisySystemBranch N j a X ∈ symmetricCarrier :=
  ((branch_invariant j a (depolarization_invariant N.e hX)).smul (1-N.t)).add
    ((depolarization_invariant N.e hX).smul (N.t/2))

def noisyRestricted (N : Noise) (j : Setting) (a : Fin 2) :
    symmetricCarrier →ₗ[ℂ] symmetricCarrier where
  toFun X := ⟨noisySystemBranch N j a X, noisy_invariant N j a X.property⟩
  map_add' X Y := Subtype.ext ((noisySystemBranch N j a).map_add X Y)
  map_smul' c X := Subtype.ext ((noisySystemBranch N j a).map_smul c X)

def noisyBranch (N : Noise) (j : Setting) (a : Fin 2) : FeatureSpace →ₗ[ℂ] FeatureSpace :=
  U.symm.toLinearMap.comp ((noisyRestricted N j a).comp U.toLinearMap)

theorem U_noisyBranch (N : Noise) (j : Setting) (a : Fin 2) (q : FeatureSpace) :
    (U (noisyBranch N j a q) : Mat) = noisySystemBranch N j a (U q) := by
  change (U (U.symm (noisyRestricted N j a (U q))) : Mat) = _
  rw [U.apply_symm_apply]
  rfl

def noisyStep (N : Noise) (j : Setting) : Step Q Unit 2 :=
  FiniteQutritPhysicalMemoryExamples.noisyStep j N.e N.t
    N.e_nonneg N.e_le_one N.t_nonneg N.t_le_one

theorem actual_noisyBranch (N : Noise) (j : Setting) (a : Fin 2) (q : FeatureSpace) :
    (noisyStep N j).branch Q Unit 2 a (joint (U q : Mat)) =
      joint (U (noisyBranch N j a q) : Mat) := by
  rw [U_noisyBranch]
  change (FiniteQutritPhysicalMemoryExamples.noisyStep j N.e N.t _ _ _ _).branch
    Q Unit 2 a (joint (U q : Mat)) = _
  rw [FiniteQutritPhysicalMemoryExamples.noisyStep_branch,
    FiniteQutritPhysicalMemoryExamples.noisyReadout_branch, original_readout_branch]
  rfl

def noisyTree (N : Noise) : (w : List Setting) → Tree Q Unit 2 w.length
  | [] => .done
  | j :: w => .node (noisyStep N j) (fun _ => noisyTree N w)

def noisyWord (N : Noise) : (w : List Setting) → History 2 w.length → FeatureSpace → FeatureSpace
  | [], _, q => q
  | j :: w, (a,h), q => noisyWord N w h (noisyBranch N j a q)

theorem actual_noisyWord (N : Noise) (w : List Setting) (h : History 2 w.length)
    (q : FeatureSpace) :
    run Q Unit 2 (noisyTree N w) h (joint (U q : Mat)) =
      joint (U (noisyWord N w h q) : Mat) := by
  induction w generalizing q with
  | nil => rfl
  | cons j w ih =>
    change run Q Unit 2 (noisyTree N w) h.2
      ((noisyStep N j).branch Q Unit 2 h.1 (joint (U q : Mat))) = _
    rw [actual_noisyBranch, ih]
    rfl

theorem noisyBranch_cone (N : Noise) (j : Setting) (a : Fin 2) {q : FeatureSpace}
    (hq : q ∈ cone) : noisyBranch N j a q ∈ cone := by
  have hp : (joint (U q : Mat)).PosSemidef :=
    hq.kronecker (by simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Matrix Unit Unit ℂ))
  have hb := (noisyStep N j).branch_posSemidef Q Unit 2 a hp
  rw [actual_noisyBranch] at hb
  have he := hb.submatrix (fun a : Q => (a,()))
  change (U (noisyBranch N j a q) : Mat).PosSemidef
  convert he using 1
  ext i k
  simp [joint, Matrix.submatrix, Matrix.kroneckerMap_apply]

theorem noisy_normalized (N : Noise) (w : List Setting) {q : FeatureSpace} (hq : q ∈ density) :
    (∀ h, 0 ≤ (trace (noisyWord N w h q)).re) ∧
      (∑ h, (trace (noisyWord N w h q)).re) = 1 := by
  have hd : IsDensityOperator (joint (U q : Mat)) := by
    constructor
    · exact hq.1.kronecker (by simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Matrix Unit Unit ℂ))
    · rw [joint_trace]; exact hq.2
  have h := FiniteInterventionProcess.normalized_weights Q Unit 2 (noisyTree N w) hd
  simp only [FiniteInterventionProcess.weight, actual_noisyWord, joint_trace] at h
  exact h


theorem oldEmbedding_reconstruction (x : FiniteQutritPhysicalMemoryExamples.FeatureSpace) :
    (U (oldEmbedding x) : Mat) = FiniteQutritPhysicalMemoryExamples.operatorCombination
      (FiniteQutritPhysicalMemoryExamples.coefficientEquiv.symm x) := by
  change (U (coefficientEquiv (zeroExtend
    (FiniteQutritPhysicalMemoryExamples.coefficientEquiv.symm x))) : Mat) = _
  rw [U_coefficient, zeroExtend_combination]

theorem oldEmbedding_feature (j : Setting) :
    oldEmbedding (FinitePositiveKernel.feature FiniteQutritPhysicalMemoryExamples.kernel
      FiniteQutritPhysicalMemoryExamples.kernel_positive j) = feature j.castSucc := by
  apply U.injective
  apply Subtype.ext
  rw [oldEmbedding_reconstruction, U_feature, effect_old]
  change FiniteQutritPhysicalMemoryExamples.operatorCombination
    (FiniteQutritPhysicalMemoryExamples.coefficientEquiv.symm
      (FiniteQutritPhysicalMemoryExamples.coefficientEquiv (Pi.single j 1))) = _
  rw [LinearEquiv.symm_apply_apply]
  simp [FiniteQutritPhysicalMemoryExamples.operatorCombination]

theorem noisyWord_zero (N : Noise) (w : List Setting) (h : History 2 w.length) :
    noisyWord N w h 0 = 0 := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change noisyWord N w h.2 (noisyBranch N j h.1 0) = 0
    rw [map_zero, ih]

theorem noisyWord_append (N : Noise) (u v : List Setting) (h : History 2 u.length)
    (g : History 2 v.length) (q : FeatureSpace) :
    noisyWord N (u ++ v) (FiniteQutritPhysicalMemoryExamples.wordAppendHistory u v h g) q =
      noisyWord N v g (noisyWord N u h q) := by
  induction u generalizing q with
  | nil => rfl
  | cons j u ih => exact ih h.2 (noisyBranch N j h.1 q)

theorem noisy_sum_weight (N : Noise) (w : List Setting) (q : FeatureSpace) :
    (∑ h, (trace (noisyWord N w h q)).re) = (trace q).re := by
  have h := FiniteInterventionProcess.sum_weight Q Unit 2 (noisyTree N w) (joint (U q : Mat))
  simp only [FiniteInterventionProcess.weight, actual_noisyWord, joint_trace] at h
  exact h

theorem noisy_prefix_marginal (N : Noise) (u v : List Setting) (h : History 2 u.length)
    (q : FeatureSpace) :
    (∑ g, (trace (noisyWord N v g (noisyWord N u h q))).re) =
      (trace (noisyWord N u h q)).re := noisy_sum_weight N v _

theorem noisy_no_future_signaling (N : Noise) (u v w : List Setting)
    (h : History 2 u.length) (q : FeatureSpace) :
    (∑ g, (trace (noisyWord N v g (noisyWord N u h q))).re) =
      (∑ g, (trace (noisyWord N w g (noisyWord N u h q))).re) := by
  rw [noisy_prefix_marginal, noisy_prefix_marginal]

theorem noisy_branch_sum_trace (N : Noise) (j : Setting) (q : FeatureSpace) :
    (∑ a, trace (noisyBranch N j a q)) = trace q := by
  have h := (noisyStep N j).sum_trace Q Unit 2 (joint (U q : Mat))
  simp_rw [actual_noisyBranch, joint_trace] at h
  exact h

theorem noisy_trace_nonincreasing (N : Noise) (j : Setting) (a : Fin 2)
    {q : FeatureSpace} (hq : q ∈ cone) :
    (trace (noisyBranch N j a q)).re ≤ (trace q).re := by
  have h0 := (Complex.le_def.mp (noisyBranch_cone N j 0 hq).trace_nonneg).1
  have h1 := (Complex.le_def.mp (noisyBranch_cone N j 1 hq).trace_nonneg).1
  change 0 ≤ (trace (noisyBranch N j 0 q)).re at h0
  change 0 ≤ (trace (noisyBranch N j 1 q)).re at h1
  have hs := congrArg Complex.re (noisy_branch_sum_trace N j q)
  simp only [Fin.sum_univ_two, Complex.add_re] at hs
  fin_cases a
  · change (trace (noisyBranch N j 0 q)).re ≤ (trace q).re; linarith
  · change (trace (noisyBranch N j 1 q)).re ≤ (trace q).re; linarith

end SKEFTHawking.QuantumNetwork.FiniteQutritInvariantReconstruction
