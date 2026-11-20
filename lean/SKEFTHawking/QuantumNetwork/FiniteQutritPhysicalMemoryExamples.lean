import SKEFTHawking.QuantumNetwork.FinitePhysicalMemoryDimension
import SKEFTHawking.QuantumNetwork.FiniteQutritPhysicalMemory
import SKEFTHawking.FinitePositiveKernel
import Mathlib.Analysis.InnerProductSpace.PiL2
import SKEFTHawking.QuantumNetwork.FiniteThreeLevelAppendedMemoryExamples
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-!
# Physical dimension and operator-feature reconstruction

The physical competitor always uses its complete retained carrier. The actual
qutrit attains the selected table at dimension three. The separately constructed
positive kernel concerns operator features, whose complex dimension is five.
Deterministic perturbation statements certify exclusion and carry no statistical
or arbitrary-matrix physical realization claim.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritPhysicalMemoryExamples
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteQutritPhysicalMemory FinitePhysicalMemoryDimension
open FiniteAdaptiveMapPerturbation
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

def attainer : CommonCut Q Unit Setting Setting 2 where
  initial := joint rho
  density := by
    constructor
    · exact rho_density.1.kronecker
        (by simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Matrix Unit Unit ℂ))
    · rw [joint_trace, rho_density.2]
  prefixLength _ := 1
  prefixTree j := wordTree Unit [j]
  prefixHistory _ := (0,())
  suffixLength _ := 1
  suffixTree i := wordTree Unit [i]
  suffixHistory _ := (0,())

theorem attainer_probability : attainer.probability = selected := rfl

/-- All accessible retained records are in `S × E`, so the generic bound applies. -/
theorem selected_physical_lower_bound {S E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E] {o : ℕ} (C : CommonCut S E Setting Setting o)
    (h : C.probability = selected) : 3 ≤ Fintype.card (S × E) := by
  apply C.dimension_ge_three
  rw [h, selected_det]
  norm_num

/-- Canonical finite carriers realize exactly the same resource dimension.
This minimum concerns physical realization, not unique hidden-system recovery. -/
theorem selected_minimum_dimension :
    IsLeast {d : ℕ | ∃ C : CommonCut (Fin d) Unit Setting Setting 2,
      C.probability = selected} 3 := by
  constructor
  · exact ⟨attainer, attainer_probability⟩
  · rintro d ⟨C,hC⟩
    simpa using selected_physical_lower_bound C hC

/-- A normalized state cannot live on an empty retained carrier. -/
theorem no_density_empty {R : Type*} [Fintype R] [IsEmpty R]
    (X : Matrix R R ℂ) : ¬ IsDensityOperator X := by
  intro h
  have ht : X.trace = 0 := by simp [Matrix.trace]
  have hh := h.2
  rw [ht] at hh
  norm_num at hh

theorem product_abs_le_one {A : Type*} (s : Finset A) (f : A → ℝ)
    (hf : ∀ a ∈ s, |f a| ≤ 1) : |∏ a ∈ s, f a| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun a _ => abs_nonneg _) hf

/-- Telescoping products costs one entry error per factor, with no positivity
requirement on the estimates. -/
theorem product_error {A : Type*} (s : Finset A) (f g : A → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hf : ∀ a ∈ s, |f a| ≤ 1) (hg : ∀ a ∈ s, |g a| ≤ 1)
    (he : ∀ a ∈ s, |f a - g a| ≤ δ) :
    |(∏ a ∈ s, f a) - ∏ a ∈ s, g a| ≤ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hs : ∀ x ∈ s, |f x| ≤ 1 := fun x hx => hf x (Finset.mem_insert_of_mem hx)
    have ht : ∀ x ∈ s, |g x| ≤ 1 := fun x hx => hg x (Finset.mem_insert_of_mem hx)
    have hu : ∀ x ∈ s, |f x - g x| ≤ δ := fun x hx => he x (Finset.mem_insert_of_mem hx)
    calc
      |f a * (∏ x ∈ s, f x) - g a * ∏ x ∈ s, g x| =
          |f a * ((∏ x ∈ s, f x) - ∏ x ∈ s, g x) +
            (f a - g a) * ∏ x ∈ s, g x| := by congr 1; ring
      _ ≤ |f a * ((∏ x ∈ s, f x) - ∏ x ∈ s, g x)| +
          |(f a - g a) * ∏ x ∈ s, g x| := abs_add_le _ _
      _ = |f a| * |(∏ x ∈ s, f x) - ∏ x ∈ s, g x| +
          |f a - g a| * |∏ x ∈ s, g x| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (s.card * δ) + δ * 1 := by
        apply add_le_add
        · exact mul_le_mul (hf a (Finset.mem_insert_self _ _)) (ih hs ht hu)
            (abs_nonneg _) (by norm_num)
        · exact mul_le_mul (he a (Finset.mem_insert_self _ _))
            (product_abs_le_one s g ht) (abs_nonneg _) hδ
      _ = (↑(s.card + 1) : ℝ) * δ := by push_cast; ring

/-- Five factors and 120 determinant terms yield the stated coarse constant. -/
theorem determinant_error (M N : Matrix Setting Setting ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hM : ∀ i j, |M i j| ≤ 1) (hN : ∀ i j, |N i j| ≤ 1)
    (he : ∀ i j, |M i j - N i j| ≤ δ) : |M.det - N.det| ≤ 600 * δ := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  calc
    |∑ σ : Equiv.Perm Setting,
        ((Equiv.Perm.sign σ • ∏ i, M (σ i) i) -
          (Equiv.Perm.sign σ • ∏ i, N (σ i) i))| ≤
        ∑ σ : Equiv.Perm Setting, |(Equiv.Perm.sign σ • ∏ i, M (σ i) i) -
          (Equiv.Perm.sign σ • ∏ i, N (σ i) i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm Setting, (5 : ℝ) * δ := by
      apply Finset.sum_le_sum
      intro σ _
      have hp := product_error Finset.univ (fun i => M (σ i) i)
        (fun i => N (σ i) i) hδ (fun i _ => hM _ _) (fun i _ => hN _ _)
        (fun i _ => he _ _)
      rw [← smul_sub]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
        simpa [hs, abs_sub_comm] using hp
    _ = 600 * δ := by simp [Fintype.card_perm]; ring

theorem nearby_selected_positive_det (M : Matrix Setting Setting ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hr : δ < 1 / 583200) (hM : ∀ i j, |M i j| ≤ 1)
    (he : ∀ i j, |M i j - selected i j| ≤ δ) : 0 < M.det := by
  have hH : ∀ i j, |selected i j| ≤ 1 := by
    intro i j
    rw [abs_of_nonneg (selected_nonneg i j)]
    exact (selected_le_third i j).trans (by norm_num)
  have hd := determinant_error M selected hδ hM hH he
  rw [selected_det, abs_le] at hd
  linarith

theorem nearby_selected_millionth (M : Matrix Setting Setting ℝ)
    (hM : ∀ i j, |M i j| ≤ 1)
    (he : ∀ i j, |M i j - selected i j| ≤ 1 / 1000000) :
    521 / 1215000 ≤ M.det := by
  have hH : ∀ i j, |selected i j| ≤ 1 := by
    intro i j
    rw [abs_of_nonneg (selected_nonneg i j)]
    exact (selected_le_third i j).trans (by norm_num)
  have hd := determinant_error M selected (by norm_num) hM hH he
  rw [selected_det, abs_le] at hd
  linarith

/-- Nine coordinates describe operators, not a nine-dimensional physical carrier. -/
def operatorCoordinates : Matrix (Q × Q) Setting ℂ := fun ab j => projector j ab.1 ab.2

def kernel : Matrix Setting Setting ℂ := selected.map Complex.ofReal

/-- The selected fixture has a separately proved operator Gram representation.
Generic controlled probability minors need not be symmetric or positive kernels. -/
theorem kernel_gram :
    kernel = (1 / 3 : ℝ) • (operatorCoordinatesᴴ * operatorCoordinates) := by
  ext i j
  change (selected i j : ℂ) = _
  rw [selected_trace]
  fin_cases i <;> fin_cases j <;>
    norm_num [operatorCoordinates, projector, Matrix.smul_apply,
      Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.trace,
      Fintype.sum_prod_type, Fin.sum_univ_succ, map_ofNat]

theorem kernel_positive : kernel.PosSemidef := by
  rw [kernel_gram]
  exact (Matrix.posSemidef_conjTranspose_mul_self operatorCoordinates).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 3)

theorem kernel_det : kernel.det = 1 / 972 := by
  change (Complex.ofRealHom.mapMatrix selected).det = _
  rw [← Complex.ofRealHom.map_det, selected_det]
  norm_num

theorem kernel_mulVec_eq_zero {c : Setting → ℂ} (hc : kernel *ᵥ c = 0) : c = 0 := by
  have hd : IsUnit kernel.det := isUnit_iff_ne_zero.mpr (by rw [kernel_det]; norm_num)
  have h := congrArg (fun x => kernel⁻¹ *ᵥ x) hc
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h
  exact h

/-- The existing kernel quotient has no nonzero null coefficients for this fixture. -/
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

def coefficientEquiv : (Setting → ℂ) ≃ₗ[ℂ] FeatureSpace :=
  LinearEquiv.ofBijective (FinitePositiveKernel.mkLinear kernel kernel_positive)
    ⟨LinearMap.ker_eq_bot.mp kernel_nullSpace,
      FinitePositiveKernel.mk_surjective kernel kernel_positive⟩

/-- The reconstructed complex feature dimension is exactly five, whereas the
retained physical Hilbert minimum of the same experiment is three. -/
theorem feature_dimension : Module.finrank ℂ FeatureSpace = 5 := by
  apply Nat.le_antisymm
  · exact FinitePositiveKernel.finrank_le_card kernel kernel_positive
  · have h := coefficientEquiv.finrank_eq
    rw [Module.finrank_pi] at h
    exact h.le

theorem feature_pairing (i j : Setting) :
    ⟪FinitePositiveKernel.feature kernel kernel_positive i,
      FinitePositiveKernel.feature kernel kernel_positive j⟫_ℂ =
      (selected i j : ℂ) := FinitePositiveKernel.inner_feature _ _ _ _

/-- Scaled Euclidean coordinates give the weighted Hilbert-Schmidt structure;
the ordinary matrix sup norm plays no role. -/
def operatorEmbedding : Mat →ₗ[ℂ] EuclideanSpace ℂ (Q × Q) where
  toFun X := WithLp.toLp 2 (fun ab => (Real.sqrt 3 : ℂ)⁻¹ * X ab.1 ab.2)
  map_add' X Y := by ext ab; exact mul_add _ _ _
  map_smul' c X := by ext ab; change _ * (c * _) = c * (_ * _); ring

theorem operatorEmbedding_inner (X Y : Mat) :
    ⟪operatorEmbedding X, operatorEmbedding Y⟫_ℂ = (Xᴴ * Y).trace / 3 := by
  have hs : (Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹ = 1 / 3 := by
    rw [← mul_inv]
    have h : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    rw [h]
    norm_num
  have hstar : star ((Real.sqrt 3 : ℂ)⁻¹) = (Real.sqrt 3 : ℂ)⁻¹ := by simp
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ ab : Q × Q, ((Real.sqrt 3 : ℂ)⁻¹ * Y ab.1 ab.2) *
    star ((Real.sqrt 3 : ℂ)⁻¹ * X ab.1 ab.2)) = _
  simp only [star_mul, hstar]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = ((Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹) * (star (X b a) * Y b a) := by ring
    _ = _ := by rw [hs]; ring

def operatorCombination : (Setting → ℂ) →ₗ[ℂ] Mat where
  toFun c := ∑ j, c j • projector j
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

def operatorMap : (Setting → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Q × Q) :=
  operatorEmbedding.comp operatorCombination

theorem operator_feature_inner (i j : Setting) :
    ⟪operatorEmbedding (projector i), operatorEmbedding (projector j)⟫_ℂ = kernel i j := by
  rw [operatorEmbedding_inner, (projector_hermitian i).eq]
  change _ = (selected i j : ℂ)
  rw [selected_trace]
  fin_cases i <;> fin_cases j <;>
    norm_num [projector, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ]

/-- The physical operators, rather than a branch Gram on carrier three,
realize the coefficient pairing of the existing kernel construction. -/
theorem operatorMap_inner (c d : Setting → ℂ) :
    ⟪operatorMap c, operatorMap d⟫_ℂ = FinitePositiveKernel.pairing kernel c d := by
  change ⟪operatorEmbedding (∑ i, c i • projector i),
    operatorEmbedding (∑ j, d j • projector j)⟫_ℂ = _
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

/-- The actual span of scaled qutrit operators inherits its Euclidean inner product. -/
abbrev OperatorSpace := LinearMap.range operatorMap

def operatorEquiv : (Setting → ℂ) ≃ₗ[ℂ] OperatorSpace :=
  LinearEquiv.ofInjective operatorMap operatorMap_injective

/-- A representative-independent linear identification onto the operator span. -/
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

/-- The finite positive-kernel quotient and the weighted operator span are isometric. -/
def reconstruction : FeatureSpace ≃ₗᵢ[ℂ] OperatorSpace where
  toLinearEquiv := reconstructionLinear
  norm_map' x := by
    have h := reconstruction_inner x x
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (reconstructionLinear x),
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x] at h
    have hr : ‖reconstructionLinear x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
    nlinarith [norm_nonneg (reconstructionLinear x), norm_nonneg x]

def resetKraus : Fin 9 → Mat := fun k =>
  (Real.sqrt (1 / 3) : ℝ) • Matrix.single
    ((finProdFinEquiv : Q × Q ≃ Fin 9).symm k).1 ((finProdFinEquiv : Q × Q ≃ Fin 9).symm k).2 1

theorem resetKraus_normalized : IsKrausChannel resetKraus := by
  unfold IsKrausChannel
  rw [← Fintype.sum_equiv (finProdFinEquiv : Q × Q ≃ Fin 9)
    (fun ab => (resetKraus (finProdFinEquiv ab))ᴴ * resetKraus (finProdFinEquiv ab))
    (fun k => (resetKraus k)ᴴ * resetKraus k) (fun _ => rfl)]
  simp only [resetKraus, Equiv.symm_apply_apply,
    sqrt_normalization _ (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.sum_apply, Matrix.smul_apply, Fin.reduceFinMk] <;> decide

/-- The nine matrix-unit Kraus operators implement complete depolarization. -/
theorem resetKraus_action (X : Mat) : krausMap resetKraus X = X.trace • rho := by
  unfold krausMap
  rw [← Fintype.sum_equiv (finProdFinEquiv : Q × Q ≃ Fin 9)
    (fun ab => resetKraus (finProdFinEquiv ab) * X * (resetKraus (finProdFinEquiv ab))ᴴ)
    (fun k => resetKraus k * X * (resetKraus k)ᴴ) (fun _ => rfl)]
  simp only [resetKraus, Equiv.symm_apply_apply,
    sqrt_action _ (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.trace] <;> ring

def identityKraus : Fin 1 → Mat := fun _ => 1

theorem identityKraus_normalized : IsKrausChannel identityKraus := by
  simp [identityKraus, IsKrausChannel]

def depolarizingKraus (e : ℝ) : Fin 10 → Mat := mixKraus identityKraus resetKraus e

theorem depolarizingKraus_normalized {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) :
    IsKrausChannel (depolarizingKraus e) :=
  mixKraus_channel identityKraus_normalized resetKraus_normalized he he1

theorem depolarizingKraus_action {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) (X : Mat) :
    krausMap (depolarizingKraus e) X = (1-e) • X + e • (X.trace • rho) := by
  rw [depolarizingKraus, mixKraus_action _ _ he he1, resetKraus_action]
  simp [identityKraus, krausMap]

theorem depolarizingKraus_identity (e : ℝ) :
    depolarizingKraus e (Fin.castAdd 9 (0 : Fin 1)) = Real.sqrt (1-e) • (1 : Mat) := by
  simp only [depolarizingKraus, mixKraus, Fin.addCases_left, identityKraus]

/-- The other nine Kraus operators have the specified `sqrt(e/3)` coefficient. -/
theorem depolarizingKraus_matrixUnit {e : ℝ} (he : 0 ≤ e) (ab : Q × Q) :
    depolarizingKraus e (Fin.natAdd 1 (finProdFinEquiv ab)) =
      Real.sqrt (e / 3) • Matrix.single ab.1 ab.2 (1 : ℂ) := by
  simp only [depolarizingKraus, mixKraus, Fin.addCases_right, resetKraus,
    Equiv.symm_apply_apply, smul_smul]
  congr 1
  rw [← Real.sqrt_mul he]
  congr 1
  ring

def fairReadout : FiniteInstrument Q 2 where
  count := 1
  operators _ _ := Real.sqrt (1 / 2) • (1 : Mat)
  normalized := by
    simp only [Fin.sum_univ_two, Fin.sum_univ_one,
      sqrt_normalization _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, ← add_smul]
    norm_num

theorem fairReadout_branch (a : Fin 2) (X : Mat) :
    fairReadout.branch a X = (1 / 2 : ℝ) • X := by
  change krausMap (fun _ : Fin 1 => Real.sqrt (1 / 2) • (1 : Mat)) X = _
  simp only [krausMap, Fin.sum_univ_one,
    sqrt_action _ (by norm_num : (0 : ℝ) ≤ 1 / 2), Matrix.one_mul,
    Matrix.conjTranspose_one, Matrix.mul_one]

def noisyReadout (i : Setting) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    FiniteInstrument Q 2 := mixInstrument (readout i) fairReadout t ht ht1

theorem noisyReadout_branch (i : Setting) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (a : Fin 2) (X : Mat) :
    (noisyReadout i t ht ht1).branch a X =
      (1-t) • (readout i).branch a X + (t / 2) • X := by
  rw [noisyReadout, mixInstrument_branch, fairReadout_branch, smul_smul]
  congr 1
  congr 1
  ring

theorem jointDepolarizing_normalized {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) :
    IsKrausChannel (fun k => joint (depolarizingKraus e k)) := by
  unfold IsKrausChannel
  calc
    _ = joint (∑ k, (depolarizingKraus e k)ᴴ * depolarizingKraus e k) := by
      simp only [joint_adjoint, joint_mul, joint_sum]
    _ = joint (1 : Mat) := congrArg joint (depolarizingKraus_normalized he he1)
    _ = 1 := joint_one


/-- Evolution precedes the suffix readout within one existing step; no extra
binary event is inserted by either noise source. -/
def noisyStep (i : Setting) (e t : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : Step Q Unit 2 where
  count := 10
  evolution k := joint (depolarizingKraus e k)
  normalized := jointDepolarizing_normalized he he1
  instrument := noisyReadout i t ht ht1

theorem jointKraus_action {k : ℕ} (K : Fin k → Mat) (X : Mat) :
    krausMap (fun k => joint (K k)) (joint X) = joint (krausMap K X) := by
  simp only [krausMap, joint_mul, joint_adjoint, joint_sum]

theorem noisyStep_branch (i : Setting) (e t : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (a : Fin 2) (X : Mat) :
    (noisyStep i e t he he1 ht ht1).branch Q Unit 2 a (joint X) =
      joint ((noisyReadout i t ht ht1).branch a
        ((1-e) • X + e • (X.trace • rho))) := by
  change ((noisyReadout i t ht ht1).lift Unit).branch a
    (krausMap (fun k => joint (depolarizingKraus e k)) (joint X)) = _
  rw [jointKraus_action, depolarizingKraus_action he he1, joint, lift_branch_tensor]
  rfl

def noisyAttainer (e t : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    CommonCut Q Unit Setting Setting 2 where
  initial := attainer.initial
  density := attainer.density
  prefixLength := attainer.prefixLength
  prefixTree := attainer.prefixTree
  prefixHistory := attainer.prefixHistory
  suffixLength _ := 1
  suffixTree i := .node (noisyStep i e t he he1 ht ht1) (fun _ => .done)
  suffixHistory _ := (0,())

theorem attainer_prefixState (j : Setting) :
    attainer.prefixState j = joint ((1 / 3 : ℝ) • projector j) := by
  change run Q Unit 2 (wordTree Unit [j]) (0,()) (joint rho) = _
  rw [joint, word_product_input]
  congr 1
  simp only [systemProduct, outcomeOperator, ite_true, Matrix.one_mul, rho,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, (projector_hermitian j).eq,
    projector_idempotent]

theorem readout_trace (i : Setting) (X : Mat) :
    ((readout i).branch 0 X).trace = (projector i * X).trace := by
  rw [readout, FiniteAdaptiveReadoutDiscrimination.projectiveReadout_branch_zero,
    Matrix.trace_mul_cycle, projector_idempotent]

/-- The exact table of an actual normalized evolution/readout experiment. -/
theorem noisyAttainer_probability (e t : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (i j : Setting) :
    (noisyAttainer e t he he1 ht ht1).probability i j =
      (1-t) * ((1-e) * selected i j + e / 9) + t / 6 := by
  unfold CommonCut.probability weight
  rw [append_run]
  change ((noisyStep i e t he he1 ht ht1).branch Q Unit 2 0
    (attainer.prefixState j)).trace.re = _
  rw [attainer_prefixState, noisyStep_branch, joint_trace, noisyReadout_branch]
  simp only [Matrix.trace_add, Matrix.trace_smul, readout_trace]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, projector_trace, smul_eq_mul, rho_density.2]
  have hr : (projector i * rho).trace = (1 / 3 : ℂ) := by
    simp [rho, Matrix.trace_smul, projector_trace]
  rw [hr]
  rw [selected_trace]
  simp only [Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.one_re, Complex.one_im]
  norm_num
  ring

theorem noisyAttainer_error (e t : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (i j : Setting) :
    |(noisyAttainer e t he he1 ht ht1).probability i j - selected i j| ≤
      2 * e / 9 + t / 6 := by
  rw [noisyAttainer_probability]
  have h0 := selected_nonneg i j
  have h1 := selected_le_third i j
  have ha : |1 / 9 - selected i j| ≤ 2 / 9 := by
    rw [abs_le]; constructor <;> linarith
  have hb : |1 / 6 - selected i j| ≤ 1 / 6 := by
    rw [abs_le]; constructor <;> linarith
  have hte : 0 ≤ (1-t)*e := mul_nonneg (sub_nonneg.mpr ht1) he
  calc
    _ = |((1-t)*e) * (1 / 9 - selected i j) + t * (1 / 6 - selected i j)| := by
      congr 1; ring
    _ ≤ |((1-t)*e) * (1 / 9 - selected i j)| +
        |t * (1 / 6 - selected i j)| := abs_add_le _ _
    _ = ((1-t)*e) * |1 / 9 - selected i j| + t * |1 / 6 - selected i j| := by
      simp only [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1),
        abs_of_nonneg he, abs_of_nonneg ht]
    _ ≤ ((1-t)*e) * (2 / 9) + t * (1 / 6) :=
      add_le_add (mul_le_mul_of_nonneg_left ha hte) (mul_le_mul_of_nonneg_left hb ht)
    _ ≤ 2 * e / 9 + t / 6 := by nlinarith [mul_nonneg ht he]

def smallNoiseAttainer : CommonCut Q Unit Setting Setting 2 :=
  noisyAttainer (1 / 10000000) (1 / 10000000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

def noisySelected : Matrix Setting Setting ℝ := smallNoiseAttainer.probability

theorem noisySelected_error (i j : Setting) :
    |noisySelected i j - selected i j| ≤ 7 / 180000000 := by
  have h := noisyAttainer_error (1 / 10000000) (1 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) i j
  norm_num at h
  exact h

theorem noisySelected_positive_det : 0 < noisySelected.det := by
  apply nearby_selected_positive_det noisySelected (by norm_num)
    (by norm_num : (7 / 180000000 : ℝ) < 1 / 583200)
  · intro i j
    change |smallNoiseAttainer.probability i j| ≤ 1
    rw [abs_of_nonneg (smallNoiseAttainer.probability_nonneg i j)]
    exact smallNoiseAttainer.probability_le_one i j
  · exact noisySelected_error

/-- Both noise sources are strictly nonzero, and the actual noisy table still
requires and attains physical retained Hilbert dimension three. -/
theorem noisySelected_minimum_dimension :
    IsLeast {d : ℕ | ∃ C : CommonCut (Fin d) Unit Setting Setting 2,
      C.probability = noisySelected} 3 := by
  constructor
  · exact ⟨smallNoiseAttainer, rfl⟩
  · rintro d ⟨C,hC⟩
    have hd := C.dimension_ge_three (by rw [hC]; exact ne_of_gt noisySelected_positive_det)
    simpa using hd

theorem small_noise_margin :
    (0 : ℝ) < 1 / 10000000 ∧ (7 / 180000000 : ℝ) < 1 / 1000000 := by norm_num

def featureBasis : Module.Basis Setting ℂ FeatureSpace :=
  (Pi.basisFun ℂ Setting).map coefficientEquiv

theorem featureBasis_apply (i : Setting) :
    featureBasis i = FinitePositiveKernel.feature kernel kernel_positive i := by
  change coefficientEquiv ((Pi.basisFun ℂ Setting) i) = _
  rw [Pi.basisFun_apply]
  rfl

theorem features_independent :
    LinearIndependent ℂ (FinitePositiveKernel.feature kernel kernel_positive) := by
  have h : (fun i => featureBasis i) = FinitePositiveKernel.feature kernel kernel_positive :=
    funext featureBasis_apply
  rw [← h]
  exact featureBasis.linearIndependent

theorem operatorMap_single (i : Setting) :
    operatorMap (Pi.single i 1) = operatorEmbedding (projector i) := by
  simp [operatorMap, operatorCombination, Pi.single_apply]

/-- The target is exactly the complex span of the five physical operators in
their weighted Hilbert-Schmidt representation. -/
theorem operator_range_eq_span : operatorMap.range =
    Submodule.span ℂ (Set.range (fun i => operatorEmbedding (projector i))) := by
  apply le_antisymm
  · rintro x ⟨c,rfl⟩
    change operatorEmbedding (∑ i, c i • projector i) ∈ _
    rw [map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨Pi.single i 1, operatorMap_single i⟩

theorem reconstruction_feature (i : Setting) :
    (reconstruction (FinitePositiveKernel.feature kernel kernel_positive i) :
      EuclideanSpace ℂ (Q × Q)) = operatorEmbedding (projector i) := by
  change operatorMap (coefficientEquiv.symm (coefficientEquiv (Pi.single i 1))) = _
  rw [coefficientEquiv.symm_apply_apply, operatorMap_single]

/-- The existing feature-sum theorem gives a concrete operator expansion for
every reconstructed vector. -/
theorem reconstruction_spanning (x : OperatorSpace) :
    ∃ c : Setting → ℂ, (x : EuclideanSpace ℂ (Q × Q)) =
      ∑ i, c i • operatorEmbedding (projector i) := by
  obtain ⟨c,hc⟩ := FinitePositiveKernel.exists_feature_sum kernel kernel_positive
    (reconstruction.symm x)
  refine ⟨c, ?_⟩
  have h := congrArg (fun z => (reconstruction z : EuclideanSpace ℂ (Q × Q))) hc
  simpa only [reconstruction.apply_symm_apply, map_sum, map_smul,
    Submodule.coe_sum, Submodule.coe_smul, reconstruction_feature] using h

/-- The algebraic null-space quotient has the same isometric reconstruction
after its existing linear identification with the separation quotient. -/
def algebraicReconstruction :
    (FinitePositiveKernel.Coefficients kernel_positive ⧸
      FinitePositiveKernel.nullSpace kernel kernel_positive) ≃ₗ[ℂ] OperatorSpace :=
  (FinitePositiveKernel.quotientEquiv kernel kernel_positive).trans reconstruction.toLinearEquiv

theorem nearby_physical_lower_bound {S E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E] {o : ℕ} (C : CommonCut S E Setting Setting o)
    {δ : ℝ} (hδ : 0 ≤ δ) (hr : δ < 1 / 583200)
    (he : ∀ i j, |C.probability i j - selected i j| ≤ δ) :
    3 ≤ Fintype.card (S × E) := by
  apply C.dimension_ge_three
  apply ne_of_gt
  apply nearby_selected_positive_det C.probability hδ hr _ he
  intro i j
  rw [abs_of_nonneg (C.probability_nonneg i j)]
  exact C.probability_le_one i j

/-- Independent observed error and model-fit error add deterministically. -/
theorem observation_fit_lower_bound {S E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E] {o : ℕ} (C : CommonCut S E Setting Setting o)
    (O : Matrix Setting Setting ℝ) {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : η + ε < 1 / 583200) (hO : ∀ i j, |O i j - selected i j| ≤ η)
    (hfit : ∀ i j, |C.probability i j - O i j| ≤ ε) :
    3 ≤ Fintype.card (S × E) := by
  apply nearby_physical_lower_bound C (add_nonneg hη hε) hr
  intro i j
  calc
    _ ≤ |C.probability i j - O i j| + |O i j - selected i j| := abs_sub_le _ _ _
    _ ≤ ε + η := add_le_add (hfit i j) (hO i j)
    _ = η + ε := add_comm _ _

/-- The entry-size hypothesis follows even for estimates with negative entries. -/
theorem estimate_abs_bound (O : Matrix Setting Setting ℝ) {δ : ℝ} (hr : δ ≤ 2 / 3)
    (he : ∀ i j, |O i j - selected i j| ≤ δ) : ∀ i j, |O i j| ≤ 1 := by
  intro i j
  calc
    |O i j| ≤ |O i j - selected i j| + |selected i j| := by
      simpa using abs_sub_le (O i j) (selected i j) 0
    _ ≤ δ + 1 / 3 := add_le_add (he i j)
      (by rw [abs_of_nonneg (selected_nonneg i j)]; exact selected_le_third i j)
    _ ≤ 1 := by linarith

def wordAppendHistory : (u v : List Setting) → History 2 u.length → History 2 v.length →
    History 2 (u ++ v).length
  | [], _, _, g => g
  | _ :: u, v, (a,h), g => (a, wordAppendHistory u v h g)

theorem word_run_concatenation {E : Type*} [Fintype E] [DecidableEq E]
    (u v : List Setting) (h : History 2 u.length) (g : History 2 v.length)
    (X : Matrix (Q × E) (Q × E) ℂ) :
    run Q E 2 (wordTree E (u ++ v)) (wordAppendHistory u v h g) X =
      run Q E 2 (wordTree E v) g (run Q E 2 (wordTree E u) h X) := by
  induction u generalizing X with
  | nil => rfl
  | cons j u ih =>
    rcases h with ⟨a,h⟩
    exact ih h ((localStep Q E 2 (readout j)).branch Q E 2 a X)

/-- Concatenated controlled words agree with the substrate's actual append run. -/
theorem word_append_coherence {E : Type*} [Fintype E] [DecidableEq E]
    (u v : List Setting) (h : History 2 u.length) (g : History 2 v.length)
    (X : Matrix (Q × E) (Q × E) ℂ) :
    run Q E 2 (wordTree E (u ++ v)) (wordAppendHistory u v h g) X =
      run Q E 2 (appendTree (wordTree E u) (fun _ => wordTree E v))
        (appendHistory h g) X := by
  rw [word_run_concatenation, append_run]

theorem selected_symmetric (i j : Setting) : selected i j = selected j i := by
  rw [selected_trace, selected_trace, Matrix.trace_mul_comm]

def duplicateIndex (i : Setting) : Setting := if i = 4 then 3 else i
def duplicateTable : Matrix Setting Setting ℝ := selected.submatrix duplicateIndex duplicateIndex

theorem duplicate_det_zero : duplicateTable.det = 0 := by
  apply Matrix.det_zero_of_row_eq (i := (3 : Setting)) (j := (4 : Setting)) (by decide)
  funext j
  simp [duplicateTable, duplicateIndex]

/-- Noncommutation survives the duplicate control, while its determinant vanishes. -/
theorem projector_zero_three_noncommuting : projector 0 * projector 3 ≠ projector 3 * projector 0 := by
  intro h
  have hp0 : projector 0 = !![1,0,0; 0,0,0; 0,0,0] := rfl
  have hp3 : projector 3 = !![1/2,1/2,0; 1/2,1/2,0; 0,0,0] := rfl
  have he := congrArg (fun M : Mat => M 0 1) h
  norm_num [hp0, hp3, Matrix.mul_apply, Fin.sum_univ_succ] at he

/-- The scalar spoof selects a different suffix using a free prefix label.
Its arithmetic is valid, but the corresponding dimension-one common-cut model
is excluded by the derived bound below. -/
theorem scalar_prefix_label_spoof (i j : Setting) :
    0 ≤ 3 * selected i j ∧ 3 * selected i j ≤ 1 ∧
      (1 / 3) * (3 * selected i j) = selected i j := by
  have h0 := selected_nonneg i j
  have h1 := selected_le_third i j
  constructor
  · positivity
  constructor
  · linarith
  · ring

theorem no_scalar_common_cut {o : ℕ} (C : CommonCut Unit Unit Setting Setting o) :
    C.probability ≠ selected := by
  intro h
  have hd := selected_physical_lower_bound C h
  norm_num at hd

/-- Storing a command label already costs five classical dimensions; retaining
the first outcome as well costs ten. These are retained Hilbert carriers. -/
theorem spoof_record_accounting :
    Fintype.card (Setting × Unit) = 5 ∧ Fintype.card (Setting × Fin 2) = 10 := by decide

theorem retained_record_dimension {C R : Type*} [Fintype C] [Fintype R] :
    Fintype.card (C × R) = Fintype.card C * Fintype.card R := Fintype.card_prod _ _

theorem retained_block_dimension {C : Type*} [Fintype C] (R : C → Type*)
    [∀ c, Fintype (R c)] : Fintype.card (Sigma R) = ∑ c, Fintype.card (R c) :=
  Fintype.card_sigma

theorem full_reset_table (i j : Setting) :
    (noisyAttainer 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).probability i j =
      1 / 9 := by rw [noisyAttainer_probability]; norm_num

def resetTable : Matrix Setting Setting ℝ :=
  (noisyAttainer 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).probability

theorem resetTable_rank : resetTable.rank = 1 := by
  let A : Matrix Setting Unit ℝ := fun _ _ => 1 / 9
  let B : Matrix Unit Setting ℝ := fun _ _ => 1
  have hAB : resetTable = A * B := by
    ext i j
    simp [resetTable, full_reset_table, A, B, Matrix.mul_apply]
  have hu : resetTable.rank ≤ 1 := by
    rw [hAB]
    exact (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_card_width A)
  let R := resetTable.submatrix (fun _ : Unit => (0 : Setting)) (fun _ : Unit => (0 : Setting))
  have hr : IsUnit R := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (by simp [R, resetTable, Matrix.det_unique, full_reset_table]))
  have hl := Matrix.rank_submatrix_le resetTable (fun _ : Unit => (0 : Setting))
    (fun _ : Unit => (0 : Setting))
  have hR := Matrix.rank_of_isUnit R hr
  change R.rank ≤ resetTable.rank at hl
  rw [hR] at hl
  exact Nat.le_antisymm hu hl

/-- At the coarse strict-radius boundary the deterministic lower bound is zero. -/
theorem strict_radius_boundary : (1 / 972 : ℝ) - 600 * (1 / 583200) = 0 := by norm_num

theorem negative_determinant_invertible (M : Matrix Setting Setting ℝ) (h : M.det < 0) :
    M.rank = 5 := by
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (ne_of_lt h))
  exact Matrix.rank_of_isUnit M hu

theorem rank_three_square_bound (d : ℕ) (h : 3 ≤ d ^ 2) : 2 ≤ d := by
  by_contra hn
  have hd : d ≤ 1 := by omega
  interval_cases d <;> norm_num at h

/-- The earlier attained real three-coordinate realization passes the square
bound at physical dimension two. This arithmetic neither constructs a qubit
realization nor supplies a stronger positivity constraint. -/
theorem earlier_linear_model_square_control :
    Module.finrank ℝ (Fin 3 → ℝ) ≤ (2 : ℕ) ^ 2 ∧
      ¬ Module.finrank ℝ (Fin 3 → ℝ) ≤ (1 : ℕ) ^ 2 := by
  rw [FiniteThreeLevelAppendedMemoryExamples.attained_dimension_three]
  norm_num

theorem noisyReadout_first_operator (i : Setting) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (a : Fin 2) :
    (noisyReadout i t ht ht1).operators a (Fin.castAdd 1 (0 : Fin 1)) =
      Real.sqrt (1-t) • outcomeOperator i a := by
  change mixKraus (fun _ : Fin 1 => outcomeOperator i a)
    (fun _ : Fin 1 => Real.sqrt (1 / 2) • (1 : Mat)) t (Fin.castAdd 1 (0 : Fin 1)) = _
  rw [mixKraus, Fin.addCases_left]

theorem noisyReadout_second_operator (i : Setting) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (a : Fin 2) :
    (noisyReadout i t ht ht1).operators a (Fin.natAdd 1 (0 : Fin 1)) =
      Real.sqrt (t / 2) • (1 : Mat) := by
  change mixKraus (fun _ : Fin 1 => outcomeOperator i a)
    (fun _ : Fin 1 => Real.sqrt (1 / 2) • (1 : Mat)) t (Fin.natAdd 1 (0 : Fin 1)) = _
  rw [mixKraus, Fin.addCases_right, smul_smul]
  congr 1
  rw [← Real.sqrt_mul ht]
  congr 1
  ring

theorem noisySelected_exact_max_error :
    (∀ i j, |noisySelected i j - selected i j| ≤ 5833333 / 150000000000000) ∧
      |noisySelected 0 0 - selected 0 0| = 5833333 / 150000000000000 := by
  have htable (i j : Setting) : selected i j = (1 / 12 : ℝ) * integerTable i j := by
    exact congrArg (fun M : Matrix Setting Setting ℝ => M i j) selected_eq
  have hn (i j : Setting) : noisySelected i j =
      (1-(1 / 10000000 : ℝ)) * ((1-1 / 10000000)*selected i j + (1 / 10000000)/9) +
        (1 / 10000000)/6 := noisyAttainer_probability _ _ _ _ _ _ i j
  constructor
  · intro i j
    rw [hn, htable]
    fin_cases i <;> fin_cases j <;> norm_num [integerTable]
  · rw [hn, htable]
    norm_num [integerTable]

def negativeEstimate : Matrix Setting Setting ℝ := fun i j =>
  if i = 0 ∧ j = 1 then -1 / 1000000 else selected i j

theorem negativeEstimate_error (i j : Setting) :
    |negativeEstimate i j - selected i j| ≤ 1 / 1000000 := by
  unfold negativeEstimate
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩
    rw [selected_trace]
    norm_num [projector, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp

theorem negativeEstimate_positive_det : 0 < negativeEstimate.det := by
  apply nearby_selected_positive_det negativeEstimate (by norm_num)
    (by norm_num : (1 / 1000000 : ℝ) < 1 / 583200)
  · exact estimate_abs_bound negativeEstimate (by norm_num) negativeEstimate_error
  · exact negativeEstimate_error

/-- A nearby invertible estimate with a negative entry cannot be an actual
probability minor. The deterministic exclusion makes no attainability claim. -/
theorem negativeEstimate_not_physical {S E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E] {o : ℕ} (C : CommonCut S E Setting Setting o) :
    C.probability ≠ negativeEstimate := by
  intro h
  have hp := C.probability_nonneg 0 1
  rw [h] at hp
  norm_num [negativeEstimate] at hp

theorem no_qubit_common_cut {o : ℕ} (C : CommonCut (Fin 2) Unit Setting Setting o) :
    C.probability ≠ selected := by
  intro h
  have hd := selected_physical_lower_bound C h
  norm_num at hd

/-- An empty suffix is the identity branch, including zero prefix states. -/
theorem empty_suffix_retains_prefix {S E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E] {o n : ℕ} (T : Tree S E o n) (h : History o n)
    (X : Matrix (S × E) (S × E) ℂ) :
    run S E o (appendTree T (fun _ => (.done : Tree S E o 0)))
      (appendHistory h ()) X = run S E o T h X := by
  rw [append_run]
  rfl

theorem impossible_pair_zero :
    run Q Unit 2 (wordTree Unit [0,1]) (0,0,()) (joint rho) = 0 := by
  rw [joint, word_product_input]
  have hprod : systemProduct [0,1] (0,0,()) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [systemProduct, outcomeOperator, projector, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hprod, Matrix.zero_mul, Matrix.zero_mul]
  simp

/-- Joint eigenvectors of commuting Hermitian maps bound the dimension of
their entire complex operator span, not merely the chosen Gram fixture. -/
theorem commuting_symmetric_span_bound {I : Type*}
    (T : I → Module.End ℂ (EuclideanSpace ℂ Q))
    (hsym : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Function.onFun Commute T)) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range T)) ≤ 3 := by
  classical
  let s : Set (EuclideanSpace ℂ Q) :=
    ⋃ χ : I → ℂ, ((⨅ i, (T i).eigenspace (χ i)) : Submodule ℂ (EuclideanSpace ℂ Q))
  have hs : ⊤ ≤ Submodule.span ℂ s := by
    dsimp only [s]
    rw [Submodule.span_iUnion]
    simp_rw [Submodule.span_eq]
    rw [LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm]
  obtain ⟨β,b,hb⟩ : ∃ (β : Type) (b : Module.Basis β ℂ (EuclideanSpace ℂ Q)),
      Set.range b ⊆ s := ⟨_, Module.Basis.ofSpan hs, Module.Basis.ofSpan_subset hs⟩
  letI : Fintype β := FiniteDimensional.fintypeBasisIndex b
  have heigen (j : β) : ∃ χ : I → ℂ, ∀ i, T i (b j) = χ i • b j := by
    obtain ⟨χ,hχ⟩ := Set.mem_iUnion.mp (hb ⟨j,rfl⟩)
    refine ⟨χ, fun i => Module.End.mem_eigenspace_iff.mp ?_⟩
    exact (iInf_le (fun k => (T k).eigenspace (χ k)) i) hχ
  have hdiag (A : Module.End ℂ (EuclideanSpace ℂ Q))
      (hA : A ∈ Submodule.span ℂ (Set.range T)) :
      ∀ i j : β, i ≠ j → (b.repr (A (b j))) i = 0 := by
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨k,rfl⟩ := hA
      intro i j hij
      obtain ⟨χ,hχ⟩ := heigen j
      rw [hχ k, map_smul, b.repr_self]
      simp [hij]
    | zero => simp
    | add A B hA hB ihA ihB =>
      intro i j hij
      simp [ihA i j hij, ihB i j hij]
    | smul c A hA ih =>
      intro i j hij
      simp [ih i j hij]
  let D : Submodule.span ℂ (Set.range T) →ₗ[ℂ] (β → ℂ) :=
    { toFun A j := (b.repr (A.val (b j))) j
      map_add' A B := by ext j; simp
      map_smul' c A := by ext j; simp }
  have hinj : Function.Injective D := by
    intro A B hAB
    apply Subtype.ext
    apply b.ext
    intro j
    apply b.ext_elem
    intro i
    by_cases hij : i = j
    · subst i
      exact congrFun hAB j
    · rw [hdiag A A.property i j hij, hdiag B B.property i j hij]
  calc
    _ ≤ Module.finrank ℂ (β → ℂ) := LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card β := Module.finrank_pi ℂ
    _ = 3 := by rw [← Module.finrank_eq_card_basis b]; simp

/-- In particular, every commuting family of qutrit Hermitian projectors has
complex operator span at most three. The stronger statement needs only
Hermiticity and commutation, not idempotence. -/
theorem commuting_hermitian_span_bound {I : Type*} (P : I → Mat)
    (hsym : ∀ i, (P i).IsHermitian) (hcomm : ∀ i j, P i * P j = P j * P i) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range P)) ≤ 3 := by
  let T : I → Module.End ℂ (EuclideanSpace ℂ Q) := fun i => Matrix.toEuclideanLin (P i)
  have ht : ∀ i, (T i).IsSymmetric := fun i => Matrix.isSymmetric_toEuclideanLin_iff.mpr (hsym i)
  have hc : Pairwise (Function.onFun Commute T) := by
    intro i j _
    change (Matrix.toLpLin 2 2 (P i)).comp (Matrix.toLpLin 2 2 (P j)) =
      (Matrix.toLpLin 2 2 (P j)).comp (Matrix.toLpLin 2 2 (P i))
    rw [← Matrix.toLpLin_mul, ← Matrix.toLpLin_mul, hcomm i j]
  have hmap : (Submodule.span ℂ (Set.range P)).map
      Matrix.toEuclideanLin.toLinearMap = Submodule.span ℂ (Set.range T) := by
    rw [Submodule.map_span]
    congr 1
    ext A
    constructor
    · rintro ⟨B, ⟨i,rfl⟩, rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨P i, ⟨i,rfl⟩, rfl⟩
  have hd := commuting_symmetric_span_bound T ht hc
  rw [← hmap, Matrix.toEuclideanLin.finrank_map_eq] at hd
  exact hd

/-- A normalized spectator leaves all four outcome weights unchanged. The
separate all-input positivity theorem includes correlated joint inputs. -/
theorem spectator_pair_weights {E : Type*} [Fintype E] [DecidableEq E]
    {σ : Matrix E E ℂ} (hσ : IsDensityOperator σ) (i j : Setting) (a b : Fin 2) :
    weight Q E 2 (wordTree E [j,i]) (a,b,()) (rho ⊗ₖ σ) =
      if a = 0 then (if b = 0 then selected i j else 1 / 3 - selected i j)
      else (if b = 0 then 1 / 3 - selected i j else 1 / 3 + selected i j) := by
  rw [word_product_weight E _ _ _ hσ.2]
  rw [← word_product_weight Unit [j,i] (a,b,()) rho
    (σ := (1 : Matrix Unit Unit ℂ)) (by simp [Matrix.trace])]
  exact pair_all_outcomes i j a b

theorem spectator_initial_density {E : Type*} [Fintype E] [DecidableEq E]
    {σ : Matrix E E ℂ} (hσ : IsDensityOperator σ) : IsDensityOperator (rho ⊗ₖ σ) := by
  constructor
  · exact rho_density.1.kronecker hσ.1
  · rw [Matrix.trace_kronecker, rho_density.2, hσ.2, mul_one]

theorem attainer_suffixFunctional (i : Setting) (X : Mat) :
    attainer.suffixFunctional i (joint X) = (projector i * X).trace := by
  change (run Q Unit 2 (wordTree Unit [i]) (0,()) (joint X)).trace = _
  rw [joint, word_product_input, Matrix.trace_kronecker]
  simp only [systemProduct, outcomeOperator, ite_true, Matrix.one_mul,
    (projector_hermitian i).eq]
  rw [Matrix.trace_mul_cycle, projector_idempotent]
  simp [Matrix.trace]

/-- Each commanded pair has four normalized outcomes, including zero histories. -/
theorem pair_total_one (i j : Setting) :
    (∑ h, weight Q Unit 2 (wordTree Unit [j,i]) h (joint rho)) = 1 :=
  (word_normalized Unit [j,i] attainer.density).2

/-- The selected entries are twenty-five controlled experiments, not a
normalized twenty-five-outcome measurement. -/
theorem selected_entries_total : (∑ i, ∑ j, selected i j) = 19 / 6 := by
  rw [selected_eq]
  norm_num [integerTable, Matrix.smul_apply, Fin.sum_univ_succ]

theorem empty_word_returns_input {E : Type*} [Fintype E] [DecidableEq E]
    (X : Matrix (Q × E) (Q × E) ℂ) :
    run Q E 2 (wordTree E []) () X = X := rfl

end SKEFTHawking.QuantumNetwork.FiniteQutritPhysicalMemoryExamples
