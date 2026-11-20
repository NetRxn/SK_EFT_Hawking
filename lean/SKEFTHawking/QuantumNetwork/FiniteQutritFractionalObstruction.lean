import SKEFTHawking.QuantumNetwork.FiniteQutritEuclideanTransfer

/-!
# The fractional feature interpolation fails the inherited physical cone

The negative entry is a fractional feature readout. Integer ten-record Kraus
experiments remain normalized and positive, as proved in the preceding module.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritFractionalObstruction
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteQutritPhysicalMemory FiniteQutritInvariantCarrier
open FiniteQutritInvariantReconstruction FiniteQutritAveragedTransfer
open FiniteQutritAveragedMixing FiniteQutritEuclideanTransfer
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace
open scoped Matrix.Norms.L2Operator MatrixOrder

private theorem vec6_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

def theta : ℝ := 1/3-Real.sqrt (9/10)/2+Real.sqrt (7/10)/6

theorem sqrt_nine_tenths_lower : (4743/5000 : ℝ) < Real.sqrt (9/10) := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9/10)
  have hp := Real.sqrt_nonneg (9/10 : ℝ)
  nlinarith

theorem sqrt_seven_tenths_upper : Real.sqrt (7/10) < (837/1000 : ℝ) := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7/10)
  have hp := Real.sqrt_nonneg (7/10 : ℝ)
  nlinarith

theorem theta_strict : theta < (-11/7500 : ℝ) := by
  unfold theta
  linarith [sqrt_nine_tenths_lower, sqrt_seven_tenths_upper]

theorem half_weight (i : Index) :
    Real.exp ((1/2 : ℝ)*Real.log (eigenvalue i)) = Real.sqrt (eigenvalue i) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (eigenvalue_pos i)]
  congr 1
  ring

theorem physical_input : feature 1 ∈ density := by
  constructor
  · change (U (feature 1) : Mat).PosSemidef
    rw [U_feature]
    change (projector 1).PosSemidef
    simpa only [(projector_hermitian 1).eq, projector_idempotent] using
      Matrix.posSemidef_conjTranspose_mul_self (projector 1)
  · change (U (feature 1) : Mat).trace = 1
    rw [U_feature]
    exact projector_trace 1

theorem input_expansion :
    effect 1 = (1/3 : ℂ) • eigenvector 0 + (1/2 : ℂ) • eigenvector 1 +
      (1/6 : ℂ) • eigenvector 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [effect, projector, eigenvector, eigenCoordinates, symmetricMatrix,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem half_entry : (U (E (1/2) (feature 1)) : Mat) 2 2 = (theta : ℂ) := by
  rw [E, U_spectral, U_feature]
  simp_rw [half_weight]
  norm_num [synthesis, coefficients, effect, projector, eigenvector,
    eigenCoordinates, symmetricMatrix, Fin.sum_univ_succ, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, vec6_last, smul_eq_mul, theta, eigenvalue]
  ring

theorem half_not_physical : E (1/2) (feature 1) ∉ cone := by
  intro h
  have hd := h.diag_nonneg (i := 2)
  rw [half_entry] at hd
  have hr := (Complex.le_def.mp hd).1
  have hn := theta_strict
  norm_num at hr
  linarith

theorem half_trace_one : FiniteQutritInvariantReconstruction.trace
    (E (1/2) (feature 1)) = 1 := (E_trace _ _).trans physical_input.2

theorem no_positive_extension :
    ¬ ∃ Φ : Mat →ₗ[ℂ] Mat,
      (∀ X : Mat, X.PosSemidef → (Φ X).PosSemidef) ∧
      (∀ q : FeatureSpace, Φ (U q) = (U (E (1/2) q) : Mat)) := by
  rintro ⟨Φ,hpos,hagree⟩
  apply half_not_physical
  change (U (E (1/2) (feature 1)) : Mat).PosSemidef
  rw [← hagree]
  exact hpos _ physical_input.1

theorem quarter_entry :
    temporalKernel (1/4,feature 2) (1/4,feature 1) = ((theta/3 : ℝ) : ℂ) := by
  change ⟪feature 2,E ((1/4 : ℝ)+1/4) (feature 1)⟫_ℂ = _
  rw [show (1/4 : ℝ)+1/4=1/2 by norm_num, ← U_inner, U_feature,
    (effect_hermitian 2).eq]
  have he (X : Mat) : (effect 2 * X).trace = X 2 2 := by
    simp [effect, projector, Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three]
  rw [he, half_entry]
  push_cast
  rfl

theorem fractional_readout_negative :
    (temporalKernel (1/4,feature 2) (1/4,feature 1)).re < (-11/22500 : ℝ) := by
  rw [quarter_entry, Complex.ofReal_re]
  linarith [theta_strict]

theorem actual_fractional_labels :
    prefixWord 1 = [1,1] ∧ prefixHistory 1 = (0,0,()) ∧
    suffixWord 2 = [2,2] ∧ suffixHistory 2 = (0,0,()) :=
  ⟨rfl,rfl,rfl,rfl⟩

def diagonalEntry : ℝ := 1/9+Real.sqrt (9/10)/6+Real.sqrt (7/10)/18

theorem quarter_diagonal (i : Index) (hi : i=1 ∨ i=2) :
    temporalKernel (1/4,feature i) (1/4,feature i) = (diagonalEntry : ℂ) := by
  change ⟪feature i,E ((1/4 : ℝ)+1/4) (feature i)⟫_ℂ = _
  rw [show (1/4 : ℝ)+1/4=1/2 by norm_num, ← U_inner, U_feature,
    (effect_hermitian i).eq, E, U_spectral, U_feature]
  simp_rw [half_weight]
  rcases hi with rfl | rfl
  all_goals
    norm_num [synthesis, coefficients, effect, projector, eigenvector, eigenCoordinates,
      symmetricMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last,
      smul_eq_mul, diagonalEntry, eigenvalue]
    ring

def twoLabels : Fin 2 → ℝ × FeatureSpace := ![(1/4,feature 1),(1/4,feature 2)]
def twoGram : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => temporalKernel (twoLabels i) (twoLabels j)

theorem twoGram_form : twoGram =
    !![(diagonalEntry : ℂ),(theta/3 : ℝ); (theta/3 : ℝ),(diagonalEntry : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact quarter_diagonal 1 (Or.inl rfl)
  · change temporalKernel (1/4,feature 1) (1/4,feature 2) = _
    rw [← temporal_hermitian, quarter_entry]
    simp
  · exact quarter_entry
  · exact quarter_diagonal 2 (Or.inr rfl)

def smallEigenvalue : ℝ := Real.sqrt (9/10)/3
def largeEigenvalue : ℝ := 2/9+Real.sqrt (7/10)/9
def twoEigenvectors : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;-1,1]

theorem twoEigenvectors_det : twoEigenvectors.det = 2 := by
  norm_num [twoEigenvectors, Matrix.det_fin_two]

theorem twoGram_eigenbasis : twoGram * twoEigenvectors =
    twoEigenvectors * Matrix.diagonal ![(smallEigenvalue : ℂ),(largeEigenvalue : ℂ)] := by
  rw [twoGram_form]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, twoEigenvectors,
      Matrix.diagonal_apply, diagonalEntry, theta, smallEigenvalue, largeEigenvalue] <;> ring

theorem two_eigenvalues_positive : 0 < smallEigenvalue ∧ 0 < largeEigenvalue := by
  constructor
  · exact div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)
  · unfold largeEigenvalue
    positivity

theorem twoGram_det : twoGram.det = ((smallEigenvalue*largeEigenvalue : ℝ) : ℂ) := by
  rw [twoGram_form, Matrix.det_fin_two]
  simp [diagonalEntry, theta, smallEigenvalue, largeEigenvalue]
  ring

theorem twoGram_positive_definite : twoGram.PosDef := by
  have hp : twoGram.PosSemidef := temporal_psd twoLabels
  apply hp.posDef_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [twoGram_det]
  exact_mod_cast (mul_pos two_eigenvalues_positive.1 two_eigenvalues_positive.2).ne'

def basisVector (i : Index) : FeatureSpace := J (WithLp.toLp 2 (Pi.single i 1))

theorem basis_coordinates (i k : Index) : J.symm (basisVector i) k = if k=i then 1 else 0 := by
  simp [basisVector, eq_comm]

theorem basis_inner (i j : Index) : ⟪basisVector i,basisVector j⟫_ℂ = if i=j then 1 else 0 := by
  rw [basisVector, basisVector, J.inner_map_map, PiLp.inner_apply]
  simp [RCLike.inner_apply, Pi.single_apply]

theorem basis_expansion (q : FeatureSpace) : q = ∑ i, J.symm q i • basisVector i := by
  apply J.symm.injective
  ext k
  simp [map_sum, map_smul, basisVector, Pi.single_apply, mul_ite]

theorem spectral_basis (a : Index → ℂ) (i : Index) : spectral a (basisVector i) = a i • basisVector i := by
  apply J.symm.injective
  ext k
  simp only [coordinates_spectral, map_smul, PiLp.smul_apply, smul_eq_mul, basis_coordinates]
  by_cases hk : k=i
  · subst k; simp
  · simp [hk]

theorem transfer_coordinates (q : FeatureSpace) (i : Index) :
    J.symm (quotientTransfer q) i = (eigenvalue i : ℂ) * J.symm q i := by
  rw [← E_one, E, coordinates_spectral, one_mul, Real.exp_log (eigenvalue_pos i)]

theorem transfer_basis (i : Index) :
    quotientTransfer (basisVector i) = (eigenvalue i : ℂ) • basisVector i := by
  rw [← E_one, E, spectral_basis, one_mul, Real.exp_log (eigenvalue_pos i)]

theorem eigenvalue_injective : Function.Injective eigenvalue := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [eigenvalue,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last] at h

/-- Every eigenspace of the actual quotient transfer is its derived single line. -/
theorem simple_eigenspace (i : Index) (q : FeatureSpace)
    (hq : quotientTransfer q = (eigenvalue i : ℂ) • q) :
    q = J.symm q i • basisVector i := by
  apply J.symm.injective
  ext k
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul, basis_coordinates]
  by_cases hk : k=i
  · subst k; simp
  · simp only [if_neg hk, mul_zero]
    have h := congrArg (fun v => J.symm v k) hq
    rw [transfer_coordinates, map_smul] at h
    change (eigenvalue k : ℂ) * J.symm q k = (eigenvalue i : ℂ) * J.symm q k at h
    have hn : (eigenvalue k : ℂ) ≠ (eigenvalue i : ℂ) := by
      intro he
      exact hk (eigenvalue_injective (Complex.ofReal_injective he))
    exact (mul_eq_mul_right_iff.mp h).resolve_left hn

theorem root_commutes (R : FeatureSpace →ₗ[ℂ] FeatureSpace)
    (hR : R.comp R = quotientTransfer) (q : FeatureSpace) :
    R (quotientTransfer q) = quotientTransfer (R q) := by
  have h (v : FeatureSpace) : R (R v) = quotientTransfer v := congrArg (fun L => L v) hR
  rw [← h q, h (R q)]

theorem root_basis (R : FeatureSpace →ₗ[ℂ] FeatureSpace)
    (hR : R.comp R = quotientTransfer) (i : Index) :
    R (basisVector i) = J.symm (R (basisVector i)) i • basisVector i := by
  apply simple_eigenspace
  rw [← root_commutes R hR, transfer_basis, map_smul]

/-- The Hilbert-positive self-adjoint root is forced on each of the six actual
simple eigenspaces, including the stationary scalar. -/
theorem positive_root_basis (R : FeatureSpace →ₗ[ℂ] FeatureSpace)
    (hR : R.comp R = quotientTransfer) (hs : R.IsSymmetric)
    (hp : ∀ q : FeatureSpace, 0 ≤ (⟪q,R q⟫_ℂ).re) (i : Index) :
    R (basisVector i) = (Real.sqrt (eigenvalue i) : ℂ) • basisVector i := by
  let z : ℂ := J.symm (R (basisVector i)) i
  have hd : R (basisVector i) = z • basisVector i := root_basis R hR i
  have hstar := hs (basisVector i) (basisVector i)
  rw [hd, inner_smul_left, inner_smul_right, basis_inner, if_pos rfl,
    mul_one, mul_one] at hstar
  have him : z.im = 0 := by
    have h := congrArg Complex.im hstar
    simp only [Complex.conj_im] at h
    linarith
  have hpos := hp (basisVector i)
  rw [hd, inner_smul_right, basis_inner, if_pos rfl, mul_one] at hpos
  have hsq : z*z = (eigenvalue i : ℂ) := by
    have h := congrArg (fun L => J.symm (L (basisVector i)) i) hR
    change J.symm (R (R (basisVector i))) i = J.symm (quotientTransfer (basisVector i)) i at h
    rw [hd, map_smul, hd, map_smul, map_smul, transfer_basis, map_smul] at h
    simpa [basis_coordinates] using h
  have hre : z.re = Real.sqrt (eigenvalue i) := by
    have h := congrArg Complex.re hsq
    simp only [Complex.mul_re, Complex.ofReal_re, him, mul_zero, sub_zero] at h
    have hr := Real.sq_sqrt (eigenvalue_pos i).le
    nlinarith [Real.sqrt_nonneg (eigenvalue i)]
  have hz : z = (Real.sqrt (eigenvalue i) : ℂ) := by
    apply Complex.ext
    · exact hre
    · simpa only [Complex.ofReal_im] using him
  rw [hd, hz]

theorem positive_root_unique (R : FeatureSpace →ₗ[ℂ] FeatureSpace)
    (hR : R.comp R = quotientTransfer) (hs : R.IsSymmetric)
    (hp : ∀ q : FeatureSpace, 0 ≤ (⟪q,R q⟫_ℂ).re) : R = E (1/2) := by
  ext q
  rw [basis_expansion q]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [positive_root_basis R hR hs hp, E, spectral_basis, half_weight]

theorem no_physical_positive_root :
    ¬ ∃ R : FeatureSpace →ₗ[ℂ] FeatureSpace,
      R.comp R = quotientTransfer ∧ R.IsSymmetric ∧
      (∀ q : FeatureSpace, 0 ≤ (⟪q,R q⟫_ℂ).re) ∧
      (∀ q : FeatureSpace, q ∈ cone → R q ∈ cone) := by
  rintro ⟨R,hsq,hs,hp,hcone⟩
  have h := positive_root_unique R hsq hs hp
  subst R
  exact half_not_physical (hcone _ physical_input.1)

def physicalAmplification (Phi : Mat →ₗ[ℂ] Mat) (n : ℕ)
    (X : Matrix (Q × Fin n) (Q × Fin n) ℂ) : Matrix (Q × Fin n) (Q × Fin n) ℂ :=
  fun u v => Phi (FiniteQutritInvariantExamples.block (Fin n) u.2 v.2 X) u.1 v.1

/-- Positivity of every finite spectator amplification, in the actual physical
matrix order. This is distinct from Hilbert positivity on F. -/
def PhysicalCompletelyPositive (Phi : Mat →ₗ[ℂ] Mat) : Prop :=
  ∀ n : ℕ, ∀ X : Matrix (Q × Fin n) (Q × Fin n) ℂ,
    X.PosSemidef → (physicalAmplification Phi n X).PosSemidef

theorem physical_CP_positive (Phi : Mat →ₗ[ℂ] Mat) (hPhi : PhysicalCompletelyPositive Phi)
    (X : Mat) (hX : X.PosSemidef) : (Phi X).PosSemidef := by
  have hI : (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef :=
    by simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Matrix (Fin 1) (Fin 1) ℂ)
  have h := (hPhi 1 (X ⊗ₖ 1) (hX.kronecker hI)).submatrix (fun a : Q => (a,0))
  have hb : FiniteQutritInvariantExamples.block (Fin 1) 0 0 (X ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)) = X := by
    ext a b
    simp [FiniteQutritInvariantExamples.block]
  convert h using 1
  ext a b
  change Phi X a b = Phi (FiniteQutritInvariantExamples.block (Fin 1) 0 0 (X ⊗ₖ 1)) a b
  rw [hb]

theorem no_CP_extension :
    ¬ ∃ Phi : Mat →ₗ[ℂ] Mat, PhysicalCompletelyPositive Phi ∧
      ∀ q : FeatureSpace, Phi (U q) = (U (E (1/2) q) : Mat) := by
  rintro ⟨Phi,hcp,hagree⟩
  exact no_positive_extension ⟨Phi, physical_CP_positive Phi hcp, hagree⟩

/-- The order premise on G is weighted Hilbert self-adjoint nonnegativity.
The restriction acts on F at every time, and physical-cone preservation is
required at every nonnegative time. No arbitrary ambient CPTP embedding claim
is made. -/
theorem no_nonnegative_generator_embedding
    (G : FeatureSpace →L[ℂ] FeatureSpace) (hG : 0 ≤ G)
    (hunit : NormedSpace.exp (-G) = LinearMap.toContinuousLinearMap quotientTransfer)
    (hcone : ∀ t : ℝ, 0 ≤ t → ∀ q : FeatureSpace, q ∈ cone →
      NormedSpace.exp ((-t) • G) q ∈ cone) : False := by
  letI : NormedAlgebra ℚ (FeatureSpace →L[ℂ] FeatureSpace) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hsa : IsSelfAdjoint G :=
    ((ContinuousLinearMap.nonneg_iff_isPositive G).mp hG).isSelfAdjoint
  let R : FeatureSpace →L[ℂ] FeatureSpace := NormedSpace.exp ((-1/2 : ℝ) • G)
  have hRpos : R.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive R).mp
    (((IsSelfAdjoint.all (-1/2 : ℝ)).smul hsa).exp_nonneg)
  have hsq : R*R = LinearMap.toContinuousLinearMap quotientTransfer := by
    change NormedSpace.exp ((-1/2 : ℝ) • G) * NormedSpace.exp ((-1/2 : ℝ) • G) = _
    rw [← NormedSpace.exp_add_of_commute (Commute.refl _)]
    rw [← add_smul, show (-1/2 : ℝ)+(-1/2) = -1 by norm_num, neg_one_smul]
    exact hunit
  apply no_physical_positive_root
  refine ⟨R.toLinearMap, ?_, hRpos.isSymmetric, ?_, ?_⟩
  · ext q
    exact congrArg (fun T : FeatureSpace →L[ℂ] FeatureSpace => T q) hsq
  · intro q
    change 0 ≤ (⟪q,R q⟫_ℂ).re
    have h := (ContinuousLinearMap.isPositive_iff_complex R).mp hRpos q
    have he : (⟪q,R q⟫_ℂ).re = (⟪R q,q⟫_ℂ).re := by
      rw [← inner_conj_symm (R q) q]
      rfl
    rw [he]
    exact h.2
  · intro q hq
    change NormedSpace.exp ((-1/2 : ℝ) • G) q ∈ cone
    have ht := hcone (1/2) (by norm_num) q hq
    rw [← neg_div] at ht
    exact ht

theorem no_invariant_physical_semigroup
    (G : FeatureSpace →L[ℂ] FeatureSpace) (hG : 0 ≤ G)
    (Phi : ℝ → Mat →ₗ[ℂ] Mat)
    (hrestriction : ∀ t : ℝ, 0 ≤ t → ∀ q : FeatureSpace,
      Phi t (U q) = (U (NormedSpace.exp ((-t) • G) q) : Mat))
    (hunit : ∀ q : FeatureSpace, Phi 1 (U q) = transfer (U q))
    (hpositive : ∀ t : ℝ, 0 ≤ t → ∀ X : Mat, X.PosSemidef → (Phi t X).PosSemidef) : False := by
  apply no_nonnegative_generator_embedding G hG
  · ext q
    apply U.injective
    apply Subtype.ext
    change (U (NormedSpace.exp (-G) q) : Mat) = (U (quotientTransfer q) : Mat)
    rw [U_transfer, ← hunit, hrestriction 1 (by norm_num)]
    simp
  · intro t ht q hq
    change (U (NormedSpace.exp ((-t) • G) q) : Mat).PosSemidef
    rw [← hrestriction t ht]
    exact hpositive t ht _ hq

theorem principal_root_exists :
    (E (1/2)).comp (E (1/2)) = quotientTransfer ∧ (E (1/2)).IsSymmetric ∧
      (∀ q : FeatureSpace, 0 ≤ (⟪q,E (1/2) q⟫_ℂ).re) := by
  refine ⟨?_,E_selfadjoint _,E_nonneg _⟩
  rw [← E_add, show (1/2 : ℝ)+1/2=1 by norm_num, E_one]

variable (A : Type*) [Fintype A] [DecidableEq A]

def spectatorDensity (e : A) : Matrix A A ℂ := Matrix.single e e 1

theorem spectatorDensity_physical (e : A) : IsDensityOperator (spectatorDensity A e) := by
  have he : spectatorDensity A e = Matrix.diagonal (Pi.single e 1) := by
    ext f g
    by_cases hf : f=e <;> by_cases hg : g=e <;>
      simp_all [spectatorDensity, Matrix.single, Matrix.diagonal_apply] <;> aesop
  constructor
  · rw [he, Matrix.posSemidef_diagonal_iff]
    intro f
    by_cases hf : e=f <;> simp [hf]
  · simp [spectatorDensity, Matrix.trace, Matrix.single]

theorem spectator_half_input (e : A) :
    IsDensityOperator (effect 1 ⊗ₖ spectatorDensity A e) ∧
      effect 1 ⊗ₖ spectatorDensity A e ∈ FiniteQutritInvariantExamples.matrixCarrier A := by
  refine ⟨⟨?_,?_⟩,tensor_mem A ⟨effect 1,effect_symmetric 1⟩ _⟩
  · have hP : (effect 1).PosSemidef := by
      have hp := physical_input.1
      change (U (feature 1) : Mat).PosSemidef at hp
      simpa only [U_feature] using hp
    exact hP.kronecker (spectatorDensity_physical A e).1
  · rw [Matrix.trace_kronecker, (spectatorDensity_physical A e).2]
    change (projector 1).trace * 1 = 1
    rw [projector_trace, mul_one]

omit [Fintype A] in
theorem spectator_half_entry (e : A) :
    spectatorE A (1/2) (effect 1 ⊗ₖ spectatorDensity A e) (2,e) (2,e) = (theta : ℂ) := by
  have he : matrixSpectral (fun i => (Real.exp ((1/2 : ℝ)*Real.log (eigenvalue i)) : ℂ))
      (effect 1) 2 2 = (theta : ℂ) := by
    rw [← U_feature 1]
    change (synthesis (fun i => (Real.exp ((1/2 : ℝ)*Real.log (eigenvalue i)) : ℂ) *
      coefficients (U (feature 1)) i)) 2 2 = _
    rw [← U_spectral]
    exact half_entry
  rw [spectatorE, spectator_product]
  change matrixSpectral (fun i => (Real.exp ((1/2 : ℝ)*Real.log (eigenvalue i)) : ℂ))
    (effect 1) 2 2 * spectatorDensity A e e e = _
  rw [he]
  simp [spectatorDensity, Matrix.single]

omit [Fintype A] in
theorem spectator_half_not_physical (e : A) :
    ¬ (spectatorE A (1/2) (effect 1 ⊗ₖ spectatorDensity A e)).PosSemidef := by
  intro h
  have hd := h.diag_nonneg (i := (2,e))
  rw [spectator_half_entry] at hd
  have hr := (Complex.le_def.mp hd).1
  norm_num at hr
  linarith [theta_strict]

theorem nonempty_spectator_obstruction [Nonempty A] :
    ∃ X : Matrix (Q × A) (Q × A) ℂ,
      IsDensityOperator X ∧ X ∈ FiniteQutritInvariantExamples.matrixCarrier A ∧
      ¬ (spectatorE A (1/2) X).PosSemidef := by
  let e : A := Classical.choice (inferInstance : Nonempty A)
  exact ⟨effect 1 ⊗ₖ spectatorDensity A e,(spectator_half_input A e).1,
    (spectator_half_input A e).2,spectator_half_not_physical A e⟩

end SKEFTHawking.QuantumNetwork.FiniteQutritFractionalObstruction
