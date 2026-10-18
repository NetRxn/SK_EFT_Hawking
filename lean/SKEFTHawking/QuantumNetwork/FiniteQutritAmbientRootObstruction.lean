import SKEFTHawking.QuantumNetwork.FiniteQutritFractionalObstruction

/-!
# No positive square root of the actual ambient qutrit channel

The full complex matrix algebra has nine eigenvectors, with repeated eigenvalues
in the off-diagonal sectors. Only the three simple diagonal eigenlines are used
to exclude every signed positive root. The conclusion concerns homogeneous
same-system semigroups; time-dependent paths and retained-environment dilations
are outside its scope. Integer Kraus histories retain their physical meaning.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritAmbientRootObstruction
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteQutritPhysicalMemory FiniteQutritInvariantCarrier
open FiniteQutritAveragedTransfer FiniteQutritAveragedMixing
open FiniteQutritFractionalObstruction
open scoped BigOperators ComplexOrder Kronecker

private theorem vec6_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

abbrev AmbientIndex := Fin 9

def diagonalPart (d : Fin 3 → ℂ) : Mat := Matrix.diagonal d

def symmetricPart (s : Fin 3 → ℂ) : Mat :=
  !![0,s 0,s 1; s 0,0,s 2; s 1,s 2,0]

def antisymmetricPart (a : Fin 3 → ℂ) : Mat :=
  !![0,a 0,a 1; -a 0,0,a 2; -a 1,-a 2,0]

def diagonalCoordinates (X : Mat) : Fin 3 → ℂ := ![X 0 0,X 1 1,X 2 2]
def symmetricCoordinates (X : Mat) : Fin 3 → ℂ :=
  ![(X 0 1+X 1 0)/2,(X 0 2+X 2 0)/2,(X 1 2+X 2 1)/2]
def antisymmetricCoordinates (X : Mat) : Fin 3 → ℂ :=
  ![(X 0 1-X 1 0)/2,(X 0 2-X 2 0)/2,(X 1 2-X 2 1)/2]

theorem transpose_decomposition (X : Mat) :
    diagonalPart (diagonalCoordinates X) + symmetricPart (symmetricCoordinates X) +
      antisymmetricPart (antisymmetricCoordinates X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalPart, diagonalCoordinates, symmetricPart, symmetricCoordinates,
      antisymmetricPart, antisymmetricCoordinates] <;> ring

/-- Direct evaluation of all ten original projector sandwiches, for arbitrary
complex entries. No transpose or adjoint symmetry is assumed. -/
theorem actual_ambient_action (X : Mat) : transfer X =
    !![(8*X 0 0+X 1 1+X 2 2)/10,(4*X 0 1+X 1 0-X 2 1)/10,
        (4*X 0 2-X 1 2+X 2 0)/10;
       (X 0 1+4*X 1 0-X 1 2)/10,(X 0 0+9*X 1 1)/10,
        (-X 0 2-X 1 0+4*X 1 2)/10;
       (X 0 2+4*X 2 0-X 2 1)/10,(-X 0 1-X 2 0+4*X 2 1)/10,
        (X 0 0+9*X 2 2)/10] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transfer_apply, pinching_apply, projector, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply, Matrix.smul_apply, Matrix.vecMul, dotProduct, smul_eq_mul] <;> ring

/-- The three rational blocks use transpose symmetry, not Hermitian symmetry. -/
def diagonalBlock : Matrix (Fin 3) (Fin 3) ℂ := !![8/10,1/10,1/10;1/10,9/10,0;1/10,0,9/10]
def symmetricBlock : Matrix (Fin 3) (Fin 3) ℂ := !![5/10,0,-1/10;0,5/10,-1/10;-1/10,-1/10,4/10]
def antisymmetricBlock : Matrix (Fin 3) (Fin 3) ℂ := !![3/10,0,1/10;0,3/10,-1/10;1/10,-1/10,4/10]

theorem actual_blocks (d s a : Fin 3 → ℂ) :
    transfer (diagonalPart d + symmetricPart s + antisymmetricPart a) =
      diagonalPart (diagonalBlock *ᵥ d) + symmetricPart (symmetricBlock *ᵥ s) +
        antisymmetricPart (antisymmetricBlock *ᵥ a) := by
  rw [actual_ambient_action]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalPart, symmetricPart, antisymmetricPart, diagonalBlock,
      symmetricBlock, antisymmetricBlock, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring

/-- The first six vectors are literally the existing mixing vectors. -/
def ambientEigenvector : AmbientIndex → Mat :=
  ![eigenvector 0,eigenvector 1,eigenvector 2,eigenvector 3,eigenvector 4,eigenvector 5,
    antisymmetricPart ![1,-1,2],antisymmetricPart ![1,1,0],antisymmetricPart ![1,-1,-1]]

def ambientEigenvalue : AmbientIndex → ℂ := ![1,9/10,7/10,3/5,1/2,3/10,1/2,3/10,1/5]

def ambientCoefficients (X : Mat) : AmbientIndex → ℂ :=
  let d := diagonalCoordinates X
  let s := symmetricCoordinates X
  let a := antisymmetricCoordinates X
  ![(d 0+d 1+d 2)/3,(d 1-d 2)/2,(-2*d 0+d 1+d 2)/6,
    (s 0+s 1-s 2)/3,(s 0-s 1)/2,(s 0+s 1+2*s 2)/6,
    (a 0-a 1+2*a 2)/6,(a 0+a 1)/2,(a 0-a 1-a 2)/3]

def ambientSynthesis : (AmbientIndex → ℂ) →ₗ[ℂ] Mat where
  toFun c := ∑ i, c i • ambientEigenvector i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z c := by simp [Finset.smul_sum, smul_smul]

theorem ambient_expansion (X : Mat) : ambientSynthesis (ambientCoefficients X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientSynthesis, ambientCoefficients, diagonalCoordinates, symmetricCoordinates,
      antisymmetricCoordinates, ambientEigenvector, eigenvector, eigenCoordinates,
      symmetricMatrix, antisymmetricPart, Fin.sum_univ_succ, smul_eq_mul] <;> ring

theorem ambient_coefficients_synthesis (c : AmbientIndex → ℂ) :
    ambientCoefficients (ambientSynthesis c) = c := by
  ext k
  fin_cases k <;>
    simp [ambientCoefficients, diagonalCoordinates, symmetricCoordinates,
      antisymmetricCoordinates, ambientSynthesis, ambientEigenvector, eigenvector,
      eigenCoordinates, symmetricMatrix, antisymmetricPart, Fin.sum_univ_succ,
      smul_eq_mul] <;> ring

private theorem actual_skew_eigenvector (i : Fin 3) :
    transfer (antisymmetricPart (![![1,-1,2],![1,1,0],![1,-1,-1]] i)) =
      (![1/2,3/10,1/5] i : ℂ) •
        antisymmetricPart (![![1,-1,2],![1,1,0],![1,-1,-1]] i) := by
  rw [actual_ambient_action]
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [antisymmetricPart, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, vec6_last]

theorem actual_ambient_eigenvector (i : AmbientIndex) :
    transfer (ambientEigenvector i) = ambientEigenvalue i • ambientEigenvector i := by
  fin_cases i
  · simpa [ambientEigenvector, ambientEigenvalue, eigenvalue] using actual_eigenvector 0
  · simpa [ambientEigenvector, ambientEigenvalue, eigenvalue] using actual_eigenvector 1
  · simpa [ambientEigenvector, ambientEigenvalue, eigenvalue] using actual_eigenvector 2
  · simpa [ambientEigenvector, ambientEigenvalue, eigenvalue] using actual_eigenvector 3
  · simpa [ambientEigenvector, ambientEigenvalue, eigenvalue] using actual_eigenvector 4
  · simpa [ambientEigenvector, ambientEigenvalue, eigenvalue] using actual_eigenvector 5
  · exact actual_skew_eigenvector 0
  · exact actual_skew_eigenvector 1
  · exact actual_skew_eigenvector 2

/-- An explicit inverse on the entire nine-dimensional complex carrier. -/
def ambientEquiv : (AmbientIndex → ℂ) ≃ₗ[ℂ] Mat where
  toFun := ambientSynthesis
  invFun := ambientCoefficients
  left_inv := ambient_coefficients_synthesis
  right_inv := ambient_expansion
  map_add' := ambientSynthesis.map_add
  map_smul' := ambientSynthesis.map_smul

theorem ambient_synthesis_transfer (c : AmbientIndex → ℂ) :
    transfer (ambientSynthesis c) =
      ambientSynthesis (fun i => ambientEigenvalue i * c i) := by
  simp only [ambientSynthesis, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    map_smul, actual_ambient_eigenvector, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem ambient_coordinate_transfer (X : Mat) (i : AmbientIndex) :
    ambientCoefficients (transfer X) i = ambientEigenvalue i * ambientCoefficients X i := by
  conv_lhs => rw [← ambient_expansion X, ambient_synthesis_transfer,
    ambient_coefficients_synthesis]

theorem ambient_coordinate_smul (z : ℂ) (X : Mat) :
    ambientCoefficients (z • X) = z • ambientCoefficients X :=
  ambientEquiv.symm.map_smul z X

private theorem diagonal_eigenvalue_simple (i k : AmbientIndex)
    (hi : i=0 ∨ i=1 ∨ i=2) (hk : k ≠ i) : ambientEigenvalue k ≠ ambientEigenvalue i := by
  rcases hi with rfl | rfl | rfl <;> fin_cases k <;>
    first | exact (hk rfl).elim | norm_num [ambientEigenvalue, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

/-- Ambient simplicity only for the three diagonal eigenlines. The repeated
1/2 and 3/10 eigenspaces are not asserted to be simple. -/
theorem ambient_simple_eigenspace (i : AmbientIndex) (hi : i=0 ∨ i=1 ∨ i=2)
    (X : Mat) (hX : transfer X = ambientEigenvalue i • X) :
    X = ambientCoefficients X i • ambientEigenvector i := by
  have hc : ambientCoefficients X = Pi.single i (ambientCoefficients X i) := by
    ext k
    by_cases hk : k=i
    · subst k; simp
    · simp only [Pi.single_apply, if_neg hk]
      have he := congrArg (fun Y => ambientCoefficients Y k) hX
      rw [ambient_coordinate_transfer, ambient_coordinate_smul] at he
      change ambientEigenvalue k * ambientCoefficients X k =
        ambientEigenvalue i * ambientCoefficients X k at he
      exact (mul_eq_mul_right_iff.mp he).resolve_left (diagonal_eigenvalue_simple i k hi hk)
  calc
    X = ambientSynthesis (ambientCoefficients X) := (ambient_expansion X).symm
    _ = ambientSynthesis (Pi.single i (ambientCoefficients X i)) := congrArg ambientSynthesis hc
    _ = _ := by simp [ambientSynthesis]

theorem ambient_eigenline_iff (i : AmbientIndex) (hi : i=0 ∨ i=1 ∨ i=2) (X : Mat) :
    transfer X = ambientEigenvalue i • X ↔ ∃ z : ℂ, X = z • ambientEigenvector i := by
  constructor
  · intro hX
    exact ⟨_,ambient_simple_eigenspace i hi X hX⟩
  · rintro ⟨z,rfl⟩
    rw [map_smul, actual_ambient_eigenvector, smul_comm]

theorem ambient_root_commutes (R : Mat →ₗ[ℂ] Mat)
    (hR : R.comp R = transfer) (X : Mat) : R (transfer X) = transfer (R X) := by
  have h (Y : Mat) : R (R Y) = transfer Y := congrArg (fun L => L Y) hR
  rw [← h X, h (R X)]

theorem root_diagonal_line (R : Mat →ₗ[ℂ] Mat) (hR : R.comp R = transfer)
    (i : AmbientIndex) (hi : i=0 ∨ i=1 ∨ i=2) :
    R (ambientEigenvector i) =
      ambientCoefficients (R (ambientEigenvector i)) i • ambientEigenvector i := by
  apply ambient_simple_eigenspace i hi
  rw [← ambient_root_commutes R hR, actual_ambient_eigenvector, map_smul]

theorem root_diagonal_scalar_square (R : Mat →ₗ[ℂ] Mat) (hR : R.comp R = transfer)
    (i : AmbientIndex) (hi : i=0 ∨ i=1 ∨ i=2) :
    let z := ambientCoefficients (R (ambientEigenvector i)) i
    z*z = ambientEigenvalue i := by
  let z := ambientCoefficients (R (ambientEigenvector i)) i
  have hd : R (ambientEigenvector i) = z • ambientEigenvector i :=
    root_diagonal_line R hR i hi
  have hv : ambientEigenvector i 1 1 = 1 := by
    rcases hi with rfl | rfl | rfl <;>
      norm_num [ambientEigenvector, eigenvector, eigenCoordinates, symmetricMatrix,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, vec6_last]
  have h := congrArg (fun L => L (ambientEigenvector i) 1 1) hR
  change R (R (ambientEigenvector i)) 1 1 = transfer (ambientEigenvector i) 1 1 at h
  rw [hd, map_smul, hd, actual_ambient_eigenvector] at h
  simpa [Matrix.smul_apply, smul_eq_mul, hv] using h

private theorem complex_signed_sqrt (z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : z*z = (r : ℂ)) : z = (Real.sqrt r : ℂ) ∨ z = -(Real.sqrt r : ℂ) := by
  have hs : (Real.sqrt r : ℂ)*(Real.sqrt r : ℂ) = (r : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hr
  have hf : (z-(Real.sqrt r : ℂ))*(z+(Real.sqrt r : ℂ)) = 0 := by
    calc
      _ = z*z - (Real.sqrt r : ℂ)*(Real.sqrt r : ℂ) := by ring
      _ = 0 := by rw [hz,hs,sub_self]
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)

theorem ambient_identity : ambientEigenvector 0 = (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ambientEigenvector, eigenvector, eigenCoordinates, symmetricMatrix,
      Matrix.one_apply, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, vec6_last]

theorem coordinate_projector_positive (j : Fin 3) : (projector j.castSucc.castSucc).PosSemidef := by
  simpa only [(projector_hermitian _).eq, projector_idempotent] using
    Matrix.posSemidef_conjTranspose_mul_self (projector j.castSucc.castSucc)

/-- The three witness inputs are the actual trace-one PSD coordinate projectors. -/
theorem coordinate_projector_density (j : Fin 3) :
    (projector j.castSucc.castSucc).PosSemidef ∧ (projector j.castSucc.castSucc).trace = 1 :=
  ⟨coordinate_projector_positive j,projector_trace _⟩

theorem coordinate_projector_expansions :
    projector 0 = (1/3 : ℂ) • ambientEigenvector 0 - (1/3 : ℂ) • ambientEigenvector 2 ∧
    projector 1 = (1/3 : ℂ) • ambientEigenvector 0 + (1/2 : ℂ) • ambientEigenvector 1 +
      (1/6 : ℂ) • ambientEigenvector 2 ∧
    projector 2 = (1/3 : ℂ) • ambientEigenvector 0 - (1/2 : ℂ) • ambientEigenvector 1 +
      (1/6 : ℂ) • ambientEigenvector 2 := by
  refine ⟨?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [projector, ambientEigenvector, eigenvector, eigenCoordinates, symmetricMatrix,
      Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, vec6_last]

/-- Unitality is forced by the square equation and physical positivity. -/
theorem positive_root_scalar_zero (R : Mat →ₗ[ℂ] Mat) (hR : R.comp R = transfer)
    (hp : ∀ X : Mat, X.PosSemidef → (R X).PosSemidef) :
    ambientCoefficients (R (ambientEigenvector 0)) 0 = 1 := by
  let c := ambientCoefficients (R (ambientEigenvector 0)) 0
  have hd : R (ambientEigenvector 0) = c • ambientEigenvector 0 :=
    root_diagonal_line R hR 0 (Or.inl rfl)
  have hs : c*c = (1 : ℂ) := root_diagonal_scalar_square R hR 0 (Or.inl rfl)
  have hi : (1 : Mat).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Mat)
  have hpos := (hp 1 hi).diag_nonneg (i := 0)
  rw [ambient_identity] at hd
  rw [hd] at hpos
  have hr := (Complex.le_def.mp hpos).1
  have hsign := complex_signed_sqrt c 1 (by norm_num) (by simpa using hs)
  norm_num at hsign
  rcases hsign with h | h
  · exact h
  · rw [h] at hr
    norm_num [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hr

theorem positive_root_unital (R : Mat →ₗ[ℂ] Mat) (hR : R.comp R = transfer)
    (hp : ∀ X : Mat, X.PosSemidef → (R X).PosSemidef) : R 1 = 1 := by
  have hd := root_diagonal_line R hR 0 (Or.inl rfl)
  rw [positive_root_scalar_zero R hR hp, one_smul, ambient_identity] at hd
  exact hd

/-- These three entries are forced before choosing any root on the repeated
non-diagonal eigenspaces. -/
theorem root_projector_entries (R : Mat →ₗ[ℂ] Mat) (c a b : ℂ)
    (h0 : R (ambientEigenvector 0) = c • ambientEigenvector 0)
    (h1 : R (ambientEigenvector 1) = a • ambientEigenvector 1)
    (h2 : R (ambientEigenvector 2) = b • ambientEigenvector 2) :
    R (projector 0) 0 0 = c/3+2*b/3 ∧
    R (projector 1) 1 1 = c/3+a/2+b/6 ∧
    R (projector 1) 2 2 = c/3-a/2+b/6 := by
  have hp0 : R (projector 0) = (1/3 : ℂ) • (c • ambientEigenvector 0) -
      (1/3 : ℂ) • (b • ambientEigenvector 2) := by
    rw [coordinate_projector_expansions.1, map_sub, map_smul, map_smul, h0,h2]
  have hp1 : R (projector 1) = (1/3 : ℂ) • (c • ambientEigenvector 0) +
      (1/2 : ℂ) • (a • ambientEigenvector 1) + (1/6 : ℂ) • (b • ambientEigenvector 2) := by
    rw [coordinate_projector_expansions.2.1, map_add, map_add, map_smul, map_smul,
      map_smul, h0,h1,h2]
  rw [hp0,hp1]
  constructor
  · norm_num [ambientEigenvector, eigenvector, eigenCoordinates, symmetricMatrix,
      Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val_succ, vec6_last]
    ring
  · constructor <;>
      norm_num [ambientEigenvector, eigenvector, eigenCoordinates, symmetricMatrix,
        Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, vec6_last] <;> ring

private theorem sqrt_seven_tenths_lower : (1/2 : ℝ) < Real.sqrt (7/10) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7/10)
  have hp := Real.sqrt_nonneg (7/10 : ℝ)
  nlinarith

/-- No auxiliary order, trace, unitality, normality, or feature-invariance
hypothesis is imposed on the putative ambient complex-linear root. -/
theorem ambient_positive_root_impossible (R : Mat →ₗ[ℂ] Mat)
    (hR : R.comp R = transfer)
    (hp : ∀ X : Mat, X.PosSemidef → (R X).PosSemidef) : False := by
  let a := ambientCoefficients (R (ambientEigenvector 1)) 1
  let b := ambientCoefficients (R (ambientEigenvector 2)) 2
  have h0 : R (ambientEigenvector 0) = (1 : ℂ) • ambientEigenvector 0 := by
    rw [root_diagonal_line R hR 0 (Or.inl rfl),positive_root_scalar_zero R hR hp]
  have h1 : R (ambientEigenvector 1) = a • ambientEigenvector 1 :=
    root_diagonal_line R hR 1 (Or.inr (Or.inl rfl))
  have h2 : R (ambientEigenvector 2) = b • ambientEigenvector 2 :=
    root_diagonal_line R hR 2 (Or.inr (Or.inr rfl))
  have ha2 : a*a = ((9/10 : ℝ) : ℂ) := by
    simpa [ambientEigenvalue] using root_diagonal_scalar_square R hR 1 (Or.inr (Or.inl rfl))
  have hb2 : b*b = ((7/10 : ℝ) : ℂ) := by
    simpa [ambientEigenvalue, Matrix.cons_val_two] using
      root_diagonal_scalar_square R hR 2 (Or.inr (Or.inr rfl))
  have ha := complex_signed_sqrt a (9/10) (by norm_num) ha2
  have hb := complex_signed_sqrt b (7/10) (by norm_num) hb2
  have he := root_projector_entries R 1 a b h0 h1 h2
  have p0 := (hp _ (coordinate_projector_positive 0)).diag_nonneg (i := 0)
  have p11 := (hp _ (coordinate_projector_positive 1)).diag_nonneg (i := 1)
  have p22 := (hp _ (coordinate_projector_positive 1)).diag_nonneg (i := 2)
  change 0 ≤ R (projector 0) 0 0 at p0
  change 0 ≤ R (projector 1) 1 1 at p11
  change 0 ≤ R (projector 1) 2 2 at p22
  rw [he.1] at p0
  rw [he.2.1] at p11
  rw [he.2.2] at p22
  rcases hb with hb | hb
  · rcases ha with ha | ha
    · rw [ha,hb] at p22
      have r22 : 0 ≤ (1/3 : ℝ) - Real.sqrt (9/10)/2 + Real.sqrt (7/10)/6 := by
        simpa only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re,
          Complex.ofReal_re, Complex.one_re, Complex.zero_re] using (Complex.le_def.mp p22).1
      have ht := theta_strict
      unfold theta at ht
      linarith
    · rw [ha,hb] at p11
      have r11 : 0 ≤ (1/3 : ℝ) + (-Real.sqrt (9/10))/2 + Real.sqrt (7/10)/6 := by
        simpa only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
          Complex.ofReal_re, Complex.one_re, Complex.zero_re] using (Complex.le_def.mp p11).1
      have ht := theta_strict
      unfold theta at ht
      linarith
  · rw [hb] at p0
    have r0 : 0 ≤ (1/3 : ℝ) + 2*(-Real.sqrt (7/10))/3 := by
      have hr := (Complex.le_def.mp p0).1
      norm_num only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
        Complex.zero_re, Complex.neg_im, mul_zero, sub_zero, map_ofNat] at hr
      exact hr
    linarith [sqrt_seven_tenths_lower]

theorem no_ambient_positive_square_root :
    ¬ ∃ R : Mat →ₗ[ℂ] Mat, R.comp R = transfer ∧
      (∀ X : Mat, X.PosSemidef → (R X).PosSemidef) := by
  rintro ⟨R,hR,hp⟩
  exact ambient_positive_root_impossible R hR hp

/-- The original normalized Kraus transfer is physically CP on every finite
spectator, on all correlated ambient inputs. -/
theorem actual_transfer_CP : PhysicalCompletelyPositive transfer := by
  intro n X hX
  have he : physicalAmplification transfer n X = amplified (Fin n) X := by
    ext u v
    exact (congrArg (fun Y => Y u.1 v.1)
      (amplified_block (Fin n) X u.2 v.2)).symm
  rw [he]
  exact amplified_positive (Fin n) hX

theorem no_ambient_CP_square_root :
    ¬ ∃ R : Mat →ₗ[ℂ] Mat, R.comp R = transfer ∧ PhysicalCompletelyPositive R := by
  rintro ⟨R,hR,hcp⟩
  exact ambient_positive_root_impossible R hR (physical_CP_positive R hcp)

theorem no_ambient_CPTP_square_root :
    ¬ ∃ R : Mat →ₗ[ℂ] Mat, R.comp R = transfer ∧ PhysicalCompletelyPositive R ∧
      (∀ X : Mat, (R X).trace = X.trace) := by
  rintro ⟨R,hR,hcp,_⟩
  exact no_ambient_CP_square_root ⟨R,hR,hcp⟩

/-- Only the nonnegative half-time composition law and positivity are used.
Continuity, a generator and a zero-time identity are unnecessary. -/
theorem ambient_positive_semigroup_impossible (Phi : ℝ → Mat →ₗ[ℂ] Mat)
    (hpositive : ∀ t : ℝ, 0 ≤ t → ∀ X : Mat, X.PosSemidef → (Phi t X).PosSemidef)
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → Phi (s+t) = (Phi s).comp (Phi t))
    (hone : Phi 1 = transfer) : False := by
  apply ambient_positive_root_impossible (Phi (1/2))
  · have h := hadd (1/2) (1/2) (by norm_num) (by norm_num)
    rw [show (1/2 : ℝ)+1/2 = 1 by norm_num, hone] at h
    exact h.symm
  · exact hpositive (1/2) (by norm_num)

theorem no_ambient_positive_semigroup :
    ¬ ∃ Phi : ℝ → Mat →ₗ[ℂ] Mat,
      (∀ t : ℝ, 0 ≤ t → ∀ X : Mat, X.PosSemidef → (Phi t X).PosSemidef) ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → Phi (s+t) = (Phi s).comp (Phi t)) ∧
      Phi 1 = transfer := by
  rintro ⟨Phi,hpos,hadd,hone⟩
  exact ambient_positive_semigroup_impossible Phi hpos hadd hone

theorem no_ambient_CP_semigroup :
    ¬ ∃ Phi : ℝ → Mat →ₗ[ℂ] Mat,
      (∀ t : ℝ, 0 ≤ t → PhysicalCompletelyPositive (Phi t)) ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → Phi (s+t) = (Phi s).comp (Phi t)) ∧
      Phi 1 = transfer := by
  rintro ⟨Phi,hcp,hadd,hone⟩
  apply ambient_positive_semigroup_impossible Phi _ hadd hone
  intro t ht
  exact physical_CP_positive (Phi t) (hcp t ht)

theorem no_ambient_CPTP_semigroup :
    ¬ ∃ Phi : ℝ → Mat →ₗ[ℂ] Mat,
      (∀ t : ℝ, 0 ≤ t → PhysicalCompletelyPositive (Phi t) ∧
        ∀ X : Mat, (Phi t X).trace = X.trace) ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → Phi (s+t) = (Phi s).comp (Phi t)) ∧
      Phi 1 = transfer := by
  rintro ⟨Phi,hcptp,hadd,hone⟩
  exact no_ambient_CP_semigroup ⟨Phi,fun t ht => (hcptp t ht).1,hadd,hone⟩

/-- The obstructed map is nevertheless the actual unital normalized Kraus
channel, preserving trace and the physical cone. -/
theorem actual_channel_nonvacuity :
    IsKrausChannel krausOperator ∧
    (∀ X : Mat, krausMap krausOperator X = transfer X) ∧
    PhysicalCompletelyPositive transfer ∧
    (∀ X : Mat, (transfer X).trace = X.trace) ∧
    transfer 1 = 1 ∧
    ¬ (∃ R : Mat →ₗ[ℂ] Mat, R.comp R = transfer ∧
      (∀ X : Mat, X.PosSemidef → (R X).PosSemidef)) :=
  ⟨kraus_normalized,kraus_action,actual_transfer_CP,transfer_trace,transfer_one,
    no_ambient_positive_square_root⟩

/-- Every natural integer iterate, including zero, retains positivity,
trace preservation and unitality despite the absence of a positive half-step. -/
theorem actual_integer_controls (n : ℕ) :
    (∀ X : Mat, X.PosSemidef → (iterate n X).PosSemidef) ∧
    (∀ X : Mat, (iterate n X).trace = X.trace) ∧ iterate n 1 = 1 := by
  refine ⟨fun _ hX => iterate_positive n hX,iterate_trace n,?_⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    change iterate n (transfer 1) = 1
    rw [transfer_one,ih]

/-- The genuine retained fresh-setting/outcome tree remains positive on
correlated spectators and its coarse graining is the integer joint channel. -/
theorem actual_joint_controls (E : Type*) [Fintype E] [DecidableEq E]
    (n : ℕ) (X : Matrix (Q × E) (Q × E) ℂ) (hX : X.PosSemidef) :
    (amplifiedIterate E n X).PosSemidef ∧
    (∑ h, run Q E 10 (recordTree E n) h X) = amplifiedIterate E n X := by
  refine ⟨?_,discarded_history E n X⟩
  induction n generalizing X with
  | zero => exact hX
  | succ n ih =>
    change (amplifiedIterate E n (amplified E X)).PosSemidef
    exact ih _ (amplified_positive E hX)

/-- All records, including impossible leaves, retain nonnegative normalized
weights on every actual joint density input. -/
theorem actual_joint_record_normalization (E : Type*) [Fintype E] [DecidableEq E]
    (n : ℕ) (X : Matrix (Q × E) (Q × E) ℂ) (hX : IsDensityOperator X) :
    (∀ h, 0 ≤ weight Q E 10 (recordTree E n) h X) ∧
      (∑ h, weight Q E 10 (recordTree E n) h X) = 1 :=
  all_records_normalized E n hX

/-- Product inputs leave the spectator untouched at every integer depth. -/
theorem actual_integer_spectator (E : Type*) [Fintype E] [DecidableEq E]
    (n : ℕ) (X : Mat) (sigma : Matrix E E ℂ) :
    amplifiedIterate E n (X ⊗ₖ sigma) = iterate n X ⊗ₖ sigma :=
  amplified_iterate_product E n X sigma

end SKEFTHawking.QuantumNetwork.FiniteQutritAmbientRootObstruction
