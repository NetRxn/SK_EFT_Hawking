import SKEFTHawking.QuantumNetwork.FiniteQutritAveragedTransfer

/-!
# Exact complex spectrum on the least reachable symmetric carrier

The coordinate metric comes from trace(XᴴY)/3. The eigenvectors and their
spanning coefficients below are derived for every complex symmetric matrix.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritAveragedMixing
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteQutritPhysicalMemory FiniteQutritInvariantCarrier
open FiniteQutritInvariantReconstruction FiniteQutritAveragedTransfer
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

private theorem vec6_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

def coordinateMetric : Index → ℝ := ![1/3,1/3,1/3,2/3,2/3,2/3]

theorem pairing_coordinates (c d : Index → ℂ) :
    pairing (symmetricMatrix c) (symmetricMatrix d) =
      ∑ i, (coordinateMetric i : ℂ) * star (c i) * d i := by
  simp [pairing_trace, symmetricMatrix, coordinateMetric, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.trace, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last,
    Complex.star_def]
  ring

/-- Columns are the actual action in coordinates (00,11,22,01,02,12). -/
def actionMatrix : Matrix Index Index ℂ :=
  !![4/5,1/10,1/10,0,0,0; 1/10,9/10,0,0,0,0; 1/10,0,9/10,0,0,0;
    0,0,0,1/2,0,-1/10; 0,0,0,0,1/2,-1/10; 0,0,0,-1/10,-1/10,2/5]

theorem actual_coordinate_action (c : Index → ℂ) :
    transfer (symmetricMatrix c) = symmetricMatrix (actionMatrix *ᵥ c) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [transfer_apply, pinching_apply, projector, symmetricMatrix, actionMatrix,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last] <;> ring

def eigenCoordinates : Index → (Index → ℂ) := ![
  ![1,1,1,0,0,0], ![0,1,-1,0,0,0], ![-2,1,1,0,0,0],
  ![0,0,0,1,1,-1], ![0,0,0,1,-1,0], ![0,0,0,1,1,2]]

def eigenvector (i : Index) : Mat := symmetricMatrix (eigenCoordinates i)
def eigenvalue : Index → ℝ := ![1,9/10,7/10,3/5,1/2,3/10]
def eigenNormSq : Index → ℝ := ![1,2/3,2,2,4/3,4]

theorem eigenvector_mem (i : Index) : eigenvector i ∈ symmetricCarrier := symmetricMatrix_mem _

theorem symmetricMatrix_smul (z : ℂ) (c : Index → ℂ) :
    symmetricMatrix (z • c) = z • symmetricMatrix c := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem coordinate_eigenvector (i : Index) :
    actionMatrix *ᵥ eigenCoordinates i = (eigenvalue i : ℂ) • eigenCoordinates i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [actionMatrix, eigenCoordinates, eigenvalue,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem actual_eigenvector (i : Index) :
    transfer (eigenvector i) = (eigenvalue i : ℂ) • eigenvector i := by
  rw [eigenvector, actual_coordinate_action, coordinate_eigenvector, symmetricMatrix_smul]

theorem eigenvector_pairing (i j : Index) :
    pairing (eigenvector i) (eigenvector j) = if i=j then (eigenNormSq i : ℂ) else 0 := by
  rw [eigenvector, eigenvector, pairing_coordinates]
  fin_cases i <;> fin_cases j <;>
    norm_num [eigenCoordinates, coordinateMetric, eigenNormSq, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last,
      Fin.ext_iff, map_ofNat]

theorem eigenNormSq_positive (i : Index) : 0 < eigenNormSq i := by
  fin_cases i <;> norm_num [eigenNormSq, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec6_last]

/-- All-complex expansion coefficients, not an assumption of spanning. -/
def coefficients (X : Mat) : Index → ℂ := ![
  (X 0 0+X 1 1+X 2 2)/3,
  (X 1 1-X 2 2)/2,
  (-2*X 0 0+X 1 1+X 2 2)/6,
  (X 0 1+X 0 2-X 1 2)/3,
  (X 0 1-X 0 2)/2,
  (X 0 1+X 0 2+2*X 1 2)/6]

def synthesis : (Index → ℂ) →ₗ[ℂ] Mat where
  toFun c := ∑ i, c i • eigenvector i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

theorem expansion (X : symmetricCarrier) : synthesis (coefficients X) = X := by
  have hs := X.property
  have h10 := hs.apply 0 1
  have h20 := hs.apply 0 2
  have h21 := hs.apply 1 2
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [synthesis, coefficients, eigenvector, eigenCoordinates, symmetricMatrix,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, vec6_last, smul_eq_mul, h10, h20, h21] <;> ring

theorem coefficients_synthesis (c : Index → ℂ) : coefficients (synthesis c) = c := by
  ext i
  fin_cases i <;>
    simp [coefficients, synthesis, eigenvector, eigenCoordinates, symmetricMatrix,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, vec6_last, smul_eq_mul] <;> ring

theorem synthesis_mem (c : Index → ℂ) : synthesis c ∈ symmetricCarrier :=
  by
  change (∑ i, c i • eigenvector i) ∈ symmetricCarrier
  exact Submodule.sum_mem _ (fun i _ => (eigenvector_mem i).smul _)

def eigenEquiv : (Index → ℂ) ≃ₗ[ℂ] symmetricCarrier where
  toFun c := ⟨synthesis c, synthesis_mem c⟩
  invFun X := coefficients X
  left_inv := coefficients_synthesis
  right_inv X := Subtype.ext (expansion X)
  map_add' c d := Subtype.ext (synthesis.map_add c d)
  map_smul' a c := Subtype.ext (synthesis.map_smul a c)

def eigenbasis : Module.Basis Index ℂ symmetricCarrier :=
  (Pi.basisFun ℂ Index).map eigenEquiv


theorem eigenbasis_apply (i : Index) : (eigenbasis i : Mat) = eigenvector i := by
  simp [eigenbasis, Module.Basis.map_apply, Pi.basisFun_apply, eigenEquiv, synthesis]

theorem pairing_synthesis (c d : Index → ℂ) :
    pairing (synthesis c) (synthesis d) =
      ∑ i, star (c i) * d i * (eigenNormSq i : ℂ) := by
  simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, pairing,
    map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    Finset.mul_sum]
  change (∑ j, ∑ i, d j * (star (c i) * pairing (eigenvector i) (eigenvector j))) = _
  simp_rw [eigenvector_pairing]
  simp [mul_ite, mul_assoc, mul_comm, mul_left_comm]

private theorem complex_norm_coefficient (z : ℂ) (r : ℝ) :
    (star z * z * (r : ℂ)).re = ‖z‖^2 * r := by
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply]
  ring

theorem synthesis_norm_sq (c : Index → ℂ) :
    hsNorm (synthesis c)^2 = ∑ i, ‖c i‖^2 * eigenNormSq i := by
  have h := congrArg Complex.re (pairing_synthesis c c)
  rw [pairing_self, Complex.ofReal_re] at h
  simpa only [Complex.re_sum, complex_norm_coefficient] using h

theorem synthesis_transfer (c : Index → ℂ) :
    transfer (synthesis c) = synthesis (fun i => (eigenvalue i : ℂ) * c i) := by
  simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, actual_eigenvector, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem iterate_eigenvector (n : ℕ) (i : Index) :
    iterate n (eigenvector i) = ((eigenvalue i : ℂ)^n) • eigenvector i := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
    change iterate n (transfer (eigenvector i)) = _
    rw [actual_eigenvector, map_smul, ih, smul_smul, pow_succ]
    rw [mul_comm]

theorem iterate_expansion (n : ℕ) (X : symmetricCarrier) :
    iterate n X = synthesis (fun i => (eigenvalue i : ℂ)^n * coefficients X i) := by
  conv_lhs => rw [← expansion X]
  simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, iterate_eigenvector, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem scalar_coefficient (X : Mat) : coefficients X 0 = X.trace/3 := by
  simp [coefficients, Matrix.trace, Fin.sum_univ_succ]
  ring

theorem eigenvalue_nonneg (i : Index) : 0 ≤ eigenvalue i := by
  fin_cases i <;> norm_num [eigenvalue, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec6_last]

theorem tracezero_eigenvalue_bound (i : Index) (hi : i ≠ 0) : eigenvalue i ≤ 9/10 := by
  fin_cases i <;> norm_num [eigenvalue, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec6_last] at *

theorem synthesis_contraction (c : Index → ℂ) (hc : c 0 = 0) :
    hsNorm (transfer (synthesis c)) ≤ (9/10 : ℝ) * hsNorm (synthesis c) := by
  have h : hsNorm (transfer (synthesis c))^2 ≤
      (9/10 : ℝ)^2 * hsNorm (synthesis c)^2 := by
    rw [synthesis_transfer, synthesis_norm_sq, synthesis_norm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i = 0
    · subst i
      simp [hc]
    · have hl := tracezero_eigenvalue_bound i hi
      have h0 := eigenvalue_nonneg i
      have hn := le_of_lt (eigenNormSq_positive i)
      have hb : eigenvalue i ^ 2 ≤ (9/10 : ℝ)^2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hb (mul_nonneg (sq_nonneg ‖c i‖) hn)
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0,
        mul_pow, mul_assoc, mul_left_comm, mul_comm] using hm
  nlinarith [hsNorm_nonneg (transfer (synthesis c)), hsNorm_nonneg (synthesis c)]

theorem tracezero_contraction (X : symmetricCarrier) (hX : (X : Mat).trace = 0) :
    hsNorm (transfer X) ≤ (9/10 : ℝ) * hsNorm X := by
  have hc : coefficients X 0 = 0 := by rw [scalar_coefficient, hX, zero_div]
  simpa only [expansion] using synthesis_contraction (coefficients X) hc

theorem tracezero_iterate (n : ℕ) (X : symmetricCarrier) (hX : (X : Mat).trace = 0) :
    hsNorm (iterate n X) ≤ (9/10 : ℝ)^n * hsNorm X := by
  induction n generalizing X with
  | zero => simp [iterate]
  | succ n ih =>
    change hsNorm (iterate n (transfer X)) ≤ _
    calc
      _ ≤ (9/10 : ℝ)^n * hsNorm (transfer X) :=
        ih ⟨transfer X, transfer_invariant X.property⟩ (by rw [transfer_trace, hX])
      _ ≤ (9/10 : ℝ)^n * ((9/10 : ℝ) * hsNorm X) :=
        mul_le_mul_of_nonneg_left (tracezero_contraction X hX) (by positivity)
      _ = (9/10 : ℝ)^(n+1) * hsNorm X := by rw [pow_succ]; ring

/-- The stationary scalar is fixed by the actual trace, rather than supplied. -/
def stationary (X : Mat) : Mat := (X.trace/3) • (1 : Mat)

theorem stationary_mem (X : Mat) : stationary X ∈ symmetricCarrier := Matrix.isSymm_one.smul _

theorem stationary_trace (X : Mat) : (stationary X).trace = X.trace := by
  simp [stationary, Matrix.trace_smul, Matrix.trace_one]

theorem stationary_fixed (X : Mat) : transfer (stationary X) = stationary X := by
  simp only [stationary, map_smul, transfer_one]

theorem iterate_stationary (n : ℕ) (X : Mat) : iterate n (stationary X) = stationary X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change iterate n (transfer (stationary X)) = _
    rw [stationary_fixed, ih]

/-- Every complex input in the actual six-dimensional carrier, including zero. -/
theorem mixing (n : ℕ) (X : symmetricCarrier) :
    hsNorm (iterate n X - stationary X) ≤
      (9/10 : ℝ)^n * hsNorm ((X : Mat)-stationary X) := by
  have h := tracezero_iterate n
    ⟨(X : Mat)-stationary X, X.property.sub (stationary_mem X)⟩
    (by rw [Matrix.trace_sub, stationary_trace, sub_self])
  simpa only [map_sub, iterate_stationary] using h

theorem hsNorm_U (q : FeatureSpace) : hsNorm (U q) = ‖q‖ := by
  have h := U_inner q q
  rw [← pairing_trace, pairing_self, inner_self_eq_norm_sq_to_K (𝕜 := ℂ),
    RCLike.ofReal_eq_complex_ofReal] at h
  have hr : hsNorm (U q)^2 = ‖q‖^2 := by exact_mod_cast h
  nlinarith [hsNorm_nonneg (U q), norm_nonneg q]

theorem hsNorm_zero_symmetric (X : symmetricCarrier) (hX : hsNorm X = 0) : (X : Mat) = 0 := by
  have hn : ‖U.symm X‖ = 0 := by rw [← hsNorm_U, U.apply_symm_apply]; exact hX
  have he := norm_eq_zero.mp hn
  have hu := congrArg U he
  simpa only [U.apply_symm_apply, map_zero, Submodule.coe_zero] using congrArg (fun x : symmetricCarrier => (x : Mat)) hu

theorem fixed_space (X : symmetricCarrier) :
    transfer X = X ↔ ∃ c : ℂ, (X : Mat) = c • (1 : Mat) := by
  constructor
  · intro hX
    let Y : symmetricCarrier := ⟨(X : Mat)-stationary X, X.property.sub (stationary_mem X)⟩
    have ht : (Y : Mat).trace = 0 := by simp [Y, Matrix.trace_sub, stationary_trace]
    have hf : transfer Y = Y := by simp only [Y, map_sub, hX, stationary_fixed]
    have hn := tracezero_contraction Y ht
    rw [hf] at hn
    have hz : hsNorm Y = 0 := by nlinarith [hsNorm_nonneg Y]
    have he := hsNorm_zero_symmetric Y hz
    exact ⟨(X : Mat).trace/3, sub_eq_zero.mp he⟩
  · rintro ⟨c,hc⟩
    rw [hc, map_smul, transfer_one]

/-- The exact finite dimensionless gap on this trace-zero carrier. -/
theorem exact_gap :
    1 - eigenvalue 1 = (1/10 : ℝ) ∧
      (∀ i : Index, i ≠ 0 → eigenvalue i ≤ eigenvalue 1) := by
  constructor
  · norm_num [eigenvalue]
  · intro i hi
    simpa [eigenvalue] using tracezero_eigenvalue_bound i hi

def quotientStationary (q : FeatureSpace) : FeatureSpace :=
  U.symm ⟨stationary (U q), stationary_mem _⟩

theorem U_stationary (q : FeatureSpace) :
    (U (quotientStationary q) : Mat) = stationary (U q) := by
  change (U (U.symm _) : Mat) = _
  rw [U.apply_symm_apply]

theorem quotient_selfadjoint (q r : FeatureSpace) :
    ⟪quotientTransfer q,r⟫_ℂ = ⟪q,quotientTransfer r⟫_ℂ := by
  rw [← U_inner, ← U_inner, U_transfer, U_transfer]
  simpa only [pairing_trace] using transfer_selfadjoint (U q) (U r)

theorem quotient_hilbert_positive_contraction (q : FeatureSpace) :
    0 ≤ (⟪q,quotientTransfer q⟫_ℂ).re ∧ (⟪q,quotientTransfer q⟫_ℂ).re ≤ ‖q‖^2 := by
  have h := hilbert_positive_contraction (U q)
  rw [hsNorm_U] at h
  rw [← U_inner, U_transfer]
  simpa only [pairing_trace] using h

theorem quotient_mixing (n : ℕ) (q : FeatureSpace) :
    ‖quotientIterate n q-quotientStationary q‖ ≤
      (9/10 : ℝ)^n * ‖q-quotientStationary q‖ := by
  have h := mixing n (U q)
  have he (r : FeatureSpace) : hsNorm ((U r : Mat)-stationary (U q)) =
      ‖r-quotientStationary q‖ := by
    rw [← U_stationary]
    rw [← Submodule.coe_sub, ← map_sub]
    exact hsNorm_U _
  rw [← U_iterate, he, he] at h
  exact h


theorem eigenvector_norm_sq (i : Index) : hsNorm (eigenvector i)^2 = eigenNormSq i := by
  have h := eigenvector_pairing i i
  rw [pairing_self, if_pos rfl] at h
  exact Complex.ofReal_injective h

theorem eigenvector_nonzero (i : Index) : eigenvector i ≠ 0 := by
  intro h
  have hn := eigenvector_norm_sq i
  rw [h] at hn
  have hz : hsNorm (0 : Mat) = 0 := by simp [hsNorm]
  rw [hz] at hn
  have hp := eigenNormSq_positive i
  nlinarith

theorem quotient_iterate_trace (n : ℕ) (q : FeatureSpace) :
    FiniteQutritInvariantReconstruction.trace (quotientIterate n q) =
      FiniteQutritInvariantReconstruction.trace q := by
  change (U (quotientIterate n q) : Mat).trace = _
  rw [U_iterate, iterate_trace]
  rfl

theorem quotient_iterate_cone (n : ℕ) {q : FeatureSpace} (hq : q ∈ cone) :
    quotientIterate n q ∈ cone := by
  change (U (quotientIterate n q) : Mat).PosSemidef
  rw [U_iterate]
  exact iterate_positive n hq

theorem quotient_iterate_initial (n : ℕ) : quotientIterate n initial = initial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change quotientIterate n (quotientTransfer initial) = _
    rw [quotient_initial_fixed, ih]

variable (E : Type*) [Fintype E] [DecidableEq E]

/-- Actual system partial trace; no division by the spectator dimension. -/
def partialTrace (X : Matrix (Q × E) (Q × E) ℂ) : Matrix E E ℂ :=
  fun e f => ∑ a : Q, X (a,e) (a,f)

def relativeProjection (X : Matrix (Q × E) (Q × E) ℂ) : Matrix (Q × E) (Q × E) ℂ :=
  ((1/3 : ℂ) • (1 : Mat)) ⊗ₖ partialTrace E X

/-- Direct-sum Hilbert-Schmidt norm of the actual system blocks. Each block
has the factor 1/3 from the system pairing; there is no factor card(E). -/
def jointNorm (X : Matrix (Q × E) (Q × E) ℂ) : ℝ :=
  Real.sqrt (∑ e : E, ∑ f : E,
    hsNorm (FiniteQutritInvariantExamples.block E e f X)^2)

def jointPairing (X Y : Matrix (Q × E) (Q × E) ℂ) : ℂ :=
  ∑ e : E, ∑ f : E, pairing (FiniteQutritInvariantExamples.block E e f X)
    (FiniteQutritInvariantExamples.block E e f Y)

theorem partialTrace_block (X : Matrix (Q × E) (Q × E) ℂ) (e f : E) :
    partialTrace E X e f = (FiniteQutritInvariantExamples.block E e f X).trace := rfl

theorem relative_block (X : Matrix (Q × E) (Q × E) ℂ) (e f : E) :
    FiniteQutritInvariantExamples.block E e f (relativeProjection E X) =
      stationary (FiniteQutritInvariantExamples.block E e f X) := by
  ext a b
  simp [relativeProjection, FiniteQutritInvariantExamples.block, stationary,
    Matrix.kronecker_apply, Matrix.smul_apply, Matrix.one_apply, partialTrace_block,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem jointNorm_nonneg (X : Matrix (Q × E) (Q × E) ℂ) : 0 ≤ jointNorm E X :=
  Real.sqrt_nonneg _

theorem jointNorm_sq (X : Matrix (Q × E) (Q × E) ℂ) :
    jointNorm E X ^ 2 = ∑ e : E, ∑ f : E,
      hsNorm (FiniteQutritInvariantExamples.block E e f X)^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem jointPairing_self (X : Matrix (Q × E) (Q × E) ℂ) :
    jointPairing E X X = (jointNorm E X ^ 2 : ℝ) := by
  simp only [jointPairing, pairing_self, jointNorm_sq, Complex.ofReal_sum]

/-- A concrete Hilbert embedding of the joint matrix, as all its actual
weighted system blocks. This also covers a zero-dimensional spectator. -/
def jointEmbedding : Matrix (Q × E) (Q × E) ℂ →ₗ[ℂ]
    PiLp 2 (fun _ : E × E => EuclideanSpace ℂ (Q × Q)) where
  toFun X := WithLp.toLp 2 (fun ef => operatorEmbedding
    (FiniteQutritInvariantExamples.block E ef.1 ef.2 X))
  map_add' X Y := by
    ext ef ab
    change operatorEmbedding (FiniteQutritInvariantExamples.block E ef.1 ef.2 (X+Y)) ab = _
    rw [map_add, map_add]
    rfl
  map_smul' c X := by
    ext ef ab
    change operatorEmbedding (FiniteQutritInvariantExamples.block E ef.1 ef.2 (c • X)) ab = _
    rw [map_smul, map_smul]
    rfl

theorem jointEmbedding_inner (X Y : Matrix (Q × E) (Q × E) ℂ) :
    ⟪jointEmbedding E X,jointEmbedding E Y⟫_ℂ = jointPairing E X Y := by
  rw [PiLp.inner_apply]
  change (∑ ef : E × E, pairing (FiniteQutritInvariantExamples.block E ef.1 ef.2 X)
    (FiniteQutritInvariantExamples.block E ef.1 ef.2 Y)) = _
  rw [Fintype.sum_prod_type]
  rfl

theorem jointEmbedding_norm (X : Matrix (Q × E) (Q × E) ℂ) :
    ‖jointEmbedding E X‖ = jointNorm E X := by
  have h := jointEmbedding_inner E X X
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), RCLike.ofReal_eq_complex_ofReal,
    jointPairing_self] at h
  have hr : ‖jointEmbedding E X‖^2 = jointNorm E X^2 := by exact_mod_cast h
  nlinarith [norm_nonneg (jointEmbedding E X), jointNorm_nonneg E X]

theorem jointPairing_trace (X Y : Matrix (Q × E) (Q × E) ℂ) :
    jointPairing E X Y = (Xᴴ * Y).trace / 3 := by
  simp only [jointPairing, pairing_trace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, FiniteQutritInvariantExamples.block,
    LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type]
  simp only [← Finset.sum_div]
  congr 1
  conv_lhs =>
    arg 2
    ext e
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.sum_comm]

theorem amplified_iterate_block (n : ℕ) (X : Matrix (Q × E) (Q × E) ℂ) (e f : E) :
    FiniteQutritInvariantExamples.block E e f (amplifiedIterate E n X) =
      iterate n (FiniteQutritInvariantExamples.block E e f X) := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change FiniteQutritInvariantExamples.block E e f
      (amplifiedIterate E n (amplified E X)) = _
    rw [ih, amplified_block]
    rfl

theorem amplified_relative_fixed (X : Matrix (Q × E) (Q × E) ℂ) :
    amplified E (relativeProjection E X) = relativeProjection E X := by
  ext ⟨a,e⟩ ⟨b,f⟩
  have h : FiniteQutritInvariantExamples.block E e f
      (amplified E (relativeProjection E X)) =
      FiniteQutritInvariantExamples.block E e f (relativeProjection E X) := by
    rw [amplified_block, relative_block, stationary_fixed]
  exact congrArg (fun Z : Mat => Z a b) h

theorem relative_mem (X : Matrix (Q × E) (Q × E) ℂ) :
    relativeProjection E X ∈ FiniteQutritInvariantExamples.matrixCarrier E := by
  intro e f
  rw [relative_block]
  exact stationary_mem _

/-- All finite spectators, including the empty type, and arbitrary complex blocks. -/
theorem spectator_mixing (n : ℕ) (X : Matrix (Q × E) (Q × E) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier E) :
    jointNorm E (amplifiedIterate E n X-relativeProjection E X) ≤
      (9/10 : ℝ)^n * jointNorm E (X-relativeProjection E X) := by
  have hh : jointNorm E (amplifiedIterate E n X-relativeProjection E X)^2 ≤
      ((9/10 : ℝ)^n * jointNorm E (X-relativeProjection E X))^2 := by
    rw [mul_pow, jointNorm_sq, jointNorm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro f _
    have hm := mixing n ⟨FiniteQutritInvariantExamples.block E e f X, hX e f⟩
    have h0 := hsNorm_nonneg
      (iterate n (FiniteQutritInvariantExamples.block E e f X)-
        stationary (FiniteQutritInvariantExamples.block E e f X))
    have h1 := hsNorm_nonneg
      (FiniteQutritInvariantExamples.block E e f X-
        stationary (FiniteQutritInvariantExamples.block E e f X))
    simp only [map_sub, amplified_iterate_block, relative_block]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 9/10) n]
  nlinarith [jointNorm_nonneg E (amplifiedIterate E n X-relativeProjection E X),
    mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 9/10) n)
      (jointNorm_nonneg E (X-relativeProjection E X))]

theorem spectator_fixed_space (X : Matrix (Q × E) (Q × E) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier E) :
    amplified E X = X ↔ X = relativeProjection E X := by
  constructor
  · intro hf
    ext ⟨a,e⟩ ⟨b,f⟩
    have hb : transfer (FiniteQutritInvariantExamples.block E e f X) =
        FiniteQutritInvariantExamples.block E e f X := by
      rw [← amplified_block, hf]
    obtain ⟨c,hc⟩ := (fixed_space ⟨_,hX e f⟩).mp hb
    change FiniteQutritInvariantExamples.block E e f X = c • (1 : Mat) at hc
    have hs : FiniteQutritInvariantExamples.block E e f X =
        stationary (FiniteQutritInvariantExamples.block E e f X) := by
      rw [hc]
      simp [stationary, Matrix.trace_smul, Matrix.trace_one]
    rw [← relative_block E X e f] at hs
    exact congrArg (fun Z : Mat => Z a b) hs
  · intro hf
    conv_lhs => rw [hf]
    rw [amplified_relative_fixed, ← hf]

theorem spectator_fixed_tensors (X : Matrix (Q × E) (Q × E) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier E) :
    amplified E X = X ↔ ∃ σ : Matrix E E ℂ, X = (1 : Mat) ⊗ₖ σ := by
  constructor
  · intro hf
    refine ⟨(1/3 : ℂ) • partialTrace E X, ?_⟩
    calc
      X = relativeProjection E X := (spectator_fixed_space E X hX).mp hf
      _ = (1 : Mat) ⊗ₖ ((1/3 : ℂ) • partialTrace E X) := by
        ext ⟨a,e⟩ ⟨b,f⟩
        simp [relativeProjection, Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul]
        ring
  · rintro ⟨σ,rfl⟩
    rw [amplified_product, transfer_one]

theorem relative_zero_of_partialTrace_zero (X : Matrix (Q × E) (Q × E) ℂ)
    (hX : partialTrace E X = 0) : relativeProjection E X = 0 := by
  simp [relativeProjection, hX]

theorem spectator_tracezero_contraction (n : ℕ) (X : Matrix (Q × E) (Q × E) ℂ)
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier E)
    (ht : partialTrace E X = 0) :
    jointNorm E (amplifiedIterate E n X) ≤ (9/10 : ℝ)^n * jointNorm E X := by
  simpa [relative_zero_of_partialTrace_zero E X ht] using spectator_mixing E n X hX


theorem empty_spectator_norm (X : Matrix (Q × PEmpty) (Q × PEmpty) ℂ) :
    jointNorm PEmpty X = 0 := by simp [jointNorm]

theorem empty_spectator_mixing (n : ℕ) (X : Matrix (Q × PEmpty) (Q × PEmpty) ℂ) :
    jointNorm PEmpty (amplifiedIterate PEmpty n X-relativeProjection PEmpty X) ≤
      (9/10 : ℝ)^n * jointNorm PEmpty (X-relativeProjection PEmpty X) :=
  spectator_mixing PEmpty n X (by intro e; cases e)

end SKEFTHawking.QuantumNetwork.FiniteQutritAveragedMixing
