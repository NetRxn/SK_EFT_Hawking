import SKEFTHawking.FinitePositiveKernel
import SKEFTHawking.QuantumNetwork.FiniteGibbsClock

/-! Finite null-quotient dynamics and Gibbs observable Gram spaces.
All descended maps are complex linear. No continuum or generator claim. -/
noncomputable section
open Matrix
open scoped ComplexOrder InnerProductSpace
namespace SKEFTHawking.FinitePositiveKernel
variable {ι : Type*} [Fintype ι] {K : Matrix ι ι ℂ} (hK : K.PosSemidef)

/-- The coefficient map preserves exactly the subspace removed by reconstruction. -/
def NullPreserving (L : Coefficients hK →ₗ[ℂ] Coefficients hK) : Prop :=
  nullSpace K hK ≤ (nullSpace K hK).comap L

/-- Linear descent through the algebraic quotient, transported to the constructed space. -/
def descend (L : Coefficients hK →ₗ[ℂ] Coefficients hK) (hL : NullPreserving hK L) :
    Space K hK →ₗ[ℂ] Space K hK :=
  (quotientEquiv K hK).toLinearMap.comp
    (((nullSpace K hK).mapQ (nullSpace K hK) L hL).comp
      (quotientEquiv K hK).symm.toLinearMap)

theorem quotientEquiv_mk (x : Coefficients hK) :
    quotientEquiv K hK (Submodule.Quotient.mk x) = mk K hK x :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

theorem descend_mk (L : Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hL : NullPreserving hK L) (x : Coefficients hK) :
    descend hK L hL (mk K hK x) = mk K hK (L x) := by
  rw [← quotientEquiv_mk hK x]
  simp only [descend, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.mapQ_apply]
  exact quotientEquiv_mk hK _

theorem nullPreserving_id : NullPreserving hK LinearMap.id := by
  intro x hx
  exact hx

theorem nullPreserving_comp {L M : Coefficients hK →ₗ[ℂ] Coefficients hK}
    (hL : NullPreserving hK L) (hM : NullPreserving hK M) :
    NullPreserving hK (L.comp M) := fun _ hx => hL (hM hx)

theorem descend_id : descend hK LinearMap.id (nullPreserving_id hK) = LinearMap.id := by
  ext z
  obtain ⟨x, rfl⟩ := mk_surjective K hK z
  exact descend_mk hK _ _ x

theorem descend_comp {L M : Coefficients hK →ₗ[ℂ] Coefficients hK}
    (hL : NullPreserving hK L) (hM : NullPreserving hK M) :
    descend hK (L.comp M) (nullPreserving_comp hK hL hM) =
      (descend hK L hL).comp (descend hK M hM) := by
  ext z
  obtain ⟨x, rfl⟩ := mk_surjective K hK z
  simp only [descend_mk, LinearMap.comp_apply]

/-- Iterating a descended map agrees with iterating on representatives. -/
theorem descend_iterate (L : Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hL : NullPreserving hK L) (n : ℕ) (x : Coefficients hK) :
    (descend hK L hL)^[n] (mk K hK x) = mk K hK (L^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih, descend_mk]

theorem nullPreserving_pow (L : Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hL : NullPreserving hK L) (n : ℕ) : NullPreserving hK (L ^ n) := by
  induction n with
  | zero => exact nullPreserving_id hK
  | succ n ih => exact nullPreserving_comp hK ih hL

/-- Powers in the endomorphism algebra commute with descent. -/
theorem descend_pow (L : Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hL : NullPreserving hK L) (n : ℕ) :
    descend hK (L ^ n) (nullPreserving_pow hK L hL n) = (descend hK L hL) ^ n := by
  ext z
  obtain ⟨x, rfl⟩ := mk_surjective K hK z
  rw [descend_mk]
  simpa only [Module.End.pow_apply] using (descend_iterate hK L hL n x).symm

/-- Kernel energy is the squared quotient norm. -/
theorem norm_mk_sq (x : Coefficients hK) :
    ‖mk K hK x‖ ^ 2 = (pairing K x x).re := by
  rw [← inner_mk K hK]
  exact norm_sq_eq_re_inner (𝕜 := ℂ) (mk K hK x)

/-- Energy-decreasing linear maps preserve null vectors. -/
theorem nullPreserving_of_energy (L : Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hE : ∀ x, (pairing K (L x) (L x)).re ≤ (pairing K x x).re) :
    NullPreserving hK L := by
  intro x hx
  apply (mem_nullSpace_iff K hK _).mpr
  apply (mk_eq_zero_iff K hK _).mp
  apply norm_eq_zero.mp
  have hn := hE x
  rw [← norm_mk_sq hK, ← norm_mk_sq hK] at hn
  have hx0 := (mk_eq_zero_iff K hK x).mpr ((mem_nullSpace_iff K hK x).mp hx)
  rw [hx0, norm_zero] at hn
  nlinarith [norm_nonneg (mk K hK (L x))]

theorem descend_norm_le (L : Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hE : ∀ x, (pairing K (L x) (L x)).re ≤ (pairing K x x).re)
    (z : Space K hK) :
    ‖descend hK L (nullPreserving_of_energy hK L hE) z‖ ≤ ‖z‖ := by
  obtain ⟨x, rfl⟩ := mk_surjective K hK z
  rw [descend_mk]
  have hn := hE x
  rw [← norm_mk_sq hK, ← norm_mk_sq hK] at hn
  nlinarith [norm_nonneg (mk K hK (L x)), norm_nonneg (mk K hK x)]

/-- A contractive operator on the complete reconstructed space. -/
def descendContraction (L : Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hE : ∀ x, (pairing K (L x) (L x)).re ≤ (pairing K x x).re) :
    Space K hK →L[ℂ] Space K hK :=
  (descend hK L (nullPreserving_of_energy hK L hE)).mkContinuous 1
    (fun z => by simpa using descend_norm_le hK L hE z)

/-- Inner-product preservation supplies null preservation without faithfulness. -/
theorem nullPreserving_of_pairing (L : Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hP : ∀ x y, pairing K (L x) (L y) = pairing K x y) : NullPreserving hK L :=
  nullPreserving_of_energy hK L (fun x => le_of_eq (congrArg Complex.re (hP x x)))

def descendIsometry (L : Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hP : ∀ x y, pairing K (L x) (L y) = pairing K x y) :
    Space K hK →ₗᵢ[ℂ] Space K hK :=
  (descend hK L (nullPreserving_of_pairing hK L hP)).isometryOfInner (by
    intro z w
    obtain ⟨x, rfl⟩ := mk_surjective K hK z
    obtain ⟨y, rfl⟩ := mk_surjective K hK w
    simp only [descend_mk, inner_mk]
    exact hP x y)

/-- A right inverse modulo null vectors gives a surjective isometry of the quotient. -/
def descendUnitary (L M : Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hP : ∀ x y, pairing K (L x) (L y) = pairing K x y)
    (hInv : ∀ x, L (M x) - x ∈ nullSpace K hK) :
    Space K hK ≃ₗᵢ[ℂ] Space K hK :=
  LinearIsometryEquiv.ofSurjective (descendIsometry hK L hP) (by
    intro z
    obtain ⟨x, rfl⟩ := mk_surjective K hK z
    refine ⟨mk K hK (M x), ?_⟩
    change descend hK L _ (mk K hK (M x)) = _
    rw [descend_mk, mk_eq_mk_iff]
    exact (mem_nullSpace_iff K hK _).mp (hInv x))

theorem descendUnitary_mk (L M : Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hP : ∀ x y, pairing K (L x) (L y) = pairing K x y)
    (hInv : ∀ x, L (M x) - x ∈ nullSpace K hK) (x : Coefficients hK) :
    descendUnitary hK L M hP hInv (mk K hK x) = mk K hK (L x) :=
  descend_mk hK L _ x

/-- A matrix acts on kernel coefficients independently of their derived seminorm. -/
def coefficientMap (A : Matrix ι ι ℂ) : Coefficients hK →ₗ[ℂ] Coefficients hK :=
  A.mulVecLin

omit hK in
theorem pairing_mulVec (A : Matrix ι ι ℂ) (x y : ι → ℂ) :
    pairing K (A *ᵥ x) (A *ᵥ y) = pairing (Aᴴ * K * A) x y := by
  simp only [pairing, star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, mul_assoc]

/-- The PSD defect controls every complex coefficient vector. -/
theorem energy_le_of_defect (A : Matrix ι ι ℂ) (hA : (K - Aᴴ * K * A).PosSemidef)
    (x : Coefficients hK) :
    (pairing K (coefficientMap hK A x) (coefficientMap hK A x)).re ≤
      (pairing K x x).re := by
  have hn := (hA.dotProduct_mulVec_nonneg x).1
  change (pairing K (A *ᵥ x) (A *ᵥ x)).re ≤ _
  rw [pairing_mulVec]
  simpa only [pairing, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Complex.zero_re,
    sub_nonneg] using hn

def matrixContraction (A : Matrix ι ι ℂ) (hA : (K - Aᴴ * K * A).PosSemidef) :
    Space K hK →L[ℂ] Space K hK :=
  descendContraction hK (coefficientMap hK A) (energy_le_of_defect hK A hA)

theorem matrixContraction_norm_le (A : Matrix ι ι ℂ)
    (hA : (K - Aᴴ * K * A).PosSemidef) (z : Space K hK) :
    ‖matrixContraction hK A hA z‖ ≤ ‖z‖ :=
  descend_norm_le hK _ (energy_le_of_defect hK A hA) z

/-- Matrix invariance yields quotient inner-product preservation even for singular kernels. -/
theorem matrix_pairing_of_invariance (A : Matrix ι ι ℂ) (hA : Aᴴ * K * A = K)
    (x y : Coefficients hK) :
    pairing K (coefficientMap hK A x) (coefficientMap hK A y) = pairing K x y := by
  change pairing K (A *ᵥ x) (A *ᵥ y) = _
  rw [pairing_mulVec, hA]

/-- Algebraic coefficient group laws descend to the reconstructed space. -/
theorem descend_group (L : ℝ → Coefficients hK →ₗ[ℂ] Coefficients hK)
    (hL : ∀ t, NullPreserving hK (L t))
    (hadd : ∀ s t, L (s + t) = (L s).comp (L t)) (s t : ℝ) :
    descend hK (L (s + t)) (hL (s + t)) =
      (descend hK (L s) (hL s)).comp (descend hK (L t) (hL t)) := by
  ext z
  obtain ⟨x, rfl⟩ := mk_surjective K hK z
  simp only [LinearMap.comp_apply, descend_mk, hadd]

section SingularExample

def singularProjection : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 0]

theorem singularProjection_not_isUnit : ¬ IsUnit singularProjection := by
  rw [Matrix.isUnit_iff_isUnit_det]
  norm_num [singularProjection, Matrix.det_fin_two]

theorem singularProjection_preserves :
    singularProjectionᴴ * degenerate * singularProjection = degenerate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [singularProjection, degenerate, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]

theorem singularProjection_pairing (x y : Coefficients degenerate_posSemidef) :
    pairing degenerate (coefficientMap degenerate_posSemidef singularProjection x)
      (coefficientMap degenerate_posSemidef singularProjection y) = pairing degenerate x y := by
  change pairing degenerate (singularProjection *ᵥ x) (singularProjection *ᵥ y) = _
  rw [pairing_mulVec, singularProjection_preserves]

theorem singularProjection_class (x : Coefficients degenerate_posSemidef) :
    mk degenerate degenerate_posSemidef (singularProjection *ᵥ x) =
      mk degenerate degenerate_posSemidef x := by
  unfold Coefficients at x
  apply (mk_eq_mk_iff _ _ _ _).mpr
  change pairing degenerate (singularProjection *ᵥ x - (x : Fin 2 → ℂ)) (singularProjection *ᵥ x - (x : Fin 2 → ℂ)) = 0
  simp [pairing, singularProjection, degenerate, dotProduct, mulVec, Fin.sum_univ_two]

/-- A singular coefficient operator acts as identity on a nonzero quotient. -/
theorem singularProjection_descend_identity :
    descend degenerate_posSemidef (coefficientMap degenerate_posSemidef singularProjection)
      (nullPreserving_of_pairing _ _ singularProjection_pairing) = LinearMap.id := by
  ext z
  obtain ⟨x, rfl⟩ := mk_surjective degenerate degenerate_posSemidef z
  rw [descend_mk]
  exact singularProjection_class x

/-- The strict contraction has a nonzero PSD defect even though its coefficients are singular. -/
theorem halfProjection_defect :
    degenerate - (((1/2 : ℂ) • singularProjection)ᴴ * degenerate *
      ((1/2 : ℂ) • singularProjection)) = (3/4 : ℝ) • degenerate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [singularProjection, degenerate, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.real_smul, map_ofNat]

theorem halfProjection_defect_posSemidef :
    (degenerate - (((1/2 : ℂ) • singularProjection)ᴴ * degenerate *
      ((1/2 : ℂ) • singularProjection))).PosSemidef := by
  rw [halfProjection_defect]
  exact degenerate_posSemidef.smul (by norm_num : (0 : ℝ) ≤ 3/4)

/-- The contraction acts by one half on every quotient vector, including a surviving feature. -/
theorem halfProjection_action (z : Space degenerate degenerate_posSemidef) :
    matrixContraction degenerate_posSemidef ((1/2 : ℂ) • singularProjection)
      halfProjection_defect_posSemidef z = (1/2 : ℂ) • z := by
  obtain ⟨x, rfl⟩ := mk_surjective degenerate degenerate_posSemidef z
  change descend degenerate_posSemidef _ _ (mk _ _ x) = _
  rw [descend_mk]
  change mk _ _ (((1/2 : ℂ) • singularProjection) *ᵥ x) = _
  rw [Matrix.smul_mulVec]
  change mkLinear degenerate degenerate_posSemidef
    ((1/2 : ℂ) • (singularProjection *ᵥ x : Coefficients degenerate_posSemidef)) = _
  exact ((mkLinear degenerate degenerate_posSemidef).map_smul (1/2 : ℂ)
    (singularProjection *ᵥ x)).trans
      (congrArg (fun z => (1/2 : ℂ) • z) (singularProjection_class x))

theorem halfProjection_feature_strict :
    ‖matrixContraction degenerate_posSemidef ((1/2 : ℂ) • singularProjection)
      halfProjection_defect_posSemidef (feature _ degenerate_posSemidef 0)‖ <
        ‖feature _ degenerate_posSemidef 0‖ := by
  rw [halfProjection_action, norm_smul]
  have hp := norm_pos_iff.mpr degenerate_feature_nonzero
  norm_num at ⊢
  linarith

end SingularExample

namespace GibbsObservable
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix-unit Gram kernel, conjugate-linear in the first observable. -/
def gram (ρ : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  fun p q => ((Matrix.single q.1 q.2 1) * ρ * (Matrix.single p.1 p.2 1)ᴴ).trace

theorem gram_posSemidef {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) : (gram ρ).PosSemidef := by
  letI := Matrix.toMatrixSeminormedAddCommGroup ρ hρ
  letI := Matrix.toMatrixInnerProductSpace ρ hρ
  exact Matrix.posSemidef_gram ℂ (fun p : n × n => Matrix.single p.1 p.2 (1 : ℂ))

/-- Explicit matrix-unit Gram entries; for diagonal density the column index carries its weight. -/
theorem gram_entry (ρ : Matrix n n ℂ) (i j k l : n) :
    gram ρ (i, j) (k, l) = if i = k then ρ l j else 0 := by
  simp [gram, Matrix.trace, Matrix.single_apply, ite_and]

/-- Synthesize the observable described by its matrix-unit coefficients. -/
def synth (c : n × n → ℂ) : Matrix n n ℂ :=
  ∑ p, c p • Matrix.single p.1 p.2 1

theorem synth_apply (c : n × n → ℂ) (i j : n) : synth c i j = c (i, j) := by
  simp [synth, Matrix.sum_apply, Fintype.sum_prod_type, Matrix.single_apply, ite_and]

theorem synth_flat (X : Matrix n n ℂ) : synth (fun p => X p.1 p.2) = X := by
  ext i j
  exact synth_apply _ _ _

/-- The complete coefficient form equals the Gibbs-weighted observable trace. -/
theorem pairing_gram {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (c d : n × n → ℂ) :
    pairing (gram ρ) c d = (synth d * ρ * (synth c)ᴴ).trace := by
  letI := Matrix.toMatrixSeminormedAddCommGroup ρ hρ
  letI := Matrix.toMatrixInnerProductSpace ρ hρ
  exact Matrix.star_dotProduct_gram_mulVec
    (fun p : n × n => Matrix.single p.1 p.2 (1 : ℂ)) c d

/-- Faithfulness excludes zero weighted norm for a nonzero observable. -/
theorem trace_weighted_eq_zero {ρ : Matrix n n ℂ} (hρ : ρ.PosDef)
    (X : Matrix n n ℂ) (hx : (X * ρ * Xᴴ).trace = 0) : X = 0 := by
  obtain ⟨y, hy, rfl⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hρ.isStrictlyPositive
  rw [star_eq_conjTranspose] at hx
  have hh : ((X * yᴴ) * (X * yᴴ)ᴴ).trace = 0 := by
    simpa [Matrix.conjTranspose_mul, mul_assoc] using hx
  have hz := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hh
  have hi : IsUnit yᴴ := by simpa only [star_eq_conjTranspose] using hy.star
  exact hi.mul_left_eq_zero.mp hz

/-- The matrix-unit Gram quotient is faithful whenever its density is faithful. -/
theorem mk_injective {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) :
    Function.Injective (mk (gram ρ) (gram_posSemidef hρ.posSemidef)) := by
  intro c d h
  have he := (mk_eq_mk_iff _ _ _ _).mp h
  rw [pairing_gram hρ.posSemidef] at he
  have hz := trace_weighted_eq_zero hρ _ he
  apply funext
  intro p
  have hp := congrArg (fun X => X p.1 p.2) hz
  rw [synth_apply] at hp
  exact sub_eq_zero.mp hp

/-- The reconstructed matrix-unit class of an observable. -/
def observable {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (X : Matrix n n ℂ) :
    Space (gram ρ) (gram_posSemidef hρ) := mk _ _ (fun p => X p.1 p.2)

theorem inner_observable {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (X Y : Matrix n n ℂ) :
    ⟪observable hρ X, observable hρ Y⟫_ℂ = (Y * ρ * Xᴴ).trace := by
  rw [observable, observable, inner_mk, pairing_gram hρ, synth_flat, synth_flat]

/-- Matrix-unit synthesis is a linear equivalence before quotienting. -/
def synthEquiv {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    Coefficients (gram_posSemidef hρ) ≃ₗ[ℂ] Matrix n n ℂ where
  toFun := synth
  invFun X := fun p => X p.1 p.2
  left_inv c := by apply funext; intro p; exact synth_apply c p.1 p.2
  right_inv := synth_flat
  map_add' c d := by ext i j; simp only [Matrix.add_apply, synth_apply]; rfl
  map_smul' z c := by ext i j; simp only [Matrix.smul_apply, synth_apply]; rfl

def observableLinear {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    Matrix n n ℂ →ₗ[ℂ] Space (gram ρ) (gram_posSemidef hρ) :=
  (mkLinear _ _).comp (synthEquiv hρ).symm.toLinearMap

theorem observable_smul {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (z : ℂ) (X : Matrix n n ℂ) : observable hρ (z • X) = z • observable hρ X :=
  (observableLinear hρ).map_smul z X

theorem observable_surjective {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    Function.Surjective (observable hρ) := by
  intro z
  obtain ⟨c, rfl⟩ := mk_surjective (gram ρ) (gram_posSemidef hρ) z
  refine ⟨synth c, ?_⟩
  apply congrArg (mk _ _)
  apply funext
  intro p
  exact synth_apply c p.1 p.2

theorem observable_injective {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) :
    Function.Injective (observable hρ.posSemidef) := by
  intro X Y h
  have hh := mk_injective hρ h
  ext i j
  exact congrFun hh (i, j)

theorem observable_eq_zero_iff {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (X : Matrix n n ℂ) :
    observable hρ.posSemidef X = 0 ↔ X = 0 := by
  constructor
  · intro h
    apply observable_injective hρ
    exact h.trans (map_zero (observableLinear hρ.posSemidef)).symm
  · intro h
    subst X
    exact map_zero (observableLinear hρ.posSemidef)

namespace Clock
open QuantumNetwork.FiniteGibbsClock
variable [Nonempty n] {H : Matrix n n ℂ} (hH : H.IsHermitian) (β : ℝ)

omit [Nonempty n] in
/-- Conjugation preserves the trace by its actual exponential inverse. -/
theorem trace_conjugate (A X : Matrix n n ℂ) (c : ℂ) :
    (conjugate A c X).trace = X.trace := by
  have hc := expCoeff_cancel A (-c)
  simp only [neg_neg] at hc
  rw [conjugate, Matrix.trace_mul_comm, ← mul_assoc, hc, one_mul]

omit [Nonempty n] in
/-- Gibbs covariance commutes with every exponential of its Hamiltonian. -/
theorem expCoeff_commutes_gibbs (c : ℂ) : Commute (expCoeff H c) (gibbs H β) := by
  have hc : Commute (expCoeff H c) (boltzmann H β) :=
    (((Commute.refl H).smul_left c).smul_right (-β : ℝ)).exp
  exact hc.smul_right _

theorem modular_gibbs_fixed (s : ℝ) : modular hH β s (gibbs H β) = gibbs H β := by
  rw [modular_conjugate, conjugate, (expCoeff_commutes_gibbs β _).eq,
    mul_assoc, expCoeff_cancel, mul_one]

/-- The weighted Gram form is invariant under the existing linear modular automorphism. -/
theorem modular_weighted_pairing (s : ℝ) (X Y : Matrix n n ℂ) :
    (modular hH β s Y * gibbs H β * (modular hH β s X)ᴴ).trace =
      (Y * gibbs H β * Xᴴ).trace := by
  rw [← modular_star, ← modular_gibbs_fixed hH β s, ← modular_mul, ← modular_mul]
  rw [modular_gibbs_fixed]
  exact trace_conjugate _ _ _

/-- The existing modular operation packaged as a complex linear map on observables. -/
def modularLinear (s : ℝ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := modular hH β s
  map_add' := modular_add hH β s
  map_smul' := modular_smul hH β s

/-- The actual observable automorphism in matrix-unit coordinates. -/
def modularCoefficients (s : ℝ) :
    Coefficients (gram_posSemidef (gibbs_posDef hH β).posSemidef) →ₗ[ℂ]
      Coefficients (gram_posSemidef (gibbs_posDef hH β).posSemidef) :=
  (synthEquiv (gibbs_posDef hH β).posSemidef).symm.toLinearMap.comp
    ((modularLinear hH β s).comp (synthEquiv (gibbs_posDef hH β).posSemidef).toLinearMap)

theorem synth_modularCoefficients (s : ℝ)
    (c : Coefficients (gram_posSemidef (gibbs_posDef hH β).posSemidef)) :
    synth (modularCoefficients hH β s c) = modular hH β s (synth c) :=
  synth_flat (modular hH β s (synth c))

theorem modularCoefficients_pairing (s : ℝ)
    (c d : Coefficients (gram_posSemidef (gibbs_posDef hH β).posSemidef)) :
    pairing (gram (gibbs H β)) (modularCoefficients hH β s c) (modularCoefficients hH β s d) =
      pairing (gram (gibbs H β)) c d := by
  rw [pairing_gram (gibbs_posDef hH β).posSemidef,
    pairing_gram (gibbs_posDef hH β).posSemidef,
    synth_modularCoefficients, synth_modularCoefficients]
  exact modular_weighted_pairing hH β s _ _

theorem modularCoefficients_inverse (s : ℝ)
    (c : Coefficients (gram_posSemidef (gibbs_posDef hH β).posSemidef)) :
    modularCoefficients hH β s (modularCoefficients hH β (-s) c) = c := by
  apply (synthEquiv (gibbs_posDef hH β).posSemidef).injective
  change synth (modularCoefficients hH β s (modularCoefficients hH β (-s) c)) = synth c
  rw [synth_modularCoefficients, synth_modularCoefficients, ← modular_group]
  simp only [add_neg_cancel, modular_zero]

theorem modularCoefficients_inverse_null (s : ℝ)
    (c : Coefficients (gram_posSemidef (gibbs_posDef hH β).posSemidef)) :
    modularCoefficients hH β s (modularCoefficients hH β (-s) c) - c ∈
      nullSpace _ (gram_posSemidef (gibbs_posDef hH β).posSemidef) := by
  rw [modularCoefficients_inverse, sub_self]
  exact Submodule.zero_mem _

/-- Finite Gibbs modular dynamics as a unitary map of the reconstructed Gram space. -/
def quotientModular (s : ℝ) :
    Space _ (gram_posSemidef (gibbs_posDef hH β).posSemidef) ≃ₗᵢ[ℂ]
      Space _ (gram_posSemidef (gibbs_posDef hH β).posSemidef) :=
  descendUnitary (gram_posSemidef (gibbs_posDef hH β).posSemidef)
    (modularCoefficients hH β s) (modularCoefficients hH β (-s))
    (modularCoefficients_pairing hH β s) (modularCoefficients_inverse_null hH β s)

theorem quotientModular_observable (s : ℝ) (X : Matrix n n ℂ) :
    quotientModular hH β s (observable (gibbs_posDef hH β).posSemidef X) =
      observable (gibbs_posDef hH β).posSemidef (modular hH β s X) := by
  unfold quotientModular observable
  rw [descendUnitary_mk]
  apply congrArg (mk (gram (gibbs H β)) (gram_posSemidef (gibbs_posDef hH β).posSemidef))
  apply (synthEquiv (gibbs_posDef hH β).posSemidef).injective
  change synth (modularCoefficients hH β s (fun p => X p.1 p.2)) =
    synth (fun p => modular hH β s X p.1 p.2)
  rw [synth_modularCoefficients, synth_flat, synth_flat]

theorem quotientModular_zero
    (z : Space _ (gram_posSemidef (gibbs_posDef hH β).posSemidef)) :
    quotientModular hH β 0 z = z := by
  obtain ⟨X, rfl⟩ := observable_surjective (gibbs_posDef hH β).posSemidef z
  rw [quotientModular_observable, modular_zero]

theorem quotientModular_group (s t : ℝ)
    (z : Space _ (gram_posSemidef (gibbs_posDef hH β).posSemidef)) :
    quotientModular hH β (s + t) z = quotientModular hH β s (quotientModular hH β t z) := by
  obtain ⟨X, rfl⟩ := observable_surjective (gibbs_posDef hH β).posSemidef z
  rw [quotientModular_observable, quotientModular_observable, quotientModular_observable,
    modular_group]

theorem quotientModular_inverse (s : ℝ)
    (z : Space _ (gram_posSemidef (gibbs_posDef hH β).posSemidef)) :
    quotientModular hH β (-s) (quotientModular hH β s z) = z := by
  rw [← quotientModular_group, neg_add_cancel, quotientModular_zero]

/-- The original signed comparison holds on every reconstructed observable class. -/
theorem quotientModular_eq_heisenberg (s ℏ : ℝ) (hℏ : 0 < ℏ) (X : Matrix n n ℂ) :
    quotientModular hH β s (observable (gibbs_posDef hH β).posSemidef X) =
      observable (gibbs_posDef hH β).posSemidef (heisenberg H ℏ (-β * ℏ * s) X) := by
  rw [quotientModular_observable, modular_eq_heisenberg hH β s ℏ hℏ]

/-- The off-diagonal Gibbs observable remains nonzero in the quotient. -/
theorem twoLevel_observable_nonzero (Δ β : ℝ) :
    observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef E01 ≠ 0 := by
  intro h
  exact E01_ne_zero ((observable_eq_zero_iff (gibbs_posDef (twoLevel_hermitian Δ) β) E01).mp h)

theorem twoLevel_quotient_phase (Δ β s : ℝ) :
    quotientModular (twoLevel_hermitian Δ) β s
      (observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef E01) =
      Complex.exp (Complex.I * β * Δ * s) •
        observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef E01 := by
  rw [quotientModular_observable, twoLevel_phase, observable_smul]

theorem twoLevel_quotient_sign_flip {Δ β : ℝ} (hΔ : 0 < Δ) (hβ : 0 < β) :
    quotientModular (twoLevel_hermitian Δ) β (Real.pi / (β * Δ))
      (observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef E01) =
      -observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef E01 := by
  rw [quotientModular_observable, twoLevel_sign_flip hΔ hβ]
  exact map_neg (observableLinear (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef) E01

theorem twoLevel_quotient_nontrivial {Δ β : ℝ} (hΔ : 0 < Δ) (hβ : 0 < β) :
    quotientModular (twoLevel_hermitian Δ) β (Real.pi / (β * Δ))
      (observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef E01) ≠
        observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef E01 := by
  rw [quotientModular_observable]
  intro he
  exact twoLevel_nontrivial hΔ hβ
    (observable_injective (gibbs_posDef (twoLevel_hermitian Δ) β) he)

end Clock

end GibbsObservable

end SKEFTHawking.FinitePositiveKernel
