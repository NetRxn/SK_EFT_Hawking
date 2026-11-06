import SKEFTHawking.ADW.GaussianAuxiliaryCompensation
import SKEFTHawking.ADW.FiniteGrassmannCoframe

/-!
# Finite Grassmann evaluation

C1 of the regulated auxiliary construction. The norm is transported from the
actual finite exterior basis, and formal series are evaluated by finite total
degree truncation under a proved common nilpotence budget. Actual global and
local B1 coframes discharge that budget at 4V.

The finite exponential is defined algebraically. The multinomial expansion
retains the product of coordinate factorials. No normed multiplication,
commutative structure on the full exterior algebra, integral identity, physical
state, source-action correspondence or publication acceptance is asserted here.
-/
noncomputable section
open scoped BigOperators IsMulCommutative
namespace SKEFTHawking.ADW.FiniteGrassmannEvaluation
open FiniteGrassmannCoframe

def grassmannBasis (L : Torus) :
    Module.Basis (Finset (Fin (4 * volume L * 2))) ℂ (Grassmann L) :=
  (coordinateBasis L).ExteriorAlgebra

def grassmannCoordinates (L : Torus) :
    Grassmann L ≃ₗ[ℂ] (Finset (Fin (4 * volume L * 2)) → ℂ) :=
  (grassmannBasis L).equivFun

abbrev grassmannNormedAddCommGroup (L : Torus) : NormedAddCommGroup (Grassmann L) :=
  NormedAddCommGroup.induced _ _ (grassmannCoordinates L) (grassmannCoordinates L).injective

scoped instance grassmann_normedAddCommGroup (L : Torus) : NormedAddCommGroup (Grassmann L) :=
  grassmannNormedAddCommGroup L

scoped instance grassmann_normedSpace_complex (L : Torus) : NormedSpace ℂ (Grassmann L) :=
  NormedSpace.induced ℂ _ _ (grassmannCoordinates L)

scoped instance grassmann_normedSpace_real (L : Torus) : NormedSpace ℝ (Grassmann L) :=
  NormedSpace.restrictScalars ℝ ℂ _

instance grassmann_finiteDimensional (L : Torus) : FiniteDimensional ℂ (Grassmann L) :=
  (grassmannBasis L).finiteDimensional_of_finite

scoped instance grassmann_complete (L : Torus) : CompleteSpace (Grassmann L) :=
  FiniteDimensional.complete ℂ _

theorem grassmann_norm_eq_coordinates (L : Torus) (g : Grassmann L) :
    ‖g‖ = ‖grassmannCoordinates L g‖ := rfl

theorem grassmann_norm_zero_iff (L : Torus) (g : Grassmann L) :
    ‖g‖ = 0 ↔ g = 0 := norm_eq_zero

theorem coordinates_injective (L : Torus) : Function.Injective (grassmannCoordinates L) :=
  (grassmannCoordinates L).injective

/-- Finite algebraic exponential, with no reference to an integral. -/
def nilExp {A : Type*} [Ring A] [Algebra ℂ A] (M : ℕ) (z : A) : A :=
  ∑ k ∈ Finset.range (M + 1), (k.factorial : ℂ)⁻¹ • z ^ k

@[simp] theorem nilExp_zero_cutoff {A : Type*} [Ring A] [Algebra ℂ A] (z : A) :
    nilExp 0 z = 1 := by simp [nilExp]

@[simp] theorem nilExp_zero {A : Type*} [Ring A] [Algebra ℂ A] (M : ℕ) :
    nilExp M (0 : A) = 1 := by
  simp [nilExp, Finset.sum_range_succ']

theorem map_nilExp {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (M : ℕ) (z : A) :
    f (nilExp M z) = nilExp M (f z) := by simp [nilExp, map_sum]

section Evaluation
variable {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℂ A]

/-- A common total-degree bound, stronger than separate nilpotence. -/
def JointZero (M : ℕ) (t : ι → A) : Prop :=
  ∀ β : ι →₀ ℕ, M < β.degree → β.prod (fun i e => t i ^ e) = 0

theorem eval_zero_of_low_coeff_zero (M : ℕ) (t : ι → A) (ht : JointZero M t)
    (P : MvPolynomial ι ℂ) (hP : ∀ β, β.degree ≤ M → P.coeff β = 0) :
    MvPolynomial.aeval t P = 0 := by
  classical
  rw [P.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro β _
  rw [MvPolynomial.aeval_monomial]
  by_cases hβ : β.degree ≤ M
  · simp [hP β hβ]
  · simp [ht β (by omega)]

theorem eval_eq_of_low_coeff_eq (M : ℕ) (t : ι → A) (ht : JointZero M t)
    (P Q : MvPolynomial ι ℂ)
    (h : ∀ β, β.degree ≤ M → P.coeff β = Q.coeff β) :
    MvPolynomial.aeval t P = MvPolynomial.aeval t Q := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply eval_zero_of_low_coeff_zero M t ht
  intro β hβ
  simp [h β hβ]

theorem eval_trunc_poly (M : ℕ) (t : ι → A) (ht : JointZero M t)
    (P : MvPolynomial ι ℂ) :
    MvPolynomial.aeval t (MvPowerSeries.truncTotal (M + 1)
      (P : MvPowerSeries ι ℂ)) = MvPolynomial.aeval t P := by
  apply eval_eq_of_low_coeff_eq M t ht
  intro β hβ
  rw [MvPowerSeries.coeff_truncTotal _ (by omega), MvPolynomial.coeff_coe]

/-- Evaluation of a finite truncation. Multiplicativity uses convolution locality
and the common vanishing bound; truncation itself is only linear. -/
def seriesEval (M : ℕ) (t : ι → A) (ht : JointZero M t) :
    MvPowerSeries ι ℂ →ₐ[ℂ] A where
  toFun F := MvPolynomial.aeval t (MvPowerSeries.truncTotal (M + 1) F)
  map_zero' := by simp
  map_one' := by rw [MvPowerSeries.truncTotal_one (by omega), map_one]
  map_add' F G := by simp
  map_mul' F G := by
    rw [← map_mul]
    apply eval_eq_of_low_coeff_eq M t ht
    intro β hβ
    rw [MvPowerSeries.coeff_truncTotal _ (by omega),
      MvPowerSeries.coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ (by omega)]
  commutes' c := by
    rw [show (algebraMap ℂ (MvPowerSeries ι ℂ)) c =
      ((MvPolynomial.C c : MvPolynomial ι ℂ) : MvPowerSeries ι ℂ) by simp [MvPowerSeries.algebraMap_apply]]
    rw [eval_trunc_poly M t ht]
    simp

@[simp] theorem seriesEval_coe (M : ℕ) (t : ι → A) (ht : JointZero M t)
    (P : MvPolynomial ι ℂ) :
    seriesEval M t ht (P : MvPowerSeries ι ℂ) = MvPolynomial.aeval t P :=
  eval_trunc_poly M t ht P

omit [Fintype ι] in
theorem eval_finiteExp (M : ℕ) (t : ι → A) (P : MvPolynomial ι ℂ) :
    MvPolynomial.aeval t (auxiliaryFiniteExp M P) = nilExp M (MvPolynomial.aeval t P) := by
  simp [auxiliaryFiniteExp, nilExp, map_sum]

theorem seriesEval_formalExp (M : ℕ) (t : ι → A) (ht : JointZero M t)
    (P : MvPolynomial ι ℂ) (hP : P.constantCoeff = 0) :
    seriesEval M t ht (auxiliaryFormalExp (P : MvPowerSeries ι ℂ)) =
      nilExp M (MvPolynomial.aeval t P) := by
  rw [← eval_finiteExp]
  apply eval_eq_of_low_coeff_eq M t ht
  intro β hβ
  rw [MvPowerSeries.coeff_truncTotal _ (by omega)]
  exact auxiliaryFormalExp_coeff_finite P hP M β hβ

omit [Fintype ι] in
/-- A positive polynomial has no monomials below its power; this is a lower
support-degree statement, obtained from formal-series order. -/
theorem coeff_positive_pow_zero (P : MvPolynomial ι ℂ)
    (hP : P.constantCoeff = 0) (k : ℕ) (β : ι →₀ ℕ) (hβ : β.degree < k) :
    (P ^ k).coeff β = 0 := by
  have ho := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k
    (show (P : MvPowerSeries ι ℂ).constantCoeff = 0 from hP)
  have hz := MvPowerSeries.coeff_of_lt_order
    (lt_of_lt_of_le (show (β.degree : ℕ∞) < k by exact_mod_cast hβ) ho)
  simpa only [← MvPolynomial.coe_pow, MvPolynomial.coeff_coe] using hz

theorem eval_positive_pow_zero (M : ℕ) (t : ι → A) (ht : JointZero M t)
    (P : MvPolynomial ι ℂ) (hP : P.constantCoeff = 0)
    (k : ℕ) (hk : M < k) : MvPolynomial.aeval t P ^ k = 0 := by
  rw [← map_pow]
  apply eval_zero_of_low_coeff_zero M t ht
  intro β hβ
  exact coeff_positive_pow_zero P hP k β (by omega)

/-- Mixed powers use one positive ideal and one global budget. -/
theorem eval_positive_mixed_zero (M : ℕ) (t : ι → A) (ht : JointZero M t)
    (P Q : MvPolynomial ι ℂ) (hP : P.constantCoeff = 0) (hQ : Q.constantCoeff = 0)
    (k l : ℕ) (hkl : M < k + l) :
    MvPolynomial.aeval t P ^ k * MvPolynomial.aeval t Q ^ l = 0 := by
  rw [← map_pow, ← map_pow, ← map_mul]
  apply eval_zero_of_low_coeff_zero M t ht
  intro β hβ
  have hPk := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k
    (show (P : MvPowerSeries ι ℂ).constantCoeff = 0 from hP)
  have hQl := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero l
    (show (Q : MvPowerSeries ι ℂ).constantCoeff = 0 from hQ)
  have ho := (add_le_add hPk hQl).trans MvPowerSeries.le_order_mul
  have hz := MvPowerSeries.coeff_of_lt_order
    (lt_of_lt_of_le (show (β.degree : ℕ∞) < (k : ℕ∞) + l by
      exact_mod_cast (show β.degree < k + l by omega)) ho)
  simpa only [← MvPolynomial.coe_pow, ← MvPolynomial.coe_mul,
    MvPolynomial.coeff_coe] using hz

end Evaluation

theorem nilExp_eq_exp {A : Type*} [Ring A] [Algebra ℂ A] [Module ℚ A] [IsScalarTower ℚ ℂ A] (M : ℕ) (z : A)
    (hz : z ^ (M + 1) = 0) : nilExp M z = IsNilpotent.exp z := by
  rw [IsNilpotent.exp_eq_sum hz]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Rat.cast_smul_eq_qsmul ℂ]
  simp

theorem nilExp_cutoff {A : Type*} [Ring A] [Algebra ℂ A] (M K : ℕ) (z : A)
    (hz : z ^ (M + 1) = 0) (hMK : M ≤ K) :
    nilExp K z = nilExp M z := by
  letI : Algebra ℚ A := Algebra.restrictScalars ℚ ℂ A
  letI : IsScalarTower ℚ ℂ A := IsScalarTower.restrictScalars ℚ ℂ A
  rw [nilExp_eq_exp K z (pow_eq_zero_of_le (by omega) hz), nilExp_eq_exp M z hz]

section Evaluation
variable {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℂ A]

theorem nilExp_eval_add (M : ℕ) (t : ι → A) (ht : JointZero M t)
    (P Q : MvPolynomial ι ℂ) (hP : P.constantCoeff = 0) (hQ : Q.constantCoeff = 0) :
    nilExp M (MvPolynomial.aeval t (P + Q)) =
      nilExp M (MvPolynomial.aeval t P) * nilExp M (MvPolynomial.aeval t Q) := by
  letI : Algebra ℚ A := Algebra.restrictScalars ℚ ℂ A
  letI : IsScalarTower ℚ ℂ A := IsScalarTower.restrictScalars ℚ ℂ A
  have hp := eval_positive_pow_zero M t ht P hP (M + 1) (by omega)
  have hq := eval_positive_pow_zero M t ht Q hQ (M + 1) (by omega)
  have hs := eval_positive_pow_zero M t ht (P + Q) (by simp [hP, hQ]) (M + 1) (by omega)
  rw [nilExp_eq_exp M _ hs, nilExp_eq_exp M _ hp, nilExp_eq_exp M _ hq, map_add]
  exact IsNilpotent.exp_add_of_commute (Commute.all _ _) ⟨_, hp⟩ ⟨_, hq⟩

end Evaluation

/-- Grade-two families in the genuine exterior algebra have the shared 4V budget. -/
theorem grade_two_jointZero (L : Torus) {ι : Type*}
    (t : ι → bilinearAlgebra L)
    (ht : ∀ i, (t i : Grassmann L) ∈ grade L 2) :
    JointZero (4 * volume L) t := by
  intro β hβ
  apply Subtype.ext
  have hm := weighted_product_grade L β.support t β (fun i _ => ht i)
  rw [grade_above_dimension L _ (by
    change 8 * volume L < 2 * β.degree
    omega)] at hm
  exact hm

theorem coframe_jointZero (L : Torus) (U : Links L) :
    JointZero (4 * volume L) (coframeEven L U) :=
  grade_two_jointZero L _ (fun i => coframe_grade L U i.1 i.2.1 i.2.2)

def localCoframeEven (L : Torus) (U : Links L) (x : Site L)
    (i : Fin 4 × Fin 4) : bilinearAlgebra L :=
  coframeEven L U (x, i.1, i.2)

theorem local_coframe_jointZero (L : Torus) (U : Links L) (x : Site L) :
    JointZero (4 * volume L) (localCoframeEven L U x) :=
  grade_two_jointZero L _ (fun i => coframe_grade L U x i.1 i.2)

def coframeSeriesEval (L : Torus) (U : Links L) :
    MvPowerSeries (Site L × Fin 4 × Fin 4) ℂ →ₐ[ℂ] bilinearAlgebra L :=
  seriesEval _ _ (coframe_jointZero L U)

def localCoframeSeriesEval (L : Torus) (U : Links L) (x : Site L) :
    MvPowerSeries (Fin 4 × Fin 4) ℂ →ₐ[ℂ] bilinearAlgebra L :=
  seriesEval _ _ (local_coframe_jointZero L U x)

theorem coframe_formalExp (L : Torus) (U : Links L)
    (P : MvPolynomial (Site L × Fin 4 × Fin 4) ℂ) (hP : P.constantCoeff = 0) :
    coframeSeriesEval L U (auxiliaryFormalExp (P : MvPowerSeries _ ℂ)) =
      nilExp (4 * volume L) (MvPolynomial.aeval (coframeEven L U) P) :=
  seriesEval_formalExp _ _ (coframe_jointZero L U) P hP

theorem local_coframe_formalExp (L : Torus) (U : Links L) (x : Site L)
    (P : MvPolynomial (Fin 4 × Fin 4) ℂ) (hP : P.constantCoeff = 0) :
    localCoframeSeriesEval L U x (auxiliaryFormalExp (P : MvPowerSeries _ ℂ)) =
      nilExp (4 * volume L) (MvPolynomial.aeval (localCoframeEven L U x) P) :=
  seriesEval_formalExp _ _ (local_coframe_jointZero L U x) P hP

theorem coframe_positive_pow_zero (L : Torus) (U : Links L)
    (P : MvPolynomial (Site L × Fin 4 × Fin 4) ℂ) (hP : P.constantCoeff = 0)
    (k : ℕ) (hk : 4 * volume L < k) :
    MvPolynomial.aeval (coframeEven L U) P ^ k = 0 :=
  eval_positive_pow_zero _ _ (coframe_jointZero L U) P hP k hk

theorem local_coframe_nilExp_add (L : Torus) (U : Links L) (x : Site L)
    (P Q : MvPolynomial (Fin 4 × Fin 4) ℂ)
    (hP : P.constantCoeff = 0) (hQ : Q.constantCoeff = 0) :
    nilExp (4 * volume L) (MvPolynomial.aeval (localCoframeEven L U x) (P + Q)) =
      nilExp (4 * volume L) (MvPolynomial.aeval (localCoframeEven L U x) P) *
        nilExp (4 * volume L) (MvPolynomial.aeval (localCoframeEven L U x) Q) :=
  nilExp_eval_add _ _ (local_coframe_jointZero L U x) P Q hP hQ

section Multinomial
variable {ι : Type*} [Fintype ι]

theorem auxiliaryFactorial_multinomial (β : ι →₀ ℕ) :
    auxiliaryFactorial β * β.multinomial = β.degree.factorial := by
  classical
  have h := Nat.multinomial_spec Finset.univ β
  rw [Finsupp.multinomial_of_support_subset (Finset.subset_univ _)] at h
  change auxiliaryFactorial β * β.multinomial = (auxiliaryDegree β).factorial at h
  rwa [auxiliaryDegree_eq_degree] at h

theorem auxiliaryFactorial_ne_zero (β : ι →₀ ℕ) : auxiliaryFactorial β ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)

theorem factorial_multinomial_normalization (β : ι →₀ ℕ) :
    (β.degree.factorial : ℂ)⁻¹ * (β.multinomial : ℂ) =
      (auxiliaryFactorial β : ℂ)⁻¹ := by
  have hf : (auxiliaryFactorial β : ℂ) ≠ 0 := by
    exact_mod_cast auxiliaryFactorial_ne_zero β
  have hd : (β.degree.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero β.degree
  have he : (auxiliaryFactorial β : ℂ) * (β.multinomial : ℂ) =
      (β.degree.factorial : ℂ) := by
    exact_mod_cast auxiliaryFactorial_multinomial β
  field_simp
  simpa only [mul_comm] using he

theorem finiteExp_linear_coeff (M : ℕ) (a : ι → ℂ) (β : ι →₀ ℕ) :
    (auxiliaryFiniteExp M (∑ i, a i • MvPolynomial.X i)).coeff β =
      if β.degree ≤ M then
        β.prod (fun i e => a i ^ e) / (auxiliaryFactorial β : ℂ) else 0 := by
  classical
  simp only [auxiliaryFiniteExp, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    smul_eq_mul, MvPolynomial.coeff_linearCombination_X_pow_of_fintype]
  by_cases hβ : β.degree ≤ M
  · rw [if_pos hβ, Finset.sum_eq_single β.degree]
    · rw [if_pos (show (β.sum fun _ m => m) = β.degree from rfl)]
      rw [← mul_assoc, factorial_multinomial_normalization]
      ring
    · intro k _ hk
      rw [if_neg (by change β.degree ≠ k; omega), mul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hβ]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg (by change β.degree ≠ k; have := Finset.mem_range.mp hk; omega), mul_zero]

/-- All multiindices of total degree at most M; no nonempty-coordinate premise. -/
def boundedIndices (M : ℕ) : Finset (ι →₀ ℕ) :=
  (Finsupp.finite_of_degree_lt (σ := ι) (M + 1)).toFinset

@[simp] theorem mem_boundedIndices (M : ℕ) (β : ι →₀ ℕ) :
    β ∈ boundedIndices (ι := ι) M ↔ β.degree ≤ M := by
  simp [boundedIndices]

theorem finiteExp_linear_polynomial (M : ℕ) (a : ι → ℂ) :
    auxiliaryFiniteExp M (∑ i, a i • MvPolynomial.X i) =
      ∑ β ∈ boundedIndices (ι := ι) M,
        MvPolynomial.monomial β
          (β.prod (fun i e => a i ^ e) / (auxiliaryFactorial β : ℂ)) := by
  classical
  ext β
  rw [finiteExp_linear_coeff]
  simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

theorem nilExp_linear_multinomial {A : Type*} [CommRing A] [Algebra ℂ A]
    (M : ℕ) (a : ι → ℂ) (t : ι → A) :
    nilExp M (∑ i, a i • t i) =
      ∑ β ∈ boundedIndices (ι := ι) M,
        (β.prod (fun i e => a i ^ e) / (auxiliaryFactorial β : ℂ)) •
          β.prod (fun i e => t i ^ e) := by
  have h := congrArg (MvPolynomial.aeval t) (finiteExp_linear_polynomial M a)
  simpa only [eval_finiteExp, map_sum, map_smul, MvPolynomial.aeval_X,
    MvPolynomial.aeval_monomial, ← Algebra.smul_def] using h

theorem nilExp_real_linear_multinomial {A : Type*} [CommRing A] [Algebra ℂ A]
    (M : ℕ) (h : ι → ℝ) (t : ι → A) :
    nilExp M (∑ i, (h i : ℂ) • t i) =
      ∑ β ∈ boundedIndices (ι := ι) M,
        ((auxiliaryMonomial β h : ℂ) / (auxiliaryFactorial β : ℂ)) •
          β.prod (fun i e => t i ^ e) := by
  rw [nilExp_linear_multinomial]
  apply Finset.sum_congr rfl
  intro β _
  rw [Finsupp.prod_pow]
  simp only [auxiliaryMonomial, Complex.ofReal_prod, Complex.ofReal_pow]

end Multinomial

theorem grassmann_coordinate_norm_le (L : Torus) (g : Grassmann L)
    (s : Finset (Fin (4 * volume L * 2))) :
    ‖grassmannCoordinates L g s‖ ≤ ‖g‖ :=
  norm_le_pi_norm _ _

theorem coframe_nilExp_linear_multinomial (L : Torus) (U : Links L)
    (M : ℕ) (h : (Site L × Fin 4 × Fin 4) → ℝ) :
    nilExp M (∑ i, (h i : ℂ) • coframe L U i.1 i.2.1 i.2.2) =
      ∑ β ∈ boundedIndices M,
        ((auxiliaryMonomial β h : ℂ) / (auxiliaryFactorial β : ℂ)) •
          ((β.prod (fun i e => coframeEven L U i ^ e) : bilinearAlgebra L) : Grassmann L) := by
  have he := congrArg (bilinearAlgebra L).val
    (nilExp_real_linear_multinomial M h (coframeEven L U))
  simpa only [map_nilExp, map_sum, map_smul, Subalgebra.coe_val,
    coframeEven] using he

theorem local_coframe_nilExp_linear_multinomial (L : Torus) (U : Links L) (x : Site L)
    (M : ℕ) (h : (Fin 4 × Fin 4) → ℝ) :
    nilExp M (∑ i, (h i : ℂ) • coframe L U x i.1 i.2) =
      ∑ β ∈ boundedIndices M,
        ((auxiliaryMonomial β h : ℂ) / (auxiliaryFactorial β : ℂ)) •
          ((β.prod (fun i e => localCoframeEven L U x i ^ e) : bilinearAlgebra L) : Grassmann L) := by
  have he := congrArg (bilinearAlgebra L).val
    (nilExp_real_linear_multinomial M h (localCoframeEven L U x))
  simpa only [map_nilExp, map_sum, map_smul, Subalgebra.coe_val,
    localCoframeEven, coframeEven] using he

section Controls
variable {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℂ A]

omit [Fintype ι] [Algebra ℂ A] in
theorem jointZero_mono (M K : ℕ) (t : ι → A) (ht : JointZero M t) (hMK : M ≤ K) :
    JointZero K t := fun β hβ => ht β (by omega)

theorem seriesEval_cutoff (M K : ℕ) (t : ι → A) (ht : JointZero M t)
    (hMK : M ≤ K) (F : MvPowerSeries ι ℂ) :
    seriesEval K t (jointZero_mono M K t ht hMK) F = seriesEval M t ht F := by
  apply eval_eq_of_low_coeff_eq M t ht
  intro β hβ
  rw [MvPowerSeries.coeff_truncTotal _ (by omega),
    MvPowerSeries.coeff_truncTotal _ (by omega)]

theorem positive_source_cutoff (M K : ℕ) (t : ι → A) (ht : JointZero M t)
    (P : MvPolynomial ι ℂ) (hP : P.constantCoeff = 0) (hMK : M ≤ K) :
    nilExp K (MvPolynomial.aeval t P) = nilExp M (MvPolynomial.aeval t P) :=
  nilExp_cutoff M K _ (eval_positive_pow_zero M t ht P hP _ (by omega)) hMK

theorem eval_source_locality (M : ℕ) (t : ι → A) (ht : JointZero M t)
    (P Q : MvPolynomial ι ℂ) (h : ∀ β, β.degree ≤ M → P.coeff β = Q.coeff β) :
    nilExp M (MvPolynomial.aeval t P) = nilExp M (MvPolynomial.aeval t Q) := by
  rw [eval_eq_of_low_coeff_eq M t ht P Q h]

omit [Fintype ι] [Algebra ℂ A] in
theorem jointZero_zero_family (M : ℕ) : JointZero M (fun _ : ι => (0 : A)) := by
  classical
  intro β hβ
  have hd : β ≠ 0 := by intro h; simp [h] at hβ
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
  exact Finset.prod_eq_zero hi (zero_pow (Finsupp.mem_support_iff.mp hi))

omit [Fintype ι] [Algebra ℂ A] in
theorem jointZero_zero_cutoff_iff (t : ι → A) :
    JointZero 0 t ↔ ∀ i, t i = 0 := by
  constructor
  · intro ht i
    have h := ht (Finsupp.single i 1) (by simp)
    simpa using h
  · intro ht
    convert jointZero_zero_family (ι := ι) (A := A) 0 using 1
    exact funext ht

omit [Fintype ι] in
theorem eval_zero_family (P : MvPolynomial ι ℂ) :
    MvPolynomial.aeval (fun _ : ι => (0 : A)) P = algebraMap ℂ A P.constantCoeff := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_zero'_apply]

end Controls

theorem coframe_nilExp_add (L : Torus) (U : Links L)
    (P Q : MvPolynomial (Site L × Fin 4 × Fin 4) ℂ)
    (hP : P.constantCoeff = 0) (hQ : Q.constantCoeff = 0) :
    nilExp (4 * volume L) (MvPolynomial.aeval (coframeEven L U) (P + Q)) =
      nilExp (4 * volume L) (MvPolynomial.aeval (coframeEven L U) P) *
        nilExp (4 * volume L) (MvPolynomial.aeval (coframeEven L U) Q) :=
  nilExp_eval_add _ _ (coframe_jointZero L U) P Q hP hQ

theorem coframe_positive_cutoff (L : Torus) (U : Links L)
    (P : MvPolynomial (Site L × Fin 4 × Fin 4) ℂ) (hP : P.constantCoeff = 0)
    (K : ℕ) (hK : 4 * volume L ≤ K) :
    nilExp K (MvPolynomial.aeval (coframeEven L U) P) =
      nilExp (4 * volume L) (MvPolynomial.aeval (coframeEven L U) P) :=
  positive_source_cutoff _ K _ (coframe_jointZero L U) P hP hK

theorem local_coframe_positive_pow_zero (L : Torus) (U : Links L) (x : Site L)
    (P : MvPolynomial (Fin 4 × Fin 4) ℂ) (hP : P.constantCoeff = 0)
    (k : ℕ) (hk : 4 * volume L < k) :
    MvPolynomial.aeval (localCoframeEven L U x) P ^ k = 0 :=
  eval_positive_pow_zero _ _ (local_coframe_jointZero L U x) P hP k hk

theorem local_coframe_positive_cutoff (L : Torus) (U : Links L) (x : Site L)
    (P : MvPolynomial (Fin 4 × Fin 4) ℂ) (hP : P.constantCoeff = 0)
    (K : ℕ) (hK : 4 * volume L ≤ K) :
    nilExp K (MvPolynomial.aeval (localCoframeEven L U x) P) =
      nilExp (4 * volume L) (MvPolynomial.aeval (localCoframeEven L U x) P) :=
  positive_source_cutoff _ K _ (local_coframe_jointZero L U x) P hP hK

/-- A zero actual coframe only simplifies the vector exponential. The scalar
compensation weight remains the responsibility of the integral theorem. -/
theorem one_site_identity_nilExp (x : Site oneSite) (M : ℕ) (h : (Fin 4 × Fin 4) → ℝ) :
    nilExp M (∑ i, (h i : ℂ) • coframe oneSite (fun _ _ => 1) x i.1 i.2) = 1 := by
  simp only [one_site_identity_coframe, smul_zero, Finset.sum_const_zero, nilExp_zero]

theorem nilExp_two {A : Type*} [Ring A] [Algebra ℂ A] (z : A) :
    nilExp 2 z = 1 + z + (1 / 2 : ℂ) • z ^ 2 := by
  norm_num [nilExp, Finset.sum_range_succ]

theorem nilExp_pair_sum (L : Torus) (a b c d : Gen L) :
    nilExp 2 (pair L a b + pair L c d) =
      1 + (pair L a b + pair L c d) + pair L a b * pair L c d := by
  rw [nilExp_two, square_pair_sum, smul_smul]
  norm_num

/-- The actual exterior square term survives. Dropping factorial order two
would change this genuine carrier value. -/
theorem nilExp_pair_sum_ne_linear (L : Torus) (f : Fin 4 → Gen L)
    (hf : Function.Injective f) :
    nilExp 2 (pair L (f 0) (f 1) + pair L (f 2) (f 3)) ≠
      1 + (pair L (f 0) (f 1) + pair L (f 2) (f 3)) := by
  rw [nilExp_pair_sum]
  intro h
  have hz := add_left_cancel (show
    (1 + (pair L (f 0) (f 1) + pair L (f 2) (f 3))) +
      pair L (f 0) (f 1) * pair L (f 2) (f 3) =
    (1 + (pair L (f 0) (f 1) + pair L (f 2) (f 3))) + 0 by simpa using h)
  exact four_named_word_nonzero L f hf hz

/-- Inclusion into the original noncommutative algebra preserves evaluation;
the commutative operations remain in the proved bilinear subalgebra. -/
def coframeGrassmannSeriesEval (L : Torus) (U : Links L) :
    MvPowerSeries (Site L × Fin 4 × Fin 4) ℂ →ₐ[ℂ] Grassmann L :=
  (bilinearAlgebra L).val.comp (coframeSeriesEval L U)

def localCoframeGrassmannSeriesEval (L : Torus) (U : Links L) (x : Site L) :
    MvPowerSeries (Fin 4 × Fin 4) ℂ →ₐ[ℂ] Grassmann L :=
  (bilinearAlgebra L).val.comp (localCoframeSeriesEval L U x)

theorem coframeGrassmann_formalExp (L : Torus) (U : Links L)
    (P : MvPolynomial (Site L × Fin 4 × Fin 4) ℂ) (hP : P.constantCoeff = 0) :
    coframeGrassmannSeriesEval L U (auxiliaryFormalExp (P : MvPowerSeries _ ℂ)) =
      nilExp (4 * volume L)
        ((MvPolynomial.aeval (coframeEven L U) P : bilinearAlgebra L) : Grassmann L) := by
  change (bilinearAlgebra L).val
    (coframeSeriesEval L U (auxiliaryFormalExp (P : MvPowerSeries _ ℂ))) = _
  rw [coframe_formalExp L U P hP, map_nilExp]
  rfl

theorem local_coframeGrassmann_formalExp (L : Torus) (U : Links L) (x : Site L)
    (P : MvPolynomial (Fin 4 × Fin 4) ℂ) (hP : P.constantCoeff = 0) :
    localCoframeGrassmannSeriesEval L U x (auxiliaryFormalExp (P : MvPowerSeries _ ℂ)) =
      nilExp (4 * volume L)
        ((MvPolynomial.aeval (localCoframeEven L U x) P : bilinearAlgebra L) : Grassmann L) := by
  change (bilinearAlgebra L).val
    (localCoframeSeriesEval L U x (auxiliaryFormalExp (P : MvPowerSeries _ ℂ))) = _
  rw [local_coframe_formalExp L U x P hP, map_nilExp]
  rfl

theorem coframe_positive_mixed_zero (L : Torus) (U : Links L)
    (P Q : MvPolynomial (Site L × Fin 4 × Fin 4) ℂ)
    (hP : P.constantCoeff = 0) (hQ : Q.constantCoeff = 0)
    (k l : ℕ) (hkl : 4 * volume L < k + l) :
    MvPolynomial.aeval (coframeEven L U) P ^ k *
      MvPolynomial.aeval (coframeEven L U) Q ^ l = 0 :=
  eval_positive_mixed_zero _ _ (coframe_jointZero L U) P Q hP hQ k l hkl

theorem local_coframe_positive_mixed_zero (L : Torus) (U : Links L) (x : Site L)
    (P Q : MvPolynomial (Fin 4 × Fin 4) ℂ)
    (hP : P.constantCoeff = 0) (hQ : Q.constantCoeff = 0)
    (k l : ℕ) (hkl : 4 * volume L < k + l) :
    MvPolynomial.aeval (localCoframeEven L U x) P ^ k *
      MvPolynomial.aeval (localCoframeEven L U x) Q ^ l = 0 :=
  eval_positive_mixed_zero _ _ (local_coframe_jointZero L U x) P Q hP hQ k l hkl

section EdgeControls
variable {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℂ A]

omit [Fintype ι] in
/-- Empty coordinates give the true constant case. -/
theorem empty_coordinates_nilExp [IsEmpty ι] (M : ℕ) (t : ι → A)
    (P : MvPolynomial ι ℂ) (hP : P.constantCoeff = 0) :
    nilExp M (MvPolynomial.aeval t P) = 1 := by
  have ht : t = fun _ => 0 := funext fun i => isEmptyElim i
  rw [ht, eval_zero_family, hP, map_zero, nilExp_zero]

omit [Fintype ι] in
/-- This is the vector factor in the zero-family case, not a claim that
a compensation weight is pointwise one. -/
theorem zero_family_nilExp (M : ℕ) (P : MvPolynomial ι ℂ) (hP : P.constantCoeff = 0) :
    nilExp M (MvPolynomial.aeval (fun _ => (0 : A)) P) = 1 := by
  rw [eval_zero_family, hP, map_zero, nilExp_zero]

theorem formalExp_monomial_source (M : ℕ) (t : ι → A) (ht : JointZero M t)
    (i : ι) (c : ℂ) (d : ℕ) (hd : d ≠ 0) :
    seriesEval M t ht
      (auxiliaryFormalExp ((c • MvPolynomial.X i ^ d : MvPolynomial ι ℂ) :
        MvPowerSeries ι ℂ)) = nilExp M (c • t i ^ d) := by
  have hc : (c • MvPolynomial.X i ^ d : MvPolynomial ι ℂ).constantCoeff = 0 := by
    simp [hd]
  simpa only [map_smul, map_pow, MvPolynomial.aeval_X] using
    seriesEval_formalExp M t ht _ hc

end EdgeControls

/-- A mixed (2,2) index has product factorial 2!2!=4, not total factorial 4!=24. -/
theorem mixed_factorial_control :
    auxiliaryFactorial (Finsupp.single false 2 + Finsupp.single true 2 : Bool →₀ ℕ) = 4 := by
  norm_num [auxiliaryFactorial, Fintype.prod_bool]

theorem mixed_degree_control :
    (Finsupp.single false 2 + Finsupp.single true 2 : Bool →₀ ℕ).degree = 4 := by
  simp

theorem mixed_multinomial_normalization_control :
    ((4 : ℕ).factorial : ℂ)⁻¹ *
      ((Finsupp.single false 2 + Finsupp.single true 2 : Bool →₀ ℕ).multinomial : ℂ) =
      (1 / 4 : ℂ) := by
  have h := factorial_multinomial_normalization
    (Finsupp.single false 2 + Finsupp.single true 2 : Bool →₀ ℕ)
  rw [mixed_factorial_control, mixed_degree_control] at h
  norm_num at h ⊢
  exact h

end SKEFTHawking.ADW.FiniteGrassmannEvaluation
