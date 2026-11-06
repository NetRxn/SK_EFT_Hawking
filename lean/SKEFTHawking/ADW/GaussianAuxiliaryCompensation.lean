import SKEFTHawking.ADW.GaussianAuxiliaryComplex
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Finite complex Gaussian compensation

The ordinary polynomial in original Eq. 4, before Grassmann evaluation.
Only coefficients through the chosen cutoff are recovered; the transformed
series can have a nonzero tail. Original Eq. 7 requires the separate coframe
nilpotence and integral construction.
-/

noncomputable section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
namespace SKEFTHawking.ADW

variable {ι : Type*} [Fintype ι]

def auxiliaryQuadraticPolynomial (σ : ℝ) : MvPolynomial ι ℂ :=
  ∑ i, MvPolynomial.C ((σ ^ 2 / 2 : ℝ) : ℂ) * MvPolynomial.X i ^ 2

def auxiliaryFormalExp (U : MvPowerSeries ι ℂ) : MvPowerSeries ι ℂ :=
  PowerSeries.subst U (PowerSeries.exp ℂ)

def auxiliaryFiniteExp (M : ℕ) (U : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  ∑ k ∈ Finset.range (M + 1), ((k.factorial : ℂ)⁻¹) • U ^ k

/-- Literal total-degree truncation of the two formal exponentials. -/
def compensationPolynomial (M : ℕ) (σ : ℝ) (S : MvPolynomial ι ℂ) :
    MvPolynomial ι ℂ :=
  MvPowerSeries.truncTotal (M + 1)
    (auxiliaryFormalExp (S : MvPowerSeries ι ℂ) *
      auxiliaryFormalExp (-((auxiliaryQuadraticPolynomial σ : MvPolynomial ι ℂ) :
        MvPowerSeries ι ℂ)))

theorem auxiliaryDegree_eq_degree (β : ι →₀ ℕ) : auxiliaryDegree β = β.degree := by
  classical
  exact (Finsupp.sum_fintype β (fun _ n ↦ n) (by simp)).symm

theorem auxiliaryQuadraticPolynomial_coe (σ : ℝ) :
    ((auxiliaryQuadraticPolynomial σ : MvPolynomial ι ℂ) : MvPowerSeries ι ℂ) =
      auxiliaryQuadraticSeries σ := by
  change MvPolynomial.coeToMvPowerSeries.ringHom _ = _
  simp [auxiliaryQuadraticPolynomial, auxiliaryQuadraticSeries, map_sum]

theorem auxiliaryQuadraticPolynomial_constantCoeff (σ : ℝ) :
    (auxiliaryQuadraticPolynomial (ι := ι) σ).constantCoeff = 0 := by
  simp [auxiliaryQuadraticPolynomial]

omit [Fintype ι] in
private theorem coeff_pow_zero (U : MvPowerSeries ι ℂ)
    (hU : U.constantCoeff = 0) (β : ι →₀ ℕ) (k : ℕ) (hk : β.degree < k) :
    MvPowerSeries.coeff β (U ^ k) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hk)
    (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hU)

omit [Fintype ι] in
theorem auxiliaryFormalExp_coeff (U : MvPowerSeries ι ℂ)
    (hU : U.constantCoeff = 0) (β : ι →₀ ℕ) (M : ℕ) (hβ : β.degree ≤ M) :
    MvPowerSeries.coeff β (auxiliaryFormalExp U) =
      ∑ k ∈ Finset.range (M + 1),
        (k.factorial : ℂ)⁻¹ * MvPowerSeries.coeff β (U ^ k) := by
  classical
  rw [auxiliaryFormalExp, PowerSeries.coeff_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero hU)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (M + 1))]
  · simp [PowerSeries.coeff_exp, smul_eq_mul]
  · intro k hk
    by_contra hn
    have hMk : M < k := by simpa using hn
    have hz := coeff_pow_zero U hU β k (lt_of_le_of_lt hβ hMk)
    simp [Function.mem_support, hz] at hk

omit [Fintype ι] in
theorem auxiliaryFormalExp_neg (U : MvPowerSeries ι ℂ)
    (hU : U.constantCoeff = 0) :
    PowerSeries.subst U (PowerSeries.evalNegHom (PowerSeries.exp ℂ)) =
      auxiliaryFormalExp (-U) := by
  ext β
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hU),
    auxiliaryFormalExp, PowerSeries.coeff_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero (by simpa using hU))]
  apply finsum_congr
  intro k
  rw [show (-U) ^ k = (-1 : ℂ) ^ k • U ^ k by rw [← smul_pow]; simp]
  simp only [PowerSeries.evalNegHom, PowerSeries.coeff_rescale, map_smul, smul_eq_mul]
  ring

omit [Fintype ι] in
theorem auxiliaryFormalExp_mul_neg (U : MvPowerSeries ι ℂ)
    (hU : U.constantCoeff = 0) :
    auxiliaryFormalExp U * auxiliaryFormalExp (-U) = 1 := by
  rw [← auxiliaryFormalExp_neg U hU]
  have h := congrArg (PowerSeries.substAlgHom
    (PowerSeries.HasSubst.of_constantCoeff_zero hU))
    (PowerSeries.exp_mul_exp_neg_eq_one (A := ℂ))
  simpa only [map_mul, map_one, PowerSeries.coe_substAlgHom, auxiliaryFormalExp] using h

omit [Fintype ι] in
theorem auxiliaryFormalExp_coeff_finite (S : MvPolynomial ι ℂ)
    (hS : S.constantCoeff = 0) (M : ℕ) (β : ι →₀ ℕ) (hβ : β.degree ≤ M) :
    MvPowerSeries.coeff β (auxiliaryFormalExp (S : MvPowerSeries ι ℂ)) =
      (auxiliaryFiniteExp M S).coeff β := by
  rw [auxiliaryFormalExp_coeff _ (by exact hS) β M hβ]
  simp only [auxiliaryFiniteExp, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    smul_eq_mul, ← MvPolynomial.coe_pow, MvPolynomial.coeff_coe]

theorem compensationPolynomial_coeff (M : ℕ) (σ : ℝ) (S : MvPolynomial ι ℂ)
    (β : ι →₀ ℕ) :
    (compensationPolynomial M σ S).coeff β =
      if auxiliaryDegree β ≤ M then
        MvPowerSeries.coeff β (auxiliaryFormalExp (S : MvPowerSeries ι ℂ) *
          auxiliaryFormalExp (-((auxiliaryQuadraticPolynomial σ : MvPolynomial ι ℂ) :
            MvPowerSeries ι ℂ))) else 0 := by
  simp only [compensationPolynomial, MvPowerSeries.coeff_truncTotal_eq_ite,
    auxiliaryDegree_eq_degree, Nat.lt_succ_iff]

theorem compensationPolynomial_totalDegree (M : ℕ) (σ : ℝ)
    (S : MvPolynomial ι ℂ) : (compensationPolynomial M σ S).totalDegree ≤ M := by
  exact Nat.le_of_lt_succ (MvPowerSeries.totalDegree_truncTotal_lt _ (by omega))


omit [Fintype ι] in
private theorem coeff_mul_congr_degree (F G F' G' : MvPowerSeries ι ℂ)
    (β : ι →₀ ℕ)
    (hF : ∀ α, α.degree ≤ β.degree → MvPowerSeries.coeff α F = MvPowerSeries.coeff α F')
    (hG : ∀ α, α.degree ≤ β.degree → MvPowerSeries.coeff α G = MvPowerSeries.coeff α G') :
    MvPowerSeries.coeff β (F * G) = MvPowerSeries.coeff β (F' * G') := by
  classical
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hd : p.1.degree + p.2.degree = β.degree := by
    simpa using congrArg Finsupp.degree (Finset.mem_antidiagonal.mp hp)
  rw [hF _ (by omega), hG _ (by omega)]

/-- Finite deterministic algorithm: powers 0 through M, then ordinary multiplication
and total-degree truncation. -/
theorem compensationPolynomial_eq_finite (M : ℕ) (σ : ℝ) (S : MvPolynomial ι ℂ)
    (hS : S.constantCoeff = 0) :
    compensationPolynomial M σ S =
      MvPowerSeries.truncTotal (M + 1)
        (((auxiliaryFiniteExp M S *
          auxiliaryFiniteExp M (-auxiliaryQuadraticPolynomial σ)) :
          MvPolynomial ι ℂ) : MvPowerSeries ι ℂ) := by
  ext β
  rw [compensationPolynomial, MvPowerSeries.coeff_truncTotal_eq_ite,
    MvPowerSeries.coeff_truncTotal_eq_ite]
  split_ifs with hβ
  · rw [MvPolynomial.coe_mul]
    apply coeff_mul_congr_degree
    · intro α hα
      exact (auxiliaryFormalExp_coeff_finite S hS M α (by omega)).trans
        (MvPolynomial.coeff_coe _ _).symm
    · intro α hα
      change MvPowerSeries.coeff α
        (auxiliaryFormalExp ((-auxiliaryQuadraticPolynomial σ : MvPolynomial ι ℂ) :
          MvPowerSeries ι ℂ)) = _
      exact (auxiliaryFormalExp_coeff_finite _
        (by simp [auxiliaryQuadraticPolynomial_constantCoeff]) M α (by omega)).trans
        (MvPolynomial.coeff_coe _ _).symm
  · rfl

/-- A rectangle of finite powers is a coefficient algorithm at every retained degree. -/
theorem compensationPolynomial_coeff_finite (M : ℕ) (σ : ℝ)
    (S : MvPolynomial ι ℂ) (hS : S.constantCoeff = 0) (β : ι →₀ ℕ) :
    (compensationPolynomial M σ S).coeff β =
      if auxiliaryDegree β ≤ M then
        ∑ k ∈ Finset.range (M + 1), ∑ l ∈ Finset.range (M + 1),
          ((k.factorial : ℂ)⁻¹ * (l.factorial : ℂ)⁻¹) *
            (S ^ k * (-auxiliaryQuadraticPolynomial σ) ^ l).coeff β
      else 0 := by
  rw [compensationPolynomial_eq_finite M σ S hS,
    MvPowerSeries.coeff_truncTotal_eq_ite]
  simp only [Nat.lt_succ_iff, ← auxiliaryDegree_eq_degree, MvPolynomial.coeff_coe]
  congr 1
  simp only [auxiliaryFiniteExp, Finset.sum_mul, Finset.mul_sum,
    smul_mul_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [Finset.sum_comm]

/-- Compensation recovers all coefficients through M, without a claim about the tail. -/
theorem compensation_series_coeff (M : ℕ) (σ : ℝ) (S : MvPolynomial ι ℂ)
    (_hS : S.constantCoeff = 0) (β : ι →₀ ℕ) (hβ : auxiliaryDegree β ≤ M) :
    MvPowerSeries.coeff β
      (auxiliaryGaussianSeries σ *
        ((compensationPolynomial M σ S : MvPolynomial ι ℂ) : MvPowerSeries ι ℂ)) =
      MvPowerSeries.coeff β (auxiliaryFormalExp (S : MvPowerSeries ι ℂ)) := by
  have heq :
      auxiliaryGaussianSeries σ *
        (auxiliaryFormalExp (S : MvPowerSeries ι ℂ) *
          auxiliaryFormalExp (-((auxiliaryQuadraticPolynomial σ : MvPolynomial ι ℂ) :
            MvPowerSeries ι ℂ))) =
        auxiliaryFormalExp (S : MvPowerSeries ι ℂ) := by
    rw [auxiliaryQuadraticPolynomial_coe]
    have hi := auxiliaryFormalExp_mul_neg (auxiliaryQuadraticSeries (ι := ι) σ)
      (auxiliaryQuadraticSeries_constantCoeff σ)
    change auxiliaryFormalExp (auxiliaryQuadraticSeries σ) * _ = _
    calc
      _ = auxiliaryFormalExp (S : MvPowerSeries ι ℂ) *
        (auxiliaryFormalExp (auxiliaryQuadraticSeries σ) *
          auxiliaryFormalExp (-auxiliaryQuadraticSeries σ)) := by ring
      _ = _ := by rw [hi, mul_one]
  rw [← heq]
  apply coeff_mul_congr_degree
  · intro α _
    rfl
  · intro α hα
    rw [MvPolynomial.coeff_coe, compensationPolynomial_coeff,
      if_pos (by rw [auxiliaryDegree_eq_degree] at hβ ⊢; omega)]

theorem compensation_series_truncTotal (M : ℕ) (σ : ℝ)
    (S : MvPolynomial ι ℂ) (hS : S.constantCoeff = 0) :
    MvPowerSeries.truncTotal (M + 1)
      (auxiliaryGaussianSeries σ *
        ((compensationPolynomial M σ S : MvPolynomial ι ℂ) : MvPowerSeries ι ℂ)) =
    MvPowerSeries.truncTotal (M + 1)
      (auxiliaryFormalExp (S : MvPowerSeries ι ℂ)) := by
  ext β
  rw [MvPowerSeries.coeff_truncTotal_eq_ite, MvPowerSeries.coeff_truncTotal_eq_ite]
  split_ifs with hβ
  · exact compensation_series_coeff M σ S hS β
      (by rw [auxiliaryDegree_eq_degree]; omega)
  · rfl

theorem integrable_compensation_monomial (M : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (S : MvPolynomial ι ℂ) (β : ι →₀ ℕ) :
    Integrable (fun h : ι → ℝ ↦ auxiliaryWeight σ (compensationPolynomial M σ S) h *
      (auxiliaryMonomial β h : ℂ)) (Measure.pi fun _ : ι ↦ gaussianReal 0 v) :=
  integrable_auxiliaryWeight_mul_monomial σ hσ v hv _ β

theorem integral_compensation_normalized (M : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (S : MvPolynomial ι ℂ)
    (hS : S.constantCoeff = 0) (β : ι →₀ ℕ) (hβ : auxiliaryDegree β ≤ M) :
    (∫ h : ι → ℝ, auxiliaryWeight σ (compensationPolynomial M σ S) h *
      (auxiliaryMonomial β h : ℂ) ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v)) /
      (auxiliaryFactorial β : ℂ) =
      MvPowerSeries.coeff β (auxiliaryFormalExp (S : MvPowerSeries ι ℂ)) := by
  change MvPowerSeries.coeff β (auxiliarySeries σ v (compensationPolynomial M σ S)) = _
  rw [auxiliarySeries_eq_exp_quadratic_mul σ hσ v hv]
  exact compensation_series_coeff M σ S hS β hβ

theorem integral_compensation_raw (M : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (S : MvPolynomial ι ℂ)
    (hS : S.constantCoeff = 0) (β : ι →₀ ℕ) (hβ : auxiliaryDegree β ≤ M) :
    (∫ h : ι → ℝ, auxiliaryWeight σ (compensationPolynomial M σ S) h *
      (auxiliaryMonomial β h : ℂ) ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v)) =
      (auxiliaryFactorial β : ℂ) *
        MvPowerSeries.coeff β (auxiliaryFormalExp (S : MvPowerSeries ι ℂ)) := by
  have hf : (auxiliaryFactorial β : ℂ) ≠ 0 := by
    simp only [auxiliaryFactorial, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (β i))
  have h := integral_compensation_normalized M σ hσ v hv S hS β hβ
  exact (div_eq_iff hf).mp h |>.trans (mul_comm _ _)

theorem compensation_M_zero (σ : ℝ) (S : MvPolynomial ι ℂ)
    (hS : S.constantCoeff = 0) : compensationPolynomial 0 σ S = 1 := by
  rw [compensationPolynomial_eq_finite 0 σ S hS]
  simp [auxiliaryFiniteExp, MvPowerSeries.truncTotal_one]

theorem compensation_empty (M : ℕ) (σ : ℝ) (S : MvPolynomial (Fin 0) ℂ)
    (hS : S.constantCoeff = 0) : S = 0 ∧ compensationPolynomial M σ S = 1 := by
  have hz : S = 0 := by
    ext β
    have hb : β = 0 := Subsingleton.elim _ _
    simpa [hb, ← MvPolynomial.constantCoeff_eq] using hS
  refine ⟨hz, ?_⟩
  subst S
  simp [compensationPolynomial, auxiliaryQuadraticPolynomial, auxiliaryFormalExp,
    PowerSeries.subst_zero_eq_C_constantCoeff, MvPowerSeries.truncTotal_one]


def compensationLinearSource : MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.monomial (Finsupp.single 0 1) Complex.I

theorem compensationLinearSource_constantCoeff : compensationLinearSource.constantCoeff = 0 := by
  norm_num [compensationLinearSource, MvPolynomial.constantCoeff_monomial]

theorem compensation_control_linear_source (n : Fin 4) :
    MvPowerSeries.coeff (Finsupp.single 0 n.val)
      (auxiliaryFormalExp (compensationLinearSource : MvPowerSeries (Fin 1) ℂ)) =
      (![1, Complex.I, -1/2, -Complex.I/6] : Fin 4 → ℂ) n := by
  rw [auxiliaryFormalExp_coeff_finite compensationLinearSource
    compensationLinearSource_constantCoeff 3 _
      (by simp [Finsupp.degree_single]; omega)]
  fin_cases n <;> norm_num [auxiliaryFiniteExp, compensationLinearSource,
    Finset.sum_range_succ, MvPolynomial.monomial_pow, MvPolynomial.monomial_mul,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_one, Finsupp.single_zero, Finsupp.single_eq_zero, eq_comm,
    Finsupp.single_smul, smul_eq_mul, Complex.I_sq]
  all_goals ring

theorem compensation_control_linear (σ : ℝ) (n : Fin 4) :
    MvPowerSeries.coeff (Finsupp.single 0 n.val)
      (auxiliaryGaussianSeries σ *
        ((compensationPolynomial 3 σ compensationLinearSource :
          MvPolynomial (Fin 1) ℂ) : MvPowerSeries (Fin 1) ℂ)) =
      (![1, Complex.I, -1/2, -Complex.I/6] : Fin 4 → ℂ) n := by
  rw [compensation_series_coeff 3 σ _ compensationLinearSource_constantCoeff _
    (by simp [auxiliaryDegree]; omega)]
  exact compensation_control_linear_source n


private theorem quadratic_one (σ : ℝ) :
    auxiliaryQuadraticPolynomial (ι := Fin 1) σ =
      MvPolynomial.monomial (Finsupp.single 0 2) ((σ ^ 2 / 2 : ℝ) : ℂ) := by
  simp [auxiliaryQuadraticPolynomial, MvPolynomial.C_mul_X_pow_eq_monomial]

omit [Fintype ι] in
private theorem neg_monomial (α : ι →₀ ℕ) (c : ℂ) :
    -(MvPolynomial.monomial α c) = MvPolynomial.monomial α (-c) :=
  (map_neg (MvPolynomial.monomial α) c).symm

theorem compensation_control_linear_polynomial (σ : ℝ) (n : Fin 4) :
    (compensationPolynomial 3 σ compensationLinearSource).coeff (Finsupp.single 0 n.val) =
      (![1, Complex.I, -1/2-((σ^2/2 : ℝ) : ℂ),
        -Complex.I/6-Complex.I*((σ^2/2 : ℝ) : ℂ)] : Fin 4 → ℂ) n := by
  rw [compensationPolynomial_coeff_finite _ _ _ compensationLinearSource_constantCoeff]
  simp only [quadratic_one, compensationLinearSource, neg_monomial]
  fin_cases n <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      MvPolynomial.monomial_pow, MvPolynomial.monomial_mul]
  all_goals norm_num [auxiliaryDegree, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_one, Finsupp.single_eq_zero,
    Finsupp.single_smul, ← Finsupp.single_add, eq_comm]
  all_goals ring

def compensationMixedIndex : Fin 2 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1

def compensationMixedSource : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.monomial compensationMixedIndex (1 + Complex.I)

theorem compensationMixedSource_constantCoeff : compensationMixedSource.constantCoeff = 0 := by
  norm_num [compensationMixedSource, MvPolynomial.constantCoeff_monomial,
    compensationMixedIndex, Finsupp.ext_iff, Fin.forall_fin_two]

theorem compensation_control_mixed_source :
    MvPowerSeries.coeff (2 • compensationMixedIndex)
      (auxiliaryFormalExp (compensationMixedSource : MvPowerSeries (Fin 2) ℂ)) =
      Complex.I := by
  rw [auxiliaryFormalExp_coeff_finite compensationMixedSource
    compensationMixedSource_constantCoeff 4 _ (by
      norm_num [compensationMixedIndex, map_add, Finsupp.degree_single])]
  simp only [auxiliaryFiniteExp, compensationMixedSource, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, MvPolynomial.monomial_pow,
    MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
  norm_num [compensationMixedIndex, Finsupp.ext_iff, Fin.forall_fin_two, smul_eq_mul]
  ring_nf
  norm_num [Complex.I_sq]

theorem compensation_control_mixed_raw (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 2 → ℝ, auxiliaryWeight σ
      (compensationPolynomial 4 σ compensationMixedSource) h *
        (auxiliaryMonomial (2 • compensationMixedIndex) h : ℂ)
        ∂(Measure.pi fun _ : Fin 2 ↦ gaussianReal 0 v)) = 4 * Complex.I := by
  rw [integral_compensation_raw _ _ hσ _ hv _ compensationMixedSource_constantCoeff _
    (by norm_num [auxiliaryDegree, compensationMixedIndex, Fin.sum_univ_succ])]
  rw [compensation_control_mixed_source]
  norm_num [auxiliaryFactorial, compensationMixedIndex, Fin.prod_univ_succ]

def compensationHighSource : MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.monomial (Finsupp.single 0 7) Complex.I

theorem compensationHighSource_constantCoeff : compensationHighSource.constantCoeff = 0 := by
  norm_num [compensationHighSource, MvPolynomial.constantCoeff_monomial]

theorem compensation_control_high_source (n : Fin 8) :
    MvPowerSeries.coeff (Finsupp.single 0 n.val)
      (auxiliaryFormalExp (compensationHighSource : MvPowerSeries (Fin 1) ℂ)) =
      if n.val = 0 then 1 else if n.val = 7 then Complex.I else 0 := by
  rw [auxiliaryFormalExp_coeff_finite compensationHighSource
    compensationHighSource_constantCoeff 7 _ (by simp [Finsupp.degree_single]; omega)]
  fin_cases n <;> norm_num [auxiliaryFiniteExp, compensationHighSource,
    Finset.sum_range_succ, MvPolynomial.monomial_pow, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, MvPolynomial.coeff_one,
    Finsupp.single_zero, Finsupp.single_eq_zero, eq_comm, Finsupp.single_smul, smul_eq_mul]

theorem compensation_control_high_raw (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ, auxiliaryWeight σ
      (compensationPolynomial 7 σ compensationHighSource) h *
        (auxiliaryMonomial (Finsupp.single 0 7) h : ℂ)
        ∂(Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 v)) = 5040 * Complex.I := by
  rw [integral_compensation_raw _ _ hσ _ hv _ compensationHighSource_constantCoeff _
    (by norm_num [auxiliaryDegree])]
  have hc : MvPowerSeries.coeff (Finsupp.single 0 7)
      (auxiliaryFormalExp (compensationHighSource : MvPowerSeries (Fin 1) ℂ)) =
      Complex.I := by
    simpa using compensation_control_high_source ⟨7, by omega⟩
  rw [hc]
  norm_num [auxiliaryFactorial]


theorem compensation_control_high (σ : ℝ) (n : Fin 8) :
    MvPowerSeries.coeff (Finsupp.single 0 n.val)
      (auxiliaryGaussianSeries σ *
        ((compensationPolynomial 7 σ compensationHighSource :
          MvPolynomial (Fin 1) ℂ) : MvPowerSeries (Fin 1) ℂ)) =
      if n.val = 0 then 1 else if n.val = 7 then Complex.I else 0 := by
  rw [compensation_series_coeff 7 σ _ compensationHighSource_constantCoeff _
    (by simp [auxiliaryDegree]; omega)]
  exact compensation_control_high_source n

theorem compensationPolynomial_coeff_above (M : ℕ) (σ : ℝ)
    (S : MvPolynomial ι ℂ) (β : ι →₀ ℕ) (hβ : M < auxiliaryDegree β) :
    (compensationPolynomial M σ S).coeff β = 0 := by
  rw [compensationPolynomial_coeff, if_neg (by omega)]

theorem compensation_control_high_polynomial (σ : ℝ) (n : Fin 8) :
    (compensationPolynomial 7 σ compensationHighSource).coeff (Finsupp.single 0 n.val) =
      (![1, 0, -((σ^2/2 : ℝ) : ℂ), 0, ((σ^2/2 : ℝ) : ℂ)^2/2, 0,
        -((σ^2/2 : ℝ) : ℂ)^3/6, Complex.I] : Fin 8 → ℂ) n := by
  rw [compensationPolynomial_coeff_finite _ _ _ compensationHighSource_constantCoeff]
  simp only [quadratic_one, compensationHighSource, neg_monomial]
  fin_cases n <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      MvPolynomial.monomial_pow, MvPolynomial.monomial_mul]
  all_goals norm_num [auxiliaryDegree, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_one, Finsupp.single_eq_zero, Finsupp.single_smul,
    ← Finsupp.single_add, eq_comm]
  all_goals ring

/-- The degree-seven source survives at M=7 and is excluded from P at M=6. -/
theorem compensation_control_cutoff (σ : ℝ) :
    (compensationPolynomial 7 σ compensationHighSource).coeff (Finsupp.single 0 7) =
      Complex.I ∧
    (compensationPolynomial 6 σ compensationHighSource).coeff (Finsupp.single 0 7) = 0 := by
  constructor
  · simpa using compensation_control_high_polynomial σ ⟨7, by omega⟩
  · exact compensationPolynomial_coeff_above 6 σ _ _
      (by norm_num [auxiliaryDegree])

theorem compensation_zero_source (M : ℕ) (σ : ℝ) :
    compensationPolynomial M σ (0 : MvPolynomial ι ℂ) =
      MvPowerSeries.truncTotal (M + 1)
        (auxiliaryFormalExp (-auxiliaryQuadraticSeries (ι := ι) σ)) := by
  simp [compensationPolynomial, auxiliaryFormalExp, auxiliaryQuadraticPolynomial_coe,
    PowerSeries.subst_zero_eq_C_constantCoeff]

theorem compensation_control_M_zero_integral (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (S : MvPolynomial ι ℂ)
    (hS : S.constantCoeff = 0) :
    (∫ h : ι → ℝ, auxiliaryWeight σ (compensationPolynomial 0 σ S) h
      ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v)) = 1 := by
  rw [compensation_M_zero σ S hS]
  have h := integral_compensation_normalized 0 σ hσ v hv (0 : MvPolynomial ι ℂ)
    (by simp) 0 (by simp [auxiliaryDegree])
  simpa [compensation_M_zero, auxiliaryMonomial, auxiliaryFactorial,
    auxiliaryFormalExp, PowerSeries.subst_zero_eq_C_constantCoeff] using h

theorem compensation_control_two_scales :
    (∫ h : Fin 1 → ℝ, auxiliaryWeight 2
      (compensationPolynomial 7 2 compensationHighSource) h *
        (auxiliaryMonomial (Finsupp.single 0 7) h : ℂ)
        ∂(Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 4)) = 5040 * Complex.I ∧
    (∫ h : Fin 1 → ℝ, auxiliaryWeight (1/2)
      (compensationPolynomial 7 (1/2) compensationHighSource) h *
        (auxiliaryMonomial (Finsupp.single 0 7) h : ℂ)
        ∂(Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 (1/4))) = 5040 * Complex.I := by
  exact ⟨compensation_control_high_raw 2 (by norm_num) 4 (by norm_num),
    compensation_control_high_raw (1/2) (by norm_num) (1/4) (by norm_num)⟩

/-- A concrete nonzero tail rules out replacing the retained identity by global equality. -/
theorem compensation_control_tail :
    MvPowerSeries.coeff (Finsupp.single 0 2)
      (auxiliaryGaussianSeries 2 *
        ((compensationPolynomial 0 2 (0 : MvPolynomial (Fin 1) ℂ) :
          MvPolynomial (Fin 1) ℂ) : MvPowerSeries (Fin 1) ℂ)) = 2 := by
  rw [compensation_M_zero _ _ (by simp), MvPolynomial.coe_one, mul_one,
    auxiliaryGaussianSeries_coeff]
  norm_num [auxiliaryGaussianMultiCoeff, auxiliaryGaussianCoeff]


private theorem formalExp_coeff_trunc (M : ℕ) (U : MvPowerSeries ι ℂ)
    (hU : U.constantCoeff = 0) (β : ι →₀ ℕ) (hβ : β.degree ≤ M) :
    MvPowerSeries.coeff β (auxiliaryFormalExp U) =
      MvPowerSeries.coeff β
        (auxiliaryFormalExp ((MvPowerSeries.truncTotal (M + 1) U :
          MvPolynomial ι ℂ) : MvPowerSeries ι ℂ)) := by
  have ht : MvPowerSeries.constantCoeff
      ((MvPowerSeries.truncTotal (M + 1) U : MvPolynomial ι ℂ) :
        MvPowerSeries ι ℂ) = 0 := by
    change (MvPowerSeries.truncTotal (M + 1) U).constantCoeff = 0
    simp [MvPowerSeries.constantCoeff_truncTotal_eq_ite, hU]
  rw [auxiliaryFormalExp_coeff U hU β M hβ,
    auxiliaryFormalExp_coeff _ ht β M hβ]
  apply Finset.sum_congr rfl
  intro k _
  rw [← MvPolynomial.coe_pow, MvPolynomial.coeff_coe,
    MvPowerSeries.coeff_truncTotal_pow U (by omega)]

/-- Terms in the source above M do not affect the constructed polynomial. -/
theorem compensation_source_truncation (M : ℕ) (σ : ℝ)
    (S : MvPolynomial ι ℂ) (hS : S.constantCoeff = 0) :
    compensationPolynomial M σ S =
      compensationPolynomial M σ
        (MvPowerSeries.truncTotal (M + 1) (S : MvPowerSeries ι ℂ)) := by
  ext β
  rw [compensationPolynomial_coeff, compensationPolynomial_coeff]
  split_ifs with hβ
  · apply coeff_mul_congr_degree
    · intro α hα
      exact formalExp_coeff_trunc M _ hS α
        (by rw [auxiliaryDegree_eq_degree] at hβ; omega)
    · intro _ _
      rfl
  · rfl


private theorem quadratic_two (σ : ℝ) :
    auxiliaryQuadraticPolynomial (ι := Fin 2) σ =
      MvPolynomial.monomial (Finsupp.single 0 2) ((σ ^ 2 / 2 : ℝ) : ℂ) +
      MvPolynomial.monomial (Finsupp.single 1 2) ((σ ^ 2 / 2 : ℝ) : ℂ) := by
  simp [auxiliaryQuadraticPolynomial, Fin.sum_univ_succ,
    MvPolynomial.C_mul_X_pow_eq_monomial]


theorem compensation_control_mixed_polynomial (σ : ℝ) :
    (compensationPolynomial 4 σ compensationMixedSource).coeff (2 • compensationMixedIndex) =
      ((σ ^ 2 / 2 : ℝ) : ℂ) ^ 2 + Complex.I := by
  have hs : compensationMixedSource.IsHomogeneous 2 := by
    apply MvPolynomial.isHomogeneous_monomial
    norm_num [compensationMixedIndex, map_add, Finsupp.degree_single]
  have hq : (auxiliaryQuadraticPolynomial (ι := Fin 2) σ).IsHomogeneous 2 := by
    rw [quadratic_two]
    apply MvPolynomial.IsHomogeneous.add
    all_goals apply MvPolynomial.isHomogeneous_monomial; simp
  have hz (k l : ℕ) (h : k + l ≠ 2) :
      (compensationMixedSource ^ k * (-auxiliaryQuadraticPolynomial σ) ^ l).coeff
        (2 • compensationMixedIndex) = 0 := by
    apply (hs.pow k |>.mul (hq.neg.pow l)).coeff_eq_zero
    norm_num [compensationMixedIndex, map_nsmul, map_add, Finsupp.degree_single]
    omega
  rw [compensationPolynomial_coeff_finite _ _ _ compensationMixedSource_constantCoeff,
    if_pos (by norm_num [auxiliaryDegree, compensationMixedIndex, Fin.sum_univ_succ])]
  norm_num [Finset.sum_range_succ, hz]
  simp only [quadratic_two, compensationMixedSource, neg_add, neg_monomial,
    pow_succ, pow_zero, add_mul, mul_add, one_mul, mul_one,
    MvPolynomial.monomial_mul, MvPolynomial.coeff_add]
  norm_num [compensationMixedIndex, MvPolynomial.coeff_monomial, MvPolynomial.coeff_one,
    Finsupp.ext_iff, Fin.forall_fin_two, smul_eq_mul]
  ring_nf

private theorem mixed_offdegree (σ : ℝ) (β : Fin 2 →₀ ℕ) (k l : ℕ)
    (h : β.degree ≠ 2 * k + 2 * l) :
    (compensationMixedSource ^ k * (-auxiliaryQuadraticPolynomial σ) ^ l).coeff β = 0 := by
  have hs : compensationMixedSource.IsHomogeneous 2 := by
    apply MvPolynomial.isHomogeneous_monomial
    norm_num [compensationMixedIndex, map_add, Finsupp.degree_single]
  have hq : (auxiliaryQuadraticPolynomial (ι := Fin 2) σ).IsHomogeneous 2 := by
    rw [quadratic_two]
    apply MvPolynomial.IsHomogeneous.add
    all_goals apply MvPolynomial.isHomogeneous_monomial; simp
  exact (hs.pow k |>.mul (hq.neg.pow l)).coeff_eq_zero h

private theorem mixed_coefficient_0 (σ : ℝ) :
    (compensationPolynomial 4 σ compensationMixedSource).coeff (Finsupp.single 0 2) =
      -((σ^2/2 : ℝ) : ℂ) := by
  rw [compensationPolynomial_coeff_finite _ _ _ compensationMixedSource_constantCoeff]
  norm_num [Finset.sum_range_succ, auxiliaryDegree, compensationMixedIndex,
    Fin.sum_univ_succ, mixed_offdegree, map_add, map_nsmul, Finsupp.degree_single]
  simp only [quadratic_two, compensationMixedSource, neg_add,
    pow_succ, pow_zero, add_mul, mul_add, one_mul, mul_one,
    MvPolynomial.monomial_mul, MvPolynomial.coeff_add]
  norm_num [compensationMixedIndex, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_one, Finsupp.ext_iff, Fin.forall_fin_two, smul_eq_mul]

private theorem mixed_coefficient_1 (σ : ℝ) :
    (compensationPolynomial 4 σ compensationMixedSource).coeff (Finsupp.single 1 2) =
      -((σ^2/2 : ℝ) : ℂ) := by
  rw [compensationPolynomial_coeff_finite _ _ _ compensationMixedSource_constantCoeff]
  norm_num [Finset.sum_range_succ, auxiliaryDegree, compensationMixedIndex,
    Fin.sum_univ_succ, mixed_offdegree, map_add, map_nsmul, Finsupp.degree_single]
  simp only [quadratic_two, compensationMixedSource, neg_add,
    pow_succ, pow_zero, add_mul, mul_add, one_mul, mul_one,
    MvPolynomial.monomial_mul, MvPolynomial.coeff_add]
  norm_num [compensationMixedIndex, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_one, Finsupp.ext_iff, Fin.forall_fin_two, smul_eq_mul]

private theorem mixed_coefficient_2 (σ : ℝ) :
    (compensationPolynomial 4 σ compensationMixedSource).coeff (compensationMixedIndex) =
      1+Complex.I := by
  rw [compensationPolynomial_coeff_finite _ _ _ compensationMixedSource_constantCoeff]
  norm_num [Finset.sum_range_succ, auxiliaryDegree, compensationMixedIndex,
    Fin.sum_univ_succ, mixed_offdegree, map_add, map_nsmul, Finsupp.degree_single]
  simp only [quadratic_two, compensationMixedSource, neg_add,
    pow_succ, pow_zero, add_mul, mul_add, one_mul, mul_one,
    MvPolynomial.monomial_mul, MvPolynomial.coeff_add]
  norm_num [compensationMixedIndex, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_one, Finsupp.ext_iff, Fin.forall_fin_two, smul_eq_mul]

private theorem mixed_coefficient_3 (σ : ℝ) :
    (compensationPolynomial 4 σ compensationMixedSource).coeff (Finsupp.single 0 4) =
      ((σ^2/2 : ℝ) : ℂ)^2/2 := by
  rw [compensationPolynomial_coeff_finite _ _ _ compensationMixedSource_constantCoeff]
  norm_num [Finset.sum_range_succ, auxiliaryDegree, compensationMixedIndex,
    Fin.sum_univ_succ, mixed_offdegree, map_add, map_nsmul, Finsupp.degree_single]
  simp only [quadratic_two, compensationMixedSource, neg_add,
    pow_succ, pow_zero, add_mul, mul_add, one_mul, mul_one,
    MvPolynomial.monomial_mul, MvPolynomial.coeff_add]
  norm_num [compensationMixedIndex, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_one, Finsupp.ext_iff, Fin.forall_fin_two, smul_eq_mul]
  all_goals ring

private theorem mixed_coefficient_4 (σ : ℝ) :
    (compensationPolynomial 4 σ compensationMixedSource).coeff (Finsupp.single 1 4) =
      ((σ^2/2 : ℝ) : ℂ)^2/2 := by
  rw [compensationPolynomial_coeff_finite _ _ _ compensationMixedSource_constantCoeff]
  norm_num [Finset.sum_range_succ, auxiliaryDegree, compensationMixedIndex,
    Fin.sum_univ_succ, mixed_offdegree, map_add, map_nsmul, Finsupp.degree_single]
  simp only [quadratic_two, compensationMixedSource, neg_add,
    pow_succ, pow_zero, add_mul, mul_add, one_mul, mul_one,
    MvPolynomial.monomial_mul, MvPolynomial.coeff_add]
  norm_num [compensationMixedIndex, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_one, Finsupp.ext_iff, Fin.forall_fin_two, smul_eq_mul]
  all_goals ring

private theorem mixed_coefficient_5 (σ : ℝ) :
    (compensationPolynomial 4 σ compensationMixedSource).coeff (Finsupp.single 0 3 + Finsupp.single 1 1) =
      -(1+Complex.I)*((σ^2/2 : ℝ) : ℂ) := by
  rw [compensationPolynomial_coeff_finite _ _ _ compensationMixedSource_constantCoeff]
  norm_num [Finset.sum_range_succ, auxiliaryDegree, compensationMixedIndex,
    Fin.sum_univ_succ, mixed_offdegree, map_add, map_nsmul, Finsupp.degree_single]
  simp only [quadratic_two, compensationMixedSource, neg_add,
    pow_succ, pow_zero, add_mul, mul_add, one_mul, mul_one,
    MvPolynomial.monomial_mul, MvPolynomial.coeff_add]
  norm_num [compensationMixedIndex, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_one, Finsupp.ext_iff, Fin.forall_fin_two, smul_eq_mul]

private theorem mixed_coefficient_6 (σ : ℝ) :
    (compensationPolynomial 4 σ compensationMixedSource).coeff (Finsupp.single 0 1 + Finsupp.single 1 3) =
      -(1+Complex.I)*((σ^2/2 : ℝ) : ℂ) := by
  rw [compensationPolynomial_coeff_finite _ _ _ compensationMixedSource_constantCoeff]
  norm_num [Finset.sum_range_succ, auxiliaryDegree, compensationMixedIndex,
    Fin.sum_univ_succ, mixed_offdegree, map_add, map_nsmul, Finsupp.degree_single]
  simp only [quadratic_two, compensationMixedSource, neg_add,
    pow_succ, pow_zero, add_mul, mul_add, one_mul, mul_one,
    MvPolynomial.monomial_mul, MvPolynomial.coeff_add]
  norm_num [compensationMixedIndex, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_one, Finsupp.ext_iff, Fin.forall_fin_two, smul_eq_mul]


/-- Every displayed degree-two and degree-four coefficient of the mixed complex control. -/
theorem compensation_control_mixed_coefficients (σ : ℝ) (n : Fin 8) :
    (compensationPolynomial 4 σ compensationMixedSource).coeff
      ((![Finsupp.single 0 2, Finsupp.single 1 2, compensationMixedIndex,
        Finsupp.single 0 4, Finsupp.single 1 4,
        Finsupp.single 0 3 + Finsupp.single 1 1,
        Finsupp.single 0 1 + Finsupp.single 1 3,
        2 • compensationMixedIndex] : Fin 8 → (Fin 2 →₀ ℕ)) n) =
      (![-((σ^2/2 : ℝ) : ℂ), -((σ^2/2 : ℝ) : ℂ), 1+Complex.I,
        ((σ^2/2 : ℝ) : ℂ)^2/2, ((σ^2/2 : ℝ) : ℂ)^2/2,
        -(1+Complex.I)*((σ^2/2 : ℝ) : ℂ), -(1+Complex.I)*((σ^2/2 : ℝ) : ℂ),
        ((σ^2/2 : ℝ) : ℂ)^2+Complex.I] : Fin 8 → ℂ) n := by
  fin_cases n
  · simpa using mixed_coefficient_0 σ
  · simpa using mixed_coefficient_1 σ
  · simpa using mixed_coefficient_2 σ
  · simpa using mixed_coefficient_3 σ
  · simpa using mixed_coefficient_4 σ
  · simpa using mixed_coefficient_5 σ
  · simpa using mixed_coefficient_6 σ
  · simpa using compensation_control_mixed_polynomial σ

/-- Adding a source term of degree M+1 changes no retained coefficient. -/
theorem compensation_control_discarded_source (σ : ℝ) :
    compensationPolynomial 7 σ
      (compensationHighSource +
        MvPolynomial.monomial (Finsupp.single 0 8) (3 + Complex.I)) =
      compensationPolynomial 7 σ compensationHighSource := by
  have hz : MvPowerSeries.truncTotal 8
      (MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) 8) (3 + Complex.I)) = 0 := by
    ext β
    rw [MvPowerSeries.coeff_truncTotal_eq_ite]
    by_cases hb : β = Finsupp.single 0 8
    · subst β
      simp [Finsupp.degree_single]
    · simp [MvPowerSeries.coeff_monomial, hb]
  have ht : MvPowerSeries.truncTotal 8
      ((compensationHighSource +
        MvPolynomial.monomial (Finsupp.single 0 8) (3 + Complex.I) :
          MvPolynomial (Fin 1) ℂ) : MvPowerSeries (Fin 1) ℂ) =
      MvPowerSeries.truncTotal 8
        (compensationHighSource : MvPowerSeries (Fin 1) ℂ) := by
    rw [MvPolynomial.coe_add, map_add, MvPolynomial.coe_monomial, hz, add_zero]
  have hsum : (compensationHighSource +
      MvPolynomial.monomial (Finsupp.single 0 8) (3 + Complex.I)).constantCoeff = 0 := by
    rw [map_add, compensationHighSource_constantCoeff]
    norm_num [MvPolynomial.constantCoeff_monomial]
  have h1 := compensation_source_truncation 7 σ
    (compensationHighSource + MvPolynomial.monomial (Finsupp.single 0 8) (3 + Complex.I))
    hsum
  have h2 := compensation_source_truncation 7 σ compensationHighSource
    compensationHighSource_constantCoeff
  exact h1.trans ((congrArg (compensationPolynomial 7 σ) ht).trans h2.symm)

end SKEFTHawking.ADW
