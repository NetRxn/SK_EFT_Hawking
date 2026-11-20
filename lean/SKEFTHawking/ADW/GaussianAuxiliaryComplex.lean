import SKEFTHawking.ADW.GaussianPolynomialAffine
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Complex polynomial Gaussian auxiliary transform

The explicit finite Hermite weight has genuinely integrable monomial insertions under
Gaussian probability. Their normalized coefficients agree, in every multiindex, with
the product of the input polynomial and the actual formal exponential of the positive
quadratic form. Finite coordinate types may be empty; polynomial degrees are unrestricted.

This proves the complex polynomial transform in the regulated auxiliary construction,
before Grassmann evaluation. Compensation/truncation, coframes, Berezin integration,
link integration and physical reconstruction require separate results.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SKEFTHawking.ADW
noncomputable section
variable {ι : Type*} [Fintype ι]

def auxiliaryDegree (α : ι →₀ ℕ) : ℕ := ∑ i, α i
def auxiliaryFactorial (β : ι →₀ ℕ) : ℕ := ∏ i, (β i).factorial
def auxiliaryHermite (σ : ℝ) (α : ι →₀ ℕ) (h : ι → ℝ) : ℝ :=
  ∏ i, Polynomial.aeval (h i / σ) (Polynomial.hermite (α i))
def auxiliaryMonomial (β : ι →₀ ℕ) (h : ι → ℝ) : ℝ := ∏ i, h i ^ β i
/-- The explicit complex Hermite weight, with inverse scale and no coefficient conjugation. -/
def auxiliaryWeight (σ : ℝ) (P : MvPolynomial ι ℂ) (h : ι → ℝ) : ℂ :=
  ∑ α ∈ P.support, P.coeff α * ((σ ^ auxiliaryDegree α)⁻¹ : ℝ) *
    (auxiliaryHermite σ α h : ℂ)

theorem auxiliaryHermite_mul_monomial (σ : ℝ) (α β : ι →₀ ℕ) (h : ι → ℝ) :
    auxiliaryHermite σ α h * auxiliaryMonomial β h =
      ∏ i, Polynomial.aeval (h i / σ) (Polynomial.hermite (α i)) * h i ^ β i := by
  exact (Finset.prod_mul_distrib).symm

theorem integrable_auxiliaryHermite_mul_monomial (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (α β : ι →₀ ℕ) :
    Integrable (fun h : ι → ℝ ↦
      (auxiliaryHermite σ α h * auxiliaryMonomial β h : ℝ))
      (Measure.pi fun _ : ι ↦ gaussianReal 0 v) := by
  simpa only [auxiliaryHermite_mul_monomial] using
    integrable_prod_hermite_mul_pow_affine (fun i ↦ α i) (fun i ↦ β i) σ hσ v hv

theorem auxiliaryWeight_mul_monomial (σ : ℝ) (P : MvPolynomial ι ℂ)
    (β : ι →₀ ℕ) (h : ι → ℝ) :
    auxiliaryWeight σ P h * (auxiliaryMonomial β h : ℂ) =
      ∑ α ∈ P.support, (P.coeff α * ((σ ^ auxiliaryDegree α)⁻¹ : ℝ)) *
        ((auxiliaryHermite σ α h * auxiliaryMonomial β h : ℝ) : ℂ) := by
  simp only [auxiliaryWeight, Finset.sum_mul, Complex.ofReal_mul, mul_assoc]

/-- Every monomial insertion is Bochner-integrable, independently of its integral formula. -/
theorem integrable_auxiliaryWeight_mul_monomial (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P : MvPolynomial ι ℂ) (β : ι →₀ ℕ) :
    Integrable (fun h : ι → ℝ ↦
      auxiliaryWeight σ P h * (auxiliaryMonomial β h : ℂ))
      (Measure.pi fun _ : ι ↦ gaussianReal 0 v) := by
  simp only [auxiliaryWeight_mul_monomial]
  apply integrable_finsetSum
  intro α _
  exact ((integrable_auxiliaryHermite_mul_monomial σ hσ v hv α β).ofReal).const_mul _


theorem integral_auxiliaryHermite_mul_monomial (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (α β : ι →₀ ℕ) :
    (∫ h : ι → ℝ, ((auxiliaryHermite σ α h * auxiliaryMonomial β h : ℝ) : ℂ)
      ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v)) =
      ((∏ i, σ ^ α i * ((β i).descFactorial (α i) : ℝ) *
        ∫ y : ℝ, y ^ (β i - α i) ∂gaussianReal 0 v : ℝ) : ℂ) := by
  rw [integral_complex_ofReal]
  congr 1
  simpa only [auxiliaryHermite_mul_monomial] using
    integral_prod_hermite_mul_pow_affine (fun i ↦ α i) (fun i ↦ β i) σ hσ v hv

theorem integral_auxiliaryWeight_mul_monomial_raw (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P : MvPolynomial ι ℂ) (β : ι →₀ ℕ) :
    (∫ h : ι → ℝ, auxiliaryWeight σ P h * (auxiliaryMonomial β h : ℂ)
      ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v)) =
      ∑ α ∈ P.support, (P.coeff α * ((σ ^ auxiliaryDegree α)⁻¹ : ℝ)) *
        ((∏ i, σ ^ α i * ((β i).descFactorial (α i) : ℝ) *
          ∫ y : ℝ, y ^ (β i - α i) ∂gaussianReal 0 v : ℝ) : ℂ) := by
  simp only [auxiliaryWeight_mul_monomial]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro α _
    rw [integral_const_mul, integral_auxiliaryHermite_mul_monomial σ hσ v hv]
  · intro α _
    exact ((integrable_auxiliaryHermite_mul_monomial σ hσ v hv α β).ofReal).const_mul _



/-- All-order centered Gaussian recurrence, obtained from the affine Hermite insertion. -/
theorem auxiliaryMoment_recurrence (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (n : ℕ) :
    (∫ y : ℝ, y ^ (n + 2) ∂gaussianReal 0 v) =
      (n + 1 : ℝ) * σ ^ 2 * ∫ y : ℝ, y ^ n ∂gaussianReal 0 v := by
  have h := integral_hermite_mul_affine 1 (Polynomial.X ^ (n + 1)) σ 0 hσ v hv
  simp only [Polynomial.hermite_one, Polynomial.aeval_X, sub_zero, Polynomial.eval_pow,
    Polynomial.eval_X, pow_one, Function.iterate_one, Polynomial.derivative_X_pow,
    Nat.add_sub_cancel, Polynomial.eval_mul, Polynomial.eval_C,
    Nat.cast_add, Nat.cast_one, integral_const_mul] at h
  have he : (fun x : ℝ ↦ x / σ * x ^ (n + 1)) =
      (fun x : ℝ ↦ x ^ (n + 2) / σ) := by
    funext x
    simp only [pow_succ]
    ring
  rw [he, integral_div] at h
  apply (div_eq_iff (ne_of_gt hσ)).mp at h
  nlinarith [h]


theorem auxiliaryDescFactorial_ratio (a b : ℕ) (hab : a ≤ b) (m : ℝ) :
    ((b.descFactorial a : ℝ) * m) / (b.factorial : ℝ) =
      m / ((b - a).factorial : ℝ) := by
  have hf : ((b - a).factorial : ℝ) * (b.descFactorial a : ℝ) =
      (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_mul_descFactorial hab
  have hb : (b.factorial : ℝ) ≠ 0 := by positivity
  have hd : ((b - a).factorial : ℝ) ≠ 0 := by positivity
  apply (div_eq_div_iff hb hd).mpr
  rw [← hf]
  ring

/-- Scale cancellation and coordinatewise factorial normalization, including off-order zero. -/
theorem auxiliaryNormalizedKernel (σ : ℝ) (hσ : 0 < σ)
    (α β : ι →₀ ℕ) (m : ℕ → ℝ) :
    (σ ^ auxiliaryDegree α)⁻¹ *
        (∏ i, σ ^ α i * ((β i).descFactorial (α i) : ℝ) * m (β i - α i)) /
        (auxiliaryFactorial β : ℝ) =
      if α ≤ β then ∏ i, m (β i - α i) / ((β i - α i).factorial : ℝ) else 0 := by
  classical
  have hs : σ ^ auxiliaryDegree α ≠ 0 := pow_ne_zero _ (ne_of_gt hσ)
  have hp :
      (∏ i, σ ^ α i * ((β i).descFactorial (α i) : ℝ) * m (β i - α i)) =
      σ ^ auxiliaryDegree α *
        ∏ i, ((β i).descFactorial (α i) : ℝ) * m (β i - α i) := by
    simp only [auxiliaryDegree, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [hp, inv_mul_cancel_left₀ hs]
  by_cases hab : α ≤ β
  · rw [if_pos hab]
    simp only [auxiliaryFactorial, Nat.cast_prod, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact auxiliaryDescFactorial_ratio (α i) (β i) (hab i) _
  · rw [if_neg hab]
    have hi : ∃ i, β i < α i := by
      simpa only [Finsupp.le_def, not_forall, not_le] using hab
    obtain ⟨i, hi⟩ := hi
    have hz : ∏ i, ((β i).descFactorial (α i) : ℝ) * m (β i - α i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.descFactorial_of_lt hi])
    rw [hz, zero_div]


theorem auxiliaryMoment_even (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (k : ℕ) :
    (∫ y : ℝ, y ^ (2 * k) ∂gaussianReal 0 v) * (k.factorial : ℝ) =
      ((2 * k).factorial : ℝ) * (σ ^ 2 / 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hr := auxiliaryMoment_recurrence σ hσ v hv (2 * k)
    have he : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [he, hr, Nat.factorial_succ, Nat.cast_mul (k + 1) k.factorial,
      Nat.cast_add k 1, Nat.cast_one]
    calc
      ((↑(2 * k) + 1) * σ ^ 2 * ∫ y : ℝ, y ^ (2 * k) ∂gaussianReal 0 v) *
          ((↑k + 1) * ↑k.factorial) =
          (↑(2 * k + 2) : ℝ) * (↑(2 * k + 1) : ℝ) *
            ((∫ y : ℝ, y ^ (2 * k) ∂gaussianReal 0 v) * ↑k.factorial) *
            (σ ^ 2 / 2) := by push_cast; ring
      _ = (↑(2 * k + 2) : ℝ) * (↑(2 * k + 1) : ℝ) *
            (↑(2 * k).factorial * (σ ^ 2 / 2) ^ k) * (σ ^ 2 / 2) := by rw [ih]
      _ = ↑(2 * k + 2).factorial * (σ ^ 2 / 2) ^ (k + 1) := by
        simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
        ring

theorem auxiliaryMoment_odd (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (k : ℕ) :
    (∫ y : ℝ, y ^ (2 * k + 1) ∂gaussianReal 0 v) = 0 := by
  induction k with
  | zero => simp [integral_id_gaussianReal]
  | succ k ih =>
    have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [he, auxiliaryMoment_recurrence σ hσ v hv, ih, mul_zero]



def auxiliaryGaussianCoeff (σ : ℝ) (n : ℕ) : ℂ :=
  if Even n then ((σ ^ 2 / 2 : ℝ) : ℂ) ^ (n / 2) / ((n / 2).factorial : ℂ) else 0

def auxiliaryGaussianMultiCoeff (σ : ℝ) (β : ι →₀ ℕ) : ℂ :=
  ∏ i, auxiliaryGaussianCoeff σ (β i)

theorem auxiliaryMoment_normalized (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (n : ℕ) :
    ((∫ y : ℝ, y ^ n ∂gaussianReal 0 v : ℝ) : ℂ) / (n.factorial : ℂ) =
      auxiliaryGaussianCoeff σ n := by
  by_cases hn : Even n
  · obtain ⟨k, hk⟩ := hn
    have he : n = 2 * k := by omega
    rw [he, auxiliaryGaussianCoeff, if_pos (by simp)]
    have hm := auxiliaryMoment_even σ hσ v hv k
    have hmc : ((∫ y : ℝ, y ^ (2 * k) ∂gaussianReal 0 v : ℝ) : ℂ) *
        (k.factorial : ℂ) = ((2 * k).factorial : ℂ) * ((σ ^ 2 / 2 : ℝ) : ℂ) ^ k := by
      exact_mod_cast hm
    have hdiv : 2 * k / 2 = k := by omega
    rw [hdiv]
    apply (div_eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero (2 * k))
      (by exact_mod_cast Nat.factorial_ne_zero k)).mpr
    simpa only [mul_comm] using hmc
  · obtain ⟨k, hk⟩ := (Nat.not_even_iff_odd.mp hn).exists_bit1
    rw [auxiliaryGaussianCoeff, if_neg hn, hk, auxiliaryMoment_odd σ hσ v hv]
    simp

theorem auxiliaryNormalizedKernel_complex (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (α β : ι →₀ ℕ) :
    (((σ ^ auxiliaryDegree α)⁻¹ : ℝ) : ℂ) *
        ((∏ i, σ ^ α i * ((β i).descFactorial (α i) : ℝ) *
          ∫ y : ℝ, y ^ (β i - α i) ∂gaussianReal 0 v : ℝ) : ℂ) /
        (auxiliaryFactorial β : ℂ) =
      if α ≤ β then auxiliaryGaussianMultiCoeff σ (β - α) else 0 := by
  classical
  have hk := congrArg Complex.ofReal
    (auxiliaryNormalizedKernel σ hσ α β (fun n ↦ ∫ y : ℝ, y ^ n ∂gaussianReal 0 v))
  push_cast at hk ⊢
  rw [hk]
  split_ifs
  · simp only [auxiliaryGaussianMultiCoeff, Complex.ofReal_prod, Complex.ofReal_div,
      Complex.ofReal_natCast, Finsupp.coe_tsub, Pi.sub_apply]
    apply Finset.prod_congr rfl
    intro i _
    exact auxiliaryMoment_normalized σ hσ v hv _
  · rfl

/-- Every normalized integral coefficient is the Gaussian convolution of the complex polynomial. -/
theorem integral_auxiliaryWeight_mul_monomial_normalized (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P : MvPolynomial ι ℂ) (β : ι →₀ ℕ) :
    (∫ h : ι → ℝ, auxiliaryWeight σ P h * (auxiliaryMonomial β h : ℂ)
      ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v)) / (auxiliaryFactorial β : ℂ) =
      ∑ α ∈ P.support, if α ≤ β then
        P.coeff α * auxiliaryGaussianMultiCoeff σ (β - α) else 0 := by
  classical
  rw [integral_auxiliaryWeight_mul_monomial_raw σ hσ v hv, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro α _
  rw [mul_assoc, mul_div_assoc, auxiliaryNormalizedKernel_complex σ hσ v hv]
  split_ifs <;> simp



def auxiliaryLinearSeries (c : ℂ) : MvPowerSeries ι ℂ :=
  ∑ i, c • MvPowerSeries.X i

def auxiliaryQuadraticSeries (σ : ℝ) : MvPowerSeries ι ℂ :=
  ∑ i, MvPowerSeries.C ((σ ^ 2 / 2 : ℝ) : ℂ) * MvPowerSeries.X i ^ 2

/-- The actual formal exponential, defined independently of Gaussian moment coefficients. -/
def auxiliaryGaussianSeries (σ : ℝ) : MvPowerSeries ι ℂ :=
  PowerSeries.subst (auxiliaryQuadraticSeries σ) (PowerSeries.exp ℂ)

theorem auxiliaryQuadraticSeries_constantCoeff (σ : ℝ) :
    MvPowerSeries.constantCoeff (auxiliaryQuadraticSeries (ι := ι) σ) = 0 := by
  simp [auxiliaryQuadraticSeries]

theorem auxiliaryQuadraticSeries_hasSubst (σ : ℝ) :
    PowerSeries.HasSubst (auxiliaryQuadraticSeries (ι := ι) σ) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (auxiliaryQuadraticSeries_constantCoeff σ)

theorem auxiliaryLinearSeries_pow_coeff (c : ℂ) (γ : ι →₀ ℕ) (n : ℕ) :
    MvPowerSeries.coeff γ ((auxiliaryLinearSeries (ι := ι) c) ^ n) =
      if auxiliaryDegree γ = n then (γ.multinomial : ℂ) * c ^ auxiliaryDegree γ else 0 := by
  classical
  have h := MvPolynomial.coeff_linearCombination_X_pow_of_fintype (fun _ : ι ↦ c) γ n
  have hp : ((∑ i, c • MvPolynomial.X i : MvPolynomial ι ℂ) : MvPowerSeries ι ℂ) =
      auxiliaryLinearSeries c := by
    change MvPolynomial.coeToMvPowerSeries.ringHom (∑ i, c • MvPolynomial.X i) = _
    simp [auxiliaryLinearSeries]
  rw [← hp, ← MvPolynomial.coe_pow, MvPolynomial.coeff_coe]
  rw [Finsupp.sum_fintype γ (fun (_ : ι) m ↦ m) (fun _ ↦ rfl),
    Finsupp.prod_fintype γ (fun (_ : ι) m ↦ c ^ m) (fun _ ↦ pow_zero c),
    Finset.prod_pow_eq_pow_sum] at h
  exact h

theorem auxiliaryQuadraticSeries_eq_expand (σ : ℝ) :
    auxiliaryQuadraticSeries (ι := ι) σ =
      MvPowerSeries.expand 2 (by decide) (auxiliaryLinearSeries ((σ ^ 2 / 2 : ℝ) : ℂ)) := by
  simp [auxiliaryQuadraticSeries, auxiliaryLinearSeries, MvPowerSeries.smul_eq_C_mul,
    MvPowerSeries.expand_C]

theorem auxiliaryQuadraticSeries_pow_coeff_double (σ : ℝ) (γ : ι →₀ ℕ) (n : ℕ) :
    MvPowerSeries.coeff (2 • γ) ((auxiliaryQuadraticSeries (ι := ι) σ) ^ n) =
      if auxiliaryDegree γ = n then (γ.multinomial : ℂ) *
        ((σ ^ 2 / 2 : ℝ) : ℂ) ^ auxiliaryDegree γ else 0 := by
  rw [auxiliaryQuadraticSeries_eq_expand, ← map_pow,
    MvPowerSeries.coeff_expand_smul, auxiliaryLinearSeries_pow_coeff]


theorem auxiliaryMultinomial_factorial (γ : ι →₀ ℕ) :
    (auxiliaryFactorial γ : ℂ) * (γ.multinomial : ℂ) =
      ((auxiliaryDegree γ).factorial : ℂ) := by
  classical
  have hm := Nat.multinomial_spec Finset.univ (fun i ↦ γ i)
  rw [Finsupp.multinomial_of_support_subset (Finset.subset_univ γ.support)] at hm
  exact_mod_cast hm

theorem auxiliaryGaussianMultiCoeff_double (σ : ℝ) (γ : ι →₀ ℕ) :
    auxiliaryGaussianMultiCoeff σ (2 • γ) =
      ((σ ^ 2 / 2 : ℝ) : ℂ) ^ auxiliaryDegree γ / (auxiliaryFactorial γ : ℂ) := by
  classical
  simp only [auxiliaryGaussianMultiCoeff, auxiliaryGaussianCoeff, Finsupp.smul_apply,
    smul_eq_mul, auxiliaryFactorial, auxiliaryDegree, Nat.cast_prod]
  simp only [show ∀ n : ℕ, Even (2 * n) from fun n ↦ even_two_mul n, if_true,
    show ∀ n : ℕ, 2 * n / 2 = n from fun n ↦ by omega,
    Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]

theorem auxiliaryGaussianSeries_coeff_double (σ : ℝ) (γ : ι →₀ ℕ) :
    MvPowerSeries.coeff (2 • γ) (auxiliaryGaussianSeries (ι := ι) σ) =
      auxiliaryGaussianMultiCoeff σ (2 • γ) := by
  classical
  rw [auxiliaryGaussianSeries, PowerSeries.coeff_subst (auxiliaryQuadraticSeries_hasSubst σ)]
  rw [finsum_eq_single _ (auxiliaryDegree γ)]
  · rw [auxiliaryQuadraticSeries_pow_coeff_double, if_pos rfl, PowerSeries.coeff_exp,
      auxiliaryGaussianMultiCoeff_double]
    simp only [smul_eq_mul, map_div₀, map_one, map_natCast]
    have hf : ((auxiliaryDegree γ).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (auxiliaryDegree γ)
    have hg : (auxiliaryFactorial γ : ℂ) ≠ 0 := by
      dsimp [auxiliaryFactorial]
      rw [Nat.cast_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ by exact_mod_cast Nat.factorial_ne_zero (γ i))
    have hm := auxiliaryMultinomial_factorial γ
    apply (eq_div_iff hg).mpr
    calc
      (1 / ↑(auxiliaryDegree γ).factorial *
          (↑γ.multinomial * ((σ ^ 2 / 2 : ℝ) : ℂ) ^ auxiliaryDegree γ)) *
          ↑(auxiliaryFactorial γ) =
          ((σ ^ 2 / 2 : ℝ) : ℂ) ^ auxiliaryDegree γ *
            ((↑(auxiliaryFactorial γ) * ↑γ.multinomial) /
              ↑(auxiliaryDegree γ).factorial) := by ring
      _ = _ := by rw [hm, div_self hf, mul_one]
  · intro n hn
    rw [auxiliaryQuadraticSeries_pow_coeff_double, if_neg (Ne.symm hn), smul_zero]


/-- Independent coefficient calculation for exp(Q), using coordinate expansion and multinomials. -/
theorem auxiliaryGaussianSeries_coeff (σ : ℝ) (γ : ι →₀ ℕ) :
    MvPowerSeries.coeff γ (auxiliaryGaussianSeries (ι := ι) σ) =
      auxiliaryGaussianMultiCoeff σ γ := by
  classical
  by_cases hall : ∀ i, Even (γ i)
  · let δ : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i ↦ γ i / 2)
    have he : γ = 2 • δ := by
      ext i
      have hi := Nat.even_iff.mp (hall i)
      simp only [Finsupp.smul_apply, smul_eq_mul, δ, Finsupp.coe_equivFunOnFinite_symm]
      omega
    rw [he, auxiliaryGaussianSeries_coeff_double]
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hd : ¬ 2 ∣ γ i := by
      rintro ⟨k, hk⟩
      apply hi
      exact ⟨k, by omega⟩
    have hz : ∀ n : ℕ, MvPowerSeries.coeff γ
        ((auxiliaryQuadraticSeries (ι := ι) σ) ^ n) = 0 := by
      intro n
      rw [auxiliaryQuadraticSeries_eq_expand, ← map_pow]
      exact MvPowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ hd
    rw [auxiliaryGaussianSeries, PowerSeries.coeff_subst (auxiliaryQuadraticSeries_hasSubst σ)]
    simp only [hz, smul_zero, finsum_zero]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [auxiliaryGaussianCoeff, hi])



/-- Formal series whose coefficients are the actual normalized auxiliary integrals. -/
def auxiliarySeries (σ : ℝ) (v : ℝ≥0) (P : MvPolynomial ι ℂ) : MvPowerSeries ι ℂ :=
  fun β ↦ (∫ h : ι → ℝ, auxiliaryWeight σ P h * (auxiliaryMonomial β h : ℂ)
    ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v)) / (auxiliaryFactorial β : ℂ)

theorem auxiliaryGaussianSeries_mul_polynomial_coeff (σ : ℝ)
    (P : MvPolynomial ι ℂ) (β : ι →₀ ℕ) :
    MvPowerSeries.coeff β (auxiliaryGaussianSeries σ * (P : MvPowerSeries ι ℂ)) =
      ∑ α ∈ P.support, if α ≤ β then
        P.coeff α * auxiliaryGaussianMultiCoeff σ (β - α) else 0 := by
  classical
  have hp : (P : MvPowerSeries ι ℂ) =
      ∑ α ∈ P.support, MvPowerSeries.monomial α (P.coeff α) := by
    have h := congrArg MvPolynomial.coeToMvPowerSeries.ringHom P.as_sum
    simpa only [map_sum, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      MvPolynomial.coe_monomial] using h
  rw [hp, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [MvPowerSeries.coeff_mul_monomial]
  split_ifs <;> simp [auxiliaryGaussianSeries_coeff, mul_comm]

/-- Full formal auxiliary identity for every finite complex polynomial and positive scale. -/
theorem auxiliarySeries_eq_exp_quadratic_mul (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P : MvPolynomial ι ℂ) :
    auxiliarySeries σ v P =
      auxiliaryGaussianSeries σ * (P : MvPowerSeries ι ℂ) := by
  apply MvPowerSeries.ext
  intro β
  rw [auxiliaryGaussianSeries_mul_polynomial_coeff]
  exact integral_auxiliaryWeight_mul_monomial_normalized σ hσ v hv P β


theorem integrable_auxiliaryWeight (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P : MvPolynomial ι ℂ) :
    Integrable (auxiliaryWeight σ P)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 v) := by
  simpa [auxiliaryMonomial] using
    integrable_auxiliaryWeight_mul_monomial σ hσ v hv P 0

theorem auxiliarySeries_monomial_coeff (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (α β : ι →₀ ℕ) (c : ℂ) :
    MvPowerSeries.coeff β (auxiliarySeries σ v (MvPolynomial.monomial α c)) =
      if α ≤ β then c * auxiliaryGaussianMultiCoeff σ (β - α) else 0 := by
  rw [auxiliarySeries_eq_exp_quadratic_mul σ hσ v hv,
    MvPolynomial.coe_monomial, MvPowerSeries.coeff_mul_monomial]
  split_ifs <;> simp [auxiliaryGaussianSeries_coeff, mul_comm]

theorem integral_auxiliaryWeight_monomial_diagonal (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (α : ι →₀ ℕ) (c : ℂ) :
    (∫ h : ι → ℝ, auxiliaryWeight σ (MvPolynomial.monomial α c) h *
      (auxiliaryMonomial α h : ℂ) ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 v)) =
      (auxiliaryFactorial α : ℂ) * c := by
  have hh := auxiliarySeries_monomial_coeff σ hσ v hv α α c
  simp only [le_refl, if_true, tsub_self] at hh
  have hg : auxiliaryGaussianMultiCoeff (ι := ι) σ 0 = 1 := by
    simp [auxiliaryGaussianMultiCoeff, auxiliaryGaussianCoeff]
  rw [hg, mul_one] at hh
  change _ / (auxiliaryFactorial α : ℂ) = c at hh
  have hf : (auxiliaryFactorial α : ℂ) ≠ 0 := by
    simp only [auxiliaryFactorial, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ by exact_mod_cast Nat.factorial_ne_zero (α i))
  simpa [mul_comm] using (div_eq_iff hf).mp hh



theorem auxiliarySeries_add (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P R : MvPolynomial ι ℂ) :
    auxiliarySeries σ v (P + R) = auxiliarySeries σ v P + auxiliarySeries σ v R := by
  simp only [auxiliarySeries_eq_exp_quadratic_mul σ hσ v hv, MvPolynomial.coe_add, mul_add]

def auxiliaryControlPolynomial : MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.monomial 0 1 +
    MvPolynomial.monomial (Finsupp.single 0 1) Complex.I +
    MvPolynomial.monomial (Finsupp.single 0 2) (-2)

/-- The signed/nonreal quadratic control is an actual normalized Gaussian integral. -/
theorem auxiliary_control_quadratic (n : ℕ) (hn : n ≤ 4) :
    (∫ h : Fin 1 → ℝ, auxiliaryWeight 2 auxiliaryControlPolynomial h *
      (auxiliaryMonomial (Finsupp.single 0 n) h : ℂ)
      ∂(Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 4)) /
        (auxiliaryFactorial (Finsupp.single (0 : Fin 1) n) : ℂ) =
      (![1, Complex.I, 0, 2 * Complex.I, -2] : Fin 5 → ℂ) ⟨n, by omega⟩ := by
  change MvPowerSeries.coeff (Finsupp.single 0 n)
    (auxiliarySeries 2 4 auxiliaryControlPolynomial) = _
  rw [auxiliaryControlPolynomial, auxiliarySeries_add 2 (by norm_num) 4 (by norm_num),
    auxiliarySeries_add 2 (by norm_num) 4 (by norm_num)]
  simp only [map_add, auxiliarySeries_monomial_coeff 2 (by norm_num) 4 (by norm_num)]
  interval_cases n <;>
    norm_num [auxiliaryGaussianMultiCoeff, auxiliaryGaussianCoeff, Finsupp.le_def,
      Finsupp.coe_tsub, Pi.sub_apply, Fin.prod_univ_one, Nat.even_iff]
  all_goals ring


/-- Empty dimension retains a nonreal constant under the actual probability integral. -/
theorem auxiliary_control_empty :
    (∫ h : Fin 0 → ℝ,
      auxiliaryWeight 2 (MvPolynomial.monomial 0 (-2 + 3 * Complex.I)) h
      ∂(Measure.pi fun _ : Fin 0 ↦ gaussianReal 0 4)) = -2 + 3 * Complex.I := by
  simpa [auxiliaryMonomial, auxiliaryFactorial] using
    integral_auxiliaryWeight_monomial_diagonal (ι := Fin 0) 2 (by norm_num) 4
      (by norm_num) 0 (-2 + 3 * Complex.I)

/-- Raw order four detects the exponential factorial, beyond the normalized control. -/
theorem auxiliary_control_quadratic_raw_four :
    (∫ h : Fin 1 → ℝ, auxiliaryWeight 2 auxiliaryControlPolynomial h *
      (auxiliaryMonomial (Finsupp.single 0 4) h : ℂ)
      ∂(Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 4)) = -48 := by
  have hh := auxiliary_control_quadratic 4 (by omega)
  norm_num [auxiliaryFactorial, Fin.prod_univ_one] at hh
  convert (div_eq_iff (by norm_num : (24 : ℂ) ≠ 0)).mp hh using 1
  norm_num

/-- Mixed indices distinguish coordinate factorials from total-degree factorials. -/
theorem auxiliary_control_mixed (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (n : ℕ) (hn : n = 1 ∨ n = 2 ∨ n = 3) :
    (∫ h : Fin 2 → ℝ,
      auxiliaryWeight σ
        (MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (1 + Complex.I)) h *
      (auxiliaryMonomial (Finsupp.single 0 n + Finsupp.single 1 1) h : ℂ)
      ∂(Measure.pi fun _ : Fin 2 ↦ gaussianReal 0 v)) /
        (auxiliaryFactorial (Finsupp.single (0 : Fin 2) n + Finsupp.single 1 1) : ℂ) =
      if n = 1 then 1 + Complex.I else
        if n = 3 then (1 + Complex.I) * ((σ ^ 2 / 2 : ℝ) : ℂ) else 0 := by
  change MvPowerSeries.coeff _ (auxiliarySeries σ v _) = _
  rw [auxiliarySeries_monomial_coeff σ hσ v hv]
  rcases hn with rfl | rfl | rfl <;>
    norm_num [auxiliaryGaussianMultiCoeff, auxiliaryGaussianCoeff, Finsupp.le_def,
      Finsupp.coe_tsub, Pi.sub_apply, Fin.prod_univ_two, Fin.forall_fin_two, Nat.even_iff]

/-- Coordinate order, rather than total degree, forces this actual integral to vanish. -/
theorem auxiliary_control_off_order (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 2 → ℝ,
      auxiliaryWeight σ (MvPolynomial.monomial (Finsupp.single 0 2) (1 : ℂ)) h *
      (auxiliaryMonomial (Finsupp.single 0 1 + Finsupp.single 1 8) h : ℂ)
      ∂(Measure.pi fun _ : Fin 2 ↦ gaussianReal 0 v)) = 0 := by
  have hh := auxiliarySeries_monomial_coeff (ι := Fin 2) σ hσ v hv
    (Finsupp.single 0 2) (Finsupp.single 0 1 + Finsupp.single 1 8) 1
  rw [if_neg (by norm_num [Finsupp.le_def, Fin.forall_fin_two,
    Fin.forall_fin_one])] at hh
  change _ / (auxiliaryFactorial _ : ℂ) = 0 at hh
  have hf : (auxiliaryFactorial
      (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 8) : ℂ) ≠ 0 := by
    norm_num [auxiliaryFactorial, Fin.prod_univ_two]
  simpa using (div_eq_iff hf).mp hh

/-- An index five insertion cannot survive an order four monomial. -/
theorem auxiliary_control_off_order_five (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ,
      auxiliaryWeight σ (MvPolynomial.monomial (Finsupp.single 0 5) (1 : ℂ)) h *
      (auxiliaryMonomial (Finsupp.single 0 4) h : ℂ)
      ∂(Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 v)) = 0 := by
  have hh := auxiliarySeries_monomial_coeff (ι := Fin 1) σ hσ v hv
    (Finsupp.single 0 5) (Finsupp.single 0 4) 1
  rw [if_neg (by norm_num [Finsupp.le_def, Fin.forall_fin_two,
    Fin.forall_fin_one])] at hh
  change _ / (auxiliaryFactorial _ : ℂ) = 0 at hh
  have hf : (auxiliaryFactorial (Finsupp.single (0 : Fin 1) 4) : ℂ) ≠ 0 := by
    norm_num [auxiliaryFactorial, Fin.prod_univ_one]
  simpa using (div_eq_iff hf).mp hh


/-- Arbitrary scale and degree seven expose truncation, phase, and inverse-scale errors. -/
theorem auxiliary_control_high (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (n : ℕ) (hn : n = 7 ∨ n = 9) :
    (∫ h : Fin 1 → ℝ,
      auxiliaryWeight σ (MvPolynomial.monomial (Finsupp.single 0 7) Complex.I) h *
      (auxiliaryMonomial (Finsupp.single 0 n) h : ℂ)
      ∂(Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 v)) /
        (auxiliaryFactorial (Finsupp.single (0 : Fin 1) n) : ℂ) =
      if n = 7 then Complex.I else Complex.I * ((σ ^ 2 / 2 : ℝ) : ℂ) := by
  change MvPowerSeries.coeff _ (auxiliarySeries σ v _) = _
  rw [auxiliarySeries_monomial_coeff σ hσ v hv]
  rcases hn with rfl | rfl <;>
    norm_num [auxiliaryGaussianMultiCoeff, auxiliaryGaussianCoeff, Finsupp.le_def,
      Finsupp.coe_tsub, Pi.sub_apply, Fin.prod_univ_one, Fin.forall_fin_one, Nat.even_iff]

theorem auxiliary_control_high_raw (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ,
      auxiliaryWeight σ (MvPolynomial.monomial (Finsupp.single 0 7) Complex.I) h *
      (auxiliaryMonomial (Finsupp.single 0 7) h : ℂ)
      ∂(Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 v)) = 5040 * Complex.I := by
  have hh := integral_auxiliaryWeight_monomial_diagonal (ι := Fin 1) σ hσ v hv
    (Finsupp.single 0 7) Complex.I
  norm_num [auxiliaryFactorial, Fin.prod_univ_one] at hh
  exact hh

/-- These coefficients are defined by actual integrals; both nonunit scales are instantiated. -/
theorem auxiliary_control_high_two_scales :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 9)
      (auxiliarySeries 2 4 (MvPolynomial.monomial (Finsupp.single 0 7) Complex.I)) =
        2 * Complex.I ∧
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 9)
      (auxiliarySeries (1 / 2) (1 / 4)
        (MvPolynomial.monomial (Finsupp.single 0 7) Complex.I)) = Complex.I / 8 := by
  constructor
  · have hh := auxiliary_control_high 2 (by norm_num) 4 (by norm_num) 9 (by omega)
    change MvPowerSeries.coeff _ (auxiliarySeries 2 4 _) = _ at hh
    norm_num at hh
    simpa [mul_comm] using hh
  · have hh := auxiliary_control_high (1 / 2) (by norm_num) (1 / 4)
      (by norm_num) 9 (by omega)
    change MvPowerSeries.coeff _ (auxiliarySeries (1 / 2) (1 / 4) _) = _ at hh
    norm_num at hh
    convert hh using 1
    ring

/-- The unweighted actual integral forces the positive quadratic exponent sign. -/
theorem auxiliary_control_unweighted (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (n : ℕ) (hn : n ≤ 4) :
    (∫ h : Fin 1 → ℝ, auxiliaryWeight σ (1 : MvPolynomial (Fin 1) ℂ) h *
      (auxiliaryMonomial (Finsupp.single 0 n) h : ℂ)
      ∂(Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 v)) /
        (auxiliaryFactorial (Finsupp.single (0 : Fin 1) n) : ℂ) =
      (![1, 0, ((σ ^ 2 / 2 : ℝ) : ℂ), 0, ((σ ^ 4 / 8 : ℝ) : ℂ)] :
        Fin 5 → ℂ) ⟨n, by omega⟩ := by
  change MvPowerSeries.coeff _ (auxiliarySeries σ v 1) = _
  rw [show (1 : MvPolynomial (Fin 1) ℂ) = MvPolynomial.monomial 0 1 from rfl,
    auxiliarySeries_monomial_coeff σ hσ v hv]
  interval_cases n <;>
    norm_num [auxiliaryGaussianMultiCoeff, auxiliaryGaussianCoeff,
      Finsupp.coe_tsub, Pi.sub_apply, Fin.prod_univ_one, Nat.even_iff]
  all_goals ring


/-- The raw degree-seven integral is also instantiated at both nonunit scales. -/
theorem auxiliary_control_high_raw_two_scales :
    (∫ h : Fin 1 → ℝ,
      auxiliaryWeight 2 (MvPolynomial.monomial (Finsupp.single 0 7) Complex.I) h *
      (auxiliaryMonomial (Finsupp.single 0 7) h : ℂ)
      ∂(Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 4)) = 5040 * Complex.I ∧
    (∫ h : Fin 1 → ℝ,
      auxiliaryWeight (1 / 2) (MvPolynomial.monomial (Finsupp.single 0 7) Complex.I) h *
      (auxiliaryMonomial (Finsupp.single 0 7) h : ℂ)
      ∂(Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 (1 / 4))) = 5040 * Complex.I := by
  exact ⟨auxiliary_control_high_raw 2 (by norm_num) 4 (by norm_num),
    auxiliary_control_high_raw (1 / 2) (by norm_num) (1 / 4) (by norm_num)⟩

end
end SKEFTHawking.ADW
