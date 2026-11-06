import SKEFTHawking.ADW.FiniteGrassmannEvaluation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Grassmann-valued Gaussian auxiliary identity

Finite multinomial expansion proves Bochner integrability before the value of the
integral is computed. All vectors lie in the actual exterior algebra; only their
bilinear preimages use commutative multiplication. Actual coframes discharge the
common global cutoff. This is the fixed-link local identity, not site-measure
transport, action correspondence, or a publication acceptance statement.
-/
noncomputable section
open scoped BigOperators IsMulCommutative NNReal
namespace SKEFTHawking.ADW.GaussianGrassmannAuxiliary
open MeasureTheory ProbabilityTheory FiniteGrassmannCoframe FiniteGrassmannEvaluation
open scoped SKEFTHawking.ADW.FiniteGrassmannEvaluation

variable {ι : Type*} [Fintype ι]

/-- The actual finite Gaussian product measure, with variance v in every coordinate. -/
abbrev gaussianMeasure (ι : Type*) [Fintype ι] (v : ℝ≥0) :=
  Measure.pi (fun _ : ι ↦ gaussianReal 0 v)

/-- Real auxiliary coordinates act on the original exterior carrier. -/
def linearField (L : Torus) (t : ι → bilinearAlgebra L) (h : ι → ℝ) : Grassmann L :=
  ∑ i, (h i : ℂ) • (t i : Grassmann L)

/-- The finite expansion is independent of nilpotence and of any integral identity. -/
theorem weight_nilExp_expansion (L : Torus) (M : ℕ) (σ : ℝ)
    (P : MvPolynomial ι ℂ) (t : ι → bilinearAlgebra L) (h : ι → ℝ) :
    auxiliaryWeight σ P h • nilExp M (linearField L t h) =
      ∑ β ∈ boundedIndices M,
        ((auxiliaryWeight σ P h * (auxiliaryMonomial β h : ℂ)) /
          (auxiliaryFactorial β : ℂ)) •
            ((β.prod (fun i e ↦ t i ^ e) : bilinearAlgebra L) : Grassmann L) := by
  have he := congrArg (bilinearAlgebra L).val (nilExp_real_linear_multinomial M h t)
  have he' : nilExp M (linearField L t h) =
      ∑ β ∈ boundedIndices M,
        ((auxiliaryMonomial β h : ℂ) / (auxiliaryFactorial β : ℂ)) •
          ((β.prod (fun i e ↦ t i ^ e) : bilinearAlgebra L) : Grassmann L) := by
    simpa only [map_nilExp, map_sum, map_smul, Subalgebra.coe_val, linearField] using he
  rw [he', Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [smul_smul, mul_div_assoc]

/-- Integrability of each fixed-vector summand, with arbitrary scalar polynomial P. -/
theorem integrable_monomial_vector (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P : MvPolynomial ι ℂ)
    (β : ι →₀ ℕ) (g : Grassmann L) :
    Integrable (fun h : ι → ℝ ↦
      ((auxiliaryWeight σ P h * (auxiliaryMonomial β h : ℂ)) /
        (auxiliaryFactorial β : ℂ)) • g) (gaussianMeasure ι v) :=
  ((integrable_auxiliaryWeight_mul_monomial σ hσ v hv P β).div_const _).smul_const g

/-- Independent G-valued Bochner integrability, established before computing its value. -/
theorem integrable_weight_nilExp (L : Torus) (M : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P : MvPolynomial ι ℂ)
    (t : ι → bilinearAlgebra L) :
    Integrable (fun h : ι → ℝ ↦ auxiliaryWeight σ P h • nilExp M (linearField L t h))
      (gaussianMeasure ι v) := by
  simp_rw [weight_nilExp_expansion]
  exact integrable_finsetSum _ (fun β _ ↦ integrable_monomial_vector L σ hσ v hv P β _)

/-- Actual finite-sum Bochner integral bridge, retaining coordinate factorials. -/
theorem integral_weight_nilExp (L : Torus) (M : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P : MvPolynomial ι ℂ)
    (t : ι → bilinearAlgebra L) :
    (∫ h : ι → ℝ, auxiliaryWeight σ P h • nilExp M (linearField L t h)
      ∂gaussianMeasure ι v) =
      ∑ β ∈ boundedIndices M,
        ((∫ h : ι → ℝ, auxiliaryWeight σ P h * (auxiliaryMonomial β h : ℂ)
          ∂gaussianMeasure ι v) / (auxiliaryFactorial β : ℂ)) •
            ((β.prod (fun i e ↦ t i ^ e) : bilinearAlgebra L) : Grassmann L) := by
  simp_rw [weight_nilExp_expansion]
  rw [integral_finsetSum _
    (fun β _ ↦ integrable_monomial_vector L σ hσ v hv P β _)]
  apply Finset.sum_congr rfl
  intro β _
  rw [integral_smul_const, integral_div]

/-- Formal-series evaluation is a finite coefficient sum in the actual carrier. -/
theorem included_seriesEval (L : Torus) (M : ℕ) (t : ι → bilinearAlgebra L)
    (ht : JointZero M t) (F : MvPowerSeries ι ℂ) :
    ((seriesEval M t ht F : bilinearAlgebra L) : Grassmann L) =
      ∑ β ∈ boundedIndices M, (MvPowerSeries.coeff β F) •
        ((β.prod (fun i e ↦ t i ^ e) : bilinearAlgebra L) : Grassmann L) := by
  change (bilinearAlgebra L).val (MvPolynomial.aeval t
    (MvPowerSeries.truncTotal (M + 1) F)) = _
  simp only [MvPowerSeries.truncTotal, MvPowerSeries.truncFinset_apply,
    map_sum, MvPolynomial.aeval_monomial, ← Algebra.smul_def, map_smul]
  rfl

/-- Eq7 in the genuine exterior algebra for arbitrary complex zero-constant source. -/
theorem gaussian_eq7 (L : Torus) (M : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (t : ι → bilinearAlgebra L)
    (ht : JointZero M t) (S : MvPolynomial ι ℂ) (hS : S.constantCoeff = 0) :
    nilExp M ((MvPolynomial.aeval t S : bilinearAlgebra L) : Grassmann L) =
      ∫ h : ι → ℝ, auxiliaryWeight σ (compensationPolynomial M σ S) h •
        nilExp M (linearField L t h) ∂gaussianMeasure ι v := by
  rw [integral_weight_nilExp L M σ hσ v hv]
  have he := congrArg (bilinearAlgebra L).val (seriesEval_formalExp M t ht S hS)
  simp only [map_nilExp, Subalgebra.coe_val] at he
  rw [← he, included_seriesEval]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [integral_compensation_normalized M σ hσ v hv S hS β
    (by simpa only [auxiliaryDegree_eq_degree] using (mem_boundedIndices M β).mp hβ)]

/-- Actual local coframes use the global M=4V and require no algebraic premises. -/
theorem local_coframe_eq7 (L : Torus) (U : Links L) (x : Site L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : MvPolynomial (Fin 4 × Fin 4) ℂ) (hS : S.constantCoeff = 0) :
    nilExp (4 * volume L)
      ((MvPolynomial.aeval (localCoframeEven L U x) S : bilinearAlgebra L) : Grassmann L) =
      ∫ h : (Fin 4 × Fin 4) → ℝ,
        auxiliaryWeight σ (compensationPolynomial (4 * volume L) σ S) h •
          nilExp (4 * volume L) (∑ i, (h i : ℂ) • coframe L U x i.1 i.2)
        ∂gaussianMeasure (Fin 4 × Fin 4) v :=
  gaussian_eq7 L _ σ hσ v hv _ (local_coframe_jointZero L U x) S hS

/-- The actual global coordinate family also discharges the same common mixed budget. -/
theorem global_coframe_eq7 (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : MvPolynomial (Site L × Fin 4 × Fin 4) ℂ) (hS : S.constantCoeff = 0) :
    nilExp (4 * volume L)
      ((MvPolynomial.aeval (coframeEven L U) S : bilinearAlgebra L) : Grassmann L) =
      ∫ h : (Site L × Fin 4 × Fin 4) → ℝ,
        auxiliaryWeight σ (compensationPolynomial (4 * volume L) σ S) h •
          nilExp (4 * volume L) (∑ i, (h i : ℂ) • coframe L U i.1 i.2.1 i.2.2)
        ∂gaussianMeasure (Site L × Fin 4 × Fin 4) v :=
  gaussian_eq7 L _ σ hσ v hv _ (coframe_jointZero L U) S hS

/-- A square-zero summand contributes only the first binomial derivative. -/
theorem squareZero_add_pow {A : Type*} [CommRing A] (x y : A) (hx : x ^ 2 = 0)
    (n : ℕ) : (x + y) ^ (n + 1) = y ^ (n + 1) + (n + 1 : A) * x * y ^ n := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [pow_succ (x + y), ih]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      (y ^ (n + 1) + (↑n + 1) * x * y ^ n) * (x + y) =
        y ^ (n + 2) + (↑n + 1 + 1) * x * y ^ (n + 1) +
          (↑n + 1) * x ^ 2 * y ^ n := by ring
      _ = _ := by rw [hx]; ring

/-- A list of commuting square-zero elements reaches its full factorial product. -/
theorem squareZero_list_sum_top {A : Type*} [CommRing A] (xs : List A)
    (hx : ∀ x ∈ xs, x ^ 2 = 0) :
    xs.sum ^ xs.length = (xs.length.factorial : A) * xs.prod ∧
      xs.sum ^ (xs.length + 1) = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨ht, hz⟩ := ih (fun y hy ↦ hx y (by simp [hy]))
    have hx' := hx x (by simp)
    simp only [List.sum_cons, List.length_cons, List.prod_cons]
    constructor
    · rw [squareZero_add_pow x xs.sum hx' xs.length, hz, ht]
      simp only [zero_add, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    · rw [squareZero_add_pow x xs.sum hx' (xs.length + 1), hz,
        pow_succ xs.sum (xs.length + 1), hz]
      simp

/-- Coordinate pairs as elements of the proved commutative subalgebra. -/
def coordinatePair (L : Torus) (k : Fin (4 * volume L)) : bilinearAlgebra L :=
  ⟨pair L (orderedGenerator L ⟨k.val * 2, by omega⟩)
    (orderedGenerator L ⟨k.val * 2 + 1, by omega⟩), pair_mem L _ _⟩

theorem coordinatePair_square (L : Torus) (k : Fin (4 * volume L)) :
    coordinatePair L k ^ 2 = 0 := by
  apply Subtype.ext
  change (pair L (orderedGenerator L ⟨k.val * 2, by omega⟩)
    (orderedGenerator L ⟨k.val * 2 + 1, by omega⟩)) ^ 2 = 0
  rw [pow_two]
  exact overlapping_pairs_zero L
      (orderedGenerator L ⟨k.val * 2, by omega⟩)
      (orderedGenerator L ⟨k.val * 2 + 1, by omega⟩)
      (orderedGenerator L ⟨k.val * 2 + 1, by omega⟩)

theorem coordinatePair_product_nonzero (L : Torus) :
    (List.ofFn (coordinatePair L)).prod ≠ 0 := by
  intro hz
  have he := congrArg (bilinearAlgebra L).val hz
  exact top_pairs_nonzero L (by
    simpa only [map_list_prod, map_zero, List.map_ofFn, coordinatePair, topPairs,
      Subalgebra.coe_val, Function.comp_def] using he)

/-- Two disjoint coordinate pairs, used for quadratic and complex controls. -/
def pairSum (L : Torus) (a b : Fin (4 * volume L)) : bilinearAlgebra L :=
  coordinatePair L a + coordinatePair L b

theorem pairSum_cube (L : Torus) (a b : Fin (4 * volume L)) :
    pairSum L a b ^ 3 = 0 := by
  have h := (squareZero_list_sum_top [coordinatePair L a, coordinatePair L b]
    (by intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;> exact coordinatePair_square L _)).2
  simpa [pairSum] using h

/-- Singleton coordinate families use the actual nilpotence power, including M=0. -/
theorem single_jointZero (L : Torus) (M : ℕ) (t : bilinearAlgebra L)
    (ht : t ^ (M + 1) = 0) : JointZero M (fun _ : Fin 1 ↦ t) := by
  intro β hβ
  have hd : β.degree = β 0 := by
    rw [← auxiliaryDegree_eq_degree]
    simp [auxiliaryDegree]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simpa using pow_eq_zero_of_le (by omega : M + 1 ≤ β 0) ht

/-- Independent integrability is exported for actual local coframes. -/
theorem integrable_local_coframe (L : Torus) (U : Links L) (x : Site L) (M : ℕ)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (P : MvPolynomial (Fin 4 × Fin 4) ℂ) :
    Integrable (fun h : (Fin 4 × Fin 4) → ℝ ↦ auxiliaryWeight σ P h •
      nilExp M (∑ i, (h i : ℂ) • coframe L U x i.1 i.2))
        (gaussianMeasure (Fin 4 × Fin 4) v) :=
  integrable_weight_nilExp L M σ hσ v hv P (localCoframeEven L U x)

/-- Independent integrability is exported for the actual global coordinate family. -/
theorem integrable_global_coframe (L : Torus) (U : Links L) (M : ℕ)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (P : MvPolynomial (Site L × Fin 4 × Fin 4) ℂ) :
    Integrable (fun h : (Site L × Fin 4 × Fin 4) → ℝ ↦ auxiliaryWeight σ P h •
      nilExp M (∑ i, (h i : ℂ) • coframe L U i.1 i.2.1 i.2.2))
        (gaussianMeasure (Site L × Fin 4 × Fin 4) v) :=
  integrable_weight_nilExp L M σ hσ v hv P (coframeEven L U)

/-- At every cutoff the compensation weight has mean one; it need not equal one. -/
theorem compensation_weight_mean (M : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (S : MvPolynomial ι ℂ)
    (hS : S.constantCoeff = 0) :
    (∫ h : ι → ℝ, auxiliaryWeight σ (compensationPolynomial M σ S) h
      ∂gaussianMeasure ι v) = 1 := by
  have he := integral_compensation_normalized M σ hσ v hv S hS 0
    (by simp [auxiliaryDegree])
  have hc : MvPowerSeries.coeff (0 : ι →₀ ℕ)
      (auxiliaryFormalExp (S : MvPowerSeries ι ℂ)) = 1 := by
    rw [auxiliaryFormalExp_coeff_finite S hS 0 _ (by simp)]
    simp [auxiliaryFiniteExp]
  simpa only [auxiliaryMonomial, Finsupp.coe_zero, Pi.zero_apply, pow_zero,
    Finset.prod_const_one, Complex.ofReal_one, mul_one, auxiliaryFactorial,
    Nat.factorial_zero, Nat.cast_one, div_one, hc] using he

/-- Zero coframes leave the genuine scalar weight under the integral. -/
theorem zero_family_weighted_mean (L : Torus) (M : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (S : MvPolynomial ι ℂ)
    (hS : S.constantCoeff = 0) :
    (∫ h : ι → ℝ, auxiliaryWeight σ (compensationPolynomial M σ S) h •
      nilExp M (linearField L (fun _ ↦ 0) h) ∂gaussianMeasure ι v) = 1 := by
  simp only [linearField, Subalgebra.coe_zero, smul_zero, Finset.sum_const_zero, nilExp_zero]
  rw [integral_smul_const, compensation_weight_mean M σ hσ v hv S hS, one_smul]

/-- The mandatory actual one-site identity-link control uses M=4 and its full weight. -/
theorem one_site_identity_weighted_mean (x : Site oneSite)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : MvPolynomial (Fin 4 × Fin 4) ℂ) (hS : S.constantCoeff = 0) :
    (∫ h : (Fin 4 × Fin 4) → ℝ,
      auxiliaryWeight σ (compensationPolynomial 4 σ S) h •
        nilExp 4 (∑ i, (h i : ℂ) • coframe oneSite (fun _ _ ↦ 1) x i.1 i.2)
      ∂gaussianMeasure (Fin 4 × Fin 4) v) = 1 := by
  simp only [one_site_identity_nilExp]
  rw [integral_smul_const, compensation_weight_mean 4 σ hσ v hv S hS, one_smul]

/-- Initial disjoint pairs in B1's actual exterior basis. -/
def pairPrefix (L : Torus) (n : ℕ) : List (bilinearAlgebra L) :=
  (List.ofFn (coordinatePair L)).take n

theorem pairPrefix_length (L : Torus) (n : ℕ) (hn : n ≤ 4 * volume L) :
    (pairPrefix L n).length = n := by
  simp only [pairPrefix, List.length_take, List.length_ofFn]
  exact Nat.min_eq_left hn

theorem pairPrefix_squareZero (L : Torus) (n : ℕ) :
    ∀ x ∈ pairPrefix L n, x ^ 2 = 0 := by
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hx)
  exact coordinatePair_square L k

theorem pairPrefix_product_nonzero (L : Torus) (n : ℕ) :
    (pairPrefix L n).prod ≠ 0 := by
  intro hz
  have hn := coordinatePair_product_nonzero L
  apply hn
  rw [← List.take_append_drop n (List.ofFn (coordinatePair L)), List.prod_append]
  rw [show ((List.ofFn (coordinatePair L)).take n).prod = 0 from hz, zero_mul]

/-- Every feasible prefix has the exact nonzero factorial power and next-power zero. -/
theorem pairPrefix_sum_powers (L : Torus) (n : ℕ) (hn : n ≤ 4 * volume L) :
    (pairPrefix L n).sum ^ n = (n.factorial : ℂ) • (pairPrefix L n).prod ∧
      (pairPrefix L n).sum ^ (n + 1) = 0 ∧ (pairPrefix L n).sum ^ n ≠ 0 := by
  have he := squareZero_list_sum_top (pairPrefix L n) (pairPrefix_squareZero L n)
  rw [pairPrefix_length L n hn] at he
  have ht : (pairPrefix L n).sum ^ n = (n.factorial : ℂ) • (pairPrefix L n).prod := by
    simpa only [Algebra.smul_def, map_natCast] using he.1
  refine ⟨ht, he.2, ?_⟩
  rw [ht]
  exact smul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)
    (pairPrefix_product_nonzero L n)

/-- Seven disjoint pairs survive on every actual regulator with V at least two. -/
theorem seven_pair_actual (L : Torus) (hV : 2 ≤ volume L) :
    (((pairPrefix L 7).sum : bilinearAlgebra L) : Grassmann L) ^ 7 =
        (5040 : ℂ) • (((pairPrefix L 7).prod : bilinearAlgebra L) : Grassmann L) ∧
      (((pairPrefix L 7).sum : bilinearAlgebra L) : Grassmann L) ^ 8 = 0 ∧
      (((pairPrefix L 7).sum : bilinearAlgebra L) : Grassmann L) ^ 7 ≠ 0 := by
  obtain ⟨ht, hz, hn⟩ := pairPrefix_sum_powers L 7 (by omega)
  constructor
  · have he := congrArg (bilinearAlgebra L).val ht
    norm_num only [Nat.factorial] at he
    simpa only [map_pow, map_smul, Subalgebra.coe_val] using he
  constructor
  · simpa only [map_pow, map_zero, Subalgebra.coe_val] using
      congrArg (bilinearAlgebra L).val hz
  · intro he
    apply hn
    apply Subtype.ext
    exact he

/-- Any square-zero G vector has the expected first-order finite exponential. -/
theorem nilExp_squareZero (L : Torus) (M : ℕ) (hM : 1 ≤ M)
    (z : Grassmann L) (hz : z ^ 2 = 0) : nilExp M z = 1 + z := by
  rw [nilExp_cutoff 1 M z hz hM]
  simp [nilExp, Finset.sum_range_succ]

/-- Degree seven source evaluated in the actual carrier; its nonzero term is retained. -/
theorem high_source_integral (L : Torus) (hV : 2 ≤ volume L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ, auxiliaryWeight σ (compensationPolynomial 7 σ compensationHighSource) h •
      nilExp 7 (linearField L (fun _ ↦ (pairPrefix L 7).sum) h)
      ∂gaussianMeasure (Fin 1) v) =
      1 + Complex.I • ((((pairPrefix L 7).sum : bilinearAlgebra L) : Grassmann L) ^ 7) := by
  let t := (pairPrefix L 7).sum
  have hz : t ^ 8 = 0 := (pairPrefix_sum_powers L 7 (by omega)).2.1
  rw [← gaussian_eq7 L 7 σ hσ v hv (fun _ ↦ t) (single_jointZero L 7 t hz)
    compensationHighSource compensationHighSource_constantCoeff]
  have he : ((MvPolynomial.aeval (fun _ : Fin 1 ↦ t) compensationHighSource :
      bilinearAlgebra L) : Grassmann L) = Complex.I • ((t : Grassmann L) ^ 7) := by
    simp [compensationHighSource, MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  rw [he]
  apply nilExp_squareZero L 7 (by omega)
  rw [smul_pow, ← pow_mul]
  have hz' : (t : Grassmann L) ^ 14 = 0 := by
    have hz8 : (t : Grassmann L) ^ 8 = 0 := by
      simpa only [map_pow, map_zero, Subalgebra.coe_val] using
        congrArg (bilinearAlgebra L).val hz
    exact pow_eq_zero_of_le (by omega : 8 ≤ 14) hz8
  simp [hz']

/-- Raw moment normalization is 5040i / 7!, as used in the surviving G term. -/
theorem high_raw_factorial (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ, auxiliaryWeight σ (compensationPolynomial 7 σ compensationHighSource) h *
      (auxiliaryMonomial (Finsupp.single 0 7) h : ℂ) ∂gaussianMeasure (Fin 1) v) /
        (Nat.factorial 7 : ℂ) = Complex.I := by
  rw [compensation_control_high_raw σ hσ v hv]
  norm_num

/-- Two actual disjoint pairs: the surviving square and vanishing cube. -/
def testT : bilinearAlgebra oneSite := pairSum oneSite ⟨0, by decide⟩ ⟨1, by decide⟩
def testU : bilinearAlgebra oneSite := pairSum oneSite ⟨2, by decide⟩ ⟨3, by decide⟩

theorem testT_cube : testT ^ 3 = 0 := pairSum_cube _ _ _
theorem testU_cube : testU ^ 3 = 0 := pairSum_cube _ _ _

/-- The mixed top coefficient is 2*2 times the actual nonzero eight-generator word. -/
theorem test_mixed_square :
    testT ^ 2 * testU ^ 2 = (4 : ℂ) • (List.ofFn (coordinatePair oneSite)).prod := by
  have ht := (squareZero_list_sum_top [coordinatePair oneSite ⟨0, by decide⟩,
    coordinatePair oneSite ⟨1, by decide⟩] (by
      intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> exact coordinatePair_square _ _)).1
  have hu := (squareZero_list_sum_top [coordinatePair oneSite ⟨2, by decide⟩,
    coordinatePair oneSite ⟨3, by decide⟩] (by
      intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> exact coordinatePair_square _ _)).1
  have ht' : testT ^ 2 = (2 : bilinearAlgebra oneSite) *
      (coordinatePair oneSite ⟨0, by decide⟩ * coordinatePair oneSite ⟨1, by decide⟩) := by
    simpa [testT, pairSum] using ht
  have hu' : testU ^ 2 = (2 : bilinearAlgebra oneSite) *
      (coordinatePair oneSite ⟨2, by decide⟩ * coordinatePair oneSite ⟨3, by decide⟩) := by
    simpa [testU, pairSum] using hu
  rw [ht', hu']
  norm_num [List.ofFn_succ, Algebra.smul_def, FiniteGrassmannCoframe.volume, oneSite, Site]
  simp only [Fin.cast, Fin.succ, map_ofNat]
  norm_num
  ring

/-- The mixed factorial witness is nonzero in the genuine Grassmann carrier. -/
theorem test_mixed_nonzero :
    (testT : Grassmann oneSite) ^ 2 * (testU : Grassmann oneSite) ^ 2 ≠ 0 := by
  have hn : testT ^ 2 * testU ^ 2 ≠ 0 := by
    rw [test_mixed_square]
    exact smul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (coordinatePair_product_nonzero oneSite)
  intro hz
  apply hn
  apply Subtype.ext
  exact hz

theorem test_square_nonzero : (testT : Grassmann oneSite) ^ 2 ≠ 0 := by
  intro hz
  exact test_mixed_nonzero (by rw [hz, zero_mul])

/-- Complex linear source: actual integral retains the minus quadratic and its factorial. -/
theorem complex_linear_integral (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ, auxiliaryWeight σ (compensationPolynomial 2 σ compensationLinearSource) h •
      nilExp 2 (linearField oneSite (fun _ ↦ testT) h) ∂gaussianMeasure (Fin 1) v) =
      1 + Complex.I • (testT : Grassmann oneSite) -
        (1 / 2 : ℂ) • (testT : Grassmann oneSite) ^ 2 := by
  rw [← gaussian_eq7 oneSite 2 σ hσ v hv _
    (single_jointZero _ _ _ testT_cube) compensationLinearSource
    compensationLinearSource_constantCoeff]
  have he : ((MvPolynomial.aeval (fun _ : Fin 1 ↦ testT) compensationLinearSource :
      bilinearAlgebra oneSite) : Grassmann oneSite) = Complex.I • (testT : Grassmann oneSite) := by
    simp [compensationLinearSource, MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  rw [he, nilExp_two, smul_pow, smul_smul]
  norm_num [Complex.I_sq, neg_smul, sub_eq_add_neg]

/-- The surviving quadratic actually distinguishes the integral from its linear truncation. -/
theorem complex_linear_not_linear :
    1 + Complex.I • (testT : Grassmann oneSite) -
      (1 / 2 : ℂ) • (testT : Grassmann oneSite) ^ 2 ≠
        1 + Complex.I • (testT : Grassmann oneSite) := by
  intro he
  have hz : (1 / 2 : ℂ) • (testT : Grassmann oneSite) ^ 2 = 0 :=
    sub_eq_self.mp he
  exact (smul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) test_square_nonzero) hz

/-- Raw mixed moment is divided by 2!*2!, not 4!. -/
theorem mixed_raw_factorial (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 2 → ℝ, auxiliaryWeight σ (compensationPolynomial 4 σ compensationMixedSource) h *
      (auxiliaryMonomial (2 • compensationMixedIndex) h : ℂ) ∂gaussianMeasure (Fin 2) v) /
        ((Nat.factorial 2 : ℂ) * (Nat.factorial 2 : ℂ)) = Complex.I := by
  rw [compensation_control_mixed_raw σ hσ v hv]
  norm_num

/-- All actual mixed coframe monomials above the shared cutoff vanish. -/
theorem actual_global_mixed_bound (L : Torus) (U : Links L)
    (β : (Site L × Fin 4 × Fin 4) →₀ ℕ) (hβ : 4 * volume L < β.degree) :
    ((β.prod (fun i e ↦ coframeEven L U i ^ e) : bilinearAlgebra L) : Grassmann L) = 0 := by
  rw [coframe_jointZero L U β hβ]
  rfl

/-- The mandatory cross-site witness is nonzero before the shared mixed cutoff. -/
theorem actual_cross_site_nonzero (L : Torus) (x y : Site L) (hxy : x ≠ y) :
    pair L (x, Sum.inr 0) (x, Sum.inl 0) *
      pair L (y, Sum.inr 0) (y, Sum.inl 0) ≠ 0 :=
  two_site_bilinear_product_nonzero L x y hxy

/-- True zero-cutoff integrand is one, separately from positive-cutoff zero coframes. -/
theorem zero_cutoff_integrand (L : Torus) (σ : ℝ)
    (S : MvPolynomial ι ℂ) (hS : S.constantCoeff = 0)
    (t : ι → bilinearAlgebra L) (h : ι → ℝ) :
    auxiliaryWeight σ (compensationPolynomial 0 σ S) h •
      nilExp 0 (linearField L t h) = 1 := by
  rw [compensation_M_zero σ S hS, nilExp_zero_cutoff]
  simp [auxiliaryWeight, MvPolynomial.support_one, auxiliaryDegree, auxiliaryHermite]

/-- Empty coordinates give the constant integrand at every cutoff. -/
theorem empty_integrand (L : Torus) (M : ℕ) (σ : ℝ)
    (S : MvPolynomial (Fin 0) ℂ) (hS : S.constantCoeff = 0)
    (t : Fin 0 → bilinearAlgebra L) (h : Fin 0 → ℝ) :
    auxiliaryWeight σ (compensationPolynomial M σ S) h •
      nilExp M (linearField L t h) = 1 := by
  rw [(compensation_empty M σ S hS).2]
  simp [linearField, auxiliaryWeight, MvPolynomial.support_one, auxiliaryDegree, auxiliaryHermite]

/-- Source tails change neither the compensation polynomial nor the actual G value. -/
theorem source_truncation_locality (L : Torus) (M : ℕ) (σ : ℝ)
    (S : MvPolynomial ι ℂ) (hS : S.constantCoeff = 0)
    (t : ι → bilinearAlgebra L) (ht : JointZero M t) :
    compensationPolynomial M σ S = compensationPolynomial M σ
      (MvPowerSeries.truncTotal (M + 1) (S : MvPowerSeries ι ℂ)) ∧
    nilExp M ((MvPolynomial.aeval t S : bilinearAlgebra L) : Grassmann L) =
      nilExp M ((MvPolynomial.aeval t
        (MvPowerSeries.truncTotal (M + 1) (S : MvPowerSeries ι ℂ)) : bilinearAlgebra L) :
          Grassmann L) := by
  refine ⟨compensation_source_truncation M σ S hS, ?_⟩
  rw [eval_trunc_poly M t ht]

/-- Source evaluation and the mixed factorial produce the actual i*t²*u² term. -/
theorem mixed_integral (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 2 → ℝ, auxiliaryWeight σ (compensationPolynomial 4 σ compensationMixedSource) h •
      nilExp 4 (linearField oneSite ![testT, testU] h) ∂gaussianMeasure (Fin 2) v) =
      1 + (1 + Complex.I) • ((testT : Grassmann oneSite) * (testU : Grassmann oneSite)) +
        Complex.I • ((testT : Grassmann oneSite) ^ 2 * (testU : Grassmann oneSite) ^ 2) := by
  have hg (i : Fin 2) : ((![testT, testU] i : bilinearAlgebra oneSite) : Grassmann oneSite) ∈
      grade oneSite 2 := by
    fin_cases i <;> exact Submodule.add_mem (grade oneSite 2)
      (pair_grade oneSite _ _) (pair_grade oneSite _ _)
  have hj : JointZero 4 (![testT, testU]) := by
    simpa [FiniteGrassmannCoframe.volume, Site, oneSite] using
      grade_two_jointZero oneSite (![testT, testU]) hg
  rw [← gaussian_eq7 oneSite 4 σ hσ v hv _ hj compensationMixedSource
    compensationMixedSource_constantCoeff]
  have hz : (testT * testU) ^ 3 = 0 := by rw [mul_pow, testT_cube, zero_mul]
  have hs : ((1 + Complex.I) • (testT * testU)) ^ 3 = 0 := by
    rw [smul_pow, hz, smul_zero]
  have he : MvPolynomial.aeval (![testT, testU]) compensationMixedSource =
      (1 + Complex.I) • (testT * testU) := by
    simp [compensationMixedSource, compensationMixedIndex, MvPolynomial.aeval_monomial,
      ← Algebra.smul_def, add_smul]
  rw [he]
  have hsG : (((1 + Complex.I) • (testT * testU) : bilinearAlgebra oneSite) :
      Grassmann oneSite) ^ 3 = 0 := by
    simpa only [map_pow, map_zero, Subalgebra.coe_val] using
      congrArg (bilinearAlgebra oneSite).val hs
  rw [nilExp_cutoff 2 4 _ hsG (by omega), nilExp_two]
  have hsq : ((1 + Complex.I) • (testT * testU)) ^ 2 =
      (2 * Complex.I) • (testT ^ 2 * testU ^ 2) := by
    rw [smul_pow, mul_pow]
    congr 1
    calc
      (1 + Complex.I) ^ 2 = 1 + 2 * Complex.I + Complex.I ^ 2 := by ring
      _ = 2 * Complex.I := by rw [Complex.I_sq]; ring
  have hsqG := congrArg (bilinearAlgebra oneSite).val hsq
  simp only [map_pow, map_smul, map_mul, Subalgebra.coe_val] at hsqG
  simp only [Subalgebra.coe_smul, Subalgebra.coe_mul]
  rw [hsqG, smul_smul]
  norm_num
  congr 1
  ring

/-- A wrong mixed coefficient changes the genuine integral target. -/
theorem mixed_target_not_linear :
    1 + (1 + Complex.I) • ((testT : Grassmann oneSite) * (testU : Grassmann oneSite)) +
      Complex.I • ((testT : Grassmann oneSite) ^ 2 * (testU : Grassmann oneSite) ^ 2) ≠
        1 + (1 + Complex.I) • ((testT : Grassmann oneSite) * (testU : Grassmann oneSite)) := by
  intro he
  have hz := add_left_cancel (show
      (1 + (1 + Complex.I) • ((testT : Grassmann oneSite) * (testU : Grassmann oneSite))) +
        Complex.I • ((testT : Grassmann oneSite) ^ 2 * (testU : Grassmann oneSite) ^ 2) =
      (1 + (1 + Complex.I) • ((testT : Grassmann oneSite) * (testU : Grassmann oneSite))) + 0
    by simpa using he)
  exact (smul_ne_zero Complex.I_ne_zero test_mixed_nonzero) hz

/-- A general quadratic source acts on the actual nonzero square. -/
theorem quadratic_integral (g : ℂ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ, auxiliaryWeight σ
      (compensationPolynomial 2 σ (MvPolynomial.monomial (Finsupp.single 0 2) g)) h •
      nilExp 2 (linearField oneSite (fun _ ↦ testT) h) ∂gaussianMeasure (Fin 1) v) =
      1 + g • (testT : Grassmann oneSite) ^ 2 := by
  have hS : (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2) g).constantCoeff = 0 := by
    simp [MvPolynomial.constantCoeff_monomial]
  rw [← gaussian_eq7 oneSite 2 σ hσ v hv _ (single_jointZero _ _ _ testT_cube) _ hS]
  have he : ((MvPolynomial.aeval (fun _ : Fin 1 ↦ testT)
      (MvPolynomial.monomial (Finsupp.single 0 2) g) : bilinearAlgebra oneSite) :
      Grassmann oneSite) = g • (testT : Grassmann oneSite) ^ 2 := by
    simp [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  rw [he]
  apply nilExp_squareZero oneSite 2 (by omega)
  rw [smul_pow, ← pow_mul]
  have hz : (testT : Grassmann oneSite) ^ 3 = 0 := by
    simpa only [map_pow, map_zero, Subalgebra.coe_val] using
      congrArg (bilinearAlgebra oneSite).val testT_cube
  rw [pow_eq_zero_of_le (by omega : 3 ≤ 2 * 2) hz, smul_zero]

/-- Two distinct positive variances yield the same actual compensated G value. -/
theorem quadratic_two_scales (g : ℂ) :
    (∫ h : Fin 1 → ℝ, auxiliaryWeight 2
      (compensationPolynomial 2 2 (MvPolynomial.monomial (Finsupp.single 0 2) g)) h •
      nilExp 2 (linearField oneSite (fun _ ↦ testT) h) ∂gaussianMeasure (Fin 1) 4) =
    (∫ h : Fin 1 → ℝ, auxiliaryWeight (1/2)
      (compensationPolynomial 2 (1/2) (MvPolynomial.monomial (Finsupp.single 0 2) g)) h •
      nilExp 2 (linearField oneSite (fun _ ↦ testT) h) ∂gaussianMeasure (Fin 1) (1/4)) := by
  rw [quadratic_integral g 2 (by norm_num) 4 (by norm_num),
    quadratic_integral g (1/2) (by norm_num) (1/4) (by norm_num)]

/-- The finite integral bridge also identifies the independently defined auxiliary series. -/
theorem integral_seriesEval (L : Torus) (M : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P : MvPolynomial ι ℂ)
    (t : ι → bilinearAlgebra L) (ht : JointZero M t) :
    (∫ h : ι → ℝ, auxiliaryWeight σ P h • nilExp M (linearField L t h)
      ∂gaussianMeasure ι v) =
      ((seriesEval M t ht (auxiliarySeries σ v P) : bilinearAlgebra L) : Grassmann L) := by
  rw [integral_weight_nilExp L M σ hσ v hv, included_seriesEval]
  rfl

/-- A real or imaginary Gaussian coupling produces plus or minus sigma²/2. -/
theorem uncompensated_gaussian (c : ℂ) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ, nilExp 2 (linearField oneSite (fun _ ↦ c • testT) h)
      ∂gaussianMeasure (Fin 1) v) =
      1 + (((σ ^ 2 / 2 : ℝ) : ℂ) * c ^ 2) • (testT : Grassmann oneSite) ^ 2 := by
  have hz : (c • testT) ^ 3 = 0 := by rw [smul_pow, testT_cube, smul_zero]
  have ht := single_jointZero oneSite 2 (c • testT) hz
  have he := integral_seriesEval oneSite 2 σ hσ v hv (1 : MvPolynomial (Fin 1) ℂ)
    (fun _ ↦ c • testT) ht
  have hw (h : Fin 1 → ℝ) : auxiliaryWeight σ (1 : MvPolynomial (Fin 1) ℂ) h = 1 := by
    simp [auxiliaryWeight, auxiliaryHermite, auxiliaryDegree]
  simp_rw [hw, one_smul] at he
  rw [he, auxiliarySeries_eq_exp_quadratic_mul σ hσ v hv, MvPolynomial.coe_one, mul_one]
  have hg : auxiliaryGaussianSeries (ι := Fin 1) σ =
      auxiliaryFormalExp ((auxiliaryQuadraticPolynomial σ : MvPolynomial (Fin 1) ℂ) :
        MvPowerSeries (Fin 1) ℂ) :=
    congrArg auxiliaryFormalExp (auxiliaryQuadraticPolynomial_coe σ).symm
  rw [hg]
  have hf := congrArg (bilinearAlgebra oneSite).val (seriesEval_formalExp 2
    (fun _ : Fin 1 ↦ c • testT) ht (auxiliaryQuadraticPolynomial σ)
      (auxiliaryQuadraticPolynomial_constantCoeff σ))
  simp only [map_nilExp, Subalgebra.coe_val] at hf
  rw [hf]
  have hq : ((MvPolynomial.aeval (fun _ : Fin 1 ↦ c • testT)
      (auxiliaryQuadraticPolynomial σ) : bilinearAlgebra oneSite) : Grassmann oneSite) =
      (((σ ^ 2 / 2 : ℝ) : ℂ) * c ^ 2) • (testT : Grassmann oneSite) ^ 2 := by
    simp [auxiliaryQuadraticPolynomial, ← Algebra.smul_def, smul_pow, smul_smul]
    congr 1
    ring
  rw [hq]
  apply nilExp_squareZero oneSite 2 (by omega)
  rw [smul_pow, ← pow_mul]
  have hz3 : (testT : Grassmann oneSite) ^ 3 = 0 := by
    simpa only [map_pow, map_zero, Subalgebra.coe_val] using
      congrArg (bilinearAlgebra oneSite).val testT_cube
  rw [pow_eq_zero_of_le (by omega : 3 ≤ 2 * 2) hz3, smul_zero]

/-- The imaginary Gaussian coupling reverses the actual nonzero quadratic sign. -/
theorem imaginary_gaussian (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ, nilExp 2 (linearField oneSite (fun _ ↦ Complex.I • testT) h)
      ∂gaussianMeasure (Fin 1) v) =
      1 - (((σ ^ 2 / 2 : ℝ) : ℂ)) • (testT : Grassmann oneSite) ^ 2 := by
  rw [uncompensated_gaussian Complex.I σ hσ v hv, Complex.I_sq]
  simp [neg_smul, sub_eq_add_neg]

/-- The compensation polynomial changes with the variance even though Eq7 does not. -/
theorem quadratic_compensation_coefficient (g : ℂ) (σ : ℝ) :
    (compensationPolynomial 2 σ
      (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2) g)).coeff (Finsupp.single 0 2) =
      g - ((σ ^ 2 / 2 : ℝ) : ℂ) := by
  rw [compensationPolynomial_coeff_finite _ _ _ (by simp [MvPolynomial.constantCoeff_monomial])]
  norm_num [auxiliaryDegree, auxiliaryFiniteExp, auxiliaryQuadraticPolynomial,
    Finset.sum_range_succ, MvPolynomial.C_mul_X_pow_eq_monomial,
    MvPolynomial.monomial_pow, MvPolynomial.monomial_mul, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, MvPolynomial.coeff_smul, MvPolynomial.coeff_one,
    map_neg, ← Finsupp.single_add, Finsupp.single_smul,
    Finsupp.ext_iff, Fin.forall_fin_one,
    Finsupp.single_eq_zero, smul_eq_mul]
  ring

/-- Degree-one compensation is genuinely linear, independently of the variance. -/
theorem linear_compensation_one (σ : ℝ) :
    compensationPolynomial 1 σ compensationLinearSource = 1 + compensationLinearSource := by
  ext β
  have hb : β = Finsupp.single 0 (β 0) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  rw [hb]
  rw [compensationPolynomial_coeff_finite _ _ _ compensationLinearSource_constantCoeff]
  by_cases hn : β 0 ≤ 1
  · interval_cases hk : β 0 <;>
      norm_num [auxiliaryDegree, auxiliaryFiniteExp, auxiliaryQuadraticPolynomial,
        compensationLinearSource, Finset.sum_range_succ, MvPolynomial.C_mul_X_pow_eq_monomial,
        MvPolynomial.monomial_pow, MvPolynomial.monomial_mul, MvPolynomial.coeff_sum,
        MvPolynomial.coeff_monomial, MvPolynomial.coeff_smul, MvPolynomial.coeff_one,
        map_neg, ← Finsupp.single_add, Finsupp.single_smul,
        Finsupp.ext_iff, Fin.forall_fin_one, smul_eq_mul]
  · have hn0 : β 0 ≠ 0 := by omega
    have hn1 : β 0 ≠ 1 := by omega
    simp [auxiliaryDegree, hn, compensationLinearSource, MvPolynomial.coeff_monomial,
      MvPolynomial.coeff_one, Ne.symm hn0, Ne.symm hn1, Finsupp.ext_iff, Fin.forall_fin_one]

/-- Scalar Hermite transformation is additive; no nonlinear integral map is assumed. -/
theorem auxiliaryWeight_add (σ : ℝ) (P Q : MvPolynomial ι ℂ) (h : ι → ℝ) :
    auxiliaryWeight σ (P + Q) h = auxiliaryWeight σ P h + auxiliaryWeight σ Q h := by
  classical
  change (AddMonoidAlgebra.coeff (P + Q)).sum (fun α c ↦ c * ((σ ^ auxiliaryDegree α)⁻¹ : ℝ) *
      (auxiliaryHermite σ α h : ℂ)) = _
  exact Finsupp.sum_add_index (by intros; simp) (by intros; ring)

/-- The positive-cutoff zero-coframe test weight is 1+i*h/sigma², not pointwise one. -/
theorem nonconstant_weight_formula (σ : ℝ) (h : Fin 1 → ℝ) :
    auxiliaryWeight σ (compensationPolynomial 1 σ compensationLinearSource) h =
      1 + Complex.I * (h 0 : ℂ) / (σ : ℂ) ^ 2 := by
  rw [linear_compensation_one, auxiliaryWeight_add]
  norm_num [auxiliaryWeight, compensationLinearSource, MvPolynomial.support_monomial,
    MvPolynomial.coeff_monomial, auxiliaryDegree, auxiliaryHermite,
    Polynomial.hermite_one, Complex.ofReal_div, Complex.ofReal_inv, div_eq_mul_inv]
  ring

/-- Two explicit auxiliary field values separate the weight at every positive scale. -/
theorem nonconstant_weight_values (σ : ℝ) (hσ : 0 < σ) :
    auxiliaryWeight σ (compensationPolynomial 1 σ compensationLinearSource) (fun _ ↦ 0) = 1 ∧
    auxiliaryWeight σ (compensationPolynomial 1 σ compensationLinearSource) (fun _ ↦ σ ^ 2) =
      1 + Complex.I := by
  constructor
  · simp [nonconstant_weight_formula]
  · rw [nonconstant_weight_formula]
    have hs : (σ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hσ
    push_cast
    field_simp

/-- The nonconstant scalar weight has mean one against its actual Gaussian. -/
theorem nonconstant_weight_mean (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ, (1 + Complex.I * (h 0 : ℂ) / (σ : ℂ) ^ 2)
      ∂gaussianMeasure (Fin 1) v) = 1 := by
  simp_rw [← nonconstant_weight_formula]
  exact compensation_weight_mean 1 σ hσ v hv _ compensationLinearSource_constantCoeff

/-- Genuine G-valued zero-family integral with the explicit nonconstant weight. -/
theorem nonconstant_zero_family_integral (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ, (1 + Complex.I * (h 0 : ℂ) / (σ : ℂ) ^ 2) • (1 : Grassmann L)
      ∂gaussianMeasure (Fin 1) v) = 1 := by
  rw [integral_smul_const, nonconstant_weight_mean σ hσ v hv, one_smul]

/-- Both variance choices change the actual ordinary coefficient. -/
theorem quadratic_two_scale_coefficients (g : ℂ) :
    (compensationPolynomial 2 2
      (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2) g)).coeff (Finsupp.single 0 2) =
        g - 2 ∧
    (compensationPolynomial 2 (1/2)
      (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2) g)).coeff (Finsupp.single 0 2) =
        g - 1/8 := by
  constructor <;> rw [quadratic_compensation_coefficient] <;> norm_num

/-- The fourteen-generator word is nonzero; it consists of the seven disjoint coordinate pairs. -/
theorem seven_word_nonzero (L : Torus) :
    (((pairPrefix L 7).prod : bilinearAlgebra L) : Grassmann L) ≠ 0 := by
  intro hz
  exact pairPrefix_product_nonzero L 7 (Subtype.ext hz)

/-- The retained degree-seven contribution changes the actual target from one. -/
theorem high_target_nontrivial (L : Torus) (hV : 2 ≤ volume L) :
    1 + Complex.I • ((((pairPrefix L 7).sum : bilinearAlgebra L) : Grassmann L) ^ 7) ≠ 1 := by
  intro he
  have hz := add_left_cancel (show
      (1 : Grassmann L) + Complex.I •
        ((((pairPrefix L 7).sum : bilinearAlgebra L) : Grassmann L) ^ 7) = 1 + 0 by
    simpa using he)
  exact (smul_ne_zero Complex.I_ne_zero (seven_pair_actual L hV).2.2) hz

/-- The positive cutoff test weight is demonstrably nonconstant. -/
theorem weight_values_differ (σ : ℝ) (hσ : 0 < σ) :
    auxiliaryWeight σ (compensationPolynomial 1 σ compensationLinearSource) (fun _ ↦ 0) ≠
      auxiliaryWeight σ (compensationPolynomial 1 σ compensationLinearSource) (fun _ ↦ σ ^ 2) := by
  rw [(nonconstant_weight_values σ hσ).1, (nonconstant_weight_values σ hσ).2]
  norm_num [Complex.ext_iff]

/-- Compensation polynomials at the two variances really differ. -/
theorem quadratic_polynomials_differ (g : ℂ) :
    compensationPolynomial 2 2 (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2) g) ≠
      compensationPolynomial 2 (1/2) (MvPolynomial.monomial (Finsupp.single 0 2) g) := by
  intro he
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 2)) he
  rw [(quadratic_two_scale_coefficients g).1, (quadratic_two_scale_coefficients g).2] at hc
  have hz : (2 : ℂ) = 1/8 := (sub_right_inj).mp hc
  norm_num at hz

/-- True M=0 constant-integrand identity on the actual Gaussian measure. -/
theorem zero_cutoff_integral (L : Torus) (σ : ℝ)
    (v : ℝ≥0) (S : MvPolynomial ι ℂ) (hS : S.constantCoeff = 0)
    (t : ι → bilinearAlgebra L) :
    (∫ h : ι → ℝ, auxiliaryWeight σ (compensationPolynomial 0 σ S) h •
      nilExp 0 (linearField L t h) ∂gaussianMeasure ι v) = 1 := by
  simp_rw [zero_cutoff_integrand L σ S hS t]
  simp [gaussianMeasure]

/-- Empty-coordinate Gaussian identity for every cutoff, without nonempty hypotheses. -/
theorem empty_integral (L : Torus) (M : ℕ) (σ : ℝ)
    (v : ℝ≥0) (S : MvPolynomial (Fin 0) ℂ) (hS : S.constantCoeff = 0)
    (t : Fin 0 → bilinearAlgebra L) :
    (∫ h : Fin 0 → ℝ, auxiliaryWeight σ (compensationPolynomial M σ S) h •
      nilExp M (linearField L t h) ∂gaussianMeasure (Fin 0) v) = 1 := by
  simp_rw [empty_integrand L M σ S hS t]
  simp [gaussianMeasure]

/-- Source locality holds for the actual integral as well as for the polynomial and G target. -/
theorem integral_source_truncation (L : Torus) (M : ℕ) (σ : ℝ)
    (v : ℝ≥0) (S : MvPolynomial ι ℂ) (hS : S.constantCoeff = 0)
    (t : ι → bilinearAlgebra L) :
    (∫ h : ι → ℝ, auxiliaryWeight σ (compensationPolynomial M σ S) h •
      nilExp M (linearField L t h) ∂gaussianMeasure ι v) =
    (∫ h : ι → ℝ, auxiliaryWeight σ (compensationPolynomial M σ
      (MvPowerSeries.truncTotal (M + 1) (S : MvPowerSeries ι ℂ))) h •
        nilExp M (linearField L t h) ∂gaussianMeasure ι v) := by
  rw [compensation_source_truncation M σ S hS]

/-- Increasing a valid common cutoff changes neither the compensated integral nor its G value. -/
theorem integral_cutoff (L : Torus) (M K : ℕ) (hMK : M ≤ K)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : MvPolynomial ι ℂ) (hS : S.constantCoeff = 0)
    (t : ι → bilinearAlgebra L) (ht : JointZero M t) :
    (∫ h : ι → ℝ, auxiliaryWeight σ (compensationPolynomial K σ S) h •
      nilExp K (linearField L t h) ∂gaussianMeasure ι v) =
    (∫ h : ι → ℝ, auxiliaryWeight σ (compensationPolynomial M σ S) h •
      nilExp M (linearField L t h) ∂gaussianMeasure ι v) := by
  rw [← gaussian_eq7 L K σ hσ v hv t (jointZero_mono M K t ht hMK) S hS,
    ← gaussian_eq7 L M σ hσ v hv t ht S hS]
  have he := congrArg (bilinearAlgebra L).val (positive_source_cutoff M K t ht S hS hMK)
  simpa only [map_nilExp, Subalgebra.coe_val] using he

/-- The nonzero discarded scalar tail is killed by the actual common zero-cutoff ideal. -/
theorem scalar_tail_actual_cutoff (L : Torus) (t : Fin 1 → bilinearAlgebra L)
    (ht : JointZero 0 t) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 2)
      (auxiliaryGaussianSeries 2 *
        ((compensationPolynomial 0 2 (0 : MvPolynomial (Fin 1) ℂ) :
          MvPolynomial (Fin 1) ℂ) : MvPowerSeries (Fin 1) ℂ)) = 2 ∧
      ((t 0 : Grassmann L) ^ 2) = 0 := by
  refine ⟨compensation_control_tail, ?_⟩
  have hz := (jointZero_zero_cutoff_iff t).mp ht 0
  rw [hz]
  simp

/-- A concrete positive regulator with at least two sites, for the degree-seven test. -/
def highTestTorus : Torus := ⟨fun _ ↦ 2, by simp⟩

theorem highTestTorus_volume : volume highTestTorus = 16 := by
  norm_num [FiniteGrassmannCoframe.volume, Site, highTestTorus]

/-- Concrete actual G-valued degree-seven integral differs from one. -/
theorem high_concrete_integral_nontrivial (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ, auxiliaryWeight σ (compensationPolynomial 7 σ compensationHighSource) h •
      nilExp 7 (linearField highTestTorus (fun _ ↦ (pairPrefix highTestTorus 7).sum) h)
      ∂gaussianMeasure (Fin 1) v) ≠ 1 := by
  have hV : 2 ≤ volume highTestTorus := by rw [highTestTorus_volume]; omega
  rw [high_source_integral highTestTorus hV σ hσ v hv]
  exact high_target_nontrivial highTestTorus hV

/-- Real Gaussian coupling retains the positive sigma²/2 coefficient in G. -/
theorem real_gaussian (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ h : Fin 1 → ℝ, nilExp 2 (linearField oneSite (fun _ ↦ testT) h)
      ∂gaussianMeasure (Fin 1) v) =
      1 + (((σ ^ 2 / 2 : ℝ) : ℂ)) • (testT : Grassmann oneSite) ^ 2 := by
  simpa using uncompensated_gaussian 1 σ hσ v hv

end SKEFTHawking.ADW.GaussianGrassmannAuxiliary
