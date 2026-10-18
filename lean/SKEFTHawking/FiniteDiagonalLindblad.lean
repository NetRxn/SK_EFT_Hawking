import SKEFTHawking.FiniteGibbsDephasingConvergence

/-! Finite diagonal Lindblad generators and their signature-block fixed algebra. -/
noncomputable section
open Matrix Filter
open scoped ComplexOrder InnerProductSpace Topology
namespace SKEFTHawking.FinitePositiveKernel.DiagonalLindblad
open OpenSystems GibbsObservable
variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

/-- Real diagonal noise observables. -/
def jumps (ell : κ → n → ℝ) (r : κ) : Matrix n n ℂ := diagonal (fun i => (ell r i : ℂ))

/-- The pairwise decay rate is computed from the actual jumps. -/
def rate (ell : κ → n → ℝ) (i j : n) : ℝ := (∑ r, (ell r i - ell r j)^2)/2

omit [Fintype n] [DecidableEq n] in
theorem rate_nonneg (ell : κ → n → ℝ) (i j : n) : 0 ≤ rate ell i j := by
  unfold rate
  positivity

omit [Fintype n] [DecidableEq n] in
@[simp] theorem rate_self (ell : κ → n → ℝ) (i : n) : rate ell i i = 0 := by
  simp [rate]

theorem generator_entry (ell : κ → n → ℝ) (X : Matrix n n ℂ) (i j : n) :
    lindbladGenerator 0 (jumps ell) X i j = -(rate ell i j : ℂ) * X i j := by
  have hstar (r : κ) : (jumps ell r)ᴴ = jumps ell r := by
    ext k l
    by_cases h : k = l <;> simp [jumps, Matrix.conjTranspose_apply, h, eq_comm]
  simp only [lindbladGenerator, LinearMap.add_apply, lindbladHamPart_apply,
    lindbladJump_apply, lindbladAnticommPart_apply, zero_mul, mul_zero, sub_self,
    smul_zero, zero_add, hstar]
  simp [jumps, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.sum_apply,
    rate, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem liouvillian_diagonal (ell : κ → n → ℝ) :
    lindbladLiouvillian 0 (jumps ell) = diagonal (fun p : n × n => -(rate ell p.1 p.2 : ℂ)) := by
  ext p q
  rw [lindbladLiouvillian, LinearMap.toMatrix_apply]
  change lindbladGenerator 0 (jumps ell) (Matrix.stdBasis ℂ n n q) p.1 p.2 = _
  rw [generator_entry]
  simp [Matrix.stdBasis, Matrix.diagonal_apply, Pi.single_apply, Prod.ext_iff, ite_and, ite_apply]

 theorem toLin_diagonal_entry (d : n × n → ℂ) (X : Matrix n n ℂ) (i j : n) :
    Matrix.toLin (Matrix.stdBasis ℂ n n) (Matrix.stdBasis ℂ n n) (diagonal d) X i j =
      d (i,j) * X i j := by
  rw [Matrix.toLin_apply]
  simp [Matrix.stdBasis, Matrix.sum_apply, Fintype.sum_prod_type, Matrix.mulVec_diagonal,
    Pi.single_apply, ite_apply]

/-- Entries of the existing exponential, not a replacement evolution. -/
theorem propagator_entry (ell : κ → n → ℝ) (t : ℝ) (X : Matrix n n ℂ) (i j : n) :
    lindbladPropagatorAction 0 (jumps ell) t X i j =
      (Real.exp (-t * rate ell i j) : ℂ) * X i j := by
  unfold lindbladPropagatorAction lindbladPropagator
  rw [liouvillian_diagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal, toLin_diagonal_entry]
  congr 1
  simp [← Complex.exp_eq_exp_ℂ]

omit [Fintype n] [DecidableEq n] in
/-- Zero rate means equality of every jump signature. -/
theorem rate_eq_zero_iff (ell : κ → n → ℝ) (i j : n) :
    rate ell i j = 0 ↔ ∀ r, ell r i = ell r j := by
  unfold rate
  rw [div_eq_zero_iff]
  simp only [OfNat.ofNat_ne_zero, or_false]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg (ell r i - ell r j))]
  simp [sub_eq_zero]

/-- The fixed observable retains entire equal-signature blocks. -/
def blockExpectation (ell : κ → n → ℝ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => if rate ell i j = 0 then X i j else 0

omit [Fintype n] [DecidableEq n] in
theorem blockExpectation_idempotent (ell : κ → n → ℝ) (X : Matrix n n ℂ) :
    blockExpectation ell (blockExpectation ell X) = blockExpectation ell X := by
  ext i j
  by_cases h : rate ell i j = 0 <;> simp [blockExpectation, h]

theorem propagator_diagonal (ell : κ → n → ℝ) (t : ℝ) (d : n → ℂ) :
    lindbladPropagatorAction 0 (jumps ell) t (diagonal d) = diagonal d := by
  ext i j
  rw [propagator_entry]
  by_cases h : i = j <;> simp [h]

/-- A faithful diagonal weight; normalization is independent of the norm estimates. -/
def density (w : n → ℝ) : Matrix n n ℂ := diagonal (fun i => (w i : ℂ))

omit [Fintype n] in
theorem density_posDef (w : n → ℝ) (hw : ∀ i, 0 < w i) : (density w).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast hw i

abbrev WeightedSpace (w : n → ℝ) (hw : ∀ i, 0 < w i) :=
  Space (gram (density w)) (gram_posSemidef (density_posDef w hw).posSemidef)

/-- The reconstructed squared norm is a weighted sum over all matrix entries. -/
theorem pairing_density (w : n → ℝ) (c : n × n → ℂ) :
    (pairing (gram (density w)) c c).re = ∑ p : n × n, w p.2 * ‖c p‖^2 := by
  simp only [← Complex.normSq_eq_norm_sq]
  simp [pairing, gram_entry, density, Matrix.diagonal_apply, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, Complex.normSq_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Entry multipliers act on the original reconstruction coefficients. -/
def entryMap (m : n × n → ℂ) : (n × n → ℂ) →ₗ[ℂ] (n × n → ℂ) where
  toFun c p := m p * c p
  map_add' c d := by ext p; simp [mul_add]
  map_smul' a c := by ext p; simp [mul_left_comm]

/-- A pointwise multiplier bound yields the actual weighted energy bound. -/
theorem entryMap_energy_le (w : n → ℝ) (hw : ∀ i, 0 < w i)
    (m : n × n → ℂ) (hm : ∀ p, ‖m p‖ ≤ 1) (c : n × n → ℂ) :
    (pairing (gram (density w)) (entryMap m c) (entryMap m c)).re ≤
      (pairing (gram (density w)) c c).re := by
  rw [pairing_density, pairing_density]
  apply Finset.sum_le_sum
  intro p _
  change w p.2 * ‖m p * c p‖^2 ≤ _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (hw p.2).le
  have h := mul_le_mul_of_nonneg_right (hm p) (norm_nonneg (c p))
  exact pow_le_pow_left₀ (by positivity) (by simpa using h) 2

/-- Both time evolution and its limit use the existing energy-controlled quotient descent. -/
def quotientEntry (w : n → ℝ) (hw : ∀ i, 0 < w i)
    (m : n × n → ℂ) (hm : ∀ p, ‖m p‖ ≤ 1) :
    WeightedSpace w hw →L[ℂ] WeightedSpace w hw :=
  descendContraction (gram_posSemidef (density_posDef w hw).posSemidef)
    (entryMap m) (entryMap_energy_le w hw m hm)

theorem quotientEntry_observable (w : n → ℝ) (hw : ∀ i, 0 < w i)
    (m : n × n → ℂ) (hm : ∀ p, ‖m p‖ ≤ 1) (X : Matrix n n ℂ) :
    quotientEntry w hw m hm (observable (density_posDef w hw).posSemidef X) =
      observable (density_posDef w hw).posSemidef (fun i j => m (i,j) * X i j) := by
  change descend _ _ _ (mk _ _ _) = _
  rw [descend_mk]
  rfl

omit [Fintype n] [DecidableEq n] in
theorem exp_rate_norm_le (ell : κ → n → ℝ) (t : ℝ) (ht : 0 ≤ t) (p : n × n) :
    ‖(Real.exp (-t * rate ell p.1 p.2) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  nlinarith [rate_nonneg ell p.1 p.2]

/-- The descended actual Lindblad exponential. -/
def evolution (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) : WeightedSpace w hw →L[ℂ] WeightedSpace w hw :=
  quotientEntry w hw (fun p => (Real.exp (-t * rate ell p.1 p.2) : ℂ))
    (exp_rate_norm_le ell t ht)

theorem evolution_observable (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (X : Matrix n n ℂ) :
    evolution w hw ell t ht (observable (density_posDef w hw).posSemidef X) =
      observable (density_posDef w hw).posSemidef
        (lindbladPropagatorAction 0 (jumps ell) t X) := by
  rw [evolution, quotientEntry_observable]
  apply congrArg (observable _)
  ext i j
  exact (propagator_entry ell t X i j).symm

theorem evolution_norm_le (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (z : WeightedSpace w hw) : ‖evolution w hw ell t ht z‖ ≤ ‖z‖ :=
  descend_norm_le _ _ (entryMap_energy_le w hw _ (exp_rate_norm_le ell t ht)) z

/-- The limit retains exactly the zero-rate entries. -/
def projection (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ) :
    WeightedSpace w hw →L[ℂ] WeightedSpace w hw :=
  quotientEntry w hw (fun p => if rate ell p.1 p.2 = 0 then 1 else 0)
    (by intro p; split_ifs <;> norm_num)

theorem projection_observable (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (X : Matrix n n ℂ) :
    projection w hw ell (observable (density_posDef w hw).posSemidef X) =
      observable (density_posDef w hw).posSemidef (blockExpectation ell X) := by
  rw [projection, quotientEntry_observable]
  apply congrArg (observable _)
  ext i j
  by_cases h : rate ell i j = 0 <;> simp [blockExpectation, h]

theorem projection_idempotent (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (z : WeightedSpace w hw) : projection w hw ell (projection w hw ell z) = projection w hw ell z := by
  obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [projection_observable, projection_observable, blockExpectation_idempotent]

theorem observable_norm_sq (w : n → ℝ) (hw : ∀ i, 0 < w i) (X : Matrix n n ℂ) :
    ‖observable (density_posDef w hw).posSemidef X‖^2 = ∑ p : n × n, w p.2 * ‖X p.1 p.2‖^2 := by
  rw [observable, norm_mk_sq, pairing_density]

/-- Entrywise comparison is measured in the reconstructed norm, not an auxiliary norm. -/
theorem observable_norm_le (w : n → ℝ) (hw : ∀ i, 0 < w i)
    (X Y : Matrix n n ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i j, ‖Y i j‖ ≤ C * ‖X i j‖) :
    ‖observable (density_posDef w hw).posSemidef Y‖ ≤
      C * ‖observable (density_posDef w hw).posSemidef X‖ := by
  have hs : ‖observable (density_posDef w hw).posSemidef Y‖^2 ≤
      C^2 * ‖observable (density_posDef w hw).posSemidef X‖^2 := by
    rw [observable_norm_sq w hw, observable_norm_sq w hw, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    have hp := pow_le_pow_left₀ (norm_nonneg (Y p.1 p.2)) (h p.1 p.2) 2
    calc
      w p.2 * ‖Y p.1 p.2‖^2 ≤ w p.2 * (C * ‖X p.1 p.2‖)^2 :=
        mul_le_mul_of_nonneg_left hp (hw p.2).le
      _ = C^2 * (w p.2 * ‖X p.1 p.2‖^2) := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  nlinarith only [hs]


/-- Quantitative convergence to the full fixed algebra from a bound on computed rates. -/
theorem evolution_error_norm_le (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (δ : ℝ) (hgap : ∀ i j, rate ell i j ≠ 0 → δ ≤ rate ell i j)
    (t : ℝ) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    ‖evolution w hw ell t ht z - projection w hw ell z‖ ≤
      Real.exp (-δ*t) * ‖z - projection w hw ell z‖ := by
  obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [evolution_observable, projection_observable]
  let L := observableLinear (density_posDef w hw).posSemidef
  change ‖L _ - L _‖ ≤ _ * ‖L _ - L _‖
  rw [← map_sub, ← map_sub]
  change ‖observable (density_posDef w hw).posSemidef
    (lindbladPropagatorAction 0 (jumps ell) t X - blockExpectation ell X)‖ ≤
    Real.exp (-δ*t) * ‖observable (density_posDef w hw).posSemidef (X - blockExpectation ell X)‖
  refine observable_norm_le w hw (X - blockExpectation ell X)
    (lindbladPropagatorAction 0 (jumps ell) t X - blockExpectation ell X)
    (Real.exp (-δ*t)) (Real.exp_pos _).le ?_
  intro i j
  change ‖lindbladPropagatorAction 0 (jumps ell) t X i j - blockExpectation ell X i j‖ ≤
    Real.exp (-δ*t) * ‖X i j - blockExpectation ell X i j‖
  rw [propagator_entry]
  by_cases h : rate ell i j = 0
  · simp [blockExpectation, h]
  · simp only [blockExpectation, h, if_false, sub_zero, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith [hgap i j h]

/-- Positive computed gap gives convergence along nonnegative actual time. -/
theorem evolution_tendsto (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ i j, rate ell i j ≠ 0 → δ ≤ rate ell i j)
    (z : WeightedSpace w hw) :
    Tendsto (fun t : NNReal => evolution w hw ell t t.property z) atTop
      (𝓝 (projection w hw ell z)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Tendsto (fun t : NNReal => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hm := Filter.Tendsto.const_mul_atTop hδ hc
  have he : Tendsto (fun t : NNReal => Real.exp (-δ*(t:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hm)
  apply squeeze_zero (fun t : NNReal => norm_nonneg _) (fun t : NNReal =>
    evolution_error_norm_le w hw ell δ hgap t t.property z)
  simpa using he.mul_const ‖z - projection w hw ell z‖

/-- Matrix fixed points are exactly the equal-signature block algebra. -/
theorem propagator_fixed_iff (ell : κ → n → ℝ) (t : ℝ) (ht : 0 < t)
    (X : Matrix n n ℂ) :
    lindbladPropagatorAction 0 (jumps ell) t X = X ↔ blockExpectation ell X = X := by
  constructor
  · intro h
    ext i j
    by_cases hr : rate ell i j = 0
    · simp [blockExpectation, hr]
    · have he := congrFun (congrFun h i) j
      rw [propagator_entry] at he
      have hp : 0 < rate ell i j := lt_of_le_of_ne (rate_nonneg ell i j) (Ne.symm hr)
      have hn : (Real.exp (-t * rate ell i j) : ℂ) ≠ 1 := by
        have he : Real.exp (-t * rate ell i j) < 1 :=
          Real.exp_lt_one_iff.mpr (by nlinarith)
        exact_mod_cast ne_of_lt he
      have hz : X i j = 0 := by
        have hh : ((Real.exp (-t * rate ell i j) : ℂ)-1)*X i j = 0 := by
          rw [sub_mul, one_mul, he, sub_self]
        exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hn)
      simp [blockExpectation, hr, hz]
  · intro h
    ext i j
    rw [propagator_entry]
    by_cases hr : rate ell i j = 0
    · simp [hr]
    · have hz := congrFun (congrFun h i) j
      simp [blockExpectation, hr] at hz
      simp [← hz]

theorem evolution_fixed_iff (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (t : ℝ) (ht : 0 < t) (z : WeightedSpace w hw) :
    evolution w hw ell t ht.le z = z ↔ projection w hw ell z = z := by
  obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [evolution_observable, projection_observable,
    (observable_injective (density_posDef w hw)).eq_iff,
    (observable_injective (density_posDef w hw)).eq_iff]
  exact propagator_fixed_iff ell t ht X

/-- The faithful diagonal weight is stationary under the actual generator's exponential. -/
theorem density_stationary (w : n → ℝ) (ell : κ → n → ℝ) (t : ℝ) :
    lindbladPropagatorAction 0 (jumps ell) t (density w) = density w :=
  propagator_diagonal ell t _

/-- Normalizing the weights gives a trace-one state without changing the proofs. -/
theorem density_trace (w : n → ℝ) : (density w).trace = ((∑ i, w i : ℝ) : ℂ) := by
  simp [density, Matrix.trace]

/-- Complete positivity is supplied by the existing general Lindblad theorem. -/
theorem propagator_CP [Nonempty n] (ell : κ → n → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    MatrixMap.IsCompletelyPositive (lindbladPropagatorAction 0 (jumps ell) t) :=
  isCompletelyPositive_lindbladPropagatorAction 0 Matrix.isHermitian_zero _ ht

theorem evolution_zero (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (z : WeightedSpace w hw) : evolution w hw ell 0 (by norm_num) z = z := by
  obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [evolution_observable]
  simp [lindbladPropagatorAction, lindblad_propagator_zero]

theorem evolution_add (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (z : WeightedSpace w hw) :
    evolution w hw ell (s+t) (add_nonneg hs ht) z =
      evolution w hw ell s hs (evolution w hw ell t ht z) := by
  obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [evolution_observable, evolution_observable, evolution_observable]
  apply congrArg (observable _)
  ext i j
  simp only [propagator_entry]
  rw [show -(s+t) * rate ell i j = -s * rate ell i j + -t * rate ell i j by ring,
    Real.exp_add, Complex.ofReal_mul, mul_assoc]

omit [Fintype n] [DecidableEq n] in
/-- Literal fixed blocks: entries joining different signatures vanish. -/
theorem blockExpectation_fixed_iff (ell : κ → n → ℝ) (X : Matrix n n ℂ) :
    blockExpectation ell X = X ↔ ∀ i j, (¬ ∀ r, ell r i = ell r j) → X i j = 0 := by
  constructor
  · intro h i j hij
    have hr : rate ell i j ≠ 0 := by simpa [rate_eq_zero_iff] using hij
    have he := congrFun (congrFun h i) j
    simpa [blockExpectation, hr] using he.symm
  · intro h
    ext i j
    by_cases hr : rate ell i j = 0
    · simp [blockExpectation, hr]
    · have hz := h i j (by simpa [← rate_eq_zero_iff] using hr)
      simp [blockExpectation, hr, hz]

/-- Each matrix unit has its own explicitly computed decay rate. -/
theorem propagator_single (ell : κ → n → ℝ) (t : ℝ) (i j : n) :
    lindbladPropagatorAction 0 (jumps ell) t (Matrix.single i j (1 : ℂ)) =
      (Real.exp (-t * rate ell i j) : ℂ) • Matrix.single i j 1 := by
  ext k l
  rw [propagator_entry]
  by_cases hi : i = k <;> by_cases hj : j = l <;>
    simp [hi, hj]

theorem projection_single_zero (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (i j : n) (hr : rate ell i j ≠ 0) :
    projection w hw ell (observable (density_posDef w hw).posSemidef (Matrix.single i j 1)) = 0 := by
  rw [projection_observable]
  have h : blockExpectation ell (Matrix.single i j (1 : ℂ)) = 0 := by
    ext k l
    by_cases hi : i = k
    · subst k
      by_cases hj : j = l
      · subst l; simp [blockExpectation, hr]
      · simp [blockExpectation, hj]
    · simp [blockExpectation, hi]
  rw [h]
  exact map_zero (observableLinear (density_posDef w hw).posSemidef)

theorem single_error_norm (w : n → ℝ) (hw : ∀ i, 0 < w i) (ell : κ → n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (i j : n) (hr : rate ell i j ≠ 0) :
    ‖evolution w hw ell t ht (observable (density_posDef w hw).posSemidef (Matrix.single i j 1)) -
      projection w hw ell (observable (density_posDef w hw).posSemidef (Matrix.single i j 1))‖ =
      Real.exp (-t * rate ell i j) *
        ‖observable (density_posDef w hw).posSemidef (Matrix.single i j 1)‖ := by
  rw [projection_single_zero w hw ell i j hr, sub_zero, evolution_observable,
    propagator_single, observable_smul, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem observable_single_nonzero (w : n → ℝ) (hw : ∀ i, 0 < w i) (i j : n) :
    observable (density_posDef w hw).posSemidef (Matrix.single i j 1) ≠ 0 := by
  rw [ne_eq, observable_eq_zero_iff (density_posDef w hw)]
  intro h
  have he := congrFun (congrFun h i) j
  simp at he

/-- No noise is the identity on the entire reconstructed space. -/
theorem evolution_zero_jumps (w : n → ℝ) (hw : ∀ i, 0 < w i) (t : ℝ) (ht : 0 ≤ t)
    (z : WeightedSpace w hw) : evolution w hw (fun (_ : κ) _ => 0) t ht z = z := by
  obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [evolution_observable]
  apply congrArg (observable _)
  ext i j
  simp [propagator_entry, rate]

/-- Three distinct signatures exhibit multiple decay rates. -/
def threeJumps : Fin 1 → Fin 3 → ℝ := fun _ i => (i.val : ℝ)

theorem three_rates : rate threeJumps 0 1 = 1/2 ∧ rate threeJumps 1 2 = 1/2 ∧
    rate threeJumps 0 2 = 2 := by norm_num [rate, threeJumps, Fin.sum_univ_one]

theorem three_gap (i j : Fin 3) (h : rate threeJumps i j ≠ 0) : 1/2 ≤ rate threeJumps i j := by
  fin_cases i <;> fin_cases j <;> norm_num [rate, threeJumps, Fin.sum_univ_one] at *

/-- A concrete normalized faithful three-level state. -/
def threeWeights : Fin 3 → ℝ := fun _ => 1/3

theorem threeWeights_pos (i : Fin 3) : 0 < threeWeights i := by norm_num [threeWeights]

theorem three_density_trace : (density threeWeights).trace = 1 := by
  rw [density_trace]
  norm_num [threeWeights, Fin.sum_univ_three]

theorem three_sharp (t : ℝ) (ht : 0 ≤ t) :
    ‖evolution threeWeights threeWeights_pos threeJumps t ht
        (observable (density_posDef threeWeights threeWeights_pos).posSemidef (Matrix.single 0 1 1)) -
      projection threeWeights threeWeights_pos threeJumps
        (observable (density_posDef threeWeights threeWeights_pos).posSemidef (Matrix.single 0 1 1))‖ =
      Real.exp (-t/2) *
        ‖observable (density_posDef threeWeights threeWeights_pos).posSemidef (Matrix.single 0 1 1)‖ := by
  rw [single_error_norm _ _ _ _ _ _ _ (by rw [three_rates.1]; norm_num), three_rates.1]
  congr 2
  ring

/-- Duplicate signatures preserve an off-diagonal block even at positive time. -/
def duplicateJumps : Fin 1 → Fin 3 → ℝ := fun _ i => if i = 2 then 1 else 0

theorem duplicate_fixed (t : ℝ) :
    lindbladPropagatorAction 0 (jumps duplicateJumps) t (Matrix.single 0 1 (1 : ℂ)) =
      Matrix.single 0 1 1 := by
  rw [propagator_single]
  have hr : rate duplicateJumps 0 1 = 0 := by
    norm_num [rate, duplicateJumps, Fin.sum_univ_one,
      show (0 : Fin 3) ≠ 2 from by decide, show (1 : Fin 3) ≠ 2 from by decide]
  rw [hr]
  simp

omit [DecidableEq n] in
/-- Finiteness supplies a positive gap on the complement, including the empty complement. -/
theorem exists_positive_gap (ell : κ → n → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, rate ell i j ≠ 0 → δ ≤ rate ell i j := by
  classical
  let s := Finset.univ.filter (fun p : n × n => rate ell p.1 p.2 ≠ 0)
  by_cases hs : s.Nonempty
  · refine ⟨s.inf' hs (fun p => rate ell p.1 p.2), ?_, ?_⟩
    · apply (Finset.lt_inf'_iff hs).mpr
      intro p hp
      have hn : rate ell p.1 p.2 ≠ 0 := (Finset.mem_filter.mp hp).2
      exact lt_of_le_of_ne (rate_nonneg ell p.1 p.2) (Ne.symm hn)
    · intro i j hij
      exact Finset.inf'_le (s := s) (fun p => rate ell p.1 p.2)
        (b := (i,j)) (by simp [s, hij])
  · refine ⟨1, by norm_num, ?_⟩
    intro i j hij
    exact False.elim (hs ⟨(i,j), by simp [s, hij]⟩)

/-- Finite diagonal noise always converges to its complete signature-block algebra. -/
theorem evolution_tendsto_fixed_algebra (w : n → ℝ) (hw : ∀ i, 0 < w i)
    (ell : κ → n → ℝ) (z : WeightedSpace w hw) :
    Tendsto (fun t : NNReal => evolution w hw ell t t.property z) atTop
      (𝓝 (projection w hw ell z)) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_positive_gap ell
  exact evolution_tendsto w hw ell δ hδ hgap z

theorem three_error_bound (t : ℝ) (ht : 0 ≤ t) (z : WeightedSpace threeWeights threeWeights_pos) :
    ‖evolution threeWeights threeWeights_pos threeJumps t ht z -
      projection threeWeights threeWeights_pos threeJumps z‖ ≤
      Real.exp (-t/2) * ‖z - projection threeWeights threeWeights_pos threeJumps z‖ := by
  have h := evolution_error_norm_le threeWeights threeWeights_pos threeJumps (1/2)
    three_gap t ht z
  convert h using 1
  congr 2
  ring

/-- The sharp three-level coherence survives faithful reconstruction. -/
theorem three_coherence_norm_pos :
    0 < ‖observable (density_posDef threeWeights threeWeights_pos).posSemidef
      (Matrix.single 0 1 1)‖ :=
  norm_pos_iff.mpr (observable_single_nonzero threeWeights threeWeights_pos 0 1)

/-- The degenerate-signature obstruction persists in the actual quotient evolution. -/
theorem duplicate_quotient_fixed (t : ℝ) (ht : 0 ≤ t) :
    evolution threeWeights threeWeights_pos duplicateJumps t ht
      (observable (density_posDef threeWeights threeWeights_pos).posSemidef (Matrix.single 0 1 1)) =
      observable (density_posDef threeWeights threeWeights_pos).posSemidef (Matrix.single 0 1 1) := by
  rw [evolution_observable, duplicate_fixed]

end SKEFTHawking.FinitePositiveKernel.DiagonalLindblad
