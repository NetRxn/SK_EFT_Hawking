import SKEFTHawking.FiniteGibbsDephasing

/-! The full fixed diagonal algebra is the limit of the actual Gibbs dephasing
channels. The same projection controls discrete iterations and Lindblad time. -/
noncomputable section
open Matrix Filter
open scoped ComplexOrder InnerProductSpace Topology
namespace SKEFTHawking.FinitePositiveKernel.GibbsDephasing
open QuantumNetwork QuantumNetwork.FiniteGibbsClock GibbsObservable OpenSystems

/-- The conditional expectation retaining every diagonal entry. -/
def diagonalExpectation (X : Matrix (Fin 2) (Fin 2) ℂ) := diagonal (diag X)

theorem dephasing_half (X : Matrix (Fin 2) (Fin 2) ℂ) :
    krausMap (dephasingKraus (1/2)) X = diagonalExpectation X := by
  ext i j
  rw [dephasing_entry (by norm_num) (by norm_num)]
  by_cases h : i = j <;> simp [diagonalExpectation, h]

/-- The projection is an existing stationary Kraus quotient, at strength one half. -/
def diagonalProjection (Δ β : ℝ) : GibbsSpace Δ β →L[ℂ] GibbsSpace Δ β :=
  quotientDephasing Δ β (1/2) (by norm_num) (by norm_num)

theorem diagonalProjection_observable (Δ β : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    diagonalProjection Δ β (observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef X) =
      observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef (diagonalExpectation X) := by
  rw [diagonalProjection, quotientDephasing_observable, dephasing_half]

theorem diagonalProjection_diagonal (Δ β : ℝ) (d : Fin 2 → ℂ) :
    diagonalProjection Δ β (observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef (diagonal d)) =
      observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef (diagonal d) := by
  rw [diagonalProjection_observable]
  simp [diagonalExpectation]

theorem diagonalProjection_idempotent (Δ β : ℝ) (z : GibbsSpace Δ β) :
    diagonalProjection Δ β (diagonalProjection Δ β z) = diagonalProjection Δ β z := by
  obtain ⟨X, rfl⟩ := observable_surjective (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef z
  rw [diagonalProjection_observable]
  exact diagonalProjection_diagonal Δ β _

theorem diagonalProjection_selfAdjoint (Δ β : ℝ) : IsSelfAdjoint (diagonalProjection Δ β) :=
  quotientDephasing_selfAdjoint _ _ _ _ _

theorem diagonalProjection_positive (Δ β : ℝ) : (diagonalProjection Δ β).IsPositive :=
  (quotientDephasing_positive_iff _ _ _ _ _).mpr (by norm_num)

theorem diagonalProjection_norm_le (Δ β : ℝ) (z : GibbsSpace Δ β) :
    ‖diagonalProjection Δ β z‖ ≤ ‖z‖ := quotientDephasing_norm_le _ _ _ _ _ z

/-- Fixed vectors are exactly the classes of all diagonal observables. -/
theorem diagonalProjection_fixed_iff (Δ β : ℝ) (z : GibbsSpace Δ β) :
    diagonalProjection Δ β z = z ↔ ∃ d : Fin 2 → ℂ,
      observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef (diagonal d) = z := by
  constructor
  · intro h
    obtain ⟨X, hX⟩ := observable_surjective (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef z
    refine ⟨diag X, ?_⟩
    rw [← h, ← hX, diagonalProjection_observable]
    rfl
  · rintro ⟨d, rfl⟩
    exact diagonalProjection_diagonal Δ β d

/-- Exact decomposition, valid for every observable rather than a single coherence. -/
theorem quotientDephasing_error (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (z : GibbsSpace Δ β) :
    quotientDephasing Δ β γ h0 h1 z - diagonalProjection Δ β z =
      (1-2*γ : ℂ) • (z - diagonalProjection Δ β z) := by
  obtain ⟨X, rfl⟩ := observable_surjective (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef z
  rw [quotientDephasing_observable, diagonalProjection_observable]
  let L := observableLinear (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef
  change L _ - L _ = (1-2*γ : ℂ) • (L _ - L _)
  rw [← map_sub, ← map_sub, ← map_smul]
  apply congrArg L
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, dephasing_entry h0 h1]
  by_cases h : i = j <;> simp [diagonalExpectation, h]

theorem quotientDephasing_projection (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (z : GibbsSpace Δ β) :
    quotientDephasing Δ β γ h0 h1 (diagonalProjection Δ β z) = diagonalProjection Δ β z := by
  have h := quotientDephasing_error Δ β γ h0 h1 (diagonalProjection Δ β z)
  rw [diagonalProjection_idempotent, sub_self, smul_zero, sub_eq_zero] at h
  exact h

theorem quotientDephasing_pow_error (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (k : ℕ) (z : GibbsSpace Δ β) :
    (quotientDephasing Δ β γ h0 h1 ^ k) z - diagonalProjection Δ β z =
      (1-2*γ : ℂ)^k • (z - diagonalProjection Δ β z) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    rw [← quotientDephasing_projection Δ β γ h0 h1 z, ← map_sub, ih, map_smul,
      map_sub, quotientDephasing_projection, quotientDephasing_error, smul_smul, pow_succ]

theorem quotientDephasing_pow_error_norm (Δ β γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (k : ℕ) (z : GibbsSpace Δ β) :
    ‖(quotientDephasing Δ β γ h0 h1 ^ k) z - diagonalProjection Δ β z‖ =
      |1-2*γ|^k * ‖z - diagonalProjection Δ β z‖ := by
  rw [quotientDephasing_pow_error, norm_smul, norm_pow]
  norm_cast

/-- Exact Gibbs norm error for the existing Lindblad propagator quotient. -/
theorem quotientLindblad_error (Δ β a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (z : GibbsSpace Δ β) :
    quotientLindblad Δ β a t ha ht z - diagonalProjection Δ β z =
      (Real.exp (-2*a*t) : ℂ) • (z - diagonalProjection Δ β z) := by
  unfold quotientLindblad
  rw [quotientDephasing_error]
  congr 1
  unfold timeStrength
  push_cast
  ring

theorem quotientLindblad_error_norm (Δ β a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (z : GibbsSpace Δ β) :
    ‖quotientLindblad Δ β a t ha ht z - diagonalProjection Δ β z‖ =
      Real.exp (-2*a*t) * ‖z - diagonalProjection Δ β z‖ := by
  rw [quotientLindblad_error, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- Every starting class converges to its full diagonal component. -/
theorem quotientDephasing_tendsto (Δ β γ : ℝ) (h0 : 0 < γ) (h1 : γ < 1)
    (z : GibbsSpace Δ β) :
    Tendsto (fun k : ℕ => (quotientDephasing Δ β γ h0.le h1.le ^ k) z)
      atTop (𝓝 (diagonalProjection Δ β z)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [quotientDephasing_pow_error_norm]
  have hlt : |1-2*γ| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hlt).mul_const
    ‖z - diagonalProjection Δ β z‖

/-- Nonnegative time parametrizes the already defined actual quotient evolution. -/
theorem quotientLindblad_tendsto (Δ β a : ℝ) (ha : 0 < a) (z : GibbsSpace Δ β) :
    Tendsto (fun t : NNReal => quotientLindblad Δ β a t ha.le t.property z)
      atTop (𝓝 (diagonalProjection Δ β z)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [quotientLindblad_error_norm]
  have hc : Tendsto (fun t : NNReal => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hm := Filter.Tendsto.const_mul_atTop (by positivity : 0 < 2*a) hc
  have he : Tendsto (fun t : NNReal => Real.exp (-2*a*(t:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hm)
  simpa using he.mul_const ‖z - diagonalProjection Δ β z‖

/-- Positive rate and positive time have precisely the full diagonal fixed algebra. -/
theorem quotientLindblad_fixed_iff (Δ β a t : ℝ) (ha : 0 < a) (ht : 0 < t)
    (z : GibbsSpace Δ β) :
    quotientLindblad Δ β a t ha.le ht.le z = z ↔ diagonalProjection Δ β z = z := by
  constructor
  · intro h
    have he := quotientLindblad_error_norm Δ β a t ha.le ht.le z
    rw [h] at he
    have hex : Real.exp (-2*a*t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    have hn : ‖z - diagonalProjection Δ β z‖ = 0 := by
      nlinarith [norm_nonneg (z - diagonalProjection Δ β z)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
  · intro h
    have he := quotientLindblad_error Δ β a t ha.le ht.le z
    rw [h, sub_self, smul_zero, sub_eq_zero] at he
    exact he

/-- Faithfulness makes the quotient fixed-algebra statement a literal matrix statement. -/
theorem diagonalProjection_observable_fixed_iff (Δ β : ℝ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    diagonalProjection Δ β (observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef X) =
      observable (gibbs_posDef (twoLevel_hermitian Δ) β).posSemidef X ↔
      diagonalExpectation X = X := by
  rw [diagonalProjection_observable]
  exact (observable_injective (gibbs_posDef (twoLevel_hermitian Δ) β)).eq_iff

/-- A surviving off-diagonal direction witnesses that the fixed algebra is proper. -/
theorem diagonalProjection_coherence (Δ β : ℝ) :
    diagonalProjection Δ β (coherence Δ β) = 0 := by
  unfold diagonalProjection
  rw [quotientDephasing_coherence]
  norm_num

/-- At the endpoint strength one the error does not decrease. -/
theorem quotientDephasing_one_error_norm (Δ β : ℝ) (k : ℕ) (z : GibbsSpace Δ β) :
    ‖(quotientDephasing Δ β 1 (by norm_num) (by norm_num) ^ k) z - diagonalProjection Δ β z‖ =
      ‖z - diagonalProjection Δ β z‖ := by
  rw [quotientDephasing_pow_error_norm]
  norm_num

/-- The endpoint obstruction has a nonzero faithful Gibbs witness at every iterate. -/
theorem quotientDephasing_one_coherence_error_pos (Δ β : ℝ) (k : ℕ) :
    0 < ‖(quotientDephasing Δ β 1 (by norm_num) (by norm_num) ^ k) (coherence Δ β) -
      diagonalProjection Δ β (coherence Δ β)‖ := by
  rw [quotientDephasing_one_error_norm, diagonalProjection_coherence, sub_zero]
  exact norm_pos_iff.mpr (coherence_nonzero Δ β)

/-- Zero generator rate leaves every vector fixed, not just the diagonal algebra. -/
theorem quotientLindblad_zero_rate (Δ β t : ℝ) (ht : 0 ≤ t) (z : GibbsSpace Δ β) :
    quotientLindblad Δ β 0 t (by norm_num) ht z = z := by
  have h := quotientLindblad_error Δ β 0 t (by norm_num) ht z
  simpa using h

end SKEFTHawking.FinitePositiveKernel.GibbsDephasing
