import NavierStokes.R3.WholeSpaceUniqueness

/-! Quantitative stability for smooth equal-force flows on R³ at unit viscosity.
The localized PDE calculation follows the Apache-2.0 NavierStokes backport's
WholeSpaceComparisonClosure, with nonzero initial energy retained through
Gronwall and cutoff exhaustion. No weak-solution or existence claim is made. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace
namespace SKEFTHawking.ClassicalFlowStability
open NavierStokesR3
open ProblemStatement Comparison ComparisonCutoffs WholeSpaceComparisonClosure
open NavierStokes.ProblemStatement (spatialDerivative spatialDivergence)
open NavierStokes.PeriodicUniqueness (spatial_smooth time_differentiable_at_interior)

/-- The actual pressure-flux estimate gives a uniform localized energy rate,
without any initial-data equality assumption. -/
theorem exists_weighted_rate_of_time_gradient {T M CP R₀ : ℝ} {g : ℝ → ℝ}
    {u v : VelocityField} {p q : PressureField}
    (hM0 : 0 ≤ M) (hCP0 : 0 ≤ CP)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hwu : ∀ t ∈ Icc (0 : ℝ) T, MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M)
    (hG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖spatialDerivative u t x‖ ≤ g t)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    (hvanish : ∀ R ≥ R₀, ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      fderiv ℝ (weight R) x (u (t, x)) = 0)
    (hpressure : ∀ R ≥ 1, ∀ t ∈ Ioo (0 : ℝ) T,
      |∫ x : Space, (p - q) (t, x) * fderiv ℝ (weight R) x ((u - v) (t, x))| ≤
        CP * pressureEnvelope R (dissipationRoot (cutoff R) (u - v) t)
          (cutoffL6 (cutoff R) (u - v) t)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, max 1 R₀ ≤ R → ∀ t ∈ Ioo (0 : ℝ) T,
      weightedEnergyRate (weight R) (u - v) t ≤
        (2 * g t) * weightedEnergy (weight R) (u - v) t + D / R := by
  let C0 := LocalizedFluxEstimates.weightLaplacianConstant * M ^ 2 / 2
  let C1 := 4 * derivativeConstant 1 * M ^ (3 / 2 : ℝ)
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact div_nonneg (mul_nonneg
      LocalizedFluxEstimates.weightLaplacianConstant_pos.le (sq_nonneg M)) (by norm_num)
  have hC1 : 0 ≤ C1 := by
    dsimp [C1]
    exact mul_nonneg (mul_nonneg (by norm_num) (derivativeConstant_pos 1).le)
      (Real.rpow_nonneg hM0 _)
  obtain ⟨D, hD, hrate⟩ := ComparisonRateBound.exists_uniform_rate_bound hC0 hC1 hCP0
    WeightedSobolev.weightedSobolevConstant_pos.le
    (mul_nonneg (derivativeConstant_pos 1).le hM0)
  refine ⟨D, hD, ?_⟩
  intro R hR t ht
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRpos : 0 < R := zero_lt_one.trans_le hR1
  have htcc : t ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self ht
  have hut := spatial_smooth hu htcc
  have hvt := spatial_smooth hv htcc
  have hwt := hut.sub hvt
  have hw2 := hwu t htcc
  let A := dissipationRoot (cutoff R) (u - v) t
  let B := cutoffL6 (cutoff R) (u - v) t
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hm : 0 ≤ comparisonLpNorm 2 (fun x => (u - v) (t, x)) := ENNReal.toReal_nonneg
  have hAsq : A ^ 2 = weightedDissipation (weight R) (u - v) t := by
    apply Real.sq_sqrt
    exact LocalizedDifferenceEnergy.weightedDissipation_nonneg (weight_nonneg R) _ _
  have hSob0 := WeightedSobolev.cutoffL6_le
    ((cutoff_smooth R).of_le (by simp)) (cutoff_hasCompactSupport hRpos)
    (hwt.of_le (by simp)) hw2 (cutoff_nonneg R) (cutoff_le_one R)
    (div_nonneg (derivativeConstant_pos 1).le hRpos.le) (cutoff_fderiv_le hRpos)
  have hSob : B ≤ WeightedSobolev.weightedSobolevConstant *
      (A + (derivativeConstant 1 * M) / R) := by
    apply hSob0.trans
    apply mul_le_mul_of_nonneg_left _ WeightedSobolev.weightedSobolevConstant_pos.le
    apply add_le_add_right
    calc
      derivativeConstant 1 / R * comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤
          derivativeConstant 1 / R * M := mul_le_mul_of_nonneg_left (hM t htcc)
            (div_nonneg (derivativeConstant_pos 1).le hRpos.le)
      _ = _ := by ring
  have hc := LocalizedFluxEstimates.neg_coupling_le_weightedEnergy
    (u := u) (w := u - v) (t := t)
    (weight_smooth R).continuous (weight_hasCompactSupport hRpos) (weight_nonneg R)
    (hut.of_le (by simp)) hwt.continuous (hG t htcc)
  have hl := (LocalizedFluxEstimates.weight_laplacian_flux_bound hRpos hw2).2
  have hl' : |∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
      ∑ i : Fin 3, partialD i (partialD i (weight R)) x| ≤
      LocalizedFluxEstimates.weightLaplacianConstant * M ^ 2 / R ^ 2 := by
    apply hl.trans
    calc
      _ ≤ (LocalizedFluxEstimates.weightLaplacianConstant / R ^ 2) * M ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm (hM t htcc) 2)
          (div_nonneg LocalizedFluxEstimates.weightLaplacianConstant_pos.le (sq_nonneg _))
      _ = _ := by ring
  have htflux := (LocalizedFluxEstimates.transport_flux_bound
    ((cutoff_smooth R).of_le (by simp)) (cutoff_hasCompactSupport hRpos)
    hut.continuous hvt.continuous hw2 (cutoff_nonneg R) (cutoff_le_one R)
    (div_nonneg (derivativeConstant_pos 1).le hRpos.le) (cutoff_fderiv_le hRpos)
    (hvanish R ((le_max_right _ _).trans hR) t htcc)).2
  have htflux' : |∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
      fderiv ℝ (weight R) x (v (t, x))| ≤
      (8 * derivativeConstant 1 * M ^ (3 / 2 : ℝ)) / R * B ^ (3 / 2 : ℝ) := by
    apply htflux.trans
    calc
      _ ≤ (8 * (derivativeConstant 1 / R)) * M ^ (3 / 2 : ℝ) * B ^ (3 / 2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hB _)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hm (hM t htcc) (by norm_num))
          (mul_nonneg (by norm_num) (div_nonneg (derivativeConstant_pos 1).le hRpos.le))
      _ = _ := by ring
  have hpflux := hpressure R hR1 t ht
  have hbalance := LocalizedDifferenceEnergy.difference_energy_balance
    (weight_smooth R) (weight_hasCompactSupport hRpos) hut hvt
    (spatial_smooth hp htcc) (spatial_smooth hq htcc)
    (time_differentiable_at_interior hu ht) (time_differentiable_at_interior hv ht)
    (hdu t ht) (hdv t ht) (hNS t ht)
  apply hrate R hR1 A hA B hB hSob
    (weightedEnergy (weight R) (u - v) t) (weightedEnergyRate (weight R) (u - v) t) (g t)
  rw [hAsq, hbalance]
  have hlle := (le_abs_self (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
    ∑ i : Fin 3, partialD i (partialD i (weight R)) x)).trans hl'
  have htle := (le_abs_self (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
    fderiv ℝ (weight R) x (v (t, x)))).trans htflux'
  have hple : (∫ x : Space, (p - q) (t, x) *
      fderiv ℝ (weight R) x ((u - v) (t, x))) ≤ CP * pressureEnvelope R A B :=
    (le_abs_self _).trans hpflux
  have hsum := add_le_add (add_le_add
    (add_le_add hc (mul_le_mul_of_nonneg_left hlle (by norm_num : (0 : ℝ) ≤ 1 / 2)))
    (mul_le_mul_of_nonneg_left htle (by norm_num : (0 : ℝ) ≤ 1 / 2))) hple
  convert! hsum using 1
  dsimp only [C0, C1, pressureEnvelope]
  ring

/-- The constant-gradient API is recovered exactly from the time-gradient estimate. -/
theorem exists_weighted_rate_of_pressure_flux {T M G CP R₀ : ℝ}
    {u v : VelocityField} {p q : PressureField}
    (hM0 : 0 ≤ M) (hCP0 : 0 ≤ CP)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hwu : ∀ t ∈ Icc (0 : ℝ) T, MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M)
    (hG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖spatialDerivative u t x‖ ≤ G)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    (hvanish : ∀ R ≥ R₀, ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      fderiv ℝ (weight R) x (u (t, x)) = 0)
    (hpressure : ∀ R ≥ 1, ∀ t ∈ Ioo (0 : ℝ) T,
      |∫ x : Space, (p - q) (t, x) * fderiv ℝ (weight R) x ((u - v) (t, x))| ≤
        CP * pressureEnvelope R (dissipationRoot (cutoff R) (u - v) t)
          (cutoffL6 (cutoff R) (u - v) t)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, max 1 R₀ ≤ R → ∀ t ∈ Ioo (0 : ℝ) T,
      weightedEnergyRate (weight R) (u - v) t ≤
        (2 * G) * weightedEnergy (weight R) (u - v) t + D / R := by
  exact exists_weighted_rate_of_time_gradient (g := fun _ => G)
    hM0 hCP0 hu hv hp hq hwu hM hG hdu hdv hNS hvanish hpressure

/-- Gronwall with a genuine initial error and interior derivatives only. -/
theorem le_initial_exp_add {T K ε a : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ a)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, E t ≤ a * Real.exp (K * t) + ε * t * Real.exp (K * t) := by
  have hshiftCont : ContinuousOn (fun t => E t - a * Real.exp (K * t)) (Icc 0 T) :=
    hcont.sub ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).continuousOn)
  have hshiftInitial : E 0 - a * Real.exp (K * 0) ≤ 0 := by
    simpa using sub_nonpos.mpr hinitial
  have hshiftDeriv (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (fun s => E s - a * Real.exp (K * s))
        (E' t - a * (Real.exp (K * t) * K)) t := by
    convert! (hderiv t ht).sub ((((hasDerivAt_id t).const_mul K).exp).const_mul a) using 1
    simp
  have hshiftBound (t : ℝ) (ht : t ∈ Ioo 0 T) :
      E' t - a * (Real.exp (K * t) * K) ≤ K * (E t - a * Real.exp (K * t)) + ε := by
    nlinarith [hbound t ht]
  intro t ht
  have hh := ComparisonGronwall.le_exp_mul_of_deriv_le hT hK hε hshiftCont
    hshiftInitial hshiftDeriv hshiftBound t ht
  linarith

/-- Cutoff exhaustion retains the actual nonzero initial squared L² difference. -/
theorem energy_le_of_weighted_rate {w : VelocityField} {T K C R₀ : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab 0 T))
    (hi : ∀ t ∈ Icc (0 : ℝ) T, SquareIntegrableAtTime w t)
    (hrate : ∀ R : ℝ, max 1 R₀ ≤ R → ∀ t ∈ Ioo (0 : ℝ) T,
      weightedEnergyRate (weight R) w t ≤ K * weightedEnergy (weight R) w t + C / R) :
    ∀ t ∈ Icc (0 : ℝ) T,
      l2Sq (fun x => w (t, x)) ≤ l2Sq (fun x => w (0, x)) * Real.exp (K * t) := by
  intro t ht
  have hs := spatial_smooth hw ht
  have hs0 := spatial_smooth hw (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
  have hlim := WholeSpaceEnergyLimit.integral_weight_tendsto hs.continuous (hi t ht)
  have hbound (R : ℝ) (hR : max 1 R₀ ≤ R) :
      weightedEnergy (weight R) w t ≤ l2Sq (fun x => w (0, x)) * Real.exp (K * t) +
        (C * t * Real.exp (K * t)) / R := by
    have hRpos : 0 < R := zero_lt_one.trans_le ((le_max_left _ _).trans hR)
    have hcont := LocalizedDifferenceEnergy.weightedEnergy_continuousOn
      (weight_smooth R).continuous (weight_hasCompactSupport hRpos) hw
    have hinit : weightedEnergy (weight R) w 0 ≤ l2Sq (fun x => w (0, x)) := by
      apply integral_mono
        (LocalizedDifferenceEnergy.integrable_weighted_energy (weight_smooth R).continuous
          (weight_hasCompactSupport hRpos) hs0.continuous) (hi 0 ⟨le_rfl, hT⟩)
      intro x
      exact mul_le_of_le_one_left (sq_nonneg _) (weight_le_one R x)
    have hh := le_initial_exp_add hT hK (div_nonneg hC hRpos.le) hcont hinit
      (fun s hs => LocalizedDifferenceEnergy.weightedEnergy_hasDerivAt
        (weight_smooth R) (weight_hasCompactSupport hRpos) hw hs) (hrate R hR) t ht
    convert hh using 1
    ring
  have hz : Tendsto (fun R : ℝ => (C * t * Real.exp (K * t)) / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => C * t * Real.exp (K * t))
        atTop (𝓝 (C * t * Real.exp (K * t)))).mul tendsto_inv_atTop_zero
  have hupper := (tendsto_const_nhds (x := l2Sq (fun x => w (0, x)) * Real.exp (K * t))).add hz
  simpa only [add_zero] using le_of_tendsto_of_tendsto hlim hupper
    (eventually_atTop.2 ⟨max 1 R₀, hbound⟩)

/-- Whole-space quantitative stability of actual equal-force classical flows.
The pressure flux is recovered from the equations. Only the reference has compact
support; the competitor needs uniformly finite energy, and initial errors may be nonzero. -/
theorem classical_energy_stability_of_gradient_bound {T : ℝ} (hT : 0 < T)
    {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K)
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖spatialDerivative u t x‖ ≤ G) :
    ∀ t ∈ Icc (0 : ℝ) T,
      l2Sq (fun x => (u - v) (t, x)) ≤
        l2Sq (fun x => (u - v) (0, x)) * Real.exp ((2 * G) * t) := by
  have heu := CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab hu hK hsupp
  let H : PressureRecovery.Hypotheses T u v p q :=
    ⟨hT, hu, hv, hp, hq, hdu, hdv, (fun t ht x => by simpa using hNS t ht x), heu, hev⟩
  have hum : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x => u (t, x)) volume :=
    fun t ht => (spatial_smooth hu ht).continuous.aestronglyMeasurable
  have hvm : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x => v (t, x)) volume :=
    fun t ht => (spatial_smooth hv ht).continuous.aestronglyMeasurable
  have hew := uniformFiniteEnergy_sub hum hvm heu hev
  obtain ⟨M, hM0, hM⟩ := uniformFiniteEnergy_lpNorm_two_bound
    (fun t ht => (hum t ht).sub (hvm t ht)) hew
  obtain ⟨U, hU0, hU⟩ := CompactComparisonBounds.exists_lpNorm_three_bound
    hu.continuousOn hK hsupp
  obtain ⟨G₀, hG₀, hTensor⟩ := uniformFiniteEnergy_tensorDiff_lpNorm_one_bound hum hvm heu hev
  obtain ⟨CP, hCP, hpressure⟩ := PressureFlux.exists_uniform_actual_pressure_flux_bound
    H M U G₀ hM0 hU0 hG₀ hM hU hTensor
  obtain ⟨R₀, _hR₀, hvanish⟩ := CompactComparisonBounds.exists_radius_weight_derivative_zero hK hsupp
  obtain ⟨D, hD, hrate⟩ := exists_weighted_rate_of_pressure_flux hM0 hCP hu hv hp hq
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2) hG hdu hdv hNS hvanish
    (fun R hR t ht => by
      simpa only [pressureEnvelope, neg_div] using hpressure R hR t ht)
  exact energy_le_of_weighted_rate hT.le (mul_nonneg (by norm_num) hG0) hD (hu.sub hv)
    (fun t ht => (memLp_two_iff_integrable_sq_norm (hM t ht).1.aestronglyMeasurable).mp
      (hM t ht).1) hrate

/-- Compact smooth reference flow supplies a finite exponential growth coefficient.
No pressure-flux or stability estimate is assumed by this PDE entry point. -/
theorem classical_energy_stability_on_Icc {T : ℝ} (hT : 0 < T)
    {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K)
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T,
      l2Sq (fun x => (u - v) (t, x)) ≤
        l2Sq (fun x => (u - v) (0, x)) * Real.exp (C * t) := by
  obtain ⟨G, hG0, hG⟩ := CompactComparisonBounds.exists_gradient_bound hT hu hK hsupp
  exact ⟨2 * G, mul_nonneg (by norm_num) hG0,
    classical_energy_stability_of_gradient_bound hT hu hv hp hq hK hsupp hev hdu hdv hNS hG0 hG⟩

/-- The quantitative estimate recovers classical uniqueness at zero initial error. -/
theorem classical_eq_of_zero_initial_error {T : ℝ} (hT : 0 < T)
    {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K)
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    (hzero : ∀ x, u (0, x) = v (0, x)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  obtain ⟨C, _, hbound⟩ := classical_energy_stability_on_Icc hT hu hv hp hq hK hsupp hev hdu hdv hNS
  have heu := CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab hu hK hsupp
  obtain ⟨_, _, hdiff⟩ := uniformFiniteEnergy_sub_of_continuousOn
    hu.continuousOn hv.continuousOn heu hev
  have hinit : l2Sq (fun x => (u - v) (0, x)) = 0 := by
    simp [l2Sq, hzero]
  intro t ht x
  have hle := hbound t ht
  rw [hinit, zero_mul] at hle
  have hz := le_antisymm hle (l2Sq_nonneg (fun x => (u - v) (t, x)))
  have heq := WholeSpaceEnergyLimit.eq_zero_of_l2Sq_eq_zero
    (spatial_smooth (hu.sub hv) ht).continuous (hdiff t ht).1 hz
  exact sub_eq_zero.mp (heq x)

end SKEFTHawking.ClassicalFlowStability
