import SKEFTHawking.ClassicalFlowStability

/-! Continuous time-dependent gradient envelopes for actual equal-force classical
flows. The integrating factor retains initial error and vanishing cutoff error. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace
namespace SKEFTHawking.ClassicalFlowTimeStability
open SKEFTHawking.ClassicalFlowStability NavierStokesR3
open ProblemStatement Comparison ComparisonCutoffs WholeSpaceComparisonClosure
open NavierStokes.ProblemStatement (spatialDerivative spatialDivergence)
open NavierStokes.PeriodicUniqueness (spatial_smooth time_differentiable_at_interior)

/-- A continuous nonnegative coefficient gives an integral, rather than supremum, exponent. -/
theorem le_initial_integral_exp_add {T ε a : ℝ} {k E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hε : 0 ≤ ε) (hk : ContinuousOn k (Icc 0 T))
    (hk0 : ∀ t ∈ Icc 0 T, 0 ≤ k t)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ a)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ k t * E t + ε) :
    ∀ t ∈ Icc 0 T,
      E t ≤ (a + ε*t) * Real.exp (∫ s in 0..t, k s) := by
  let A : ℝ → ℝ := fun t => ∫ s in 0..t, k s
  have hki : IntegrableOn k (uIcc 0 T) volume := by
    simpa [uIcc_of_le hT] using hk.integrableOn_Icc
  have hAc : ContinuousOn A (Icc 0 T) := by
    simpa [A, uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval hki
  have hAd (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt A (k t) t := by
    have hkc := hk.continuousAt (Icc_mem_nhds ht.1 ht.2)
    apply intervalIntegral.integral_hasDerivAt_right
      ((hk.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
      _ hkc
    exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hk.mono Ioo_subset_Icc_self) t ht
  have hA0 (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ A t :=
    intervalIntegral.integral_nonneg ht.1 (fun s hs => hk0 s ⟨hs.1, hs.2.trans ht.2⟩)
  let F : ℝ → ℝ := fun t => E t * Real.exp (-A t)
  let F' : ℝ → ℝ := fun t => E' t * Real.exp (-A t) + E t * (Real.exp (-A t) * (-k t))
  have hFc : ContinuousOn F (Icc 0 T) := hcont.mul (Real.continuous_exp.comp_continuousOn hAc.neg)
  have hFi : F 0 ≤ a := by simpa [F, A] using hinitial
  have hFd (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt F (F' t) t :=
    (hderiv t ht).mul (hAd t ht).neg.exp
  have hFb (t : ℝ) (ht : t ∈ Ioo 0 T) : F' t ≤ 0 * F t + ε := by
    have he : Real.exp (-A t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hA0 t ⟨ht.1.le, ht.2.le⟩))
    have hb : E' t - k t * E t ≤ ε := by linarith [hbound t ht]
    calc
      F' t = (E' t - k t * E t) * Real.exp (-A t) := by dsimp [F']; ring
      _ ≤ ε * Real.exp (-A t) := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ ≤ 0 * F t + ε := by simpa using mul_le_of_le_one_right hε he
  intro t ht
  have hh := le_initial_exp_add hT (by norm_num : (0:ℝ) ≤ 0) hε hFc hFi hFd hFb t ht
  simp only [zero_mul, Real.exp_zero, mul_one] at hh
  calc
    E t = F t * Real.exp (A t) := by
      dsimp [F]
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ ≤ (a + ε*t) * Real.exp (A t) := mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

/-- Radius exhaustion preserves the integral-in-time growth factor. -/
theorem energy_le_of_time_weighted_rate {w : VelocityField} {T C R₀ : ℝ} {k : ℝ → ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hk : ContinuousOn k (Icc 0 T))
    (hk0 : ∀ t ∈ Icc 0 T, 0 ≤ k t)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab 0 T))
    (hi : ∀ t ∈ Icc (0 : ℝ) T, SquareIntegrableAtTime w t)
    (hrate : ∀ R : ℝ, max 1 R₀ ≤ R → ∀ t ∈ Ioo (0 : ℝ) T,
      weightedEnergyRate (weight R) w t ≤ k t * weightedEnergy (weight R) w t + C / R) :
    ∀ t ∈ Icc (0 : ℝ) T,
      l2Sq (fun x => w (t, x)) ≤ l2Sq (fun x => w (0, x)) * Real.exp (∫ s in 0..t, k s) := by
  intro t ht
  have hs := spatial_smooth hw ht
  have hs0 := spatial_smooth hw (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
  have hlim := WholeSpaceEnergyLimit.integral_weight_tendsto hs.continuous (hi t ht)
  have hbound (R : ℝ) (hR : max 1 R₀ ≤ R) :
      weightedEnergy (weight R) w t ≤ l2Sq (fun x => w (0, x)) * Real.exp (∫ s in 0..t, k s) +
        (C * t * Real.exp (∫ s in 0..t, k s)) / R := by
    have hRpos : 0 < R := zero_lt_one.trans_le ((le_max_left _ _).trans hR)
    have hcont := LocalizedDifferenceEnergy.weightedEnergy_continuousOn
      (weight_smooth R).continuous (weight_hasCompactSupport hRpos) hw
    have hinit : weightedEnergy (weight R) w 0 ≤ l2Sq (fun x => w (0, x)) := by
      apply integral_mono
        (LocalizedDifferenceEnergy.integrable_weighted_energy (weight_smooth R).continuous
          (weight_hasCompactSupport hRpos) hs0.continuous) (hi 0 ⟨le_rfl, hT⟩)
      intro x
      exact mul_le_of_le_one_left (sq_nonneg _) (weight_le_one R x)
    have hh := le_initial_integral_exp_add hT (div_nonneg hC hRpos.le) hk hk0 hcont hinit
      (fun s hs => LocalizedDifferenceEnergy.weightedEnergy_hasDerivAt
        (weight_smooth R) (weight_hasCompactSupport hRpos) hw hs) (hrate R hR) t ht
    convert hh using 1
    ring
  have hz : Tendsto (fun R : ℝ => (C * t * Real.exp (∫ s in 0..t, k s)) / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => C * t * Real.exp (∫ s in 0..t, k s))
        atTop (𝓝 (C * t * Real.exp (∫ s in 0..t, k s)))).mul tendsto_inv_atTop_zero
  have hupper := (tendsto_const_nhds (x := l2Sq (fun x => w (0, x)) * Real.exp (∫ s in 0..t, k s))).add hz
  simpa only [add_zero] using le_of_tendsto_of_tendsto hlim hupper
    (eventually_atTop.2 ⟨max 1 R₀, hbound⟩)

/-- Actual classical PDE stability under a continuous nonnegative time envelope. -/
theorem classical_energy_stability_of_time_gradient {T : ℝ} (hT : 0 < T)
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
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 T))
    (hg0 : ∀ t ∈ Icc 0 T, 0 ≤ g t)
    (hG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖spatialDerivative u t x‖ ≤ g t) :
    ∀ t ∈ Icc (0 : ℝ) T,
      l2Sq (fun x => (u - v) (t, x)) ≤
        l2Sq (fun x => (u - v) (0, x)) * Real.exp (2 * ∫ s in 0..t, g s) := by
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
  obtain ⟨D, hD, hrate⟩ := exists_weighted_rate_of_time_gradient hM0 hCP hu hv hp hq
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2) hG hdu hdv hNS hvanish
    (fun R hR t ht => by
      simpa only [pressureEnvelope, neg_div] using hpressure R hR t ht)
  have henergy := energy_le_of_time_weighted_rate hT.le hD (continuousOn_const.mul hg)
    (fun t ht => mul_nonneg (by norm_num) (hg0 t ht)) (hu.sub hv)
    (fun t ht => (memLp_two_iff_integrable_sq_norm (hM t ht).1.aestronglyMeasurable).mp
      (hM t ht).1) hrate
  intro t ht
  simpa only [Pi.mul_apply, Pi.sub_apply, intervalIntegral.integral_const_mul] using henergy t ht

/-- Constant envelopes recover precisely the previous exponential coefficient. -/
theorem constant_integral_exponent (G t : ℝ) :
    2 * (∫ _ in 0..t, G) = (2*G)*t := by
  simp
  ring

/-- The affine envelope has its actual integrated exponent. -/
theorem affine_integral_exponent (A B t : ℝ) :
    2 * (∫ s in 0..t, A+B*s) = 2*A*t+B*t^2 := by
  rw [intervalIntegral.integral_add (f := fun _ => A) (g := fun s => B*s)
    (continuous_const.intervalIntegrable 0 t)
    ((continuous_const.mul continuous_id).intervalIntegrable 0 t),
    intervalIntegral.integral_const_mul]
  simp
  ring

/-- For increasing envelopes the integrated coefficient is strictly below the slab maximum. -/
theorem affine_exponent_lt_slab_max (A B T t : ℝ) (hB : 0 < B)
    (ht : t ∈ Ioo 0 T) :
    Real.exp (2*A*t+B*t^2) < Real.exp ((2*(A+B*T))*t) := by
  apply Real.exp_lt_exp.mpr
  have hp : 0 < B*t*(2*T-t) := mul_pos (mul_pos hB ht.1) (by linarith [ht.1, ht.2])
  nlinarith

/-- A genuinely varying time envelope is consumed by the actual PDE theorem. -/
theorem classical_energy_stability_affine {T : ℝ} (hT : 0 < T)
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
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖spatialDerivative u t x‖ ≤ A+B*t) :
    ∀ t ∈ Icc (0 : ℝ) T,
      l2Sq (fun x => (u - v) (t, x)) ≤
        l2Sq (fun x => (u - v) (0, x)) * Real.exp (2*A*t+B*t^2) := by
  have hh := classical_energy_stability_of_time_gradient hT hu hv hp hq hK hsupp hev hdu hdv hNS
    (g := fun t => A+B*t) (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    (fun t ht => add_nonneg hA (mul_nonneg hB ht.1)) hG
  intro t ht
  simpa only [affine_integral_exponent] using hh t ht

/-- The prior constant-gradient PDE statement is an instance of the time-envelope theorem. -/
theorem classical_energy_stability_constant {T : ℝ} (hT : 0 < T)
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
        l2Sq (fun x => (u - v) (0, x)) * Real.exp ((2*G)*t) := by
  have hh := classical_energy_stability_of_time_gradient hT hu hv hp hq hK hsupp hev hdu hdv hNS
    (g := fun _ => G) continuousOn_const (fun _ _ => hG0) hG
  intro t ht
  simpa only [constant_integral_exponent] using hh t ht

/-- With nonzero initial error, the actual affine-envelope bound improves the slab-maximum bound. -/
theorem classical_affine_energy_lt_slab_max {T : ℝ} (hT : 0 < T)
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
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (hG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖spatialDerivative u t x‖ ≤ A+B*t)
    (hinit : 0 < l2Sq (fun x => (u-v) (0,x))) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      l2Sq (fun x => (u - v) (t, x)) <
        l2Sq (fun x => (u - v) (0, x)) * Real.exp ((2*(A+B*T))*t) := by
  have hh := classical_energy_stability_affine hT hu hv hp hq hK hsupp hev hdu hdv hNS hA hB.le hG
  intro t ht
  exact lt_of_le_of_lt (hh t (Ioo_subset_Icc_self ht))
    (mul_lt_mul_of_pos_left (affine_exponent_lt_slab_max A B T t hB ht) hinit)

end SKEFTHawking.ClassicalFlowTimeStability
