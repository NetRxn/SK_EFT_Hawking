import SKEFTHawking.ClassicalFlowForcedLocalized
import SKEFTHawking.ClassicalFlowTimeStability

/-! Forced whole-space stability for uniformly compact velocity differences.
Pressure and the individual velocities need not have compact support. Forcing
square integrability is explicit; no general unequal-force pressure recovery is used. -/
noncomputable section
open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace SKEFTHawking.ClassicalFlowForcedCompact
open NavierStokesR3
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open CompactEnergy
open ClassicalFlowForcedLocalized (residualDifference infty_add_one_le)

/-- Integration by parts with compact transported scalar, not compact advector. -/
theorem integral_fderiv_compact_scalar {f : Space → ℝ} {v : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v) (hcf : HasCompactSupport f) :
    (∫ x, fderiv ℝ f x (v x)) = -(∫ x, f x * ∑ i : Fin 3, spatialPartial i v x i) := by
  have hl : (fun x => fderiv ℝ f x (v x)) =
      (fun x => ∑ i : Fin 3, v x i * spatialPartial i f x) := by
    funext x; exact fderiv_apply_eq_sum f x (v x)
  have hr : (fun x => f x * ∑ i : Fin 3, spatialPartial i v x i) =
      (fun x => ∑ i : Fin 3, f x * spatialPartial i v x i) := by
    funext x; exact Finset.mul_sum _ _ _
  have hiL (i : Fin 3) : Integrable (fun x => v x i * spatialPartial i f x) :=
    ((component_contDiff hv i).continuous.mul (spatial_partial_contDiff hf i).continuous).integrable_of_hasCompactSupport
      (compact_partial hcf i).mul_left
  have hiR (i : Fin 3) : Integrable (fun x => f x * spatialPartial i v x i) :=
    (hf.continuous.mul (component_contDiff (spatial_partial_contDiff hv i) i).continuous).integrable_of_hasCompactSupport
      hcf.mul_right
  rw [hl,hr,integral_finsetSum _ (fun i _ => hiL i),integral_finsetSum _ (fun i _ => hiR i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := integral_mul_partial hf (component_contDiff hv i) hcf i
  simpa only [spatialPartial,fderiv_component hv,neg_neg] using (congrArg Neg.neg h).symm

theorem integral_transport_compact_difference {w v : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v) (hcw : HasCompactSupport w)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i)=0) :
    (∫ x, ⟪w x,fderiv ℝ w x (v x)⟫_ℝ)=0 := by
  have h := integral_fderiv_compact_scalar (hw.norm_sq ℝ) hv (compact_norm_sq hcw)
  have he : (fun x => fderiv ℝ (fun y => ‖w y‖^2) x (v x)) =
      (fun x => 2*⟪w x,fderiv ℝ w x (v x)⟫_ℝ) := by
    funext x; exact fderiv_normsq hw x (v x)
  rw [he,integral_const_mul] at h
  simp only [hdiv,mul_zero,integral_zero,neg_zero] at h
  linarith

/-- Exact residual-difference balance with all products integrable before splitting. -/
theorem energy_balance {u v : VelocityField} {p q : PressureField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t,x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t,x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t,x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t,x)))
    (htu : ∀ x, DifferentiableAt ℝ (fun s => u (s,x)) t)
    (htv : ∀ x, DifferentiableAt ℝ (fun s => v (s,x)) t)
    (hcw : HasCompactSupport (fun x => (u-v) (t,x)))
    (hdu : ∀ x, spatialDivergence u t x=0) (hdv : ∀ x, spatialDivergence v t x=0)
    (hF : Continuous (residualDifference u v p q t)) :
    CompactEnergy.energyRate (u-v) t + 2*CompactEnergy.dissipation (u-v) t =
      -2*(∫ x, ⟪(u-v) (t,x),spatialDerivative u t x ((u-v) (t,x))⟫_ℝ) +
      2*(∫ x, ⟪(u-v) (t,x),residualDifference u v p q t x⟫_ℝ) := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u-v) (t,x)) := hu.sub hv
  have hπ : ContDiff ℝ ∞ (fun x : Space => (p-q) (t,x)) := hp.sub hq
  have hiL := integrable_inner_left hw.continuous (spatialLaplacian_contDiff hw).continuous hcw
  have hiC := integrable_inner_left hw.continuous
    ((hu.fderiv_right infty_add_one_le).clm_apply hw).continuous hcw
  have hiT := integrable_inner_left hw.continuous
    ((hw.fderiv_right infty_add_one_le).clm_apply hv).continuous hcw
  have hiP := integrable_inner_left hw.continuous (pressureGradient_contDiff hπ).continuous hcw
  have hiF := integrable_inner_left hw.continuous hF hcw
  have he : (fun x => ⟪(u-v) (t,x),temporalDerivative (u-v) t x⟫_ℝ) =
      (fun x => ⟪(u-v) (t,x),spatialLaplacian (u-v) t x⟫_ℝ -
        ⟪(u-v) (t,x),spatialDerivative u t x ((u-v) (t,x))⟫_ℝ -
        ⟪(u-v) (t,x),spatialDerivative (u-v) t x (v (t,x))⟫_ℝ -
        ⟪(u-v) (t,x),pressureGradient (p-q) t x⟫_ℝ +
        ⟪(u-v) (t,x),residualDifference u v p q t x⟫_ℝ) := by
    funext x
    rw [ClassicalFlowForcedLocalized.forced_difference_equation hu hv hp hq (htu x) (htv x)]
    simp only [inner_add_right,inner_sub_right]
  have hdivw : ∀ x, spatialDivergence (u-v) t x=0 := by
    intro x; rw [spatialDivergence_sub hu hv,hdu,hdv,sub_self]
  have hT := integral_transport_compact_difference hw hv hcw hdv
  change (∫ x, ⟪(u-v) (t,x),spatialDerivative (u-v) t x (v (t,x))⟫_ℝ)=0 at hT
  unfold CompactEnergy.energyRate
  rw [integral_const_mul,he]
  erw [integral_add (((hiL.sub hiC).sub hiT).sub hiP) hiF,
    integral_sub ((hiL.sub hiC).sub hiT) hiP,integral_sub (hiL.sub hiC) hiT,
    integral_sub hiL hiC]
  rw [integral_laplacian_energy hw hcw,
    integral_pressure_energy_zero hw hπ hcw hdivw]
  erw [hT]
  dsimp only [CompactEnergy.dissipation,spatialDerivative]
  ring

theorem primitive_continuous {T : ℝ} {f : ℝ → ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) : ContinuousOn (fun t => ∫ s in 0..t, f s) (Icc 0 T) := by
  have hi : IntegrableOn f (uIcc 0 T) volume := by simpa [uIcc_of_le hT] using hf.integrableOn_Icc
  simpa [uIcc_of_le hT] using intervalIntegral.continuousOn_primitive_interval hi

theorem primitive_derivative {T : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 T))
    {t : ℝ} (ht : t ∈ Ioo 0 T) : HasDerivAt (fun r => ∫ s in 0..r, f s) (f t) t := by
  apply intervalIntegral.integral_hasDerivAt_right
    ((hf.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
    _ (hf.continuousAt (Icc_mem_nhds ht.1 ht.2))
  exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hf.mono Ioo_subset_Icc_self) t ht

/-- The forcing primitive retains the exact integrating-factor convolution. -/
theorem forced_integrating_factor {T : ℝ} {k H E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hk : ContinuousOn k (Icc 0 T)) (hH : ContinuousOn H (Icc 0 T))
    (hE : ContinuousOn E (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hb : ∀ t ∈ Ioo 0 T, E' t ≤ k t*E t+H t) :
    ∀ t ∈ Icc 0 T, E t ≤ Real.exp (∫ s in 0..t,k s) *
      (E 0 + ∫ s in 0..t,Real.exp (-(∫ r in 0..s,k r))*H s) := by
  let A := fun t => ∫ s in 0..t,k s
  have hAc : ContinuousOn A (Icc 0 T) := primitive_continuous hT hk
  let J := fun t => ∫ s in 0..t,Real.exp (-A s)*H s
  have hjc : ContinuousOn (fun s => Real.exp (-A s)*H s) (Icc 0 T) :=
    (Real.continuous_exp.comp_continuousOn hAc.neg).mul hH
  let V := fun t => E t*Real.exp (-A t)-J t
  let V' := fun t => E' t*Real.exp (-A t)+E t*(Real.exp (-A t)*(-k t)) - Real.exp (-A t)*H t
  have hVc : ContinuousOn V (Icc 0 T) :=
    (hE.mul (Real.continuous_exp.comp_continuousOn hAc.neg)).sub (primitive_continuous hT hjc)
  have hV0 : V 0 ≤ E 0 := by simp [V,A,J]
  have hVd : ∀ t ∈ Ioo 0 T, HasDerivAt V (V' t) t := by
    intro t ht
    exact ((hd t ht).mul (primitive_derivative hk ht).neg.exp).sub (primitive_derivative hjc ht)
  have hVb : ∀ t ∈ Ioo 0 T, V' t ≤ 0*V t+0 := by
    intro t ht
    have h := mul_le_mul_of_nonneg_right (hb t ht) (Real.exp_pos (-A t)).le
    dsimp [V']
    nlinarith
  intro t ht
  have h := ClassicalFlowStability.le_initial_exp_add hT (by norm_num : (0:ℝ) ≤ 0)
    (by norm_num : (0:ℝ) ≤ 0) hVc hV0 hVd hVb t ht
  simp only [zero_mul,add_zero,Real.exp_zero,mul_one] at h
  have he : E t ≤ (E 0+J t)*Real.exp (A t) := by
    have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (A t)).le
    have hh' : (E t*Real.exp (-A t))*Real.exp (A t)=E t := by
      rw [mul_assoc, ← Real.exp_add]; simp
    dsimp [V] at hh
    rw [sub_mul,hh'] at hh
    nlinarith
  simpa only [A,J,mul_comm] using he

theorem coupling_bound {u w : VelocityField} {t G : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t,x)))
    (hw : ContDiff ℝ ∞ (fun x : Space => w (t,x)))
    (hcw : HasCompactSupport (fun x => w (t,x)))
    (hG : ∀ x, ‖spatialDerivative u t x‖ ≤ G) :
    -(∫ x, ⟪w (t,x),spatialDerivative u t x (w (t,x))⟫_ℝ) ≤ G*l2Sq w t := by
  have hi := integrable_inner_left hw.continuous
    ((hu.fderiv_right infty_add_one_le).clm_apply hw).continuous hcw
  have he := integrable_norm_sq hw.continuous hcw
  rw [← integral_neg]
  change (∫ x, -⟪w (t,x),spatialDerivative u t x (w (t,x))⟫_ℝ) ≤ G*(∫ x,‖w (t,x)‖^2)
  rw [← integral_const_mul]
  apply integral_mono hi.neg (he.const_mul G)
  intro x
  exact nonlinear_energy_bound (spatialDerivative u t x) (w (t,x)) (hG x)

theorem work_bound {w : Space → Space} {F : Space → Space} {η : ℝ}
    (hw : Continuous w) (hcw : HasCompactSupport w) (hF : Continuous F)
    (hFi : Integrable (fun x => ‖F x‖^2)) (hη : 0 < η) :
    2*(∫ x,⟪w x,F x⟫_ℝ) ≤ η*(∫ x,‖w x‖^2)+η⁻¹*(∫ x,‖F x‖^2) := by
  have hi := integrable_inner_left hw hF hcw
  have he := integrable_norm_sq hw hcw
  have hp (x : Space) : 2*⟪w x,F x⟫_ℝ ≤ η*‖w x‖^2+η⁻¹*‖F x‖^2 := by
    have h := ClassicalFlowForcedLocalized.weighted_work_pointwise (w x) (F x)
      (by norm_num : (0:ℝ) ≤ 1) le_rfl hη
    simp only [one_mul] at h
    linarith [le_abs_self ⟪w x,F x⟫_ℝ]
  have h := integral_mono (hi.const_mul 2) ((he.const_mul η).add (hFi.const_mul η⁻¹)) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (he.const_mul η) (hFi.const_mul η⁻¹)] at h
  simpa only [integral_const_mul] using h

/-- The actual slab derivative has no assumed transformed-energy conclusion. -/
theorem slab_energy_balance {T t : ℝ} {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K) (hs : ∀ r ∈ Icc 0 T,tsupport (fun x => (u-v) (r,x)) ⊆ K)
    (ht : t ∈ Ioo 0 T) (hdu : ∀ x,spatialDivergence u t x=0) (hdv : ∀ x,spatialDivergence v t x=0) :
    HasDerivAt (l2Sq (u-v))
      (-2*CompactEnergy.dissipation (u-v) t -
        2*(∫ x,⟪(u-v) (t,x),spatialDerivative u t x ((u-v) (t,x))⟫_ℝ)+
        2*(∫ x,⟪(u-v) (t,x),residualDifference u v p q t x⟫_ℝ)) t := by
  have hb := energy_balance (spatial_smooth hu (Ioo_subset_Icc_self ht))
    (spatial_smooth hv (Ioo_subset_Icc_self ht)) (spatial_smooth hp (Ioo_subset_Icc_self ht))
    (spatial_smooth hq (Ioo_subset_Icc_self ht))
    (time_differentiable_at_interior hu ht) (time_differentiable_at_interior hv ht)
    (slice_compact hK (hs t (Ioo_subset_Icc_self ht))) hdu hdv
    (ClassicalFlowForcedLocalized.residualDifference_continuous_slice hu hv hp hq ht)
  have hd : HasDerivAt (l2Sq (u-v)) (CompactEnergy.energyRate (u-v) t) t :=
    energy_hasDerivAt hK (hu.sub hv) hs ht
  have he : CompactEnergy.energyRate (u-v) t =
      -2*CompactEnergy.dissipation (u-v) t -
        2*(∫ x,⟪(u-v) (t,x),spatialDerivative u t x ((u-v) (t,x))⟫_ℝ)+
        2*(∫ x,⟪(u-v) (t,x),residualDifference u v p q t x⟫_ℝ) := by linarith
  rw [he] at hd
  exact hd

theorem slab_rate_le {T t η G H : ℝ} {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K) (hs : ∀ r ∈ Icc 0 T,tsupport (fun x => (u-v) (r,x)) ⊆ K)
    (ht : t ∈ Ioo 0 T) (hdu : ∀ x,spatialDivergence u t x=0) (hdv : ∀ x,spatialDivergence v t x=0)
    (hG : ∀ x,‖spatialDerivative u t x‖ ≤ G)
    (hFi : Integrable (fun x => ‖residualDifference u v p q t x‖^2))
    (hH : (∫ x,‖residualDifference u v p q t x‖^2) ≤ H) (hη : 0 < η) :
    CompactEnergy.energyRate (u-v) t ≤ (2*G+η)*l2Sq (u-v) t+η⁻¹*H := by
  have htc := Ioo_subset_Icc_self ht
  have hw := spatial_smooth (hu.sub hv) htc
  have hc := slice_compact hK (hs t htc)
  have hF := ClassicalFlowForcedLocalized.residualDifference_continuous_slice hu hv hp hq ht
  have hb := energy_balance (spatial_smooth hu htc) (spatial_smooth hv htc)
    (spatial_smooth hp htc) (spatial_smooth hq htc)
    (time_differentiable_at_interior hu ht) (time_differentiable_at_interior hv ht) hc hdu hdv hF
  have hg := coupling_bound (spatial_smooth hu htc) hw hc hG
  have hf := work_bound hw.continuous hc hF hFi hη
  have hh := mul_le_mul_of_nonneg_left hH (inv_nonneg.mpr hη.le)
  change 2*(∫ x,⟪(u-v) (t,x),residualDifference u v p q t x⟫_ℝ) ≤
    η*l2Sq (u-v) t+η⁻¹*(∫ x,‖residualDifference u v p q t x‖^2) at hf
  nlinarith [CompactEnergy.dissipation_nonneg (u-v) t]

/-- Global forced stability restricted by compact difference support, at unit viscosity. -/
theorem forced_stability {T η : ℝ} {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hT : 0 ≤ T) (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T)) (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K) (hs : ∀ r ∈ Icc 0 T,tsupport (fun x => (u-v) (r,x)) ⊆ K)
    (hdu : ∀ t ∈ Ioo 0 T,∀ x,spatialDivergence u t x=0)
    (hdv : ∀ t ∈ Ioo 0 T,∀ x,spatialDivergence v t x=0)
    {g H : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 T)) (hH : ContinuousOn H (Icc 0 T))
    (hG : ∀ t ∈ Ioo 0 T,∀ x,‖spatialDerivative u t x‖ ≤ g t)
    (hFi : ∀ t ∈ Ioo 0 T,Integrable (fun x => ‖residualDifference u v p q t x‖^2))
    (hFH : ∀ t ∈ Ioo 0 T,(∫ x,‖residualDifference u v p q t x‖^2) ≤ H t) (hη : 0 < η) :
    ∀ t ∈ Icc 0 T,l2Sq (u-v) t ≤ Real.exp (∫ s in 0..t,2*g s+η) *
      (l2Sq (u-v) 0+η⁻¹*(∫ s in 0..t,Real.exp (-(∫ r in 0..s,2*g r+η))*H s)) := by
  have h := forced_integrating_factor hT ((hg.const_mul 2).add continuousOn_const)
    (hH.const_mul η⁻¹) (l2Sq_continuousOn hK (hu.sub hv) hs)
    (fun t ht => energy_hasDerivAt hK (hu.sub hv) hs ht)
    (fun t ht => slab_rate_le hu hv hp hq hK hs ht (hdu t ht) (hdv t ht)
      (hG t ht) (hFi t ht) (hFH t ht) hη)
  intro t ht
  simpa only [Pi.sub_def,Pi.add_apply,mul_left_comm,intervalIntegral.integral_const_mul] using h t ht

/-- Equal forces recover the exponent without the Young-inequality penalty. -/
theorem zero_force_stability {T : ℝ} {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hT : 0 ≤ T) (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T)) (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K) (hs : ∀ r ∈ Icc 0 T,tsupport (fun x => (u-v) (r,x)) ⊆ K)
    (hdu : ∀ t ∈ Ioo 0 T,∀ x,spatialDivergence u t x=0)
    (hdv : ∀ t ∈ Ioo 0 T,∀ x,spatialDivergence v t x=0)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 T))
    (hG : ∀ t ∈ Ioo 0 T,∀ x,‖spatialDerivative u t x‖ ≤ g t)
    (hF : ∀ t ∈ Ioo 0 T,∀ x,residualDifference u v p q t x=0) :
    ∀ t ∈ Icc 0 T,l2Sq (u-v) t ≤ Real.exp (∫ s in 0..t,2*g s)*l2Sq (u-v) 0 := by
  have hb (t : ℝ) (ht : t ∈ Ioo 0 T) : CompactEnergy.energyRate (u-v) t ≤ (2*g t)*l2Sq (u-v) t+0 := by
    have htc := Ioo_subset_Icc_self ht
    have hc := slice_compact hK (hs t htc)
    have he := energy_balance (spatial_smooth hu htc) (spatial_smooth hv htc)
      (spatial_smooth hp htc) (spatial_smooth hq htc)
      (time_differentiable_at_interior hu ht) (time_differentiable_at_interior hv ht)
      hc (hdu t ht) (hdv t ht)
      (ClassicalFlowForcedLocalized.residualDifference_continuous_slice hu hv hp hq ht)
    simp only [hF t ht,inner_zero_right,integral_zero,mul_zero,add_zero] at he
    have hcoup := coupling_bound (spatial_smooth hu htc) (spatial_smooth (hu.sub hv) htc) hc (hG t ht)
    have hd := CompactEnergy.dissipation_nonneg (u-v) t
    simp only [Pi.sub_def,Pi.sub_apply] at hcoup he hd ⊢
    nlinarith
  have h := forced_integrating_factor hT (hg.const_mul 2) continuousOn_const
    (l2Sq_continuousOn hK (hu.sub hv) hs)
    (fun t ht => energy_hasDerivAt hK (hu.sub hv) hs ht) hb
  intro t ht
  simpa only [Pi.sub_def,mul_zero,intervalIntegral.integral_zero,add_zero] using h t ht

/-- Smooth given forcing with a fixed compact spatial support supplies its own continuous L2 envelope. -/
theorem smooth_force_stability {T η : ℝ} {u v F : VelocityField} {p q : PressureField} {K KF : Set Space}
    (hT : 0 ≤ T) (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T)) (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K) (hs : ∀ r ∈ Icc 0 T,tsupport (fun x => (u-v) (r,x)) ⊆ K)
    (hdu : ∀ t ∈ Ioo 0 T,∀ x,spatialDivergence u t x=0)
    (hdv : ∀ t ∈ Ioo 0 T,∀ x,spatialDivergence v t x=0)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 T))
    (hG : ∀ t ∈ Ioo 0 T,∀ x,‖spatialDerivative u t x‖ ≤ g t)
    (hF : ContDiffOn ℝ ∞ F (Comparison.slab 0 T)) (hKF : IsCompact KF)
    (hsF : ∀ r ∈ Icc 0 T,tsupport (fun x => F (r,x)) ⊆ KF)
    (hR : ∀ t ∈ Ioo 0 T,∀ x,residualDifference u v p q t x=F (t,x)) (hη : 0 < η) :
    ∀ t ∈ Icc 0 T,l2Sq (u-v) t ≤ Real.exp (∫ s in 0..t,2*g s+η) *
      (l2Sq (u-v) 0+η⁻¹*(∫ s in 0..t,Real.exp (-(∫ r in 0..s,2*g r+η))*l2Sq F s)) := by
  apply forced_stability hT hu hv hp hq hK hs hdu hdv hg (l2Sq_continuousOn hKF hF hsF) hG _ _ hη
  · intro t ht
    simp_rw [hR t ht]
    exact integrable_norm_sq (spatial_smooth hF (Ioo_subset_Icc_self ht)).continuous
      (slice_compact hKF (hsF t (Ioo_subset_Icc_self ht)))
  · intro t ht
    simp only [hR t ht,l2Sq,le_refl]

/-- Stream potential uses the actual smooth bump equal to one near the origin. -/
def streamPotential (x : Space) : ℝ := x 1*ComparisonCutoffs.baseCutoff x

theorem streamPotential_smooth : ContDiff ℝ ∞ streamPotential :=
  (component_contDiff contDiff_id 1).mul ComparisonCutoffs.baseCutoff_smooth

def streamField (x : Space) : Space :=
  spatialPartial 1 streamPotential x • coordinateVector 0 -
    spatialPartial 0 streamPotential x • coordinateVector 1

theorem streamField_smooth : ContDiff ℝ ∞ streamField :=
  ((spatial_partial_contDiff streamPotential_smooth 1).smul contDiff_const).sub
    ((spatial_partial_contDiff streamPotential_smooth 0).smul contDiff_const)

theorem streamPotential_compact : HasCompactSupport streamPotential :=
  ComparisonCutoffs.baseCutoff_hasCompactSupport.mul_left

theorem streamField_compact : HasCompactSupport streamField :=
  (compact_partial streamPotential_compact 1).smul_right.sub
    (compact_partial streamPotential_compact 0).smul_right

theorem streamField_partial (i : Fin 3) (x : Space) :
    spatialPartial i streamField x =
      spatialPartial i (spatialPartial 1 streamPotential) x • coordinateVector 0 -
      spatialPartial i (spatialPartial 0 streamPotential) x • coordinateVector 1 := by
  have h1 := (spatial_partial_contDiff streamPotential_smooth 1).differentiable (by simp) x
  have h0 := (spatial_partial_contDiff streamPotential_smooth 0).differentiable (by simp) x
  dsimp only [spatialPartial,streamField]
  erw [fderiv_fun_sub (h1.smul_const (coordinateVector 0)) (h0.smul_const (coordinateVector 1)),fderiv_smul_const h1,fderiv_smul_const h0]
  rfl

theorem streamField_divergence (t : ℝ) (x : Space) :
    spatialDivergence (fun z => streamField z.2) t x=0 := by
  change (∑ i : Fin 3, spatialPartial i streamField x i)=0
  simp only [streamField_partial]
  simp [coordinateVector]
  exact sub_eq_zero.mpr (ConservativeDifference.partial_comm streamPotential_smooth 0 1 x)

theorem streamField_on_ball {x : Space} (hx : ‖x‖ < 1) : streamField x=coordinateVector 0 := by
  have he : streamPotential =ᶠ[𝓝 x] (fun y : Space => y 1) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    simp only [streamPotential,ComparisonCutoffs.baseCutoff_eq_one hy.le,mul_one]
  have hd : fderiv ℝ streamPotential x = EuclideanSpace.proj 1 := by
    rw [he.fderiv_eq]
    exact (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).fderiv
  simp [streamField,spatialPartial,hd,coordinateVector]

theorem streamField_zero : streamField 0=coordinateVector 0 := streamField_on_ball (by simp)

theorem streamField_energy_pos : 0 < ∫ x : Space,‖streamField x‖^2 := by
  apply (streamField_smooth.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (compact_norm_sq streamField_compact) (fun x => sq_nonneg _) (x := 0)
  simp [streamField_zero,coordinateVector]

def streamVelocity (z : SpaceTime) : Space := z.1 • streamField z.2

theorem streamVelocity_smooth : ContDiff ℝ ∞ streamVelocity :=
  contDiff_fst.smul (streamField_smooth.comp contDiff_snd)

theorem streamVelocity_time (t : ℝ) (x : Space) : temporalDerivative streamVelocity t x=streamField x := by
  change deriv (fun s => s • streamField x) t=streamField x
  simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const (streamField x)).deriv

theorem streamVelocity_spatial (t : ℝ) (x : Space) :
    spatialDerivative streamVelocity t x=t • fderiv ℝ streamField x := by
  exact fderiv_const_smul (streamField_smooth.differentiable (by simp) x) t

def streamLaplacian (x : Space) : Space :=
  ∑ i : Fin 3,spatialPartial i (spatialPartial i streamField) x

theorem streamLaplacian_smooth : ContDiff ℝ ∞ streamLaplacian := by
  have h (i : Fin 3) := spatial_partial_contDiff (spatial_partial_contDiff streamField_smooth i) i
  change ContDiff ℝ ∞ (fun x => ∑ i : Fin 3,spatialPartial i (spatialPartial i streamField) x)
  simpa [Fin.sum_univ_succ,Pi.add_def,spatialPartial] using! (h 0).add ((h 1).add (h 2))

theorem streamLaplacian_compact : HasCompactSupport streamLaplacian := by
  have h (i : Fin 3) := compact_partial (compact_partial streamField_compact i) i
  change HasCompactSupport (fun x => ∑ i : Fin 3,spatialPartial i (spatialPartial i streamField) x)
  simpa [Fin.sum_univ_succ,Pi.add_def,spatialPartial] using! (h 0).add ((h 1).add (h 2))

theorem streamVelocity_laplacian (t : ℝ) (x : Space) :
    spatialLaplacian streamVelocity t x=t • streamLaplacian x := by
  simp only [spatialLaplacian,streamVelocity_spatial,smul_apply,streamLaplacian,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := (spatial_partial_contDiff streamField_smooth i).differentiable (by simp) x
  erw [fderiv_const_smul h t]
  rfl

theorem streamVelocity_divergence (t : ℝ) (x : Space) : spatialDivergence streamVelocity t x=0 := by
  have h := streamField_divergence t x
  simp only [spatialDivergence,streamVelocity_spatial,smul_apply]
  change (∑ i : Fin 3,t * (fderiv ℝ streamField x (coordinateVector i)) i)=0
  rw [← Finset.mul_sum]
  change t * spatialDivergence (fun z => streamField z.2) t x=0
  rw [h,mul_zero]

/-- The forcing is calculated from the accelerating compact stream field. -/
def streamForce (z : SpaceTime) : Space := streamField z.2 +
  z.1^2 • (fderiv ℝ streamField z.2 (streamField z.2)) - z.1 • streamLaplacian z.2

theorem streamForce_smooth : ContDiff ℝ ∞ streamForce := by
  exact ((streamField_smooth.comp contDiff_snd).add
    ((contDiff_fst.pow 2).smul (((streamField_smooth.fderiv_right infty_add_one_le).clm_apply
      streamField_smooth).comp contDiff_snd))).sub (contDiff_fst.smul (streamLaplacian_smooth.comp contDiff_snd))

theorem streamForce_residual (t : ℝ) (x : Space) :
    residualDifference streamVelocity 0 0 0 t x=streamForce (t,x) := by
  simp only [residualDifference,NavierStokesR3.ProblemStatement.navierStokesResidual,
    streamVelocity_time,streamVelocity_laplacian,advection,streamVelocity_spatial,one_smul]
  simp [temporalDerivative,spatialDerivative,spatialLaplacian,pressureGradient,streamForce,
    streamVelocity,smul_smul,pow_two]

def streamSupport : Set Space := tsupport streamField ∪ tsupport streamLaplacian

theorem streamSupport_compact : IsCompact streamSupport :=
  streamField_compact.union streamLaplacian_compact

theorem streamVelocity_support (t : ℝ) : tsupport (fun x => streamVelocity (t,x)) ⊆ streamSupport :=
  (tsupport_smul_subset_right (fun _ => t) streamField).trans subset_union_left

theorem streamForce_support (t : ℝ) : tsupport (fun x => streamForce (t,x)) ⊆ streamSupport := by
  apply closure_minimal _ streamSupport_compact.isClosed
  intro x hx
  by_contra h
  have hw : streamField x=0 := image_eq_zero_of_notMem_tsupport (fun hh => h (Or.inl hh))
  have hl : streamLaplacian x=0 := image_eq_zero_of_notMem_tsupport (fun hh => h (Or.inr hh))
  simp [mem_support,streamForce,hw,hl] at hx

theorem streamForce_nonzero : residualDifference streamVelocity 0 0 0 0 0 ≠ 0 := by
  rw [streamForce_residual]
  simp [streamForce,streamField_zero,coordinateVector]

theorem streamVelocity_energy (t : ℝ) : l2Sq streamVelocity t=t^2*(∫ x : Space,‖streamField x‖^2) := by
  simp only [l2Sq,streamVelocity,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]

theorem streamVelocity_energy_pos {t : ℝ} (ht : 0 < t) : 0 < l2Sq streamVelocity t := by
  rw [streamVelocity_energy]
  exact mul_pos (sq_pos_of_pos ht) streamField_energy_pos

/-- The compact derivative of the stream field gives a genuine uniform gradient bound. -/
theorem streamVelocity_gradient_bound {T : ℝ} (hT : 0 ≤ T) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ t ∈ Icc 0 T,∀ x,‖spatialDerivative streamVelocity t x‖ ≤ G := by
  obtain ⟨C,hC⟩ := ((streamField_smooth.fderiv_right infty_add_one_le).continuous).bounded_above_of_compact_support
    (streamField_compact.fderiv ℝ)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨T*C,mul_nonneg hT hC0,?_⟩
  intro t ht x
  rw [streamVelocity_spatial,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  exact mul_le_mul ht.2 (hC x) (norm_nonneg _) hT

theorem streamForce_energy_pos : 0 < l2Sq streamForce 0 := by
  simpa [l2Sq,streamForce] using streamField_energy_pos

/-- The genuine accelerating stream field consumes the global forced estimate. -/
theorem stream_witness_stability {T η : ℝ} (hT : 0 ≤ T) (hη : 0 < η) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ t ∈ Icc 0 T,
      l2Sq streamVelocity t ≤ Real.exp ((2*G+η)*t) *
        (η⁻¹*(∫ s in 0..t,Real.exp (-((2*G+η)*s))*l2Sq streamForce s)) := by
  obtain ⟨G,hG0,hG⟩ := streamVelocity_gradient_bound hT
  refine ⟨G,hG0,?_⟩
  have hs : ∀ r ∈ Icc 0 T,tsupport (fun x => (streamVelocity-0) (r,x)) ⊆ streamSupport := by
    intro r _; simpa only [sub_zero] using streamVelocity_support r
  have hdu : ∀ t ∈ Ioo 0 T,∀ x,spatialDivergence streamVelocity t x=0 :=
    fun t _ x => streamVelocity_divergence t x
  have hdv : ∀ t ∈ Ioo 0 T,∀ x,spatialDivergence (0 : VelocityField) t x=0 := by
    intro t _ x; simp [spatialDivergence,spatialDerivative]
  have hb := smooth_force_stability (u := streamVelocity) (v := 0) (p := 0) (q := 0) (F := streamForce) hT streamVelocity_smooth.contDiffOn contDiffOn_const
    contDiffOn_const contDiffOn_const streamSupport_compact hs hdu hdv
    (continuousOn_const : ContinuousOn (fun _ : ℝ => G) (Icc 0 T))
    (fun t ht x => hG t (Ioo_subset_Icc_self ht) x) streamForce_smooth.contDiffOn
    streamSupport_compact (fun r _ => streamForce_support r)
    (fun t _ x => streamForce_residual t x) hη
  intro t ht
  simpa only [sub_zero,streamVelocity_energy,intervalIntegral.integral_const,smul_eq_mul,
    mul_comm,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,add_zero,zero_add] using hb t ht

end SKEFTHawking.ClassicalFlowForcedCompact
