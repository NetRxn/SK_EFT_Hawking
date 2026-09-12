import NavierStokes.R3.LocalizedDifferenceEnergy

/-! Actual residual forcing in compactly weighted energy balances. No whole-space
pressure recovery or unequal-force global stability is asserted. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace SKEFTHawking.ClassicalFlowForcedLocalized
open NavierStokesR3
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open Comparison (weightedEnergy weightedEnergyRate weightedDissipation gradientSq)
open LocalizedDifferenceEnergy

def residualDifference (u v : VelocityField) (p q : PressureField) (t : ℝ) (x : Space) : Space :=
  NavierStokesR3.ProblemStatement.navierStokesResidual 1 u p t x -
    NavierStokesR3.ProblemStatement.navierStokesResidual 1 v q t x

def forceWork (χ : Space → ℝ) (w : VelocityField) (F : ℝ → Space → Space) (t : ℝ) : ℝ :=
  ∫ x, χ x * ⟪w (t,x), F t x⟫_ℝ

theorem integrable_forceWork {χ : Space → ℝ} {w : VelocityField} {F : ℝ → Space → Space} {t : ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hw : Continuous (fun x => w (t,x))) (hF : Continuous (F t)) :
    Integrable (fun x => χ x * ⟪w (t,x),F t x⟫_ℝ) :=
  integrable_cutoff_mul hχ hcχ (hw.inner hF)

theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

/-- The force is the difference of the actual unit-viscosity residuals. -/
theorem forced_difference_equation {u v : VelocityField} {p q : PressureField} {t : ℝ} {x : Space}
    (hu : ContDiff ℝ ∞ (fun y : Space => u (t,y)))
    (hv : ContDiff ℝ ∞ (fun y : Space => v (t,y)))
    (hp : ContDiff ℝ ∞ (fun y : Space => p (t,y)))
    (hq : ContDiff ℝ ∞ (fun y : Space => q (t,y)))
    (htu : DifferentiableAt ℝ (fun s => u (s,x)) t)
    (htv : DifferentiableAt ℝ (fun s => v (s,x)) t) :
    temporalDerivative (u-v) t x = spatialLaplacian (u-v) t x -
      spatialDerivative u t x ((u-v) (t,x)) - spatialDerivative (u-v) t x (v (t,x)) -
      pressureGradient (p-q) t x + residualDifference u v p q t x := by
  have ha := advection_difference hu hv x
  rw [temporalDerivative_sub htu htv,spatialLaplacian_sub hu hv,pressureGradient_sub hp hq]
  simp only [residualDifference,NavierStokesR3.ProblemStatement.navierStokesResidual,one_smul]
  rw [show temporalDerivative u t x + advection u t x - spatialLaplacian u t x + pressureGradient p t x -
      (temporalDerivative v t x + advection v t x - spatialLaplacian v t x + pressureGradient q t x) =
      temporalDerivative u t x - temporalDerivative v t x + (advection u t x - advection v t x) -
      (spatialLaplacian u t x - spatialLaplacian v t x) + (pressureGradient p t x - pressureGradient q t x) by abel,ha]
  abel

/-- Compactly weighted balance with explicit continuous residual forcing. -/
theorem forced_energy_balance {χ : Space → ℝ} {u v : VelocityField}
    {p q : PressureField} {t : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (htu : ∀ x : Space, DifferentiableAt ℝ (fun r => u (r, x)) t)
    (htv : ∀ x : Space, DifferentiableAt ℝ (fun r => v (r, x)) t)
    (hdivu : ∀ x : Space, spatialDivergence u t x = 0)
    (hdivv : ∀ x : Space, spatialDivergence v t x = 0)
    (hF : Continuous (residualDifference u v p q t)) :
    (1 / 2 : ℝ) * weightedEnergyRate χ (u - v) t + weightedDissipation χ (u - v) t =
      -(∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        fderiv ℝ χ x (v (t, x))) +
      (∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) +
      forceWork χ (u - v) (residualDifference u v p q) t := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) := hu.sub hv
  have hπ : ContDiff ℝ ∞ (fun x : Space => (p - q) (t, x)) := hp.sub hq
  have hdivw : ∀ x : Space, spatialDivergence (u - v) t x = 0 := by
    intro x
    rw [spatialDivergence_sub hu hv, hdivu x, hdivv x, sub_self]
  have hiL : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ (hw.inner ℝ (spatialLaplacian_contDiff hw)).continuous
  have hiC : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ
      (hw.inner ℝ ((hu.fderiv_right infty_add_one_le).clm_apply hw)).continuous
  have hiT : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ
      (hw.inner ℝ ((hw.fderiv_right infty_add_one_le).clm_apply hv)).continuous
  have hiP : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ (hw.inner ℝ (pressureGradient_contDiff hπ)).continuous
  have hiLC : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) :=
    hiL.sub hiC
  have hiLCT : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) :=
    hiLC.sub hiT
  have hiF := integrable_forceWork hχ.continuous hcχ hw.continuous hF
  have hEq : (fun x : Space => χ x *
      (2 * ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ)) =
      (fun x : Space => 2 * (
        χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
        χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
        χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ -
        χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ +
        χ x * ⟪(u - v) (t, x), residualDifference u v p q t x⟫_ℝ)) := by
    funext x
    rw [forced_difference_equation hu hv hp hq (htu x) (htv x)]
    simp only [inner_add_right,inner_sub_right]
    ring
  have hRate : weightedEnergyRate χ (u - v) t = 2 * (
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) -
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) -
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) -
      ∫ x : Space, χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) +
      2 * forceWork χ (u - v) (residualDifference u v p q) t := by
    have hsplit := integral_add (hiLCT.sub hiP) hiF
    simp only [Pi.sub_apply] at hsplit
    unfold weightedEnergyRate forceWork
    rw [hEq, integral_const_mul]
    erw [hsplit, integral_sub hiLCT hiP,
      integral_sub hiLC hiT, integral_sub hiL hiC]
    simp only [Pi.sub_apply]
    ring
  have hL := integral_weighted_spatialLaplacian hχ hw hcχ
  have hT := integral_weighted_transport hχ hw hv hcχ hdivv
  have hP : (∫ x : Space, χ x *
      ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) =
      -(∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) := by
    simp_rw [inner_pressureGradient]
    exact integral_weighted_pressure hχ hπ hw hcχ hdivw
  change (∫ x : Space, χ x *
    ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) =
      -weightedDissipation χ (u - v) t +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) at hL
  change (∫ x : Space, χ x *
    ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) =
      -(1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        fderiv ℝ χ x (v (t, x))) at hT
  rw [hL, hT, hP] at hRate
  rw [hRate]
  ring


theorem residual_continuous_slice {a b t : ℝ} {u : VelocityField} {p : PressureField}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab a b))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab a b)) (ht : t ∈ Ioo a b) :
    Continuous (NavierStokesR3.ProblemStatement.navierStokesResidual 1 u p t) := by
  have hn : (1 : WithTop ℕ∞) ≤ ∞ :=
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 1).le
  have htime := CompactTimeIntegral.continuousOn_timeDeriv_of_contDiffOn (hu.of_le hn)
  have htime' : Continuous (temporalDerivative u t) := by
    simpa only [temporalDerivative,deriv] using! CompactTimeIntegral.continuous_slice htime ht
  have hs := spatial_smooth hu (Ioo_subset_Icc_self ht)
  have hp' := spatial_smooth hp (Ioo_subset_Icc_self ht)
  change Continuous (fun x => temporalDerivative u t x + advection u t x -
    1 • spatialLaplacian u t x + pressureGradient p t x)
  simpa only [one_smul,advection,Pi.add_apply,Pi.sub_apply,spatialDerivative] using!
    ((htime'.add ((hs.fderiv_right infty_add_one_le).clm_apply hs).continuous).sub
      (spatialLaplacian_contDiff hs).continuous).add (pressureGradient_contDiff hp').continuous

theorem residualDifference_continuous_slice {a b t : ℝ} {u v : VelocityField} {p q : PressureField}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab a b))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab a b))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab a b))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab a b)) (ht : t ∈ Ioo a b) :
    Continuous (residualDifference u v p q t) :=
  (residual_continuous_slice hu hp ht).sub (residual_continuous_slice hv hq ht)

/-- Slab smoothness supplies the extra work integrability, rather than assuming it. -/
theorem integrable_residual_work {a b t : ℝ} {χ : Space → ℝ} {u v : VelocityField} {p q : PressureField}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab a b))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab a b))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab a b))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab a b)) (ht : t ∈ Ioo a b) :
    Integrable (fun x => χ x * ⟪(u-v) (t,x),residualDifference u v p q t x⟫_ℝ) :=
  integrable_forceWork hχ hcχ (spatial_smooth (hu.sub hv) (Ioo_subset_Icc_self ht)).continuous
    (residualDifference_continuous_slice hu hv hp hq ht)

theorem hasDerivAt_forced_energy_balance {a b t : ℝ} {χ : Space → ℝ}
    {u v : VelocityField} {p q : PressureField}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab a b))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab a b))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab a b))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab a b)) (ht : t ∈ Ioo a b)
    (hdivu : ∀ x : Space, spatialDivergence u t x = 0)
    (hdivv : ∀ x : Space, spatialDivergence v t x = 0) :
    HasDerivAt (weightedEnergy χ (u - v))
      (-2 * weightedDissipation χ (u - v) t -
        2 * (∫ x : Space, χ x *
          ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) +
        (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
          ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) +
        (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ χ x (v (t, x))) +
        2 * (∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) +
        2 * forceWork χ (u-v) (residualDifference u v p q) t) t := by
  have hd : HasDerivAt (weightedEnergy χ (u - v))
      (weightedEnergyRate χ (u - v) t) t :=
    weightedEnergy_hasDerivAt hχ hcχ (hu.sub hv) ht
  have hb := forced_energy_balance hχ hcχ
    (spatial_smooth hu (Ioo_subset_Icc_self ht)) (spatial_smooth hv (Ioo_subset_Icc_self ht))
    (spatial_smooth hp (Ioo_subset_Icc_self ht)) (spatial_smooth hq (Ioo_subset_Icc_self ht))
    (time_differentiable_at_interior hu ht) (time_differentiable_at_interior hv ht)
    hdivu hdivv (residualDifference_continuous_slice hu hv hp hq ht)
  convert! hd using 1
  linarith

/-- Weighted Young inequality retains the cutoff on velocity energy only. -/
theorem weighted_work_pointwise (w F : Space) {χ η : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hη : 0 < η) :
    2 * |χ * ⟪w,F⟫_ℝ| ≤ η * (χ * ‖w‖^2) + η⁻¹ * ‖F‖^2 := by
  have hy : 2 * ‖w‖ * ‖F‖ ≤ η * ‖w‖^2 + η⁻¹ * ‖F‖^2 := by
    apply (mul_le_mul_iff_right₀ hη).mp
    simp only [mul_add,← mul_assoc,mul_inv_cancel₀ hη.ne',one_mul]
    nlinarith [sq_nonneg (η * ‖w‖ - ‖F‖)]
  have hi := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm w F) hχ
  have hh := mul_le_mul_of_nonneg_left hy hχ
  have hf := mul_le_mul_of_nonneg_right hχ1 (mul_nonneg (inv_nonneg.mpr hη.le) (sq_nonneg ‖F‖))
  rw [abs_mul,abs_of_nonneg hχ]
  nlinarith

/-- A square-integrable force gives the eta-weighted L2 work estimate. -/
theorem forceWork_bound {χ : Space → ℝ} {w : VelocityField} {F : ℝ → Space → Space} {t η : ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hw : Continuous (fun x => w (t,x))) (hF : Continuous (F t))
    (hFsq : Integrable (fun x => ‖F t x‖^2)) (hη : 0 < η) :
    2 * |forceWork χ w F t| ≤ η * weightedEnergy χ w t + η⁻¹ * ∫ x, ‖F t x‖^2 := by
  have hi := integrable_forceWork hχ hcχ hw hF
  have he := integrable_weighted_energy hχ hcχ hw
  have hm := integral_mono (hi.abs.const_mul 2) ((he.const_mul η).add (hFsq.const_mul η⁻¹))
    (fun x => weighted_work_pointwise (w (t,x)) (F t x) (hχ0 x) (hχ1 x) hη)
  have ha : |forceWork χ w F t| ≤ ∫ x, |χ x * ⟪w (t,x),F t x⟫_ℝ| := abs_integral_le_integral_abs
  simp only [Pi.add_apply] at hm
  rw [integral_add (he.const_mul η) (hFsq.const_mul η⁻¹)] at hm
  simp only [integral_const_mul] at hm
  change 2 * (∫ x, |χ x * ⟪w (t,x),F t x⟫_ℝ|) ≤
    η * weightedEnergy χ w t + η⁻¹ * ∫ x, ‖F t x‖^2 at hm
  linarith

theorem zero_residual_work {u v : VelocityField} {p q : PressureField} (χ : Space → ℝ) (t : ℝ)
    (h : ∀ x, NavierStokesR3.ProblemStatement.navierStokesResidual 1 u p t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual 1 v q t x) :
    forceWork χ (u-v) (residualDifference u v p q) t = 0 := by
  simp [forceWork,residualDifference,h]

/-- Uniform acceleration supplies a nonzero actual residual for the localized identity.
Its constant spatial force is not claimed square integrable on all of space. -/
def acceleratingVelocity (c : Space) : VelocityField := fun z => z.1 • c

theorem acceleratingVelocity_smooth (c : Space) : ContDiff ℝ ∞ (acceleratingVelocity c) :=
  contDiff_fst.smul contDiff_const

theorem acceleratingVelocity_temporal (c : Space) (t : ℝ) (x : Space) :
    temporalDerivative (acceleratingVelocity c) t x = c := by
  have hd := (hasDerivAt_id t).smul_const c
  simpa only [temporalDerivative,acceleratingVelocity,deriv,id_eq,one_smul] using hd.deriv

theorem acceleratingVelocity_residual (c : Space) (t : ℝ) (x : Space) :
    residualDifference (acceleratingVelocity c) 0 0 0 t x = c := by
  unfold residualDifference NavierStokesR3.ProblemStatement.navierStokesResidual
  rw [acceleratingVelocity_temporal]
  simp [advection,spatialDerivative,spatialLaplacian,
    pressureGradient,temporalDerivative,acceleratingVelocity]

theorem acceleratingVelocity_nonzero_residual (c : Space) (hc : c ≠ 0) (t : ℝ) (x : Space) :
    residualDifference (acceleratingVelocity c) 0 0 0 t x ≠ 0 := by
  rw [acceleratingVelocity_residual]
  exact hc

theorem equal_residual_balance_recovery {χ : Space → ℝ} {u v : VelocityField}
    {p q : PressureField} {t : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (htu : ∀ x : Space, DifferentiableAt ℝ (fun r => u (r, x)) t)
    (htv : ∀ x : Space, DifferentiableAt ℝ (fun r => v (r, x)) t)
    (hdivu : ∀ x : Space, spatialDivergence u t x = 0)
    (hdivv : ∀ x : Space, spatialDivergence v t x = 0)
    (hNS : ∀ x : Space, ProblemStatement.navierStokesResidual 1 u p t x =
      ProblemStatement.navierStokesResidual 1 v q t x) :
    (1 / 2 : ℝ) * weightedEnergyRate χ (u - v) t + weightedDissipation χ (u - v) t =
      -(∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        fderiv ℝ χ x (v (t, x))) +
      ∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x)) := by
  have hzero : residualDifference u v p q t = fun _ => 0 := by
    funext x
    simp [residualDifference,hNS]
  have hF : Continuous (residualDifference u v p q t) := by rw [hzero]; exact continuous_const
  have hb := forced_energy_balance hχ hcχ hu hv hp hq htu htv hdivu hdivv hF
  rw [zero_residual_work χ t hNS] at hb
  simpa only [add_zero] using hb

/-- The L2 work estimate for actual residual differences of smooth slab fields. -/
theorem residual_work_bound {a b t η : ℝ} {χ : Space → ℝ} {u v : VelocityField} {p q : PressureField}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab a b))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab a b))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab a b))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab a b)) (ht : t ∈ Ioo a b)
    (hF : Integrable (fun x => ‖residualDifference u v p q t x‖^2)) (hη : 0 < η) :
    2 * |forceWork χ (u-v) (residualDifference u v p q) t| ≤
      η * weightedEnergy χ (u-v) t + η⁻¹ * ∫ x, ‖residualDifference u v p q t x‖^2 :=
  forceWork_bound hχ hcχ hχ0 hχ1 (spatial_smooth (hu.sub hv) (Ioo_subset_Icc_self ht)).continuous
    (residualDifference_continuous_slice hu hv hp hq ht) hF hη

theorem acceleratingVelocity_divergence (c : Space) (t : ℝ) (x : Space) :
    spatialDivergence (acceleratingVelocity c) t x = 0 := by
  simp [spatialDivergence,spatialDerivative,acceleratingVelocity]

/-- The nonzero actual residual performs a computed amount of localized work. -/
theorem acceleratingVelocity_work (χ : Space → ℝ) (c : Space) (t : ℝ) :
    forceWork χ (acceleratingVelocity c) (residualDifference (acceleratingVelocity c) 0 0 0) t =
      t * ‖c‖^2 * ∫ x, χ x := by
  unfold forceWork
  simp only [acceleratingVelocity_residual,acceleratingVelocity,real_inner_smul_left,real_inner_self_eq_norm_sq]
  have he : (fun x => χ x * (t * ‖c‖^2)) = fun x => (t * ‖c‖^2) * χ x := by funext x; ring
  rw [he,integral_const_mul]

/-- The actual smooth divergence-free accelerating flow consumes the compact-energy derivative API. -/
theorem acceleratingVelocity_energy_derivative {a b t : ℝ} {χ : Space → ℝ} (c : Space)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (ht : t ∈ Ioo a b) :
    HasDerivAt (weightedEnergy χ (acceleratingVelocity c))
      (2 * forceWork χ (acceleratingVelocity c) (residualDifference (acceleratingVelocity c) 0 0 0) t) t := by
  have hd := weightedEnergy_hasDerivAt hχ hcχ (acceleratingVelocity_smooth c).contDiffOn ht
  have hr : weightedEnergyRate χ (acceleratingVelocity c) t =
      2 * forceWork χ (acceleratingVelocity c) (residualDifference (acceleratingVelocity c) 0 0 0) t := by
    unfold weightedEnergyRate forceWork
    simp only [acceleratingVelocity_temporal,acceleratingVelocity_residual]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hr] at hd
  exact hd

theorem acceleratingVelocity_work_positive {χ : Space → ℝ} {c : Space} {t : ℝ}
    (hχ : 0 < ∫ x, χ x) (hc : c ≠ 0) (ht : 0 < t) :
    0 < forceWork χ (acceleratingVelocity c) (residualDifference (acceleratingVelocity c) 0 0 0) t := by
  rw [acceleratingVelocity_work]
  exact mul_pos (mul_pos ht (sq_pos_of_pos (norm_pos_iff.mpr hc))) hχ

end SKEFTHawking.ClassicalFlowForcedLocalized
