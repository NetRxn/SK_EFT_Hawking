/-
Adapted from PrimeNumberTheoremAnd (PNT+), revision
a5154676af9aa3095150ee410cdda80555aa0642.
Copyright: the respective upstream authors and contributors.
Released under the Apache License, Version 2.0.
Upstream: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
This compatibility extraction preserves original mathematical declarations and
namespaces. Blueprint metadata is retained as comments; project imports are
flattened in dependency order. Unused incomplete alternative Fourier estimates
are excluded. Compatibility modifications are recorded in the extraction manifest.
-/
import Mathlib.Algebra.Notation.Support
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Batteries.Tactic.Lemma
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Bound
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Convolution
import Mathlib.NumberTheory.Harmonic.Bounds

/- Upstream: PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean, original lines 1–13.
Revision a5154676af9aa3095150ee410cdda80555aa0642.
See extraction manifest for metadata/import removal and excluded alternatives. -/
section
namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function

end

/- Upstream: PrimeNumberTheoremAnd/Sobolev.lean, original lines 1–359.
Revision a5154676af9aa3095150ee410cdda80555aa0642.
See extraction manifest for metadata/import removal and excluded alternatives. -/
section
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  ext x ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  ext v ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  -- Definitions
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  -- Properties of h
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    convert! CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  -- Proof
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)

  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4

  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1] ; convert! (l5.add l7).deriv using 1 ; ring
      simp_rw [this, F]

    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert! ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert! ← evg'.deriv ; exact deriv_const' _
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · simpa [h] using! ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

end

/- Upstream: PrimeNumberTheoremAnd/Fourier.lean, original lines 1–186.
Revision a5154676af9aa3095150ee410cdda80555aa0642.
See extraction manifest for metadata/import removal and excluded alternatives. -/
section
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp)

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert! (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  change _ = ((-u : ℝ) : ℂ) * _ -- `scomp` introduces ℝ-smul on ℂ, which we undo
  simp ; ring

lemma fourierIntegral_deriv_aux2 (e : ℝ →ᵇ ℂ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (⇑e * f) :=
  hf.bdd_mul e.continuous.aestronglyMeasurable (ae_of_all _ e.norm_coe_le_norm)

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

/-- If, eventually in `T`, the integrand `f T` is bounded on `uIoc lo hi` by `B T`
and `B T * |hi - lo| → 0`, then the interval integral `∫ x in lo..hi, f T x → 0`. -/
lemma tendsto_intervalIntegral_zero_of_uniform_norm_bound
    {f : ℝ → ℝ → ℂ} {lo hi : ℝ} {B : ℝ → ℝ}
    (hB : Filter.Tendsto (fun T : ℝ => B T * |hi - lo|) Filter.atTop (nhds 0))
    (hf : ∀ᶠ T in Filter.atTop, ∀ x ∈ Set.uIoc lo hi, ‖f T x‖ ≤ B T) :
    Filter.Tendsto (fun T : ℝ => ∫ x in lo..hi, f T x) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [hf] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hT x hx)

/-- The decay `K * (log (T + 2) / (T + 2)) → 0` as `T → ∞`, for any constant `K`. -/
lemma tendsto_const_mul_log_add_two_div_add_two_atTop (K : ℝ) :
    Filter.Tendsto (fun T : ℝ => K * (Real.log (T + 2) / (T + 2)))
      Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0))
  have hshift : Filter.Tendsto (fun T : ℝ => Real.log (T + 2) / (T + 2))
      Filter.atTop (nhds 0) := by
    have := h0.comp (tendsto_atTop_add_const_right Filter.atTop 2 tendsto_id)
    simpa [Function.comp_def] using this
  simpa using hshift.const_mul K

/-- Fourier-transform decay from an integrable derivative: for integrable,
differentiable `g` with integrable derivative, `‖𝓕 g w‖ ≤ (∫ ‖deriv g x‖) / (2π·|w|)`. -/
lemma norm_fourier_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {w : ℝ} (hw : w ≠ 0) :
    ‖𝓕 g w‖ ≤ (∫ x, ‖deriv g x‖ ∂volume) / ((2 * Real.pi) * |w|) := by
  have hmul :
      𝓕 (deriv g) w = (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w := by
    have h := congrFun (Real.fourier_deriv hg hdiff hg') w
    simpa [smul_eq_mul, mul_assoc] using h
  have h_fourier :
      ‖𝓕 (deriv g) w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
      (deriv g) w
  have hleft :
      ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ =
        ‖(2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w‖ := by
    have htwopi : ‖(2 * ↑Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_two, Complex.norm_of_nonneg Real.pi_pos.le]
    have hwc : ‖(w : ℂ)‖ = |w| := by rw [norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, norm_mul, htwopi, norm_I, hwc]
    ring
  have hmain : ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    rw [hleft, ← hmul]
    exact h_fourier
  have hpos : 0 < (2 * Real.pi) * |w| := by
    positivity
  exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmain)

/-- The oscillatory-integral form of the decay bound: for `0 < T`,
`‖∫ g y · exp(T·i·y)‖ ≤ (∫ ‖deriv g x‖) / T`. -/
lemma norm_oscillatory_integral_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : 0 < T) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / T := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT.ne') (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = T := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    have hneg : -T / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hT) htwopi_pos
    rw [abs_of_neg hneg]
    field_simp [Real.pi_ne_zero]
  rw [hden]

/-- The `|T|` variant of the oscillatory-integral decay bound: for `T ≠ 0`,
`‖∫ g y · exp(T·i·y)‖ ≤ (∫ ‖deriv g x‖) / |T|`. -/
lemma norm_oscillatory_integral_le_integral_deriv_div_abs
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : T ≠ 0) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / |T| := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT) (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = |T| := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    rw [abs_div, abs_neg, abs_of_pos htwopi_pos]
    field_simp [Real.pi_ne_zero]
  rw [hden]

end

/- Upstream: PrimeNumberTheoremAnd/SmoothExistence.lean, original lines 1–107.
Revision a5154676af9aa3095150ee410cdda80555aa0642.
See extraction manifest for metadata/import removal and excluded alternatives. -/
section
open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]

/--
Let $\nu$ be a bumpfunction.
-/

/- Upstream blueprint metadata (inert):
@[blueprint
  (title := "SmoothExistence")
  (statement := /--
  There exists a smooth (once differentiable would be enough),
  nonnegative ``bumpfunction'' $\nu$,
  supported in $[1/2,2]$ with total mass one:
  $$
  \int_0^\infty \nu(x)\frac{dx}{x} = 1.
  $$
  -/)
  (proof := /-- Same idea as Urysohn-type argument. -/)]
-/
lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end

/- Upstream: PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean, original lines 1–41.
Revision a5154676af9aa3095150ee410cdda80555aa0642.
See extraction manifest for metadata/import removal and excluded alternatives. -/
section
open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

-- to replace existing `isLittleO_const_id_atTop`
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

-- to replace existing `isLittleO_const_id_atBot`
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics

end

/- Upstream: PrimeNumberTheoremAnd/Defs.lean, original lines 1–304.
Revision a5154676af9aa3095150ee410cdda80555aa0642.
See extraction manifest for metadata/import removal and excluded alternatives. -/
section
open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev

noncomputable abbrev nth_prime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

noncomputable abbrev nth_prime' (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

noncomputable abbrev Psi (x : ℝ) : ℝ := ψ x

noncomputable def M (x : ℝ) : ℝ :=
  ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)

noncomputable abbrev nth_prime_gap (n : ℕ) : ℕ :=
  nth_prime (n + 1) - nth_prime n

def prime_gap_record (p g : ℕ) : Prop :=
  ∃ n, nth_prime n = p ∧ nth_prime_gap n = g ∧
    ∀ k, nth_prime k < p → nth_prime_gap k < g

open Classical in
/- Upstream blueprint metadata (inert):
@[blueprint
  "first-gap-def"
  (title := "First prime gap")
  (statement := /--
  $P(g)$ is the first prime $p_n$ for which the prime gap
  $p_{n+1}-p_n$ is equal to $g$, or $0$ if no such gap
  exists. -/)]
-/
noncomputable def first_gap (g : ℕ) : ℕ :=
  if h : ∃ n, nth_prime_gap n = g then
    nth_prime (Nat.find h)
  else 0

def first_gap_record (g P : ℕ) : Prop :=
  first_gap g = P ∧
    ∀ g' ∈ Finset.Ico 1 g,
      Even g' ∨ g' = 1 → first_gap g' ∈ Set.Ico 1 P

def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h

def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x) ^ k)

/- Upstream blueprint metadata (inert):
@[blueprint
  "pi-def"
  (title := "pi")
  (statement := /--
  $\pi(x)$ is the number of primes less than or equal to
  $x$. -/)]
-/
noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊

/- Upstream blueprint metadata (inert):
@[blueprint
  "pi-star-def"
  (title := "pi star")
  (statement := /--
  $\pi^*(x) = \sum_{k \geq 1} \pi(x^{1/k}) / k$. -/)]
-/
noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑' (k : ℕ), pi (x ^ (1 / (k + 1 : ℝ))) / (k + 1 : ℝ)

/- Upstream blueprint metadata (inert):
@[blueprint
  "li-def"
  (title := "li and Li")
  (statement := /--
  $\mathrm{li}(x) = \int_0^x \frac{dt}{\log t}$ (in the
  principal value sense) and
  $\mathrm{Li}(x) = \int_2^x \frac{dt}{\log t}$. -/)]
-/
noncomputable def li (x : ℝ) : ℝ :=
  lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦
    ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1 - ε) (1 + ε)),
      1 / log t))

/- Upstream blueprint metadata (inert):
@[blueprint "li-def"]
-/
noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

/- Upstream blueprint metadata (inert):
@[blueprint
  "Epsi-def"
  (title := "Equation (2) of FKS2")
  (statement := /-- $E_\psi(x) = |\psi(x) - x| / x$ -/)]
-/
noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x

noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) :=
  A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1 : ℝ) / (2 : ℝ)))

/- Upstream blueprint metadata (inert):
@[blueprint
  "classical-bound-psi"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\psi$ satisfies a \emph{classical bound}
  with parameters $A, B, C, R, x_0$ if for all
  $x \geq x_0$ we have
  \[ E_\psi(x) \leq A \left(\frac{\log x}{R}\right)^B
     \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}
     \right). \]
  We say that it obeys a \emph{numerical bound} with
  parameter $\varepsilon(x_0)$ if for all $x \geq x_0$
  we have
  \[ E_\psi(x) \leq \varepsilon(x_0). \]
  -/)]
-/
def Eψ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eψ x ≤ admissible_bound A B C R x

def Eψ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ ε

def Eψ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eψ.bound (ε x₀) x₀

/- Upstream blueprint metadata (inert):
@[blueprint
  "Epi-def"
  (title := "Equation (1) of FKS2")
  (statement := /--
  $E_\pi(x) = |\pi(x) - \mathrm{Li}(x)| /
  (x / \log x)$. -/)]
-/
noncomputable def Eπ (x : ℝ) : ℝ :=
  |pi x - Li x| / (x / log x)

noncomputable def Eπ_star (x : ℝ) : ℝ :=
  |pi_star x - Li x| / (x / log x)

/- Upstream blueprint metadata (inert):
@[blueprint
  "Etheta-def"
  (title := "Equation (2) of FKS2")
  (statement := /--
  $E_\theta(x) = |\theta(x) - x| / x$ -/)]
-/
noncomputable def Eθ (x : ℝ) : ℝ := |θ x - x| / x

/- Upstream blueprint metadata (inert):
@[blueprint
  "classical-bound-theta"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\theta$ satisfies a \emph{classical bound}
  with parameters $A, B, C, R, x_0$ if for all
  $x \geq x_0$ we have
  \[ E_\theta(x) \leq A \left(\frac{\log x}{R}\right)^B
     \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}
     \right). \]
  We say that it obeys a \emph{numerical bound} with
  parameter $\varepsilon(x_0)$ if for all $x \geq x_0$
  we have
  \[ E_\theta(x) \leq \varepsilon(x_0). \]
  -/)]
-/
def Eθ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eθ x ≤ admissible_bound A B C R x

def Eθ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  ∀ x ≥ x₀, Eθ x ≤ ε x₀

/- Upstream blueprint metadata (inert):
@[blueprint "classical-bound-pi"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\pi$ satisfies a \emph{classical bound}
  with parameters $A, B, C, R, x_0$ if for all
  $x \geq x_0$ we have
  \[ E_\pi(x) \leq A \left(\frac{\log x}{R}\right)^B
     \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}
     \right). \]
  We say that it obeys a \emph{numerical bound} with
  parameter $\varepsilon(x_0)$ if for all $x \geq x_0$
  we have
  \[ E_\pi(x) \leq \varepsilon(x_0). \]
  -/)]
-/
def Eπ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ x ≤ admissible_bound A B C R x

def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε

def Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eπ.bound (ε x₀) x₀

def Eπ.vinogradovBound (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ ((3 : ℝ) / 5) / (log (log x)) ^ ((1 : ℝ) / 5))

def Eπ_star.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ admissible_bound A B C R x

def Eπ_star.bound (ε x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ ε

def Eπ_star.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eπ_star.bound (ε x₀) x₀

def Eπ_star.vinogradovBound (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ ((3 : ℝ) / 5) / (log (log x)) ^ ((1 : ℝ) / 5))

/- Upstream blueprint metadata (inert):
@[blueprint
  "admissible-bound-monotone"
  (title := "Admissible bound decreasing for large x")
  (statement := /--
  If $A,B,C,R > 0$ then the classical bound is monotone
  decreasing for $x \geq \exp( R (2B/C)^2 )$. -/)
  (proof := /-- Differentiate the bound and check the
  sign. -/)
  (latexEnv := "lemma")
  (discussion := 900)]
-/
lemma admissible_bound.mono
    (A B C R : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R) :
    AntitoneOn (admissible_bound A B C R)
      (Set.Ici (exp (R * (2 * B / C) ^ 2))) := by
  intro a ha b _ hab
  simp only [admissible_bound, mul_assoc]
  have hua : (2 * B / C) ^ 2 ≤ log a / R := by
    rw [le_div_iff₀ hR, mul_comm ((2 * B / C) ^ 2), ← log_exp (R * (2 * B / C) ^ 2)]
    exact log_le_log (exp_pos _) (Set.mem_Ici.mp ha)
  have huab : log a / R ≤ log b / R :=
    div_le_div_of_nonneg_right
      (log_le_log ((exp_pos _).trans_le (Set.mem_Ici.mp ha)) hab) hR.le
  have hua₀ : 0 < log a / R :=
    lt_of_lt_of_le (by positivity) hua
  apply mul_le_mul_of_nonneg_left _ hA.le
  rw [rpow_def_of_pos (hua₀.trans_le huab), rpow_def_of_pos hua₀,
    ← exp_add, ← exp_add, exp_le_exp]
  let sa := (log a / R) ^ ((1 : ℝ) / 2)
  let sb := (log b / R) ^ ((1 : ℝ) / 2)
  rw [show log (log b / R) = 2 * log sb from by
      grind [log_rpow (hua₀.trans_le huab) ((1 : ℝ) / 2)],
    show log (log a / R) = 2 * log sa from by
      grind [log_rpow hua₀ ((1 : ℝ) / 2)]]
  have hsab : sa ≤ sb :=
    rpow_le_rpow (le_trans (by positivity) hua) huab (by positivity)
  have : 2 * B / C ≤ sa := by
    rw [show (2 * B / C : ℝ) = ((2 * B / C) ^ 2) ^ ((1 : ℝ) / 2) from by
      rw [← rpow_natCast _ 2, ← rpow_mul (by positivity)]
      norm_num [rpow_one]]
    exact rpow_le_rpow (by positivity) hua (by positivity)
  suffices h : AntitoneOn (fun t ↦ 2 * B * log t - C * t) (Set.Ici (2 * B / C)) by
    grind [h (Set.mem_Ici.mpr this) (Set.mem_Ici.mpr (this.trans hsab)) hsab]
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact ((continuousOn_const.mul (continuousOn_log.mono fun t ht ↦
        ne_of_gt ((div_pos (by positivity) hC).trans_le ht))).sub
      (continuousOn_const.mul continuousOn_id))
  · intro t ht
    rw [interior_Ici] at ht
    exact (((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
      ((hasDerivAt_id t).const_mul C)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hdt : HasDerivAt (fun t ↦ 2 * B * log t - C * t) (2 * B * t⁻¹ - C * 1) t :=
      ((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
        ((hasDerivAt_id t).const_mul C)
    rw [hdt.deriv, mul_one, sub_nonpos, ← div_eq_mul_inv,
      div_le_iff₀ ((div_pos (by positivity) hC).trans ht)]
    linarith [(div_lt_iff₀ hC).mp ht, mul_comm C t]

/- Upstream blueprint metadata (inert):
@[blueprint
  "classical-to-numeric"
  (title := "Classic bound implies numerical bound")
  (statement := /--
  A classical bound for $x \geq x_0$ implies a numerical
  bound for $x \geq \max(x_0,
  \exp( R (2B/C)^2  ))$. -/)
  (proof := /-- Immediate from previous lemma -/)
  (latexEnv := "lemma")
  (discussion := 901)]
-/
lemma Eψ.classicalBound.to_numericalBound
    (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R)
    (hEψ : Eψ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
    Eψ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦
    le_trans (hEψ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
      (admissible_bound.mono A B C R hA hB hC hR
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)

/- Upstream blueprint metadata (inert):
@[blueprint "classical-to-numeric"]
-/
lemma Eθ.classicalBound.to_numericalBound
    (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R)
    (hEθ : Eθ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
    Eθ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦
    le_trans (hEθ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
      (admissible_bound.mono A B C R hA hB hC hR
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)

/- Upstream blueprint metadata (inert):
@[blueprint "classical-to-numeric"]
-/
lemma Eπ.classicalBound.to_numericalBound
    (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R)
    (hEπ : Eπ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
    Eπ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦
    le_trans (hEπ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
      (admissible_bound.mono A B C R hA hB hC hR
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)

end

/- Upstream: PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean, original lines 1–17.
Revision a5154676af9aa3095150ee410cdda80555aa0642.
See extraction manifest for metadata/import removal and excluded alternatives. -/
section
open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end

/- Upstream: PrimeNumberTheoremAnd/Wiener.lean, original lines 1–2462.
Revision a5154676af9aa3095150ee410cdda80555aa0642.
See extraction manifest for metadata/import removal and excluded alternatives. -/
section
set_option linter.style.header false

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

/--
The Fourier transform of an absolutely integrable function $\psi: \R \to \C$ is defined by the
formula $$ \hat \psi(u) := \int_\R e(-tu) \psi(t)\ dt$$ where $e(\theta) := e^{2\pi i \theta}$.

Let $f: \N \to \C$ be an arithmetic function such that $\sum_{n=1}^\infty \frac{|f(n)|}{n^\sigma} <
\infty$ for all $\sigma>1$.  Then the Dirichlet series
$$ F(s) := \sum_{n=1}^\infty \frac{f(n)}{n^s}$$
is absolutely convergent for $\sigma>1$.
-/

noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s

lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

-- TODO - add to mathlib
attribute [fun_prop] Real.continuous_fourierChar

lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop

lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]

lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group

set_option backward.isDefEq.respectTransparency false in
/- Upstream blueprint metadata (inert):
@[blueprint "first-fourier"
  (title := "first-fourier")
  (statement := /--
  If $\psi: \R \to \C$ is integrable and $x > 0$, then for any $\sigma>1$
  $$ \sum_{n=1}^\infty \frac{f(n)}{n^\sigma} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) =
  \int_\R F(\sigma + it) \psi(t) x^{it}\ dt.$$
  -/)
  (proof := /--
    By the definition of the Fourier transform, the left-hand side expands as
  $$ \sum_{n=1}^\infty \int_\R \frac{f(n)}{n^\sigma} \psi(t) e( - \frac{1}{2\pi} t \log
  \frac{n}{x})\ dt$$
  while the right-hand side expands as
  $$ \int_\R \sum_{n=1}^\infty \frac{f(n)}{n^{\sigma+it}} \psi(t) x^{it}\ dt.$$
  Since
  $$\frac{f(n)}{n^\sigma} \psi(t) e( - \frac{1}{2\pi} t \log \frac{n}{x}) =
  \frac{f(n)}{n^{\sigma+it}} \psi(t) x^{it}$$
  the claim then follows from Fubini's theorem.
  -/)
  (latexEnv := "lemma")]
-/
lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by

  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp



@[continuity]
lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩

attribute [fun_prop] measurable_coe_nnreal_ennreal

lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    -- TODO: find out why fun_prop does not play well with Multiplicative.ofAdd
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one,
      Multiplicative.ofAdd, Equiv.coe_fn_mk, smul_eq_mul]
    fun_prop
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2

lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

set_option backward.isDefEq.respectTransparency false in
/- Upstream blueprint metadata (inert):
@[blueprint "second-fourier"
  (title := "second-fourier")
  (statement := /--
  If $\psi: \R \to \C$ is absolutely integrable and $x > 0$, then for any $\sigma>1$
  $$ \int_{-\log x}^\infty e^{-u(\sigma-1)} \hat \psi(\frac{u}{2\pi})\ du =
  x^{\sigma - 1} \int_\R \frac{1}{\sigma+it-1} \psi(t) x^{it}\ dt.$$
  -/)
  (proof := /--
  The left-hand side expands as
  $$ \int_{-\log x}^\infty \int_\R e^{-u(\sigma-1)} \psi(t) e(-\frac{tu}{2\pi})\ dt\ du$$
  so by Fubini's theorem it suffices to verify the identity
  \begin{align*}
  \int_{-\log x}^\infty e^{-u(\sigma-1)} e(-\frac{tu}{2\pi})\ du
  &= \int_{-\log x}^\infty e^{(it - \sigma + 1)u}\ du \\
  &= \frac{1}{it - \sigma + 1} e^{(it - \sigma + 1)u}\ \Big|_{-\log x}^\infty \\
  &= x^{\sigma - 1} \frac{1}{\sigma+it-1} x^{it}
  \end{align*}
  -/)
  (latexEnv := "lemma")]
-/
lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by

  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  dsimp [Real.fourierChar, Circle.exp]

  simp_rw [mul_smul_comm, ← smul_mul_assoc, integral_mul_const]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  congr 1
  conv =>
    lhs
    enter [2]
    ext a
    rw [AddChar.coe_mk, Submonoid.mk_smul, smul_eq_mul]
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I + -↑u * (↑σ' - 1) = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num)]
    _ = _ := by ring
  simp_rw [this]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx

/--
Now let $A \in \C$, and suppose that there is a continuous function $G(s)$ defined on
$\mathrm{Re} s \geq 1$ such that $G(s) = F(s) - \frac{A}{s-1}$ whenever $\mathrm{Re} s > 1$.
We also make the Chebyshev-type hypothesis
\begin{equation}\label{cheby}
\sum_{n \leq x} |f(n)| \ll x
\end{equation}
for all $x \geq 1$ (this hypothesis is not strictly necessary, but simplifies the arguments and
can be obtained fairly easily in applications).
-/

lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)

/- Upstream blueprint metadata (inert):
@[blueprint "prelim-decay"
  (title := "Preliminary decay bound I")
  (statement := /--
  If $\psi:\R \to \C$ is absolutely integrable then $$ |\hat \psi(u)| \leq \| \psi \|_1 $$
  for all $u \in \R$. where $C$ is an absolute constant.
  -/)
  (proof := /-- Immediate from the triangle inequality. -/)
  (latexEnv := "lemma")
  (discussion := 561)]
-/
theorem prelim_decay (ψ : ℝ → ℂ) (u : ℝ) : ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ ∫ t, ‖ψ t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm ..

/- Upstream blueprint metadata (inert):
@[blueprint "prelim-decay-2"
  (title := "Preliminary decay bound II")
  (statement := /--
If $\psi:\R \to \C$ is absolutely integrable and of bounded variation, then
$$ |\hat \psi(u)| \leq \| \psi \|_{TV} / 2\pi |u| $$
for all non-zero $u \in \R$.
  -/)
  (proof := /-- By Lebesgue--Stiejtes integration by parts we have
$$ 2\pi i u \hat \psi(u) = \int _\R e(-tu) d\psi(t)$$
and the claim then follows from the triangle inequality. -/)
  (latexEnv := "lemma")
  (discussion := 562)]
-/
noncomputable def AbsolutelyContinuous (f : ℝ → ℂ) : Prop := (∀ᵐ x, DifferentiableAt ℝ f x) ∧
  ∀ a b : ℝ, f b - f a = ∫ t in a..b, deriv f t

/- Upstream blueprint metadata (inert):
@[blueprint "prelim-decay-3"
  (title := "Preliminary decay bound III")
  (statement := /--
If $\psi:\R \to \C$ is absolutely integrable, absolutely continuous, and $\psi'$ is of bounded
variation, then
$$ |\hat \psi(u)| \leq \| \psi' \|_{TV} / (2\pi |u|)^2$$
for all non-zero $u \in \R$.
  -/)
  (proof := /-- Should follow from previous lemma. -/)
  (proofUses := ["prelim-decay-2"])
  (latexEnv := "lemma")
  (discussion := 563)]
-/
/- Upstream blueprint metadata (inert):
@[blueprint "decay-alt"
  (title := "Decay bound, alternate form")
  (statement := /--
If $\psi:\R \to \C$ is absolutely
integrable, absolutely continuous, and $\psi'$ is of bounded variation, then
$$ |\hat \psi(u)| \leq ( \|\psi\|_1 + \| \psi' \|_{TV} / (2\pi)^2) / (1+|u|^2)$$
for all $u \in \R$.  -/)
  (proof := /-- Should follow from previous lemmas. -/)
  (proofUses := ["prelim-decay", "prelim-decay-3", "decay"])
  (latexEnv := "lemma")
  (discussion := 564)]
-/
lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm

lemma decay_bounds_aux {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∀ t, ‖f t‖ ≤ A * (1 + t ^ 2)⁻¹) :
    ∫ t, ‖f t‖ ≤ π * A := by
  have l1 : Integrable (fun x ↦ A * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul A
  simp_rw [← integral_univ_inv_one_add_sq, mul_comm, ← integral_const_mul]
  exact integral_mono (l1.mono' hf (Eventually.of_forall h)).norm l1 h

theorem decay_bounds_W21 (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  have l0 : 1 * (4 * π)⁻¹ * A = (4 * π ^ 2)⁻¹ * (π * A) := by field_simp
  have l1 : ∫ (v : ℝ), ‖f v‖ ≤ π * A := by
    apply decay_bounds_aux f.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA
  have l2 : ∫ (v : ℝ), ‖deriv (deriv f) v‖ ≤ π * A := by
    apply decay_bounds_aux f.deriv.deriv.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA'
  apply decay_bounds_key f u |>.trans
  change W21.norm _ * _ ≤ _
  simp_rw [W21.norm, div_eq_mul_inv, add_mul, l0] ; gcongr

/- Upstream blueprint metadata (inert):
@[blueprint
  "decay"
  (title := "Decay bounds")
  (statement := /--
    If $\psi:\R \to \C$ is $C^2$ and obeys the bounds
    $$ |\psi(t)|, |\psi''(t)| \leq A / (1 + |t|^2)$$
    for all $t \in \R$, then
  $$ |\hat \psi(u)| \leq C A / (1+|u|^2)$$
  for all $u \in \R$, where $C$ is an absolute constant.
  -/)
  (proof := /--
   From two integration by parts we obtain the identity
  $$ (1+u^2) \hat \psi(u) = \int_{\bf R} (\psi(t) - \frac{u}{4\pi^2} \psi''(t)) e(-tu)\ dt.$$
  Now apply the triangle inequality and the identity $\int_{\bf R} \frac{dt}{1+t^2}\ dt = \pi$ to
  obtain the claim with $C = \pi + 1 / 4 \pi$.
  -/)
  (latexEnv := "lemma")]
-/
lemma decay_bounds (ψ : CS 2 ℂ) (hA : ∀ t, ‖ψ t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv^[2] ψ t‖ ≤ A / (1 + t ^ 2)) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  exact decay_bounds_W21 ψ hA hA' u

lemma decay_bounds_cor_aux (ψ : CS 2 ℂ) : ∃ C : ℝ, ∀ u, ‖ψ u‖ ≤ C / (1 + u ^ 2) := by
  have l1 : HasCompactSupport (fun u : ℝ => ((1 + u ^ 2) : ℝ) * ψ u) := by exact ψ.h2.mul_left
  have := ψ.h1.continuous
  obtain ⟨C, hC⟩ := l1.exists_bound_of_continuous (by fun_prop)
  refine ⟨C, fun u => ?_⟩
  specialize hC u
  simp only [norm_mul, Complex.norm_real, norm_of_nonneg (one_add_sq_pos u).le] at hC
  rwa [le_div_iff₀' (one_add_sq_pos _)]

lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩

set_option backward.isDefEq.respectTransparency false in
@[continuity, fun_prop] lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf

lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa using! (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    apply Continuous.aestronglyMeasurable ; fun_prop
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)





lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

-- Here compact support is used but perhaps it is not necessary
set_option backward.isDefEq.respectTransparency false in
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- `nnabla` is the backward difference `u n - u (n+1)`; kept alongside `nabla`
   for summation-by-parts identities that prefer that orientation. -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

lemma nnabla_cast (u : ℝ → E) [Sub E] : nnabla u ∘ ((↑) : ℕ → ℝ) = nnabla (u ∘ (↑)) := by
  ext n ; simp [nnabla]

end nabla

lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl

lemma Finset.sum_shift_front' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = (fun _ => u 0) + cumsum (shift u) := by
  ext n ; apply Finset.sum_shift_front

lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma Finset.sum_shift_back' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = cumsum u + u := by
  ext n ; apply Finset.sum_shift_back

lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel

lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  simpa using! summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply,
    eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩

lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]

lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using! Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h

lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]

lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp

lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

lemma isBigO_pow_pow_of_le {m n : ℕ} (h : m ≤ n) :
    (fun x : ℝ => x ^ m) =O[atTop] (fun x : ℝ => x ^ n) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with x l1
  simpa [abs_eq_self.mpr (zero_le_one.trans l1)] using pow_le_pow_right₀ l1 h

lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)

lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert! (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  ext x
  simp only [Function.comp_apply]
  congr
  field_simp
  simp

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp

lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)

lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring

lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le

lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1

lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring

lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by

  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by simpa using! (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

lemma Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)

/-- Should this be a gcongr lemma? -/
@[local gcongr]
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by

  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _

  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]

  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    gcongr

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using! (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

  apply EventuallyEq.trans_isBigO l1

  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp

lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx

def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n

def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f

lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n

lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by

  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO

  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a] using! IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]

  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp

theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by simpa using! Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le

theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict

theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity

theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by

  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh

  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖

  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]

  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])

/- Upstream blueprint metadata (inert):
@[blueprint
  "limiting"
  (title := "Limiting Fourier identity")
  (statement := /--
  If $\psi: \R \to \C$ is $C^2$ and compactly supported and $x \geq 1$, then
  $$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} )
    - A \int_{-\log x}^\infty \hat \psi(\frac{u}{2\pi})\ du
    = \int_\R G(1+it) \psi(t) x^{it}\ dt.$$
  -/)
  (proof := /--
  By Lemma \ref{first-fourier} and Lemma \ref{second-fourier}, we know that for any $\sigma>1$,
  we have
  $$ \sum_{n=1}^\infty \frac{f(n)}{n^\sigma} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} )
    - A x^{1-\sigma} \int_{-\log x}^\infty e^{-u(\sigma-1)} \hat \psi(\frac{u}{2\pi})\ du
    = \int_\R G(\sigma+it) \psi(t) x^{it}\ dt.$$
  Now take limits as $\sigma \to 1$ using dominated convergence together with \eqref{cheby}
  and Lemma \ref{decay} to obtain the result.
  -/)
  (latexEnv := "lemma")]
-/
lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using! Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)




set_option backward.isDefEq.respectTransparency false in
lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by

  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf

  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))

  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext ; congr ; ext
    simp only [← ofReal_mul, mul_comm (f _), fourierChar, Circle.exp, ContinuousMap.coe_mk,
      innerₗ_apply_apply, RCLike.inner_apply, conj_trivial, AddChar.coe_mk, mul_neg, ofReal_neg,
      neg_mul]
    congr
    rw [← neg_mul] ; congr ; norm_cast ; field_simp
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)

/- Upstream blueprint metadata (inert):
@[blueprint
  "limiting-cor"
  (title := "Corollary of limiting identity")
  (statement := /--
  With the hypotheses as above, we have
  $$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} )
    = A \int_{-\infty}^\infty \hat \psi(\frac{u}{2\pi})\ du + o(1)$$
  as $x \to \infty$.
  -/)
  (proof := /--
  Immediate from the Riemann-Lebesgue lemma, and also noting that
  $\int_{-\infty}^{-\log x} \hat \psi(\frac{u}{2\pi})\ du = o(1)$.
  -/)
  (latexEnv := "corollary")]
-/
lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm





/- Upstream blueprint metadata (inert):
@[blueprint
  "smooth-ury"
  (title := "Smooth Urysohn lemma")
  (statement := /--
  If $I$ is a closed interval contained in an open interval $J$, then there exists a smooth
  function $\Psi: \R \to \R$ with $1_I \leq \Psi \leq 1_J$.
  -/)
  (proof := /--
  A standard analysis lemma, which can be proven by convolving $1_K$ with a smooth approximation
  to the identity for some interval $K$ between $I$ and $J$. Note that we have
  ``SmoothBumpFunction''s on smooth manifolds in Mathlib, so this shouldn't be too hard...
  -/)
  (latexEnv := "lemma")]
-/
lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩



noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

lemma one_div_sub_one (n : ℕ) : 1 / (↑(n - 1) : ℝ) ≤ 2 / n := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => { norm_cast ; rw [div_le_div_iff₀] <;> simp [mul_add] <;> linarith }

lemma quadratic_pos (a b c x : ℝ) (ha : 0 < a) (hΔ : discrim a b c < 0) :
    0 < a * x ^ 2 + b * x + c := by
  have l1 : a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - discrim a b c / (4 * a) := by
    simp only [discrim]; field_simp; ring
  have l2 : 0 < - discrim a b c := by linarith
  rw [l1, sub_eq_add_neg, ← neg_div] ; positivity

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

noncomputable def pp' (a x : ℝ) : ℝ := a ^ 2 * (2 * (x + 1))

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

lemma pp_deriv (a x : ℝ) : HasDerivAt (pp a) (pp' a x) x := by
  unfold pp pp'
  simpa using hasDerivAt_id x |>.add_const 1 |>.pow 2 |>.const_mul _

lemma pp_deriv_eq (a : ℝ) : deriv (pp a) = pp' a := by
  ext x ; exact pp_deriv a x |>.deriv

lemma pp'_deriv (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
  simpa using! hasDerivAt_id x |>.add_const 1 |>.const_mul 2 |>.const_mul (a ^ 2)

lemma pp'_deriv_eq (a : ℝ) : deriv (pp' a) = fun _ => a ^ 2 * 2 := by
  ext x ; exact pp'_deriv a x |>.deriv

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_le (a t : ℝ) (ht : 0 ≤ t) : |hh a t| ≤ t⁻¹ := by
  by_cases h0 : t = 0
  · simp [hh, h0]
  replace ht : 0 < t := lt_of_le_of_ne ht (by tauto)
  unfold hh
  rw [abs_inv, inv_le_inv₀ (by positivity) ht, abs_mul, abs_eq_self.mpr ht.le]
  convert_to! t * 1 ≤ _
  · simp
  apply mul_le_mul le_rfl ?_ zero_le_one ht.le
  rw [abs_eq_self.mpr (by positivity)]
  simp only [le_add_iff_nonneg_right]
  positivity

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    convert! l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert! (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert! l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp

lemma gg_l1 {x : ℝ} (hx : 0 < x) (n : ℕ) : |gg x n| ≤ 1 / n := by
  simp only [gg_of_hh hx.ne.symm, one_div, mul_inv_rev, abs_mul]
  apply mul_le_mul le_rfl (hh_le _ _ (by positivity)) (by positivity) (by positivity) |>.trans
    (le_of_eq ?_)
  simp [abs_inv, abs_eq_self.mpr hx.le] ; field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to! 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi

lemma sum_telescopic (a : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 := by
  apply Finset.sum_range_sub

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa using! hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg' hf

  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    convert_to! ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) ≤ _
    · congr ; ext i ; simp ; ring
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    apply le_of_eq ; ring_nf

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring

lemma cancel_main {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) (hn : 2 ≤ n) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  convert! cancel_aux' hf hg hf' hg' n using 1
  match n with
  | n + 2 => simp only [cumsum_succ] ; push_cast ; ring

lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 => convert! cancel_aux' hf hg hf' hg' (n + 2) using 1 ; simp [cumsum_succ] ; ring

theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← sdiff_eq_compl_inter]
    simp [ae, this]

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert! _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert! this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert! (l1 x hx).const_mul (a * c / b) using 1
    simp only [g']
    field_simp
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring

lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i

  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1

  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))

  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv

  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self

  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to! ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp

  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  convert_to! ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa using! this.mono_set Ioi_subset_Ici_self

lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx

lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx

variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
    (norm_nonneg (f i / i)) using 1
  · simp
  · change _ = _ * (W21.norm ψ * _)
    simp only [W21.norm, mul_inv_rev, one_div, Complex.norm_div, RCLike.norm_natCast]
    ring

lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))

lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by

  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  simpa only [← Summable.tsum_const_smul _ l5] using!
    Summable.tsum_mono l1 (by simpa using l5.const_smul (W21.norm ψ)) l6

lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by

  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)

lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by

  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · apply Continuous.aestronglyMeasurable ; fun_prop
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl

lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by

  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring


set_option backward.isDefEq.respectTransparency false in
lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  -- Shorter notation for clarity
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  -- Build the truncation
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  -- Choose the truncation radius
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

  -- Apply the compact support case
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  -- Control the tail term
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert! (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp

  -- Conclude the proof
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]

  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using! this

  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict

  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)

/- Upstream blueprint metadata (inert):
@[blueprint
  "schwarz-id"
  (title := "Limiting identity for Schwartz functions")
  (statement := /--
  The previous corollary also holds for functions $\psi$ that are assumed to be in the Schwartz
  class, as opposed to being $C^2$ and compactly supported.
  -/)
  (proof := /--
  For any $R>1$, one can use a smooth cutoff function (provided by Lemma \ref{smooth-ury} to write
  $\psi = \psi_{\leq R} + \psi_{>R}$, where $\psi_{\leq R}$ is $C^2$ (in fact smooth) and compactly
  supported (on $[-R,R]$), and $\psi_{>R}$ obeys bounds of the form
  $$ |\psi_{>R}(t)|, |\psi''_{>R}(t)| \ll R^{-1} / (1 + |t|^2) $$
  where the implied constants depend on $\psi$.  By Lemma \ref{decay} we then have
  $$ \hat \psi_{>R}(u) \ll R^{-1} / (1+|u|^2).$$
  Using this and \eqref{cheby} one can show that
  $$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi_{>R}( \frac{1}{2\pi} \log \frac{n}{x} ),
    A \int_{-\infty}^\infty \hat \psi_{>R} (\frac{u}{2\pi})\ du \ll R^{-1} $$
  (with implied constants also depending on $A$), while from Lemma \ref{limiting-cor} one has
  $$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi_{\leq R}( \frac{1}{2\pi} \log \frac{n}{x} )
    = A \int_{-\infty}^\infty \hat \psi_{\leq R} (\frac{u}{2\pi})\ du + o(1).$$
  Combining the two estimates and letting $R$ be large, we obtain the claim.
  -/)
  (latexEnv := "lemma")]
-/
lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'





-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead

/- Upstream blueprint metadata (inert):
@[blueprint
  "bij"
  (title := "Bijectivity of Fourier transform")
  (statement := /--
  The Fourier transform is a bijection on the Schwartz class. [Note: only surjectivity is
  actually used.]
  -/)
  (proof := /--
  This is a standard result in Fourier analysis.
  It can be proved here by appealing to Mellin inversion, Theorem \ref{MellinInversion}.
  In particular, given $f$ in the Schwartz class, let
  $F : \R_+ \to \C : x \mapsto f(\log x)$ be a function in the ``Mellin space''; then the
  Mellin transform of $F$ on the imaginary axis $s=it$ is the Fourier transform of $f$.
  The Mellin inversion theorem gives Fourier inversion.
  -/)
  (latexEnv := "lemma")]
-/
lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f




noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

set_option backward.isDefEq.respectTransparency false in
lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]



/- Upstream blueprint metadata (inert):
@[blueprint
  "WienerIkeharaSmooth"
  (title := "Smoothed Wiener-Ikehara")
  (statement := /--
    If $\Psi: (0,\infty) \to \C$ is smooth and compactly supported away from the origin, then,
  $$ \sum_{n=1}^\infty f(n) \Psi( \frac{n}{x} ) = A x \int_0^\infty \Psi(y)\ dy + o(x)$$
  as $x \to \infty$.
  -/)
  (proof := /--
  By Lemma \ref{bij}, we can write
  $$ y \Psi(y) = \hat \psi( \frac{1}{2\pi} \log y )$$
  for all $y>0$ and some Schwartz function $\psi$.  Making this substitution, the claim is then
  equivalent after standard manipulations to
  $$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} )
    = A \int_{-\infty}^\infty \hat \psi(\frac{u}{2\pi})\ du + o(1)$$
  and the claim follows from Lemma \ref{schwarz-id}.
  -/)
  (latexEnv := "corollary")]
-/
lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)

  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]

  have key := limiting_cor_schwartz g hf hcheby hG hG'

  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp

  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx

  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus

  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4



lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

@[norm_cast]
theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by

  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key

lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by

  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by

  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)

lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith

lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx

lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]

theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume ((Function.support fun y ↦ ψ y) ∩ Ioi 0) := by convert! volume.mono r4 ; norm_num
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using! zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this

/--
Now we add the hypothesis that $f(n) \geq 0$ for all $n$.

-/

/- Upstream blueprint metadata (inert):
@[blueprint
  (title := "Wiener-Ikehara in an interval")
  (statement := /--
  For any closed interval $I \subset (0,+\infty)$, we have
  $$ \sum_{n=1}^\infty f(n) 1_I( \frac{n}{x} ) = A x |I|  + o(x).$$
  -/)
  (proof := /-- Use Lemma \ref{smooth-ury} to bound $1_I$ above and below by smooth compactly supported functions whose integral is close to the measure of $|I|$, and use the non-negativity of $f$. -/)
  (latexEnv := "proposition")]
-/
lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by

  -- Take care of the trivial case `a = b`
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  -- Notation to make the proof more readable
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  -- A few facts about the indicator function of `Icc a b`
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

  -- Bound from above by a smooth function
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Bound from below by a smooth function
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Combine the two bounds
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith



lemma le_floor_mul_iff (hb : 0 ≤ b) (hx : 0 < x) : n ≤ ⌊b * x⌋₊ ↔ n / x ≤ b := by
  rw [div_le_iff₀ hx, Nat.le_floor_iff] ; positivity

lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Icc_iff_div (hb : 0 ≤ b) (hx : 0 < x) : n ∈ Finset.Icc ⌈a * x⌉₊ ⌊b * x⌋₊ ↔ n / x ∈ Icc a b := by
  rw [Finset.mem_Icc, mem_Icc, ceil_mul_le_iff hx, le_floor_mul_iff hb hx]

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]

lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]

lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]

lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop

-- TODO with `Ico`



/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/

lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N

lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]

lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [← S_sub_S h2.2] using! l2.trans_lt h1

/- Upstream blueprint metadata (inert):
@[blueprint "WienerIkehara"
  (title := "Wiener-Ikehara Theorem (1)")
  (statement := /--
    We have
  $$ \sum_{n\leq x} f(n) = A x + o(x).$$
  -/)
  (proof := /-- Apply the preceding proposition with $I = [\varepsilon,1]$ and then send
  $\varepsilon$ to zero (using \eqref{cheby} to control the error). -/)
  (latexEnv := "corollary")]
-/
theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  convert_to Tendsto (S f 0) atTop (𝓝 A) ; · ext N ; simp [S, cumsum]
  apply (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using! WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
  · have : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (this.const_sub 1).const_mul A

theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith

/--
\section{Weak PNT}

-/

-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)

/- Upstream blueprint metadata (inert):
@[blueprint
  (title := "WeakPNT")
  (statement := /--
    We have
  $$ \sum_{n \leq x} \Lambda(n) = x + o(x).$$
  -/)
  (proof := /-- Already done by Stoll, assuming Wiener-Ikehara. -/)]
-/
theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_setOf_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

end

/- Upstream: PrimeNumberTheoremAnd/Consequences.lean, original lines 1–1918.
Revision a5154676af9aa3095150ee410cdda80555aa0642.
See extraction manifest for metadata/import removal and excluded alternatives. -/
section
open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma Set.Ico_subset_Ico_of_Icc_subset_Icc {a b c d : ℝ} (h : Set.Icc a b ⊆ Set.Icc c d) :
    Set.Ico a b ⊆ Set.Ico c d := by
  intro z hz
  have hz' := Set.Ico_subset_Icc_self.trans h hz
  have hcd : c ≤ d := by
    contrapose! hz'
    rw [Icc_eq_empty_of_lt hz']
    exact notMem_empty _
  simp only [mem_Ico, mem_Icc] at *
  refine ⟨hz'.1, hz'.2.eq_or_lt.resolve_left ?_⟩
  rintro rfl
  apply hz.2.not_ge
  have := h <| right_mem_Icc.mpr (hz.1.trans hz.2.le)
  simp only [mem_Icc] at this
  exact this.2

lemma th43_b (x : ℝ) (hx : 2 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ =
      θ x / log x + ∫ t in Set.Icc 2 x, θ t / (t * (Real.log t) ^ 2) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx

/- Upstream blueprint metadata (inert):
@[blueprint
  (title := "finsum-range-eq-sum-range")
  (statement := /--
   For any arithmetic function $f$ and real number $x$, one has
  $$ \sum_{n \leq x} f(n) = \sum_{n \leq ⌊x⌋_+} f(n)$$
  and
  $$ \sum_{n < x} f(n) = \sum_{n < ⌈x⌉_+} f(n).$$
  -/)
  (proof := /-- Straightforward. -/)
  (latexEnv := "lemma")]
-/
lemma finsum_range_eq_sum_range {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n ∈ range ⌈x⌉₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intros
  simp only [mem_range]
  exact Iff.symm Nat.lt_ceil

lemma finsum_range_eq_sum_range' {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R}
    (x : ℝ) : ∑ᶠ (n : ℕ) (_ : n ≤ x), f n = ∑ n ∈ Iic ⌊x⌋₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intro n h
  simp only [mem_Iic]
  exact Iff.symm <| Nat.le_floor_iff'
    fun (hc : n = 0) ↦ (h : f n ≠ 0) <| (congrArg f hc).trans ArithmeticFunction.map_zero


lemma log2_pos : 0 < log 2 := by
  rw [Real.log_pos_iff zero_le_two]
  exact one_lt_two


/-- If u ~ v and w-u = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (w - u) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← add_sub_cancel u w]
  exact add_isLittleO huv hwu

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_setOf_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this

/-- `(⌊x⌋₊ + 1) / x → 1` as `x → ∞`. -/
lemma tendsto_floor_add_one_div_self : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ + 1 : ℝ) / x) atTop (nhds 1) := by
  have h := Asymptotics.isEquivalent_nat_floor (R := ℝ)
  have h' : IsEquivalent atTop (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) + 1) _root_.id :=
    h.add_isLittleO (isLittleO_const_id_atTop 1)
  rwa [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx a; simp only [_root_.id] at a; linarith)] at h'

/-- `x =Θ x / c` for nonzero constant `c`. -/
lemma isTheta_self_div_const {c : ℝ} (hc : c ≠ 0) : (fun x : ℝ ↦ x) =Θ[atTop] fun x ↦ x / c := by
  have : (fun x : ℝ ↦ x / c) = fun x ↦ c⁻¹ * x := by ext x; ring
  exact this ▸ (isTheta_const_mul_left (inv_ne_zero hc)).mpr (isTheta_refl ..) |>.symm

/-- Filtered sum over `Iic n` equals filtered sum over `Icc 1 n` for primes. -/
lemma filter_prime_Iic_eq_Icc (n : ℕ) : filter Prime (Iic n) = filter Prime (Icc 1 n) := by
  ext p; simp only [mem_filter, mem_Iic, mem_Icc, and_congr_left_iff]
  exact fun hp ↦ ⟨fun h ↦ ⟨hp.one_lt.le, h⟩, fun ⟨_, h⟩ ↦ h⟩

/-- `Icc 0 n = insert 0 (Icc 1 n)` -/
lemma Icc_zero_eq_insert (n : ℕ) : Icc 0 n = insert 0 (Icc 1 n) := by
  ext m; simp [mem_Icc]; omega

/- Upstream blueprint metadata (inert):
@[blueprint "chebyshev-asymptotic"
  (title := "chebyshev-asymptotic")
  (statement := /--
  One has
  $$ \sum_{p \leq x} \log p = x + o(x).$$
  -/)
  (proof := /--
  From the prime number theorem we already have
  $$ \sum_{n \leq x} \Lambda(n) = x + o(x)$$
  so it suffices to show that
  $$ \sum_{j \geq 2} \sum_{p^j \leq x} \log p = o(x).$$
  Only the terms with $j \leq \log x / \log 2$ contribute, and each $j$ contributes at most
  $\sqrt{x} \log x$ to the sum, so the left-hand side is $O( \sqrt{x} \log^2 x ) = o(x)$ as
  required.
  -/)]
-/
theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using! isLittleO_sqrt_mul_log.const_mul_left 2

theorem chebyshev_asymptotic_finsum :
    (fun x ↦ ∑ᶠ (p : ℕ) (_ : p ≤ x) (_ : Nat.Prime p), log p) ~[atTop] fun x ↦ x := by
  have hReal :
      (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) ~[atTop]
        fun x ↦ x := by
    have h x : ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ) = θ x := by
      rw [Chebyshev.theta_eq_sum_Icc]
      have hfin : {p : ℕ | (p : ℝ) ≤ x ∧ p.Prime}.Finite :=
        (Iic ⌊x⌋₊).finite_toSet.subset fun p ⟨hpx, _⟩ ↦ mem_Iic.mpr (Nat.le_floor hpx)
      calc ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)
          = ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x ∧ p.Prime), log (p : ℝ) :=
            finsum_congr fun p ↦ by by_cases hp : p.Prime <;> simp [hp]
        _ = ∑ p ∈ hfin.toFinset, log (p : ℝ) := finsum_mem_eq_finite_toFinset_sum _ hfin
        _ = _ := sum_congr (by ext p; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq,
            mem_filter, mem_Icc, and_congr_left_iff]; exact fun hp ↦
            ⟨fun hpx ↦ ⟨Nat.zero_le _, Nat.le_floor hpx⟩, fun ⟨_, hpn⟩ ↦
              (le_or_gt 0 x).elim
                (fun hx ↦ (Nat.floor_le hx).trans' (Nat.cast_le.mpr hpn)) fun hx ↦
                absurd (Nat.le_zero.mp (Nat.floor_eq_zero.mpr (hx.trans_le zero_le_one) ▸ hpn))
                  hp.ne_zero⟩) (fun _ _ ↦ rfl)
    have heq :
        (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) =ᶠ[atTop] θ :=
      Filter.Eventually.of_forall h
    exact chebyshev_asymptotic.congr_left heq.symm
  simp only [IsEquivalent,
    show (fun n : ℕ ↦ ∑ᶠ (p : ℕ) (_ : p ≤ n) (_ : p.Prime), log (p : ℝ)) =
      (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) ∘ Nat.cast
    from funext fun _ ↦ finsum_congr fun _ ↦ by simp]
  exact hReal.isLittleO.comp_tendsto tendsto_natCast_atTop_atTop

theorem chebyshev_asymptotic' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun t ↦ ε * t)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ (x : ℝ), θ x = x + f x := by
  have H := chebyshev_asymptotic
  rw [IsEquivalent, isLittleO_iff] at H
  let f := (fun x ↦ θ x - x)
  have integrable (x : ℝ) (hx : 2 ≤ x) : IntegrableOn f (Set.Icc 2 x) := by
    rw [IntegrableOn]
    refine Integrable.sub ?_ (ContinuousOn.integrableOn_Icc (continuousOn_id' _))
    refine Chebyshev.integrableOn_theta_div_id_mul_log_sq x |>.mul_continuousOn (g' := fun t => t * log t ^ 2)
      (ContinuousOn.mul (continuousOn_id' _) (ContinuousOn.pow (continuousOn_log |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) 2)) isCompact_Icc |>.congr_fun_ae ?_
    simp only [measurableSet_Icc, ae_restrict_eq, EventuallyEq, eventually_inf_principal]
    refine .of_forall fun t ⟨ht1, _⟩ => ?_
    rw [div_mul_cancel₀]
    simpa only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      log_eq_zero, or_self_left, not_or] using ⟨by linarith, by linarith, by linarith⟩
  refine ⟨f, fun ε hε ↦ ?_, integrable, ?_⟩
  · rw [isLittleO_iff]
    intro c hc
    specialize @H (c * ε) (mul_pos hc hε)
    simp only [Pi.sub_apply, norm_eq_abs, mul_assoc, eventually_atTop, norm_mul,
      abs_of_pos hε, f] at H ⊢
    exact H
  refine fun r => by simp [f]

theorem chebyshev_asymptotic'' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun _ ↦ ε)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ x > (0 : ℝ), θ x = x + x * (f x) := by
  obtain ⟨f, hf1, inte, hf2⟩ := chebyshev_asymptotic'
  refine ⟨fun t => f t / t, fun ε hε ↦ ?_, ?_, ?_⟩
  · simp only [isLittleO_iff, norm_eq_abs, norm_mul, eventually_atTop,
      norm_div] at hf1 ⊢
    intro r hr
    replace hf1 := hf1 ε hε
    obtain ⟨N, hN⟩ := hf1 hr
    use |N| + 1
    intro x hx
    have hx' : |N| + 1 ≤ |x| := by rwa [abs_of_nonneg (a := x) (le_trans (by positivity) hx)]
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hx'), mul_assoc]
    exact hN x (le_trans (le_trans (le_abs_self N) (by linarith)) hx)

  · intro x hx
    refine inte x hx |>.mul_continuousOn (g' := fun t : ℝ => t⁻¹)
      (continuousOn_inv₀ |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) isCompact_Icc |>.congr_fun_ae <| .of_forall <| by simp [div_eq_mul_inv]
  intro x hx
  rw [hf2, mul_div_cancel₀]
  linarith

-- one could also consider adding a version with p < x instead of p \leq x


/- Upstream blueprint metadata (inert):
@[blueprint
  (title := "primorial-bounds")
  (statement := /--
  We have
    $$ \prod_{p \leq x} p = \exp( x + o(x) )$$
  -/)
  (proof := /-- Exponentiate Theorem \ref{chebyshev_asymptotic}. -/)
  (latexEnv := "corollary")]
-/
theorem primorial_bounds :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
      ∀ x : ℝ, ∏ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, p = exp (x + E x) := by
  use (fun x ↦ ∑ p ∈ (filter Nat.Prime (Iic ⌊x⌋₊)), log p - x)
  constructor
  · exact Asymptotics.IsEquivalent.isLittleO chebyshev_asymptotic
  intro x
  simp only [cast_prod, add_sub_cancel, exp_sum]
  apply Finset.prod_congr rfl
  intros x hx
  rw[Real.exp_log]
  rw[Finset.mem_filter] at hx
  norm_cast
  exact Nat.Prime.pos hx.right

theorem primorial_bounds_finprod :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
      ∀ x : ℝ, ∏ᶠ (p : ℕ) (_ : p ≤ x) (_ : Nat.Prime p), p = exp (x + E x) := by
  obtain ⟨E, hE, hprod⟩ := primorial_bounds
  refine ⟨E, hE, fun x ↦ ?_⟩
  have hfin : {p : ℕ | (p : ℝ) ≤ x ∧ p.Prime}.Finite :=
    (Iic ⌊x⌋₊).finite_toSet.subset fun p ⟨hpx, _⟩ ↦ mem_Iic.mpr <| le_floor hpx
  have heq : ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), p =
      ∏ p ∈ (Iic ⌊x⌋₊).filter Prime, p := by
    calc ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), p
        = ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x ∧ p.Prime), p :=
      finprod_congr fun p ↦ by by_cases hp : p.Prime <;> simp [hp]
      _ = ∏ p ∈ hfin.toFinset, p := finprod_mem_eq_finite_toFinset_prod _ hfin
      _ = _ := prod_congr (by ext p; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq,
          mem_filter, mem_Iic, and_congr_left_iff]; exact fun hp ↦
          ⟨le_floor, fun hpn ↦ (le_or_gt 0 x).elim
          (fun hx ↦ (Nat.floor_le hx).trans' (cast_le.mpr hpn)) fun hx ↦
          absurd (le_zero.mp (floor_eq_zero.mpr (hx.trans_le zero_le_one) ▸ hpn))
          hp.ne_zero⟩) (fun _ _ ↦ rfl)
  simp only [heq, hprod]

lemma continuousOn_log0 :
    ContinuousOn (fun x ↦ -1 / (x * log x ^ 2)) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma continuousOn_log1 : ContinuousOn (fun x ↦ (log x ^ 2)⁻¹ * x⁻¹) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma integral_log_inv (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in a..b, ((log t)^2)⁻¹ := by
  rw [le_iff_lt_or_eq] at hb
  rcases hb with hb | rfl; swap
  · simp only [intervalIntegral.integral_same, sub_self, add_zero]
  · have := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x => (log x)⁻¹)
      (u' := fun x => -1 / (x * (log x)^2))
      (v := fun x => x)
      (v' := fun _ => 1) (a := a) (b := b)
      (fun x hx => by
        rw [Set.uIcc_eq_union, Set.Icc_eq_empty (lt_iff_not_ge |>.1 hb), Set.union_empty] at hx
        obtain ⟨hx1, _⟩ := hx
        rw [show (-1 / (x * log x ^ 2)) = (-1 / log x ^ 2) * (x⁻¹) by
          rw [mul_comm x]; field_simp]
        apply HasDerivAt.comp
          (h := fun t => log t) (h₂ := fun t => t⁻¹) (x := x)
        · simpa using! HasDerivAt.inv (c := fun t : ℝ => t) (c' := 1) (x := log x)
            (hasDerivAt_id' (log x))
            (by simp only [ne_eq, log_eq_zero, not_or]; refine ⟨?_, ?_, ?_⟩ <;> linarith)
        · apply hasDerivAt_log; linarith)
      (fun x _ => hasDerivAt_id' x)
      (by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt hb)]
        apply ContinuousOn.integrableOn_Icc
        refine continuousOn_log0.mono fun x hx ↦ ?_
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] at hx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> linarith)
      (by
        constructor <;>
        apply MeasureTheory.integrable_const)
    simp only [mul_one] at this
    rw [this]
    simp_rw [neg_div, neg_mul]
    rw [sub_eq_add_neg]
    congr 1
    rw [intervalIntegral.integral_of_le (le_of_lt hb),
      intervalIntegral.integral_of_le (le_of_lt hb),
      ← MeasureTheory.integral_neg]
    simp_rw [neg_neg]
    refine integral_congr_ae ?_
    · rw [ae_restrict_eq, eventuallyEq_inf_principal_iff]
      · refine .of_forall fun x hx => ?_
        simp only [Set.mem_Ioc, one_div, mul_inv_rev, mul_assoc] at hx ⊢
        rw [inv_mul_cancel₀, mul_one]
        linarith
      exact measurableSet_Ioc

lemma integral_log_inv' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  have := integral_log_inv a b ha hb
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, if_pos hb, Set.uIoc_of_le hb,
    smul_eq_mul, one_mul] at this
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  rw [this]

lemma integral_log_inv'' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    (log a)⁻¹ * a + ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) + ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  rw [integral_log_inv' a b ha hb]
  group

lemma integral_log_inv_pos (x : ℝ) (hx : 2 < x) :
    0 < ∫ t in Set.Icc 2 x, (log t)⁻¹ := by
  classical
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · simp only [Function.support_inv, measurableSet_Icc, Measure.restrict_apply']
    rw [show Function.support log ∩ Set.Icc 2 x = Set.Icc 2 x by
      rw [Set.inter_eq_right]
      intro t ht
      simp only [Set.mem_Icc, Function.mem_support, ne_eq, log_eq_zero, not_or] at ht ⊢
      exact ⟨by linarith, by linarith, by linarith⟩]
    simpa
  · simp only [measurableSet_Icc, ae_restrict_eq, EventuallyLE, eventually_inf_principal]
    refine .of_forall fun t (ht : _ ∧ _) => ?_
    simpa only [Pi.zero_apply, inv_nonneg] using log_nonneg (by linarith)
  · apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀
    · exact (continuousOn_log).mono <| by aesop

    · rintro t ⟨ht, -⟩
      simp only [ne_eq, log_eq_zero, not_or]
      exact ⟨by linarith, by linarith, by linarith⟩

lemma integral_log_inv_ne_zero (x : ℝ) (hx : 2 < x) :
    ∫ t in Set.Icc 2 x, (log t)⁻¹ ≠ 0 := by
  have := integral_log_inv_pos x hx
  linarith

lemma pi_asymp_aux (x : ℝ) (hx : 2 ≤ x) : Nat.primeCounting ⌊x⌋₊ =
    (log x)⁻¹ * θ x + ∫ t in Set.Icc 2 x, θ t * (t * log t ^ 2)⁻¹ := by
  rw [th43_b _ hx]
  simp_rw [div_eq_mul_inv, Chebyshev.theta_eq_sum_Icc]
  ring_nf!

theorem pi_asymp'' :
    (fun x => ((Nat.primeCounting ⌊x⌋₊ : ℝ) / ∫ t in Set.Icc 2 x, 1 / log t) - (1 : ℝ)) =o[atTop]
      fun _ => (1 : ℝ) := by
  obtain ⟨f, hf, f_int, hf'⟩ := chebyshev_asymptotic''
  have eq1 : ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (log x)⁻¹ * (x + x * f x) +
      (∫ t in Set.Icc 2 x,
        (t + t * f t) * (t * log t ^ 2)⁻¹) := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    rw [pi_asymp_aux x hx, hf' x (by linarith)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
    rw [hf' t (by grind)]

  replace eq1 :
    ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (log x)⁻¹ * (x + x * f x) +
      ((∫ t in Set.Icc 2 x, (log t ^ 2)⁻¹) +
        (∫ t in Set.Icc 2 x, (f t) * (log t ^ 2)⁻¹)) := by
    filter_upwards [eq1, eventually_ge_atTop 2] with x eq1 hx
    rw [eq1]
    congr
    simp_rw [mul_inv_rev, add_mul]
    rw [MeasureTheory.integral_add]
    · congr 1
      all_goals
        apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        field [show t ≠ 0 by grind]
    · apply IntegrableOn.mul_continuousOn
        (hg := ContinuousOn.integrableOn_Icc <| continuousOn_id' _)
        (hK := isCompact_Icc)
      apply continuousOn_log1.mono ?_
      intro y h
      simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] at h ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
    · rw [show (fun t ↦ t * f t * ((log t ^ 2)⁻¹ * t⁻¹)) =
        fun t ↦ f t * (t * (log t ^ 2)⁻¹ * t⁻¹) by ext; ring]
      apply IntegrableOn.mul_continuousOn (hK := isCompact_Icc)
      · apply f_int x (by linarith)
      · simp_rw [mul_assoc]
        refine ContinuousOn.mul (continuousOn_id' (Set.Icc 2 x)) ?_
        apply continuousOn_log1.mono ?_
        intro y h
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or] at h ⊢
        exact ⟨by linarith, by linarith, by linarith⟩

  simp_rw [mul_add] at eq1
  simp_rw [show ∀ (x : ℝ),
    (log x)⁻¹ * x + (log x)⁻¹ * (x * f x) +
    ((∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹) +
      ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) =
    ((log x)⁻¹ * x + (∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹)) +
    ((log x)⁻¹ * (x * f x) +
      ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)
    by intros; ring] at eq1

  replace eq1 :
    ∃ (C : ℝ), ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
      ((log x)⁻¹ * (x * f x) +
        ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) +
      C := by
    use ((log 2)⁻¹ * 2)
    filter_upwards [eq1, eventually_ge_atTop 2] with x eq1 hx
    rw [eq1, ← integral_log_inv'' _ _ (by rfl) hx]
    ring
  replace eq1 :
    ∃ (C : ℝ), ∀ᶠ (x : ℝ) in atTop,
      (⌊x⌋₊.primeCounting / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - 1 =
      ((log x)⁻¹ * (x * f x) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) +
      C / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
    obtain ⟨C, hC⟩ := eq1
    use C
    filter_upwards [hC, eventually_gt_atTop 2] with x hC hx
    rw [hC]
    field [integral_log_inv_ne_zero]
  simp_rw [isLittleO_iff] at hf
  choose C hC using eq1
  simp_rw [← one_div] at hC
  apply isLittleO_congr hC (by rfl) |>.mpr
  have ineq1 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c) : ∀ᶠ(x : ℝ) in atTop,
    (log x)⁻¹ * x * |f x| ≤ c * ε * ((log x)⁻¹ * x) := by
    filter_upwards [eventually_ge_atTop 2, hf ε hε hc] with x hx hM
    simp only [norm_eq_abs] at hM
    rw [abs_of_pos hε] at hM
    rw [mul_comm (c * ε)]
    gcongr
    bound
  have int_flog {a b : ℝ} (ha: 2 ≤ a) (hb : 2 ≤ b) :
      IntegrableOn (fun t ↦ |f t| * (log t ^ 2)⁻¹) (Set.Icc a b) volume := by
    apply IntegrableOn.mul_continuousOn
    · apply Integrable.abs <| f_int b hb |>.mono (Set.Icc_subset_Icc_left ha) (by rfl)
    · refine ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
      · simp
        grind
      · intro t ht
        simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
        exact ⟨by linarith, by linarith, by linarith⟩
    · exact isCompact_Icc
  have int_inv_log_sq {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
      IntegrableOn (fun t ↦ (log t ^ 2)⁻¹) (Set.Icc a b) volume := by
    refine ContinuousOn.integrableOn_Icc <|
      ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
    · grind
    · intro t ht
      simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
  simp_rw [eventually_atTop] at hf
  choose M hM using hf
  have ineq2 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c)  :
    ∃ (D : ℝ),
      ∀ᶠ (x : ℝ) in atTop,
      |∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹| ≤
      c * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) + D := by
    use (((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), |f t| * (log t ^ 2)⁻¹) -
              c * ε * ∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹) +
            c * ε * ((log 2)⁻¹ * 2))
    filter_upwards [eventually_gt_atTop (max 2 (M ε hε hc))] with x hx
    calc _
      _ ≤ ∫ (t : ℝ) in Set.Icc 2 x, |f t * (log t ^ 2)⁻¹| :=
        norm_integral_le_integral_norm fun a ↦ f a * (log a ^ 2)⁻¹
      _ = ∫ (t : ℝ) in Set.Icc 2 x, |f t| * (log t ^ 2)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        rw [abs_mul, abs_of_nonneg (a := (log t ^ 2)⁻¹)]
        norm_num
        apply pow_nonneg
        exact log_nonneg <| by grind
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          (∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x,
          |f t| * (log t ^ 2)⁻¹) := by
        rw [← setIntegral_union₀, Set.Icc_union_Icc_eq_Icc (le_max_left ..) hx.le]
        · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton (le_max_left ..) hx.le, volume_singleton]
        · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
        · apply int_flog (by rfl) (le_max_left ..)
        · apply int_flog (le_max_left ..) (le_trans (le_max_left ..) hx.le)
      _ ≤ (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          (∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x,
          (c * ε) * (log t ^ 2)⁻¹) := by
          gcongr 1
          apply setIntegral_mono_on
          · apply int_flog (le_max_left ..) (le_trans (le_max_left ..) hx.le)
          · rw [IntegrableOn, integrable_const_mul_iff]
            · apply int_inv_log_sq (le_max_left ..) (le_trans (le_max_left ..) hx.le)
            · simp only [isUnit_iff_ne_zero, ne_eq, _root_.mul_eq_zero, not_or]
              exact ⟨by linarith, by linarith⟩
          · exact measurableSet_Icc
          · intro t ht
            simp only [Set.mem_Icc, sup_le_iff] at ht
            apply mul_le_mul_of_nonneg_right
            · refine hM ε hε hc t ht.1.2 |>.trans ?_
              simp only [norm_eq_abs, abs_of_pos hε, le_refl]
            · norm_num
              refine pow_nonneg (log_nonneg <| by linarith) 2
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) * ∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x, (log t ^ 2)⁻¹) := by
          congr 1
          exact integral_const_mul (c * ε) _
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) *
            ((∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x, (log t ^ 2)⁻¹) +
            ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) -
            ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)))) := by
        ring
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) *
            ((∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹) -
              ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)))) := by
          congr 3
          rw [add_comm, ← setIntegral_union₀, Set.Icc_union_Icc_eq_Icc (le_max_left ..) hx.le]
          · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton (le_max_left ..) hx.le,
              volume_singleton]
          · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
          · apply int_inv_log_sq (by rfl) (le_max_left ..)
          · apply int_inv_log_sq (le_max_left ..) (le_trans (le_max_left ..) hx.le)
      _ = ((c * ε) * (∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹)) +
        ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
        |f t| * (log t ^ 2)⁻¹) -
        (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) := by
        ring
      _ = ((c * ε) * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
            ((log 2)⁻¹ * 2) - ((log x)⁻¹ * x))) +
        ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
        |f t| * (log t ^ 2)⁻¹) -
        (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) := by
        congr 2
        rw [integral_log_inv' _ _ (by rfl)]
        · ring
        · simp only [max_lt_iff] at hx
          linarith
      _ = _ := by ring
  choose D hD using ineq2

  have ineq4 (const : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, |const / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| ≤ 1/2 * ε := by
    obtain rfl|hconst := eq_or_ne const 0
    · filter_upwards with x
      simp[hε.le]
    have ineq (x : ℝ) (hx : 2 < x) :=
      calc (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)
        _ ≥ (∫ (_ : ℝ) in Set.Icc 2 x, (log x)⁻¹) := by
          apply setIntegral_mono_on (integrable_const _)
          · refine ContinuousOn.integrableOn_Icc <|
              ContinuousOn.inv₀ (continuousOn_log |>.mono ?_) ?_
            · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, not_and, not_le,
              isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
            · intro t ht
              simp only [Set.mem_Icc, ne_eq, log_eq_zero, not_or] at ht ⊢
              exact ⟨by linarith, by linarith, by linarith⟩
          · exact measurableSet_Icc
          · intro t ⟨ht1, ht2⟩
            gcongr
            bound
        _ = (x - 2) * (log x)⁻¹ := by
          rw [MeasureTheory.integral_const]
          simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, volume_Icc,
            smul_eq_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff, sub_nonneg,
            inv_eq_zero, log_eq_zero, Measure.real]
          refine Or.inl (le_of_lt hx)

    simp_rw [abs_div]
    have ineq (x : ℝ) (hx : 2 < x) :
        |const| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| ≤
        |const| / ((x - 2) * (log x)⁻¹) := by
      apply div_le_div₀ (abs_nonneg _) (by rfl)
      · apply mul_pos
        · linarith
        · norm_num
          rw [Real.log_pos_iff]
          · linarith
          · linarith
      · rw [abs_of_pos (integral_log_inv_pos _ hx)]
        exact ineq x hx
    have ineq (x : ℝ) (hx : 2 < x) :
        |const| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| ≤
        |const| * (log x / ((x - 2))) := by
      refine ineq x hx |>.trans <| le_of_eq ?_
      field_simp
    have lim := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 (by norm_num)
    simp only [pow_one, one_mul, ← sub_eq_add_neg] at lim
    rw [tendsto_atTop_nhds] at lim
    specialize lim (Metric.ball 0 ((1/2) * ε / |const| : ℝ)) (by
      simp only [Metric.mem_ball, dist_self]
      apply _root_.div_pos
      · linarith
      · simpa only [abs_pos, ne_eq]) Metric.isOpen_ball
    obtain ⟨M, hM⟩ := lim
    rw [eventually_atTop]
    refine ⟨max 3 M, ?_⟩
    intro x hx
    simp only [Metric.mem_ball, dist_zero_right, max_le_iff, norm_eq_abs] at hM hx
    refine ineq x (by linarith) |>.trans ?_
    specialize hM x hx.2
    rw [abs_of_nonneg (by
      apply div_nonneg
      · refine log_nonneg (by linarith)
      · linarith)] at hM
    have ineq' : |const| * (log x / (x - 2)) < |const| * ((1/2) * ε / |const|) := by
      rw [mul_lt_mul_iff_right₀]
      · exact hM
      · simpa only [abs_pos, ne_eq]
    rw [mul_div_cancel₀] at ineq'
    · refine le_of_lt ineq'
    · simpa only [ne_eq, abs_eq_zero]
  rw [isLittleO_iff]
  intro ε hε
  specialize ineq4 (|D ε hε (1/2) (by linarith)| + |C|) ε hε
  simp only [one_div, norm_eq_abs, norm_one, mul_one]
  filter_upwards [eventually_gt_atTop 2, ineq4, ineq1 ε hε (1 / 2) (by norm_num),
      hD ε hε (1 / 2) (by norm_num)] with x hx hB ineq1 hD
  have := integral_log_inv_pos x (by linarith) |>.le
  calc _
    _ ≤ |((log x)⁻¹ * (x * f x) / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) /
          ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      apply abs_add_three
    _ = |(log x)⁻¹ * (x * f x)| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      rw [abs_div, abs_div, abs_div]
    _ = |(log x)⁻¹ * (x * f x)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        repeat rw [abs_of_pos <| integral_log_inv_pos _ (by linarith)]
    _ = ((log x)⁻¹ * x * |f x|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        congr
        rw [abs_mul, abs_mul, abs_of_nonneg (by bound), abs_of_nonneg (by linarith), mul_assoc]
    _ ≤ ((1/2) * ε * ((log x)⁻¹ * x)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        ((1/2) * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) +
          D ε hε (1/2) (by linarith)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        gcongr
    _ = ((1/2) * ε * (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (D ε hε (1/2) (by linarith) + |C|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      ring
    _ = (1/2) * ε + (D ε hε (1/2) (by linarith) + |C|) /
        (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      congr 1
      rw [mul_div_assoc, div_self, mul_one]
      apply integral_log_inv_ne_zero
      linarith
    _ ≤ (1/2) * ε + (|D ε hε (1/2) (by linarith)| + |C|) /
        (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      gcongr
      apply le_abs_self
    _ ≤ (1/2) * ε + (1/2) * ε := by
      rw [abs_div, abs_of_nonneg, abs_of_pos (a := ∫ _ in _, _)] at hB
      · gcongr
      · apply integral_log_inv_pos; linarith
      · positivity
    _ = ε := by
      field

/- Upstream blueprint metadata (inert):
@[blueprint
  (title := "pi-asymp")
  (statement := /--
  There exists a function $c(x)$ such that $c(x) = o(1)$ as $x \to \infty$ and
  $$ \pi(x) = (1 + c(x)) \int_2^x \frac{dt}{\log t}$$
  for all $x$ large enough.
  -/)
  (proof := /--
  We have the identity
  $$ \pi(x) = \frac{1}{\log x} \sum_{p \leq x} \log p
  + \int_2^x (\sum_{p \leq t} \log p) \frac{dt}{t \log^2 t}$$
  as can be proven by interchanging the sum and integral and using the fundamental theorem of
  calculus.  For any $\eps$, we know from Theorem \ref{chebyshev_asymptotic} that there is $x_\eps$
  such that $\sum_{p \leq t} \log p = t + O(\eps t)$ for $t \geq x_\eps$, hence for $x \geq x_\eps$
  $$ \pi(x) = \frac{1}{\log x} (x + O(\eps x))
  + \int_{x_\eps}^x (t + O(\eps t)) \frac{dt}{t \log^2 t} + O_\eps(1)$$
  where the $O_\eps(1)$ term can depend on $x_\eps$ but is independent of $x$.  One can evaluate
  this after an integration by parts as
  $$ \pi(x) = (1+O(\eps)) \int_{x_\eps}^x \frac{dt}{\log t} + O_\eps(1)$$
  $$  = (1+O(\eps)) \int_{2}^x \frac{dt}{\log t} $$
  for $x$ large enough, giving the claim.
  -/)]
-/
theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ (x : ℝ) in atTop,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in (2 : ℝ)..x, 1 / (log t) := by
  refine ⟨_, pi_asymp'', ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  field [(integral_log_inv_pos x (by linarith)).ne']

lemma inv_div_log_asy : ∃ c, ∀ᶠ (x : ℝ) in atTop,
    ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2 ≤ c * (x / log x ^ 2) := by
  have := Chebyshev.integral_one_div_log_sq_isBigO
  rw [isBigO_iff] at this
  obtain ⟨c, hc⟩ := this
  use c
  filter_upwards [hc, eventually_ge_atTop 2] with x hc hx
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  apply le_trans (by apply le_norm_self)
  nth_rewrite 2 [norm_of_nonneg (by positivity)] at hc
  exact hc

lemma integral_log_inv_pialt (x : ℝ) (hx : 4 ≤ x) : ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t =
    x / log x - 2 / log 2 + ∫ (t : ℝ) in Set.Icc 2 x, 1 / (log t) ^ 2 := by
  have := integral_log_inv 2 x (by norm_num) (by linarith)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hx]),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [hx]),
    ← mul_one_div, one_div, ← mul_one_div, one_div]
  simp only [one_div, this, mul_comm]

lemma integral_div_log_asymptotic : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ᶠ (x : ℝ) in atTop, ∫ t in Set.Icc 2 x, 1 / (log t) = (1 + c x) * x / (log x) := by
  obtain ⟨c, hc⟩ := inv_div_log_asy
  use fun x => ((∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2) - 2 / log 2) * log x / x
  constructor
  · simp_rw [mul_div_assoc, mul_comm]
    apply isLittleO_mul_iff_isLittleO_div _|>.mpr
    · simp_rw [one_div_div]
      apply IsLittleO.sub
      · apply IsBigO.trans_isLittleO (g := (fun x ↦ x / log x ^ 2))
        · rw [isBigO_iff]
          use c
          filter_upwards [eventually_ge_atTop 2, hc] with x hx hc
          simp only [norm_eq_abs]
          rwa [abs_of_nonneg, abs_of_nonneg]
          · bound
          · apply setIntegral_nonneg measurableSet_Icc fun t ht ↦ (by bound)
        apply isLittleO_of_tendsto
        · simp
        apply tendsto_log_atTop.inv_tendsto_atTop.congr'
        filter_upwards [eventually_ne_atTop 0] with x hx
        simp only [Pi.inv_apply]
        field
      apply isLittleO_mul_iff_isLittleO_div _|>.mp
      · conv => arg 2; ext; rw [mul_comm]
        apply IsLittleO.const_mul_left isLittleO_log_id_atTop
      · filter_upwards [eventually_ge_atTop 2] with x hx
        simp; grind
    filter_upwards [eventually_ge_atTop 2] with x hx
    simp
    grind
  · filter_upwards [eventually_ge_atTop 4] with x hx
    rw [integral_log_inv_pialt x hx]
    field [show log x ≠ 0 by simp; grind]

/- Upstream blueprint metadata (inert):
@[blueprint
  (title := "pi-alt")
  (statement := /--
    One has
  $$ \pi(x) = (1+o(1)) \frac{x}{\log x}$$
  as $x \to \infty$.
  -/)
  (proof := /--
  An integration by parts gives
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} - \frac{2}{\log 2} +
  \int_2^x \frac{dt}{\log^2 t}.$$
  We have the crude bounds
  $$ \int_2^{\sqrt{x}} \frac{dt}{\log^2 t} = O( \sqrt{x} )$$
  and
  $$ \int_{\sqrt{x}}^x \frac{dt}{\log^2 t} = O( \frac{x}{\log^2 x} )$$
  and combining all this we obtain
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} + O( \frac{x}{\log^2 x} )$$
  $$ = (1+o(1)) \frac{x}{\log x}$$
  and the claim then follows from Theorem \ref{pi_asymp}.
  -/)
  (latexEnv := "corollary")]
-/
theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  obtain ⟨f, hf, h⟩ := pi_asymp
  obtain ⟨f', hf', h'⟩ := integral_div_log_asymptotic
  use (fun x => (log x / x) * ⌊x⌋₊.primeCounting - 1)
  constructor
  · apply IsLittleO.congr' (f₁ := (fun x ↦ f x + f x * f' x + f' x)) _ _ (by rfl)
    · apply IsLittleO.add _ hf'
      apply IsLittleO.add hf
      convert! hf.mul hf'
      ring
    · filter_upwards [eventually_ge_atTop 2, h, h'] with x hx h h'
      rw [h, intervalIntegral.integral_of_le hx, ← integral_Icc_eq_integral_Ioc, h']
      have : log x ≠ 0 := by simp; grind
      field
  · intro x
    obtain rfl|hx := eq_or_ne x 0
    · simp
    obtain rfl|hx := eq_or_ne x 1
    · simp
    obtain rfl|hx := eq_or_ne x (-1 : ℝ)
    · simp
      norm_num
    have : log x ≠ 0 := by simp_all
    field

theorem pi_alt' :
    (fun (x : ℝ) ↦ (primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / log x) := by
  obtain ⟨f, ⟨hf1, hf2⟩⟩ := pi_alt
  simp_rw [hf2, IsEquivalent]
  have : ((fun x ↦ (1 + f x) * x / log x) - fun x ↦ x / log x) =
      (fun x ↦ f x * x / log x) := by
    ext
    simp
    ring
  rw [this]
  convert hf1.mul_isBigO (f₂ := (fun x ↦ x / log x)) (g₂ := (fun x ↦ x /log x))
      (isBigO_refl ..) using 2
  all_goals first | ring | rfl


lemma pi_nth_prime (n : ℕ) :
    primeCounting (nth_prime n) = n + 1 := by
  rw [primeCounting, primeCounting', count_nth_succ_of_infinite infinite_setOf_prime]

lemma tendsto_nth_prime_atTop : Tendsto nth_prime atTop atTop :=
  nth_strictMono infinite_setOf_prime |>.tendsto_atTop

lemma pi_nth_prime_asymp :
    (fun n ↦ (nth_prime n) / (log (nth_prime n))) ~[atTop] (fun (n : ℕ) ↦ (n : ℝ)) := by
  trans (fun (n : ℕ) ↦ ( n + 1 : ℝ))
  · have : Tendsto (fun n ↦ ((nth_prime n) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_iff.mpr tendsto_nth_prime_atTop
    convert! pi_alt'.comp_tendsto this |>.symm
    simp only [Function.comp_apply, floor_natCast]
    rw [pi_nth_prime]
    norm_cast
  · apply IsEquivalent.add_isLittleO (by rfl)
    exact isLittleO_const_id_atTop (1 : ℝ) |>.natCast_atTop

lemma log_nth_prime_asymp : (fun n ↦ log (nth_prime n)) ~[atTop] (fun n ↦ log n) := by
  have := pi_nth_prime_asymp.log tendsto_natCast_atTop_atTop
  · apply IsEquivalent.trans _ this
    apply IsEquivalent.congr_right (v := (fun n ↦ log (nth_prime n) - log (log (nth_prime n))))
    swap
    · filter_upwards with n
      rw [log_div]
      · exact_mod_cast prime_nth_prime n |>.ne_zero
      · apply log_ne_zero.mpr ⟨?_, ?_, ?_⟩
        <;> norm_cast<;> linarith [prime_nth_prime n |>.two_le]
    symm
    apply IsEquivalent.sub_isLittleO (by rfl)
    apply IsLittleO.comp_tendsto isLittleO_log_id_atTop
    have : Tendsto (fun n ↦ ((nth_prime n) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_iff.mpr tendsto_nth_prime_atTop
    apply tendsto_log_atTop.comp this

lemma nth_prime_asymp : (fun n ↦ ((nth_prime n) : ℝ)) ~[atTop] (fun n ↦ n * log n) := by
  have := pi_nth_prime_asymp.mul log_nth_prime_asymp
  convert! this using 1
  ext n
  simp only [Pi.mul_apply]
  have : log (nth_prime n) ≠ 0 :=by
    apply log_ne_zero.mpr ⟨?_, ?_, ?_⟩
      <;> norm_cast<;> linarith [prime_nth_prime n |>.two_le]
  field

/- Upstream blueprint metadata (inert):
@[blueprint
  (title := "pn-asymptotic")
  (statement := /--
   One has
    $$ p_n = (1+o(1)) n \log n$$
  as $n \to \infty$.
  -/)
  (proof := /--
    Use Corollary \ref{pi_alt} to show that $n=\pi(p_n)\sim p_n/\log p_n$
    Taking logs gives $\log n \sim \log p_n - \log\log p_n \sim \log p_n$.
    Multiplying these gives $p_n\sim n\log n$ from which the result follows.
  -/)
  (latexEnv := "proposition")]
-/
theorem pn_asymptotic : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, n > 1 → nth_prime n = (1 + c n) * n * log n := by
  let c : ℕ → ℝ := fun n ↦ (nth_prime n) / (n * log n) - 1
  refine ⟨c, ?_, ?_⟩
  swap
  · intro n hn
    have : log n ≠ 0 := by rw [Real.log_ne_zero]; rify at hn; grind
    simp [c]
    field_simp
  apply isLittleO_of_tendsto
  · simp
  simp only [div_one]
  unfold c
  have := isEquivalent_iff_tendsto_one ?_|>.mp nth_prime_asymp
  swap
  · filter_upwards [eventually_ge_atTop 2] with n hn
    simp
    norm_cast
    grind
  convert! this.add_const (-1 : ℝ) using 2
  norm_num


/- Upstream blueprint metadata (inert):
@[blueprint
  (title := "pn-pn-plus-one")
  (statement := /--
  We have $p_{n+1} - p_n = o(p_n)$
    as $n \to \infty$.
  -/)
  (proof := /-- Easy consequence of preceding proposition. -/)
  (latexEnv := "corollary")]
-/
theorem pn_pn_plus_one : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, nth_prime (n + 1) - nth_prime n = (c n) * nth_prime n := by
  use (fun n => (nth_prime (n+1) - nth_prime n) / nth_prime n)
  refine ⟨?_, ?_⟩
  · obtain ⟨k, k_o1, p_n_eq⟩ := pn_asymptotic
    simp only [isLittleO_one_iff]
    rw [Filter.tendsto_congr' (f₂ := fun n ↦
        ((1 + k (n+1))*(n+1)*log (n+1) - (1 + k n)*n*log n) / ((1 + k n)*n*log n))]
    swap
    · simp only [EventuallyEq, eventually_atTop]
      use 2; intro n hn
      rw [p_n_eq n (by linarith), p_n_eq (n+1) (by linarith)]
      grind
    simp_rw [sub_div]
    have zero_eq_minus: (0 : ℝ) = 1 - 1 := by
      simp
    rw [zero_eq_minus]
    apply Filter.Tendsto.sub
    · conv =>
        arg 1
        intro n
        equals ((1 + k (n + 1)) / (1 + k n) ) * ((↑n + 1) * log (↑n + 1) / (↑n * log ↑n)) =>
          field_simp
      nth_rw 6 [← (one_mul 1)]
      apply Filter.Tendsto.mul
      · have one_div: nhds 1 = nhds ((1: ℝ) / 1) := by simp
        rw [one_div]
        apply Filter.Tendsto.div
        · nth_rw 3 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · simp
          · rw [Filter.tendsto_add_atTop_iff_nat]
            rw [Asymptotics.isLittleO_iff_tendsto] at k_o1
            · simp only [div_one] at k_o1
              exact k_o1
            · simp
        · nth_rw 2 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · simp
          · rw [Asymptotics.isLittleO_iff_tendsto] at k_o1
            · simp only [div_one] at k_o1
              exact k_o1
            · simp

        simp
      · conv =>
          arg 1
          intro x
          equals ((↑x + 1) / x) * (log (↑x + 1) / (log ↑x)) =>
            field_simp
        nth_rw 3 [← (one_mul 1)]
        apply Filter.Tendsto.mul
        · simp_rw [add_div]
          nth_rw 2 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · rw [← Filter.tendsto_add_atTop_iff_nat 1]
            field_simp
            simp
          · simp only [one_div]
            exact tendsto_inv_atTop_nhds_zero_nat
        · have log_eq: ∀ (n: ℕ), log (↑n + 1) = log ↑n + log (1 + 1/n) := by
            intro n
            by_cases n_eq_zero: n = 0
            · simp [n_eq_zero]
            · calc
                _ = log (n * (1 + 1 / n)) := by field_simp
                _ = log n + log (1 + 1/n) := by
                  rw [Real.log_mul]
                  · simpa
                  · simp only [one_div, ne_eq]
                    positivity

          simp_rw [log_eq]
          simp_rw [add_div]
          nth_rw 3 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · rw [← Filter.tendsto_add_atTop_iff_nat 2]
            have log_not_zero: ∀ n: ℕ, log (n + 2) ≠ 0 := by
              intro n
              simp only [ne_eq, log_eq_zero, not_or]
              refine ⟨?_, ?_, ?_⟩
              · norm_cast
              · norm_cast
                simp
              · norm_cast
            simp [log_not_zero]
          · rw [← Filter.tendsto_add_atTop_iff_nat 2]
            apply squeeze_zero (g := fun (n: ℕ) => (log 2 / log (n + 2)))
            · intro n
              have log_plus_nonzero: 0 ≤ log (1 + 1 / ↑(n + 2)) := by
                apply log_nonneg
                simp only [cast_add, cast_ofNat, one_div, le_add_iff_nonneg_right, inv_nonneg]
                norm_cast
                simp only [le_add_iff_nonneg_left, _root_.zero_le]
              exact div_nonneg log_plus_nonzero (log_natCast_nonneg (n + 2))
            · intro n
              norm_cast
              have log_le_2: log (1 + 1 / ↑(n + 2)) ≤ log 2 := by
                apply Real.log_le_log
                · positivity
                · have two_eq_one_plus_one: (2 : ℝ) = 1 + 1 := by
                    norm_num
                  rw [two_eq_one_plus_one]
                  simp only [cast_add, cast_ofNat, one_div, add_le_add_iff_left, ge_iff_le]
                  apply inv_le_one_of_one_le₀
                  linarith

              rw [div_le_div_iff_of_pos_right]
              · exact log_le_2
              · apply Real.log_pos
                norm_cast
                simp
            · apply Filter.Tendsto.div_atTop (l := atTop) (a := log 2)
              · simp
              · norm_cast
                have shift_fn :=
                  Filter.tendsto_add_atTop_iff_nat (f := fun n => log (n)) (l := atTop) 2
                rw [shift_fn]
                apply Filter.Tendsto.comp Real.tendsto_log_atTop
                exact tendsto_natCast_atTop_atTop

    · have eventually_nonzero: ∃ t, t > 2 ∧ ∀ n, 1 + k (n + t) ≠ 0 := by
        rw [Asymptotics.isLittleO_iff_tendsto] at k_o1
        · rw [NormedAddGroup.tendsto_nhds_zero] at k_o1
          specialize k_o1 ((1 : ℝ) / 2)
          simp only [one_div, gt_iff_lt, inv_pos, ofNat_pos, div_one, norm_eq_abs, eventually_atTop, forall_const] at k_o1
          obtain ⟨a, ha⟩ := k_o1
          use (a + 3)
          refine ⟨by simp, ?_⟩
          intro n
          specialize ha (n + (a + 3))
          have a_le_plus: a ≤ n + (a + 3) := by omega
          simp only [a_le_plus, forall_const] at ha

          by_contra!
          rw [add_eq_zero_iff_eq_neg] at this
          rw [← abs_neg] at ha
          rw [← this] at ha
          simp only [abs_one] at ha
          have two_inv_lt := inv_lt_one_of_one_lt₀ (a := (2 : ℝ)) (by simp)
          linarith
        · simp

      obtain ⟨t, t_gt_2, ht⟩ := eventually_nonzero
      rw [← Filter.tendsto_add_atTop_iff_nat t]
      have denom_nonzero: ∀ n, ((1 + k (n + t)) * ↑(n + t) * log ↑(n + t)) ≠ 0 := by
        intro n
        simp only [cast_add, ne_eq, _root_.mul_eq_zero, log_eq_zero, not_or]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · exact ht n
        · norm_cast
          omega
        · norm_cast
          omega
        · refine ⟨?_, by norm_cast⟩
          norm_cast
          omega
      conv =>
        arg 1
        intro n
        rw [div_self (denom_nonzero n)]
      simp
  · intro n
    have nth_nonzero: nth_prime n ≠ 0 := by
      exact Nat.Prime.ne_zero (prime_nth_prime n)
    simp [nth_nonzero]



lemma prime_in_gap' (a b : ℕ) (h : a.primeCounting < b.primeCounting)
    : ∃ (p : ℕ), p.Prime ∧ (a + 1) ≤ p ∧ p < (b + 1) := by
  obtain ⟨p, hp, pp⟩ := exists_of_count_lt_count h
  exact ⟨p, pp, hp.left, hp.right⟩

lemma prime_in_gap (a b : ℝ) (ha : 0 < a)
    (h : ⌊a⌋₊.primeCounting < ⌊b⌋₊.primeCounting)
    : ∃(p : ℕ), p.Prime ∧ a < p ∧ p ≤ b := by

  have hab : ⌊a⌋₊ < ⌊b⌋₊ := Monotone.reflect_lt Nat.monotone_primeCounting h
  obtain ⟨w, h, ha, hb⟩ := prime_in_gap' ⌊a⌋₊ ⌊b⌋₊ h
  refine ⟨w, h, lt_of_floor_lt ha, ?_⟩
  have : a < b := by
    by_contra h
    cases lt_or_eq_of_le <| le_of_not_gt h with
    | inl hh => linarith [floor_le_floor <| le_of_lt hh]
    | inr hh =>
      rw [hh] at hab
      rwa [←lt_self_iff_false ⌊a⌋₊]
  by_contra h
  have : ⌊b⌋₊ < w := floor_lt (by linarith) |>.mpr (lt_of_not_ge h)
  have : ⌊b⌋₊ + 1 ≤ w := by linarith
  linarith

lemma bound_f_second_term (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop, (1 + f x) < (1 + δ) := by
  have bound_one_plus_f: ∀ y: ℝ, ∀ z: ℝ, |f y| < z → 1 + (f y) < 1 + z := by
    intro y z hf
    by_cases f_pos: 0 < f y
    · rw [abs_of_pos f_pos] at hf
      linarith
    · rw [not_lt] at f_pos
      rw [abs_of_nonpos f_pos] at hf
      linarith

  have f_small := NormedAddGroup.tendsto_nhds_zero.mp hf δ hδ
  simp only [norm_eq_abs, eventually_atTop] at f_small
  obtain ⟨p, hp⟩ := f_small

  let a := ((max 1 p) : ℝ)
  have ha: ∀ b: ℝ, a ≤ b → |f b| < δ := by
    intro b hb
    have b_ge_p: p ≤ b := by
      have a_ge_p: p ≤ a := by simp [a]
      linarith
    exact hp b b_ge_p

  rw [Filter.eventually_atTop]

  use a
  intro b hb
  exact bound_one_plus_f b δ (ha b (by linarith))


lemma bound_f_first_term {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x: ℝ in atTop, (1 + f ((1 + ε) * x)) > (1 - δ)  := by
  have bound_one_plus_f: ∀ y: ℝ, ∀ z: ℝ, |f y| < z → 1 + (f y) > 1 - z := by
    intro y z hf
    by_cases f_pos: 0 < f y
    · rw [abs_of_pos f_pos] at hf
      linarith
    · rw [not_lt] at f_pos
      rw [abs_of_nonpos f_pos] at hf
      linarith

  have f_small := NormedAddGroup.tendsto_nhds_zero.mp hf δ hδ
  simp only [norm_eq_abs, eventually_atTop] at f_small
  obtain ⟨p, hp⟩ := f_small

  let a := ((max 1 p) : ℝ)
  have ha: ∀ b: ℝ, a ≤ b → |f b| < δ := by
    intro b hb
    have b_ge_p: p ≤ b := by
      have a_ge_p: p ≤ a := by simp [a]
      linarith
    exact hp b b_ge_p


  rw [Filter.eventually_atTop]

  use a
  intro b hb

  have a_pos: 0 < a := by
    simp [a]

  have pos_mul: ∀ x y z : ℝ, 0 < x → 0 < y → 1 < z → x ≤ y → x < y * z := by
    intro x y z _ hy hz hlt
    have y_lt: y < y * z := by
      exact (lt_mul_iff_one_lt_right hy).mpr hz
    linarith

  have mul_increase: a ≤ (1 + ε) * b := by
    simp only [ a] at hb
    have a_le := pos_mul a b (1 + ε) a_pos (by linarith) (by linarith) (by linarith)
    linarith

  exact bound_one_plus_f ((1 + ε) * b) δ (ha ((1 + ε) * b) mul_increase)

lemma smaller_terms {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ)
    (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop, (1 - δ) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) <
      (1 + f ((1 + ε) * x)) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) := by
  have first_term := bound_f_first_term hε f hf δ hδ
  simp only [gt_iff_lt, eventually_atTop] at first_term
  obtain ⟨p, hp⟩ := first_term
  simp only [eventually_atTop]
  let a := max p 1
  have ha: ∀ (b : ℝ), a ≤ b → 1 - δ < 1 + f ((1 + ε) * b) := by
    intro b hb
    have a_ge_p: p ≤ a := by
      simp [a]
    specialize hp b (by linarith)
    exact hp
  use a
  intro b hb
  rw [mul_lt_mul_iff_left₀]
  · exact ha b hb
  · simp only [sup_le_iff, a] at hb
    have b_ge_one: 1 ≤ b := hb.2
    have log_pos: Real.log ((1 + ε) *b) > 0 := by
      have one_pplus_pos: 1 < (1 + ε) := by linarith
      refine (Real.log_pos_iff ?_).mpr ?_
      · positivity
      · exact one_lt_mul_of_lt_of_le one_pplus_pos b_ge_one

    positivity

lemma second_smaller_terms (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop,
      (1 + δ) * (x / Real.log x) > (1 + f x) * (x / Real.log x) := by
  have first_term := bound_f_second_term f hf δ hδ

  simp only [_root_.add_lt_add_iff_left, eventually_atTop] at first_term
  obtain ⟨p, hp⟩ := first_term
  simp only [gt_iff_lt, eventually_atTop]
  let a := max p 2
  have ha: ∀ (b : ℝ), a ≤ b → 1 + δ > 1 + f ( b) := by
    intro b hb
    have a_ge_p: p <= a := by simp [a]
    specialize hp b (by linarith)
    linarith
  use a
  intro b hb
  specialize ha b hb
  have rhs_nonzero:  b / log ( b) > 0 := by
    simp only [sup_le_iff, a] at hb
    obtain ⟨_, hb2⟩ := hb
    have log_pos: Real.log (b) > 0 := by
      refine (Real.log_pos_iff ?_).mpr ?_
      · positivity
      · linarith
    positivity
  rw [mul_lt_mul_iff_left₀]
  · exact ha
  · linarith

lemma x_log_x_atTop : Filter.Tendsto (fun x => x / Real.log x) Filter.atTop Filter.atTop := by
  have inv_log_x_div := Filter.Tendsto.comp (f := fun x => Real.log x / x) (g := fun x => x⁻¹)
    (x := Filter.atTop) (y := (nhdsWithin 0 (Set.Ioi 0))) (z := Filter.atTop) ?_ ?_
  · simp_rw [Function.comp_def, inv_div] at inv_log_x_div
    exact inv_log_x_div
  · exact tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
  · rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have log_div_x := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by simp)
      simp only [pow_one, one_mul, add_zero] at log_div_x
      exact log_div_x
    · simp only [Set.mem_Ioi, eventually_atTop]
      use 2
      intro x hx
      have log_pos: 0 < Real.log x := by
        refine (Real.log_pos_iff ?_).mpr ?_ <;> linarith
      positivity


lemma tendsto_by_squeeze (ε : ℝ) (hε : ε > 0) :
    Tendsto (fun (x : ℝ) => (Nat.primeCounting ⌊(1 + ε) * x⌋₊ : ℝ) -
      (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop atTop := by
  obtain ⟨c, hc, pi_x_eq⟩ := pi_alt
  rw [Asymptotics.isLittleO_iff_tendsto (by simp)] at hc
  conv =>
    arg 1
    intro x
    rw [pi_x_eq]
    rw [pi_x_eq]
  simp only [div_one] at hc

  -- (1 + δ) * (( x / (Real.log (x)))) > (1 + f ( x)) * ( x / (Real.log (x)))

  let d: ℝ := ε/(2*(2 + ε))
  have hd: 0 < d := by positivity
  have first_helper := smaller_terms hε c hc (d) hd
  have second_helper := second_smaller_terms c hc d hd

  apply Filter.tendsto_atTop_mono' (f₁ := fun x => (
      ((1 - d) * ((1 + ε) * x / log ((1 + ε) * x)))
      -
      ((1 + d) * (x / log x)))
    )
  · rw [Filter.EventuallyLE]

    simp only [eventually_atTop] at first_helper
    simp only [gt_iff_lt, eventually_atTop] at second_helper

    obtain ⟨a1, ha1⟩ := first_helper
    obtain ⟨a2, ha2⟩ := second_helper

    simp only [eventually_atTop]

    use (max a1 a2)
    intro b hb

    have lt_compare: ∀ a b c d : ℝ, a < c ∧ b > d → a - b ≤ c - d := by
      intro a b c d h_lt
      obtain ⟨a_lt, b_gt⟩ := h_lt
      linarith

    apply lt_compare
    simp only [ sup_le_iff] at hb
    specialize ha1 b hb.1
    specialize ha2 b hb.2
    field_simp
    field_simp at ha1 ha2
    exact ⟨ha1, ha2⟩
  · rw [← Filter.tendsto_comp_val_Ioi_atTop (a := 1)]
    have log_split: ∀ x: Set.Ioi 1, x.val / log ((1 + ε) * x.val) =
      x.val / (log (1 + ε) + log (x.val)) := by
      intro x
      have x_ge_one: 1 < x.val := Set.mem_Ioi.mp x.property
      rw [Real.log_mul (by linarith) (by linarith)]

    have log_factor: ∀ x: Set.Ioi 1, x.val / (log (1 + ε) + log (x.val)) =
      x.val / ((1 + (log (1 + ε)/(log x.val))) * (log x.val)) := by
      intro x
      have : log (x.val) ≠ 0 := by
        have pos := Real.log_pos x.property
        linarith
      field_simp
      rw [add_comm]

    conv at log_factor =>
      intro x
      rhs
      rw [div_mul_eq_div_mul_one_div]

    conv =>
      arg 1
      intro x
      lhs
      rw [mul_div_assoc]
      rw [log_split x]

    conv =>
      arg 1
      intro x
      lhs
      rw [log_factor]

    suffices Tendsto (fun x : Set.Ioi (1 : ℝ) ↦ (1 - d) * ((1 + ε) * x) /
      ((1 + log (1 + ε) / log x) * log x) - (1 + d) * x / log x) atTop atTop by
      field_simp at this ⊢
      exact this
    conv =>
      arg 1
      intro x
      rw [sub_eq_add_neg]
      rw [← neg_div]
      rw [div_add_div]
      · skip
      tactic =>
        simp only [ne_eq, _root_.mul_eq_zero, log_eq_zero, not_or]
        have x_pos := x.property
        simp_rw [Set.Ioi, Set.mem_setOf_eq] at x_pos
        refine ⟨?_, by linarith, by linarith, by linarith⟩
        have log_num_pos: 0 < log (1 + ε) := by
          exact Real.log_pos (by linarith)
        have log_denom_pos: 0 < log x := by
          exact Real.log_pos x.property
        positivity
      tactic =>
        have pos := Real.log_pos (x.property)
        linarith

    conv =>
      arg 1
      intro x
      equals ↑x * (log ↑x * ((1 + ε) * (1 - d)) -
          (1 + log (1 + ε) / log ↑x) * ((1 + d) * log ↑x)) /
        (log ↑x * ((1 + log (1 + ε) / log ↑x) * log ↑x)) =>
        ring

    simp only [mul_div_mul_comm]
    conv =>
      arg 1
      intro x
      rw [mul_comm]

    apply Filter.Tendsto.pos_mul_atTop (C := (1 + ε) * (1 - d) - (1 + d))
    · simp only [d, sub_pos]
      field_simp
      ring_nf
      rw [add_assoc]
      rw [add_lt_add_iff_left]
      apply lt_of_sub_pos
      ring_nf
      positivity
    · conv =>
        arg 1
        intro x
        lhs
        rhs
        equals (log x.val) * ((1 + log (1 + ε) / log ↑x) * ((1 + d))) =>
          ring

      simp_rw [← mul_sub]
      conv =>
        arg 1
        intro x
        rhs
        rw [mul_comm]

      simp only [mul_div_mul_comm]
      conv =>
        arg 1
        intro x
        lhs
        equals 1 =>
          have log_pos := Real.log_pos x.property
          field_simp

      simp only [one_mul]
      conv =>
        arg 3
        equals nhds (((1 + ε) * (1 - d) - (1 + d)) / 1) => simp

      apply Filter.Tendsto.div
      · apply Filter.Tendsto.sub
        · simp
        · conv =>
            arg 3
            equals nhds (1 * (1 + d)) => simp
          apply Filter.Tendsto.mul
          · conv =>
              arg 3
              equals nhds (1 + 0) => simp
            apply Filter.Tendsto.add
            · simp
            · apply Filter.Tendsto.div_atTop (a := log (1 + ε))
              · simp
              · simp only [tendsto_comp_val_Ioi_atTop]
                exact tendsto_log_atTop
          · simp
      · conv =>
          arg 3
          equals nhds (1 + 0) => simp
        apply Filter.Tendsto.add
        · simp
        · apply Filter.Tendsto.div_atTop (a := log (1 + ε))
          · simp
          · simp only [tendsto_comp_val_Ioi_atTop]
            exact tendsto_log_atTop
      · simp
    · let x_div_log (x: ℝ) := x / Real.log x
      conv =>
        arg 1
        equals (fun (x : Set.Ioi 1) => x_div_log x.val) => rfl

      rw [Filter.tendsto_comp_val_Ioi_atTop (a := 1)]
      exact x_log_x_atTop

/- Upstream blueprint metadata (inert):
@[blueprint
  (title := "prime-between")
  (statement := /-- For every $\eps>0$, there is a prime between $x$ and $(1+\eps)x$ for
  all sufficiently large $x$. -/)
  (proof := /-- Use Corollary \ref{pi_alt} to show that $\pi((1+\eps)x) - \pi(x)$ goes to infinity
  as $x \to \infty$. -/)
  (latexEnv := "corollary")]
-/
theorem prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x := by
  have squeeze := tendsto_by_squeeze (ε/2) (by linarith)
  rw [Filter.tendsto_iff_forall_eventually_mem] at squeeze
  specialize squeeze (Set.Ici 1) (by exact Ici_mem_atTop 1)
  simp only [Set.mem_Ici, eventually_atTop] at squeeze
  obtain ⟨a, ha⟩ := squeeze
  rw [eventually_atTop]
  use (max a 1)
  intro b hb
  rw [sup_le_iff] at hb
  specialize ha b hb.1

  have val_lt : (⌊b⌋₊.primeCounting : ℝ) < ⌊(1 + ε/2) * b⌋₊.primeCounting := by linarith
  norm_cast at val_lt

  have jump := prime_in_gap b ((1 + ε/2) * b) (by linarith) val_lt
  obtain ⟨p, hp, b_lt_p, p_le⟩ := jump
  have p_lt: p < (1 + ε) * b := by
    linarith
  use p


/- Upstream blueprint metadata (inert):
@[blueprint
  "mun"
  (statement := /-- We have $|\sum_{n \leq x} \frac{\mu(n)}{n}| \leq 1$. -/)
  (proof := /--
  From M\"obius inversion $1_{n=1} = \sum_{d|n} \mu(d)$ and summing we have
    $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
    for any $x \geq 1$. Since $\lfloor \frac{x}{d} \rfloor = \frac{x}{d} - \epsilon_d$ with
    $0 \leq \epsilon_d < 1$ and $\epsilon_x = 0$, we conclude that
    $$ 1 ≥ x \sum_{d \leq x} \frac{\mu(d)}{d} - (x - 1)$$
    and the claim follows.
  -/)
  (latexEnv := "proposition")]
-/
theorem sum_mobius_div_self_le (N : ℕ) : |∑ n ∈ range N, μ n / (n : ℚ)| ≤ 1 := by
  cases N with
  | zero => simp only [range_zero, sum_empty, abs_zero, zero_le_one]
  | succ N =>
  /- simple cases -/
  obtain rfl | hN := N.eq_zero_or_pos
  · simp
  /- annoying case -/
  have h_sum : 1 = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1),
      μ d * Int.fract (N / d : ℚ) := calc
    (1 : ℚ) = ∑ m ∈ Ioc 0 N, ∑ d ∈ m.divisors, μ d := by
      have (x : ℕ) (hx : x ∈ Ioc 0 N) : ∑ d ∈ divisors x, μ d = if x = 1 then 1 else 0 := by
        rw [mem_Ioc] at hx
        rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
      rw [sum_congr rfl this]
      simp [hN.ne']
    _ = ∑ d ∈ range (N + 1), μ d * (N / d : ℕ) := by
      simp_rw [← coe_mul_zeta_apply, ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
      rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (add_one_pos _),
        sum_insert (by simp), Ico_add_one_add_one_eq_Ioc]
      simp
    _ = ∑ d ∈ range (N + 1), (μ d : ℚ) * ⌊(N / d : ℚ)⌋ := by
      simp_rw [Rat.floor_natCast_div_natCast]
      simp [← Int.natCast_ediv]
    _ = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1),
        μ d * Int.fract (N / d : ℚ) := by
      simp_rw [sum_mul, ← sum_sub_distrib, mul_comm_div, ← mul_sub, Int.self_sub_fract]
  rw [eq_sub_iff_add_eq, eq_comm, ← eq_div_iff (by norm_num [Nat.pos_iff_ne_zero.mp hN])] at h_sum

  /- Next, we establish bounds for the error term -/
  have hf' (d : ℕ) : |Int.fract ((N : ℚ) / d)| < 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact Int.fract_lt_one _
  have h_bound : |∑ d ∈ range (N + 1), μ d * Int.fract ((N : ℚ) / d)| ≤ N - 1 := by
    /- range (N + 1) → Icc 1 N + part that evals to 0 -/
    rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (by simp), sum_insert (by simp),
      ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, zero_add,
      Finset.Ico_add_one_right_eq_Icc, zero_add]
    /- Ico 1 (N + 1) → Ico 1 N ∪ {N + 1} that evals to 0 -/
    rw [← Ico_insert_right hN, sum_insert (by simp), div_self (by simp; grind), Int.fract_one,
      mul_zero, zero_add]
    /- bound sum -/
    have (d : ℕ) : |μ d * Int.fract ((N : ℚ) / d)| ≤ 1 := by
      rw [abs_mul, ← one_mul 1]
      refine mul_le_mul ?_ (hf' _).le (abs_nonneg _) zero_le_one
      norm_cast
      exact abs_moebius_le_one
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum fun d _ ↦ this d).trans
    simp [cast_sub (one_le_iff_ne_zero.mpr hN.ne')]

  rw [h_sum, abs_le]
  rw [abs_le, neg_sub] at h_bound
  constructor
  <;> simp only [le_div_iff₀, div_le_iff₀, cast_pos.mpr hN]
  <;> linarith [h_bound.left]



lemma sum_mobius_mul_floor (x : ℝ) (hx : 1 ≤ x) :
  ∑ n ∈ Iic ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) * (⌊x/n⌋ : ℝ) = 1 := by
  norm_cast
  convert ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum μ ⌊x⌋₊ |>.symm using 1
  · rw [Iic_eq_Icc, bot_eq_zero, ← add_sum_Ioc_eq_sum_Icc (by simp)]
    simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, div_zero, Int.floor_zero, mul_zero,
      zero_add, Int.natCast_ediv]
    refine sum_congr rfl fun n hn ↦ ?_
    congr
    norm_cast
    rw [← floor_div_natCast, Int.natCast_floor_eq_floor]
    positivity
  · simpa [moebius_mul_coe_zeta, one_apply]


noncomputable def mu_log : ArithmeticFunction ℝ :=
    ⟨(fun n ↦ μ n * ArithmeticFunction.log n), (by simp)⟩

lemma mu_log_apply (n : ℕ) : mu_log n = μ n * ArithmeticFunction.log n := by
  rfl

lemma mu_log_mul_zeta : mu_log * ArithmeticFunction.zeta = -Λ := by
  ext n
  rw [coe_mul_zeta_apply]
  simp_rw [mu_log_apply]
  rw [sum_moebius_mul_log_eq]
  rfl

lemma mu_log_eq_mu_mul_neg_lambda : mu_log = μ * -Λ := by
  rw [← mu_log_mul_zeta, mul_comm, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

lemma sum_mu_Lambda (x : ℝ) : ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ) * log n = - ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x/k) := by
  rw [Iic_eq_Icc, bot_eq_zero, ← add_sum_Ioc_eq_sum_Icc (by simp), ← add_sum_Ioc_eq_sum_Icc (by simp)]
  simp only [ArithmeticFunction.map_zero, Int.cast_zero, CharP.cast_eq_zero, log_zero, mul_zero,
    zero_add, div_zero, zero_mul]
  simp_rw [← log_apply, ← mu_log_apply, mu_log_eq_mu_mul_neg_lambda]
  rw [sum_Ioc_mul_eq_sum_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun n hn ↦ ?_
  simp_rw [ArithmeticFunction.neg_apply, sum_neg_distrib]
  ring_nf
  congr 2
  unfold Psi
  congr
  rw [← floor_div_natCast]
  rfl

lemma M_log_identity (x : ℝ) (hx : 1 ≤ x) : M x * log x = ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (log (x/k) - Psi (x/k)) := by
  have h_log_identity : ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k) = (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x - ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k := by
    rw [Finset.sum_mul _ _ _]
    rw [← Finset.sum_sub_distrib] ; refine Finset.sum_congr rfl fun i hi => ?_ ; by_cases hi' : i = 0 <;> simp +decide [*, Real.log_div, ne_of_gt (zero_lt_one.trans_le hx)] ; ring
  generalize_proofs at *
  have h_log_identity' : ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k = -∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
    convert sum_mu_Lambda x using 1
  have h_psi_identity :
      (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k)) =
        -∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k := by
    simpa [neg_neg] using (congrArg Neg.neg h_log_identity').symm
  unfold M
  symm
  calc
    (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - Psi (x / k))) =
        (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
          simp [mul_sub, Finset.sum_sub_distrib]
    _ = ((∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
          simp [h_log_identity]
    _ = ((∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) -
          (-∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) := by
          simp [h_psi_identity]
    _ = (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x := by ring

noncomputable def R (x : ℝ) : ℝ := Psi x - x

lemma R_isLittleO : R =o[atTop] id := by
  have h_pnt : (fun x => Psi x - x) =o[atTop] (fun x => x) := by
    have h_psi : (fun x => Psi x) ~[atTop] (fun x => x) := by
      simpa [Psi] using! WeakPNT''
    exact h_psi
  convert! h_pnt using 1

lemma sum_mobius_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) =O[atTop] id := by
  have h_abs : ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ) / n| ≤ 1 := by
    intros x hx
    have h_sum : ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ) / n = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ) / n := by
      rw [Finset.range_eq_Ico] ; rfl
    have := sum_mobius_div_self_le (⌊x⌋₊ + 1) ; simp_all +decide [Finset.sum_range_succ']
    norm_cast at *
  rw [Asymptotics.isBigO_iff]
  use 1; filter_upwards [Filter.eventually_ge_atTop 1] with x hx; simp_all +decide [div_eq_mul_inv, mul_assoc, mul_comm]
  simpa only [← Finset.mul_sum _ _ _, abs_mul] using mul_le_of_le_one_right (abs_nonneg x) (h_abs x hx)

lemma sum_log_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, log (x / k)) =O[atTop] id := by
  have h_sum_log : ∀ x : ℝ, 1 ≤ x → |∑ k ∈ Finset.Iic ⌊x⌋₊, Real.log (x / k)| ≤ 2 * x := by
    have h_sum_log_le_x : ∀ x : ℝ, 1 ≤ x → ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) ≤ x := by
      intro x hx
      have h_sum_log : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / (k : ℝ)) ≤ Real.log (x ^ ⌊x⌋₊ / Nat.factorial ⌊x⌋₊) := by
        rw [← Real.log_prod]
        · norm_num [Finset.prod_div_distrib]
          erw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
        · exact fun n hn => div_ne_zero (by positivity) (Nat.cast_ne_zero.mpr <| by linarith [Finset.mem_Icc.mp hn])
      have h_exp_bound : x ^ ⌊x⌋₊ / Nat.factorial ⌊x⌋₊ ≤ Real.exp x := by
        have h_term : x ^ ⌊x⌋₊ / (⌊x⌋₊! : ℝ) ≤ ∑' k : ℕ, x ^ k / (k ! : ℝ) := by
          exact Summable.le_tsum (show Summable _ from Real.summable_pow_div_factorial x) ⌊x⌋₊ (fun _ _ => by positivity)
        simpa [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div] using h_term
      exact h_sum_log.trans (Real.log_le_iff_le_exp (by positivity) |>.2 h_exp_bound)
    intros x hx
    have h_sum_eq : ∑ k ∈ Finset.Iic ⌊x⌋₊, Real.log (x / k) = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) := by
      erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
      erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
    rw [abs_of_nonneg] <;> linarith [h_sum_log_le_x x hx, show 0 ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) from Finset.sum_nonneg fun _ _ => Real.log_nonneg <| by rw [le_div_iff₀ <| Nat.cast_pos.mpr <| by linarith [Finset.mem_Icc.mp ‹_›]] ; linarith [Nat.floor_le <| show 0 ≤ x by linarith, show (↑‹ℕ› : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast Finset.mem_Icc.mp ‹_› |>.2]]
  rw [Asymptotics.isBigO_iff]
  exact ⟨2, Filter.eventually_atTop.mpr ⟨1, fun x hx => le_trans (h_sum_log x hx) (by norm_num [abs_of_nonneg (by linarith : 0 ≤ x)])⟩⟩

lemma R_locally_bounded (K : ℝ) (hK : 0 ≤ K) : ∃ C, ∀ y ∈ Set.Icc 0 K, |R y| ≤ C := by
  have hR_bounded : BddAbove (Set.image (fun y => |R y|) (Set.Icc 0 K)) := by
    have hR_bounded : ∀ y ∈ Set.Icc 0 K, |R y| ≤ ∑ p ∈ Iic ⌊K⌋₊, log p + K := by
      intro y hy
      simp only [R, Psi, Chebyshev.psi_eq_sum_Icc]
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · refine le_trans (sub_le_self _ hy.1) ?_
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr <| Nat.floor_mono hy.2) fun ?_ ?_ ?_ => ?_) ?_
        · exact vonMangoldt_nonneg
        · refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i hi => ?_) hK
          exact vonMangoldt_le_log
      · refine le_trans ?_ (le_add_of_nonneg_left ?_)
        · exact le_trans (sub_le_self _ <| Finset.sum_nonneg fun _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg) hy.2
        · exact Finset.sum_nonneg fun _ _ => Real.log_natCast_nonneg _
    exact ⟨_, Set.forall_mem_image.2 hR_bounded⟩
  exact ⟨hR_bounded.choose, fun y hy => hR_bounded.choose_spec <| Set.mem_image_of_mem _ hy⟩

lemma sum_bounded_of_linear_bound {f : ℝ → ℝ} {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C) (h : ∀ y, 1 ≤ y → |f y| ≤ ε * y + C) (x : ℝ) (hx : 1 ≤ x) :
  ∑ k ∈ Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x * (log x + 1) + C * x := by
    have h_sum_bound : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x * ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ)) + C * ⌊x⌋₊ := by
      have h_sum_bound : ∀ k ∈ Finset.Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x / k + C := by
        exact fun k hk => by simpa only [mul_div_assoc] using! h (x / k) (by rw [le_div_iff₀ (Nat.cast_pos.mpr <| Finset.mem_Icc.mp hk |>.1)] ; nlinarith [Nat.floor_le (show 0 ≤ x by positivity), show (k : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast Finset.mem_Icc.mp hk |>.2])
      convert! Finset.sum_le_sum h_sum_bound using 1 ; norm_num [div_eq_mul_inv, Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_comm]
    have h_harmonic : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ)) ≤ Real.log n + 1 := by
      intro n _hn
      have h := harmonic_le_one_add_log n
      simpa [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        one_div, add_comm, add_left_comm, add_assoc] using h
    have h_harmonic_x :
        ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ)) ≤ Real.log x + 1 := by
      refine (h_harmonic _ <| Nat.floor_pos.mpr hx).trans ?_
      have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
        refine Real.log_le_log (Nat.cast_pos.mpr <| Nat.floor_pos.mpr hx) ?_
        exact Nat.floor_le (by positivity)
      simpa using add_le_add_right hlog 1
    have h_term1 : ε * x * (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ))) ≤ ε * x * (Real.log x + 1) := by
      refine mul_le_mul_of_nonneg_left h_harmonic_x ?_
      exact mul_nonneg hε (by positivity)
    have h_term2 : C * (⌊x⌋₊ : ℝ) ≤ C * x := by
      refine mul_le_mul_of_nonneg_left ?_ hC
      exact Nat.floor_le (by positivity)
    exact h_sum_bound.trans (add_le_add h_term1 h_term2)

lemma sum_abs_R_isLittleO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * log x) := by
  have h_eps : ∀ ε > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀, (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) ≤ ε * x * Real.log x := by
    intro ε hε_pos
    obtain ⟨A, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ y ≥ A, |R y| ≤ (ε / 2) * y := by
      have := R_isLittleO
      rw [Asymptotics.isLittleO_iff] at this
      norm_num at *
      exact Exists.elim (this (half_pos hε_pos)) fun A hA => ⟨Max.max A 1, by positivity, fun y hy => by simpa only [abs_of_nonneg (by linarith [le_max_right A 1] : 0 ≤ y)] using hA y (le_trans (le_max_left A 1) hy)⟩
    obtain ⟨C_A, hC_A⟩ : ∃ C_A : ℝ, ∀ y ∈ Set.Icc 0 A, |R y| ≤ C_A := by
      exact ⟨_, fun y hy => R_locally_bounded A hA.1.le |> Classical.choose_spec |> fun h => h y hy⟩
    have h_sum_bound : ∀ x ≥ max A 2, (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) ≤ (ε / 2) * x * (Real.log x + 1) + C_A * x := by
      intros x hx
      have h_sum_bound : ∀ y ≥ 1, |R y| ≤ (ε / 2) * y + C_A := by
        intros y hy
        by_cases hyA : y ≥ A
        · exact le_add_of_le_of_nonneg (hA.right y hyA) (by
          exact le_trans (abs_nonneg _) (hC_A 0 ⟨by norm_num, by linarith⟩))
        · exact le_add_of_nonneg_of_le (by
          positivity) (hC_A y ⟨by
          linarith, by
            linarith⟩)
      have := sum_bounded_of_linear_bound (show 0 ≤ ε / 2 by positivity) (show 0 ≤ C_A by exact le_trans (abs_nonneg _) (hC_A 0 ⟨by norm_num, by linarith⟩)) (fun y hy => h_sum_bound y hy) x (by linarith [le_max_right A 2]) ; aesop
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, (ε / 2) * (Real.log x + 1) + C_A ≤ ε * Real.log x := by
      exact ⟨Real.exp (2 * (C_A / ε + 1)), fun x hx => by nlinarith [Real.log_exp (2 * (C_A / ε + 1)), Real.log_le_log (by positivity) hx, mul_div_cancel₀ C_A hε_pos.ne']⟩
    exact ⟨Max.max x₀ (Max.max A 2), fun x hx => le_trans (h_sum_bound x (le_trans (le_max_right _ _) hx)) (by nlinarith [hx₀ x (le_trans (le_max_left _ _) hx), le_max_right x₀ (Max.max A 2), le_max_left x₀ (Max.max A 2), le_max_right A 2, le_max_left A 2, Real.log_nonneg (show x ≥ 1 by linarith [le_max_right x₀ (Max.max A 2), le_max_left x₀ (Max.max A 2), le_max_right A 2, le_max_left A 2])])⟩
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have h_sum_eq : ∀ x : ℝ, x ≥ 1 → (∑ k ∈ Finset.Iic ⌊x⌋₊, |R (x / k)|) = (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) := by
      intro x hx
      have h0 : (0 : ℕ) ∈ Finset.Iic ⌊x⌋₊ := by simp [Finset.mem_Iic]
      have hI : (Finset.Iic ⌊x⌋₊).erase 0 = Finset.Icc 1 ⌊x⌋₊ := by
        ext n
        simp [Finset.mem_Iic, Finset.mem_Icc, Nat.one_le_iff_ne_zero, and_comm]
      rw [← Finset.sum_erase_add (Finset.Iic ⌊x⌋₊) (fun k => |R (x / k)|) h0]
      simp [hI, R, Psi, Chebyshev.psi_eq_sum_Icc]
    rw [Metric.tendsto_nhds]
    simp +zetaDelta only [gt_iff_lt, ge_iff_le, dist_zero_right, norm_div, norm_eq_abs, norm_mul,
    eventually_atTop] at *
    intro ε hε; obtain ⟨x₀, hx₀⟩ := h_eps (ε / 2) (half_pos hε) ; use Max.max x₀ 2; intro x hx; rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _), abs_of_nonneg (by linarith [le_max_right x₀ 2]), abs_of_nonneg (Real.log_nonneg (by linarith [le_max_right x₀ 2]))] ; rw [div_lt_iff₀] <;> nlinarith [hx₀ x (le_trans (le_max_left x₀ 2) hx), Real.log_pos (by linarith [le_max_right x₀ 2] : 1 < x), mul_pos (by linarith [le_max_right x₀ 2] : 0 < x) (Real.log_pos (by linarith [le_max_right x₀ 2] : 1 < x)), h_sum_eq x (by linarith [le_max_right x₀ 2])]
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using absurd hx' (by nlinarith [Real.log_pos hx])

lemma R_linear_bound (ε : ℝ) (hε : 0 < ε) : ∃ C, 0 ≤ C ∧ ∀ y, 1 ≤ y → |R y| ≤ ε * y + C := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, A ≤ y → |R y| ≤ ε * y := by
    have := R_isLittleO.def hε
    rw [Filter.eventually_atTop] at this; rcases this with ⟨A, hA⟩ ; exact ⟨Max.max A 1, by positivity, fun y hy => by simpa [abs_of_nonneg (show 0 ≤ y by linarith [le_max_right A 1])] using hA y (le_trans (le_max_left A 1) hy)⟩
  obtain ⟨CA, hCA⟩ : ∃ CA : ℝ, ∀ y ∈ Set.Icc 0 A, |R y| ≤ CA := by
    exact R_locally_bounded A hA.1.le |> fun ⟨CA, hCA⟩ => ⟨CA, fun y hy => hCA y hy⟩
  exact ⟨Max.max CA 0, by positivity, fun y hy => if hy' : y ≤ A then le_trans (hCA y ⟨by linarith, by linarith⟩) (by linarith [le_max_left CA 0, le_max_right CA 0, show 0 ≤ ε * y by nlinarith]) else le_trans (hA.2 y (by linarith)) (by linarith [le_max_left CA 0, le_max_right CA 0, show 0 ≤ ε * y by nlinarith])⟩

lemma sum_abs_R_isLittleO' : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * log x) := by
  apply sum_abs_R_isLittleO

lemma M_isLittleO : M =o[atTop] id := by
  have h_identity : ∀ x ≥ 1, M x * Real.log x = ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - Psi (x / k)) := by
    exact fun x a => M_log_identity x a
  have h_term1 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) =O[atTop] id := by
    have h_abs : ∀ x ≥ 1, |∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)| ≤ ∑ k ∈ Iic ⌊x⌋₊, Real.log (x / k) := by
      intros x hx
      have h_abs : ∀ k ∈ Iic ⌊x⌋₊, |(μ k : ℝ) * Real.log (x / k)| ≤ Real.log (x / k) := by
        intros k hk
        have h_abs : |(μ k : ℝ)| ≤ 1 := by
          norm_num [ArithmeticFunction.moebius]
          split_ifs <;> norm_num
        by_cases hk0 : k = 0
        · rw [hk0] ; norm_num [ArithmeticFunction.map_zero, Nat.cast_zero, Real.log_zero, div_zero, abs_zero]
        · have hx_pos : 0 < x := by positivity
          have hk_pos : 0 < (k : ℝ) := by positivity
          rw [Real.log_div hx_pos.ne' hk_pos.ne']
          simp only [abs_mul, ge_iff_le]
          simp_all only [ge_iff_le, mem_Iic]
          exact le_trans (mul_le_of_le_one_left (abs_nonneg _) h_abs) (by rw [abs_of_nonneg] ; exact sub_nonneg_of_le <| Real.log_le_log hk_pos (Nat.cast_le.mpr hk |>.trans (Nat.floor_le hx_pos.le)))
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_abs)
    have h_sum_log : (fun x => ∑ k ∈ Iic ⌊x⌋₊, Real.log (x / k)) =O[atTop] id := by
      convert sum_log_div_isBigO using 1
    rw [Asymptotics.isBigO_iff] at *
    exact ⟨h_sum_log.choose, by filter_upwards [h_sum_log.choose_spec, Filter.eventually_ge_atTop 1] with x hx₁ hx₂ using le_trans (h_abs x hx₂) (le_trans (le_abs_self _) hx₁)⟩
  have h_term2 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) =O[atTop] id := by
    convert sum_mobius_div_isBigO using 1
  have h_term3 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)) =o[atTop] (fun x => x * Real.log x) := by
    have h_abs : ∀ x ≥ 1, |∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)| ≤ ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)| := by
      intros x hx
      have h_abs : ∀ k ∈ Iic ⌊x⌋₊, |(μ k : ℝ) * R (x / k)| ≤ |R (x / k)| := by
        norm_num [abs_mul]
        intro k hk; exact mul_le_of_le_one_left (abs_nonneg _) (mod_cast by exact abs_moebius_le_one)
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_abs)
    have h_sum_abs_R : (fun x => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * Real.log x) := by
      exact sum_abs_R_isLittleO
    rw [Asymptotics.isLittleO_iff] at *
    intro c hc; filter_upwards [h_sum_abs_R hc, Filter.eventually_ge_atTop 1] with x hx₁ hx₂; exact le_trans (h_abs x hx₂) (le_trans (le_abs_self _) hx₁)
  have h_combined : (fun x => M x * Real.log x) =o[atTop] (fun x => x * Real.log x) := by
    have h_combined : (fun x => M x * Real.log x) = (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) - (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) - (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)) := by
      ext x; by_cases hx : 1 ≤ x <;> simp_all +decide only [ge_iff_le, mul_sub, sum_sub_distrib, not_le, Pi.sub_apply]
      · simp +decide [sub_sub, mul_sub, Finset.sum_sub_distrib, Psi, R]
      · unfold M R; norm_num [Nat.floor_eq_zero.mpr hx]
        norm_num [Finset.Iic_eq_Icc]
    rw [h_combined]
    refine Asymptotics.IsLittleO.sub ?_ h_term3
    refine Asymptotics.IsLittleO.sub ?_ ?_
    · refine h_term1.trans_isLittleO ?_
      rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
      · norm_num [← div_div]
        exact le_trans (Filter.Tendsto.div_atTop (tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with x hx; aesop)) (Real.tendsto_log_atTop)) (by norm_num)
      · exact ⟨2, by rintro x hx (rfl | rfl | rfl) <;> norm_num at hx⟩
    · refine h_term2.trans_isLittleO ?_
      rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
      · norm_num [← div_div]
        exact le_trans (Filter.Tendsto.div_atTop (tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with x hx; aesop)) (Real.tendsto_log_atTop)) (by norm_num)
      · exact ⟨2, by rintro x hx (rfl | rfl | rfl) <;> linarith⟩
  rw [Asymptotics.isLittleO_iff_tendsto'] at *
  · refine h_combined.congr' (by filter_upwards [Filter.eventually_gt_atTop 1] with x hx using by rw [mul_div_mul_right _ _ (ne_of_gt <| Real.log_pos hx)] ; rfl)
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using absurd hx' <| ne_of_gt <| mul_pos (by positivity) <| Real.log_pos hx
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using by nlinarith [Real.log_pos hx]
  · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'

end
