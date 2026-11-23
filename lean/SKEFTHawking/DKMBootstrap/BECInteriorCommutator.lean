import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Compact interior one-particle BEC commutator

The carrier is the actual smooth compact test space on `Ioo l r`, extended by zero to ℝ.
The kinetic operator uses ordinary real derivatives. All compositions preserve this carrier.
This is an interior differential domain, with no assertion about self-adjoint wall realizations,
operator cores, spectral powers, thermal moments, or the interacting Fock-space lift.
-/

noncomputable section

open Set MeasureTheory
open scoped Distributions ContDiff

namespace SKEFTHawking.DKMBootstrap.BECInteriorCommutator

abbrev Domain (l r : ℝ) := TestFunction (⟨Ioo l r, isOpen_Ioo⟩) ℂ ⊤

variable {l r : ℝ}

/-- The genuine first real derivative, bundled with its inherited interior support. -/
def D : Domain l r →ₗ[ℂ] Domain l r where
  toFun ψ :=
    { toFun := deriv ψ
      contDiff' := ψ.contDiff.deriv' (n := ∞)
      hasCompactSupport' := ψ.hasCompactSupport.deriv
      tsupport_subset' := tsupport_deriv_subset.trans ψ.tsupport_subset }
  map_add' ψ φ := by
    ext x
    exact deriv_add (ψ.contDiff.differentiable (by simp)).differentiableAt
      (φ.contDiff.differentiable (by simp)).differentiableAt
  map_smul' b ψ := by
    ext x
    exact deriv_const_mul b (ψ.contDiff.differentiable (by simp)).differentiableAt

@[simp] theorem D_apply (ψ : Domain l r) (x : ℝ) : D ψ x = deriv ψ x := rfl

/-- Multiplication by a globally smooth coefficient preserves compact interior support. -/
def mulOp (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) : Domain l r →ₗ[ℂ] Domain l r where
  toFun ψ :=
    { toFun := fun x ↦ f x * ψ x
      contDiff' := hf.mul ψ.contDiff
      hasCompactSupport' := ψ.hasCompactSupport.mul_left
      tsupport_subset' := tsupport_mul_subset_right.trans ψ.tsupport_subset }
  map_add' ψ φ := by ext x; exact mul_add _ _ _
  map_smul' b ψ := by ext x; exact mul_left_comm _ _ _

@[simp] theorem mulOp_apply (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (ψ : Domain l r) (x : ℝ) : mulOp f hf ψ x = f x * ψ x := rfl

/-- The one-particle differential Hamiltonian on the invariant interior test space. -/
def kinetic (a : ℝ) (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    Domain l r →ₗ[ℂ] Domain l r :=
  -(a : ℂ) • (D.comp D) + mulOp V hV

/-- The bracket is defined by the two actual compositions. -/
def commutator (a : ℝ) (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hf : ContDiff ℝ ∞ f) : Domain l r →ₗ[ℂ] Domain l r :=
  (kinetic a V hV).comp (mulOp f hf) - (mulOp f hf).comp (kinetic a V hV)

/-- The ordinary product rule, expressed in the same bundled domain. -/
theorem D_mul (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (ψ : Domain l r) :
    D (mulOp f hf ψ) = mulOp (deriv f) hf.deriv' ψ + mulOp f hf (D ψ) := by
  ext x
  exact deriv_mul (hf.differentiable (by simp)).differentiableAt
    (ψ.contDiff.differentiable (by simp)).differentiableAt

/-- Twice differentiating the actual product supplies every term, including f''. -/
theorem D2_mul (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (ψ : Domain l r) :
    D (D (mulOp f hf ψ)) =
      mulOp (deriv (deriv f)) hf.deriv'.deriv' ψ +
      (2 : ℂ) • mulOp (deriv f) hf.deriv' (D ψ) + mulOp f hf (D (D ψ)) := by
  rw [D_mul, map_add, D_mul, D_mul]
  ext x
  simp only [add_apply, smul_apply, mulOp_apply, smul_eq_mul]
  ring

/-- Actual compact-interior differential bracket; the potential cancels by multiplication. -/
theorem commutator_action (a : ℝ) (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hf : ContDiff ℝ ∞ f) (ψ : Domain l r) :
    commutator a V f hV hf ψ =
      -(a : ℂ) • ((2 : ℂ) • mulOp (deriv f) hf.deriv' (D ψ) +
        mulOp (deriv (deriv f)) hf.deriv'.deriv' ψ) := by
  have h := D2_mul f hf ψ
  ext x
  have hx := congrArg (fun u : Domain l r ↦ u x) h
  simp only [commutator, kinetic, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, sub_apply,
    add_apply, smul_apply, mulOp_apply, smul_eq_mul] at *
  rw [hx]
  ring

/-- Pointwise identification with the familiar first-order differential expression. -/
theorem commutator_apply (a : ℝ) (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hf : ContDiff ℝ ∞ f) (ψ : Domain l r) (x : ℝ) :
    commutator a V f hV hf ψ x =
      -(a : ℂ) * (2 * deriv f x * deriv ψ x + deriv (deriv f) x * ψ x) := by
  rw [commutator_action]
  simp only [smul_apply, add_apply, mulOp_apply, D_apply, smul_eq_mul]
  ring

/-- Unit-modulus phase at the physical real coordinate. -/
def phase (q x : ℝ) : ℂ := Complex.exp ((q : ℂ) * x * Complex.I)

theorem phase_smooth (q : ℝ) : ContDiff ℝ ∞ (phase q) := by
  have h : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
  exact ((contDiff_const.mul h).mul contDiff_const).cexp

/-- Modulation stays in precisely the same compact interior test space. -/
def modulate (q : ℝ) : Domain l r →ₗ[ℂ] Domain l r := mulOp (phase q) (phase_smooth q)

theorem phase_deriv (q x : ℝ) :
    deriv (phase q) x = (q : ℂ) * Complex.I * phase q x := by
  change deriv (fun y : ℝ ↦ Complex.exp ((q : ℂ) * y * Complex.I)) x = _
  have h := ((((hasDerivAt_id (x : ℂ)).const_mul (q : ℂ)).mul_const
    Complex.I).cexp).comp_ofReal.deriv
  simpa only [phase, mul_one, id_eq] using h.trans (mul_comm _ _)

/-- The packet identity follows from the proved bracket and actual phase derivative. -/
theorem commutator_modulate (a q : ℝ) (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hf : ContDiff ℝ ∞ f) (χ : Domain l r) :
    commutator a V f hV hf (modulate q χ) =
      modulate q (commutator a V f hV hf χ -
        (2 * (a : ℂ) * Complex.I * q) • mulOp (deriv f) hf.deriv' χ) := by
  ext x
  rw [commutator_apply]
  have hd := congrArg (fun u : Domain l r ↦ u x) (D_mul (phase q) (phase_smooth q) χ)
  simp only [D_apply, mulOp_apply, add_apply] at hd
  change _ = phase q x * (_ - _)
  rw [show deriv (modulate q χ) x =
      deriv (phase q) x * χ x + phase q x * deriv χ x from hd]
  rw [phase_deriv, commutator_apply]
  change _ = phase q x * (_ - (2 * (a : ℂ) * Complex.I * q) * (deriv f x * χ x))
  change -(a : ℂ) * (2 * deriv f x * _ + deriv (deriv f) x * (phase q x * χ x)) = _
  ring

/-- Conservation control on the same domain for any constant observable. -/
theorem constant_control (a : ℝ) (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (b : ℂ) (ψ : Domain l r) :
    commutator a V (fun _ ↦ b) hV contDiff_const ψ = 0 := by
  ext x
  rw [commutator_apply]
  simp

/-- The physical one-dimensional Lebesgue L² carrier (zero extension outside the interval). -/
abbrev Hilbert : Type := Lp ℂ 2 (volume : Measure ℝ)

theorem memL2 (ψ : Domain l r) : MemLp ψ 2 (volume : Measure ℝ) :=
  ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport

/-- Actual linear inclusion of compact interior functions into Lebesgue L². -/
def toL2 : Domain l r →ₗ[ℂ] Hilbert where
  toFun ψ := (memL2 ψ).toLp ψ
  map_add' ψ φ := (memL2 ψ).toLp_add (memL2 φ)
  map_smul' b ψ := (memL2 ψ).toLp_const_smul b

theorem toL2_ae (ψ : Domain l r) : (toL2 ψ : ℝ → ℂ) =ᵐ[volume] ψ :=
  (memL2 ψ).coeFn_toLp

/-- Continuity upgrades Lebesgue a.e. equality to equality of the actual tests. -/
theorem toL2_injective : Function.Injective (toL2 : Domain l r → Hilbert) := by
  intro ψ φ h
  have he : (ψ : ℝ → ℂ) =ᵐ[volume] φ :=
    (toL2_ae ψ).symm.trans ((Filter.EventuallyEq.of_eq (congrArg
      (fun u : Hilbert ↦ (u : ℝ → ℂ)) h)).trans (toL2_ae φ))
  exact TestFunction.ext (congrFun ((ψ.continuous.ae_eq_iff_eq volume φ.continuous).mp he))

theorem phase_norm (q x : ℝ) : ‖phase q x‖ = 1 := by
  simpa only [phase, ← Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I (q * x)

/-- Modulation is an isometry for the actual Lebesgue L² norm. -/
theorem modulate_norm (q : ℝ) (ψ : Domain l r) :
    ‖toL2 (modulate q ψ)‖ = ‖toL2 ψ‖ := by
  change ‖(memL2 (modulate q ψ)).toLp _‖ = ‖(memL2 ψ).toLp _‖
  rw [Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  apply eLpNorm_congr_norm_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    change ‖phase q x * ψ x‖ = ‖ψ x‖
    rw [norm_mul, phase_norm, one_mul])

/-- Reverse triangle bound for the derived packet response in actual L². -/
theorem packet_lower_bound (a q : ℝ) (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hf : ContDiff ℝ ∞ f) (χ : Domain l r) :
    2 * |a| * |q| * ‖toL2 (mulOp (deriv f) hf.deriv' χ)‖ -
        ‖toL2 (commutator a V f hV hf χ)‖ ≤
      ‖toL2 (commutator a V f hV hf (modulate q χ))‖ := by
  rw [commutator_modulate, modulate_norm, map_sub, map_smul]
  have hb := norm_sub_norm_le
    ((2 * (a : ℂ) * Complex.I * q) • toL2 (mulOp (deriv f) hf.deriv' χ))
    (toL2 (commutator a V f hV hf χ))
  rw [norm_sub_rev] at hb
  simpa [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc] using hb

/-- A pointwise derivative-product witness gives a strictly positive actual L² norm.
The upgrade uses continuity and the injective inclusion, not a point-mass argument. -/
theorem derivative_product_norm_pos (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (χ : Domain l r) (hne : ∃ x, deriv f x * χ x ≠ 0) :
    0 < ‖toL2 (mulOp (deriv f) hf.deriv' χ)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have he : mulOp (deriv f) hf.deriv' χ = 0 :=
    toL2_injective (by simpa using hz)
  obtain ⟨x, hx⟩ := hne
  exact hx (congrArg (fun u : Domain l r ↦ u x) he)

/-- Arbitrarily large responses on actual unit tests, under explicit packet nondegeneracy. -/
theorem no_finite_packet_bound {a : ℝ} (ha : 0 < a) (V f : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (χ : Domain l r)
    (hχ : ‖toL2 χ‖ = 1) (hne : ∃ x, deriv f x * χ x ≠ 0) (R : ℝ) :
    ∃ ψ : Domain l r, ‖toL2 ψ‖ = 1 ∧ R < ‖toL2 (commutator a V f hV hf ψ)‖ := by
  let p := ‖toL2 (mulOp (deriv f) hf.deriv' χ)‖
  have hp : 0 < p := derivative_product_norm_pos f hf χ hne
  have hc : 0 < 2 * a * p := by positivity
  obtain ⟨q, hq⟩ := exists_nat_gt ((R + ‖toL2 (commutator a V f hV hf χ)‖) /
    (2 * a * p))
  have hq' := (div_lt_iff₀ hc).mp hq
  have hb := packet_lower_bound a (q : ℝ) V f hV hf χ
  rw [abs_of_pos ha, abs_of_nonneg (Nat.cast_nonneg q)] at hb
  refine ⟨modulate q χ, (modulate_norm q χ).trans hχ, ?_⟩
  dsimp [p] at *
  nlinarith

/-- Normalize any nondegenerate compact packet; normalization is not an extra premise. -/
theorem no_domain_bound {a : ℝ} (ha : 0 < a) (V f : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (χ : Domain l r)
    (hne : ∃ x, deriv f x * χ x ≠ 0) (R : ℝ) :
    ∃ ψ : Domain l r, ‖toL2 ψ‖ = 1 ∧ R < ‖toL2 (commutator a V f hV hf ψ)‖ := by
  have hχ : χ ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := hne
    apply hx
    simp [h]
  have hn : 0 < ‖toL2 χ‖ := norm_pos_iff.mpr (by
    intro h
    exact hχ (toL2_injective (by simpa using h)))
  let b : ℂ := ((‖toL2 χ‖⁻¹ : ℝ) : ℂ)
  have hb : b ≠ 0 := by simpa [b] using inv_ne_zero hn.ne'
  have hunit : ‖toL2 (b • χ)‖ = 1 := by
    rw [map_smul, norm_smul]
    simp [b, Complex.norm_real, hn.ne']
  have hprod : ∃ x, deriv f x * (b • χ) x ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    change deriv f x * (b * χ x) ≠ 0
    rw [mul_left_comm]
    exact mul_ne_zero hb hx
  exact no_finite_packet_bound ha V f hV hf (b • χ) hunit hprod R

/-- No bounded operator on ambient Lebesgue L² extends this interior bracket. -/
theorem no_bounded_extension {a : ℝ} (ha : 0 < a) (V f : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (χ : Domain l r)
    (hne : ∃ x, deriv f x * χ x ≠ 0) :
    ¬ ∃ A : Hilbert →L[ℂ] Hilbert,
      ∀ ψ : Domain l r, A (toL2 ψ) = toL2 (commutator a V f hV hf ψ) := by
  rintro ⟨A, hA⟩
  obtain ⟨ψ, hψ, hR⟩ := no_domain_bound ha V f hV hf χ hne ‖A‖
  have hb := A.le_opNorm (toL2 ψ)
  rw [hA ψ, hψ, mul_one] at hb
  exact (not_lt_of_ge hb) hR

/-- Lebesgue L² on the physical open interval, with its restricted measure. -/
abbrev IntervalHilbert (l r : ℝ) : Type :=
  Lp ℂ 2 ((volume : Measure ℝ).restrict (Ioo l r))

/-- The actual restricted-measure inclusion of the same compact interior test functions. -/
def toIntervalL2 : Domain l r →ₗ[ℂ] IntervalHilbert l r where
  toFun ψ := ((memL2 ψ).restrict (Ioo l r)).toLp ψ
  map_add' ψ φ := ((memL2 ψ).restrict (Ioo l r)).toLp_add
    ((memL2 φ).restrict (Ioo l r))
  map_smul' b ψ := ((memL2 ψ).restrict (Ioo l r)).toLp_const_smul b

theorem toIntervalL2_ae (ψ : Domain l r) :
    (toIntervalL2 ψ : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo l r)] ψ :=
  ((memL2 ψ).restrict (Ioo l r)).coeFn_toLp

/-- Interior support makes restriction preserve the full-line norm exactly, for every test. -/
theorem toIntervalL2_norm (ψ : Domain l r) : ‖toIntervalL2 ψ‖ = ‖toL2 ψ‖ := by
  change ‖((memL2 ψ).restrict (Ioo l r)).toLp _‖ = ‖(memL2 ψ).toLp _‖
  rw [Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  exact eLpNorm_restrict_eq_of_support_subset
    ((subset_tsupport (ψ : ℝ → ℂ)).trans ψ.tsupport_subset)

/-- Injectivity follows from support and full-line injectivity, without a restricted a.e. rule. -/
theorem toIntervalL2_injective :
    Function.Injective (toIntervalL2 : Domain l r → IntervalHilbert l r) := by
  intro ψ φ h
  apply toL2_injective
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply norm_eq_zero.mp
  rw [← toIntervalL2_norm, map_sub, h, sub_self, norm_zero]

/-- The phase output has the same norm in actual interval L². -/
theorem modulate_interval_norm (q : ℝ) (ψ : Domain l r) :
    ‖toIntervalL2 (modulate q ψ)‖ = ‖toIntervalL2 ψ‖ := by
  simpa only [toIntervalL2_norm] using modulate_norm q ψ

/-- The accepted differential packet bound in the restricted interval carrier. -/
theorem packet_interval_lower_bound (a q : ℝ) (V f : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (χ : Domain l r) :
    2 * |a| * |q| * ‖toIntervalL2 (mulOp (deriv f) hf.deriv' χ)‖ -
        ‖toIntervalL2 (commutator a V f hV hf χ)‖ ≤
      ‖toIntervalL2 (commutator a V f hV hf (modulate q χ))‖ := by
  simpa only [toIntervalL2_norm] using packet_lower_bound a q V f hV hf χ

/-- A smooth compact interior packet can be chosen equal to one at any interior point. -/
theorem exists_packet_at {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo l r) :
    ∃ χ : Domain l r, χ x₀ = 1 := by
  obtain ⟨b, hb, hc, hd, _, h1⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (isOpen_Ioo.mem_nhds hx₀)
  refine ⟨{ toFun := Complex.ofReal ∘ b
            contDiff' := Complex.ofRealCLM.contDiff.comp hd
            hasCompactSupport' := hc.comp_left (g := Complex.ofReal) (by simp)
            tsupport_subset' := (tsupport_comp_subset (g := Complex.ofReal) (by simp) b).trans
              hb }, ?_⟩
  change (b x₀ : ℂ) = 1
  simp [h1]

/-- A nonzero interior derivative constructs the packet nondegeneracy used by the proof. -/
theorem exists_nondegenerate_packet (f : ℝ → ℂ) {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo l r)
    (hd : deriv f x₀ ≠ 0) :
    ∃ χ : Domain l r, deriv f x₀ * χ x₀ ≠ 0 := by
  obtain ⟨χ, hχ⟩ := exists_packet_at hx₀
  exact ⟨χ, by simpa [hχ] using hd⟩

/-- Nonconstancy on the interval forces a nonzero derivative at an interior point. -/
theorem exists_deriv_ne_zero_of_nonconstant (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x ∈ Ioo l r, ∃ y ∈ Ioo l r, f x ≠ f y) :
    ∃ x ∈ Ioo l r, deriv f x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx, y, hy, hxy⟩ := hn
  exact hxy (isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo l r).isPreconnected
    (hf.differentiable (by simp)).differentiableOn h hx hy)

/-- Nonconstancy alone supplies a compact packet; no lower bound is assumed. -/
theorem exists_nondegenerate_packet_of_nonconstant (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hn : ∃ x ∈ Ioo l r, ∃ y ∈ Ioo l r, f x ≠ f y) :
    ∃ χ : Domain l r, ∃ x, deriv f x * χ x ≠ 0 := by
  obtain ⟨x, hx, hd⟩ := exists_deriv_ne_zero_of_nonconstant f hf hn
  obtain ⟨χ, hχ⟩ := exists_nondegenerate_packet f hx hd
  exact ⟨χ, x, hχ⟩

/-- The normalized packet obstruction on actual interval-L² unit vectors. -/
theorem no_interval_bound {a : ℝ} (ha : 0 < a) (V f : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (χ : Domain l r)
    (hne : ∃ x, deriv f x * χ x ≠ 0) (R : ℝ) :
    ∃ ψ : Domain l r, ‖toIntervalL2 ψ‖ = 1 ∧
      R < ‖toIntervalL2 (commutator a V f hV hf ψ)‖ := by
  simpa only [toIntervalL2_norm] using no_domain_bound ha V f hV hf χ hne R

/-- The interval obstruction follows from a nonzero derivative at one interior point. -/
theorem no_interval_bound_of_deriv_ne_zero {a : ℝ} (ha : 0 < a) (V f : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Ioo l r) (hd : deriv f x₀ ≠ 0) (R : ℝ) :
    ∃ ψ : Domain l r, ‖toIntervalL2 ψ‖ = 1 ∧
      R < ‖toIntervalL2 (commutator a V f hV hf ψ)‖ := by
  obtain ⟨χ, hχ⟩ := exists_nondegenerate_packet f hx₀ hd
  exact no_interval_bound ha V f hV hf χ ⟨x₀, hχ⟩ R

/-- Every smooth profile nonconstant on the interval has arbitrarily large unit responses. -/
theorem no_interval_bound_of_nonconstant {a : ℝ} (ha : 0 < a) (V f : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x ∈ Ioo l r, ∃ y ∈ Ioo l r, f x ≠ f y) (R : ℝ) :
    ∃ ψ : Domain l r, ‖toIntervalL2 ψ‖ = 1 ∧
      R < ‖toIntervalL2 (commutator a V f hV hf ψ)‖ := by
  obtain ⟨χ, hχ⟩ := exists_nondegenerate_packet_of_nonconstant f hf hn
  exact no_interval_bound ha V f hV hf χ hχ R

/-- No ambient bounded interval-L² operator extends the bracket of a nonconstant profile. -/
theorem no_bounded_interval_extension_of_nonconstant {a : ℝ} (ha : 0 < a)
    (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x ∈ Ioo l r, ∃ y ∈ Ioo l r, f x ≠ f y) :
    ¬ ∃ A : IntervalHilbert l r →L[ℂ] IntervalHilbert l r,
      ∀ ψ : Domain l r, A (toIntervalL2 ψ) = toIntervalL2 (commutator a V f hV hf ψ) := by
  rintro ⟨A, hA⟩
  obtain ⟨ψ, hψ, hR⟩ := no_interval_bound_of_nonconstant ha V f hV hf hn ‖A‖
  have hb := A.le_opNorm (toIntervalL2 ψ)
  rw [hA ψ, hψ, mul_one] at hb
  exact (not_lt_of_ge hb) hR

/-- A single nonzero interior derivative already excludes a bounded interval-L² extension. -/
theorem no_bounded_interval_extension_of_deriv_ne_zero {a : ℝ} (ha : 0 < a)
    (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Ioo l r) (hd : deriv f x₀ ≠ 0) :
    ¬ ∃ A : IntervalHilbert l r →L[ℂ] IntervalHilbert l r,
      ∀ ψ : Domain l r, A (toIntervalL2 ψ) = toIntervalL2 (commutator a V f hV hf ψ) := by
  rintro ⟨A, hA⟩
  obtain ⟨ψ, hψ, hR⟩ := no_interval_bound_of_deriv_ne_zero ha V f hV hf hx₀ hd ‖A‖
  have hb := A.le_opNorm (toIntervalL2 ψ)
  rw [hA ψ, hψ, mul_one] at hb
  exact (not_lt_of_ge hb) hR

/-- A real compact interior multiplier with unit slope exists on every nonempty interval. -/
theorem exists_compact_real_profile (hlr : l < r) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo l r ∧
      ∃ x ∈ Ioo l r, deriv (fun y ↦ (f y : ℂ)) x = 1 := by
  obtain ⟨x₀, hl, hr⟩ := exists_between hlr
  obtain ⟨b, hb, hc, hd, _, h1⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (isOpen_Ioo.mem_nhds ⟨hl, hr⟩)
  let f : ℝ → ℝ := fun x ↦ b x * (x - x₀)
  refine ⟨f, hd.mul (contDiff_id.sub contDiff_const), hc.mul_right,
    tsupport_mul_subset_left.trans hb, x₀, ⟨hl, hr⟩, ?_⟩
  have hd' : HasDerivAt f 1 x₀ := by
    convert ((hd.differentiable (by simp)).differentiableAt.hasDerivAt.mul
      ((hasDerivAt_id x₀).sub_const x₀)) using 1 <;> first | rfl | simp [h1]
  simpa using hd'.ofReal_comp.deriv

/-- The obstruction is realized by a smooth real compact multiplier on every l < r. -/
theorem exists_compact_real_interval_obstruction {a : ℝ} (ha : 0 < a) (hlr : l < r)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ∃ f : ℝ → ℝ, ∃ hf : ContDiff ℝ ∞ f,
      HasCompactSupport f ∧ tsupport f ⊆ Ioo l r ∧
      ¬ ∃ A : IntervalHilbert l r →L[ℂ] IntervalHilbert l r,
        ∀ ψ : Domain l r, A (toIntervalL2 ψ) = toIntervalL2
          (commutator a V (fun x ↦ (f x : ℂ)) hV (Complex.ofRealCLM.contDiff.comp hf) ψ) := by
  obtain ⟨f, hf, hc, hs, x, hx, hd⟩ := exists_compact_real_profile hlr
  refine ⟨f, hf, hc, hs, ?_⟩
  apply no_bounded_interval_extension_of_deriv_ne_zero ha V _ hV _ hx
  simp [hd]

/-- Every interior test vanishes off the interval, including at either endpoint. -/
theorem zero_of_not_mem (ψ : Domain l r) {x : ℝ} (hx : x ∉ Ioo l r) : ψ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h ↦ hx (ψ.tsupport_subset h))

/-- Compact interior support gives vanishing in a full neighborhood of any exterior point. -/
theorem eventually_zero_of_not_mem (ψ : Domain l r) {x : ℝ} (hx : x ∉ Ioo l r) :
    (ψ : ℝ → ℂ) =ᶠ[nhds x] 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (ψ.tsupport_subset h))

/-- The test and both ordinary derivatives vanish near either endpoint, from support alone. -/
theorem eventually_zero_derivatives_of_not_mem (ψ : Domain l r) {x : ℝ}
    (hx : x ∉ Ioo l r) :
    ∀ᶠ y in nhds x, ψ y = 0 ∧ deriv ψ y = 0 ∧ deriv (deriv ψ) y = 0 := by
  filter_upwards [eventually_zero_of_not_mem ψ hx, eventually_zero_of_not_mem (D ψ) hx,
    eventually_zero_of_not_mem (D (D ψ)) hx] with y h0 h1 h2
  exact ⟨h0, h1, h2⟩

/-- Dirichlet and Neumann endpoint data for the same tests, with no wall-domain assertion. -/
theorem endpoint_data (ψ : Domain l r) :
    ψ l = 0 ∧ ψ r = 0 ∧ deriv ψ l = 0 ∧ deriv ψ r = 0 := by
  have hl : l ∉ Ioo l r := by simp
  have hr : r ∉ Ioo l r := by simp
  exact ⟨zero_of_not_mem ψ hl, zero_of_not_mem ψ hr,
    zero_of_not_mem (D ψ) hl, zero_of_not_mem (D ψ) hr⟩

end SKEFTHawking.DKMBootstrap.BECInteriorCommutator
