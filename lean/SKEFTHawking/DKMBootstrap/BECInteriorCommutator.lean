import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
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

end SKEFTHawking.DKMBootstrap.BECInteriorCommutator
