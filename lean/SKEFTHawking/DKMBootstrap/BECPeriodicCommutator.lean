import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.Holder
import SKEFTHawking.KineticEssentialSelfAdjoint
import Mathlib.Tactic

/-!
# Periodic one-particle first commutator on a common trigonometric domain

The carrier is L² of the physical circle of positive period L, with normalized Haar
measure. Finite Fourier synthesis identifies a dense subspace of this actual L².
The spectral kinetic action and cosine multiplication are linear endomorphisms of
that common domain. Their bracket has no bounded extension to ambient L² when the
kinetic scale is positive. Each domain vector has a canonical continuous trigonometric
representative, and the kinetic action agrees a.e. with minus a times its actual
second derivative in the real periodic coordinate. Its self-adjoint closure has the
finite Fourier domain as an operator core and has an unbounded cosine bracket.
The maximal domain, wall realizations, Fock dynamics, and higher-order commutators
remain outside this construction.
Physical Lebesgue normalization would multiply the characters by L⁻¹/²; no
change-of-measure equivalence is constructed here.
-/
noncomputable section
open Complex MeasureTheory
namespace SKEFTHawking.DKMBootstrap.BECPeriodicCommutator

variable (L : ℝ) [Fact (0 < L)]

abbrev ModeSpace := Lp ℂ 2 (@AddCircle.haarAddCircle L inferInstance)
abbrev mode (n : ℤ) : ModeSpace L := fourierLp 2 n

 theorem mode_normalized (n : ℤ) : ‖mode L n‖ = 1 :=
  orthonormal_fourier.1 n

 theorem modes_orthonormal : Orthonormal ℂ (mode L) :=
  orthonormal_fourier

/-- Real-valued cosine multiplier, expressed using conjugate characters. -/
def cosine (x : AddCircle L) : ℂ :=
  (fourier 1 x + fourier (-1) x) / 2

 omit [Fact (0 < L)] in
 theorem cosine_real (x : AddCircle L) : (cosine L x).im = 0 := by
  unfold cosine
  rw [fourier_neg]
  simp only [Complex.div_ofNat_im, Complex.add_im, Complex.conj_im, add_neg_cancel, zero_div]

 omit [Fact (0 < L)] in
 theorem cosine_mul_fourier (n : ℤ) (x : AddCircle L) :
    cosine L x * fourier n x =
      (fourier (n + 1) x + fourier (n - 1) x) / 2 := by
  rw [cosine, fourier_add, show n - 1 = n + (-1) by omega,
    fourier_add]
  ring

/-- The physical kinetic scale, with a = ℏ²/(2m). -/
def scale (a : ℝ) : ℝ := a * (2 * Real.pi / L)^2

 theorem scale_pos {a : ℝ} (ha : 0 < a) : 0 < scale L a := by
  exact mul_pos ha (sq_pos_of_pos (div_pos (mul_pos (by norm_num) Real.pi_pos)
    (Fact.out : 0 < L)))

omit [Fact (0 < L)] in
/-- The derivative eigenvalue is Mathlib's actual periodic character derivative. -/
 theorem mode_derivative (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourier n (y : AddCircle L))
      (2 * Real.pi * Complex.I * n / L * fourier n (x : AddCircle L)) x :=
  hasDerivAt_fourier L n x

omit [Fact (0 < L)] in
/-- The spectral energy agrees with minus a times the squared derivative eigenvalue. -/
theorem kinetic_eigenvalue (a : ℝ) (n : ℤ) :
    -(a : ℂ) * (2 * Real.pi * Complex.I * n / L)^2 =
      (scale L a : ℂ) * (n : ℂ)^2 := by
  simp only [scale, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  ring_nf
  simp [Complex.I_sq]

/-- Explicit spectral kinetic action on a mode. -/
def kineticMode (c : ℝ) (n : ℤ) : ModeSpace L :=
  ((c : ℂ) * (n : ℂ)^2) • mode L n

/-- Multiplication by cosine on a mode, as its exact Fourier expansion. -/
def cosineMode (n : ℤ) : ModeSpace L :=
  (1 / 2 : ℂ) • (mode L (n + 1) + mode L (n - 1))

/-- The two-mode L² vector really is pointwise cosine multiplication, almost everywhere. -/
theorem cosineMode_ae (n : ℤ) :
    (cosineMode L n : AddCircle L → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun x => cosine L x * (mode L n : AddCircle L → ℂ) x) := by
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (mode L (n + 1) + mode L (n - 1)),
    Lp.coeFn_add (mode L (n + 1)) (mode L (n - 1)),
    coeFn_fourierLp 2 (n + 1), coeFn_fourierLp 2 (n - 1), coeFn_fourierLp 2 n]
    with x hs ha hp hm hn
  change ((1 / 2 : ℂ) • (mode L (n + 1) + mode L (n - 1)) : ModeSpace L) x = _
  rw [hs]
  change (1 / 2 : ℂ) * ((mode L (n + 1) + mode L (n - 1)) : ModeSpace L) x = _
  rw [ha]
  change (1 / 2 : ℂ) * ((mode L (n + 1) : AddCircle L → ℂ) x +
    (mode L (n - 1) : AddCircle L → ℂ) x) = _
  rw [hp, hm, hn, cosine_mul_fourier]
  ring

/-- Spectral kinetic action on the two-mode cosine expansion. -/
def kineticCosineMode (c : ℝ) (n : ℤ) : ModeSpace L :=
  (1 / 2 : ℂ) • (kineticMode L c (n + 1) + kineticMode L c (n - 1))

/-- Cosine action on a kinetic eigenmode, extended by scalar linearity. -/
def cosineKineticMode (c : ℝ) (n : ℤ) : ModeSpace L :=
  ((c : ℂ) * (n : ℂ)^2) • cosineMode L n

def firstCommutatorMode (c : ℝ) (n : ℤ) : ModeSpace L :=
  kineticCosineMode L c n - cosineKineticMode L c n

 theorem first_commutator_action (c : ℝ) (n : ℤ) :
    firstCommutatorMode L c n =
      ((c : ℂ) * (2 * (n : ℂ) + 1) / 2) • mode L (n + 1) +
      ((c : ℂ) * (1 - 2 * (n : ℂ)) / 2) • mode L (n - 1) := by
  simp only [firstCommutatorMode, kineticCosineMode, cosineKineticMode,
    kineticMode, cosineMode, Int.cast_add, Int.cast_one,
    smul_add, smul_smul, sub_eq_add_neg, neg_add_rev, ← neg_smul]
  module

/-- Constant multiplication commutes with any linear kinetic action on its domain. -/
 theorem constant_commutator_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : E →ₗ[ℂ] E) (b : ℂ) (v : E) : T (b • v) - b • T v = 0 := by
  rw [T.map_smul, sub_self]

/-- The upward matrix element is extracted by actual L² orthonormality. -/
theorem upward_matrix_element (c : ℝ) (n : ℤ) :
    inner ℂ (mode L (n + 1)) (firstCommutatorMode L c n) =
      (c : ℂ) * (2 * (n : ℂ) + 1) / 2 := by
  rw [first_commutator_action, inner_add_right, inner_smul_right, inner_smul_right]
  have h := orthonormal_iff_ite.mp (modes_orthonormal L)
  rw [h, h]
  simp [show n + 1 ≠ n - 1 by omega]

 theorem coefficient_le_norm (c : ℝ) (n : ℤ) :
    ‖(c : ℂ) * (2 * (n : ℂ) + 1) / 2‖ ≤ ‖firstCommutatorMode L c n‖ := by
  rw [← upward_matrix_element L c n]
  simpa [mode_normalized] using
    norm_inner_le_norm (mode L (n + 1)) (firstCommutatorMode L c n)

/-- No finite bound for the declared spectral two-mode response on normalized tests.
This is a finite-mode spectral certificate, not a maximal operator-domain theorem. -/
theorem no_finite_mode_bound {c : ℝ} (hc : 0 < c) (R : ℝ) :
    ∃ n : ℤ, ‖mode L n‖ = 1 ∧ R < ‖firstCommutatorMode L c n‖ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (R / c)
  refine ⟨n, mode_normalized L _, ?_⟩
  have hn' : R < c * (n : ℝ) := by
    have := (div_lt_iff₀ hc).mp hn
    nlinarith
  have hpos : 0 ≤ c * (2 * (n : ℝ) + 1) / 2 := by positivity
  have he : ‖(c : ℂ) * (2 * ((n : ℤ) : ℂ) + 1) / 2‖ =
      c * (2 * (n : ℝ) + 1) / 2 := by
    rw [show (c : ℂ) * (2 * ((n : ℤ) : ℂ) + 1) / 2 =
      ((c * (2 * (n : ℝ) + 1) / 2 : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  have hb := coefficient_le_norm L c (n : ℤ)
  rw [he] at hb
  nlinarith

 theorem physical_no_finite_mode_bound {a : ℝ} (ha : 0 < a) (R : ℝ) :
    ∃ n : ℤ, ‖mode L n‖ = 1 ∧ R < ‖firstCommutatorMode L (scale L a) n‖ :=
  no_finite_mode_bound L (scale_pos L ha) R

/-- Synthesis of finitely supported Fourier coefficients into actual Haar L². -/
def synthesis : (ℤ →₀ ℂ) →ₗ[ℂ] ModeSpace L :=
  Finsupp.linearCombination ℂ (mode L)

theorem synthesis_injective : Function.Injective (synthesis L) :=
  (modes_orthonormal L).linearIndependent

/-- The common invariant domain is a subspace of L², not a separate sequence space. -/
def trigDomain : Submodule ℂ (ModeSpace L) := (synthesis L).range

theorem trigDomain_eq_span :
    trigDomain L = Submodule.span ℂ (Set.range (mode L)) :=
  Finsupp.range_linearCombination ℂ

theorem trigDomain_dense : (trigDomain L).topologicalClosure = ⊤ := by
  rw [trigDomain_eq_span]
  exact span_fourierLp_closure_eq_top (by norm_num)

/-- Unique finite coefficients identify the actual domain with the coefficient space. -/
def trigEquiv : (ℤ →₀ ℂ) ≃ₗ[ℂ] trigDomain L :=
  LinearEquiv.ofInjective (synthesis L) (synthesis_injective L)

@[simp] theorem coe_trigEquiv (v : ℤ →₀ ℂ) :
    (trigEquiv L v : ModeSpace L) = synthesis L v := rfl

/-- Each Fourier character, now regarded as a vector of the common domain. -/
def domainMode (n : ℤ) : trigDomain L := trigEquiv L (Finsupp.single n 1)

@[simp] theorem coe_domainMode (n : ℤ) :
    (domainMode L n : ModeSpace L) = mode L n := by
  simp [domainMode, synthesis]

theorem trigEquiv_linearCombination :
    (trigEquiv L).toLinearMap = Finsupp.linearCombination ℂ (domainMode L) := by
  apply Finsupp.lhom_ext
  intro n b
  have hs : Finsupp.single n b = b • Finsupp.single n (1 : ℂ) := by simp
  rw [hs]
  simp only [map_smul, Finsupp.linearCombination_single, one_smul]
  rfl

/-- Canonical continuous trigonometric polynomial with the unique domain coefficients. -/
def trigPolynomial (v : ℤ →₀ ℂ) : C(AddCircle L, ℂ) :=
  v.sum (fun n b ↦ b • fourier n)

/-- The continuous polynomial maps to the existing L² synthesis by linearity. -/
theorem trigPolynomial_toLp (v : ℤ →₀ ℂ) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (trigPolynomial L v) =
      synthesis L v := by
  simp only [trigPolynomial, Finsupp.sum, map_sum, map_smul, synthesis,
    Finsupp.linearCombination_apply, Finsupp.sum, fourierLp, mode]

/-- The canonical continuous polynomial represents the constructed domain vector a.e. -/
theorem trigPolynomial_ae (v : ℤ →₀ ℂ) :
    (synthesis L v : AddCircle L → ℂ) =ᵐ[AddCircle.haarAddCircle]
      trigPolynomial L v := by
  rw [← trigPolynomial_toLp]
  exact ContinuousMap.coeFn_toLp _ _

/-- Pullback of the continuous circle polynomial to the real coordinate. -/
def trigLift (v : ℤ →₀ ℂ) (x : ℝ) : ℂ := trigPolynomial L v (x : AddCircle L)

omit [Fact (0 < L)] in
/-- Actual first derivative of the finite polynomial, using the character derivative. -/
theorem trigLift_hasDerivAt (v : ℤ →₀ ℂ) (x : ℝ) :
    HasDerivAt (trigLift L v)
      (v.sum (fun n b ↦ b *
        (2 * Real.pi * Complex.I * n / L * fourier n (x : AddCircle L)))) x := by
  have hp : trigLift L v =
      fun y : ℝ ↦ ∑ n ∈ v.support, v n * fourier n (y : AddCircle L) := by
    funext y
    simp [trigLift, trigPolynomial, Finsupp.sum]
  rw [hp]
  exact HasDerivAt.fun_sum (fun n _ ↦ (mode_derivative L n x).const_mul (v n))

omit [Fact (0 < L)] in
/-- The first derivative is the finite sum of the genuine differentiated characters. -/
theorem trigLift_deriv (v : ℤ →₀ ℂ) (x : ℝ) :
    deriv (trigLift L v) x = v.sum (fun n b ↦ b *
      (2 * Real.pi * Complex.I * n / L * fourier n (x : AddCircle L))) :=
  (trigLift_hasDerivAt L v x).deriv

omit [Fact (0 < L)] in
/-- Differentiate the actual first derivative a second time, still on the same support. -/
theorem trigLift_deriv_hasDerivAt (v : ℤ →₀ ℂ) (x : ℝ) :
    HasDerivAt (deriv (trigLift L v))
      (v.sum (fun n b ↦ b * (2 * Real.pi * Complex.I * n / L)^2 *
        fourier n (x : AddCircle L))) x := by
  have hd : deriv (trigLift L v) = fun y : ℝ ↦ v.sum (fun n b ↦ b *
      (2 * Real.pi * Complex.I * n / L * fourier n (y : AddCircle L))) :=
    funext (trigLift_deriv L v)
  rw [hd]
  have h := HasDerivAt.fun_sum (u := v.support) (fun n _ ↦
    ((mode_derivative L n x).const_mul (2 * Real.pi * Complex.I * n / L)).const_mul
      (v n))
  simpa only [Finsupp.sum, pow_two, mul_assoc] using h

omit [Fact (0 < L)] in
/-- Formula for the actual second real derivative, rather than a spectral definition. -/
theorem trigLift_second_deriv (v : ℤ →₀ ℂ) (x : ℝ) :
    deriv (deriv (trigLift L v)) x =
      v.sum (fun n b ↦ b * (2 * Real.pi * Complex.I * n / L)^2 *
        fourier n (x : AddCircle L)) :=
  (trigLift_deriv_hasDerivAt L v x).deriv

/-- Finite diagonal action, to be transported to the declared L² domain. -/
def kineticCoeffs (c : ℝ) : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) :=
  Finsupp.linearCombination ℂ
    (fun n ↦ ((c : ℂ) * (n : ℂ)^2) • Finsupp.single n 1)

/-- Finite shifts preserve finite support, in both directions. -/
def cosineCoeffs : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) :=
  Finsupp.linearCombination ℂ
    (fun n ↦ (1 / 2 : ℂ) • (Finsupp.single (n + 1) 1 + Finsupp.single (n - 1) 1))

/-- Spectral kinetic operator on the actual common invariant trigonometric domain. -/
def kinetic (c : ℝ) : trigDomain L →ₗ[ℂ] trigDomain L :=
  (trigEquiv L).toLinearMap ∘ₗ kineticCoeffs c ∘ₗ (trigEquiv L).symm.toLinearMap

/-- Cosine operator on the same domain; pointwise multiplication is proved below. -/
def cosineOp : trigDomain L →ₗ[ℂ] trigDomain L :=
  (trigEquiv L).toLinearMap ∘ₗ cosineCoeffs ∘ₗ (trigEquiv L).symm.toLinearMap

theorem kinetic_domainMode (c : ℝ) (n : ℤ) :
    kinetic L c (domainMode L n) = ((c : ℂ) * (n : ℂ)^2) • domainMode L n := by
  simp only [kinetic, domainMode, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, kineticCoeffs, Finsupp.linearCombination_single,
    one_smul, map_smul]

theorem cosineOp_domainMode (n : ℤ) :
    cosineOp L (domainMode L n) =
      (1 / 2 : ℂ) • (domainMode L (n + 1) + domainMode L (n - 1)) := by
  simp only [cosineOp, domainMode, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, cosineCoeffs, Finsupp.linearCombination_single,
    one_smul, map_smul, map_add]

/-- The domain action is the finite Fourier sum of the spectral kinetic responses. -/
theorem kinetic_finite_sum (c : ℝ) (v : ℤ →₀ ℂ) :
    (kinetic L c (trigEquiv L v) : ModeSpace L) =
      v.sum (fun n b ↦ b • kineticMode L c n) := by
  change ((trigDomain L).subtype.comp (kinetic L c)) ((trigEquiv L).toLinearMap v) = _
  rw [LinearMap.congr_fun (trigEquiv_linearCombination L) v,
    Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
  simp only [Function.comp_apply, LinearMap.comp_apply, kinetic_domainMode,
    Submodule.subtype_apply, Submodule.coe_smul, coe_domainMode, kineticMode]

/-- The continuous kinetic polynomial maps to the already constructed domain action. -/
theorem kinetic_polynomial_toLp (c : ℝ) (v : ℤ →₀ ℂ) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
      (v.sum (fun n b ↦ b • (((c : ℂ) * (n : ℂ)^2) • fourier n))) =
      (kinetic L c (trigEquiv L v) : ModeSpace L) := by
  rw [kinetic_finite_sum]
  simp only [Finsupp.sum, map_sum, map_smul, kineticMode, mode, fourierLp]

/-- The spectral kinetic action has the claimed finite continuous representative a.e. -/
theorem kinetic_polynomial_ae (c : ℝ) (v : ℤ →₀ ℂ) :
    ((kinetic L c (trigEquiv L v) : ModeSpace L) : AddCircle L → ℂ)
      =ᵐ[AddCircle.haarAddCircle]
        (v.sum (fun n b ↦ b • (((c : ℂ) * (n : ℂ)^2) • fourier n)) :
          C(AddCircle L, ℂ)) := by
  rw [← kinetic_polynomial_toLp]
  exact ContinuousMap.coeFn_toLp _ _

omit [Fact (0 < L)] in
/-- Pointwise differential identification of the continuous kinetic representative. -/
theorem kinetic_polynomial_eq_neg_second_deriv (a : ℝ) (v : ℤ →₀ ℂ) (x : ℝ) :
    (v.sum (fun n b ↦ b • (((scale L a : ℂ) * (n : ℂ)^2) • fourier n)) :
        C(AddCircle L, ℂ)) (x : AddCircle L) =
      -(a : ℂ) * deriv (deriv (trigLift L v)) x := by
  rw [trigLift_second_deriv]
  simp only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← kinetic_eigenvalue]
  ring

/-- Canonical continuous representative of every vector in the constructed domain. -/
def representative (u : trigDomain L) : C(AddCircle L, ℂ) :=
  trigPolynomial L ((trigEquiv L).symm u)

/-- This representative agrees with the given L² domain vector almost everywhere. -/
theorem representative_ae (u : trigDomain L) :
    (u : ModeSpace L) =ᵐ[AddCircle.haarAddCircle] representative L u := by
  have h := trigPolynomial_ae L ((trigEquiv L).symm u)
  simpa only [← coe_trigEquiv, LinearEquiv.apply_symm_apply, representative] using h

/-- The domain representative pulled back to the real coordinate. -/
def representativeLift (u : trigDomain L) (x : ℝ) : ℂ :=
  representative L u (x : AddCircle L)

/-- The existing kinetic action is minus a times the actual second derivative of its
continuous representative. The a.e. circle statement holds for every real lift of that
circle point, so no measurable choice of coordinate is needed. This is a comparison on
the finite common domain only. -/
theorem kinetic_eq_neg_second_deriv_ae (a : ℝ) (u : trigDomain L) :
    ∀ᵐ z : AddCircle L ∂AddCircle.haarAddCircle, ∀ x : ℝ, (x : AddCircle L) = z →
      (kinetic L (scale L a) u : ModeSpace L) z =
        -(a : ℂ) * deriv (deriv (representativeLift L u)) x := by
  have h := kinetic_polynomial_ae L (scale L a) ((trigEquiv L).symm u)
  simp only [LinearEquiv.apply_symm_apply] at h
  filter_upwards [h] with z hz
  intro x hx
  rw [hz, ← hx]
  exact kinetic_polynomial_eq_neg_second_deriv L a ((trigEquiv L).symm u) x

theorem cosineOp_finite_sum (v : ℤ →₀ ℂ) :
    (cosineOp L (trigEquiv L v) : ModeSpace L) =
      v.sum (fun n b ↦ b • cosineMode L n) := by
  change ((trigDomain L).subtype.comp (cosineOp L)) ((trigEquiv L).toLinearMap v) = _
  rw [LinearMap.congr_fun (trigEquiv_linearCombination L) v,
    Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
  simp only [Function.comp_apply, LinearMap.comp_apply, cosineOp_domainMode,
    Submodule.subtype_apply, Submodule.coe_smul, Submodule.coe_add, coe_domainMode, cosineMode]

private theorem cosine_ae_add {u v u' v' : ModeSpace L}
    (hu : (u' : AddCircle L → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ cosine L x * u x))
    (hv : (v' : AddCircle L → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ cosine L x * v x)) :
    (u' + v' : ModeSpace L) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ cosine L x * (u + v : ModeSpace L) x) := by
  filter_upwards [hu, hv, Lp.coeFn_add u' v', Lp.coeFn_add u v] with x hu hv h₁ h₂
  rw [h₁, h₂]
  change u' x + v' x = cosine L x * (u x + v x)
  rw [hu, hv, mul_add]

private theorem cosine_ae_smul {u u' : ModeSpace L} (b : ℂ)
    (hu : (u' : AddCircle L → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ cosine L x * u x)) :
    (b • u' : ModeSpace L) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ cosine L x * (b • u : ModeSpace L) x) := by
  filter_upwards [hu, Lp.coeFn_smul b u', Lp.coeFn_smul b u] with x hu h₁ h₂
  rw [h₁, h₂]
  change b * u' x = cosine L x * (b * u x)
  rw [hu]
  ring

/-- The invariant cosine action is actual multiplication on every domain vector,
with equality understood almost everywhere for L² representatives. -/
theorem cosineOp_ae (v : trigDomain L) :
    ((cosineOp L v : ModeSpace L) : AddCircle L → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ cosine L x * (v : ModeSpace L) x) := by
  obtain ⟨v, rfl⟩ := (trigEquiv L).surjective v
  induction v using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, Submodule.coe_zero]
    filter_upwards [Lp.coeFn_zero ℂ (2 : ENNReal) (@AddCircle.haarAddCircle L inferInstance)]
      with x hx
    change (0 : ModeSpace L) x = cosine L x * (0 : ModeSpace L) x
    rw [hx]
    simp
  | add v w hv hw =>
    simpa only [map_add, Submodule.coe_add] using cosine_ae_add L hv hw
  | single n b =>
    have hs : Finsupp.single n b = b • Finsupp.single n (1 : ℂ) := by simp
    rw [hs]
    simp only [map_smul, Submodule.coe_smul]
    apply cosine_ae_smul L b
    change ((cosineOp L (domainMode L n) : ModeSpace L) : AddCircle L → ℂ) =ᵐ[_]
      (fun x ↦ cosine L x * (domainMode L n : ModeSpace L) x)
    simpa only [cosineOp_domainMode, Submodule.coe_smul, Submodule.coe_add,
      coe_domainMode, cosineMode] using cosineMode_ae L n

/-- Both compositions are defined on the same invariant domain. -/
def commutator (c : ℝ) : trigDomain L →ₗ[ℂ] trigDomain L :=
  (kinetic L c).comp (cosineOp L) - (cosineOp L).comp (kinetic L c)

/-- The actual operator bracket recovers the previously checked spectral response. -/
theorem commutator_domainMode (c : ℝ) (n : ℤ) :
    (commutator L c (domainMode L n) : ModeSpace L) = firstCommutatorMode L c n := by
  simp only [commutator, LinearMap.sub_apply, LinearMap.comp_apply, cosineOp_domainMode,
    map_smul, map_add, kinetic_domainMode, Submodule.coe_sub, Submodule.coe_smul,
    Submodule.coe_add, coe_domainMode]
  rfl

theorem commutator_action (c : ℝ) (n : ℤ) :
    (commutator L c (domainMode L n) : ModeSpace L) =
      ((c : ℂ) * (2 * (n : ℂ) + 1) / 2) • mode L (n + 1) +
      ((c : ℂ) * (1 - 2 * (n : ℂ)) / 2) • mode L (n - 1) := by
  rw [commutator_domainMode, first_commutator_action]

/-- Unit vectors of the actual common domain have arbitrarily large bracket image. -/
theorem no_domain_bound {c : ℝ} (hc : 0 < c) (R : ℝ) :
    ∃ v : trigDomain L, ‖(v : ModeSpace L)‖ = 1 ∧
      R < ‖(commutator L c v : ModeSpace L)‖ := by
  obtain ⟨n, hn, hR⟩ := no_finite_mode_bound L hc R
  refine ⟨domainMode L n, ?_, ?_⟩
  · simpa only [coe_domainMode] using hn
  · simpa only [commutator_domainMode] using hR

/-- No bounded operator on ambient L² agrees with this domain commutator. -/
theorem no_bounded_extension {c : ℝ} (hc : 0 < c) :
    ¬ ∃ A : ModeSpace L →L[ℂ] ModeSpace L,
      ∀ v : trigDomain L, A (v : ModeSpace L) = (commutator L c v : ModeSpace L) := by
  rintro ⟨A, hA⟩
  obtain ⟨v, hv, hR⟩ := no_domain_bound L hc ‖A‖
  have hb := A.le_opNorm (v : ModeSpace L)
  rw [hA v, hv, mul_one] at hb
  exact (not_lt_of_ge hb) hR

theorem physical_no_bounded_extension {a : ℝ} (ha : 0 < a) :
    ¬ ∃ A : ModeSpace L →L[ℂ] ModeSpace L,
      ∀ v : trigDomain L,
        A (v : ModeSpace L) = (commutator L (scale L a) v : ModeSpace L) :=
  no_bounded_extension L (scale_pos L ha)

/-- Scalar multiplication preserves the same domain and its kinetic bracket vanishes. -/
theorem kinetic_constant_control (c : ℝ) (b : ℂ) (v : trigDomain L) :
    kinetic L c (b • v) - b • kinetic L c v = 0 :=
  constant_commutator_zero (kinetic L c) b v

/-- The constant control uses actual multiplication of L² representatives as well. -/
theorem constant_ae (b : ℂ) (v : trigDomain L) :
    ((b • v : trigDomain L) : ModeSpace L) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ b * (v : ModeSpace L) x) :=
  Lp.coeFn_smul b (v : ModeSpace L)

/-! ## Self-adjoint closure of the actual differential kinetic on the Fourier core

The partial operator below uses the existing kinetic action, whose differential
identification is `kinetic_eq_neg_second_deriv_ae`. Only its finite Fourier core is
identified here; no characterization of the full closure domain is needed.
-/

/-- The existing differential kinetic, as a partial linear operator in ambient Haar L². -/
def kineticPMap (c : ℝ) : ModeSpace L →ₗ.[ℂ] ModeSpace L where
  domain := trigDomain L
  toFun := (trigDomain L).subtype.comp (kinetic L c)

@[simp] theorem kineticPMap_apply (c : ℝ) (u : trigDomain L) :
    kineticPMap L c u = (kinetic L c u : ModeSpace L) := rfl

theorem kineticPMap_dense (c : ℝ) : Dense ((kineticPMap L c).domain : Set (ModeSpace L)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr (trigDomain_dense L)

/-- Symmetry follows from orthonormal Fourier modes and their real kinetic eigenvalues. -/
theorem kineticPMap_symmetric (c : ℝ) : DFT.IsSymmetricPMap (kineticPMap L c) := by
  intro u w
  obtain ⟨v, rfl⟩ := (trigEquiv L).surjective u
  obtain ⟨z, rfl⟩ := (trigEquiv L).surjective w
  change inner ℂ (kinetic L c (trigEquiv L v) : ModeSpace L) (trigEquiv L z) =
    inner ℂ (trigEquiv L v : ModeSpace L) (kinetic L c (trigEquiv L z))
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ h₁ h₂ => simp only [map_add, Submodule.coe_add, inner_add_left, h₁, h₂]
  | single n b =>
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => simp only [map_add, Submodule.coe_add, inner_add_right, h₁, h₂]
    | single m d =>
      have hs (k : ℤ) (a : ℂ) :
          trigEquiv L (Finsupp.single k a) = a • domainMode L k := by
        rw [domainMode, ← map_smul]
        simp
      simp only [hs, map_smul, kinetic_domainMode, Submodule.coe_smul, coe_domainMode,
        inner_smul_left, inner_smul_right, map_mul, map_pow,
        Complex.conj_ofReal, map_intCast]
      rw [orthonormal_iff_ite.mp (modes_orthonormal L)]
      split_ifs with h
      · subst m; ring
      · simp

/-- The imaginary shift of the differential kinetic, with the same finite domain. -/
def shiftedKinetic (c μ : ℝ) : trigDomain L →ₗ[ℂ] ModeSpace L :=
  (trigDomain L).subtype.comp (kinetic L c) -
    (Complex.I * (μ : ℂ)) • (trigDomain L).subtype

theorem kinetic_shift_ne_zero (c μ : ℝ) (hμ : μ ≠ 0) (n : ℤ) :
    (c : ℂ) * (n : ℂ)^2 - Complex.I * (μ : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp [pow_two, Complex.mul_im] at hi
  exact hμ hi

/-- A shifted mode has a finite Fourier preimage, obtained by dividing its coefficient. -/
theorem shiftedKinetic_mode_preimage (c μ : ℝ) (hμ : μ ≠ 0) (n : ℤ) :
    shiftedKinetic L c μ
      (((c : ℂ) * (n : ℂ)^2 - Complex.I * (μ : ℂ))⁻¹ • domainMode L n) = mode L n := by
  have hn := kinetic_shift_ne_zero c μ hμ n
  simp only [shiftedKinetic, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_smul, kinetic_domainMode, Submodule.subtype_apply,
    coe_domainMode]
  rw [← sub_smul]
  simp [smul_smul, hn]

/-- Each nonzero imaginary shifted range contains the entire dense Fourier domain. -/
theorem trigDomain_le_shiftedKinetic_range (c μ : ℝ) (hμ : μ ≠ 0) :
    trigDomain L ≤ (shiftedKinetic L c μ).range := by
  apply (trigDomain_eq_span L).le.trans
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact ⟨_, shiftedKinetic_mode_preimage L c μ hμ n⟩

theorem kineticPMap_dense_shifted_range (c μ : ℝ) (hμ : μ ≠ 0) :
    Dense {w : ModeSpace L | ∃ x : (kineticPMap L c).domain,
      kineticPMap L c x - (Complex.I * (μ : ℂ)) • (x : ModeSpace L) = w} := by
  apply (kineticPMap_dense L c).mono
  intro w hw
  exact trigDomain_le_shiftedKinetic_range L c μ hμ hw

/-- The actual periodic differential kinetic is essentially self-adjoint on its Fourier core. -/
theorem kineticPMap_closure_selfAdjoint (c : ℝ) :
    IsSelfAdjoint (kineticPMap L c).closure :=
  DFT.isSelfAdjoint_closure_of_dense_range (kineticPMap_symmetric L c)
    (kineticPMap_dense L c) one_ne_zero
    (kineticPMap_dense_shifted_range L c 1 one_ne_zero)
    (kineticPMap_dense_shifted_range L c (-1) (by norm_num))

/-- The finite Fourier domain is an operator core of the self-adjoint closure. -/
theorem kineticPMap_closure_hasCore (c : ℝ) :
    (kineticPMap L c).closure.HasCore (trigDomain L) :=
  (kineticPMap L c).closureHasCore

/-- Canonical inclusion of the finite Fourier core in the closure domain. -/
def closureCore (c : ℝ) (u : trigDomain L) : (kineticPMap L c).closure.domain :=
  ⟨u, (kineticPMap L c).le_closure.1 u.2⟩

@[simp] theorem coe_closureCore (c : ℝ) (u : trigDomain L) :
    (closureCore L c u : ModeSpace L) = (u : ModeSpace L) := rfl

/-- Closing the operator preserves exactly the previously proved finite-domain action. -/
@[simp] theorem kineticPMap_closure_apply_core (c : ℝ) (u : trigDomain L) :
    (kineticPMap L c).closure (closureCore L c u) = (kinetic L c u : ModeSpace L) :=
  ((kineticPMap L c).le_closure.2 (x := u) (y := closureCore L c u) rfl).symm

/-- On the core the self-adjoint closure remains the actual negative second derivative. -/
theorem kineticPMap_closure_eq_neg_second_deriv_ae (a : ℝ) (u : trigDomain L) :
    ∀ᵐ z : AddCircle L ∂AddCircle.haarAddCircle, ∀ x : ℝ, (x : AddCircle L) = z →
      ((kineticPMap L (scale L a)).closure (closureCore L (scale L a) u) :
        AddCircle L → ℂ) z = -(a : ℂ) * deriv (deriv (representativeLift L u)) x := by
  rw [kineticPMap_closure_apply_core]
  exact kinetic_eq_neg_second_deriv_ae L a u

/-- Continuous representative of the same cosine used by the finite-domain action. -/
def cosineContinuous : C(AddCircle L, ℂ) :=
  ⟨cosine L, by unfold cosine; fun_prop⟩

/-- Actual bounded multiplication by cosine on ambient Haar L², via L∞ times L². -/
def cosineMultiplier : ModeSpace L →L[ℂ] ModeSpace L :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL AddCircle.haarAddCircle ⊤ 2 2
    (ContinuousMap.toLp ⊤ AddCircle.haarAddCircle ℂ (cosineContinuous L))

theorem cosineMultiplier_ae (u : ModeSpace L) :
    (cosineMultiplier L u : AddCircle L → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ cosine L x * u x) := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (ContinuousMap.toLp ⊤ AddCircle.haarAddCircle ℂ (cosineContinuous L)) u (r := 2)
  filter_upwards [h, ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℂ)
    AddCircle.haarAddCircle (cosineContinuous L)] with x hx hc
  change _ = cosine L x at hc
  change _ = _ * u x at hx
  exact hx.trans (congrArg (fun b : ℂ ↦ b * u x) hc)

/-- The ambient multiplier restricts to the accepted invariant finite-domain cosine action. -/
@[simp] theorem cosineMultiplier_core (u : trigDomain L) :
    cosineMultiplier L (u : ModeSpace L) = (cosineOp L u : ModeSpace L) := by
  apply Lp.ext
  exact (cosineMultiplier_ae L u).trans (cosineOp_ae L u).symm

/-- Every core vector belongs to the actual common domain of the closure bracket. -/
theorem cosineMultiplier_core_mem_closure (c : ℝ) (u : trigDomain L) :
    cosineMultiplier L (u : ModeSpace L) ∈ (kineticPMap L c).closure.domain := by
  rw [cosineMultiplier_core]
  exact (closureCore L c (cosineOp L u)).2

/-- The actual closure bracket agrees with the accepted differential bracket on the core. -/
theorem closure_bracket_core (c : ℝ) (u : trigDomain L) :
    (kineticPMap L c).closure
        ⟨cosineMultiplier L (u : ModeSpace L), cosineMultiplier_core_mem_closure L c u⟩ -
      cosineMultiplier L ((kineticPMap L c).closure (closureCore L c u)) =
        (commutator L c u : ModeSpace L) := by
  have he : (⟨cosineMultiplier L (u : ModeSpace L),
      cosineMultiplier_core_mem_closure L c u⟩ : (kineticPMap L c).closure.domain) =
      closureCore L c (cosineOp L u) := by
    apply Subtype.ext
    exact cosineMultiplier_core L u
  rw [he, kineticPMap_closure_apply_core, kineticPMap_closure_apply_core,
    cosineMultiplier_core]
  rfl

/-- No bounded ambient operator extends the closure bracket on its actual common domain.
Only the inclusion of the finite Fourier core is used; the full domain is not characterized. -/
theorem no_bounded_closure_bracket_extension {c : ℝ} (hc : 0 < c) :
    ¬ ∃ A : ModeSpace L →L[ℂ] ModeSpace L,
      ∀ u : (kineticPMap L c).closure.domain,
      ∀ hu : cosineMultiplier L (u : ModeSpace L) ∈ (kineticPMap L c).closure.domain,
        A (u : ModeSpace L) = (kineticPMap L c).closure
          ⟨cosineMultiplier L (u : ModeSpace L), hu⟩ -
            cosineMultiplier L ((kineticPMap L c).closure u) := by
  rintro ⟨A, hA⟩
  apply no_bounded_extension L hc
  refine ⟨A, fun u ↦ ?_⟩
  exact (hA (closureCore L c u) (cosineMultiplier_core_mem_closure L c u)).trans
    (closure_bracket_core L c u)

theorem physical_no_bounded_closure_bracket_extension {a : ℝ} (ha : 0 < a) :
    ¬ ∃ A : ModeSpace L →L[ℂ] ModeSpace L,
      ∀ u : (kineticPMap L (scale L a)).closure.domain,
      ∀ hu : cosineMultiplier L (u : ModeSpace L) ∈
          (kineticPMap L (scale L a)).closure.domain,
        A (u : ModeSpace L) = (kineticPMap L (scale L a)).closure
          ⟨cosineMultiplier L (u : ModeSpace L), hu⟩ -
            cosineMultiplier L ((kineticPMap L (scale L a)).closure u) :=
  no_bounded_closure_bracket_extension L (scale_pos L ha)

/-- Constant multiplication commutes on the entire closure domain. -/
theorem kineticPMap_closure_constant_control (c : ℝ) (b : ℂ)
    (u : (kineticPMap L c).closure.domain) :
    (kineticPMap L c).closure (b • u) - b • (kineticPMap L c).closure u = 0 := by
  rw [LinearPMap.map_smul, sub_self]

end SKEFTHawking.DKMBootstrap.BECPeriodicCommutator
