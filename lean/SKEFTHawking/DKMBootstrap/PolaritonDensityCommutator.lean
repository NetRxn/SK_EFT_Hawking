import SKEFTHawking.DKMBootstrap.PolaritonSpatialGenerator
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Compact planar photon-density packets

The tests are genuine compact smooth functions on Physlib `Space 2`, included in
physical Lebesgue L² and in the closed angular kinetic graph. The first bracket
uses the two actual Cartesian derivatives. No prepared state, detector, higher bracket,
Fock-space or unitary-group identification is made here.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff Distributions

namespace SKEFTHawking.DKMBootstrap.PolaritonDensityCommutator


abbrev Domain := TestFunction (⊤ : TopologicalSpace.Opens (Space 2)) ℂ ⊤
abbrev Spatial := PolaritonSpatialGenerator.Spatial

theorem deriv_smooth (i : Fin 2) {f : Space 2 → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Space.deriv i f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- Cartesian differentiation retains genuine compact support. -/
def D (i : Fin 2) : Domain →ₗ[ℂ] Domain where
  toFun ψ :=
    { toFun := Space.deriv i ψ
      contDiff' := deriv_smooth i ψ.contDiff
      hasCompactSupport' := ψ.hasCompactSupport.fderiv_apply ℝ (Space.basis i)
      tsupport_subset' := subset_univ _ }
  map_add' ψ φ := by
    ext x
    exact congrFun (Space.deriv_add _ _ (ψ.contDiff.differentiable (by simp))
      (φ.contDiff.differentiable (by simp))) x
  map_smul' c ψ := by
    ext x
    exact congrFun (Space.deriv_const_smul c (ψ.contDiff.differentiable (by simp))) x

@[simp] theorem D_apply (i : Fin 2) (ψ : Domain) (x : Space 2) :
    D i ψ x = Space.deriv i ψ x := rfl

/-- Multiplication only requires smoothness: the test supplies compact support. -/
def mulOp (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) : Domain →ₗ[ℂ] Domain where
  toFun ψ :=
    { toFun := fun x ↦ f x * ψ x
      contDiff' := hf.mul ψ.contDiff
      hasCompactSupport' := ψ.hasCompactSupport.mul_left
      tsupport_subset' := subset_univ _ }
  map_add' ψ φ := by ext x; exact mul_add _ _ _
  map_smul' c ψ := by ext x; exact mul_left_comm _ _ _

@[simp] theorem mulOp_apply (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f)
    (ψ : Domain) (x : Space 2) : mulOp f hf ψ x = f x * ψ x := rfl

theorem D_mul (i : Fin 2) (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (ψ : Domain) :
    D i (mulOp f hf ψ) = mulOp (Space.deriv i f) (deriv_smooth i hf) ψ +
      mulOp f hf (D i ψ) := by
  ext x
  have h := Space.deriv_smul (hf.differentiable (by simp)).differentiableAt
    (ψ.contDiff.differentiable (by simp)).differentiableAt (u := i) (x := x)
  change Space.deriv i (f • (ψ : Space 2 → ℂ)) x = _
  simpa only [mulOp_apply, add_apply, D_apply, smul_eq_mul, Pi.smul_apply,
    add_comm] using h

theorem D2_mul (i : Fin 2) (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (ψ : Domain) :
    D i (D i (mulOp f hf ψ)) =
      mulOp (Space.deriv i (Space.deriv i f)) (deriv_smooth i (deriv_smooth i hf)) ψ +
      (2 : ℂ) • mulOp (Space.deriv i f) (deriv_smooth i hf) (D i ψ) +
      mulOp f hf (D i (D i ψ)) := by
  rw [D_mul, map_add, D_mul, D_mul]
  ext x
  simp only [add_apply, smul_apply, mulOp_apply, smul_eq_mul]
  ring

def angularCoefficient (m : ℝ) : ℝ := (Constants.ℏ : ℝ) / (2 * m)

theorem angularCoefficient_pos {m : ℝ} (hm : 0 < m) : 0 < angularCoefficient m :=
  div_pos Constants.ℏ_pos (mul_pos (by norm_num) hm)

/-- Differential angular kinetic on compact tests. -/
def testKinetic (m : ℝ) : Domain →ₗ[ℂ] Domain :=
  -(angularCoefficient m : ℂ) • ∑ i : Fin 2, (D i).comp (D i)

/-- The first bracket consists of the actual two compositions. -/
def bracket (m : ℝ) (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) : Domain →ₗ[ℂ] Domain :=
  (testKinetic m).comp (mulOp f hf) - (mulOp f hf).comp (testKinetic m)

theorem bracket_apply (m : ℝ) (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f)
    (ψ : Domain) (x : Space 2) :
    bracket m f hf ψ x = -(angularCoefficient m : ℂ) *
      ∑ i : Fin 2, (Space.deriv i (Space.deriv i f) x * ψ x +
        2 * Space.deriv i f x * Space.deriv i ψ x) := by
  have h (i : Fin 2) := congrArg (fun u : Domain ↦ u x) (D2_mul i f hf ψ)
  simp only [add_apply, smul_apply, mulOp_apply, D_apply, smul_eq_mul] at h
  simp only [bracket, testKinetic, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, sub_apply, smul_apply, sum_apply,
    mulOp_apply, smul_eq_mul]
  simp_rw [D_apply, h]
  simp only [Fin.sum_univ_two]
  ring

/-- Native Schwartz conversion of the compact smooth test. -/
def toSchwartz (ψ : Domain) : SchwartzMap (Space 2) ℂ :=
  ψ.hasCompactSupport.toSchwartzMap ψ.contDiff

theorem memL2 (ψ : Domain) : MemLp ψ 2 (volume : Measure (Space 2)) :=
  ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport

/-- Actual physical Lebesgue L² inclusion. -/
def toL2 : Domain →ₗ[ℂ] Spatial where
  toFun ψ := (memL2 ψ).toLp ψ
  map_add' ψ φ := (memL2 ψ).toLp_add (memL2 φ)
  map_smul' c ψ := (memL2 ψ).toLp_const_smul c

theorem toL2_ae (ψ : Domain) : (toL2 ψ : Space 2 → ℂ) =ᵐ[volume] ψ :=
  (memL2 ψ).coeFn_toLp

theorem toL2_injective : Function.Injective (toL2 : Domain → Spatial) := by
  intro ψ φ h
  have he : (ψ : Space 2 → ℂ) =ᵐ[volume] φ :=
    (toL2_ae ψ).symm.trans ((Filter.EventuallyEq.of_eq (congrArg
      (fun u : Spatial ↦ (u : Space 2 → ℂ)) h)).trans (toL2_ae φ))
  exact TestFunction.ext
    (congrFun ((ψ.continuous.ae_eq_iff_eq volume φ.continuous).mp he))


/-- Plane wave at an actual Cartesian coordinate. -/
def phase (k : Fin 2) (q : ℝ) (x : Space 2) : ℂ :=
  Complex.exp (((q * x k : ℝ) : ℂ) * Complex.I)

theorem phase_smooth (k : Fin 2) (q : ℝ) : ContDiff ℝ ∞ (phase k q) := by
  have hz : ContDiff ℝ ∞ (fun x : Space 2 ↦ (x k : ℂ)) :=
    by simpa only [Function.comp_def, Complex.ofRealCLM_apply,
      Space.coordCLM_apply, Space.coord_apply] using
      Complex.ofRealCLM.contDiff.comp (Space.coordCLM k).contDiff
  unfold phase
  simp_rw [Complex.ofReal_mul]
  exact (((contDiff_const (c := (q : ℂ))).mul hz).mul
    (contDiff_const (c := Complex.I))).cexp

theorem phase_deriv (i k : Fin 2) (q : ℝ) (x : Space 2) :
    Space.deriv i (phase k q) x =
      if i = k then phase k q x * (Complex.I * (q : ℂ)) else 0 := by
  let z := Complex.ofRealCLM.comp (Space.coordCLM k)
  have h := ((z.hasFDerivAt (x := x)).const_smul (Complex.I * (q : ℂ))).cexp
  have he : (fun y ↦ Complex.exp ((Complex.I * (q : ℂ)) • z y)) = phase k q := by
    funext y
    simp only [phase, z, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      Space.coordCLM_apply, Space.coord_apply, smul_eq_mul, Complex.ofReal_mul]
    congr 1
    ring
  change HasFDerivAt (fun y ↦ Complex.exp ((Complex.I * (q : ℂ)) • z y)) _ x at h
  rw [he] at h
  have hx := congrFun he x
  rw [Space.deriv_eq, h.fderiv]
  change (Complex.exp ((Complex.I * (q : ℂ)) • z x) •
    (Complex.I * (q : ℂ)) • z) (Space.basis i) = _
  rw [hx]
  simp only [smul_apply, z, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, Space.coordCLM_apply, Space.coord_apply, Space.basis_apply,
    smul_eq_mul]
  split_ifs <;> simp_all

def modulate (k : Fin 2) (q : ℝ) : Domain →ₗ[ℂ] Domain :=
  mulOp (phase k q) (phase_smooth k q)

theorem bracket_modulate (m : ℝ) (k : Fin 2) (q : ℝ)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (χ : Domain) :
    bracket m f hf (modulate k q χ) =
      modulate k q (bracket m f hf χ -
        (2 * (angularCoefficient m : ℂ) * Complex.I * (q : ℂ)) •
          mulOp (Space.deriv k f) (deriv_smooth k hf) χ) := by
  ext x
  have hd (i : Fin 2) := congrArg (fun u : Domain ↦ u x)
    (D_mul i (phase k q) (phase_smooth k q) χ)
  simp only [D_apply, mulOp_apply, add_apply, phase_deriv] at hd
  rw [bracket_apply]
  change _ = phase k q x * (_ - _)
  rw [bracket_apply]
  change _ = phase k q x * (_ -
    (2 * (angularCoefficient m : ℂ) * Complex.I * (q : ℂ)) *
      (Space.deriv k f x * χ x))
  change -(angularCoefficient m : ℂ) * ∑ i : Fin 2,
    (Space.deriv i (Space.deriv i f) x * (phase k q x * χ x) +
      2 * Space.deriv i f x * Space.deriv i (modulate k q χ) x) = _
  simp_rw [show ∀ i, Space.deriv i (modulate k q χ) x =
    (if i = k then phase k q x * (Complex.I * (q : ℂ)) else 0) * χ x +
      phase k q x * Space.deriv i χ x from hd]
  fin_cases k <;> simp [Fin.sum_univ_two] <;> ring

theorem phase_norm (k : Fin 2) (q : ℝ) (x : Space 2) : ‖phase k q x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Isometry in physical two-dimensional Lebesgue L². -/
theorem modulate_norm (k : Fin 2) (q : ℝ) (ψ : Domain) :
    ‖toL2 (modulate k q ψ)‖ = ‖toL2 ψ‖ := by
  change ‖(memL2 (modulate k q ψ)).toLp _‖ = ‖(memL2 ψ).toLp _‖
  rw [Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  apply eLpNorm_congr_norm_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    change ‖phase k q x * ψ x‖ = ‖ψ x‖
    rw [norm_mul, phase_norm, one_mul])

/-- The response grows linearly with actual spatial modulation frequency. -/
theorem packet_lower_bound (m : ℝ) (k : Fin 2) (q : ℝ)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (χ : Domain) :
    2 * |angularCoefficient m| * |q| *
        ‖toL2 (mulOp (Space.deriv k f) (deriv_smooth k hf) χ)‖ -
        ‖toL2 (bracket m f hf χ)‖ ≤
      ‖toL2 (bracket m f hf (modulate k q χ))‖ := by
  rw [bracket_modulate, modulate_norm, map_sub, map_smul]
  have hb := norm_sub_norm_le
    ((2 * (angularCoefficient m : ℂ) * Complex.I * (q : ℂ)) •
      toL2 (mulOp (Space.deriv k f) (deriv_smooth k hf) χ))
    (toL2 (bracket m f hf χ))
  rw [norm_sub_rev] at hb
  simpa [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc] using hb

/-- Continuity, rather than a point mass, gives positive physical L² norm. -/
theorem derivative_product_norm_pos (k : Fin 2) (f : Space 2 → ℂ)
    (hf : ContDiff ℝ ∞ f) (χ : Domain) (hne : ∃ x, Space.deriv k f x * χ x ≠ 0) :
    0 < ‖toL2 (mulOp (Space.deriv k f) (deriv_smooth k hf) χ)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have he : mulOp (Space.deriv k f) (deriv_smooth k hf) χ = 0 :=
    toL2_injective (by simpa using hz)
  obtain ⟨x, hx⟩ := hne
  exact hx (congrArg (fun u : Domain ↦ u x) he)

/-- Actual unit packets with arbitrarily large first bracket, with explicit nondegeneracy. -/
theorem no_finite_packet_bound {m : ℝ} (hm : 0 < m) (k : Fin 2)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (χ : Domain)
    (hχ : ‖toL2 χ‖ = 1) (hne : ∃ x, Space.deriv k f x * χ x ≠ 0) (R : ℝ) :
    ∃ ψ : Domain, ‖toL2 ψ‖ = 1 ∧ R < ‖toL2 (bracket m f hf ψ)‖ := by
  let p := ‖toL2 (mulOp (Space.deriv k f) (deriv_smooth k hf) χ)‖
  have hp : 0 < p := derivative_product_norm_pos k f hf χ hne
  have ha := angularCoefficient_pos hm
  have hc : 0 < 2 * angularCoefficient m * p := by positivity
  obtain ⟨q, hq⟩ := exists_nat_gt ((R + ‖toL2 (bracket m f hf χ)‖) /
    (2 * angularCoefficient m * p))
  have hq' := (div_lt_iff₀ hc).mp hq
  have hb := packet_lower_bound m k (q : ℝ) f hf χ
  rw [abs_of_pos ha, abs_of_nonneg (Nat.cast_nonneg q)] at hb
  refine ⟨modulate k q χ, (modulate_norm k q χ).trans hχ, ?_⟩
  dsimp [p] at *
  nlinarith

/-- Normalization is derived from nondegeneracy. -/
theorem no_domain_bound {m : ℝ} (hm : 0 < m) (k : Fin 2)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (χ : Domain)
    (hne : ∃ x, Space.deriv k f x * χ x ≠ 0) (R : ℝ) :
    ∃ ψ : Domain, ‖toL2 ψ‖ = 1 ∧ R < ‖toL2 (bracket m f hf ψ)‖ := by
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
  have hprod : ∃ x, Space.deriv k f x * (b • χ) x ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    change Space.deriv k f x * (b * χ x) ≠ 0
    rw [mul_left_comm]
    exact mul_ne_zero hb hx
  exact no_finite_packet_bound hm k f hf (b • χ) hunit hprod R


/-- A genuine compact smooth packet can take value one at any physical point. -/
theorem exists_packet_at (x : Space 2) : ∃ χ : Domain, χ x = 1 := by
  obtain ⟨b, _, hc, hd, _, h1⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (s := univ) (x := x) (by simp)
  refine ⟨{ toFun := Complex.ofReal ∘ b
            contDiff' := Complex.ofRealCLM.contDiff.comp hd
            hasCompactSupport' := hc.comp_left (g := Complex.ofReal) (by simp)
            tsupport_subset' := subset_univ _ }, ?_⟩
  change (b x : ℂ) = 1
  simp [h1]

/-- Nonconstancy forces a genuine nonzero coordinate derivative. -/
theorem exists_deriv_ne_zero (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x y, f x ≠ f y) : ∃ k x, Space.deriv k f x ≠ 0 := by
  by_contra h
  push Not at h
  have hz (x : Space 2) : fderiv ℝ f x = 0 := by
    ext v
    rw [Space.fderiv_eq_sum_deriv]
    simp [h]
  obtain ⟨x, y, hxy⟩ := hn
  exact hxy (is_const_of_fderiv_eq_zero (hf.differentiable (by simp)) hz x y)

/-- A nonconstant profile supplies nondegeneracy without assuming a norm bound. -/
theorem no_domain_bound_of_nonconstant {m : ℝ} (hm : 0 < m)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hn : ∃ x y, f x ≠ f y) (R : ℝ) :
    ∃ ψ : Domain, ‖toL2 ψ‖ = 1 ∧ R < ‖toL2 (bracket m f hf ψ)‖ := by
  obtain ⟨k, x, hx⟩ := exists_deriv_ne_zero f hf hn
  obtain ⟨χ, hχ⟩ := exists_packet_at x
  exact no_domain_bound hm k f hf χ ⟨x, by simpa [hχ] using hx⟩ R

/-- A real compact smooth density coefficient with unit Cartesian slope at zero. -/
theorem exists_compact_real_profile (k : Fin 2) :
    ∃ f : Space 2 → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      Space.deriv k (fun x ↦ (f x : ℂ)) 0 = 1 := by
  obtain ⟨b, _, hc, hd, _, h1⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (s := univ) (x := (0 : Space 2)) (by simp)
  let f : Space 2 → ℝ := fun x ↦ b x * Space.coordCLM k x
  refine ⟨f, hd.mul (Space.coordCLM k).contDiff, hc.mul_right, ?_⟩
  have hd' := (Complex.ofRealCLM.hasFDerivAt.comp 0
    ((hd.differentiable (by simp)).differentiableAt.hasFDerivAt.mul
      (Space.coordCLM k).hasFDerivAt))
  change fderiv ℝ (fun x ↦ (f x : ℂ)) 0 (Space.basis k) = 1
  change HasFDerivAt (fun x ↦ (f x : ℂ)) _ 0 at hd'
  rw [hd'.fderiv]
  simp [Space.coordCLM_apply, Space.coord_apply, h1]

open QuantumMechanics.SpaceDHilbertSpace

/-- The test inclusion is exactly the existing native Schwartz inclusion. -/
theorem toL2_eq_schwartz (ψ : Domain) :
    toL2 ψ = (schwartzEquiv volume (toSchwartz ψ) : Spatial) := rfl

theorem toL2_mem_kinetic (m : ℝ) (ψ : Domain) :
    toL2 ψ ∈ (PolaritonSpatialGenerator.kinetic m).domain := by
  rw [toL2_eq_schwartz]
  exact PolaritonSpatialGenerator.schwartz_mem_kinetic m (toSchwartz ψ)

/-- Conversion preserves the two actual Cartesian differential operations. -/
theorem toSchwartz_D (i : Fin 2) (ψ : Domain) :
    toSchwartz (D i ψ) = LineDeriv.lineDerivOp (Space.basis i) (toSchwartz ψ) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

/-- The compact differential action is the physical closed angular kinetic action. -/
theorem kinetic_on_test {m : ℝ} (hm : 0 < m) (ψ : Domain) :
    PolaritonSpatialGenerator.kinetic m ⟨toL2 ψ, toL2_mem_kinetic m ψ⟩ =
      toL2 (testKinetic m ψ) := by
  have h := PolaritonSpatialGenerator.kinetic_schwartz_laplacian hm (toSchwartz ψ)
  change PolaritonSpatialGenerator.kinetic m ⟨toL2 ψ, _⟩ = _ at h
  rw [h, toL2_eq_schwartz,
    SchwartzSubmodule.schwartzEquiv_apply_coe]
  rw [← map_smul]
  congr 1
  ext x
  simp only [testKinetic, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    toSchwartz, smul_apply, sum_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, angularCoefficient,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rfl


/-- A compact continuous coefficient defines an actual physical L∞ class. -/
def profile (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    PolaritonSpatialGenerator.Profile :=
  (hf.continuous.memLp_top_of_hasCompactSupport hc volume).toLp f

theorem profile_ae (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (profile f hf hc : Space 2 → ℂ) =ᵐ[volume] f :=
  (hf.continuous.memLp_top_of_hasCompactSupport hc volume).coeFn_toLp

/-- Genuine L∞ multiplication agrees with multiplication of the compact tests. -/
theorem multiplier_on_test (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (ψ : Domain) :
    PolaritonSpatialGenerator.multiplier (profile f hf hc) (toL2 ψ) =
      toL2 (mulOp f hf ψ) := by
  apply Lp.ext
  filter_upwards [PolaritonSpatialGenerator.multiplier_ae (profile f hf hc) (toL2 ψ),
    profile_ae f hf hc, toL2_ae ψ, toL2_ae (mulOp f hf ψ)] with x hM hf' hψ hprod
  rw [hM, hf', hψ, hprod, mulOp_apply]

/-- Measurable bounded potentials commute; no potential differentiation is used. -/
theorem multipliers_commute (v w : PolaritonSpatialGenerator.Profile) (u : Spatial) :
    PolaritonSpatialGenerator.multiplier v (PolaritonSpatialGenerator.multiplier w u) =
      PolaritonSpatialGenerator.multiplier w (PolaritonSpatialGenerator.multiplier v u) := by
  apply Lp.ext
  filter_upwards [PolaritonSpatialGenerator.multiplier_ae v
      (PolaritonSpatialGenerator.multiplier w u),
    PolaritonSpatialGenerator.multiplier_ae w (PolaritonSpatialGenerator.multiplier v u),
    PolaritonSpatialGenerator.multiplier_ae v u,
    PolaritonSpatialGenerator.multiplier_ae w u] with x hvw hwv hv hw
  rw [hvw, hwv, hv, hw]
  ring

theorem spatialDiagonal_commute (offset : ℝ) (v w : PolaritonSpatialGenerator.Profile)
    (u : Spatial) :
    PolaritonSpatialGenerator.spatialDiagonal offset v
        (PolaritonSpatialGenerator.multiplier w u) =
      PolaritonSpatialGenerator.multiplier w
        (PolaritonSpatialGenerator.spatialDiagonal offset v u) := by
  simp only [PolaritonSpatialGenerator.spatialDiagonal, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_add, map_smul]
  rw [multipliers_commute]

section Coupled

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Physical bounded photon-only density multiplier on the actual coupled Hilbert product. -/
def density (v : PolaritonSpatialGenerator.Profile) :
    PolaritonSpatialGenerator.State E →L[ℂ] PolaritonSpatialGenerator.State E :=
  PolaritonSpatialGenerator.liftBlock .photon .photon (PolaritonSpatialGenerator.multiplier v)

omit [CompleteSpace E] in
theorem density_photon (v : PolaritonSpatialGenerator.Profile)
    (u : PolaritonSpatialGenerator.State E) :
    PolaritonSpatialGenerator.projection E .photon (density v u) =
      PolaritonSpatialGenerator.multiplier v
        (PolaritonSpatialGenerator.projection E .photon u) := by
  simp only [density, PolaritonSpatialGenerator.liftBlock, ContinuousLinearMap.comp_apply]
  rw [PolaritonSpatialGenerator.projection_injection_same]

omit [CompleteSpace E] in
theorem density_injection (v : PolaritonSpatialGenerator.Profile) (u : Spatial) :
    density (E := E) v (PolaritonSpatialGenerator.injection E .photon u) =
      PolaritonSpatialGenerator.injection E .photon (PolaritonSpatialGenerator.multiplier v u) := by
  simp only [density, PolaritonSpatialGenerator.liftBlock, ContinuousLinearMap.comp_apply]
  rw [PolaritonSpatialGenerator.projection_injection_same]

/-- Both coordinates with zero input satisfy their native domains, including the bath graph. -/
def photonTest (p : PolaritonSpatialGenerator.Model E) (ψ : Domain) :
    (PolaritonSpatialGenerator.generator p).domain :=
  PolaritonSpatialGenerator.photonInput p (toL2 ψ) (toL2_mem_kinetic p.mPhoton ψ)

/-- The density image is an exact coupled-domain element, by compact smooth multiplication. -/
theorem density_test_domain (p : PolaritonSpatialGenerator.Model E)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ψ : Domain) :
    density (profile f hf hc) (photonTest p ψ).val = (photonTest p (mulOp f hf ψ)).val := by
  change density (profile f hf hc) (PolaritonSpatialGenerator.injection E .photon (toL2 ψ)) = _
  rw [density_injection, multiplier_on_test]
  rfl

theorem density_test_mem_domain (p : PolaritonSpatialGenerator.Model E)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ψ : Domain) :
    density (profile f hf hc) (photonTest p ψ).val ∈
      (PolaritonSpatialGenerator.generator p).domain := by
  rw [density_test_domain]
  exact (photonTest p (mulOp f hf ψ)).property

/-- The actual coupled first bracket on its common compact photon test domain.
The first input has value exactly `M_f Jγ ψ`, as proved by `density_test_domain`. -/
def coupledBracket (p : PolaritonSpatialGenerator.Model E)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ψ : Domain) :
    PolaritonSpatialGenerator.State E :=
  PolaritonSpatialGenerator.generator p (photonTest p (mulOp f hf ψ)) -
    density (profile f hf hc) (PolaritonSpatialGenerator.generator p (photonTest p ψ))

/-- Compression of the full bracket, after applying the full coupled generator.
Rabi and bath couplings vanish in this projection only; no sector invariance is assumed. -/
theorem coupledBracket_compression (p : PolaritonSpatialGenerator.Model E)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ψ : Domain) :
    PolaritonSpatialGenerator.projection E .photon (coupledBracket p f hf hc ψ) =
      toL2 (bracket p.mPhoton f hf ψ) := by
  unfold coupledBracket
  rw [map_sub, density_photon]
  change _ - PolaritonSpatialGenerator.multiplier (profile f hf hc)
    (PolaritonSpatialGenerator.projection E .photon
      (PolaritonSpatialGenerator.generator p
        (PolaritonSpatialGenerator.photonInput p (toL2 ψ) _))) = _
  rw [show photonTest p (mulOp f hf ψ) =
    PolaritonSpatialGenerator.photonInput p (toL2 (mulOp f hf ψ))
      (toL2_mem_kinetic p.mPhoton (mulOp f hf ψ)) from rfl]
  rw [PolaritonSpatialGenerator.photon_compression,
    PolaritonSpatialGenerator.photon_compression, kinetic_on_test p.mPhoton_pos,
    kinetic_on_test p.mPhoton_pos, map_add]
  rw [← multiplier_on_test f hf hc ψ, spatialDiagonal_commute]
  rw [multiplier_on_test f hf hc (testKinetic p.mPhoton ψ)]
  simp only [bracket, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  abel

/-- Exact differential formula for the photon compression of the full first bracket. -/
theorem coupledBracket_compression_ae (p : PolaritonSpatialGenerator.Model E)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ψ : Domain) :
    (PolaritonSpatialGenerator.projection E .photon (coupledBracket p f hf hc ψ) :
      Space 2 → ℂ) =ᵐ[volume] fun x ↦ -(angularCoefficient p.mPhoton : ℂ) *
        ∑ i : Fin 2, (Space.deriv i (Space.deriv i f) x * ψ x +
          2 * Space.deriv i f x * Space.deriv i ψ x) := by
  rw [coupledBracket_compression]
  exact (toL2_ae _).trans (Filter.Eventually.of_forall (bracket_apply _ _ _ _))

/-- The bracket is literally `K M_f Jγψ - M_f K Jγψ` with the proved graph membership. -/
theorem coupledBracket_eq_commutator (p : PolaritonSpatialGenerator.Model E)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ψ : Domain) :
    coupledBracket p f hf hc ψ =
      PolaritonSpatialGenerator.generator p
        ⟨density (profile f hf hc) (photonTest p ψ).val,
          density_test_mem_domain p f hf hc ψ⟩ -
        density (profile f hf hc) (PolaritonSpatialGenerator.generator p (photonTest p ψ)) := by
  have he : (⟨density (profile f hf hc) (photonTest p ψ).val,
      density_test_mem_domain p f hf hc ψ⟩ : (PolaritonSpatialGenerator.generator p).domain) =
        photonTest p (mulOp f hf ψ) := Subtype.ext (density_test_domain p f hf hc ψ)
  rw [he]
  rfl

/-- Projection cannot increase the physical product Hilbert norm. -/
theorem compressed_norm_le (p : PolaritonSpatialGenerator.Model E)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ψ : Domain) :
    ‖toL2 (bracket p.mPhoton f hf ψ)‖ ≤ ‖coupledBracket p f hf hc ψ‖ := by
  rw [← coupledBracket_compression p f hf hc ψ]
  exact PiLp.norm_apply_le (coupledBracket p f hf hc ψ) .photon

theorem photonTest_norm (p : PolaritonSpatialGenerator.Model E) (ψ : Domain) :
    ‖(photonTest p ψ).val‖ = ‖toL2 ψ‖ :=
  PiLp.norm_single 2 (PolaritonSpatialGenerator.Fiber E) .photon (toL2 ψ)

/-- Arbitrarily large full coupled first brackets on normalized physical photon inputs.
No restriction is placed on the Rabi or bath coupling beyond the original model data. -/
theorem no_coupled_domain_bound (p : PolaritonSpatialGenerator.Model E)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (k : Fin 2) (χ : Domain) (hne : ∃ x, Space.deriv k f x * χ x ≠ 0) (R : ℝ) :
    ∃ ψ : Domain, ‖(photonTest p ψ).val‖ = 1 ∧ R < ‖coupledBracket p f hf hc ψ‖ := by
  obtain ⟨ψ, hψ, hR⟩ := no_domain_bound p.mPhoton_pos k f hf χ hne R
  exact ⟨ψ, (photonTest_norm p ψ).trans hψ,
    hR.trans_le (compressed_norm_le p f hf hc ψ)⟩

/-- No ambient bounded operator extends the full coupled first bracket on these tests. -/
theorem no_bounded_coupled_extension (p : PolaritonSpatialGenerator.Model E)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (k : Fin 2) (χ : Domain) (hne : ∃ x, Space.deriv k f x * χ x ≠ 0) :
    ¬ ∃ A : PolaritonSpatialGenerator.State E →L[ℂ] PolaritonSpatialGenerator.State E,
      ∀ ψ : Domain, A (photonTest p ψ).val = coupledBracket p f hf hc ψ := by
  rintro ⟨A, hA⟩
  obtain ⟨ψ, hψ, hR⟩ := no_coupled_domain_bound p f hf hc k χ hne ‖A‖
  have hb := A.le_opNorm (photonTest p ψ).val
  rw [hA ψ, hψ, mul_one] at hb
  exact (not_lt_of_ge hb) hR

/-- Nonconstancy of the actual compact profile suffices for the coupled obstruction. -/
theorem no_bounded_coupled_extension_of_nonconstant (p : PolaritonSpatialGenerator.Model E)
    (f : Space 2 → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hn : ∃ x y, f x ≠ f y) :
    ¬ ∃ A : PolaritonSpatialGenerator.State E →L[ℂ] PolaritonSpatialGenerator.State E,
      ∀ ψ : Domain, A (photonTest p ψ).val = coupledBracket p f hf hc ψ := by
  obtain ⟨k, x, hx⟩ := exists_deriv_ne_zero f hf hn
  obtain ⟨χ, hχ⟩ := exists_packet_at x
  exact no_bounded_coupled_extension p f hf hc k χ ⟨x, by simpa [hχ] using hx⟩

/-- The obstruction is inhabited by a real compact smooth physical photon multiplier. -/
theorem exists_real_coupled_obstruction (p : PolaritonSpatialGenerator.Model E) :
    ∃ f : Space 2 → ℝ, ∃ hf : ContDiff ℝ ∞ (fun x ↦ (f x : ℂ)),
      ∃ hc : HasCompactSupport (fun x ↦ (f x : ℂ)),
        PolaritonSpatialGenerator.RealProfile (profile _ hf hc) ∧
        ¬ ∃ A : PolaritonSpatialGenerator.State E →L[ℂ] PolaritonSpatialGenerator.State E,
          ∀ ψ : Domain, A (photonTest p ψ).val = coupledBracket p _ hf hc ψ := by
  obtain ⟨f, hf, hc, hd⟩ := exists_compact_real_profile 0
  let hf' : ContDiff ℝ ∞ (fun x ↦ (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  let hc' : HasCompactSupport (fun x ↦ (f x : ℂ)) :=
    hc.comp_left (g := Complex.ofReal) (by simp)
  refine ⟨f, hf', hc', ?_, ?_⟩
  · filter_upwards [profile_ae _ hf' hc'] with x hx
    simp only [hx, Complex.conj_ofReal]
  · obtain ⟨χ, hχ⟩ := exists_packet_at 0
    apply no_bounded_coupled_extension p _ hf' hc' 0 χ
    exact ⟨0, by simp [hd, hχ]⟩

end Coupled

/-- Constant coefficient control for the compressed kinetic bracket.
A photon-only constant on the coupled space need not commute with off-diagonal exchange. -/
theorem bracket_constant_control (m : ℝ) (c : ℂ) (ψ : Domain) :
    bracket m (fun _ ↦ c) contDiff_const ψ = 0 := by
  ext x
  rw [bracket_apply]
  have hd (i : Fin 2) : Space.deriv i (fun _ : Space 2 ↦ c) = 0 := by
    funext y
    simp [Space.deriv_eq]
  simp [hd, Space.deriv_eq]

end SKEFTHawking.DKMBootstrap.PolaritonDensityCommutator
