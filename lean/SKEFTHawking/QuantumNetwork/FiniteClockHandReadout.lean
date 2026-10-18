import SKEFTHawking.QuantumNetwork.FiniteGibbsClock
import SKEFTHawking.QuantumNetwork.FiniteNontracialThermalPhase

/-!
# A prepared two-level hand with a fixed projective readout

The Hamiltonian and its exponential are defined independently of the Born law.
Durations are external real parameters; interval inversion is a deterministic
calibration within this finite model.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteClockHandReadout
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
abbrev A := Fin 2
abbrev Mat := Matrix A A ℂ

def H (ω ℏ : ℝ) : Mat := FiniteGibbsClock.twoLevel (ℏ * ω)
def U (ω ℏ t : ℝ) : Mat :=
  FiniteGibbsClock.expCoeff (H ω ℏ) (-Complex.I * (t / ℏ))

theorem H_hermitian (ω ℏ : ℝ) : (H ω ℏ).IsHermitian :=
  FiniteGibbsClock.twoLevel_hermitian _

theorem H_nondegenerate {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : 0 < ℏ) :
    H ω ℏ 0 0 ≠ H ω ℏ 1 1 := by
  simp only [H, FiniteGibbsClock.twoLevel, Matrix.diagonal_apply_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact_mod_cast (ne_of_gt (mul_pos hℏ hω)).symm

theorem U_phase {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    U ω ℏ t = FiniteNontracialThermalPhase.V (ω*t) := by
  have he : (-Complex.I * ((t / ℏ : ℝ) : ℂ)) • H ω ℏ =
      (-Complex.I * ((ω*t : ℝ) : ℂ)) • FiniteGibbsClock.twoLevel 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [H, FiniteGibbsClock.twoLevel] <;> push_cast <;> field_simp <;> ring
  simpa only [U, FiniteNontracialThermalPhase.V, FiniteGibbsClock.expCoeff, Complex.ofReal_div] using congrArg NormedSpace.exp he

theorem U_diagonal {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    U ω ℏ t = Matrix.diagonal (![1, Complex.exp (-Complex.I * (ω*t))] : A → ℂ) := by
  rw [U_phase hℏ, FiniteNontracialThermalPhase.V_diagonal]
  simp only [Complex.ofReal_mul]

theorem U_adjoint {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    (U ω ℏ t)ᴴ = U ω ℏ (-t) := by
  simp only [U_phase hℏ, FiniteNontracialThermalPhase.V_adjoint, mul_neg]

theorem U_unitary {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    U ω ℏ t ∈ Matrix.unitaryGroup A ℂ := by
  rw [U_phase hℏ]
  exact FiniteNontracialThermalPhase.V_unitary _

theorem U_group (ω ℏ t s : ℝ) : U ω ℏ (t+s) = U ω ℏ t * U ω ℏ s := by
  simp only [U, add_div, Complex.ofReal_add, mul_add,
    FiniteGibbsClock.expCoeff_add]

def v : A → ℂ := fun _ => (Real.sqrt 2 : ℂ)⁻¹
def rhoPlus : Mat := Matrix.vecMulVec v (star v)
def Q (a : A) : Mat := if a = 0 then !![1/2,-1/2; -1/2,1/2] else !![1/2,1/2;1/2,1/2]

theorem sqrt_two_square : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)

theorem rhoPlus_eq : rhoPlus = Q 1 := by
  have hh : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
    rw [← mul_inv, sqrt_two_square]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;> simpa [rhoPlus, v, Q, Matrix.vecMulVec] using hh

theorem Q_adjoint (a : A) : (Q a)ᴴ = Q a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> norm_num [Q, Matrix.conjTranspose_apply]

theorem Q_mul (a b : A) : Q a * Q b = if a=b then Q a else 0 := by
  ext i j
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [Q, Matrix.mul_apply, Fin.sum_univ_two]

theorem Q_complete : (∑ a : A, Q a) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Q, Fin.sum_univ_two, Matrix.one_apply]

theorem Q_trace (a : A) : (Q a).trace = 1 := by
  fin_cases a <;> norm_num [Q, Matrix.trace, Fin.sum_univ_two]

theorem Q_density (a : A) : IsDensityOperator (Q a) := by
  refine ⟨?_, Q_trace a⟩
  have h := Matrix.posSemidef_conjTranspose_mul_self (Q a)
  rwa [Q_adjoint, Q_mul, if_pos rfl] at h

theorem rhoPlus_density : IsDensityOperator rhoPlus := by
  rw [rhoPlus_eq]; exact Q_density 1

def rho (ω ℏ t : ℝ) : Mat := U ω ℏ t * rhoPlus * (U ω ℏ t)ᴴ
def p (ω t : ℝ) : ℝ := (1 - Real.cos (ω*t))/2
def mass (ω t : ℝ) (a : A) : ℝ := if a=0 then p ω t else 1-p ω t

theorem rho_density {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) : IsDensityOperator (rho ω ℏ t) := by
  have h := krausMap_isDensityOperator
    (isKrausChannel_unitaryKraus (U_unitary hℏ ω t)) rhoPlus_density
  simpa [unitaryKraus, krausMap, rho] using h

theorem p_nonneg (ω t : ℝ) : 0 ≤ p ω t := by
  have := Real.cos_le_one (ω*t); unfold p; linarith

theorem p_le_one (ω t : ℝ) : p ω t ≤ 1 := by
  have := Real.neg_one_le_cos (ω*t); unfold p; linarith

theorem mass_nonneg (ω t : ℝ) (a : A) : 0 ≤ mass ω t a := by
  fin_cases a <;> simp [mass, p_nonneg, sub_nonneg.mpr (p_le_one ω t)]

theorem mass_sum (ω t : ℝ) : (∑ a : A, mass ω t a) = 1 := by
  simp [mass, Fin.sum_univ_two]

theorem rho_C {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    rho ω ℏ t = FiniteNontracialThermalPhase.C (ω*t) rhoPlus := by
  simp only [rho, U_phase hℏ, FiniteNontracialThermalPhase.V_adjoint]
  simp [FiniteNontracialThermalPhase.V, FiniteNontracialThermalPhase.C, FiniteGibbsClock.conjugate]

theorem rho_entries {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    rho ω ℏ t = !![1/2, ((Real.cos (ω*t):ℂ) + Complex.I*Real.sin (ω*t))/2;
      ((Real.cos (ω*t):ℂ) - Complex.I*Real.sin (ω*t))/2, 1/2] := by
  rw [rho_C hℏ, rhoPlus_eq]
  ext i j
  simp only [FiniteNontracialThermalPhase.C_entry]
  fin_cases i <;> fin_cases j <;> simp [Q, sub_eq_add_neg, div_eq_mul_inv]
  · rw [show Complex.I * ((ω:ℂ)*t) = ((ω*t:ℝ):ℂ)*Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I]
    simp [mul_comm]
  · rw [show -(Complex.I * ((ω:ℂ)*t)) = ((-(ω*t):ℝ):ℂ)*Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I]
    simp [mul_comm]

theorem born {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) :
    ((Q a * rho ω ℏ t).trace).re = mass ω t a := by
  rw [rho_entries hℏ]
  fin_cases a <;>
    simp [Q, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, mass, p,
      Complex.mul_re, Complex.mul_im, Complex.add_re, ← Complex.ofReal_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin] <;> ring

theorem sandwich {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) :
    Q a * rho ω ℏ t * Q a = (mass ω t a : ℂ) • Q a := by
  rw [rho_entries hℏ]
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [Q, Matrix.mul_apply, Fin.sum_univ_two, mass, p] <;> push_cast <;> ring

theorem p_zero (ω : ℝ) : p ω 0 = 0 := by simp [p]

theorem p_keep {ω : ℝ} (hω : ω ≠ 0) : p ω (Real.pi/ω) = 1 := by
  simp [p, mul_div_cancel₀ Real.pi hω]

theorem p_left {ω : ℝ} (hω : ω ≠ 0) : p ω (Real.pi/(3*ω)) = 1/4 := by
  have h : ω*(Real.pi/(3*ω)) = Real.pi/3 := by field_simp <;> ring
  rw [p, h, Real.cos_pi_div_three]; norm_num

theorem p_right {ω : ℝ} (hω : ω ≠ 0) : p ω (2*Real.pi/(3*ω)) = 3/4 := by
  have h : ω*(2*Real.pi/(3*ω)) = Real.pi - Real.pi/3 := by field_simp <;> ring
  rw [p, h, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num

theorem p_periodic {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    p ω (t+2*Real.pi/ω) = p ω t := by
  have h : ω*(t+2*Real.pi/ω) = ω*t+2*Real.pi := by field_simp <;> ring
  simp only [p, h, Real.cos_add_two_pi]

theorem p_reflection (ω t : ℝ) : p ω (-t) = p ω t := by simp [p]

theorem p_phase_bound (ω ω' t s : ℝ) :
    |p ω t - p ω' s| ≤ min 1 (|ω*t-ω'*s|/2) := by
  apply le_min
  · have h := p_nonneg ω t
    have h' := p_nonneg ω' s
    have j := p_le_one ω t
    have j' := p_le_one ω' s
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have h := Real.lipschitzWith_cos.dist_le_mul (ω*t) (ω'*s)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    have he : p ω t - p ω' s = -(Real.cos (ω*t)-Real.cos (ω'*s))/2 := by unfold p; ring
    rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right h (by norm_num)

theorem p_hasDerivAt (ω t : ℝ) :
    HasDerivAt (p ω) (ω * Real.sin (ω*t)/2) t := by
  unfold p
  convert (((Real.hasDerivAt_cos (ω*t)).comp t ((hasDerivAt_id t).const_mul ω)).const_sub 1).div_const 2 using 1 <;> first | rfl | ring

def interval (ω : ℝ) : Set ℝ := Set.Icc (Real.pi/(3*ω)) (2*Real.pi/(3*ω))

theorem interval_phase {ω t : ℝ} (hω : 0 < ω) (ht : t ∈ interval ω) :
    ω*t ∈ Set.Icc (Real.pi/3) (2*Real.pi/3) := by
  constructor
  · have h := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<3) hω)).mp ht.1
    nlinarith
  · have h := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<3) hω)).mp ht.2
    nlinarith

theorem sin_calibration {x : ℝ} (hx : x ∈ Set.Icc (Real.pi/3) (2*Real.pi/3)) :
    1/2 ≤ Real.sin x := by
  have hp := Real.pi_pos
  by_cases h : x ≤ Real.pi/2
  · have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith : -(Real.pi/2) ≤ Real.pi/6) h (by linarith [hx.1] : Real.pi/6 ≤ x)
    rwa [Real.sin_pi_div_six] at hh
  · have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith : -(Real.pi/2) ≤ Real.pi/6)
      (by linarith : Real.pi-x ≤ Real.pi/2) (by linarith [hx.2] : Real.pi/6 ≤ Real.pi-x)
    rwa [Real.sin_pi_div_six, Real.sin_pi_sub] at hh

theorem calibration_lower_ordered {ω t s : ℝ} (hω : 0 < ω)
    (ht : t ∈ interval ω) (hs : s ∈ interval ω) (hts : t ≤ s) :
    ω*(s-t)/4 ≤ p ω s-p ω t := by
  have hd x (_ : x ∈ interior (interval ω)) : ω/4 ≤ deriv (p ω) x := by
    rw [(p_hasDerivAt ω x).deriv]
    have hx : x ∈ interval ω := interior_subset ‹x ∈ interior (interval ω)›
    have hh := mul_le_mul_of_nonneg_left (sin_calibration (interval_phase hω hx)) hω.le
    linarith
  have hh := (convex_Icc (Real.pi/(3*ω)) (2*Real.pi/(3*ω))).mul_sub_le_image_sub_of_le_deriv
    (fun x _ => (p_hasDerivAt ω x).continuousAt.continuousWithinAt)
    (fun x _ => (p_hasDerivAt ω x).differentiableAt.differentiableWithinAt) hd t ht s hs hts
  nlinarith

theorem calibration_strictMono {ω : ℝ} (hω : 0 < ω) : StrictMonoOn (p ω) (interval ω) := by
  intro t ht s hs hts
  have h := calibration_lower_ordered hω ht hs hts.le
  have hp := mul_pos hω (sub_pos.mpr hts)
  linarith

theorem calibration_lower {ω t s : ℝ} (hω : 0 < ω)
    (ht : t ∈ interval ω) (hs : s ∈ interval ω) :
    ω*|t-s|/4 ≤ |p ω t-p ω s| := by
  rcases le_total t s with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h),
      abs_of_nonpos (sub_nonpos.mpr ((calibration_strictMono hω).monotoneOn ht hs h))]
    nlinarith [calibration_lower_ordered hω ht hs h]
  · rw [abs_of_nonneg (sub_nonneg.mpr h),
      abs_of_nonneg (sub_nonneg.mpr ((calibration_strictMono hω).monotoneOn hs ht h))]
    exact calibration_lower_ordered hω hs ht h

theorem calibration_upper {ω : ℝ} (hω : 0 ≤ ω) (t s : ℝ) :
    |p ω t-p ω s| ≤ ω*|t-s|/2 := by
  have h := (le_min_iff.mp (p_phase_bound ω ω t s)).2
  rwa [← mul_sub, abs_mul, abs_of_nonneg hω] at h

theorem calibration_range {ω t : ℝ} (hω : 0 < ω) (ht : t ∈ interval ω) :
    p ω t ∈ Set.Icc (1/4) (3/4) := by
  have hab : Real.pi/(3*ω) ≤ 2*Real.pi/(3*ω) :=
    div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) (by positivity)
  have hl := (calibration_strictMono hω).monotoneOn ⟨le_rfl,hab⟩ ht ht.1
  have hr := (calibration_strictMono hω).monotoneOn ht ⟨hab,le_rfl⟩ ht.2
  rw [p_left hω.ne'] at hl
  rw [p_right hω.ne'] at hr
  exact ⟨hl,hr⟩

def inverse (ω q : ℝ) : ℝ := Real.arccos (1-2*q)/ω

theorem inverse_p {ω t : ℝ} (hω : 0 < ω) (ht : t ∈ interval ω) :
    inverse ω (p ω t) = t := by
  have hx := interval_phase hω ht
  have he : 1-2*p ω t = Real.cos (ω*t) := by unfold p; ring
  rw [inverse, he, Real.arccos_cos (by nlinarith [Real.pi_pos, hx.1]) (by nlinarith [Real.pi_pos, hx.2])]
  exact mul_div_cancel_left₀ t hω.ne'

theorem inverse_interval {ω q : ℝ} (hω : 0 < ω) (hq : q ∈ Set.Icc (1/4) (3/4)) :
    inverse ω q ∈ interval ω := by
  have hl := Real.arccos_le_arccos (show 1-2*q ≤ Real.cos (Real.pi/3) by rw [Real.cos_pi_div_three]; linarith [hq.1])
  have hr := Real.arccos_le_arccos (show Real.cos (2*Real.pi/3) ≤ 1-2*q by
    rw [show 2*Real.pi/3 = Real.pi-Real.pi/3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    linarith [hq.2])
  rw [Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])] at hl
  rw [Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])] at hr
  constructor
  · change Real.pi/(3*ω) ≤ Real.arccos (1-2*q)/ω
    rw [div_le_div_iff₀ (by positivity : 0<3*ω) hω]
    nlinarith
  · change Real.arccos (1-2*q)/ω ≤ 2*Real.pi/(3*ω)
    rw [div_le_div_iff₀ hω (by positivity : 0<3*ω)]
    nlinarith

theorem p_inverse {ω q : ℝ} (hω : 0 < ω) (hq : q ∈ Set.Icc (1/4) (3/4)) :
    p ω (inverse ω q) = q := by
  have he : ω*(Real.arccos (1-2*q)/ω) = Real.arccos (1-2*q) := mul_div_cancel₀ _ hω.ne'
  rw [p, inverse, he, Real.cos_arccos (by linarith [hq.2]) (by linarith [hq.1])]
  ring

theorem inverse_error {ω t q : ℝ} (hω : 0 < ω) (ht : t ∈ interval ω)
    (hq : q ∈ Set.Icc (1/4) (3/4)) :
    |inverse ω q-t| ≤ 4*|q-p ω t|/ω := by
  have h := calibration_lower hω (inverse_interval hω hq) ht
  rw [p_inverse hω hq] at h
  apply (le_div_iff₀ hω).mpr
  nlinarith

theorem calibration_image {ω : ℝ} (hω : 0 < ω) :
    p ω '' interval ω = Set.Icc (1/4) (3/4) := by
  ext q
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact calibration_range hω ht
  · intro hq
    exact ⟨inverse ω q, inverse_interval hω hq, p_inverse hω hq⟩

theorem frequency_duration_bound {ω ω' : ℝ} (hω : 0 ≤ ω) (t s : ℝ) :
    |p ω t-p ω' s| ≤ min 1 ((ω*|t-s|+|ω-ω'| * |s|)/2) := by
  refine (p_phase_bound ω ω' t s).trans (min_le_min_left 1 ?_)
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ)≤2)
  calc
    |ω*t-ω'*s| = |ω*(t-s)+(ω-ω')*s| := by congr 1; ring
    _ ≤ |ω*(t-s)|+|(ω-ω')*s| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hω]

theorem born_complex {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) :
    (Q a * rho ω ℏ t).trace = (mass ω t a : ℂ) := by
  rw [rho_entries hℏ]
  fin_cases a <;>
    simp [Q, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, mass, p] <;> push_cast <;> ring

/-- Discarding the input hand and preparing v is represented by these two operators. -/
def R (r : A) : Mat := fun i j => if j=r then v i else 0

theorem R_sandwich (r : A) (X : Mat) :
    R r * X * (R r)ᴴ = X r r • rhoPlus := by
  ext i j
  fin_cases r <;>
    simp [R, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      rhoPlus, Matrix.vecMulVec, mul_comm, mul_left_comm, mul_assoc]

theorem discard_prepare (X : Mat) :
    (∑ r : A, R r * X * (R r)ᴴ) = X.trace • rhoPlus := by
  simp only [R_sandwich, ← Finset.sum_smul, Matrix.trace, Matrix.diag]

theorem R_normalized : IsKrausChannel R := by
  have hh : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
    rw [← mul_inv, sqrt_two_square]; norm_num
  unfold IsKrausChannel
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R, v, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.one_apply, hh] <;> norm_num

def g (ω ℏ t : ℝ) (a r : A) : Mat := Q a * U ω ℏ t * R r

theorem g_sandwich {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) (X : Mat) :
    (∑ r : A, g ω ℏ t a r * X * (g ω ℏ t a r)ᴴ) =
      (mass ω t a : ℂ) • (X.trace • Q a) := by
  simp only [g, Matrix.conjTranspose_mul, Q_adjoint]
  have hh r : Q a * U ω ℏ t * R r * X * ((R r)ᴴ * ((U ω ℏ t)ᴴ * Q a)) =
      Q a * U ω ℏ t * (R r * X * (R r)ᴴ) * (U ω ℏ t)ᴴ * Q a := by
    simp only [Matrix.mul_assoc]
  simp only [hh, ← Finset.mul_sum, ← Finset.sum_mul, discard_prepare]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [smul_comm (mass ω t a : ℂ) X.trace]
  simpa only [rho, Matrix.mul_assoc] using
    congrArg (fun Y : Mat => X.trace • Y) (sandwich hℏ ω t a)

def measured (ω ℏ t : ℝ) : Mat := ∑ a : A, Q a * rho ω ℏ t * Q a

def disturbance (θ : ℝ) : Mat := !![0, Complex.I*Real.sin θ/2; -Complex.I*Real.sin θ/2, 0]

theorem disturbance_matrix {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    rho ω ℏ t-measured ω ℏ t = disturbance (ω*t) := by
  simp only [measured, sandwich hℏ, Fin.sum_univ_two]
  rw [rho_entries hℏ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q, mass, p, disturbance] <;> push_cast <;> ring

theorem disturbance_absOp (θ : ℝ) :
    absOp (disturbance θ) = ((|Real.sin θ|/2:ℝ):ℂ) • (1 : Mat) := by
  have hs : ((|Real.sin θ|:ℝ):ℂ)^2 = (Real.sin θ:ℂ)^2 := by exact_mod_cast sq_abs (Real.sin θ)
  apply posSemidef_eq_of_mul_self_eq (absOp_posSemidef _)
  · exact Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by positivity))
  · rw [absOp_mul_self]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [disturbance, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Matrix.one_apply] <;> push_cast <;>
      simp only [← Complex.ofReal_sin, map_ofNat, Complex.star_def, Complex.conj_ofReal] <;> ring_nf <;>
      simp [Complex.I_sq, Complex.ofReal_pow, Complex.ofReal_sin, hs] <;> ring

theorem measurement_disturbance {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    traceDist (rho ω ℏ t) (measured ω ℏ t) = |Real.sin (ω*t)|/2 := by
  rw [traceDist, disturbance_matrix hℏ, traceNorm_eq_trace_absOp, disturbance_absOp,
    Matrix.trace_smul]
  norm_num [Matrix.trace, Fin.sum_univ_two, Complex.mul_re]
  <;> ring

theorem disturbance_quarter {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) :
    traceDist (rho ω ℏ (Real.pi/(2*ω))) (measured ω ℏ (Real.pi/(2*ω))) = 1/2 := by
  rw [measurement_disturbance hℏ]
  have he : ω*(Real.pi/(2*ω)) = Real.pi/2 := by field_simp <;> ring
  rw [he, Real.sin_pi_div_two]; norm_num

theorem disturbance_zero {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) :
    traceDist (rho ω ℏ 0) (measured ω ℏ 0) = 0 := by
  rw [measurement_disturbance hℏ]; simp

theorem disturbance_keep {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) :
    traceDist (rho ω ℏ (Real.pi/ω)) (measured ω ℏ (Real.pi/ω)) = 0 := by
  rw [measurement_disturbance hℏ, mul_div_cancel₀ Real.pi hω, Real.sin_pi]; norm_num

theorem computational_readout {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) :
    ((Matrix.single a a 1 * rho ω ℏ t).trace).re = 1/2 := by
  rw [rho_entries hℏ]
  fin_cases a <;> norm_num [Matrix.single, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]

theorem scalar_hand (ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    ((Q 0 * rho 0 ℏ t).trace).re = 0 := by
  rw [born hℏ]; simp [mass, p]

theorem U_conjugation {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (X : Mat) :
    U ω ℏ t * X * (U ω ℏ t)ᴴ = FiniteNontracialThermalPhase.C (ω*t) X := by
  simp only [U_phase hℏ, FiniteNontracialThermalPhase.V_adjoint]
  simp [FiniteNontracialThermalPhase.V, FiniteNontracialThermalPhase.C, FiniteGibbsClock.conjugate]

theorem gibbs_diagonal (ω ℏ β : ℝ) :
    FiniteGibbsClock.gibbs (H ω ℏ) β =
      Matrix.diagonal (fun i => FiniteGibbsClock.gibbs (H ω ℏ) β i i) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FiniteGibbsClock.gibbs, FiniteGibbsClock.boltzmann, H, FiniteGibbsClock.twoLevel,
      ← Matrix.diagonal_smul, Matrix.exp_diagonal]

theorem gibbs_stationary {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω β t : ℝ) :
    U ω ℏ t * FiniteGibbsClock.gibbs (H ω ℏ) β * (U ω ℏ t)ᴴ =
      FiniteGibbsClock.gibbs (H ω ℏ) β := by
  rw [U_conjugation hℏ, gibbs_diagonal ω ℏ β,
    FiniteNontracialThermalPhase.C_diagonal]

theorem diagonal_born (d : A → ℂ) (a : A) :
    (Q a * Matrix.diagonal d).trace = (1/2:ℂ) * (Matrix.diagonal d).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases a <;> simp [Q] <;> ring

theorem gibbs_readout {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω β t : ℝ) (a : A) :
    ((Q a * (U ω ℏ t * FiniteGibbsClock.gibbs (H ω ℏ) β * (U ω ℏ t)ᴴ)).trace).re = 1/2 := by
  rw [gibbs_stationary hℏ]
  have h := FiniteGibbsClock.gibbs_density (H_hermitian ω ℏ) β
  conv_lhs => rw [gibbs_diagonal ω ℏ β]
  rw [diagonal_born, ← gibbs_diagonal ω ℏ β, h.2]
  norm_num

theorem p_quarter {ω : ℝ} (hω : ω ≠ 0) : p ω (Real.pi/(2*ω)) = 1/2 := by
  have he : ω*(Real.pi/(2*ω)) = Real.pi/2 := by field_simp <;> ring
  rw [p, he, Real.cos_pi_div_two]; norm_num

def persistentTable (ω ℏ t : ℝ) (a b : A) : ℝ :=
  ((Q b * (Q a * rho ω ℏ t * Q a) * Q b).trace).re

def replacedTable (ω ℏ t : ℝ) (a b : A) : ℝ :=
  (∑ r : A, g ω ℏ 0 b r * (Q a * rho ω ℏ t * Q a) * (g ω ℏ 0 b r)ᴴ).trace.re

theorem persistent_quarter {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (a b : A) :
    persistentTable ω ℏ (Real.pi/(2*ω)) a b = if a=b then 1/2 else 0 := by
  rw [persistentTable, sandwich hℏ]
  fin_cases a <;> fin_cases b <;>
    norm_num [mass, p_quarter hω, Q, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]

theorem replaced_quarter {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (a b : A) :
    replacedTable ω ℏ (Real.pi/(2*ω)) a b = if b=1 then 1/2 else 0 := by
  rw [replacedTable, g_sandwich hℏ, sandwich hℏ]
  fin_cases a <;> fin_cases b <;>
    norm_num [mass, p_quarter hω, p_zero, Matrix.trace_smul, Q_trace]

theorem persistent_replaced_variation {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) :
    (∑ a : A, ∑ b : A, |persistentTable ω ℏ (Real.pi/(2*ω)) a b -
      replacedTable ω ℏ (Real.pi/(2*ω)) a b|)/2 = 1/2 := by
  simp only [persistent_quarter hω hℏ, replaced_quarter hω hℏ, Fin.sum_univ_two]
  norm_num

theorem keep_alias {ω : ℝ} (hω : ω ≠ 0) (k : ℕ) :
    p ω (Real.pi/ω+(k:ℝ)*(2*Real.pi/ω)) = 1 := by
  induction k with
  | zero => simpa using p_keep hω
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, p_periodic hω, ih]

/-- Clipping specifies the extension used for observations outside the calibrated range. -/
def clip (q : ℝ) : ℝ := max (1/4) (min (3/4) q)

theorem clip_mem (q : ℝ) : clip q ∈ Set.Icc (1/4) (3/4) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clip_contract {q r : ℝ} (hr : r ∈ Set.Icc (1/4) (3/4)) : |clip q-r| ≤ |q-r| := by
  unfold clip
  rcases le_total q (1/4) with h | h
  · rw [min_eq_right (by linarith : q ≤ 3/4), max_eq_left h,
      abs_of_nonpos (by linarith [hr.1]), abs_of_nonpos (by linarith [hr.1])]
    linarith
  · rcases le_total q (3/4) with h' | h'
    · rw [min_eq_right h', max_eq_right h]
    · rw [min_eq_left h', max_eq_right (by norm_num),
        abs_of_nonneg (by linarith [hr.2]), abs_of_nonneg (by linarith [hr.2])]
      linarith

theorem clipped_inverse_error {ω t : ℝ} (hω : 0 < ω) (ht : t ∈ interval ω) (q : ℝ) :
    |inverse ω (clip q)-t| ≤ 4*|q-p ω t|/ω := by
  exact (inverse_error hω ht (clip_mem q)).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (clip_contract (calibration_range hω ht)) (by norm_num)) hω.le)

end SKEFTHawking.QuantumNetwork.FiniteClockHandReadout
