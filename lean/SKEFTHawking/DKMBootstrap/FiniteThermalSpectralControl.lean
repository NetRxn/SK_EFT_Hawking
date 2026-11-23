import SKEFTHawking.DKMBootstrap.Predicates
import SKEFTHawking.QuantumNetwork.FiniteGibbsClock
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Legacy global F1/pointwise F2 obstruction and a separate finite thermal control.
The finite model has one particle on two sites, in the energy basis, with hbar = 1.
Its atomic spectral measure supplies no continuum or device matching theorem.
Standalone F3 and the existing predicate API are unchanged.
-/

namespace SKEFTHawking.DKMBootstrap

/-- Explicit diffusion-scale tests exceed every proposed global pointwise bound. -/
theorem dkm_div_frequency_unbounded (p : DKMParameters) (M : ℝ) :
    ∃ ω k : ℝ, 0 < ω ∧ k ≠ 0 ∧ M < dkmImGRetarded p ω k / ω := by
  have hτ := p.τ_pos
  have hχ := p.χ_pos
  let B := max M 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let x := min (1 / (2 * p.τ)) (p.χ / (4 * B))
  have hx : 0 < x := lt_min (by positivity) (by positivity)
  have htx : p.τ * x ≤ 1 / 2 := by
    have h := min_le_left (1 / (2 * p.τ)) (p.χ / (4 * B))
    have := (le_div_iff₀ (by positivity : 0 < 2 * p.τ)).mp h
    nlinarith
  have hBx : 4 * B * x ≤ p.χ := by
    have h := min_le_right (1 / (2 * p.τ)) (p.χ / (4 * B))
    have := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp h
    nlinarith
  let k := Real.sqrt (x / p.D)
  have hk : 0 < k := Real.sqrt_pos.mpr (div_pos hx p.D_pos)
  have hD : p.D * k ^ 2 = x := by
    rw [Real.sq_sqrt (le_of_lt (div_pos hx p.D_pos))]
    field_simp [p.D_pos.ne']
  have hq : dkmImGRetarded p x k / x = p.χ / (x * (1 + (1 - p.τ * x)^2)) := by
    rw [dkmImGRetarded_div_frequency p x k hx.ne']
    have hn : 0 < x * (1 + (1 - p.τ * x)^2) := by positivity
    have hd := dkm_denom_pos p x k (Or.inl hx.ne')
    rw [show p.χ * p.D * k^2 = p.χ * x by rw [mul_assoc, hD]]
    rw [hD]
    field_simp
  have ht0 : 0 ≤ p.τ * x := mul_nonneg p.τ_pos.le hx.le
  have hs : (1 - p.τ * x)^2 ≤ 1 := by nlinarith
  have hden : 0 < x * (1 + (1 - p.τ * x)^2) := by positivity
  have hdenle : x * (1 + (1 - p.τ * x)^2) ≤ 2 * x := by nlinarith
  have hratio : 2 * B ≤ p.χ / (x * (1 + (1 - p.τ * x)^2)) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  refine ⟨x, k, hx, hk.ne', ?_⟩
  rw [hq]
  have hm : M < 2 * B := by
    have := le_max_left M 0
    dsimp [B] at *
    linarith
  exact hm.trans_le hratio

/-- The inclusive singleton window already refutes legacy pointwise F2. -/
theorem dkm_not_hasFSumRule (p : DKMParameters) (M : ℝ) :
    ¬ HasFSumRule (dkmImGRetarded p) M := by
  intro h
  obtain ⟨ω, k, hω, _, hlarge⟩ := dkm_div_frequency_unbounded p M
  exact (not_le_of_gt hlarge) (h ω ω hω le_rfl ω k le_rfl le_rfl hω)

/-- Global modeled F1 cannot coexist with legacy pointwise F2. -/
theorem legacy_F1_F2_false (G : Correlator) (p : DKMParameters) (M : ℝ)
    (h1 : IsDKMTransportCorrelator G p) (h2 : HasFSumRule G M) : False := by
  apply dkm_not_hasFSumRule p M
  simpa only [show G = dkmImGRetarded p from funext fun ω ↦ funext fun k ↦ h1 ω k]
    using h2

/-- This refutation concerns the legacy bundle, independently of standalone F3. -/
theorem legacy_axiomSet_false (G : Correlator) (p : DKMParameters)
    (c : ℕ → ℝ) (n M : ℝ) : ¬ IsDKMAxiomSet G p c n M := by
  intro h
  exact legacy_F1_F2_false G p M h.dkm_form h.f_sum_rule

/-- Legacy real F5 always holds; it encodes no complex analytic assertion. -/
theorem legacy_real_F5_all (G : Correlator) : IsUpperHalfPlaneAnalytic G := by
  intro α _ k
  exact ⟨G α k, rfl⟩

namespace FiniteThermal

open Matrix MeasureTheory
open SKEFTHawking.QuantumNetwork.FiniteGibbsClock

/-- Site-one density in the symmetric/antisymmetric energy basis. -/
noncomputable def density : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 1/2; 1/2, 1/2]

theorem density_hermitian : density.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [density, Matrix.conjTranspose_apply]

theorem density_projection : density * density = density := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [density, Matrix.mul_apply, Fin.sum_univ_two]

theorem density_not_commuting {Δ : ℝ} (hΔ : 0 < Δ) :
    twoLevel Δ * density ≠ density * twoLevel Δ := by
  intro h
  have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ ↦ X 0 1) h
  simp [twoLevel, Matrix.diagonal_mul, Matrix.mul_diagonal, density] at hh
  exact hΔ.ne' hh

/-- The actual normalized matrix Gibbs state for H = diag(0,Delta). -/
noncomputable def state (β Δ : ℝ) := gibbs (twoLevel Δ) β

theorem boltzmann_diagonal (β Δ : ℝ) :
    boltzmann (twoLevel Δ) β =
      Matrix.diagonal ![1, (Real.exp (-β * Δ) : ℂ)] := by
  unfold boltzmann twoLevel
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [← Complex.exp_eq_exp_ℂ, Complex.real_smul]

theorem partition_formula (β Δ : ℝ) :
    partition (twoLevel Δ) β = 1 + Real.exp (-β * Δ) := by
  unfold partition
  rw [boltzmann_diagonal]
  simp only [Matrix.trace_diagonal, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.add_re, Complex.one_re, Complex.ofReal_re]

theorem state_diagonal (β Δ : ℝ) :
    state β Δ = Matrix.diagonal
      ![(((1 + Real.exp (-β * Δ))⁻¹ : ℝ) : ℂ),
        (((1 + Real.exp (-β * Δ))⁻¹ * Real.exp (-β * Δ) : ℝ) : ℂ)] := by
  unfold state gibbs
  rw [partition_formula, boltzmann_diagonal, ← Matrix.diagonal_smul]
  congr 1
  ext i
  fin_cases i <;> simp [Complex.real_smul]

theorem state_density (β Δ : ℝ) :
    SKEFTHawking.QuantumNetwork.IsDensityOperator (state β Δ) :=
  gibbs_density (twoLevel_hermitian Δ) β

/-- Transition weight defined from the actual Gibbs diagonal entries. -/
noncomputable def weight (β Δ : ℝ) : ℝ :=
  ((state β Δ 0 0).re - (state β Δ 1 1).re) / 4

theorem weight_formula (β Δ : ℝ) :
    weight β Δ = (1 - Real.exp (-β * Δ)) / (4 * (1 + Real.exp (-β * Δ))) := by
  simp only [weight, state_diagonal, Matrix.diagonal_apply_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.ofReal_re]
  field_simp

theorem weight_pos {β Δ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ) : 0 < weight β Δ := by
  rw [weight_formula]
  have he : Real.exp (-β * Δ) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hep := Real.exp_pos (-β * Δ)
  positivity

theorem density_second_moment (β Δ : ℝ) :
    (state β Δ * (density * density)).trace = (1/2 : ℂ) := by
  rw [density_projection]
  calc
    (state β Δ * density).trace = (state β Δ).trace / 2 := by
      rw [state_diagonal]
      simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Fin.sum_univ_two, density]
      ring
    _ = 1 / 2 := by rw [state, gibbs_trace_one (twoLevel_hermitian Δ) β]

/-- The matrix commutator is evaluated before taking the actual Gibbs trace. -/
noncomputable def timeCommutator (β Δ t : ℝ) : ℂ :=
  (state β Δ * (heisenberg (twoLevel Δ) 1 t density * density -
    density * heisenberg (twoLevel Δ) 1 t density)).trace

theorem timeCommutator_formula (β Δ t : ℝ) :
    timeCommutator β Δ t = (weight β Δ : ℂ) *
      (Complex.exp (-Complex.I * Δ * t) - Complex.exp (Complex.I * Δ * t)) := by
  have ht (i j : Fin 2) : heisenberg (twoLevel Δ) 1 t density i j =
      Complex.exp (Complex.I * t * ((![0, (Δ : ℂ)] : Fin 2 → ℂ) i -
        (![0, (Δ : ℂ)] : Fin 2 → ℂ) j)) * density i j := by
    simp [heisenberg, twoLevel, diagonal_conjugate_entry]
  simp only [timeCommutator, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.sub_apply, state_diagonal, Matrix.diagonal, ht]
  simp [density]
  rw [weight_formula]
  push_cast
  have hp : Complex.I * (t : ℂ) * Δ = Complex.I * Δ * t := by ring
  simp only [hp]
  field_simp
  ring

/-- The same positive transition atom is used in both the window and dispersion integrals. -/
noncomputable def spectralMeasure (β Δ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (weight β Δ) • Measure.dirac Δ

instance (β Δ : ℝ) : IsFiniteMeasure (spectralMeasure β Δ) := by
  constructor
  simp [spectralMeasure]

theorem band_mass {β Δ ω Λ : ℝ} (hωΔ : ω ≤ Δ) (hΔΛ : Δ ≤ Λ) :
    spectralMeasure β Δ (Set.Icc ω Λ) = ENNReal.ofReal (weight β Δ) := by
  simp [spectralMeasure,
    Measure.dirac_apply_of_mem (show Δ ∈ Set.Icc ω Λ from ⟨hωΔ, hΔΛ⟩)]

theorem band_mass_pos {β Δ ω Λ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ)
    (hωΔ : ω ≤ Δ) (hΔΛ : Δ ≤ Λ) : 0 < spectralMeasure β Δ (Set.Icc ω Λ) := by
  rw [band_mass hωΔ hΔΛ]
  exact ENNReal.ofReal_pos.mpr (weight_pos hβ hΔ)

theorem band_weighted_integral {β Δ ω Λ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ)
    (hωΔ : ω ≤ Δ) (hΔΛ : Δ ≤ Λ) :
    (∫⁻ Ω in Set.Icc ω Λ, ENNReal.ofReal (1 / Ω) ∂spectralMeasure β Δ) =
      ENNReal.ofReal (weight β Δ / Δ) := by
  simp only [spectralMeasure, Measure.restrict_smul, restrict_dirac,
    if_pos (show Δ ∈ Set.Icc ω Λ from ⟨hωΔ, hΔΛ⟩), lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (weight_pos hβ hΔ).le]
  congr 1
  ring

theorem thermalFactor_integral {x : ℝ} (hx : 0 < x) (β : ℝ) :
    (1 - Real.exp (-β * x)) / x = ∫ s in (0 : ℝ)..β, Real.exp (-s * x) := by
  have hf : (fun s : ℝ ↦ Real.exp (-s * x)) =
      (fun s : ℝ ↦ Real.exp ((-x) * s)) := by
    funext s
    congr 1
    ring
  rw [hf, intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hx.ne'),
    integral_exp]
  simp
  field_simp
  ring

theorem thermalFactor_antitone {β x y : ℝ} (hβ : 0 ≤ β) (hx : 0 < x) (hxy : x ≤ y) :
    (1 - Real.exp (-β * y)) / y ≤ (1 - Real.exp (-β * x)) / x := by
  rw [thermalFactor_integral (hx.trans_le hxy), thermalFactor_integral hx]
  apply intervalIntegral.integral_mono_on hβ
    ((by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-s * y))).intervalIntegrable 0 β)
    ((by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-s * x))).intervalIntegrable 0 β)
  intro s hs
  apply Real.exp_monotone
  nlinarith [hs.1]

/-- Inclusive weighted thermal bound for the actual Gibbs atom, with cutoff below the gap. -/
theorem band_thermal_bound {β Δ ω Λ : ℝ} (hβ : 0 < β) (hω : 0 < ω)
    (hωΔ : ω ≤ Δ) (hΔΛ : Δ ≤ Λ) :
    (∫⁻ Ω in Set.Icc ω Λ, ENNReal.ofReal (1 / Ω) ∂spectralMeasure β Δ) ≤
      ENNReal.ofReal ((1/2) * (1 - Real.exp (-β * ω)) / ω) := by
  have hΔ := hω.trans_le hωΔ
  rw [band_weighted_integral hβ hΔ hωΔ hΔΛ]
  apply ENNReal.ofReal_le_ofReal
  have hf := thermalFactor_antitone hβ.le hω hωΔ
  have he := Real.exp_pos (-β * Δ)
  have hn : 0 ≤ 1 - Real.exp (-β * Δ) := by
    have := Real.exp_lt_one_iff.mpr (by nlinarith : -β * Δ < 0)
    linarith
  have hw : weight β Δ / Δ ≤ (1/2) * ((1 - Real.exp (-β * Δ)) / Δ) := by
    rw [weight_formula]
    apply (div_le_iff₀ hΔ).mpr
    rw [mul_assoc, div_mul_cancel₀ _ hΔ.ne']
    apply (div_le_iff₀ (by positivity : 0 < 4 * (1 + Real.exp (-β * Δ)))).mpr
    nlinarith
  calc
    weight β Δ / Δ ≤ (1/2) * ((1 - Real.exp (-β * Δ)) / Δ) := hw
    _ ≤ (1/2) * ((1 - Real.exp (-β * ω)) / ω) := mul_le_mul_of_nonneg_left hf (by norm_num)
    _ = (1/2) * (1 - Real.exp (-β * ω)) / ω := by ring

theorem band_weighted_integral_pos_finite {β Δ ω Λ : ℝ}
    (hβ : 0 < β) (hΔ : 0 < Δ) (hωΔ : ω ≤ Δ) (hΔΛ : Δ ≤ Λ) :
    0 < (∫⁻ Ω in Set.Icc ω Λ, ENNReal.ofReal (1 / Ω) ∂spectralMeasure β Δ) ∧
    (∫⁻ Ω in Set.Icc ω Λ, ENNReal.ofReal (1 / Ω) ∂spectralMeasure β Δ) < ⊤ := by
  rw [band_weighted_integral hβ hΔ hωΔ hΔΛ]
  exact ⟨ENNReal.ofReal_pos.mpr (div_pos (weight_pos hβ hΔ) hΔ), ENNReal.ofReal_lt_top⟩

theorem band_weighted_integrable (β Δ ω Λ : ℝ) :
    IntegrableOn (fun Ω : ℝ ↦ 1 / Ω) (Set.Icc ω Λ) (spectralMeasure β Δ) := by
  exact ((integrable_dirac (by exact enorm_lt_top)).smul_measure
    ENNReal.ofReal_ne_top).restrict

/-- Actual Bochner dispersion integral against the same Gibbs transition measure. -/
noncomputable def dispersion (β Δ : ℝ) (z : ℂ) : ℂ :=
  ∫ Ω : ℝ, ((Ω : ℂ) - z)⁻¹ + ((Ω : ℂ) + z)⁻¹ ∂spectralMeasure β Δ

theorem dispersion_integrable (β Δ : ℝ) (z : ℂ) :
    Integrable (fun Ω : ℝ ↦ ((Ω : ℂ) - z)⁻¹ + ((Ω : ℂ) + z)⁻¹)
      (spectralMeasure β Δ) :=
  (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-- Evaluation is stated only in the open upper half-plane, away from both atomic poles. -/
theorem dispersion_formula {β Δ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ)
    {z : ℂ} (_hz : 0 < z.im) :
    dispersion β Δ z =
      (weight β Δ : ℂ) * (((Δ : ℂ) - z)⁻¹ + ((Δ : ℂ) + z)⁻¹) := by
  simp only [dispersion, spectralMeasure, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (weight_pos hβ hΔ).le, Complex.real_smul]

theorem dispersion_denominators {Δ : ℝ} {z : ℂ} (hz : 0 < z.im) :
    (Δ : ℂ) - z ≠ 0 ∧ (Δ : ℂ) + z ≠ 0 := by
  constructor <;> intro h <;> have hi := congrArg Complex.im h <;> simp at hi <;> linarith

theorem dispersion_differentiableAt {β Δ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ)
    {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ (dispersion β Δ) z := by
  have he : dispersion β Δ =ᶠ[nhds z] fun w ↦
      (weight β Δ : ℂ) * (((Δ : ℂ) - w)⁻¹ + ((Δ : ℂ) + w)⁻¹) := by
    have ho : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [ho.mem_nhds hz] with w hw
    exact dispersion_formula hβ hΔ hw
  apply DifferentiableAt.congr_of_eventuallyEq _ he
  exact differentiableAt_const _ |>.mul
    (((differentiableAt_const _).sub differentiableAt_id).inv
      (dispersion_denominators hz).1 |>.add
      (((differentiableAt_const _).add differentiableAt_id).inv
        (dispersion_denominators hz).2))

theorem dispersion_differentiableOn {β Δ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ) :
    DifferentiableOn ℂ (dispersion β Δ) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (dispersion_differentiableAt hβ hΔ hz).differentiableWithinAt

/-- Imaginary-frequency dispersion identity for this finite atom, in its fixed normalization. -/
theorem dispersion_imaginary_frequency {β Δ α : ℝ}
    (hβ : 0 < β) (hΔ : 0 < Δ) (hα : 0 < α) :
    dispersion β Δ (Complex.I * α) = ((2 * weight β Δ * Δ / (Δ^2 + α^2) : ℝ) : ℂ) := by
  have hz : 0 < (Complex.I * (α : ℂ)).im := by simpa using hα
  rw [dispersion_formula hβ hΔ hz]
  have hd : (Δ : ℂ)^2 + (α : ℂ)^2 ≠ 0 := by
    have hr : Δ^2 + α^2 ≠ 0 := ne_of_gt (by positivity)
    exact_mod_cast hr
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_add, Complex.ofReal_pow]
  field_simp [hd, (dispersion_denominators (Δ := Δ) hz).1,
    (dispersion_denominators (Δ := Δ) hz).2]
  ring_nf
  simp [Complex.I_sq]

/-- The actual Gibbs commutator with its retarded Fourier-Laplace factor. -/
noncomputable def timeIntegrand (β Δ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * z * t) * timeCommutator β Δ t

theorem timeIntegrand_formula (β Δ : ℝ) (z : ℂ) (t : ℝ) :
    timeIntegrand β Δ z t = (weight β Δ : ℂ) *
      (Complex.exp ((Complex.I * (z - Δ)) * t) -
        Complex.exp ((Complex.I * (z + Δ)) * t)) := by
  unfold timeIntegrand
  rw [timeCommutator_formula]
  calc
    _ = (weight β Δ : ℂ) *
        (Complex.exp (Complex.I * z * t) * Complex.exp (-Complex.I * Δ * t) -
          Complex.exp (Complex.I * z * t) * Complex.exp (Complex.I * Δ * t)) := by ring
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 2 <;> congr 1 <;> ring

theorem phase_decay {z : ℂ} (hz : 0 < z.im) (Δ : ℝ) :
    (Complex.I * (z - Δ)).re < 0 ∧ (Complex.I * (z + Δ)).re < 0 := by
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_im,
    Complex.add_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero, zero_sub]
  exact ⟨neg_neg_of_pos hz, neg_neg_of_pos hz⟩

theorem timeIntegrand_integrable (β Δ : ℝ) {z : ℂ} (hz : 0 < z.im) :
    IntegrableOn (timeIntegrand β Δ z) (Set.Ioi 0) := by
  have hm := integrableOn_exp_mul_complex_Ioi (phase_decay hz Δ).1 0
  have hp := integrableOn_exp_mul_complex_Ioi (phase_decay hz Δ).2 0
  have he : timeIntegrand β Δ z = fun t : ℝ ↦ (weight β Δ : ℂ) *
      (Complex.exp ((Complex.I * (z - Δ)) * t) -
        Complex.exp ((Complex.I * (z + Δ)) * t)) := funext (timeIntegrand_formula β Δ z)
  rw [he]
  exact (hm.sub hp).const_mul (weight β Δ : ℂ)

/-- Retarded convention i times the integral over positive physical time. -/
noncomputable def timeResponse (β Δ : ℝ) (z : ℂ) : ℂ :=
  Complex.I * ∫ t in Set.Ioi (0 : ℝ), timeIntegrand β Δ z t

theorem timeResponse_eq_dispersion {β Δ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ)
    {z : ℂ} (hz : 0 < z.im) : timeResponse β Δ z = dispersion β Δ z := by
  have hm := integrableOn_exp_mul_complex_Ioi (phase_decay hz Δ).1 0
  have hp := integrableOn_exp_mul_complex_Ioi (phase_decay hz Δ).2 0
  unfold timeResponse
  simp_rw [timeIntegrand_formula]
  rw [integral_const_mul, integral_sub hm hp,
    integral_exp_mul_complex_Ioi (phase_decay hz Δ).1 0,
    integral_exp_mul_complex_Ioi (phase_decay hz Δ).2 0,
    dispersion_formula hβ hΔ hz]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hminus : z - (Δ : ℂ) ≠ 0 := by
    intro h
    exact (dispersion_denominators hz).1 (by linear_combination -h)
  have hplus := (dispersion_denominators (Δ := Δ) hz).2
  have hplus' : z + (Δ : ℂ) ≠ 0 := by simpa only [add_comm] using hplus
  field_simp [hminus, hplus, hplus', (dispersion_denominators (Δ := Δ) hz).1]
  ring

end FiniteThermal

end SKEFTHawking.DKMBootstrap
