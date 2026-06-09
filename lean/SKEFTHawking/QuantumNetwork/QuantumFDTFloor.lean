import SKEFTHawking.QuantumNetwork.FDTNoiseFloor
import Physlib.StatisticalMechanics.CanonicalEnsemble.Basic
import Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas

/-!
# Phase 6AM Wave 4 — quantum (Callen–Welton) fluctuation-dissipation noise floor

Replaces the *classical* Johnson–Nyquist floor `S_JN = 4 kB_T σ_Q` used by Phase 6AN
(`FDTNoiseFloor.lean`) with the **exact quantum (Callen–Welton) zero-point-corrected floor**
`(ℏω/2)·coth(βℏω/2)`, **derived** by instantiating a PhysLib `CanonicalEnsemble` over the
quantum-harmonic-oscillator level spectrum `Eₙ = ℏω(n + ½)` and computing its `meanEnergy`.

The quantum floor is the physically correct certificate floor in the cryogenic-mK / GHz regime
`ℏω ≳ kB_T`, where the classical `4kB_Tσ` floor → 0 and misses the dominant zero-point `ℏω/2`.

The **Caves** phase-insensitive-amplifier added-noise inequality `A ≥ ℏω/2` STAYS a cited
hypothesis (`fdt_noise_floor_amplifier`, 6AN): it needs the bosonic CCR ladder algebra `[a,a†]=1`,
which PhysLib does not provide — a genuine wall, documented as such, not an effort deferral.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open MeasureTheory Real Temperature CanonicalEnsemble SKEFTHawking.GrapheneNoiseFormula

/-- The quantum-harmonic-oscillator **canonical ensemble**: microstates `n : ℕ` with energy
`Eₙ = ℏω(n + ½)`, on the counting measure (discrete spectrum), zero degrees of freedom. -/
noncomputable def qhoEnsemble (hbarOmega : ℝ) : CanonicalEnsemble ℕ where
  energy n := hbarOmega * (n + 1 / 2)
  dof := 0
  μ := Measure.count
  energy_measurable := by fun_prop

open scoped BigOperators

/-- Boltzmann weight factorization: `exp(−β·E₀(n+½)) = exp(−βE₀/2)·(exp(−βE₀))ⁿ`. -/
private theorem qho_weight (E0 β : ℝ) (n : ℕ) :
    Real.exp (-β * (E0 * (↑n + 1 / 2)))
      = Real.exp (-(β * E0) / 2) * Real.exp (-(β * E0)) ^ n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- For `0 < β·E₀` the geometric ratio `exp(−βE₀) < 1`. -/
private theorem qho_ratio_lt_one {E0 β : ℝ} (h : 0 < β * E0) :
    Real.exp (-(β * E0)) < 1 := by
  rw [Real.exp_lt_one_iff]; linarith

/-- The QHO Boltzmann weights are `count`-integrable (geometric summability). -/
private theorem qho_integrable {E0 β : ℝ} (hβE : 0 < β * E0) :
    Integrable (fun n : ℕ => Real.exp (-β * (E0 * (↑n + 1 / 2)))) Measure.count := by
  rw [integrable_count_iff]
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), qho_weight]
  exact (summable_geometric_of_lt_one (Real.exp_nonneg _) (qho_ratio_lt_one hβE)).mul_left _

/-- **QHO partition function** (closed form): `Z = exp(−βℏω/2) / (1 − exp(−βℏω))`. -/
theorem qho_mathematicalPartitionFunction {E0 : ℝ} {T : Temperature}
    (hE0 : 0 < E0) (hT : 0 < T.val) :
    (qhoEnsemble E0).mathematicalPartitionFunction T
      = Real.exp (-((T.β : ℝ) * E0) / 2) / (1 - Real.exp (-((T.β : ℝ) * E0))) := by
  have hβE : 0 < (T.β : ℝ) * E0 := mul_pos (Temperature.beta_pos T hT) hE0
  rw [mathematicalPartitionFunction_eq_integral]
  show ∫ n : ℕ, Real.exp (-(T.β : ℝ) * (E0 * (↑n + 1 / 2))) ∂Measure.count = _
  rw [integral_countable (qho_integrable hβE)]
  have hcount : ∀ x : ℕ, Measure.count.real {x} = 1 :=
    fun x => MeasureTheory.count_real_singleton' (measurableSet_singleton x)
  simp_rw [hcount, one_smul, qho_weight]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_nonneg _) (qho_ratio_lt_one hβE)]
  ring

/-- The energy-weighted Boltzmann sum `n ↦ E₀(n+½)·exp(−βE₀(n+½))` is `count`-integrable
(`(n+½)·rⁿ` summability, `r = exp(−βE₀) < 1`). -/
private theorem qho_energy_integrable {E0 β : ℝ} (hE0 : 0 < E0) (hβE : 0 < β * E0) :
    Integrable
      (fun n : ℕ => E0 * (↑n + 1 / 2) * Real.exp (-β * (E0 * (↑n + 1 / 2)))) Measure.count := by
  have hr : ‖Real.exp (-(β * E0))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]; exact qho_ratio_lt_one hβE
  rw [integrable_count_iff]
  have hnn : ∀ n : ℕ, 0 ≤ E0 * (↑n + 1 / 2) * Real.exp (-β * (E0 * (↑n + 1 / 2))) := by
    intro n; positivity
  simp_rw [Real.norm_eq_abs, fun n => abs_of_nonneg (hnn n), qho_weight]
  have h1 : Summable (fun n : ℕ => (↑n : ℝ) * Real.exp (-(β * E0)) ^ n) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h2 : Summable (fun n : ℕ => Real.exp (-(β * E0)) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_nonneg _) (qho_ratio_lt_one hβE)
  refine ((h1.add (h2.mul_left (1 / 2))).mul_left (E0 * Real.exp (-(β * E0) / 2))).congr
    (fun n => ?_)
  ring

/-- The Bose–Einstein + zero-point combination equals `½ coth(y/2)` (`coth = cosh/sinh`). -/
private theorem qho_coth_identity {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) / (1 - Real.exp (-y)) + 1 / 2
      = Real.cosh (y / 2) / (2 * Real.sinh (y / 2)) := by
  rw [Real.cosh_eq, Real.sinh_eq, show -y = -(y / 2) + -(y / 2) by ring, Real.exp_add]
  set a := Real.exp (y / 2) with ha
  set b := Real.exp (-(y / 2)) with hb
  have hab : a * b = 1 := by rw [ha, hb, ← Real.exp_add]; simp
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := Real.exp_pos _
  have hba : b < a := by rw [ha, hb]; exact Real.exp_lt_exp.mpr (by linarith)
  have hbb : b ^ 2 < 1 := by nlinarith
  have hd1 : 1 - b ^ 2 ≠ 0 := by nlinarith
  have hd2 : a - b ≠ 0 := by linarith
  field_simp
  linear_combination (2 * b) * hab

/-- **QHO mean energy = the Callen–Welton zero-point-corrected floor**
`⟨E⟩ = (ℏω/2)·coth(βℏω/2) = (ℏω/2)·cosh(βℏω/2)/sinh(βℏω/2)`, derived from the PhysLib
`CanonicalEnsemble.meanEnergy` of the QHO ensemble (`meanEnergy_eq_ratio_of_integrals` invoked). -/
theorem qho_meanEnergy {E0 : ℝ} {T : Temperature} (hE0 : 0 < E0) (hT : 0 < T.val) :
    (qhoEnsemble E0).meanEnergy T
      = E0 / 2 * (Real.cosh ((T.β : ℝ) * E0 / 2) / Real.sinh ((T.β : ℝ) * E0 / 2)) := by
  have hβE : 0 < (T.β : ℝ) * E0 := mul_pos (Temperature.beta_pos T hT) hE0
  set β : ℝ := (T.β : ℝ) with hβ
  set r : ℝ := Real.exp (-(β * E0)) with hr_def
  have hr1 : r < 1 := qho_ratio_lt_one hβE
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hcount : ∀ x : ℕ, Measure.count.real {x} = 1 :=
    fun x => MeasureTheory.count_real_singleton' (measurableSet_singleton x)
  have hc0 : Real.exp (-(β * E0) / 2) ≠ 0 := (Real.exp_pos _).ne'
  -- the energy-weighted Boltzmann series `∑' (n+½) rⁿ`
  have hsum_nr : ∑' n : ℕ, ((↑n : ℝ) + 1 / 2) * r ^ n = r / (1 - r) ^ 2 + 1 / 2 * (1 - r)⁻¹ := by
    have e1 : ∀ n : ℕ, ((↑n : ℝ) + 1 / 2) * r ^ n = (↑n : ℝ) * r ^ n + 1 / 2 * r ^ n :=
      fun n => by ring
    have hsf : Summable (fun n : ℕ => (↑n : ℝ) * r ^ n) :=
      (summable_pow_mul_geometric_of_norm_lt_one 1 hrnorm).congr (fun n => by simp [pow_one])
    have hsg : Summable (fun n : ℕ => 1 / 2 * r ^ n) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    rw [tsum_congr e1, hsf.tsum_add hsg,
      tsum_coe_mul_geometric_of_norm_lt_one hrnorm, tsum_mul_left,
      tsum_geometric_of_lt_one hr0 hr1]
  rw [meanEnergy_eq_ratio_of_integrals]
  have hden : (∫ n : ℕ, Real.exp (-β * (qhoEnsemble E0).energy n) ∂(qhoEnsemble E0).μ)
      = Real.exp (-(β * E0) / 2) * (1 - r)⁻¹ := by
    show ∫ n : ℕ, Real.exp (-β * (E0 * (↑n + 1 / 2))) ∂Measure.count = _
    rw [integral_countable (qho_integrable hβE)]
    simp_rw [hcount, one_smul, qho_weight]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hnum : (∫ n : ℕ, (qhoEnsemble E0).energy n
        * Real.exp (-β * (qhoEnsemble E0).energy n) ∂(qhoEnsemble E0).μ)
      = E0 * Real.exp (-(β * E0) / 2) * (r / (1 - r) ^ 2 + 1 / 2 * (1 - r)⁻¹) := by
    show ∫ n : ℕ, E0 * (↑n + 1 / 2) * Real.exp (-β * (E0 * (↑n + 1 / 2))) ∂Measure.count = _
    rw [integral_countable (qho_energy_integrable hE0 hβE)]
    simp_rw [hcount, one_smul, qho_weight]
    rw [show (fun n : ℕ => E0 * (↑n + 1 / 2) * (Real.exp (-(β * E0) / 2) * r ^ n))
          = (fun n : ℕ => E0 * Real.exp (-(β * E0) / 2) * (((↑n : ℝ) + 1 / 2) * r ^ n)) from by
        funext n; ring, tsum_mul_left, hsum_nr]
  rw [hnum, hden,
    show E0 / 2 * (Real.cosh (β * E0 / 2) / Real.sinh (β * E0 / 2))
        = E0 * (Real.cosh (β * E0 / 2) / (2 * Real.sinh (β * E0 / 2))) from by ring,
    ← qho_coth_identity hβE, ← hr_def]
  field_simp

/-- The quantum floor is bounded below by the **zero-point energy** `ℏω/2` (`coth ≥ 1`). This is the
term the classical Johnson–Nyquist floor `4kB_Tσ` misses: it `→ 0` as `T → 0`, this one cannot. -/
theorem qho_meanEnergy_ge_zeroPoint {E0 : ℝ} {T : Temperature} (hE0 : 0 < E0) (hT : 0 < T.val) :
    E0 / 2 ≤ (qhoEnsemble E0).meanEnergy T := by
  rw [qho_meanEnergy hE0 hT]
  have hx : 0 < (T.β : ℝ) * E0 / 2 := by
    have := mul_pos (Temperature.beta_pos T hT) hE0; linarith
  have hsinh : 0 < Real.sinh ((T.β : ℝ) * E0 / 2) := by
    rw [Real.sinh_eq]
    have : Real.exp (-((T.β : ℝ) * E0 / 2)) < Real.exp ((T.β : ℝ) * E0 / 2) :=
      Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hcoth : 1 ≤ Real.cosh ((T.β : ℝ) * E0 / 2) / Real.sinh ((T.β : ℝ) * E0 / 2) := by
    rw [le_div_iff₀ hsinh, one_mul]
    nlinarith [Real.cosh_sub_sinh ((T.β : ℝ) * E0 / 2), Real.exp_pos (-((T.β : ℝ) * E0 / 2))]
  nlinarith [hcoth, hE0]

/-- The derived quantum floor is **strictly positive** for every `ℏω > 0`, `T > 0`. -/
theorem qho_meanEnergy_pos {E0 : ℝ} {T : Temperature} (hE0 : 0 < E0) (hT : 0 < T.val) :
    0 < (qhoEnsemble E0).meanEnergy T :=
  lt_of_lt_of_le (by linarith : (0 : ℝ) < E0 / 2) (qho_meanEnergy_ge_zeroPoint hE0 hT)

/-- **Re-anchored detector/amplifier floor.** A linear device whose noise budget carries the
*derived* Callen–Welton quantum energy scale `(ℏω/2)coth(βℏω/2)` sits strictly above the classical
Johnson–Nyquist thermal floor `4kB_Tσ` (`GrapheneNoiseFormula.johnsonNyquistPSD`) — by at least the
zero-point `ℏω/2`. Unlike the classical floor, this excess persists as `T → 0`. Companion to the
6AN `fdt_noise_floor_amplifier`, but with the `ℏω/2` floor now **derived** from the QHO ensemble
rather than taken as the Caves hypothesis. -/
theorem fdt_quantum_noise_floor {kB_T sigma_Q E0 : ℝ} {T : Temperature}
    (hE0 : 0 < E0) (hT : 0 < T.val) :
    johnsonNyquistPSD kB_T sigma_Q < johnsonNyquistPSD kB_T sigma_Q + E0 / 2
      ∧ johnsonNyquistPSD kB_T sigma_Q + E0 / 2
          ≤ johnsonNyquistPSD kB_T sigma_Q + (qhoEnsemble E0).meanEnergy T :=
  ⟨by linarith, by linarith [qho_meanEnergy_ge_zeroPoint hE0 hT]⟩

end SKEFTHawking.QuantumNetwork
