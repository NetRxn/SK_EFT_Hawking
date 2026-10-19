import SKEFTHawking.Basic
import SKEFTHawking.WKBAnalysis
import SKEFTHawking.WKBConnection
import SKEFTHawking.DiracFluidMetric
import SKEFTHawking.QuasiOneDReduction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Dirac Fluid WKB Connection Formula (Phase 5w Wave 4)

## Overview

Capstone integration module for the Wave-4 graphene Dirac-fluid analog
Hawking pipeline. Binds:

* `DiracFluidMetric.lean` — 2+1D acoustic metric with quasi-1D block-diagonal
  structure (the (t,x) block reproduces the BEC 1+1D metric with `c_s = v_F/√2`)
* `WKBConnection.lean` — defined scalar Bogoliubov/noise/turning-point
  carriers and consequences conditional on their supplied fields
* `QuasiOneDReduction.lean` — adopted BEC infrared scalar and conditional
  supplied transverse-error envelopes, not physical bilayer derivations

## Headline content (substantive theorems)

1. **Sound-speed binding** `c_s=v_F/sqrt(2)` in the stated conformal
   record, and scalar inequality `c_s<v_F`. This does not derive high-k
   collective dispersion, prohibit escape or prove stronger physical
   Hawking robustness. Actual bilayer mode matching remains BUILD.

2. **Parameter binding** into `ExactWKBParams`, permitting generic scalar
   statements such as `decoherence_double_delta_diss` to be instantiated.
   Any Bogoliubov carrier, rate bound or physical channel identification
   remains an additional hypothesis, not a field supplied by this map.

3. **Transverse-mode quantization** in a confined channel of width `W`:
   `k_n = (n+1)π / W` (Dirichlet boundaries) with strict-monotone increasing
   per-channel cutoff energy `ω_⊥(n) = c_s · k_n`.

4. **Supplied Dean-geometry comparison**: at W=1um, c_s=4.4e5m/s
   and literal omega_H=3.14e11s^-1, c_s*pi/W>4*omega_H. This is an
   exact inequality on supplied values, not a physical finite-width,
   evanescent-error, detector-band or transmission certificate.
   Actual PDE/boundary/state/current and error matching remains BUILD.

5. **Finite channel sum**: a supplied finite sum of beta_n*Gamma_n,
   with conditional nonnegativity and uniform-factor bounds. Neither
   physical channel selection nor the Python PSD follows from that algebra.

## Reuse

`toExactWKB` binds positive supplied speed/kappa and nonnegative damping
into a parameter record. Generic statements can be instantiated when ALL
of their actual hypotheses and carrier fields are supplied; this does not
transfer all physical WKBAnalysis or WKBConnection conclusions to a bilayer.
The QuasiOneDReduction envelopes retain their physical-bound hypotheses.

## References

- Bilić, CQG 16, 3953 (1999) — relativistic acoustic metric
- Lucas & Fong, JPCM 30, 053001 (2018) — Dirac fluid review
- Geurs et al., arXiv:2509.16321 (2025) — first electronic sonic horizon
- Anderson, Balbinot, Fabbri, Parentani, PRD90,104044 (2014),
  arXiv:1404.3224 — BEC infrared transmission scalar; no bilayer
  electrical transfer, finite-band quadratic roll-off or calibrated band
- Macher & Parentani, PRD 80, 043601 (2009) — quartic dispersion BdG
- Phase 5w deep research §2 (analog metric), §4 (transverse modes)
-/

namespace SKEFTHawking.DiracFluidWKB

open SKEFTHawking.WKBConnection
open SKEFTHawking.DiracFluidMetric

/-!
## Section 1 — Graphene WKB Parameters and Sound-Speed Binding
-/

/-- Phase 5w graphene Dirac-fluid WKB parameters. Bundles the Fermi velocity
    `vF`, the horizon damping rate `Γ_H`, surface gravity `κ`, and the
    transverse channel width `W`. The acoustic sound speed is recovered as
    `c_s = vF / √2` (conformal-Dirac equation of state ε = 2p). -/
structure GrapheneWKBParams where
  /-- Fermi velocity v_F (graphene: ≈ 10⁶ m/s monolayer, ~6×10⁵ bilayer). -/
  vF : ℝ
  vF_pos : 0 < vF
  /-- Horizon damping rate Γ_H. -/
  GammaH : ℝ
  GammaH_nonneg : 0 ≤ GammaH
  /-- Surface gravity κ. -/
  kappa : ℝ
  kappa_pos : 0 < kappa
  /-- Transverse channel width W (Dean device: ~1 μm). -/
  W : ℝ
  W_pos : 0 < W

/-- The conformal sound speed of the 2+1D Dirac fluid: `c_s = v_F / √2`. -/
noncomputable def soundSpeed (g : GrapheneWKBParams) : ℝ :=
  g.vF / Real.sqrt 2

/-- The conformal sound speed is positive when `v_F > 0`. -/
theorem soundSpeed_pos (g : GrapheneWKBParams) : 0 < soundSpeed g := by
  unfold soundSpeed
  exact div_pos g.vF_pos (Real.sqrt_pos.mpr (by norm_num))

/-- The squared sound speed equals `v_F²/2`. This connects the binding
    `c_s = v_F/√2` to `DiracFluidMetric.diracFluidSoundSpeedSq` which
    asserts `c_s² = v_F²/2` directly. -/
theorem soundSpeed_sq (g : GrapheneWKBParams) :
    soundSpeed g ^ 2 = g.vF ^ 2 / 2 := by
  unfold soundSpeed
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [div_pow, h2]

/-- The squared sound speed equals `DiracFluidMetric.diracFluidSoundSpeedSq`
    of the Fermi velocity. **Substantive cross-bridge** to
    `DiracFluidMetric.lean`: the conformal-Dirac sound-speed binding here
    matches the one used in the 3×3 acoustic metric definition. -/
theorem soundSpeed_sq_eq_diracFluidSoundSpeedSq (g : GrapheneWKBParams) :
    soundSpeed g ^ 2 = SKEFTHawking.DiracFluidMetric.diracFluidSoundSpeedSq g.vF := by
  rw [soundSpeed_sq]
  rfl

/-- Constant sound-speed comparison in the defined conformal record:
    c_s=v_F/sqrt(2)<v_F. It derives no sign of high-momentum collective
    dispersion, no escape prohibition and no physical robustness or
    bilayer hydrodynamic-to-quantum matching. -/
theorem soundSpeed_lt_vF (g : GrapheneWKBParams) :
    soundSpeed g < g.vF := by
  unfold soundSpeed
  have hsqrt : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  exact div_lt_self g.vF_pos hsqrt

/-!
## Section 2 — Binding to the Dimension-Independent ExactWKBParams

The map below supplies the positive speed/kappa and nonnegative rate
fields of ExactWKBParams. Other theorem hypotheses and physical carrier
identifications remain separate; the map alone does not discharge them.
-/

/-- Bind graphene parameters to the dimension-independent
    `WKBConnection.ExactWKBParams`. The conformal sound speed is `vF/√2`. -/
noncomputable def toExactWKB (g : GrapheneWKBParams) : ExactWKBParams where
  Gamma_H := g.GammaH
  Gamma_H_nonneg := g.GammaH_nonneg
  kappa := g.kappa
  kappa_pos := g.kappa_pos
  cs := soundSpeed g
  cs_pos := soundSpeed_pos g

/-- The defined noiseFloor is <=1 when supplied Gamma_H<=kappa.
    This transports a scalar model hypothesis through toExactWKB; it
    derives no physical graphene noise covariance or relative excess
    above a Planck spectrum. Actual damping, state/current/contact and
    receiver normalization remain BUILD. -/
theorem noiseFloor_bounded_perturbative
    (g : GrapheneWKBParams) (h : g.GammaH ≤ g.kappa) :
    noiseFloor (toExactWKB g) ≤ 1 :=
  noise_floor_bounded (toExactWKB g) h

/-!
## Section 3 — Transverse-Mode Quantization

For a confined channel of width `W` with Dirichlet boundary conditions,
the transverse momenta are `k_n = (n+1)π/W` for n = 0, 1, 2, ...
The associated channel-cutoff energy is `ω_⊥(n) = c_s · k_n`.
-/

/-- Transverse momentum of the n-th channel (Dirichlet boundaries):
    `k_n = (n+1)π / W`. -/
noncomputable def transverseMomentum (n : ℕ) (W : ℝ) : ℝ :=
  ((n : ℝ) + 1) * Real.pi / W

/-- The transverse momentum is positive for any `n` when `W > 0`. -/
theorem transverseMomentum_pos (n : ℕ) (W : ℝ) (hW : 0 < W) :
    0 < transverseMomentum n W := by
  unfold transverseMomentum
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  exact div_pos (mul_pos h1 Real.pi_pos) hW

/-- The transverse momentum is strictly increasing in the channel index `n`. -/
theorem transverseMomentum_strictMono (W : ℝ) (hW : 0 < W) :
    StrictMono (fun n : ℕ => transverseMomentum n W) := by
  intro n m hnm
  unfold transverseMomentum
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  rw [div_lt_div_iff_of_pos_right hW]
  nlinarith

/-- The lowest transverse channel has momentum `π/W`. -/
theorem transverseMomentum_zero (W : ℝ) :
    transverseMomentum 0 W = Real.pi / W := by
  unfold transverseMomentum
  simp

/-- The transverse channel-cutoff energy: `ω_⊥(n) = c_s · k_n`.
    Below this frequency, the n-th channel is closed (evanescent). -/
noncomputable def channelCutoffEnergy (g : GrapheneWKBParams) (n : ℕ) : ℝ :=
  soundSpeed g * transverseMomentum n g.W

/-- The channel-cutoff energy is positive for all `n`. -/
theorem channelCutoffEnergy_pos (g : GrapheneWKBParams) (n : ℕ) :
    0 < channelCutoffEnergy g n :=
  mul_pos (soundSpeed_pos g) (transverseMomentum_pos n g.W g.W_pos)

/-- The channel-cutoff energy is strictly increasing in the channel index. -/
theorem channelCutoffEnergy_strictMono (g : GrapheneWKBParams) :
    StrictMono (channelCutoffEnergy g) := by
  intro n m hnm
  unfold channelCutoffEnergy
  have h_mono : transverseMomentum n g.W < transverseMomentum m g.W :=
    transverseMomentum_strictMono g.W g.W_pos hnm
  have h_pos : 0 < soundSpeed g := soundSpeed_pos g
  nlinarith [h_mono, h_pos]

/-!
## Section 4 — Quantitative Dean-Geometry Separation

The realised Dean bilayer-graphene de Laval nozzle has W = 1 μm and
c_s = 4.4 × 10⁵ m/s. The Hawking frequency at T_H ≈ 2.4 K is
ω_H = k_B T_H / ℏ ≈ 3.14 × 10¹¹ s⁻¹.

The supplied Dirichlet cutoff c_s*pi/W is about1.38e12s^-1 and exceeds
literal omega_H by about4.4. This comparison does not control evanescent
leakage, profile gradients, actual boundaries or a physical detector band.
-/

/-- Literal supplied-value inequality c_s*pi/W>4*omega_H at
    W=1um,c_s=4.4e5m/s and omega_H=3.14e11s^-1. The theorem has no
    scattering/state, evanescent-error, readout or bandwidth hypotheses.
    It does not certify a physical quasi-1D-safe detection interval or
    the Python producer's whole numerical grid. Those reductions and
    calibrated error bounds remain BUILD. -/
theorem dean_lowest_channel_above_four_omega_H :
    (4.4e5 : ℝ) * Real.pi / 1e-6 > 4 * 3.14e11 := by
  have hπ : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpos : (0 : ℝ) < (1e-6 : ℝ) := by norm_num
  rw [gt_iff_lt, lt_div_iff₀ hpos]
  -- Need: 4 * 3.14e11 * 1e-6 < 4.4e5 * π, i.e., 1.256e6 < 4.4e5 * π
  have h1 : (4 : ℝ) * 3.14e11 * 1e-6 = 1.256e6 := by norm_num
  rw [h1]
  -- Multiply 3.14 < π by 4.4e5 (positive) to get 1.3816e6 < 4.4e5·π
  have h2 : (4.4e5 : ℝ) * 3.14 < 4.4e5 * Real.pi :=
    mul_lt_mul_of_pos_left hπ (by norm_num)
  have h3 : (4.4e5 : ℝ) * 3.14 = 1.3816e6 := by norm_num
  linarith

/-- Algebraic upper bound1 on the adopted infrared scalar
    4*c_s*v/(c_s+v)^2 for positive supplied speeds. The theorem does
    not derive graphene transmission, physical open-channel selection
    or a finite-band roll-off. A conditional finite-sum envelope can
    use this scalar once its own hypotheses are met. -/
theorem channel_greybody_le_one
    (g : GrapheneWKBParams) (v : ℝ) (hv : 0 < v) :
    4 * soundSpeed g * v / (soundSpeed g + v) ^ 2 ≤ 1 :=
  SKEFTHawking.QuasiOneDReduction.greybody_zero_freq_le_one
    (soundSpeed g) v (soundSpeed_pos g) hv

/-!
## Section 5 — Sum-Over-Channels Spectrum

`channelSpectrumSum` defines an arbitrary finite sum beta_i*Gamma_i.
The caller supplies its finite index set and factors; the function does
not select physical open channels or derive beta/Gamma from a PDE.
Its algebra is not asserted identical to the Python current-noise array
or a full bilayer occupation/scattering/receiver construction.
-/

/-- Supplied finite weighted sum; interpreting its indices and factors
    as physical open-channel occupations requires separate matching. -/
noncomputable def channelSpectrumSum
    (N : ℕ) (β Γ : Fin N → ℝ) : ℝ :=
  ∑ i, β i * Γ i

/-- Nonnegativity of the finite weighted sum under the stated
    nonnegative-factor hypotheses; no physical state/noise realization
    or current-to-PSD relation is proved. -/
theorem channelSpectrumSum_nonneg
    (N : ℕ) (β Γ : Fin N → ℝ)
    (hβ : ∀ i, 0 ≤ β i) (hΓ : ∀ i, 0 ≤ Γ i) :
    0 ≤ channelSpectrumSum N β Γ :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hβ i) (hΓ i))

/-- Conditional finite-sum envelope from beta_i>=0 and Gamma_i<=Gamma_max.
    The value1 may bound the adopted infrared scalar, but physical
    frequency-dependent graphene factors must be established separately. -/
theorem channelSpectrumSum_bounded_uniform
    (N : ℕ) (β Γ : Fin N → ℝ) (Γmax : ℝ)
    (hβ : ∀ i, 0 ≤ β i) (hΓle : ∀ i, Γ i ≤ Γmax) :
    channelSpectrumSum N β Γ ≤ Γmax * ∑ i, β i := by
  unfold channelSpectrumSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_comm Γmax (β i)]
  exact mul_le_mul_of_nonneg_left (hΓle i) (hβ i)

/-!
## Section 6 — Module Summary

Wave 4 ships the integration capstone for the graphene Dirac-fluid analog
Hawking pipeline:

* **Sound-speed binding**: scalar c_s=v_F/sqrt(2) and c_s<v_F;
  no high-k collective-dispersion or horizon-robustness theorem.
* **Parameter binding**: actual supplied fields enter ExactWKBParams;
  all additional carrier/state/Bogoliubov hypotheses remain required.
* **Dirichlet scalar cutoffs**: positive and monotone by definition.
* **Supplied Dean comparison**: c_s*pi/W>4*literal omega_H, not a
  physical finite-width or calibrated-band certificate.
* **Finite sum**: nonnegativity and uniform-factor envelope under explicit
  supplied hypotheses, not physical open-channel selection or Python PSD.

Actual bilayer PDE/constitutive/current, boundaries, normalized scattering,
incoming state/noise and observable/reduction errors remain BUILD.
-/

end SKEFTHawking.DiracFluidWKB
