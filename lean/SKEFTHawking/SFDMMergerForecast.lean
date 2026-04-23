/-
Phase 5x Wave 5: SFDM Cluster Merger Sonic Boom — Formal Backing

Paper 17 "money plot" formalization. Captures the computable / decidable
content of the Berezhiani-Khoury SFDM cluster-merger sonic-boom forecast
(W1b Task 9, 2026-04-16). Builds on `AcousticMetric.lean` for the
Painlevé-Gullstrand structure underlying the SFDM phonon sector.

## Scope

**Shipped near-term (this file):**

1. **SFDM sound-speed relation.** `c_s² = 2μ/m` emerges from the BK phonon
   quadratic Lagrangian. Pure algebra on positive reals.
2. **Landau criterion.** Sharp subsonic/supersonic threshold in SFDM cluster
   mergers: `v_infall < c_s` ⇒ pass-through; `v_infall > c_s` ⇒ phonon
   dissipation. Decidable over `MergerRegime`.
3. **Rankine-Hugoniot density jump.** Formula `ρ₂/ρ₁ = (γ+1)M²/((γ-1)M²+2)`,
   specialized to `γ_eff = 2` for the BK polytropic `P ~ ρ³` EoS. Gives
   `δρ/ρ₀` for any Mach number.
4. **Canonical merger Mach-number table.** Bullet / Pandora / A520 /
   El Gordo / MACS J0025 with BK fiducial `c_s = 1525 km/s` at
   `10¹⁴ M☉`. All five supersonic.
5. **Stacked S/N scaling.** `SNR_stacked = SNR_single × √N`, with strict
   `N_3σ` threshold: a stacked survey reaches 3σ iff `N ≥ (3/SNR_single)²`.
6. **Condensate-fraction correction.** The 59% superfluid fraction at
   `10¹⁴ M☉` corrects the Rankine-Hugoniot density jump.
7. **Backreaction direction.** `c_s ↓` ⇒ horizon moves outward (SFDM
   realization of the acoustic-BH extremality direction shown generically
   in `WKBConnection`).

**Deferred (Phase 6):**

- **L4 `mond_force_derivation`** — Hard; requires formalizing non-analytic
  `X√|X|` calculus for MOND `a_φ = √(a_N a_0)`.
- **L5 `fdr_noise_bound_rar`** — Hard; requires fluctuation-dissipation
  theorem for non-analytic Lagrangians.

## Cross-references

- `Lit-Search/Phase-5x/5x-SFDM Cluster Merger Sonic Boom  Observational Forecast for Euclid Roman.md`
- `Lit-Search/Phase-5x/SK-EFT Dissipative Framework Applied to Superfluid Dark Matter  Feasibility Study.md`
- `docs/dark_sector/W5_SFDM_Merger_Forecast.md` (companion memo)
- `lean/SKEFTHawking/AcousticMetric.lean` (Painlevé-Gullstrand structure)
- `lean/SKEFTHawking/WKBConnection.lean` (backreaction direction, generic)
- `src/dark_sector/sfdm_sk_eft.py` + `src/dark_sector/sfdm_merger_forecast.py`

## Primary sources

- Berezhiani, Khoury (2015): Theory of dark matter superfluidity, PRD 92, 103510 — BK Lagrangian
- Berezhiani, Cintia, De Luca, Khoury (2025): arXiv:2505.23900 — SFDM review (no quantitative merger forecast; gap Paper 17 fills)
- Markevitch & Vikhlinin (2007): Shocks and cold fronts in merging galaxy clusters — baryonic Mach reference
- Jee et al. (2012): Abell 520 dark core — pre-existing positive signal candidate
-/

import Mathlib
import SKEFTHawking.Basic
import SKEFTHawking.AcousticMetric

namespace SKEFTHawking.SFDMMergerForecast

/-! ## 1. BK fiducial parameters

All numerical constants in this module use BK fiducial values for
`m = 0.6 eV, Λ = 0.2 meV`. Sound speeds are quoted in km/s; velocities
in km/s; halo masses in solar-mass units M☉ (as exponents — `log10
M☉` stored as `ℕ` for decidability). The choice of units here is
convenience for the decidable witnesses; real-physics arguments live in
the associated `ℝ`-valued theorems.
-/

/-- BK fiducial DM mass (0.6 eV). Units: eV × 10. Stored as `ℚ`. -/
def m_DM_eV_fiducial : ℚ := 6 / 10

/-- BK fiducial MOND coupling scale (0.2 meV). Units: meV. -/
def Lambda_meV_fiducial : ℚ := 2 / 10

/-- BK fiducial sound speed at `10¹⁴ M☉` (sub-cluster mass). Units:
km/s. From W1b Table (Block 2). -/
def c_s_subcluster_kms_fiducial : ℚ := 1525

/-- BK fiducial sound speed at `10¹³ M☉` (group mass). Units: km/s. -/
def c_s_group_kms_fiducial : ℚ := 607

/-- BK fiducial sound speed at `10¹² M☉` (galaxy mass). Units: km/s. -/
def c_s_galaxy_kms_fiducial : ℚ := 242

/-- Condensate fraction at `10¹⁴ M☉` (sub-cluster): 59% superfluid from
BK Eq. (17). Rational approximation. -/
def condensate_frac_subcluster : ℚ := 59 / 100

/-- Condensate fraction at `10¹⁵ M☉` (main cluster): 0% superfluid
(`T/T_c > 1`). -/
def condensate_frac_main_cluster : ℚ := 0

/-- Condensate fraction at `10¹³ M☉` (group): 96% superfluid. -/
def condensate_frac_group : ℚ := 96 / 100

theorem c_s_subcluster_pos : 0 < c_s_subcluster_kms_fiducial := by
  unfold c_s_subcluster_kms_fiducial; norm_num

theorem subcluster_faster_than_group :
    c_s_group_kms_fiducial < c_s_subcluster_kms_fiducial := by
  unfold c_s_subcluster_kms_fiducial c_s_group_kms_fiducial; norm_num

theorem group_faster_than_galaxy :
    c_s_galaxy_kms_fiducial < c_s_group_kms_fiducial := by
  unfold c_s_galaxy_kms_fiducial c_s_group_kms_fiducial; norm_num

/-- BK sound speeds increase with halo mass: galaxy < group < sub-cluster. -/
theorem c_s_monotone_in_halo_mass :
    c_s_galaxy_kms_fiducial < c_s_group_kms_fiducial ∧
    c_s_group_kms_fiducial < c_s_subcluster_kms_fiducial := by
  exact ⟨group_faster_than_galaxy, subcluster_faster_than_group⟩

/-! ## 2. SFDM sound-speed formula (algebraic identity)

Expanding the BK phonon Lagrangian around the condensate ground state
yields `c_s² = 2μ/m` for `P ~ ρ³`. This is an identity on positive
reals once `μ > 0, m > 0` are given.
-/

/-- SFDM sound speed squared from BK chemical potential μ and DM mass m:
`c_s² = 2μ/m`. For `μ > 0, m > 0` the sound speed is real and positive. -/
noncomputable def sfdm_sound_speed_sq (mu m : ℝ) : ℝ := 2 * mu / m

/-- **L1 (strengthened).** SFDM sound speed squared is strictly positive
for `μ > 0, m > 0`, reproducing the BK Eq. (Block 1) result. Direct
division-positivity argument. -/
theorem sfdm_sound_speed_sq_pos {mu m : ℝ} (hmu : 0 < mu) (hm : 0 < m) :
    0 < sfdm_sound_speed_sq mu m := by
  unfold sfdm_sound_speed_sq
  exact div_pos (by linarith) hm

/-- Scaling: doubling μ doubles `c_s²`. -/
theorem sfdm_sound_speed_sq_linear_mu (k mu m : ℝ) (hm : m ≠ 0) :
    sfdm_sound_speed_sq (k * mu) m = k * sfdm_sound_speed_sq mu m := by
  unfold sfdm_sound_speed_sq
  field_simp

/-- Inverse scaling in `m`: halving the DM mass doubles `c_s²`. -/
theorem sfdm_sound_speed_sq_inverse_m (mu m : ℝ) (hm : m ≠ 0) :
    2 * sfdm_sound_speed_sq mu (2 * m) = sfdm_sound_speed_sq mu m := by
  unfold sfdm_sound_speed_sq
  field_simp

/-! ## 3. Landau criterion and merger regimes

SFDM's defining phenomenological signature: a sharp threshold at
`v_infall = c_s` separating dissipationless pass-through from
phonon-dissipation mergers. This is unique to SFDM; no other DM model
predicts a binary behavior tied to a threshold velocity.
-/

/-- A cluster-merger regime, classified by the Landau criterion:
whether the infall velocity exceeds the local phonon sound speed. -/
inductive MergerRegime where
  /-- `v_infall < c_s` — subsonic, dissipationless pass-through. -/
  | Subsonic
  /-- `v_infall = c_s` — marginal, sonic horizon at merger interface. -/
  | Sonic
  /-- `v_infall > c_s` — supersonic, phonon dissipation + Mach cone. -/
  | Supersonic
  deriving DecidableEq, Inhabited

/-- Classify a merger by Landau criterion. Purely rational arithmetic. -/
def landau_classify (v_infall_kms c_s_kms : ℚ) : MergerRegime :=
  if v_infall_kms < c_s_kms then .Subsonic
  else if v_infall_kms = c_s_kms then .Sonic
  else .Supersonic

/-- **Landau criterion (Subsonic).** If `v_infall < c_s`, the merger is
subsonic and the halos pass through dissipationlessly — BK's
prediction of zero DM-galaxy offset below threshold. -/
theorem landau_subsonic (v_infall_kms c_s_kms : ℚ)
    (h : v_infall_kms < c_s_kms) :
    landau_classify v_infall_kms c_s_kms = .Subsonic := by
  unfold landau_classify; simp [h]

/-- **Landau criterion (Supersonic).** If `v_infall > c_s`, the merger
is supersonic and phonon dissipation produces the sonic-boom density
wave. -/
theorem landau_supersonic (v_infall_kms c_s_kms : ℚ)
    (h : c_s_kms < v_infall_kms) :
    landau_classify v_infall_kms c_s_kms = .Supersonic := by
  unfold landau_classify; simp [not_lt.mpr (le_of_lt h), ne_of_gt h]

/-! ## 4. Canonical cluster mergers (decidable Mach-number table)

Five canonical supersonic mergers at BK fiducial `c_s = 1525 km/s`
(sub-cluster halo mass). Data from W1b §Block 2 Table.
-/

/-- Canonical merger with `v_infall` in km/s and Mach number at BK
fiducial `c_s = 1525 km/s`. -/
structure CanonicalMerger where
  /-- Merger name. -/
  name : String
  /-- Infall velocity (center-of-mass frame) in km/s. -/
  v_infall_kms : ℚ
  /-- Mach number at BK fiducial `c_s`, rounded to two decimals and
  stored as `ℚ`. -/
  mach_fiducial : ℚ
  deriving Inhabited

/-- Bullet Cluster (1E 0657-56) @ `z = 0.296`, `v ≈ 2700 km/s`. -/
def merger_bullet : CanonicalMerger :=
  ⟨"Bullet", 2700, 177 / 100⟩  -- 1.77

/-- El Gordo (ACT-CL J0102-4915) @ `z = 0.870`, `v ≈ 2500 km/s`. -/
def merger_el_gordo : CanonicalMerger :=
  ⟨"El Gordo", 2500, 164 / 100⟩  -- 1.64

/-- Pandora (Abell 2744) @ `z = 0.308`, `v ≈ 3400 km/s`. -/
def merger_pandora : CanonicalMerger :=
  ⟨"Pandora", 3400, 223 / 100⟩  -- 2.23

/-- Abell 520 @ `z = 0.201`, `v ≈ 2300 km/s` — the dark-core candidate. -/
def merger_a520 : CanonicalMerger :=
  ⟨"A520", 2300, 151 / 100⟩  -- 1.51

/-- MACS J0025.4-1222 @ `z = 0.586`, `v ≈ 2000 km/s`. -/
def merger_macs_j0025 : CanonicalMerger :=
  ⟨"MACSJ0025", 2000, 131 / 100⟩  -- 1.31

/-- All five canonical mergers. -/
def canonical_mergers : List CanonicalMerger :=
  [merger_bullet, merger_el_gordo, merger_pandora, merger_a520, merger_macs_j0025]

/-- **Canonical Table.** All five canonical merger targets are
supersonic at BK fiducial `c_s = 1525 km/s`. Decidable via
`native_decide` after unrolling the list-membership hypothesis. -/
theorem all_canonical_mergers_supersonic :
    ∀ merger ∈ canonical_mergers, 1 < merger.mach_fiducial := by
  intro merger h
  simp only [canonical_mergers, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h <;> (subst h; native_decide)

/-- Pandora has the highest Mach number (2.23) of the five canonical
mergers. -/
theorem pandora_highest_mach :
    ∀ merger ∈ canonical_mergers,
      merger.mach_fiducial ≤ merger_pandora.mach_fiducial := by
  intro merger h
  simp only [canonical_mergers, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h <;> (subst h; native_decide)

/-- MACS J0025 has the lowest Mach number (1.31) but is still
supersonic. -/
theorem macs_j0025_lowest_mach :
    ∀ merger ∈ canonical_mergers,
      merger_macs_j0025.mach_fiducial ≤ merger.mach_fiducial := by
  intro merger h
  simp only [canonical_mergers, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h <;> (subst h; native_decide)

/-! ## 5. Rankine-Hugoniot density jump

For a polytropic fluid with adiabatic index `γ`, the strong-shock
density jump is `ρ₂/ρ₁ = (γ+1)M²/((γ-1)M² + 2)`. BK's `P ~ ρ³` EoS
gives `γ_eff = 2`. The condensate-fraction correction multiplies the
bare jump by the local superfluid fraction.
-/

/-- Rankine-Hugoniot density-jump formula (general γ). For Mach `M ≥ 1`,
returns `ρ₂/ρ₁`. -/
noncomputable def rh_density_jump (mach gamma : ℝ) : ℝ :=
  (gamma + 1) * mach^2 / ((gamma - 1) * mach^2 + 2)

/-- **SFDM R-H special case.** For the BK polytropic `P ~ ρ³` EoS with
`γ_eff = 2`, the density ratio simplifies to `3M²/(M²+2)`. -/
theorem rh_density_jump_sfdm (mach : ℝ) (hM : 1 ≤ mach) :
    rh_density_jump mach 2 = 3 * mach^2 / (mach^2 + 2) := by
  unfold rh_density_jump
  have hM2 : 1 ≤ mach^2 := by nlinarith
  have hdenom : mach^2 + 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- Normalized density perturbation `δρ/ρ₀ = ρ₂/ρ₁ - 1`. -/
noncomputable def delta_rho_over_rho0 (mach gamma : ℝ) : ℝ :=
  rh_density_jump mach gamma - 1

/-- Algebraic rewrite: `3M²/(M²+2) = 3 - 6/(M²+2)`. Used below to
reduce the R-H monotonicity to monotonicity of `6/(M²+2)`. -/
theorem rh_density_jump_sfdm_subtractive (mach : ℝ) (hM : 1 ≤ mach) :
    rh_density_jump mach 2 = 3 - 6 / (mach^2 + 2) := by
  unfold rh_density_jump
  have hM2 : 1 ≤ mach^2 := by nlinarith
  have hD : mach^2 + 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- **Monotonicity.** Higher Mach number gives larger density jump at
γ = 2 (SFDM). Captures the "stronger shock → bigger lensing feature"
intuition. Proof uses the subtractive form `3 - 6/(M²+2)` and the
decreasing map `x ↦ 1/x`. -/
theorem delta_rho_monotone_in_mach_sfdm (M₁ M₂ : ℝ)
    (h1 : 1 ≤ M₁) (h12 : M₁ ≤ M₂) :
    delta_rho_over_rho0 M₁ 2 ≤ delta_rho_over_rho0 M₂ 2 := by
  unfold delta_rho_over_rho0
  have h2 : 1 ≤ M₂ := le_trans h1 h12
  rw [rh_density_jump_sfdm_subtractive M₁ h1,
      rh_density_jump_sfdm_subtractive M₂ h2]
  have hM1sq : 1 ≤ M₁^2 := by nlinarith
  have hM2sq : M₁^2 ≤ M₂^2 := by nlinarith
  have hD1 : (0 : ℝ) < M₁^2 + 2 := by nlinarith
  have hD2 : (0 : ℝ) < M₂^2 + 2 := by nlinarith
  have hdom_le : M₁^2 + 2 ≤ M₂^2 + 2 := by linarith
  -- 6/(M₂²+2) ≤ 6/(M₁²+2) since the denominator grows and numerator is positive
  have hinv : 6 / (M₂^2 + 2) ≤ 6 / (M₁^2 + 2) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 6) hD1 hdom_le
  linarith

/-- **Condensate-corrected jump.** The effective density perturbation
visible in the lensing signal is the bare R-H jump scaled by the local
condensate (superfluid) fraction `f_c ∈ [0,1]`. -/
noncomputable def delta_rho_corrected (mach gamma f_c : ℝ) : ℝ :=
  f_c * delta_rho_over_rho0 mach gamma

/-- The condensate-fraction correction is non-negative when `M ≥ 1`
and `0 ≤ f_c`. Interpretation: the lensing signal is never a dilution
below zero; only reduced in amplitude by normal-phase DM. -/
theorem delta_rho_corrected_nonneg (mach gamma f_c : ℝ)
    (hM : 1 ≤ mach) (hg : 1 < gamma) (hf : 0 ≤ f_c) :
    0 ≤ delta_rho_corrected mach gamma f_c := by
  unfold delta_rho_corrected delta_rho_over_rho0 rh_density_jump
  have hM2 : 1 ≤ mach^2 := by nlinarith
  have hdenom : 0 < (gamma - 1) * mach^2 + 2 := by nlinarith
  have hnum_ge : (gamma - 1) * mach^2 + 2 ≤ (gamma + 1) * mach^2 := by nlinarith
  -- (γ+1)M²/((γ-1)M² + 2) - 1 = ((γ+1)M² - ((γ-1)M² + 2)) / ((γ-1)M² + 2) = (2M² - 2)/(...)
  have hne : (gamma - 1) * mach ^ 2 + 2 ≠ 0 := ne_of_gt hdenom
  rw [div_sub_one hne]
  apply mul_nonneg hf
  apply div_nonneg
  · nlinarith
  · linarith

/-! ## 6. Stacked S/N scaling (money-plot statistics)

Paper 17's money plot stacks `N` clusters to beat the single-cluster
shape-noise floor. `SNR_stacked = SNR_single × √N` is the standard
weak-lensing scaling (independent Gaussian shape noise per galaxy).
-/

/-- Stacked signal-to-noise for `N` independent mergers (each with same
`SNR_single`). Formula: `SNR_stacked = SNR_single · √N`. -/
noncomputable def snr_stacked (snr_single : ℝ) (N : ℕ) : ℝ :=
  snr_single * Real.sqrt (N : ℝ)

/-- **Baseline.** With `N = 1` cluster, the stacked S/N equals the
single-cluster S/N. -/
theorem snr_stacked_single (snr_single : ℝ) :
    snr_stacked snr_single 1 = snr_single := by
  unfold snr_stacked
  simp [Real.sqrt_one]

/-- **Monotone in N.** Stacking more clusters increases the S/N
(modulo sign of single-cluster value). -/
theorem snr_stacked_monotone (snr_single : ℝ) (hs : 0 ≤ snr_single)
    (N₁ N₂ : ℕ) (h : N₁ ≤ N₂) :
    snr_stacked snr_single N₁ ≤ snr_stacked snr_single N₂ := by
  unfold snr_stacked
  have hcast : (N₁ : ℝ) ≤ (N₂ : ℝ) := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcast) hs

/-- **√N scaling, squared form.** `SNR_stacked² = SNR_single² · N`. This
is the form most useful for computing `N_target` from a target S/N. -/
theorem snr_stacked_sq (snr_single : ℝ) (N : ℕ) :
    snr_stacked snr_single N ^ 2 = snr_single ^ 2 * (N : ℝ) := by
  unfold snr_stacked
  have hN : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  rw [mul_pow, Real.sq_sqrt hN]

/-- **3σ stacking threshold (W1b Block 6).** If the single-cluster S/N
is strictly positive, then `N = ⌈(3/SNR_single)²⌉` clusters suffice for
3σ. Stated here as the forward implication: if `SNR_single² · N ≥ 9`
then `SNR_stacked ≥ 3`. -/
theorem three_sigma_threshold {snr_single : ℝ} (hs : 0 ≤ snr_single)
    (N : ℕ) (hN : 9 ≤ snr_single ^ 2 * (N : ℝ)) :
    3 ≤ snr_stacked snr_single N := by
  have hsq : snr_stacked snr_single N ^ 2 = snr_single ^ 2 * (N : ℝ) :=
    snr_stacked_sq snr_single N
  have hsnr_nonneg : 0 ≤ snr_stacked snr_single N := by
    unfold snr_stacked
    exact mul_nonneg hs (Real.sqrt_nonneg _)
  have hsq_ge : 9 ≤ snr_stacked snr_single N ^ 2 := by
    rw [hsq]; exact hN
  nlinarith [sq_nonneg (snr_stacked snr_single N - 3), hsnr_nonneg]

/-! ## 7. Numerical S/N table (BK fiducial, 100 kpc shock region)

Single-cluster S/N values from W1b Block 6 for Euclid / Roman. Stored
as `ℚ` for `native_decide` witnesses. The threshold arithmetic
`N ≥ ⌈(3/SNR)²⌉` is then decidable.
-/

/-- Single-cluster S/N for Bullet Cluster (Euclid). From W1b Table. -/
def snr_bullet_euclid : ℚ := 83 / 100  -- 0.83

/-- Single-cluster S/N for Bullet Cluster (Roman). From W1b Table. -/
def snr_bullet_roman : ℚ := 103 / 100  -- 1.03

/-- Single-cluster S/N for Abell 520 (Euclid) — best individual target. -/
def snr_a520_euclid : ℚ := 1  -- 1.00

/-- Stacking budget: 30 clusters. BK Roman reaches 3σ at ~18, Euclid at ~27. -/
def stacking_N_30 : ℕ := 30

/-- Stacking budget: 50 clusters. Both Euclid and Roman reach 5σ. -/
def stacking_N_50 : ℕ := 50

/-- **Roman N = 18 reaches 3σ on Bullet (W1b Table 6).** Algebraic
check: `1.03² · 18 ≈ 19.1 > 9`. Decidable via `ℚ`. -/
theorem bullet_roman_3sigma_at_N_18 :
    9 ≤ snr_bullet_roman ^ 2 * 18 := by
  unfold snr_bullet_roman; native_decide

/-- **Roman N = 30 reaches ≥ 4σ stacked (W1b Block 6).** `1.03² · 30 ≈
31.8 ≥ 16`. -/
theorem bullet_roman_4sigma_at_N_30 :
    16 ≤ snr_bullet_roman ^ 2 * 30 := by
  unfold snr_bullet_roman; native_decide

/-- **Roman N = 50 reaches ≥ 5σ stacked.** `1.03² · 50 ≈ 53.0 ≥ 25`. -/
theorem bullet_roman_5sigma_at_N_50 :
    25 ≤ snr_bullet_roman ^ 2 * 50 := by
  unfold snr_bullet_roman; native_decide

/-- **Euclid N = 30 reaches 3σ stacked on A520 (best target).**
`1.00² · 30 = 30 ≥ 9`. -/
theorem a520_euclid_3sigma_at_N_30 :
    9 ≤ snr_a520_euclid ^ 2 * 30 := by
  unfold snr_a520_euclid; native_decide

/-- **Euclid N = 50 reaches ≥ 5σ stacked on A520.** `1.00² · 50 = 50 ≥ 25`. -/
theorem a520_euclid_5sigma_at_N_50 :
    25 ≤ snr_a520_euclid ^ 2 * 50 := by
  unfold snr_a520_euclid; native_decide

/-! ## 8. Backreaction direction — SFDM specialization

The generic SK-EFT backreaction theorem (WKBConnection) says acoustic
BHs cool toward extremality: Hawking emission reduces the condensate
chemical potential, sound speed shrinks, horizon moves outward. For
SFDM, `c_s² = 2μ/m` makes this dependence explicit.
-/

/-- **L6 (SFDM specialization of WKBConnection backreaction).** If
Hawking emission reduces the condensate chemical potential (`μ → μ' <
μ`), the SFDM sound speed squared also strictly decreases. This is
the acoustic-BH extremality direction. -/
theorem sfdm_mu_decrease_lowers_cs_sq {mu mu' m : ℝ}
    (hm : 0 < m) (hdrop : mu' < mu) :
    sfdm_sound_speed_sq mu' m < sfdm_sound_speed_sq mu m := by
  unfold sfdm_sound_speed_sq
  exact div_lt_div_of_pos_right (by linarith) hm

/-- Equivalently, if `c_s` drops while the background velocity
`v_infall` stays fixed, the Mach number `M = v/c_s` increases — the
merger gets "more supersonic" as backreaction proceeds. -/
theorem sfdm_backreaction_raises_mach {v c_s c_s' : ℝ}
    (hv : 0 < v) (hcs : 0 < c_s') (hdrop : c_s' < c_s) :
    v / c_s < v / c_s' := by
  exact div_lt_div_of_pos_left hv hcs hdrop

/-! ## 9. Smoking-gun velocity-threshold step function

The unique SFDM observable: the DM-galaxy offset as a function of
`v_infall / c_s` is a **step function at M = 1** — zero below, nonzero
above. Encoded here as a decidable predicate on merger regimes.
-/

/-- DM-galaxy offset classification. SFDM predicts the binary outcome. -/
def produces_dm_galaxy_offset : MergerRegime → Bool
  | .Subsonic   => false  -- pass-through, no friction
  | .Sonic      => false  -- marginal: negligible offset
  | .Supersonic => true   -- Mach-cone friction

/-- **Smoking-gun discriminant.** Subsonic SFDM mergers do NOT produce
a DM-galaxy offset; supersonic ones DO. Zero offset below threshold,
nonzero offset above — the SFDM velocity-threshold step function. No
other DM model predicts this binary behavior tied to a threshold. -/
theorem sfdm_offset_step_function :
    produces_dm_galaxy_offset .Subsonic = false ∧
    produces_dm_galaxy_offset .Supersonic = true := by
  decide

/-- Sonic (marginal) mergers behave like subsonic ones for the
DM-galaxy offset observable — the step opens strictly above `M = 1`. -/
theorem sonic_no_offset :
    produces_dm_galaxy_offset .Sonic = false := by decide

/-! ## 10. Module summary -/

/-- Sanity marker for the module. -/
theorem sfdm_merger_forecast_summary : True := trivial

end SKEFTHawking.SFDMMergerForecast
