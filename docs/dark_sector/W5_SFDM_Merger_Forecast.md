# Phase 5x Wave 5 — SFDM Cluster-Merger Sonic-Boom Forecast

**Wave status:** SHIPPED (2026-04-22 session 4)
**Lean module:** `lean/SKEFTHawking/SFDMMergerForecast.lean` — 30 theorems, 0 sorry, 0 new axioms, 499 LOC
**Python modules:** `src/dark_sector/sfdm_sk_eft.py` + `src/dark_sector/sfdm_merger_forecast.py`
**Tests:** `tests/test_sfdm_merger_forecast.py` — 86 passing
**Figures:** `fig_sfdm_velocity_threshold_step` (106) + `fig_sfdm_stacked_kappa_profile` (107) — the two Paper 17 money-plot panels
**Gates:** W9 (Paper 17 draft, Track A session 3)

---

## 1. Purpose

Paper 17's "money plot" turns the SFDM cluster-merger sonic-boom into a
quantitative forecast. W1b Task 9 established `CONDITIONAL GO`: single-
cluster S/N of 0.3–1.0 from Euclid or Roman under BK fiducial
parameters, rising to 3.5-5.7σ when 30–50 radio-relic mergers are
stacked. The BK 2025 Physics Reports review (arXiv:2505.23900, 118
pages) has **no quantitative merger forecast** — Paper 17 fills that
confirmed literature gap.

This wave ships the Lean-plus-Python infrastructure to make that
forecast machine-reproducible:

- **Lean.** Rankine-Hugoniot density jump at SFDM `γ_eff = 2`; Landau
  criterion subsonic/supersonic; all five canonical merger Mach numbers
  as decidable witnesses; stacked S/N √N scaling + 3σ thresholds; SFDM
  backreaction direction; velocity-threshold step function.
- **Python.** BK fiducial constants; sound-speed formula; condensate
  fraction table + BK Eq. 17; the full numerics chain from Mach number
  → R-H jump → condensate correction → convergence → single-cluster S/N
  → stacked S/N → stacking thresholds; Σ_cr under Planck vs H0DN;
  smoking-gun step function model.
- **Figures.** Two money-plot panels ready for Paper 17.

No new physics is claimed in W5 beyond W1b Task 9. The wave makes the
forecast's content machine-checkable and derives the top-line
`CONDITIONAL GO` verdict from a reproducible numerics chain.

---

## 2. Framework inputs (already shipped)

| Source | Artifact | Consumed fact |
|---|---|---|
| W1 Task 4 | SK-EFT ↔ SFDM mapping | `c_s² = 2μ/m`, parameter-mapping table, T_H ≪ T_CMB |
| W1b Task 9 | Merger sonic-boom forecast | 5-target Mach table, R-H with γ=2, condensate correction, S/N table, stacking ladder |
| `AcousticMetric.lean` | Painlevé-Gullstrand structure | 12 theorems, `gtt_vanishes_at_horizon`, `hawking_temp_from_surface_gravity` |
| `WKBConnection.lean` | Backreaction direction (generic) | Generic acoustic-BH extremality result |

---

## 3. Lean theorem roster (`SFDMMergerForecast.lean`)

30 theorems, 0 sorry, 0 new axioms. Representative roster:

### 3.1 BK fiducial constants + monotonicity (4)
- `c_s_subcluster_pos` — sub-cluster sound speed > 0
- `c_s_monotone_in_halo_mass` — galaxy < group < sub-cluster
- `subcluster_faster_than_group`, `group_faster_than_galaxy`

### 3.2 Sound-speed formula (3)
- `sfdm_sound_speed_sq_pos` — positivity from positive μ, m
- `sfdm_sound_speed_sq_linear_mu` — `c_s²` scales linearly in μ
- `sfdm_sound_speed_sq_inverse_m` — halving m doubles `c_s²`

### 3.3 Landau criterion + regime classifier (2)
- `landau_subsonic` — `v < c_s` ⇒ subsonic pass-through
- `landau_supersonic` — `v > c_s` ⇒ supersonic dissipation

### 3.4 Canonical Mach-number table (3)
- `all_canonical_mergers_supersonic` — all 5 canonical targets have M > 1 at BK fiducial
- `pandora_highest_mach` — Pandora at M = 2.23
- `macs_j0025_lowest_mach` — MACS J0025 at M = 1.31 (still > 1)

### 3.5 Rankine-Hugoniot + condensate correction (4)
- `rh_density_jump_sfdm` — closed form `3M²/(M²+2)` at γ = 2
- `rh_density_jump_sfdm_subtractive` — algebraic rewrite `3 − 6/(M²+2)`
- `delta_rho_monotone_in_mach_sfdm` — stronger shock ⇒ bigger δρ
- `delta_rho_corrected_nonneg` — `f_c · δρ/ρ₀ ≥ 0` when `f_c ≥ 0`, `M ≥ 1`

### 3.6 Stacked S/N scaling (4)
- `snr_stacked_single` — baseline `N = 1` case
- `snr_stacked_monotone` — larger N ⇒ higher stacked S/N
- `snr_stacked_sq` — squared identity `SNR² = SNR_single² · N`
- `three_sigma_threshold` — `SNR_single² · N ≥ 9 ⇒ SNR_stacked ≥ 3`

### 3.7 Decidable numerical S/N witnesses (5)
- `bullet_roman_3sigma_at_N_18` — Roman/Bullet hits 3σ by N = 18
- `bullet_roman_4sigma_at_N_30` — Roman/Bullet hits 4σ by N = 30
- `bullet_roman_5sigma_at_N_50` — Roman/Bullet hits 5σ by N = 50
- `a520_euclid_3sigma_at_N_30` — Euclid/A520 hits 3σ by N = 30
- `a520_euclid_5sigma_at_N_50` — Euclid/A520 hits 5σ by N = 50

### 3.8 Backreaction direction (2)
- `sfdm_mu_decrease_lowers_cs_sq` — `μ ↓ ⇒ c_s² ↓` from `c_s² = 2μ/m`
- `sfdm_backreaction_raises_mach` — `c_s ↓` ⇒ `M ↑` for fixed `v`

### 3.9 Smoking-gun step function (3)
- `sfdm_offset_step_function` — `Subsonic → 0`, `Supersonic → nonzero`
- `sonic_no_offset` — `M = 1` marginal ⇒ 0 (step opens strictly above)

Plus a summary marker.

---

## 4. Python chain (`sfdm_merger_forecast.py`)

### 4.1 Canonical merger catalog

Five dataclass records: Bullet, El Gordo, Pandora, A520, MACS J0025 —
each with redshift, infall velocity, angular-diameter distances, and
baryonic Mach number for comparison. `CANONICAL_MERGERS` is the Lean-
mirrored ordered tuple.

### 4.2 Forecast chain

`forecast_single_merger(merger)` runs:

1. `mach_number` = `v_infall / c_s` at BK fiducial sub-cluster `c_s`
2. `delta_rho_over_rho0` at `γ_eff = 2`
3. `delta_rho_corrected` = `f_c · δρ/ρ₀` with sub-cluster condensate fraction
4. `sigma_critical_g_cm2` from the merger's angular-diameter distances
5. `feature_area_arcmin2_for_merger` — z-scaled from 400-kpc physical extent (calibrated to W1b Bullet entry: 400 kpc @ D_L = 830 Mpc → 2.7 arcmin²)
6. `shock_convergence` = `δρ · Δr / Σ_cr`
7. Per-survey single-cluster `S/N = κ · √(n·A) / σ_γ` for Euclid + Roman

### 4.3 Top-level assessment

`assess_sfdm_merger_forecast()` returns `SFDMMergerForecastAssessment`:

| Field | Value at BK fiducial |
|---|---|
| m_dm_ev | 0.6 |
| lambda_meV | 0.2 |
| c_s_subcluster_kms | 1525.0 |
| condensate_frac_subcluster | 0.59 |
| all_canonical_supersonic | `True` |
| n_canonical_mergers | 5 |
| bullet_single_snr_euclid | **0.83** (matches W1b Table 6) |
| bullet_single_snr_roman | **1.04** (matches W1b Table 6) |
| n_clusters_for_3σ_euclid | ~20 (mean 5-target) |
| n_clusters_for_3σ_roman | ~13 (mean 5-target) |
| n_clusters_for_5σ_euclid | ~55 |
| n_clusters_for_5σ_roman | ~36 |
| sigma_cr_ratio_h0dn_vs_planck | 1.091 (H0DN raises Σ_cr by ~9%) |
| paper17_verdict | `"CONDITIONAL GO"` |

### 4.4 Calibration note

The Bullet-cluster single-cluster S/N matches W1b Table 6 exactly
(by design: the fiducial 400-kpc feature extent is calibrated to it).
The other four targets' S/N values lie within a factor ~1.5× of W1b's
per-cluster numbers — the residual comes from per-cluster geometry
details (shock width, source-plane populations, mass-model choices)
not captured by the fiducial extent. The **stacking thresholds**
computed from the mean 5-target S/N come within a factor ~1.4× of W1b
(N_3σ = 20 vs W1b's 27 for Euclid); within expected uncertainty for
an order-of-magnitude Paper 17 forecast.

Per-cluster precision requires the full lensing likelihood modeling
that Paper 17 will fold in at the paper-numerics stage (W9).

---

## 5. Figures (`visualizations.py`)

### 5.1 `fig_sfdm_velocity_threshold_step` — Fig 106 (money-plot LEFT)

DM-galaxy offset vs Mach number for three models:

- **SFDM** — step function at M = 1 (the defining signature)
- **SIDM** — smooth monotonic rise from below threshold (σ/m = 1 cm²/g)
- **CDM** — identically zero (baseline)

Five canonical merger Mach numbers overlaid as diamonds. The unique
SFDM velocity-threshold prediction is the discriminator: no other DM
model predicts a binary behavior tied to a threshold velocity.

### 5.2 `fig_sfdm_stacked_kappa_profile` — Fig 107 (money-plot RIGHT)

Stacked S/N vs N (number of stacked mergers) for Euclid and Roman,
normalized to the Bullet single-cluster S/N. Three-sigma and five-
sigma horizontal thresholds, with N = 30 and N = 50 stacking
reference points. Shows:

- 3σ reached between N ≈ 9 (Roman) and N ≈ 14 (Euclid) at the
  Bullet-referenced single-cluster S/N
- 5σ reached between N ≈ 24 (Roman) and N ≈ 36 (Euclid)

---

## 6. H₀ tension impact

`h0_sensitivity_table()` reports Σ_cr at Planck `H_0 = 67.4` vs H0DN
April-2026 `H_0 = 73.5`:

| H_0 | Σ_cr (Bullet) | ratio vs Planck |
|---|---|---|
| 67.4 | 0.625 g/cm² | 1.000 |
| 73.5 | 0.682 g/cm² | 1.091 |

H0DN raises Σ_cr by ~9%, which shifts single-cluster S/N ~4% lower.
Below the dominant Λ uncertainty (factor ~2-5×) — not meaningful for
the go/no-go verdict. Paper 17 §5 absorbs this into the systematic
error budget and introduces BK-Wang (2017) phonon-mediated
acceleration as an introduction hook linking SFDM phonon EFT to the
H_0 tension.

---

## 7. Deferred for Paper 17 / Phase 6

- **Lean L4** `mond_force_derivation` (Hard) — formalizing the
  non-analytic `X√|X|` calculus for the MOND `a_φ = √(a_N a_0)`
  identity in the strong-field limit.
- **Lean L5** `fdr_noise_bound_rar` (Hard) — the FDR noise-floor bound
  on the radial acceleration relation (RAR) scatter.
- **Lean L3** `sfdm_transport_count` (Medium) — extending the SK-EFT
  2-fluid coefficient counting to SFDM vortex mutual friction.
- **Lean L6 full** — a tighter `sfdm_backreaction_direction` result
  tying the horizon-position shift to a specific integral formula.
- **Python vortex mutual-friction** — vortex lattice + Hall-viscosity
  corrections (undeveloped in current BK literature).
- **Paper 17 §5 Σ_cr per-cluster rigor** — replace the fiducial
  feature-extent approximation with per-cluster weak-lensing likelihood
  modeling.
- **Abell 520 dark-core quantitative prediction** — the W1b §Block 8
  mass-to-light-ratio match against Jee+2012 M/L = 588. Requires
  additional normal-phase DM column-density modeling beyond current
  `src/dark_sector/sfdm_merger_forecast.py` scope.

---

## 8. Triggers to update this memo

- **Full stacked κ-profile data lands** (Euclid Year-2 or Roman HLSS
  Y1) — replace the forecast curves with fit-to-data Figure 106/107.
- **W9 Paper 17 draft** — this memo feeds the §4–5 text of Paper 17
  (§4 cluster-merger sonic boom, §5 stacking statistics + H_0-tension
  systematic budget).
- **BK-group publishes quantitative merger forecast** — reassess the
  "BK has no forecast" gap claim. As of 2026-04-22 the gap is confirmed.
- **Novel SFDM UV completion fixes Λ** — currently the forecast is
  presented as a function of Λ; an independent Λ constraint would
  collapse the parameter uncertainty.

---

## 9. References

- `docs/roadmaps/Phase5x_Roadmap.md` — Wave 5 specification
- `Lit-Search/Phase-5x/5x-SFDM Cluster Merger Sonic Boom ...` — W1b Task 9
- `Lit-Search/Phase-5x/SK-EFT Dissipative Framework Applied to Superfluid Dark Matter ...` — Wave 1 Task 4
- `lean/SKEFTHawking/SFDMMergerForecast.lean`
- `lean/SKEFTHawking/AcousticMetric.lean` (reused structure)
- `src/dark_sector/sfdm_sk_eft.py` + `sfdm_merger_forecast.py`
- `tests/test_sfdm_merger_forecast.py`
- Berezhiani, Khoury (2015) PRD 92, 103510
- Berezhiani, Cintia, De Luca, Khoury (2025) arXiv:2505.23900 (BK review, no quantitative forecast)
- Markevitch, Vikhlinin (2007) Phys. Rep. 443 — Bullet shock 3.0
- Jee et al. (2012) ApJ 747, 96 — A520 dark core M/L = 588
- H0DN Collaboration (April 2026) — H_0 = 73.50 ± 0.81 km/s/Mpc
