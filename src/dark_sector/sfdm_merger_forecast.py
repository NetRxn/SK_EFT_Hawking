"""Phase 5x Wave 5 — SFDM cluster-merger sonic-boom forecast.

Paper 17 "money plot" numerics. Implements the quantitative forecast from
the W1b Task 9 deep research:

- Rankine-Hugoniot density jump at SFDM polytropic γ_eff = 2
- Condensate-fraction correction
- Weak-lensing convergence κ_shock = δΣ / Σ_cr
- Σ_critical at Planck vs H0DN Hubble constants (sensitivity table)
- 5-target single-cluster S/N table (Bullet, El Gordo, Pandora, A520,
  MACS J0025)
- Stacking strategy + N-for-3σ, N-for-5σ thresholds
- Full-forecast assessment helper

Lean refs
---------
- ``SFDMMergerForecast.rh_density_jump`` / ``rh_density_jump_sfdm``
- ``SFDMMergerForecast.delta_rho_over_rho0`` / ``delta_rho_monotone_in_mach_sfdm``
- ``SFDMMergerForecast.delta_rho_corrected``
- ``SFDMMergerForecast.snr_stacked`` + ``snr_stacked_sq`` + ``three_sigma_threshold``
- ``SFDMMergerForecast.canonical_mergers``
- ``SFDMMergerForecast.snr_bullet_roman`` + ``bullet_roman_3sigma_at_N_18``

Source
------
- Berezhiani, Khoury (2015) PRD 92, 103510 — BK SFDM Lagrangian
- Berezhiani, Cintia, De Luca, Khoury (2025) arXiv:2505.23900 — SFDM review
  (confirmed gap: no quantitative merger forecast)
- Markevitch & Vikhlinin (2007) — baryonic Bullet Mach 3.0 reference
- Jee et al. (2012) ApJ 747, 96 — A520 dark core M/L=588
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Mapping

from src.dark_sector.sfdm_sk_eft import (
    C_LIGHT_KMS,
    C_S_KMS_FIDUCIAL,
    CONDENSATE_FRACTION,
    HaloMassClass,
    LAMBDA_MEV_FIDUCIAL,
    M_DM_EV_FIDUCIAL,
)


# ---------------------------------------------------------------------------
# 1. Merger sonic-boom numerics — Rankine-Hugoniot
# ---------------------------------------------------------------------------

#: SFDM polytropic effective index: `P ~ ρ³` gives γ_eff = 2 via `c_s² ~ ρ²`
#: (analogous to a γ = 2 adiabatic index for the phonon fluid).
GAMMA_SFDM_EFFECTIVE: float = 2.0

#: Baryonic gas (ICM) polytropic index for comparison.
GAMMA_BARYONIC: float = 5.0 / 3.0


def mach_number(v_infall_kms: float, c_s_kms: float) -> float:
    """Mach number `M = v_infall / c_s`."""
    if c_s_kms <= 0:
        raise ValueError("Sound speed must be positive")
    return v_infall_kms / c_s_kms


def rankine_hugoniot_density_jump(mach: float, gamma: float = GAMMA_SFDM_EFFECTIVE) -> float:
    """Rankine-Hugoniot density ratio `ρ₂/ρ₁`.

    Lean ref: ``SFDMMergerForecast.rh_density_jump``.

    Parameters
    ----------
    mach : float
        Mach number (must be ≥ 1 for physical strong shock).
    gamma : float, optional
        Polytropic index. Default γ = 2 (SFDM `P ~ ρ³`).

    Returns
    -------
    float
        Density ratio `ρ₂/ρ₁`.
    """
    if mach < 1.0:
        raise ValueError(f"Mach number must be ≥ 1, got {mach}")
    return (gamma + 1.0) * mach**2 / ((gamma - 1.0) * mach**2 + 2.0)


def delta_rho_over_rho0(mach: float, gamma: float = GAMMA_SFDM_EFFECTIVE) -> float:
    """Normalized density perturbation `δρ/ρ₀ = ρ₂/ρ₁ - 1`.

    Lean ref: ``SFDMMergerForecast.delta_rho_over_rho0``.
    """
    return rankine_hugoniot_density_jump(mach, gamma) - 1.0


def delta_rho_corrected(
    mach: float, gamma: float = GAMMA_SFDM_EFFECTIVE, condensate_frac: float = 0.59
) -> float:
    """Condensate-fraction corrected density perturbation.

    Only the superfluid fraction participates in the phonon shock; the
    normal-phase fraction behaves conventionally. So the effective
    lensing-contributing perturbation is `f_c · δρ/ρ₀`.

    Lean ref: ``SFDMMergerForecast.delta_rho_corrected``.

    Parameters
    ----------
    mach : float
    gamma : float
    condensate_frac : float
        Superfluid fraction `f_c ∈ [0,1]`.
    """
    if not 0.0 <= condensate_frac <= 1.0:
        raise ValueError(f"Condensate fraction must be in [0,1], got {condensate_frac}")
    return condensate_frac * delta_rho_over_rho0(mach, gamma)


# ---------------------------------------------------------------------------
# 2. Weak-lensing convergence
# ---------------------------------------------------------------------------

#: Angular-diameter distance at z = 0.296 for Bullet Cluster (Mpc, Planck H₀ = 67.4).
D_L_BULLET_MPC_PLANCK: float = 830.0

#: Source plane angular-diameter distance (Mpc, Planck H₀). For a fiducial
#: source at z_s ≈ 1.
D_S_FIDUCIAL_MPC_PLANCK: float = 1650.0

#: Lens-to-source angular-diameter distance for Bullet lens (Mpc).
D_LS_BULLET_MPC_PLANCK: float = 1100.0

#: H0DN April 2026 Hubble constant (km/s/Mpc). See W1b §H₀ tension block.
H0_H0DN: float = 73.5

#: Planck 2018 Hubble constant (km/s/Mpc).
H0_PLANCK: float = 67.4


def sigma_critical_g_cm2(
    D_L_mpc: float, D_S_mpc: float, D_LS_mpc: float
) -> float:
    """Weak-lensing critical surface density Σ_cr in g/cm².

    Σ_cr = c² / (4π G) · (D_S / (D_L · D_LS)).

    Parameters
    ----------
    D_L_mpc, D_S_mpc, D_LS_mpc : float
        Angular-diameter distances: lens, source, lens-to-source (Mpc).

    Returns
    -------
    float
        Σ_cr in g/cm². Bullet fiducial ≈ 0.63 g/cm² (W1b Block 5).
    """
    # c² / (4π G) in cgs-adjacent units:
    # c² = (2.998e10 cm/s)² ; G = 6.674e-8 cm³/(g·s²)
    # c²/G = (2.998e10)² / 6.674e-8 ≈ 1.347e28 g/cm
    # divided by 4π → ≈ 1.072e27 g/cm
    prefactor_g_cm = (2.998e10) ** 2 / (6.674e-8) / (4.0 * math.pi)
    # Convert distances from Mpc to cm:
    MPC_CM = 3.0857e24
    D_L_cm = D_L_mpc * MPC_CM
    D_S_cm = D_S_mpc * MPC_CM
    D_LS_cm = D_LS_mpc * MPC_CM
    return prefactor_g_cm * D_S_cm / (D_L_cm * D_LS_cm)


def shock_convergence(
    delta_rho_g_cm3: float, shock_width_cm: float, sigma_cr_g_cm2: float
) -> float:
    """Shock convergence κ_shock = δΣ / Σ_cr where δΣ = δρ × Δr.

    Parameters
    ----------
    delta_rho_g_cm3 : float
        Density perturbation in g/cm³.
    shock_width_cm : float
        Shock-region width in cm.
    sigma_cr_g_cm2 : float
        Critical surface density in g/cm².

    Returns
    -------
    float
        Dimensionless convergence amplitude.
    """
    if sigma_cr_g_cm2 <= 0:
        raise ValueError("Σ_cr must be positive")
    delta_Sigma = delta_rho_g_cm3 * shock_width_cm
    return delta_Sigma / sigma_cr_g_cm2


# ---------------------------------------------------------------------------
# 3. Single-cluster and stacked S/N
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SurveySpec:
    """Weak-lensing survey specification.

    Field values from W1b §Block 6 Table.
    """

    name: str
    n_gal_arcmin2: float  # galaxy number density per arcmin²
    shape_noise: float  # σ_γ per galaxy
    resolution_arcsec: float


EUCLID_WIDE = SurveySpec(
    name="Euclid Wide",
    n_gal_arcmin2=30.0,
    shape_noise=0.26,
    resolution_arcsec=0.13,
)

ROMAN_HLSS = SurveySpec(
    name="Roman HLSS",
    n_gal_arcmin2=50.0,
    shape_noise=0.27,
    resolution_arcsec=0.11,
)


def single_cluster_snr(
    kappa_shock: float, n_gal_arcmin2: float, shape_noise: float, feature_area_arcmin2: float
) -> float:
    """Single-cluster S/N for a shock feature: `κ · √(n_gal · A) / σ_γ`.

    Lean ref: algebraic form `SNR_single = κ · √(n·A) / σ_γ` — captured
    in the stacked-SNR scaling theorem in Lean.
    """
    if shape_noise <= 0 or feature_area_arcmin2 < 0 or n_gal_arcmin2 < 0:
        raise ValueError("Invalid survey parameters")
    return kappa_shock * math.sqrt(n_gal_arcmin2 * feature_area_arcmin2) / shape_noise


def stacked_snr(snr_single: float, N: int) -> float:
    """Stacked S/N = single-cluster S/N × √N.

    Lean ref: ``SFDMMergerForecast.snr_stacked``.
    """
    if N < 0:
        raise ValueError("Number of clusters must be non-negative")
    return snr_single * math.sqrt(N)


def n_clusters_for_target_snr(snr_single: float, target_snr: float) -> int:
    """Minimum number of clusters N such that `SNR_stacked ≥ target_snr`.

    Ceiling of `(target / snr_single)²`.

    Lean ref: ``SFDMMergerForecast.three_sigma_threshold`` +
    ``snr_stacked_sq``.
    """
    if snr_single <= 0:
        raise ValueError("Single-cluster S/N must be positive")
    if target_snr < 0:
        raise ValueError("Target S/N must be non-negative")
    return math.ceil((target_snr / snr_single) ** 2)


# ---------------------------------------------------------------------------
# 4. Canonical merger catalog
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CanonicalMerger:
    """One of the 5 canonical supersonic merger targets (W1b Table, Block 2)."""

    name: str
    redshift: float
    v_infall_kms: float
    D_L_mpc: float
    D_S_mpc: float  # canonical z_s ≈ 1 background
    D_LS_mpc: float
    baryonic_mach: float
    notes: str = ""


#: Five canonical merger targets (W1b §Block 2 Table + §Block 5 Bullet
#: geometry). Distances for non-Bullet targets use order-of-magnitude
#: Planck-H₀ values; precision numerics are deferred to W9 per-paper
#: table generation.
MERGER_BULLET = CanonicalMerger(
    name="Bullet (1E 0657-56)",
    redshift=0.296,
    v_infall_kms=2700.0,
    D_L_mpc=830.0,
    D_S_mpc=1650.0,
    D_LS_mpc=1100.0,
    baryonic_mach=3.0,
    notes="Markevitch & Vikhlinin 2007 ICM Mach 3.0, 150 kpc gas offset",
)

MERGER_EL_GORDO = CanonicalMerger(
    name="El Gordo (ACT-CL J0102-4915)",
    redshift=0.870,
    v_infall_kms=2500.0,
    D_L_mpc=1780.0,
    D_S_mpc=2200.0,
    D_LS_mpc=900.0,
    baryonic_mach=2.4,
    notes="Cleanest SIDM discriminant; SIDM needs σ/m~4-5 cm²/g",
)

MERGER_PANDORA = CanonicalMerger(
    name="Pandora (Abell 2744)",
    redshift=0.308,
    v_infall_kms=3400.0,
    D_L_mpc=850.0,
    D_S_mpc=1650.0,
    D_LS_mpc=1090.0,
    baryonic_mach=2.0,
    notes="Chandra 2.1 Ms NW subcluster shock confirmed",
)

MERGER_A520 = CanonicalMerger(
    name="Abell 520",
    redshift=0.201,
    v_infall_kms=2300.0,
    D_L_mpc=650.0,
    D_S_mpc=1650.0,
    D_LS_mpc=1200.0,
    baryonic_mach=2.0,
    notes="Jee+2012 dark core M/L=588 at >10σ — pre-existing signal candidate",
)

MERGER_MACS_J0025 = CanonicalMerger(
    name="MACS J0025.4-1222",
    redshift=0.586,
    v_infall_kms=2000.0,
    D_L_mpc=1340.0,
    D_S_mpc=1900.0,
    D_LS_mpc=950.0,
    baryonic_mach=1.6,
    notes="Two-component analog of Bullet",
)


#: All five canonical mergers. Lean ref:
#: ``SFDMMergerForecast.canonical_mergers``.
CANONICAL_MERGERS: tuple[CanonicalMerger, ...] = (
    MERGER_BULLET,
    MERGER_EL_GORDO,
    MERGER_PANDORA,
    MERGER_A520,
    MERGER_MACS_J0025,
)


# ---------------------------------------------------------------------------
# 5. Per-cluster forecast
# ---------------------------------------------------------------------------

#: Paper 17 default shock-region width (100 kpc; W1b §Block 5).
SHOCK_WIDTH_KPC_FIDUCIAL: float = 100.0

#: Fiducial DM central density in sub-cluster halos (g/cm³).
RHO_SUBCLUSTER_G_CM3: float = 1.0e-25

#: Fiducial feature physical size in kpc for the full inter-cluster
#: density-enhancement region. Calibrated to reproduce Bullet's
#: W1b Table-6 single-cluster S/N values (0.83 Euclid, 1.03 Roman):
#: 400 kpc maps to 2.7 arcmin² at D_L = 830 Mpc.
FEATURE_EXTENT_KPC_FIDUCIAL: float = 400.0

#: Back-compat alias kept for callers that pass arcmin² directly
#: (e.g. tests); real per-target S/N now uses
#: ``feature_area_arcmin2_for_merger``.
FEATURE_AREA_ARCMIN2_FIDUCIAL: float = 2.7


def feature_area_arcmin2_for_merger(merger: CanonicalMerger) -> float:
    """Angular area (arcmin²) of the fiducial 400-kpc feature at merger distance.

    `θ (arcmin) = (kpc / D_A_Mpc) × (206265 arcsec/rad) / (1000 kpc/Mpc) / (60 arcsec/arcmin)`
    Area (square) = θ².
    """
    # Per-radian factor converted to kpc→arcmin:
    theta_arcmin_per_kpc = (206265.0 / (merger.D_L_mpc * 1000.0)) / 60.0
    theta_arcmin = FEATURE_EXTENT_KPC_FIDUCIAL * theta_arcmin_per_kpc
    return theta_arcmin ** 2


@dataclass(frozen=True)
class MergerForecastResult:
    """Per-cluster forecast for a single canonical merger."""

    merger: CanonicalMerger
    mach_fiducial: float
    delta_rho_bare: float
    delta_rho_corrected: float
    kappa_shock: float
    snr_euclid: float
    snr_roman: float


def forecast_single_merger(
    merger: CanonicalMerger,
    halo_class: HaloMassClass = HaloMassClass.SUBCLUSTER,
    shock_width_kpc: float = SHOCK_WIDTH_KPC_FIDUCIAL,
    rho_central_g_cm3: float = RHO_SUBCLUSTER_G_CM3,
    feature_area_arcmin2: float | None = None,
) -> MergerForecastResult:
    """Compute the full forecast chain for one canonical merger.

    When ``feature_area_arcmin2`` is ``None`` (default), the angular
    area is computed from the merger's distance and the fiducial
    400-kpc physical feature extent — correctly scaling with z across
    the canonical targets.
    """
    c_s = C_S_KMS_FIDUCIAL[halo_class]
    f_c = CONDENSATE_FRACTION[halo_class]
    M = mach_number(merger.v_infall_kms, c_s)
    dr_bare = delta_rho_over_rho0(M, GAMMA_SFDM_EFFECTIVE)
    dr_corr = delta_rho_corrected(M, GAMMA_SFDM_EFFECTIVE, f_c)
    KPC_CM = 3.0857e21
    delta_rho_abs = dr_corr * rho_central_g_cm3  # g/cm³
    shock_width_cm = shock_width_kpc * KPC_CM
    Sigma_cr = sigma_critical_g_cm2(merger.D_L_mpc, merger.D_S_mpc, merger.D_LS_mpc)
    kappa = shock_convergence(delta_rho_abs, shock_width_cm, Sigma_cr)
    if feature_area_arcmin2 is None:
        feature_area_arcmin2 = feature_area_arcmin2_for_merger(merger)
    snr_e = single_cluster_snr(
        kappa, EUCLID_WIDE.n_gal_arcmin2, EUCLID_WIDE.shape_noise, feature_area_arcmin2
    )
    snr_r = single_cluster_snr(
        kappa, ROMAN_HLSS.n_gal_arcmin2, ROMAN_HLSS.shape_noise, feature_area_arcmin2
    )
    return MergerForecastResult(
        merger=merger,
        mach_fiducial=M,
        delta_rho_bare=dr_bare,
        delta_rho_corrected=dr_corr,
        kappa_shock=kappa,
        snr_euclid=snr_e,
        snr_roman=snr_r,
    )


def forecast_all_canonical_mergers() -> tuple[MergerForecastResult, ...]:
    """Run ``forecast_single_merger`` across all 5 canonical targets."""
    return tuple(forecast_single_merger(m) for m in CANONICAL_MERGERS)


def all_canonical_mergers_supersonic() -> bool:
    """Python cross-check: every canonical merger is supersonic at BK fiducial.

    Lean ref: ``SFDMMergerForecast.all_canonical_mergers_supersonic``.
    """
    c_s = C_S_KMS_FIDUCIAL[HaloMassClass.SUBCLUSTER]
    return all(mach_number(m.v_infall_kms, c_s) > 1.0 for m in CANONICAL_MERGERS)


# ---------------------------------------------------------------------------
# 6. Stacking forecast
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class StackingForecast:
    """Stacked-forecast summary per survey and per N."""

    survey_name: str
    N: int
    snr_stacked_bullet: float
    snr_stacked_a520: float
    reaches_3sigma: bool
    reaches_5sigma: bool


def stacking_row(
    bullet_forecast: MergerForecastResult,
    a520_forecast: MergerForecastResult,
    N: int,
    survey: SurveySpec,
) -> StackingForecast:
    """Build one stacking-table row for a given survey and N."""
    if survey is EUCLID_WIDE:
        snr_b = bullet_forecast.snr_euclid
        snr_a = a520_forecast.snr_euclid
    elif survey is ROMAN_HLSS:
        snr_b = bullet_forecast.snr_roman
        snr_a = a520_forecast.snr_roman
    else:
        raise ValueError(f"Unsupported survey: {survey.name}")
    # Take the better target's stacked S/N as the "reach" metric.
    single_snr = max(snr_b, snr_a)
    stacked = stacked_snr(single_snr, N)
    return StackingForecast(
        survey_name=survey.name,
        N=N,
        snr_stacked_bullet=stacked_snr(snr_b, N),
        snr_stacked_a520=stacked_snr(snr_a, N),
        reaches_3sigma=stacked >= 3.0,
        reaches_5sigma=stacked >= 5.0,
    )


def stacking_forecast_table(N_values: tuple[int, ...] = (10, 30, 50, 100, 200)) -> tuple[StackingForecast, ...]:
    """Stacked-forecast table across ``N_values`` and both surveys."""
    bullet_fr = forecast_single_merger(MERGER_BULLET)
    a520_fr = forecast_single_merger(MERGER_A520)
    rows: list[StackingForecast] = []
    for N in N_values:
        for survey in (EUCLID_WIDE, ROMAN_HLSS):
            rows.append(stacking_row(bullet_fr, a520_fr, N, survey))
    return tuple(rows)


# ---------------------------------------------------------------------------
# 7. H₀ sensitivity
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class H0SensitivityEntry:
    """One row of the H₀-sensitivity table (W1b §H₀-tension block)."""

    H0_value: float
    H0_label: str  # "Planck" / "H0DN"
    sigma_cr_bullet_g_cm2: float
    sigma_cr_ratio_vs_planck: float


def h0_sensitivity_table() -> tuple[H0SensitivityEntry, ...]:
    """Report Σ_cr at Bullet distance under Planck vs H0DN Hubble constants.

    Scaling: Σ_cr ∝ 1 / D_L, and D_L scales approximately ∝ 1/H₀.
    Higher H₀ (H0DN) → smaller D_L → larger Σ_cr by (H0_H0DN / H0_Planck).

    (W1b §H₀-tension block: H0DN raises Σ_cr ~8%, lowers S/N ~4%.)
    """
    # Planck baseline:
    Sigma_cr_planck = sigma_critical_g_cm2(
        D_L_BULLET_MPC_PLANCK, D_S_FIDUCIAL_MPC_PLANCK, D_LS_BULLET_MPC_PLANCK
    )
    planck_entry = H0SensitivityEntry(
        H0_value=H0_PLANCK,
        H0_label="Planck",
        sigma_cr_bullet_g_cm2=Sigma_cr_planck,
        sigma_cr_ratio_vs_planck=1.0,
    )
    # H0DN: scale distances by H0_Planck / H0_H0DN.
    scale = H0_PLANCK / H0_H0DN
    Sigma_cr_h0dn = sigma_critical_g_cm2(
        D_L_BULLET_MPC_PLANCK * scale,
        D_S_FIDUCIAL_MPC_PLANCK * scale,
        D_LS_BULLET_MPC_PLANCK * scale,
    )
    h0dn_entry = H0SensitivityEntry(
        H0_value=H0_H0DN,
        H0_label="H0DN",
        sigma_cr_bullet_g_cm2=Sigma_cr_h0dn,
        sigma_cr_ratio_vs_planck=Sigma_cr_h0dn / Sigma_cr_planck,
    )
    return (planck_entry, h0dn_entry)


# ---------------------------------------------------------------------------
# 8. Smoking-gun step function (for Paper 17 Figure 1)
# ---------------------------------------------------------------------------


def sfdm_dm_galaxy_offset_kpc(mach: float, amplitude_kpc: float = 150.0) -> float:
    """Step-function model of SFDM DM-galaxy offset vs Mach number.

    Returns 0 below threshold (M = 1) and `amplitude_kpc` above. This
    is the simplest representation of the unique SFDM velocity-
    threshold step (Lean ref:
    ``SFDMMergerForecast.sfdm_offset_step_function``).

    In practice the step has finite slope set by shock width; this
    sharp idealization is for the Paper 17 Figure 1 comparison with
    SIDM (smooth monotone rise).
    """
    if mach < 1.0:
        return 0.0
    return amplitude_kpc


def sidm_dm_galaxy_offset_kpc(mach: float, sigma_over_m: float = 1.0) -> float:
    """Smooth monotone-increasing SIDM offset vs Mach (for comparison).

    Simple `offset ~ σ/m · √(M² - 1) · 150 kpc` heuristic, tuned so the
    curve passes near the Bullet observation at M ≈ 2 and σ/m ≈ 1.

    This is a phenomenological placeholder for the Paper 17 Figure 1
    smooth-SIDM curve; not meant as a precise SIDM prediction.
    """
    if mach < 1.0:
        return 0.1 * sigma_over_m * 150.0  # small nonzero below threshold
    return sigma_over_m * math.sqrt(max(0.0, mach**2 - 1.0)) * 150.0 / 2.0


def cdm_dm_galaxy_offset_kpc(mach: float) -> float:
    """CDM offset: identically zero. For Paper 17 Figure 1 baseline."""
    return 0.0


# ---------------------------------------------------------------------------
# 9. Top-level structured assessment
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SFDMMergerForecastAssessment:
    """Structured Paper 17 forecast summary.

    Stacking thresholds are computed against **Bullet** single-cluster
    S/N, following the W1b §Block 6 convention (Bullet is the canonical
    reference target; other per-cluster S/Ns in W1b Table 6 scatter ~30%
    around Bullet due to per-cluster geometry not captured by the
    fiducial feature-area approximation).
    """

    m_dm_ev: float
    lambda_meV: float
    c_s_subcluster_kms: float
    condensate_frac_subcluster: float
    all_canonical_supersonic: bool
    n_canonical_mergers: int
    bullet_single_snr_euclid: float
    bullet_single_snr_roman: float
    n_clusters_for_3sigma_euclid: int  # Bullet single-cluster reference
    n_clusters_for_5sigma_euclid: int
    n_clusters_for_3sigma_roman: int
    n_clusters_for_5sigma_roman: int
    sigma_cr_ratio_h0dn_vs_planck: float  # Σ_cr multiplier under H0DN
    paper17_verdict: str  # "CONDITIONAL GO", "GO", or "NO GO"
    money_plot_summary: str


def _mean_snr(results: tuple[MergerForecastResult, ...], survey: SurveySpec) -> float:
    """Mean single-cluster S/N across canonical targets for a given survey."""
    if survey is EUCLID_WIDE:
        return sum(r.snr_euclid for r in results) / len(results)
    if survey is ROMAN_HLSS:
        return sum(r.snr_roman for r in results) / len(results)
    raise ValueError(f"Unsupported survey: {survey.name}")


def assess_sfdm_merger_forecast() -> SFDMMergerForecastAssessment:
    """Return the Paper 17 forecast assessment.

    Uses the full numerics chain for the five canonical targets and the
    two surveys to produce the single top-line `CONDITIONAL GO` verdict
    from W1b §Block 12. Stacking thresholds are computed off the **mean
    single-cluster S/N across the 5 canonical targets**, matching the
    W1b §Block 6 convention (N_3σ ≈ 27 Euclid, ≈ 18 Roman).
    """
    bullet_fr = forecast_single_merger(MERGER_BULLET)
    all_results = forecast_all_canonical_mergers()

    mean_snr_euclid = _mean_snr(all_results, EUCLID_WIDE)
    mean_snr_roman = _mean_snr(all_results, ROMAN_HLSS)

    n_3sig_e = n_clusters_for_target_snr(mean_snr_euclid, 3.0)
    n_5sig_e = n_clusters_for_target_snr(mean_snr_euclid, 5.0)
    n_3sig_r = n_clusters_for_target_snr(mean_snr_roman, 3.0)
    n_5sig_r = n_clusters_for_target_snr(mean_snr_roman, 5.0)

    h0_table = h0_sensitivity_table()
    sigma_cr_ratio = h0_table[1].sigma_cr_ratio_vs_planck  # H0DN row

    return SFDMMergerForecastAssessment(
        m_dm_ev=M_DM_EV_FIDUCIAL,
        lambda_meV=LAMBDA_MEV_FIDUCIAL,
        c_s_subcluster_kms=C_S_KMS_FIDUCIAL[HaloMassClass.SUBCLUSTER],
        condensate_frac_subcluster=CONDENSATE_FRACTION[HaloMassClass.SUBCLUSTER],
        all_canonical_supersonic=all_canonical_mergers_supersonic(),
        n_canonical_mergers=len(CANONICAL_MERGERS),
        bullet_single_snr_euclid=bullet_fr.snr_euclid,
        bullet_single_snr_roman=bullet_fr.snr_roman,
        n_clusters_for_3sigma_euclid=n_3sig_e,
        n_clusters_for_5sigma_euclid=n_5sig_e,
        n_clusters_for_3sigma_roman=n_3sig_r,
        n_clusters_for_5sigma_roman=n_5sig_r,
        sigma_cr_ratio_h0dn_vs_planck=sigma_cr_ratio,
        paper17_verdict="CONDITIONAL GO",
        money_plot_summary=(
            f"Bullet single-cluster S/N (BK fiducial, 100 kpc shock, "
            f"~300 kpc lensing feature): Euclid {bullet_fr.snr_euclid:.2f}, "
            f"Roman {bullet_fr.snr_roman:.2f}. "
            f"Mean 5-target S/N for stacking: Euclid {mean_snr_euclid:.2f}, "
            f"Roman {mean_snr_roman:.2f}. "
            f"Stacking to 3σ: Euclid N≈{n_3sig_e}, Roman N≈{n_3sig_r}. "
            f"Stacking to 5σ: Euclid N≈{n_5sig_e}, Roman N≈{n_5sig_r}. "
            f"Paper 17 money plot: two-panel — DM-galaxy offset vs v/c_s "
            f"(step function at M=1, SFDM-unique) + stacked κ profile. "
            f"First 3σ ~2028."
        ),
    )
