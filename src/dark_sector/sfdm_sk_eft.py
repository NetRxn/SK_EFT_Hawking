"""Phase 5x Wave 5 — SK-EFT framework applied to Superfluid Dark Matter.

Python companion to the generic SK-EFT ↔ SFDM parameter mapping
(Wave 1 Task 4 deep research). Provides:

- BK fiducial parameters (m, Λ, c_s per halo mass class)
- Sound-speed formula `c_s = √(2μ/m)` with BK-polytropic chemical
  potential `μ(ρ) = ρ²/(8Λ²m⁵)`
- Condensate fraction vs halo mass (BK Eq. 17)
- Bondi radius + analog Hawking temperature estimates (T_H ≪ T_CMB by
  23–29 orders — pedagogical / consistency check only)
- MOND-force FDR noise-floor bound (order-of-magnitude from
  fluctuation-dissipation)

This module does NOT compute the cluster-merger forecast — that is in
``sfdm_merger_forecast.py``. This module provides the underlying SFDM
physics primitives that both the forecast and Paper 17 §1-§3 text
rely on.

Lean refs
---------
- ``SFDMMergerForecast.sfdm_sound_speed_sq`` + positivity + scaling
- ``SFDMMergerForecast.c_s_subcluster_kms_fiducial`` etc.

Source
------
- Berezhiani, Khoury, *Theory of dark matter superfluidity*,
  PRD 92, 103510 (2015), arXiv:1507.01614
- Berezhiani, Cintia, De Luca, Khoury,
  *Superfluid Dark Matter* (review), arXiv:2505.23900 (2025)
- Visser, *Acoustic black holes*, CQG 15, 1767 (1998)
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum


# ---------------------------------------------------------------------------
# 1. Physical constants
# ---------------------------------------------------------------------------

#: Planck's reduced constant (J·s).
HBAR_J_S: float = 1.054571817e-34

#: Planck's reduced constant in eV·s.
HBAR_EV_S: float = 6.582119569e-16

#: Boltzmann constant (J/K).
K_B_J_K: float = 1.380649e-23

#: Speed of light (m/s).
C_LIGHT_M_S: float = 2.99792458e8

#: Speed of light (km/s).
C_LIGHT_KMS: float = 299792.458

#: Gravitational constant (m³/(kg·s²)).
G_NEWTON: float = 6.67430e-11

#: Solar mass (kg).
M_SUN_KG: float = 1.98892e30

#: Parsec (m).
PC_M: float = 3.0857e16

#: Kilo-parsec (m).
KPC_M: float = PC_M * 1e3

#: Mega-parsec (m).
MPC_M: float = PC_M * 1e6

#: Mean CMB temperature (K).
T_CMB_K: float = 2.725


# ---------------------------------------------------------------------------
# 2. BK fiducial SFDM parameters (Lean cross-check)
# ---------------------------------------------------------------------------


#: BK fiducial DM particle mass in eV. Lean ref:
#: ``SFDMMergerForecast.m_DM_eV_fiducial = 0.6``.
M_DM_EV_FIDUCIAL: float = 0.6

#: BK fiducial MOND coupling scale in meV. Lean ref:
#: ``SFDMMergerForecast.Lambda_meV_fiducial = 0.2``.
LAMBDA_MEV_FIDUCIAL: float = 0.2


class HaloMassClass(str, Enum):
    """Halo mass class used by BK for c_s and condensate-fraction tables."""

    GALAXY = "galaxy"  # 10^12 M_sun
    GROUP = "group"  # 10^13 M_sun
    SUBCLUSTER = "subcluster"  # 10^14 M_sun
    MAIN_CLUSTER = "main_cluster"  # 10^15 M_sun


#: BK fiducial sound speed in km/s per halo class (W1b §Block 2 Table). Lean
#: mirrors these in ``c_s_galaxy_kms_fiducial`` etc.
C_S_KMS_FIDUCIAL: dict[HaloMassClass, float] = {
    HaloMassClass.GALAXY: 242.0,
    HaloMassClass.GROUP: 607.0,
    HaloMassClass.SUBCLUSTER: 1525.0,
    HaloMassClass.MAIN_CLUSTER: float("nan"),  # 0% superfluid → no phonon c_s
}

#: Condensate fraction per halo class (BK Eq. 17 at m = 0.6 eV).
CONDENSATE_FRACTION: dict[HaloMassClass, float] = {
    HaloMassClass.GALAXY: 0.996,
    HaloMassClass.GROUP: 0.959,
    HaloMassClass.SUBCLUSTER: 0.59,
    HaloMassClass.MAIN_CLUSTER: 0.0,
}

#: Typical central DM density per halo class, g/cm³.
RHO_CENTRAL_G_CM3: dict[HaloMassClass, float] = {
    HaloMassClass.GALAXY: 1.6e-26,
    HaloMassClass.GROUP: 4.0e-26,
    HaloMassClass.SUBCLUSTER: 1.0e-25,
    HaloMassClass.MAIN_CLUSTER: 2.0e-25,
}


# ---------------------------------------------------------------------------
# 3. Sound speed formula
# ---------------------------------------------------------------------------


def sfdm_sound_speed_sq(mu_ev: float, m_ev: float) -> float:
    """BK SFDM sound speed squared in natural units (dimensionless).

    From the phonon quadratic Lagrangian:

        c_s² = 2μ/m

    Lean ref: ``SFDMMergerForecast.sfdm_sound_speed_sq``.

    Parameters
    ----------
    mu_ev : float
        Chemical potential in eV (non-relativistic chemical potential
        of the BK SFDM ground state).
    m_ev : float
        DM particle mass in eV.

    Returns
    -------
    float
        c_s² in units of c² (speed of light squared). Dimensionless.
    """
    if m_ev <= 0:
        raise ValueError(f"DM mass must be positive, got {m_ev}")
    return 2.0 * mu_ev / m_ev


def chemical_potential_ev(rho_g_cm3: float, m_ev: float, Lambda_mev: float) -> float:
    """BK chemical potential from BK Eq. (3-4): μ = ρ²/(8Λ²m⁵).

    Parameters
    ----------
    rho_g_cm3 : float
        Central DM density in g/cm³.
    m_ev : float
        DM particle mass in eV.
    Lambda_mev : float
        MOND coupling scale in meV.

    Returns
    -------
    float
        Chemical potential in eV.

    Notes
    -----
    This is an order-of-magnitude placeholder using the BK formula
    structure. The fiducial sound speeds in ``C_S_KMS_FIDUCIAL`` are
    directly from the deep research (W1b Table, Block 2) and should
    be preferred over computing from this formula.
    """
    if rho_g_cm3 <= 0 or m_ev <= 0 or Lambda_mev <= 0:
        raise ValueError("All parameters must be positive")
    Lambda_ev = Lambda_mev * 1e-3
    return (rho_g_cm3**2) / (8.0 * Lambda_ev**2 * m_ev**5)


def sound_speed_kms(halo_class: HaloMassClass) -> float:
    """Return the BK fiducial sound speed in km/s for a halo mass class.

    Direct lookup into ``C_S_KMS_FIDUCIAL``. Returns ``NaN`` for the
    main-cluster class (0% superfluid, no phonon sound speed).
    """
    return C_S_KMS_FIDUCIAL[halo_class]


# ---------------------------------------------------------------------------
# 4. Condensate fraction
# ---------------------------------------------------------------------------


def condensate_fraction(halo_class: HaloMassClass) -> float:
    """Return superfluid fraction `N_cond/N` from BK Eq. (17) via table.

    Direct lookup into ``CONDENSATE_FRACTION``.

    Lean ref: ``SFDMMergerForecast.condensate_frac_*``.
    """
    return CONDENSATE_FRACTION[halo_class]


def condensate_fraction_bk_formula(
    m_ev: float, M_halo_solar: float, T_normalization: float = 0.1
) -> float:
    """BK Eq. (17): `1 - (T/T_c)^(3/2)` with `T/T_c = 0.1 · (m/eV)^(8/3) · (M/10¹²)^(2/3)`.

    Falls below zero at high halo mass → returns 0 (fully normal phase).
    """
    if m_ev <= 0 or M_halo_solar <= 0:
        raise ValueError("Mass parameters must be positive")
    T_over_Tc = T_normalization * (m_ev ** (8.0 / 3.0)) * ((M_halo_solar / 1e12) ** (2.0 / 3.0))
    if T_over_Tc >= 1.0:
        return 0.0
    return 1.0 - T_over_Tc ** 1.5


# ---------------------------------------------------------------------------
# 5. Bondi radius + Hawking temperature estimates
# ---------------------------------------------------------------------------


def bondi_radius_pc(m_bh_solar: float, c_s_kms: float) -> float:
    """Bondi radius `r_B = G M_BH / c_s²` in parsec.

    For the Milky Way (M_BH = 4×10⁶ M_sun, c_s ≈ 220 km/s):
    r_B ≈ 0.36 pc.

    Parameters
    ----------
    m_bh_solar : float
        SMBH mass in solar masses.
    c_s_kms : float
        Local SFDM sound speed in km/s.

    Returns
    -------
    float
        Bondi radius in parsec.
    """
    if m_bh_solar <= 0 or c_s_kms <= 0:
        raise ValueError("Parameters must be positive")
    M_kg = m_bh_solar * M_SUN_KG
    c_s_ms = c_s_kms * 1e3
    r_B_m = G_NEWTON * M_kg / c_s_ms**2
    return r_B_m / PC_M


def analog_hawking_temperature_K(kappa_inv_s: float) -> float:
    """Analog Hawking temperature T_H = ℏκ/(2π k_B), κ in s⁻¹.

    Returns T_H in Kelvin. Lean ref: the existing
    ``AcousticMetric.hawking_temp_from_surface_gravity`` theorem.
    """
    if kappa_inv_s <= 0:
        raise ValueError("Surface gravity must be positive")
    return HBAR_J_S * kappa_inv_s / (2.0 * math.pi * K_B_J_K)


@dataclass(frozen=True)
class SFDMHorizonScenario:
    """One of the five SFDM acoustic-horizon scenarios from W1 Task 4 Table 1."""

    name: str
    description: str
    c_s_kms: float
    scale_L: float  # characteristic length scale
    scale_L_unit: str  # "pc" / "kpc" / "Mpc"
    kappa_inv_s: float  # surface gravity estimate
    T_H_K: float  # analog Hawking temperature


#: The five canonical SFDM horizon scenarios (all unobservable thermally).
SFDM_HORIZON_SCENARIOS: tuple[SFDMHorizonScenario, ...] = (
    SFDMHorizonScenario(
        name="MW SMBH Bondi",
        description="Bondi radius ~0.36 pc around Milky Way SMBH",
        c_s_kms=220.0,
        scale_L=0.36,
        scale_L_unit="pc",
        kappa_inv_s=2e-11,
        T_H_K=2.4e-23,
    ),
    SFDMHorizonScenario(
        name="Cluster merger interface",
        description="Merger interface at supersonic infall, ~100 kpc",
        c_s_kms=1000.0,
        scale_L=100.0,
        scale_L_unit="kpc",
        kappa_inv_s=3e-16,
        T_H_K=4e-28,
    ),
    SFDMHorizonScenario(
        name="BH sphere of influence",
        description="BH sphere of influence, MW, ~5 kpc",
        c_s_kms=150.0,
        scale_L=5.0,
        scale_L_unit="kpc",
        kappa_inv_s=1e-15,
        T_H_K=1.2e-27,
    ),
    SFDMHorizonScenario(
        name="Galactic soliton edge",
        description="Soliton boundary at ~1 kpc",
        c_s_kms=200.0,
        scale_L=1.0,
        scale_L_unit="kpc",
        kappa_inv_s=6e-15,
        T_H_K=8e-27,
    ),
    SFDMHorizonScenario(
        name="Filament infall",
        description="Cosmic web filament, virial radius ~1 Mpc",
        c_s_kms=250.0,
        scale_L=1.0,
        scale_L_unit="Mpc",
        kappa_inv_s=8e-18,
        T_H_K=1e-29,
    ),
)


def all_horizons_below_cmb() -> bool:
    """Sanity: every scenario has `T_H ≪ T_CMB`. Paper 17 key narrative.

    Returns True iff every ``SFDMHorizonScenario.T_H_K`` is strictly
    less than ``T_CMB_K``.
    """
    return all(s.T_H_K < T_CMB_K for s in SFDM_HORIZON_SCENARIOS)


def max_T_H_K() -> float:
    """Maximum analog Hawking temperature across the five scenarios (K)."""
    return max(s.T_H_K for s in SFDM_HORIZON_SCENARIOS)


# ---------------------------------------------------------------------------
# 6. MOND force + FDR noise-floor bound
# ---------------------------------------------------------------------------

#: MOND acceleration constant (m/s², Milgrom 1983).
A_0_MOND: float = 1.2e-10


def mond_acceleration(a_N_m_s2: float) -> float:
    """MOND acceleration in the strong-MOND limit: `a_φ = √(a_N · a_0)`.

    For Newtonian a_N « a_0 this is the interpolation limit. Lean ref
    L4 ``mond_force_derivation`` is Hard and deferred.
    """
    if a_N_m_s2 < 0:
        raise ValueError("Newtonian acceleration must be non-negative")
    return math.sqrt(a_N_m_s2 * A_0_MOND)


def fdr_noise_floor_fractional(
    T_over_Tc: float, Gamma_over_omega: float
) -> float:
    """FDR-derived fractional noise floor on MOND-mediated acceleration.

    Order-of-magnitude: `δa_φ / a_φ ~ (T/T_c)² · (Γ/ω)`.

    Parameters
    ----------
    T_over_Tc : float
        Temperature ratio.
    Gamma_over_omega : float
        Phonon damping / phonon frequency ratio.

    Returns
    -------
    float
        Fractional noise floor.
    """
    if T_over_Tc < 0 or Gamma_over_omega < 0:
        raise ValueError("All ratios must be non-negative")
    return T_over_Tc**2 * Gamma_over_omega


#: The observed McGaugh RAR scatter in dex (natural log, standard
#: convention). Roughly 0.06 dex intrinsic scatter per Lelli+2016.
RAR_SCATTER_DEX: float = 0.06

#: Upper-bound order-of-magnitude estimate on SFDM FDR contribution to
#: the RAR scatter (W1 Task 4 §3.1): ~10⁻⁵ to 10⁻³ fractional.
FDR_NOISE_FLOOR_RAR_MAX: float = 1e-3
FDR_NOISE_FLOOR_RAR_MIN: float = 1e-5


def fdr_below_rar_observed() -> bool:
    """Sanity: the SFDM FDR noise-floor upper bound is below observed
    RAR scatter (converted from dex to fractional).

    RAR scatter 0.06 dex ≈ 15% fractional scatter; FDR max at 10⁻³.
    """
    # 0.06 dex = 10^0.06 - 1 ≈ 0.148 fractional
    rar_fractional = 10 ** RAR_SCATTER_DEX - 1
    return FDR_NOISE_FLOOR_RAR_MAX < rar_fractional


# ---------------------------------------------------------------------------
# 7. Structured SFDM SK-EFT assessment
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SFDMSKEFTAssessment:
    """Phase 5x Wave 5 structured assessment of SFDM SK-EFT scope.

    Fields reflect the top-line conclusions of the Wave 1 Task 4 + W1b
    Task 9 deep research that are stable under the shipped Lean / Python
    primitives.

    Fields
    ------
    m_dm_ev : BK fiducial DM mass (eV).
    lambda_meV : BK fiducial MOND coupling (meV).
    all_horizons_below_cmb : True iff all 5 horizon T_H < T_CMB.
    max_T_H_K : max T_H across 5 scenarios (K).
    fdr_below_rar_observed : True iff FDR noise-floor upper bound
        does not saturate the observed RAR scatter.
    c_s_subcluster_kms : BK fiducial sub-cluster sound speed (km/s).
    condensate_frac_subcluster : BK Eq. 17 at 10^14 M_sun.
    paper17_status : narrative status string for Paper 17 §6.
    """

    m_dm_ev: float
    lambda_meV: float
    all_horizons_below_cmb: bool
    max_T_H_K: float
    fdr_below_rar_observed: bool
    c_s_subcluster_kms: float
    condensate_frac_subcluster: float
    paper17_status: str


def assess_sfdm_sk_eft() -> SFDMSKEFTAssessment:
    """Return the structured SFDM SK-EFT assessment used by Paper 17 §6."""
    return SFDMSKEFTAssessment(
        m_dm_ev=M_DM_EV_FIDUCIAL,
        lambda_meV=LAMBDA_MEV_FIDUCIAL,
        all_horizons_below_cmb=all_horizons_below_cmb(),
        max_T_H_K=max_T_H_K(),
        fdr_below_rar_observed=fdr_below_rar_observed(),
        c_s_subcluster_kms=C_S_KMS_FIDUCIAL[HaloMassClass.SUBCLUSTER],
        condensate_frac_subcluster=CONDENSATE_FRACTION[HaloMassClass.SUBCLUSTER],
        paper17_status=(
            "Thermal Hawking unobservable (T_H ≪ T_CMB by 23–29 orders). "
            "Scientific payoff is dissipative MOND corrections + FDR noise "
            "floor in RAR scatter + cluster-merger sonic boom (W5 W1b)."
        ),
    )
