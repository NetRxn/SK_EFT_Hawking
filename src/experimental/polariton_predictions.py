"""
Polariton Platform Predictions — Tier 1 Perturbative Patch

Computes analog Hawking radiation predictions for driven-dissipative
polariton condensates using the Tier 1 perturbative patch: uniform
imaginary frequency shift ω(k) → ω(k) - iΓ_pol/2.

The Tier 1 patch is valid when Γ_pol/κ << 1 (long-lifetime cavities).
The Hawking temperature formula T_H = ℏκ/(2πk_B) survives — the
driven-dissipative nature primarily affects signal visibility through
spatial attenuation, not the intrinsic thermal spectrum.

Key difference from BEC:
- T_H ~ 0.1-4 K (vs ~0.35 nK for BEC) — 10^10x hotter
- Dominant damping is cavity decay Γ_pol (frequency-independent)
- EFT phonon damping is subdominant
- Spectral signature: Γ_pol is flat, EFT damping scales as ω^n (n≥2)

References:
    - Grisins et al., PRB 94, 144518 (2016) — T_H survives
    - Falque et al., PRL 135, 023401 (2025) — Paris polariton horizons
    - Jacquet et al., Eur. Phys. J. D 76, 152 (2022) — kinematics
    - Sieberer et al., Rep. Prog. Phys. 79, 096001 (2016) — SBD framework

Lean: PolaritonTier1.lean (6 theorems, zero sorry)
"""

import numpy as np
from dataclasses import dataclass

from src.core.constants import (
    POLARITON_PLATFORMS, POLARITON_MASS, HBAR, K_B,
)
from src.core.formulas import (
    dispersive_correction,
    polariton_spatial_attenuation,
    polariton_tier1_validity,
    polariton_hawking_temperature,
)


@dataclass
class PolaritonPlatform:
    """Polariton platform parameters with Tier 1 analysis.

    Attributes:
        name: Platform identifier.
        c_s: Speed of sound [m/s].
        xi: Healing length [m].
        kappa: Surface gravity [s⁻¹].
        Gamma_pol: Polariton decay rate [s⁻¹].
        D: Adiabaticity parameter.
        T_H: Hawking temperature [K].
        validity_ratio: Γ_pol/κ.
        tier1_regime: 'excellent'/'perturbative'/'borderline'/'intractable'.
        delta_disp: Dispersive correction at nominal parameters.
        delta_diss_eft: EFT phonon dissipative correction (subdominant).
    """
    name: str
    c_s: float
    xi: float
    kappa: float
    Gamma_pol: float
    D: float
    T_H: float
    validity_ratio: float
    tier1_regime: str
    delta_disp: float
    delta_diss_eft: float


@dataclass
class PolaritonComparison:
    """Comparison between polariton and BEC platforms.

    Attributes:
        polariton: Polariton platform data.
        bec_T_H: BEC Hawking temperatures for comparison [K].
        T_H_ratio: T_H(polariton) / T_H(BEC) for each BEC platform.
        spectral_signature: Description of the spectral difference.
    """
    polariton: PolaritonPlatform
    bec_T_H: dict[str, float]
    T_H_ratio: dict[str, float]
    spectral_signature: str


def compute_polariton_platform(name: str) -> PolaritonPlatform:
    """Compute Tier 1 predictions for one polariton platform.

    Args:
        name: Key in POLARITON_PLATFORMS dict.

    Returns:
        PolaritonPlatform with all derived quantities.
    """
    params = POLARITON_PLATFORMS[name]
    c_s = params['c_s']
    xi = params['xi']
    kappa = params['kappa']
    Gamma_pol = params['Gamma_pol']
    D = params['D']

    T_H = polariton_hawking_temperature(kappa)
    validity = polariton_tier1_validity(Gamma_pol, kappa)
    regime = params['tier1_regime']

    # Dispersive correction (same formula as BEC)
    delta_disp = dispersive_correction(D)

    # EFT phonon dissipative correction (subdominant for polaritons)
    gamma_dim = params['gamma_phonon_dim']
    delta_diss_eft = gamma_dim  # In natural units, delta_diss = Gamma_H/kappa = gamma_dim

    return PolaritonPlatform(
        name=name,
        c_s=c_s,
        xi=xi,
        kappa=kappa,
        Gamma_pol=Gamma_pol,
        D=D,
        T_H=T_H,
        validity_ratio=validity,
        tier1_regime=regime,
        delta_disp=delta_disp,
        delta_diss_eft=delta_diss_eft,
    )


def compute_all_polariton_platforms() -> dict[str, PolaritonPlatform]:
    """Compute predictions for all polariton platforms."""
    return {
        name: compute_polariton_platform(name)
        for name in POLARITON_PLATFORMS
    }


def polariton_bec_comparison() -> list[PolaritonComparison]:
    """Compare polariton platforms against BEC platforms.

    The key comparison points:
    1. T_H ratio (~10^10x hotter)
    2. Spectral signature difference (flat Γ_pol vs ω-dependent EFT)
    3. Tier 1 validity (which cavity qualities are EFT-testable)
    """
    from src.core.transonic_background import (
        steinhauer_Rb87, heidelberg_K39, trento_spin_sonic,
        solve_transonic_background,
    )
    from src.core.formulas import hawking_temperature

    # BEC Hawking temperatures
    bec_temps = {}
    for name, factory in [
        ('Steinhauer', steinhauer_Rb87),
        ('Heidelberg', heidelberg_K39),
        ('Trento', trento_spin_sonic),
    ]:
        bg = solve_transonic_background(factory())
        bec_temps[name] = hawking_temperature(bg.surface_gravity)

    comparisons = []
    for pol_name in POLARITON_PLATFORMS:
        pol = compute_polariton_platform(pol_name)
        ratios = {
            bec_name: pol.T_H / T_H_bec
            for bec_name, T_H_bec in bec_temps.items()
        }
        signature = (
            f"Γ_pol = {pol.Gamma_pol:.2e} s⁻¹ (flat), "
            f"EFT damping ∝ ω^n (n≥2). "
            f"Spectral separation {'feasible' if pol.tier1_regime in ('excellent', 'perturbative') else 'challenging'}."
        )
        comparisons.append(PolaritonComparison(
            polariton=pol,
            bec_T_H=bec_temps,
            T_H_ratio=ratios,
            spectral_signature=signature,
        ))

    return comparisons


def polariton_regime_map() -> dict[str, dict]:
    """Generate the Γ_pol/κ regime map for all cavity qualities.

    Returns a dict with platform name → regime classification and
    key parameters for the figure.
    """
    return {
        name: {
            'Gamma_pol_over_kappa': params['Gamma_pol_over_kappa'],
            'tier1_regime': params['tier1_regime'],
            'tau_cav_ps': params['tau_cav'] * 1e12,
            'T_H_K': params['T_H_K'],
            'D': params['D'],
        }
        for name, params in POLARITON_PLATFORMS.items()
    }
