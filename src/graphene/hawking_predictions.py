"""
Hawking temperature predictions for graphene Dirac fluid platforms.

Adapts the BEC SK-EFT dissipative correction framework to graphene:
- c_s → v_F/√2 (conformal Dirac fluid)
- Bogoliubov superluminal → subluminal many-body dispersion
- γ₁, γ₂ → graphene transport coefficients (η/w, σ_Q-related)

All formulas import from src/core/formulas.py (Pipeline Invariant 1).
Platform parameters from src/core/constants.py (Pipeline Invariant 2).

Phase 5w Wave 3.
"""

import numpy as np
from src.core.constants import HBAR, K_B, GRAPHENE_PLATFORMS
from src.core.formulas import (
    hawking_temperature,
    first_order_correction,
    dispersive_correction,
    decoherence_parameter,
    fdr_noise_floor,
    dirac_fluid_sound_speed,
    dirac_fluid_hawking_from_geometry,
    dirac_fluid_dissipation_window,
)


def graphene_surface_gravity(platform_name):
    """Surface gravity κ = |dv/dx| at the sonic horizon.

    For a de Laval nozzle with throat length L:
    κ ≈ c_s / L

    Args:
        platform_name: key in GRAPHENE_PLATFORMS.

    Returns:
        κ [s⁻¹]
    """
    plat = GRAPHENE_PLATFORMS[platform_name]
    return plat['gradient_s1']


def graphene_adiabaticity(platform_name):
    """Adiabaticity parameter D = κ ξ_eff / c_s for graphene.

    In BEC, ξ is the healing length (UV cutoff).  In graphene, the
    effective UV cutoff is set by the electron-electron scattering
    length l_ee (the scale below which hydrodynamics breaks down).

    D = κ · l_ee / c_s

    For the Dean nozzle: κ ~ 2e12, l_ee ~ 51 nm (at 150 K),
    c_s ~ 4.4e5 m/s → D ≈ 0.23.  This is well within the
    perturbative regime (D < 1).

    Args:
        platform_name: key in GRAPHENE_PLATFORMS.

    Returns:
        D (dimensionless)
    """
    plat = GRAPHENE_PLATFORMS[platform_name]
    kappa = plat['gradient_s1']
    c_s = plat['c_s']
    l_ee_m = plat['l_ee_nm'] * 1e-9
    return kappa * l_ee_m / c_s


def graphene_damping_rate_horizon(platform_name):
    """Effective damping rate Γ_H at the horizon for graphene.

    In the BEC SK-EFT: Γ_H = (γ₁ + γ₂)(κ/c_s)².
    For graphene, the dominant damping is sound attenuation from
    shear viscosity:

    Γ_sound ≈ (η/w) × k² = (η/w) × (ω_H/c_s)²

    where η/s ≈ 4 × ℏ/(4πk_B) (Majumdar 2025) and w ≈ Ts
    (conformal, w = ε + p = 3p = 3Ts/2... simplified: w ~ Ts).

    At the horizon, ω_H ≈ κ (the surface gravity sets the
    characteristic frequency), so:

    Γ_H ≈ (η/(Ts)) × (κ/c_s)²

    With η/s = 4ℏ/(4πk_B):
    η = 4ℏs/(4πk_B)
    Γ_H ≈ (4ℏ/(4πk_BT)) × (κ/c_s)²

    Args:
        platform_name: key in GRAPHENE_PLATFORMS.

    Returns:
        Γ_H [s⁻¹]
    """
    plat = GRAPHENE_PLATFORMS[platform_name]
    kappa = plat['gradient_s1']
    c_s = plat['c_s']
    T = plat['T_ambient_K']
    eta_over_s = plat['eta_over_s_KSS']  # in units of ℏ/(4πk_B)

    # η/s in SI: η/s = eta_over_s × ℏ/(4πk_B)
    eta_over_s_SI = eta_over_s * HBAR / (4 * np.pi * K_B)  # [K·s]

    # Γ_H = (η/(s·T)) × (κ/c_s)² = (η/s)/T × (κ/c_s)²
    Gamma_H = (eta_over_s_SI / T) * (kappa / c_s) ** 2
    return Gamma_H


def graphene_hawking_prediction(platform_name):
    """Full Hawking prediction for a graphene platform.

    Returns T_H, T_eff, and all correction parameters.

    Args:
        platform_name: key in GRAPHENE_PLATFORMS.

    Returns:
        dict with keys: T_H, T_eff, delta_disp, delta_diss, D, Gamma_H,
        kappa, c_s, omega_H_over_Gamma_mr, decoherence, noise_floor
    """
    plat = GRAPHENE_PLATFORMS[platform_name]
    kappa = plat['gradient_s1']
    c_s = plat['c_s']
    T_H = hawking_temperature(kappa)

    # Adiabaticity parameter
    D = graphene_adiabaticity(platform_name)

    # Dispersive correction (subluminal: same sign as BEC, but smaller
    # because l_ee/c_s < ξ/c_s typically)
    delta_disp = dispersive_correction(D)

    # Dissipative correction
    Gamma_H = graphene_damping_rate_horizon(platform_name)
    delta_diss = first_order_correction(Gamma_H, kappa)

    # Effective temperature
    T_eff = T_H * (1 + delta_disp + delta_diss)

    # Detection parameters
    delta_k = decoherence_parameter(Gamma_H, kappa)
    n_noise = fdr_noise_floor(delta_k)
    omega_H_over_Gamma_mr = plat['omega_H_over_Gamma_mr']

    return {
        'platform': platform_name,
        'T_H_K': T_H,
        'T_eff_K': T_eff,
        'delta_disp': delta_disp,
        'delta_diss': delta_diss,
        'D': D,
        'Gamma_H_s1': Gamma_H,
        'kappa_s1': kappa,
        'c_s_ms': c_s,
        'delta_k': delta_k,
        'noise_floor': n_noise,
        'omega_H_over_Gamma_mr': omega_H_over_Gamma_mr,
        'T_H_over_T_ambient': plat['T_H_over_T_ambient'],
        'correction_pct': (delta_disp + delta_diss) * 100,
    }


def graphene_noise_spectrum(platform_name, n_points=200, omega_max_ratio=5.0):
    """Hawking occupation spectrum and thermal occupation for a graphene platform.

    Computes n_Hawking(ω) and n_thermal(ω) for plotting the spectral shape.
    For the full current noise PSD S_I(ω) in A²/Hz, use
    wkb_spectrum.compute_graphene_spectrum() instead.

    The Hawking occupation number follows from the modified
    Bogoliubov relation with dissipative corrections:

    n_Hawking(ω) = |β(ω)|² / (1 - δ_k) + n_noise

    where |β(ω)|² = 1/(exp(2πω/κ) - 1) is the thermal Planck factor.

    Args:
        platform_name: key in GRAPHENE_PLATFORMS.
        n_points: number of frequency points.
        omega_max_ratio: max frequency as multiple of ω_H.

    Returns:
        dict with keys: omega (array), n_hawking (array),
        n_thermal (array), snr (array), metadata (dict)
    """
    pred = graphene_hawking_prediction(platform_name)
    plat = GRAPHENE_PLATFORMS[platform_name]
    kappa = pred['kappa_s1']
    T_ambient = plat['T_ambient_K']
    T_H = pred['T_H_K']
    delta_k = pred['delta_k']
    n_noise = pred['noise_floor']

    omega_H = K_B * T_H / HBAR
    omega = np.linspace(0.01 * omega_H, omega_max_ratio * omega_H, n_points)

    # Hawking occupation (modified Planck with decoherence)
    beta_sq = 1.0 / (np.exp(2 * np.pi * omega / kappa) - 1.0)
    n_hawking = beta_sq / (1 - delta_k) + n_noise

    # Thermal occupation at T_ambient
    n_thermal = 1.0 / (np.exp(HBAR * omega / (K_B * T_ambient)) - 1.0)

    # Signal-to-noise: Hawking signal relative to thermal background
    # S/N per frequency bin ∝ n_hawking / √(n_thermal)
    snr = n_hawking / np.sqrt(np.maximum(n_thermal, 1e-30))

    return {
        'omega': omega,
        'omega_over_omega_H': omega / omega_H,
        'n_hawking': n_hawking,
        'n_thermal': n_thermal,
        'snr': snr,
        'metadata': pred,
    }


def all_platform_predictions():
    """Generate predictions for all graphene platforms.

    Returns:
        dict mapping platform_name → prediction dict
    """
    results = {}
    for name in GRAPHENE_PLATFORMS:
        if name == 'PN_junction_10nm':
            continue  # Not an acoustic horizon
        results[name] = graphene_hawking_prediction(name)
    return results


def prediction_summary_table():
    """Print a formatted summary table of all platform predictions."""
    preds = all_platform_predictions()

    header = (f'{"Platform":<25} {"T_H (K)":>8} {"T_eff (K)":>9} '
              f'{"δ_disp":>8} {"δ_diss":>8} {"D":>6} '
              f'{"Γ_H (s⁻¹)":>12} {"ω_H/Γ_mr":>9}')
    print(header)
    print('─' * len(header))
    for name, p in preds.items():
        print(f'{name:<25} {p["T_H_K"]:>8.2f} {p["T_eff_K"]:>9.2f} '
              f'{p["delta_disp"]:>8.2e} {p["delta_diss"]:>8.2e} '
              f'{p["D"]:>6.3f} {p["Gamma_H_s1"]:>12.2e} '
              f'{p["omega_H_over_Gamma_mr"]:>9.2f}')
