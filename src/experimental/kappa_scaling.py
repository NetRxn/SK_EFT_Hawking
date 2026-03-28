"""
Kappa-Scaling Test Predictions for SK-EFT

Computes how dissipative and dispersive EFT corrections to the Hawking
spectrum scale with surface gravity κ at fixed BEC material properties.

Physics:
    At fixed material properties (ξ, c_s, γ₁, γ₂ all constant):
    - Dispersive correction:  δ_disp(κ) = -(π/6)(ξκ/c_s)²    ∝ κ²
    - Dissipative correction: δ_diss(κ) = (γ₁+γ₂)κ/c_s²      ∝ κ
    - Crossover:              κ_cross = 6(γ₁+γ₂)/(πξ²)

    The different scaling exponents (quadratic vs linear) provide an
    experimental handle: measuring the Hawking spectrum at multiple κ
    values reveals which correction dominates. The crossover κ_cross
    is a sharp EFT prediction.

    γ₁, γ₂ are material transport coefficients [m²/s] that depend on
    the BEC properties (density, scattering length) but NOT on the flow
    geometry (κ). This independence is what makes the κ-scaling test clean.

Experimental implementation:
    - Heidelberg K-39: Tune κ via Feshbach resonance (changes a_s → c_s, ξ,
      so material properties also change. The test is still valid but the
      interpretation requires tracking material property changes.)
    - All platforms: Tune κ via flow velocity (potential step height).
      This is the cleanest scenario since only κ changes.

Lean: KappaScaling.lean
    - kappa_scaling_dispersive_quadratic
    - kappa_scaling_dissipative_linear
    - kappa_scaling_crossover_unique

References:
    - Biondi, arXiv:2504.08833 (2025), §5.3 — EFT corrections
    - Oberthaler group DMD potential control — Heidelberg capability
"""

import numpy as np
from dataclasses import dataclass

from src.core.constants import KAPPA_SCALING_FACTORS
from src.core.formulas import (
    kappa_scaling_dispersive,
    kappa_scaling_dissipative,
    kappa_scaling_crossover,
    beliaev_transport_coefficients,
)
from src.core.transonic_background import (
    BECParameters,
    TransonicBackground,
    solve_transonic_background,
    steinhauer_Rb87,
    heidelberg_K39,
    trento_spin_sonic,
)


@dataclass
class KappaScalingSweep:
    """Results of a kappa-scaling sweep for one BEC platform.

    Attributes:
        platform_name: Name of the BEC platform.
        kappa_nominal: Nominal surface gravity [s⁻¹].
        kappa_values: Swept κ values [s⁻¹].
        delta_disp_values: Dispersive correction at each κ (negative).
        delta_diss_values: Dissipative correction at each κ (positive).
        delta_total_values: Total correction δ_disp + δ_diss at each κ.
        T_eff_ratio: T_eff/T_H = 1 + δ_total at each κ.
        kappa_cross: Crossover surface gravity [s⁻¹].
        scaling_exponent_disp: Fitted exponent for |δ_disp| vs κ.
        scaling_exponent_diss: Fitted exponent for δ_diss vs κ.
        gamma_1: Material transport coefficient [m²/s].
        gamma_2: Material transport coefficient [m²/s].
        c_s: Speed of sound [m/s].
        xi: Healing length [m].
    """
    platform_name: str
    kappa_nominal: float
    kappa_values: np.ndarray
    delta_disp_values: np.ndarray
    delta_diss_values: np.ndarray
    delta_total_values: np.ndarray
    T_eff_ratio: np.ndarray
    kappa_cross: float
    scaling_exponent_disp: float
    scaling_exponent_diss: float
    gamma_1: float
    gamma_2: float
    c_s: float
    xi: float


def compute_kappa_sweep(
    params: BECParameters,
    platform_name: str,
    kappa_factors: np.ndarray | None = None,
) -> KappaScalingSweep:
    """Compute kappa-scaling predictions for one BEC platform.

    Solves the transonic background at the nominal parameters to extract
    the surface gravity κ and material transport coefficients (γ₁, γ₂).
    Then sweeps κ over the specified range while holding material
    properties fixed.

    Args:
        params: BEC physical parameters.
        platform_name: Label for this platform.
        kappa_factors: Multipliers for nominal κ. Defaults to
            KAPPA_SCALING_FACTORS from constants.py.

    Returns:
        KappaScalingSweep with full scaling analysis.
    """
    if kappa_factors is None:
        kappa_factors = KAPPA_SCALING_FACTORS

    bg = solve_transonic_background(params)
    kappa_nom = bg.surface_gravity
    c_s = params.sound_speed_upstream
    xi = params.healing_length
    n_1D = params.density_upstream
    a_s = params.scattering_length

    # Material transport coefficients (kappa-independent)
    coeffs = beliaev_transport_coefficients(n_1D, a_s, kappa_nom, c_s, xi)
    gamma_1 = coeffs['gamma_1']
    gamma_2 = coeffs['gamma_2']

    # Sweep kappa
    kappa_values = kappa_factors * kappa_nom
    delta_disp = np.array([
        kappa_scaling_dispersive(k, xi, c_s) for k in kappa_values
    ])
    delta_diss = np.array([
        kappa_scaling_dissipative(k, gamma_1, gamma_2, c_s) for k in kappa_values
    ])
    delta_total = delta_disp + delta_diss
    T_eff_ratio = 1.0 + delta_total

    # Crossover
    k_cross = kappa_scaling_crossover(gamma_1, gamma_2, xi)

    # Fit scaling exponents via log-log regression
    log_kappa = np.log(kappa_values)
    alpha_disp = _fit_exponent(log_kappa, np.abs(delta_disp))
    alpha_diss = _fit_exponent(log_kappa, delta_diss)

    return KappaScalingSweep(
        platform_name=platform_name,
        kappa_nominal=kappa_nom,
        kappa_values=kappa_values,
        delta_disp_values=delta_disp,
        delta_diss_values=delta_diss,
        delta_total_values=delta_total,
        T_eff_ratio=T_eff_ratio,
        kappa_cross=k_cross,
        scaling_exponent_disp=alpha_disp,
        scaling_exponent_diss=alpha_diss,
        gamma_1=gamma_1,
        gamma_2=gamma_2,
        c_s=c_s,
        xi=xi,
    )


def _fit_exponent(log_x: np.ndarray, y: np.ndarray) -> float:
    """Fit power-law exponent: y = A * x^alpha via log-log regression."""
    valid = y > 0
    if np.sum(valid) < 2:
        return float('nan')
    coeffs = np.polyfit(log_x[valid], np.log(y[valid]), 1)
    return coeffs[0]


def compute_all_sweeps(
    kappa_factors: np.ndarray | None = None,
) -> dict[str, KappaScalingSweep]:
    """Compute kappa-scaling sweeps for all three BEC platforms.

    Returns:
        Dictionary mapping platform name to KappaScalingSweep.
    """
    platform_factories = {
        'Steinhauer': steinhauer_Rb87,
        'Heidelberg': heidelberg_K39,
        'Trento': trento_spin_sonic,
    }
    return {
        name: compute_kappa_sweep(factory(), name, kappa_factors)
        for name, factory in platform_factories.items()
    }


def kappa_scaling_summary(sweeps: dict[str, KappaScalingSweep] | None = None) -> dict:
    """Generate a summary table of kappa-scaling predictions.

    Returns:
        Dictionary with per-platform results and cross-platform analysis.
    """
    if sweeps is None:
        sweeps = compute_all_sweeps()

    summary = {}
    for name, sweep in sweeps.items():
        nom_idx = np.argmin(np.abs(sweep.kappa_values - sweep.kappa_nominal))
        summary[name] = {
            'kappa_nominal': sweep.kappa_nominal,
            'kappa_cross': sweep.kappa_cross,
            'kappa_ratio': sweep.kappa_nominal / sweep.kappa_cross,
            'regime': ('dispersive' if sweep.kappa_nominal > sweep.kappa_cross
                       else 'dissipative'),
            'delta_disp_nominal': sweep.delta_disp_values[nom_idx],
            'delta_diss_nominal': sweep.delta_diss_values[nom_idx],
            'scaling_exponent_disp': sweep.scaling_exponent_disp,
            'scaling_exponent_diss': sweep.scaling_exponent_diss,
            'gamma_1': sweep.gamma_1,
            'gamma_2': sweep.gamma_2,
        }

    return summary
