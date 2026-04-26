"""Dispersion-correction probe for GW propagation.

Wraps the SecondOrderSK Γ_H bridge into a frequency-resolved dispersion
correction. Lean cross-reference: ``GravitationalWaves.dispersion_correction``.
"""

from __future__ import annotations

import numpy as np

from src.core.constants import GW_PARAMS
from src.core.formulas import dispersion_correction_from_GammaH


def leading_dispersion_correction(
    omega_hz: float,
    gamma_h_dimensionless: float | None = None,
) -> float:
    """Leading dissipative dispersion correction δω/ω at frequency ω.

    Parameters
    ----------
    omega_hz : float
        Probe frequency in Hz.
    gamma_h_dimensionless : float, optional
        Dimensionless Γ_H · ω/c² coefficient. Default: vestigial-regime
        placeholder ``GW.GAMMA_H_VESTIGIAL_DEFAULT``.

    Returns
    -------
    float
        Dimensionless dispersion correction δω/ω.
    """
    coef = (
        gamma_h_dimensionless
        if gamma_h_dimensionless is not None
        else GW_PARAMS["GAMMA_H_VESTIGIAL_DEFAULT"]
    )
    return dispersion_correction_from_GammaH(omega_hz, coef)


def dispersion_correction_grid(
    n_points: int = 41,
    gamma_h_dimensionless: float | None = None,
) -> tuple[np.ndarray, np.ndarray]:
    """Sweep the dispersion correction over the LIGO frequency band.

    Parameters
    ----------
    n_points : int, default=41
        Number of frequency points.
    gamma_h_dimensionless : float, optional
        Dimensionless Γ_H · ω/c² coefficient.

    Returns
    -------
    freqs : np.ndarray
        Frequencies in Hz, log-spaced from 10 Hz to 10 kHz.
    corrections : np.ndarray
        Dimensionless δω/ω values.
    """
    freqs = np.geomspace(
        GW_PARAMS["GW_FREQ_HZ_LOWER"],
        GW_PARAMS["GW_FREQ_HZ_UPPER"],
        n_points,
    )
    corrections = np.array([
        leading_dispersion_correction(f, gamma_h_dimensionless) for f in freqs
    ])
    return freqs, corrections
