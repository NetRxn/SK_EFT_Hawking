"""Numerical c_GW from vestigial-phase susceptibility.

All physics formulas come from ``src.core.formulas``. This module wraps
them with grid-evaluation and natural-anchor utilities.

Lean cross-reference: ``GravitationalWaves.c_GW`` and
``GravitationalWaves.c_GW_deviation``.
"""

from __future__ import annotations

import numpy as np

from src.core.constants import GW_PARAMS
from src.core.formulas import (
    c_GW_deviation_from_c,
    c_GW_from_chi_vest,
    c_GW_natural_range,
)


def c_GW_at_natural_anchor() -> float:
    """Return c_GW at χ_vest = 1 (natural anchor): equals c exactly.

    Lean: GravitationalWaves.c_GW_at_chi_one (Wave 2).
    """
    return c_GW_from_chi_vest(GW_PARAMS["CHI_VEST_DEFAULT"])


def c_GW_grid(
    chi_vest_lower: float | None = None,
    chi_vest_upper: float | None = None,
    n_points: int = 51,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Compute c_GW and Δc/c on a logarithmic χ_vest grid.

    Parameters
    ----------
    chi_vest_lower, chi_vest_upper : float, optional
        χ_vest grid endpoints. Default: ``GW.CHI_VEST_NATURAL_LOWER``
        / ``GW.CHI_VEST_NATURAL_UPPER`` from constants.py.
    n_points : int, default=51
        Grid resolution.

    Returns
    -------
    chi_grid : np.ndarray
        χ_vest values, shape (n_points,).
    c_GW_values : np.ndarray
        c_GW values in m/s.
    deviations : np.ndarray
        (c_GW − c) / c values (dimensionless).
    """
    lower = chi_vest_lower if chi_vest_lower is not None else GW_PARAMS["CHI_VEST_NATURAL_LOWER"]
    upper = chi_vest_upper if chi_vest_upper is not None else GW_PARAMS["CHI_VEST_NATURAL_UPPER"]
    chi_grid = np.geomspace(lower, upper, n_points)
    c_GW_values = np.array([c_GW_from_chi_vest(chi) for chi in chi_grid])
    deviations = np.array([c_GW_deviation_from_c(chi) for chi in chi_grid])
    return chi_grid, c_GW_values, deviations


def c_GW_natural_window_violation_factor() -> tuple[float, float, float]:
    """Compute the natural-range violation factor over the GW170817 cap.

    Returns the ratio max(|Δc/c|) / tol_GW170817 over the natural
    χ_vest range. Order ~10^14 — the central Wave 2 falsification number.

    Returns
    -------
    delta_min : float
        (c_GW − c)/c at χ_vest_lower.
    delta_max : float
        (c_GW − c)/c at χ_vest_upper.
    violation_ratio : float
        max(|Δc/c|) / tol_GW170817 over the natural range.
    """
    delta_min, delta_max = c_GW_natural_range(
        GW_PARAMS["CHI_VEST_NATURAL_LOWER"],
        GW_PARAMS["CHI_VEST_NATURAL_UPPER"],
    )
    abs_max = max(abs(delta_min), abs(delta_max))
    violation_ratio = abs_max / GW_PARAMS["C_GW_TWO_SIDED_CAP"]
    return float(delta_min), float(delta_max), float(violation_ratio)
