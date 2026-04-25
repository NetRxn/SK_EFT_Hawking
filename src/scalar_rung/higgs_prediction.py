"""Microscopic Higgs-mass prediction from the Wetterich scalar-channel
gap equation. Phase 5z Wave 1 correctness-push anchor.

Implements parameter scans over (Λ_UV, N_f, G_c, λ_4) and reports the
``ScalarRungQuantitativeMatch`` predicate (Lean: ScalarRungInterpretation.
scalar_rung_quantitative_match_iff) over the grid.
"""

from __future__ import annotations

import numpy as np

from src.core.constants import EW_PARAMS
from src.core.formulas import (
    higgs_mass_from_condensate,
    scalar_rung_quantitative_match,
)


def higgs_mass_scan(
    lambda_uv_range: np.ndarray,
    n_f: int = None,
    g_c_range: np.ndarray = None,
    lam4_range: np.ndarray = None,
):
    """Compute the microscopic m_H prediction over a 3D grid.

    Defaults to the EW_PARAMS fiducials.

    Parameters
    ----------
    lambda_uv_range : np.ndarray
        UV cutoff values in GeV.
    n_f : int, optional
        Weyl fermion count; defaults to ``EW.N_F_FIDUCIAL`` (15).
    g_c_range : np.ndarray, optional
        Dimensionless 4-fermion coupling values.
    lam4_range : np.ndarray, optional
        Scalar-channel quartic values.

    Returns
    -------
    np.ndarray
        4-D array indexed by (Λ_UV, G_c, λ_4) with shape
        (len(lambda_uv_range), len(g_c_range), len(lam4_range)).
    """
    if n_f is None:
        n_f = EW_PARAMS["N_F_FIDUCIAL"]
    if g_c_range is None:
        g_c_range = np.array([EW_PARAMS["G_C_FIDUCIAL"]])
    if lam4_range is None:
        lam4_range = np.array([EW_PARAMS["LAMBDA_4_FIDUCIAL"]])

    grid = np.zeros((len(lambda_uv_range), len(g_c_range), len(lam4_range)))
    for i, lambda_uv in enumerate(lambda_uv_range):
        for j, g_c in enumerate(g_c_range):
            for k, lam4 in enumerate(lam4_range):
                grid[i, j, k] = higgs_mass_from_condensate(
                    lambda_uv, n_f, g_c, lam4
                )
    return grid


def quantitative_match_grid(
    lambda_uv_range: np.ndarray,
    g_c_range: np.ndarray,
    lam4_range: np.ndarray,
    n_f: int = None,
    m_H_obs: float = None,
    tolerance: float = None,
):
    """Boolean grid: where does the microscopic m_H prediction match 125 GeV?

    Parameters
    ----------
    lambda_uv_range, g_c_range, lam4_range : np.ndarray
        Scan ranges.
    n_f : int, optional
        Weyl count, default ``EW.N_F_FIDUCIAL``.
    m_H_obs : float, optional
        Observed Higgs mass, default ``EW.M_H_GEV``.
    tolerance : float, optional
        Match tolerance, default ``EW.M_H_MATCH_TOLERANCE``.

    Returns
    -------
    np.ndarray
        Boolean 3D array indicating which grid cells satisfy the match
        predicate.
    """
    if n_f is None:
        n_f = EW_PARAMS["N_F_FIDUCIAL"]
    if m_H_obs is None:
        m_H_obs = EW_PARAMS["M_H_GEV"]
    if tolerance is None:
        tolerance = EW_PARAMS["M_H_MATCH_TOLERANCE"]

    masses = higgs_mass_scan(lambda_uv_range, n_f, g_c_range, lam4_range)
    match = np.zeros_like(masses, dtype=bool)
    for idx, val in np.ndenumerate(masses):
        match[idx] = scalar_rung_quantitative_match(
            val, m_H_obs, tolerance
        )
    return match
