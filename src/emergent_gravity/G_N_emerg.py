"""Microscopic G_N parameter scan.

Phase 6a Wave 1 correctness-push numerics. Computes
``G_N^emerg(Λ_UV, N_f, α_ADW) = α_ADW · 12π / (N_f · Λ_UV²)`` over a
parameter grid and reports where the prediction matches the observed
G_N within tolerance (Lean: ``LinearizedEFE.G_N_emerg_match_locus``).

All formulas import from ``src.core.formulas``.
"""

from __future__ import annotations

import numpy as np

from src.core.constants import GRAV_PARAMS
from src.core.formulas import (
    G_N_emergent,
    G_N_emergent_at_coupling,
    G_N_emergent_matches_observed,
    alpha_ADW_linear_ansatz,
)


def G_N_emerg_grid(
    lambda_uv_range: np.ndarray,
    n_f: float | int | None = None,
    alpha_adw_range: np.ndarray | None = None,
) -> np.ndarray:
    """Compute G_N^emerg over a 2D ``(Λ_UV, α_ADW)`` grid at fixed N_f.

    Returns a 2D array indexed by (Λ_UV, α_ADW).

    Parameters
    ----------
    lambda_uv_range : np.ndarray
        UV cutoff values in GeV.
    n_f : int or float, optional
        Weyl species count. Defaults to ``GRAV_PARAMS['N_F_DEFAULT']``.
    alpha_adw_range : np.ndarray, optional
        ADW coefficient values. Defaults to ``[1.0]`` (Sakharov-Adler).

    Returns
    -------
    np.ndarray
        G_N^emerg in GeV⁻², shape (len(lambda_uv_range), len(alpha_adw_range)).
    """
    if n_f is None:
        n_f = GRAV_PARAMS["N_F_DEFAULT"]
    if alpha_adw_range is None:
        alpha_adw_range = np.array([GRAV_PARAMS["ALPHA_ADW_SAKHAROV_DEFAULT"]])

    lam = np.asarray(lambda_uv_range, dtype=float)
    alpha = np.asarray(alpha_adw_range, dtype=float)

    grid = np.zeros((len(lam), len(alpha)))
    for i, lam_i in enumerate(lam):
        for j, alpha_j in enumerate(alpha):
            grid[i, j] = G_N_emergent(lam_i, n_f, alpha_j)
    return grid


def G_N_emerg_match_grid(
    lambda_uv_range: np.ndarray,
    n_f: float | int | None = None,
    alpha_adw_range: np.ndarray | None = None,
    g_n_obs: float | None = None,
    tolerance: float | None = None,
) -> np.ndarray:
    """Boolean grid: where does ``G_N^emerg`` match the observed value?

    Cell ``(i, j)`` is True iff ``|G_N^emerg − G_N^obs| / G_N^obs <
    tolerance`` at ``(lambda_uv_range[i], alpha_adw_range[j])``.

    Lean: ``LinearizedEFE.G_N_emerg_match_locus``.

    Parameters
    ----------
    lambda_uv_range : np.ndarray
        UV cutoff scan, in GeV.
    n_f : int or float, optional
        Defaults to ``GRAV_PARAMS['N_F_DEFAULT']``.
    alpha_adw_range : np.ndarray, optional
        Defaults to ``[1.0]``.
    g_n_obs : float, optional
        Observed G_N in GeV⁻²; defaults to ``GRAV_PARAMS['G_N_OBS_GEV_M2']``.
    tolerance : float, optional
        Fractional tolerance; defaults to ``GRAV_PARAMS['G_N_MATCH_TOLERANCE']``.

    Returns
    -------
    np.ndarray
        Boolean array of matches.
    """
    if n_f is None:
        n_f = GRAV_PARAMS["N_F_DEFAULT"]
    if alpha_adw_range is None:
        alpha_adw_range = np.array([GRAV_PARAMS["ALPHA_ADW_SAKHAROV_DEFAULT"]])
    if g_n_obs is None:
        g_n_obs = GRAV_PARAMS["G_N_OBS_GEV_M2"]
    if tolerance is None:
        tolerance = GRAV_PARAMS["G_N_MATCH_TOLERANCE"]

    lam = np.asarray(lambda_uv_range, dtype=float)
    alpha = np.asarray(alpha_adw_range, dtype=float)

    match = np.zeros((len(lam), len(alpha)), dtype=bool)
    for i, lam_i in enumerate(lam):
        for j, alpha_j in enumerate(alpha):
            match[i, j] = G_N_emergent_matches_observed(
                lam_i, n_f, alpha_j, g_n_obs, tolerance
            )
    return match


def G_N_emerg_match_locus_lambda(
    n_f: float | int,
    alpha_adw: float,
    g_n_obs: float | None = None,
) -> float:
    """Closed-form match locus: ``Λ = √(α_ADW · 12π / (N_f · G_N^obs))``.

    Returns the Λ_UV at which ``G_N^emerg(Λ, N_f, α_ADW) = G_N^obs``
    exactly. This is the algebraic locus from
    ``LinearizedEFE.G_N_emerg_match_locus``: Λ² = α_ADW · 12π / (N_f · G_N^obs).

    Parameters
    ----------
    n_f : int or float
        Weyl species count.
    alpha_adw : float
        ADW microscopic coefficient.
    g_n_obs : float, optional
        Observed G_N in GeV⁻²; defaults to ``GRAV_PARAMS['G_N_OBS_GEV_M2']``.

    Returns
    -------
    float
        Λ_UV in GeV at which the exact match holds.
    """
    if g_n_obs is None:
        g_n_obs = GRAV_PARAMS["G_N_OBS_GEV_M2"]
    if n_f <= 0 or alpha_adw <= 0 or g_n_obs <= 0:
        raise ValueError("n_f, alpha_adw, and g_n_obs must be positive.")
    lam_sq = alpha_adw * 12.0 * np.pi / (n_f * g_n_obs)
    return float(np.sqrt(lam_sq))


def G_N_emerg_planck_anchor_alpha(n_f: float | int) -> float:
    """At ``Λ = M_P^obs``, the matching α_ADW is ``α* = N_f / (12π)``.

    This follows from ``LinearizedEFE.G_N_emerg_match_at_planck_anchor``:
    at the Planck anchor the match condition reduces to
    ``α_ADW · 12π = N_f``.

    Parameters
    ----------
    n_f : int or float
        Weyl species count.

    Returns
    -------
    float
        ``α* = N_f / (12π)`` — the matching α_ADW at the Planck anchor.
    """
    if n_f <= 0:
        raise ValueError("n_f must be positive.")
    return float(n_f / (12.0 * np.pi))


def G_N_emerg_at_coupling_grid(
    lambda_uv_range: np.ndarray,
    n_f: float | int | None = None,
    g_over_g_c_range: np.ndarray | None = None,
) -> np.ndarray:
    """Compute G_N^emerg over (Λ_UV, G/G_c) using the linear-ansatz α_ADW.

    Lean: ``LinearizedEFE.G_N_emerg_at_coupling`` with
    ``alphaADW_linear``. At the natural-anchor G/G_c = 2 the ansatz
    gives α = 1/2.

    Parameters
    ----------
    lambda_uv_range : np.ndarray
        UV cutoff scan (GeV).
    n_f : float, optional
        Weyl species count; defaults to ``GRAV_PARAMS['N_F_DEFAULT']``.
    g_over_g_c_range : np.ndarray, optional
        Scan over G/G_c ratios. Must be > 1. Defaults to ``[2.0]``.

    Returns
    -------
    np.ndarray, shape (len(lambda_uv_range), len(g_over_g_c_range))
        G_N^emerg in GeV⁻² under the linear ansatz.
    """
    if n_f is None:
        n_f = GRAV_PARAMS["N_F_DEFAULT"]
    if g_over_g_c_range is None:
        g_over_g_c_range = np.array([2.0])

    lam = np.asarray(lambda_uv_range, dtype=float)
    g_over_gc = np.asarray(g_over_g_c_range, dtype=float)

    grid = np.zeros((len(lam), len(g_over_gc)))
    for i, lam_i in enumerate(lam):
        for j, x_j in enumerate(g_over_gc):
            grid[i, j] = G_N_emergent_at_coupling(lam_i, n_f, x_j)
    return grid


def natural_parameter_grid(
    n_lambda: int = 60,
    n_alpha: int = 50,
    n_f: float | int | None = None,
) -> dict:
    """Build the standard ``(Λ_UV, α_ADW)`` scan grid for Phase 6a Wave 1.

    Λ_UV: log-spaced over [LAMBDA_UV_GEV_LOWER, LAMBDA_UV_GEV_UPPER].
    α_ADW: log-spaced over [ALPHA_ADW_LOWER, ALPHA_ADW_UPPER].

    Parameters
    ----------
    n_lambda : int, default=60
        Number of Λ_UV grid points.
    n_alpha : int, default=50
        Number of α_ADW grid points.
    n_f : int, optional
        Defaults to ``GRAV_PARAMS['N_F_DEFAULT']``.

    Returns
    -------
    dict
        With keys ``lambda_uv``, ``alpha_adw``, ``g_n_grid``,
        ``match_grid``, ``locus_lambda``, ``planck_alpha``, ``n_f``.
    """
    if n_f is None:
        n_f = GRAV_PARAMS["N_F_DEFAULT"]

    lam = np.logspace(
        np.log10(GRAV_PARAMS["LAMBDA_UV_GEV_LOWER"]),
        np.log10(GRAV_PARAMS["LAMBDA_UV_GEV_UPPER"]),
        n_lambda,
    )
    alpha = np.logspace(
        np.log10(GRAV_PARAMS["ALPHA_ADW_LOWER"]),
        np.log10(GRAV_PARAMS["ALPHA_ADW_UPPER"]),
        n_alpha,
    )

    g_n_grid = G_N_emerg_grid(lam, n_f, alpha)
    match_grid = G_N_emerg_match_grid(lam, n_f, alpha)
    locus_lambda = np.array(
        [G_N_emerg_match_locus_lambda(n_f, a) for a in alpha]
    )
    planck_alpha = G_N_emerg_planck_anchor_alpha(n_f)

    return {
        "lambda_uv": lam,
        "alpha_adw": alpha,
        "g_n_grid": g_n_grid,
        "match_grid": match_grid,
        "locus_lambda": locus_lambda,
        "planck_alpha": planck_alpha,
        "n_f": n_f,
    }
