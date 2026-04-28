"""Wave 6 torsion-amplitude evaluator + parametric scans.

The Hehl-style algebraic Cartan torsion equation ``T = G_N · S`` gives
the scalar-amplitude Wave 6 prediction

    |T_EC|(Λ_UV, N_f, α_EC, n_spin)
        = α_EC · 12π/(N_f · Λ_UV²) · n_spin
        = G_N^emerg(Λ_UV, N_f, α_EC) · n_spin.

This module wraps ``src.core.formulas.torsion_amplitude_ec`` in a
``TorsionPrediction`` dataclass and exposes parameter-grid scans for
the visualisation pipeline (``fig_torsion_obs_bound``).

Lean: ``EinsteinCartanExtension.torsionAmplitude``
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable

import numpy as np

from src.core.constants import EINSTEIN_CARTAN_PARAMS
from src.core.formulas import (
    torsion_amplitude_ec,
    torsion_amplitude_at_cosmological_background,
)


@dataclass(frozen=True)
class TorsionPrediction:
    """One torsion-amplitude prediction at a (Λ_UV, N_f, α_EC, n_spin) point.

    Attributes
    ----------
    lambda_uv_gev : float
        Microscopic UV cutoff (GeV).
    n_f : float
        Number of Dirac-fermion species.
    alpha_ec : float
        Einstein-Cartan / ADW dimensionless coefficient.
    n_spin_gev3 : float
        Background spin density (GeV³).
    amplitude_gev : float
        Predicted ``|T_EC|`` (GeV).
    """

    lambda_uv_gev: float
    n_f: float
    alpha_ec: float
    n_spin_gev3: float
    amplitude_gev: float


def torsion_amplitude_at_point(
    lambda_uv_gev: float,
    n_f: float,
    alpha_ec: float = 1.0,
    n_spin_gev3: float | None = None,
) -> TorsionPrediction:
    """Single-point ``|T_EC|`` evaluation.

    Parameters
    ----------
    lambda_uv_gev : float
        Microscopic UV cutoff (GeV).
    n_f : float
        Dirac-fermion species count.
    alpha_ec : float, optional
        Einstein-Cartan rescaling coefficient (default 1.0 — Sakharov-Adler).
    n_spin_gev3 : float, optional
        Background spin density.  Default = cosmological background
        ``EINSTEIN_CARTAN_PARAMS['COSMOLOGICAL_SPIN_DENSITY_GEV3']``.

    Returns
    -------
    TorsionPrediction
    """
    if n_spin_gev3 is None:
        n_spin_gev3 = EINSTEIN_CARTAN_PARAMS['COSMOLOGICAL_SPIN_DENSITY_GEV3']
    amp = torsion_amplitude_ec(lambda_uv_gev, n_f, alpha_ec, n_spin_gev3)
    return TorsionPrediction(
        lambda_uv_gev=float(lambda_uv_gev),
        n_f=float(n_f),
        alpha_ec=float(alpha_ec),
        n_spin_gev3=float(n_spin_gev3),
        amplitude_gev=float(amp),
    )


def torsion_scan_over_alpha(
    lambda_uv_gev: float,
    n_f: float,
    alpha_values: Iterable[float] | None = None,
    n_spin_gev3: float | None = None,
) -> list[TorsionPrediction]:
    """Scan ``|T_EC|`` over a grid of ``α_EC`` values at fixed (Λ_UV, N_f).

    Defaults to a log-spaced grid from ``ALPHA_EC_NATURAL_MIN`` to
    ``ALPHA_EC_NATURAL_MAX`` (ALPHA_SCAN_POINTS samples).
    """
    if alpha_values is None:
        n_pts = EINSTEIN_CARTAN_PARAMS['ALPHA_SCAN_POINTS']
        a_min = EINSTEIN_CARTAN_PARAMS['ALPHA_EC_NATURAL_MIN']
        a_max = EINSTEIN_CARTAN_PARAMS['ALPHA_EC_NATURAL_MAX']
        alpha_values = np.logspace(
            np.log10(a_min), np.log10(a_max), int(n_pts)
        ).tolist()
    return [
        torsion_amplitude_at_point(lambda_uv_gev, n_f, a, n_spin_gev3)
        for a in alpha_values
    ]


def torsion_scan_over_lambda_uv(
    n_f: float,
    alpha_ec: float = 1.0,
    lambda_uv_values: Iterable[float] | None = None,
    n_spin_gev3: float | None = None,
) -> list[TorsionPrediction]:
    """Scan ``|T_EC|`` over a grid of ``Λ_UV`` values at fixed (N_f, α_EC).

    Defaults to a log-spaced grid from ``LAMBDA_UV_SCAN_MIN_GEV`` to
    ``LAMBDA_UV_SCAN_MAX_GEV`` (LAMBDA_UV_SCAN_POINTS samples).
    """
    if lambda_uv_values is None:
        n_pts = EINSTEIN_CARTAN_PARAMS['LAMBDA_UV_SCAN_POINTS']
        lo = EINSTEIN_CARTAN_PARAMS['LAMBDA_UV_SCAN_MIN_GEV']
        hi = EINSTEIN_CARTAN_PARAMS['LAMBDA_UV_SCAN_MAX_GEV']
        lambda_uv_values = np.logspace(
            np.log10(lo), np.log10(hi), int(n_pts)
        ).tolist()
    return [
        torsion_amplitude_at_point(lam, n_f, alpha_ec, n_spin_gev3)
        for lam in lambda_uv_values
    ]
