"""Trace-level EFE residual evaluator at representative backgrounds.

Mirrors ``efeResidualTrace`` and the at-Dirac-balanced calibration
theorem in ``lean/SKEFTHawking/NonlinearEFE.lean``.  Numerical
companion: closes the Lean ↔ Python bridge for
``efeResidualTrace_at_dirac_calibration_vanishes`` and the
linear-in-(α-1) deviation form.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable

import numpy as np


@dataclass(frozen=True)
class BackgroundCurvature:
    """Representative-background curvature-invariant tuple
    ``(R, R², R_μν², R_μνρσ²)``.

    Each canonical background contributes a different tuple; the
    trace-level EFE residual must vanish on all of them at the
    Dirac-balanced configuration (Wave 4 main result).

    Mirrors the Lean module's representative-background list
    (Wave-4 constants ``BENCHMARK_BACKGROUNDS``).
    """

    name: str
    R: float
    R_sq: float
    Ricci_sq: float
    Riemann_sq: float


def schwarzschild_horizon_background() -> BackgroundCurvature:
    """Schwarzschild vacuum at the horizon.

    Vacuum: R = R_μν = 0; only Riemann² ≠ 0.  Kretschmann scalar at
    horizon: K = R_μνρσ R^μνρσ = 12 (GM)² / r⁶ → 3 at r = 2GM.
    Reference: Wald 1984 §6.1.
    """
    return BackgroundCurvature(
        name="Schwarzschild_horizon",
        R=0.0,
        R_sq=0.0,
        Ricci_sq=0.0,
        Riemann_sq=3.0,
    )


def de_sitter_background() -> BackgroundCurvature:
    """de Sitter spacetime at unit Hubble rate H = 1.

    All four invariants non-zero: R = 12, R² = 144, R_μν² = 36,
    R_μνρσ² = 24.
    Reference: Wald §5.2; see HEAT_KERNEL deep research notes.
    """
    return BackgroundCurvature(
        name="de_Sitter_H1",
        R=12.0,
        R_sq=144.0,
        Ricci_sq=36.0,
        Riemann_sq=24.0,
    )


def flrw_radiation_background() -> BackgroundCurvature:
    """FLRW radiation cosmology at unit Hubble rate H = 1.

    Traceless stress-energy: R = 0, but R_μν² = R_μνρσ² = 12 from the
    Hubble-rate scaling of the radiation-dominated Friedmann equations.
    """
    return BackgroundCurvature(
        name="FLRW_radiation_H1",
        R=0.0,
        R_sq=0.0,
        Ricci_sq=12.0,
        Riemann_sq=12.0,
    )


def efe_residual_at_background(
    bg: BackgroundCurvature,
    G_N: float,
    rho_ADW: float,
    alpha_ADW: float,
) -> float:
    """Trace-level EFE residual at a given representative background.

    Wraps ``formulas.efe_residual_trace`` but accepts a
    ``BackgroundCurvature`` for documentation / scan loops.  The
    background data does not enter the residual at this order (the
    residual is the deviation from the calibrated configuration);
    higher-curvature corrections are the
    ``higher_curvature_correction_at_background`` channel, separately.

    Lean: NonlinearEFE.efeResidualTrace
    """
    from src.core.formulas import efe_residual_trace
    _ = bg  # background is a documentation/scan accessor at this order
    return efe_residual_trace(G_N, rho_ADW, alpha_ADW)


def efe_residual_scan_over_alpha(
    G_N: float,
    rho_ADW: float,
    alpha_values: Iterable[float],
) -> list[tuple[float, float]]:
    """Scan the trace-level EFE residual over a list of α_ADW values.

    Returns a list of ``(α_ADW, residual)`` pairs.  Demonstrates the
    linearity of the residual in (α - 1) by hand for figure / table
    consumption.

    Lean: NonlinearEFE.efeResidualTrace_eq_zero_iff_alpha_unity
    """
    from src.core.formulas import efe_residual_trace
    return [
        (float(a), float(efe_residual_trace(G_N, rho_ADW, float(a))))
        for a in alpha_values
    ]


def efe_residual_at_dirac_balanced(
    Lambda_UV: float,
    N_f: float,
    rho_ADW: float,
    alpha_ADW: float = 1.0,
) -> float:
    """Trace-level EFE residual at the Dirac-balanced calibration.

    At α_ADW = 1, the residual is identically zero; for α_ADW ≠ 1,
    the residual scales as 8π · G_N_emerg · ρ_ADW · (α-1).

    Lean: NonlinearEFE.efeResidualTrace_at_dirac_calibration_vanishes
    """
    from src.core.formulas import (
        efe_residual_trace,
        G_N_from_seeley_dewitt,
    )
    G_N = G_N_from_seeley_dewitt(Lambda_UV, N_f) * float(alpha_ADW)
    return efe_residual_trace(G_N, rho_ADW, alpha_ADW)


def alpha_log_scan(n_points: int = 21,
                    alpha_min: float = 0.1,
                    alpha_max: float = 10.0) -> np.ndarray:
    """Log-spaced α_ADW grid for parameter scans.  Default range
    ``[0.1, 10.0]`` covers the natural Vergeles band."""
    return np.logspace(
        np.log10(alpha_min), np.log10(alpha_max), int(n_points)
    )
