"""Parameter-grid anomaly hunt for path-b diff invariance at order ``a_4``.

Probes the order-4 anomaly residual on a sweep of curvature inputs
``(R_sq, Ricci_sq, Riemann_sq)`` and species counts ``N_f`` taken from
``DIFF_INVARIANCE_PARAMS['TEST_GRID_*']``.  For the Christensen-Duff
Dirac bundle the residual is at machine precision; for a perturbed
bundle (single coefficient shifted by an arbitrary nonzero ``δ``) the
residual is detectably nonzero — the falsifier.
"""

from __future__ import annotations
import numpy as np
from typing import Dict, Tuple


def _grid_points(low: float, high: float, n_pts: int) -> np.ndarray:
    """Return ``n_pts`` evenly spaced points in ``[low, high]``."""
    return np.linspace(float(low), float(high), int(n_pts))


def parameter_grid_scan_a4(N_f: float,
                             bundle_kind: str = 'dirac',
                             delta: float = 0.0,
                             ) -> Tuple[np.ndarray, np.ndarray, np.ndarray,
                                         np.ndarray]:
    """Scan the order-``a_4`` anomaly residual on a 3D curvature grid.

    Parameters
    ----------
    N_f : float
        Fermion species count.
    bundle_kind : {'dirac', 'perturbed'}
        Which coefficient bundle to scan.
    delta : float
        Perturbation magnitude (only used when ``bundle_kind == 'perturbed'``).

    Returns
    -------
    (R_sq_grid, Ricci_sq_grid, Riemann_sq_grid, residual_grid) : tuple
        4 arrays of shape ``(n_pts,)`` for the three input grids and the
        flattened residual for matched indices.

    Notes
    -----
    The grid is a 1D diagonal sweep through the 3D box rather than a
    full Cartesian product, to keep the test footprint small.
    """
    from src.core.constants import DIFF_INVARIANCE_PARAMS as DI
    from src.diff_invariance.variational_check import (
        EffectiveLagrangianBundle,
        dirac_coefficient_bundle,
        perturbed_coefficient_bundle,
        pathB_residual_at_order,
    )
    n_pts = int(DI['PARAMETER_SCAN_POINTS'])
    R_sq_grid = _grid_points(*DI['TEST_GRID_RICCI_SQ_RANGE'], n_pts)
    Ricci_sq_grid = _grid_points(*DI['TEST_GRID_RICCI_SQ_RANGE'], n_pts)
    Riemann_sq_grid = _grid_points(*DI['TEST_GRID_RIEMANN_SQ_RANGE'], n_pts)

    if bundle_kind == 'dirac':
        bundle: EffectiveLagrangianBundle = dirac_coefficient_bundle(N_f)
    elif bundle_kind == 'perturbed':
        bundle = perturbed_coefficient_bundle(N_f, delta)
    else:
        raise ValueError(
            f"bundle_kind must be 'dirac' or 'perturbed', got {bundle_kind!r}"
        )

    residual = np.empty(n_pts, dtype=float)
    for i in range(n_pts):
        residual[i] = pathB_residual_at_order(
            4, bundle, float(N_f), 0.0,
            float(R_sq_grid[i]),
            float(Ricci_sq_grid[i]),
            float(Riemann_sq_grid[i]),
        )
    return R_sq_grid, Ricci_sq_grid, Riemann_sq_grid, residual


def max_residual_over_grid(N_f: float, bundle_kind: str = 'dirac',
                             delta: float = 0.0) -> float:
    """Maximum absolute order-``a_4`` residual over the parameter grid.

    Returns the worst-case ``|residual|`` across the
    ``DIFF_INVARIANCE_PARAMS['PARAMETER_SCAN_POINTS']`` grid points.
    """
    *_, residual = parameter_grid_scan_a4(N_f, bundle_kind, delta)
    return float(np.max(np.abs(residual)))


def anomaly_hunt_dirac_passes(N_f: float = 24.0) -> bool:
    """Wave 3 correctness-push: the Dirac bundle's order-``a_4``
    residual stays below the path-b tolerance over the entire scan grid.

    For the Christensen-Duff Dirac bundle this is True identically (the
    Wave 2 main basis-change theorem
    ``a4_density_eq_a4_density_in_RC2GB_basis`` is closed-form).
    """
    from src.core.constants import DIFF_INVARIANCE_PARAMS
    tol = float(DIFF_INVARIANCE_PARAMS['PATH_B_RESIDUAL_TOLERANCE'])
    return bool(max_residual_over_grid(N_f, 'dirac') < tol)


def anomaly_hunt_perturbed_fails(N_f: float = 24.0,
                                    delta: float | None = None) -> bool:
    """Falsifier: a perturbed bundle has nonzero anomaly that exceeds
    the path-b tolerance.  Returns ``True`` iff the falsifier is
    correctly detected (the residual exceeds the tolerance at some
    grid point).

    Default ``delta = DIFF_INVARIANCE_PARAMS['ANOMALY_PROBE_OFFSET']``.
    """
    from src.core.constants import DIFF_INVARIANCE_PARAMS as DI
    if delta is None:
        delta = float(DI['ANOMALY_PROBE_OFFSET'])
    tol = float(DI['PATH_B_RESIDUAL_TOLERANCE'])
    return bool(max_residual_over_grid(N_f, 'perturbed', delta) > tol)


def report_anomaly_hunt(N_f: float = 24.0,
                          delta: float | None = None) -> Dict[str, float]:
    """Composite report: Dirac residual, perturbed residual, decision flags.

    Useful for figure generation in Stage 8 (``fig_diff_invariance_order_check``).
    """
    from src.core.constants import DIFF_INVARIANCE_PARAMS as DI
    if delta is None:
        delta = float(DI['ANOMALY_PROBE_OFFSET'])
    return {
        'N_f': float(N_f),
        'delta': float(delta),
        'tolerance': float(DI['PATH_B_RESIDUAL_TOLERANCE']),
        'dirac_max_residual': max_residual_over_grid(N_f, 'dirac'),
        'perturbed_max_residual': max_residual_over_grid(
            N_f, 'perturbed', delta),
        'dirac_passes': bool(anomaly_hunt_dirac_passes(N_f)),
        'perturbed_fails': bool(anomaly_hunt_perturbed_fails(N_f, delta)),
    }
