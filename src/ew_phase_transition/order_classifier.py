"""First-order vs crossover transition classifier over parameter grids."""

from __future__ import annotations

import numpy as np


def is_first_order_ew(E):
    """First-order EW phase transition iff `E > 0` (LO classifier).

    Lean: EWPhaseTransition.IsFirstOrderEW
    """
    return float(E) > 0.0


def is_crossover_ew(E):
    """Crossover EW phase transition iff `E = 0` (LO classifier).

    Lean: EWPhaseTransition.IsCrossoverEW
    """
    return float(E) == 0.0


def transition_order_grid(E_range, threshold=0.0):
    """Boolean grid: first-order vs crossover over a range of E values.

    Returns array `True` where `E > threshold` (first-order viable region).

    Parameters
    ----------
    E_range : np.ndarray
        Cubic-coefficient values to scan.
    threshold : float
        First-order threshold (default 0.0).

    Returns
    -------
    np.ndarray of bool
        ``True`` for first-order, ``False`` for crossover at each scan point.
    """
    E_arr = np.asarray(E_range, dtype=float)
    return E_arr > threshold
