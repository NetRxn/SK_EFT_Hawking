"""Linearized Einstein tensor in momentum space (de Donder gauge).

Numerical mirror of ``lean/SKEFTHawking/LinearizedEFE.lean`` Sections
1-3. All operations work on 4×4 numpy arrays representing components
on a single momentum mode k_μ.

Conventions
-----------
- Minkowski signature: η_μν = diag(-1, +1, +1, +1).
- Natural units: ℏ = c = 1.
- Momentum-space convention: k² = η^αβ k_α k_β = -k₀² + k₁² + k₂² + k₃².
- De Donder gauge: k^μ h̄_μν = 0 (raised index via Minkowski).
"""

from __future__ import annotations

import numpy as np

from src.core.formulas import (
    linearized_einstein_de_donder,
    trace_reverse_perturbation,
)


def minkowski_metric() -> np.ndarray:
    """The Minkowski metric η_μν = diag(-1, +1, +1, +1) as a 4×4 array.

    Lean: LinearizedEFE.η, η_zero_zero, η_spatial_diag.
    """
    return np.diag([-1.0, 1.0, 1.0, 1.0])


def minkowski_trace(h_munu: np.ndarray) -> float:
    """Minkowski trace ``η^μν h_μν = -h₀₀ + h₁₁ + h₂₂ + h₃₃``.

    Lean: LinearizedEFE.trace_h_eq.

    Parameters
    ----------
    h_munu : np.ndarray, shape (4, 4)
        Symmetric metric perturbation.

    Returns
    -------
    float
        η-trace of ``h_munu``.
    """
    h = np.asarray(h_munu, dtype=float)
    if h.shape != (4, 4):
        raise ValueError("h_munu must be shape (4, 4).")
    eta = minkowski_metric()
    return float(np.einsum("ab,ab->", eta, h))


def trace_reversed_perturbation_array(h_munu: np.ndarray) -> np.ndarray:
    """Trace-reversed perturbation ``h̄_μν = h_μν - (1/2) η_μν tr(h)``.

    Wraps the canonical implementation in ``src.core.formulas`` so the
    numerical layer matches the Lean ``LinearizedEFE.trace_reverse``
    definition exactly. Trace-reversal is involutive in 4D.

    Lean: LinearizedEFE.trace_reverse, trace_reverse_involutive.

    Parameters
    ----------
    h_munu : np.ndarray, shape (4, 4)
        Metric perturbation (symmetric expected).

    Returns
    -------
    np.ndarray, shape (4, 4)
        Trace-reversed perturbation.
    """
    return trace_reverse_perturbation(h_munu)


def linearized_einstein_de_donder_array(k_sq: float, h_bar_munu: np.ndarray) -> np.ndarray:
    """Linearized Einstein tensor in momentum space, de Donder gauge.

    ``G^(1)_μν(k) = -(1/2) k² h̄_μν``

    Wraps ``src.core.formulas.linearized_einstein_de_donder`` for the
    package-level API.

    Lean: LinearizedEFE.linEinsteinDeDonder.

    Parameters
    ----------
    k_sq : float
        Minkowski-squared momentum.
    h_bar_munu : np.ndarray, shape (4, 4)
        Trace-reversed metric perturbation.

    Returns
    -------
    np.ndarray, shape (4, 4)
        Linearized Einstein tensor.
    """
    return linearized_einstein_de_donder(k_sq, h_bar_munu)


def deDonder_gauge_residual(k_lower: np.ndarray, h_bar_munu: np.ndarray) -> np.ndarray:
    """De Donder gauge residual ``r_ν = k^μ h̄_μν``.

    Returns the 4-vector of gauge residuals; the de Donder gauge
    condition is ``r_ν = 0`` for all ν. Used to verify that a chosen
    perturbation actually sits in de Donder gauge before applying the
    simplified G^(1) formula.

    Parameters
    ----------
    k_lower : np.ndarray, shape (4,)
        Lower-index 4-momentum k_μ.
    h_bar_munu : np.ndarray, shape (4, 4)
        Trace-reversed metric perturbation.

    Returns
    -------
    np.ndarray, shape (4,)
        Gauge residual; identically zero in de Donder gauge.
    """
    k = np.asarray(k_lower, dtype=float)
    h = np.asarray(h_bar_munu, dtype=float)
    if k.shape != (4,):
        raise ValueError("k_lower must be shape (4,).")
    if h.shape != (4, 4):
        raise ValueError("h_bar_munu must be shape (4, 4).")
    eta = minkowski_metric()
    # Raise k via η: k^μ = η^μα k_α
    k_upper = eta @ k
    return k_upper @ h
