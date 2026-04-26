"""MTC state counting at the horizon — Verlinde-formula numerics.

Wraps ``src.core.formulas.verlinde_dim_horizon`` with concrete SU(2)_k
modular-data builders and per-MTC global-dimension lookups.

Lean: `BHEntropyMicroscopic.verlindeEntropy_SU2k` (opaque at Lean level;
        defined numerically here for cross-validation).
Source: Verlinde, Nucl. Phys. B 300, 360 (1988); Kaul SIGMA 8, 005 (2012),
        arXiv:1201.6102 §3-4.
"""

from __future__ import annotations

import numpy as np

from src.core.constants import BH_ENTROPY_PARAMS
from src.core.formulas import verlinde_dim_horizon


def su2k_quantum_dimensions(k: int) -> np.ndarray:
    """Quantum dimensions d_j for SU(2)_k simple objects j = 0, ..., k.

        d_j = sin((j+1) π/(k+2)) / sin(π/(k+2))    = [j+1]_q

    where labels j ∈ {0, 1, ..., k} correspond to spin j/2 simple objects.

    Parameters
    ----------
    k : int
        Chern-Simons level (k ≥ 1).

    Returns
    -------
    np.ndarray
        Array of length k+1 with d_j entries.
    """
    if k < 1:
        raise ValueError(f"SU(2)_k requires k >= 1 (got {k})")
    j = np.arange(k + 1)
    denom = np.sin(np.pi / (k + 2))
    numer = np.sin((j + 1) * np.pi / (k + 2))
    return numer / denom


def su2k_S_matrix(k: int) -> np.ndarray:
    """Modular S-matrix for SU(2)_k.

        S_{ij} = sqrt(2/(k+2)) · sin((i+1)(j+1)π/(k+2))

    where i, j ∈ {0, ..., k}. This is the standard normalization yielding
    a unitary (real symmetric) S-matrix.

    Parameters
    ----------
    k : int
        Chern-Simons level.

    Returns
    -------
    np.ndarray
        (k+1) × (k+1) S-matrix.
    """
    if k < 1:
        raise ValueError(f"SU(2)_k requires k >= 1 (got {k})")
    n = k + 1
    i, j = np.meshgrid(np.arange(n), np.arange(n), indexing="ij")
    pref = np.sqrt(2.0 / (k + 2))
    return pref * np.sin((i + 1) * (j + 1) * np.pi / (k + 2))


def verlinde_dim_at_horizon(k: int, p: int, labels) -> float:
    """Verlinde-counted Hilbert-space dim at horizon S² with `p` punctures.

        dim H_{S²; a_1, ..., a_p} = Σ_c [ Π_i S_{a_i,c} ] / S_{0,c}^{p-2}

    Parameters
    ----------
    k : int
        SU(2)_k level.
    p : int
        Number of punctures.
    labels : sequence of int
        Length-p sequence of simple-object indices.

    Returns
    -------
    float
        Verlinde state count at the horizon.
    """
    S = su2k_S_matrix(k)
    return float(verlinde_dim_horizon(p, S, list(labels), vacuum_index=0))


def mtc_global_dim_squared(mtc_name: str) -> float:
    """Total quantum dimension squared D² for a named MTC.

    Parameters
    ----------
    mtc_name : str
        One of {'Fibonacci', 'Ising', 'ToricCode', 'DS3'}.

    Returns
    -------
    float
        D² = Σ_a d_a².
    """
    table = {
        "Fibonacci": BH_ENTROPY_PARAMS["FIBONACCI_GLOBAL_DIM_SQ"],
        "Ising": BH_ENTROPY_PARAMS["ISING_GLOBAL_DIM_SQ"],
        "ToricCode": BH_ENTROPY_PARAMS["TORIC_CODE_GLOBAL_DIM_SQ"],
        "DS3": BH_ENTROPY_PARAMS["DS3_GLOBAL_DIM_SQ"],
    }
    if mtc_name not in table:
        raise KeyError(
            f"Unknown MTC: {mtc_name!r}; expected one of {list(table)}"
        )
    return float(table[mtc_name])
