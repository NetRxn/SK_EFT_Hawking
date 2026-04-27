"""Hayden-Preskill scrambling-time bound + recovery threshold.

Mirrors `HPCode.scramblingTimeBound`, `HPCode.recoveryPossible`, and
`HPCode.recovery_at_scrambling_bound` from `QECHolographyBridge.lean`.
"""

from __future__ import annotations

import math

from .code_distance import MTCSpectrum, global_dim_sq


def scrambling_time_bound(spectrum: MTCSpectrum) -> float:
    """Hayden-Preskill scrambling-time lower bound `t_scr := log D²`.

    Proxy for `(β/2π) S_BH` after the area law is pulled out.
    Dimensionless (absorbs `β/2π`).

    Mirrors `HPCode.scramblingTimeBound` from the Lean module.
    """
    return math.log(global_dim_sq(spectrum))


def recovery_threshold(
    spectrum: MTCSpectrum,
    encoding_idx: int,
) -> float:
    """Boundary entropy threshold for Hayden-Preskill recovery.

    Defined as `log(d_encode)`, where `d_encode` is the quantum dimension
    of the encoding anyon at index `encoding_idx`.

    Mirrors the recovery-possible def from the Lean module: information
    encoded on `encoding_obj` is recoverable from boundary radiation of
    accumulated entropy `B` precisely when `B ≥ recovery_threshold`.
    """
    if not 0 <= encoding_idx < len(spectrum.quantum_dims):
        raise IndexError(
            f"encoding_idx {encoding_idx} out of range for "
            f"{spectrum.name} spectrum of size {len(spectrum.quantum_dims)}"
        )
    return math.log(spectrum.quantum_dims[encoding_idx])


def recovery_possible_at_scrambling_bound(
    spectrum: MTCSpectrum,
    encoding_idx: int,
) -> bool:
    """Hayden-Preskill structural recovery at scrambling-time bound.

    Returns `True` iff the recovery threshold is at most the
    scrambling-time bound: `log d_encode ≤ log D²`.

    The Lean theorem `recovery_at_scrambling_bound` proves this is
    always `True` (over any HPCode) — this Python mirror returns the
    boolean check for numerical anchoring.
    """
    threshold = recovery_threshold(spectrum, encoding_idx)
    bound = scrambling_time_bound(spectrum)
    return threshold <= bound + 1e-12  # numerical tolerance
