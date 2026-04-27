"""Casini-Huerta log bound on entanglement entropy.

Mirrors `RTCasiniHuertaBounds` Lean theorems
`ch_log_bound_pos_at_log_pos`,
`H_CasiniHuerta_Bound_Valid_witness_saturated`, and the structural
H_CasiniHuerta_Bound_Valid tracked Prop.
"""

from __future__ import annotations

import math


def saturated_ch_entropy(L: float, c_central: float, UV_cutoff: float) -> float:
    """Saturated Casini-Huerta entropy `S(L) = (c/3) log(L/UV)`.

    Mirrors `RTCasiniHuertaBounds.saturatedCHEntropy`. Saturates the CH
    bound with equality.

    Raises:
        ValueError: if `L <= UV_cutoff` or `UV_cutoff <= 0` or `c_central <= 0`.
    """
    if c_central <= 0:
        raise ValueError(f"Central charge must be positive, got c = {c_central}")
    if UV_cutoff <= 0:
        raise ValueError(f"UV cutoff must be positive, got UV = {UV_cutoff}")
    if L <= UV_cutoff:
        raise ValueError(
            f"Region size L must exceed UV cutoff, got L = {L}, UV = {UV_cutoff}"
        )
    return (c_central / 3.0) * math.log(L / UV_cutoff)


def ch_log_bound(L: float, c_central: float, UV_cutoff: float) -> float:
    """Casini-Huerta log bound `(c/3) log(L/UV)`.

    Same numerical value as `saturated_ch_entropy`; named separately to
    distinguish "the bound" from "an entropy realising the bound".
    """
    return saturated_ch_entropy(L, c_central, UV_cutoff)


def ch_bound_holds(
    S_value: float,
    L: float,
    c_central: float,
    UV_cutoff: float,
    tolerance: float = 1e-12,
) -> bool:
    """Check whether a candidate entropy value satisfies the CH bound at L.

    Mirrors the structural condition `S_ent L ≤ (c/3) log(L/UV)` from
    `H_CasiniHuerta_Bound_Valid.ch_bound`.
    """
    bound = ch_log_bound(L, c_central, UV_cutoff)
    return S_value <= bound + tolerance


def central_charge_from_saturation(
    S_value: float,
    L: float,
    UV_cutoff: float,
) -> float:
    """Inverse: given a saturating entropy, recover the central charge.

    `c = 3 * S_value / log(L/UV)`. Useful for cross-checking 2D CFT
    central charges against measured entanglement entropies.

    Raises:
        ValueError: if `L <= UV_cutoff` or `UV_cutoff <= 0`.
    """
    if UV_cutoff <= 0:
        raise ValueError(f"UV cutoff must be positive, got UV = {UV_cutoff}")
    if L <= UV_cutoff:
        raise ValueError(
            f"Region size L must exceed UV cutoff, got L = {L}, UV = {UV_cutoff}"
        )
    return 3.0 * S_value / math.log(L / UV_cutoff)
