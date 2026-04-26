"""GW170817 constraint check for vestigial-second-sound graviton ID.

Encodes the Wave 2 falsification result: the natural χ_vest range
[0.1, 10] gives Δc/c ∈ [-0.68, +2.16], failing the GW170817 cap
(3e-15) by 14+ orders of magnitude.

Lean cross-reference: ``GravitationalWaves.LigoSatisfied``,
``GravitationalWaves.natural_lower_violates_ligo``,
``GravitationalWaves.natural_upper_violates_ligo``,
``GravitationalWaves.vestigial_natural_range_violates_ligo``.
"""

from __future__ import annotations

from dataclasses import dataclass

from src.core.constants import GW_PARAMS
from src.core.formulas import (
    c_GW_deviation_from_c,
    ligo_constraint_check,
)


@dataclass
class GW170817Verdict:
    """Structured outcome of a GW170817 compatibility check."""

    chi_vest: float
    deviation: float
    ligo_satisfied: bool
    cap: float
    violation_factor: float

    def summary(self) -> str:
        verdict = "OK" if self.ligo_satisfied else "FAIL"
        return (
            f"χ_vest={self.chi_vest:.6g}: Δc/c={self.deviation:.3e}, "
            f"|Δc/c|/cap={self.violation_factor:.2e} [{verdict}]"
        )


def ligo_compatibility_check(chi_vest: float) -> GW170817Verdict:
    """Evaluate GW170817 compatibility at a given χ_vest.

    Parameters
    ----------
    chi_vest : float
        Vestigial-phase metric-channel susceptibility (dimensionless).

    Returns
    -------
    GW170817Verdict
        Structured result.
    """
    deviation = c_GW_deviation_from_c(chi_vest)
    cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]
    satisfied = ligo_constraint_check(deviation, cap)
    return GW170817Verdict(
        chi_vest=float(chi_vest),
        deviation=float(deviation),
        ligo_satisfied=bool(satisfied),
        cap=float(cap),
        violation_factor=float(abs(deviation) / cap) if cap > 0 else float("inf"),
    )


def chi_vest_window_compatible_with_ligo(
    cap: float | None = None,
) -> tuple[float, float]:
    """Closed-form GW170817-compatible χ_vest window.

    Returns ``[(1 - cap)², (1 + cap)²]``: the window of χ_vest values
    inside which the LIGO bound is satisfied.

    Parameters
    ----------
    cap : float, optional
        Symmetric two-sided cap. Default: GW170817 cap from constants.

    Returns
    -------
    tuple
        (chi_lo, chi_hi) — the GW170817-compatible window.
    """
    tol = cap if cap is not None else GW_PARAMS["C_GW_TWO_SIDED_CAP"]
    return ((1.0 - tol) ** 2, (1.0 + tol) ** 2)


def ligo_falsification_summary() -> dict:
    """Compute the Wave 2 main physics finding: natural-range vs GW170817.

    Returns
    -------
    dict
        Keys: chi_vest_lower, chi_vest_upper, delta_lower, delta_upper,
        ligo_compatible_window, violation_ratio_lower, violation_ratio_upper,
        natural_range_compatible (False).
    """
    chi_lo = GW_PARAMS["CHI_VEST_NATURAL_LOWER"]
    chi_hi = GW_PARAMS["CHI_VEST_NATURAL_UPPER"]
    cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]

    verdict_lo = ligo_compatibility_check(chi_lo)
    verdict_hi = ligo_compatibility_check(chi_hi)

    natural_compatible = bool(verdict_lo.ligo_satisfied and verdict_hi.ligo_satisfied)

    return {
        "chi_vest_lower": float(chi_lo),
        "chi_vest_upper": float(chi_hi),
        "delta_lower": float(verdict_lo.deviation),
        "delta_upper": float(verdict_hi.deviation),
        "cap": float(cap),
        "ligo_compatible_window": chi_vest_window_compatible_with_ligo(cap),
        "violation_ratio_lower": float(verdict_lo.violation_factor),
        "violation_ratio_upper": float(verdict_hi.violation_factor),
        "natural_range_compatible": natural_compatible,
    }
