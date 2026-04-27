"""Bridge predicate evaluation: chirality-wall × phase-transition →
EWBG verdict.

Mirrors the Lean predicates from
``EWBaryogenesisChiralityWall.lean``. The full SM under the KLRS
hypothesis is doubly forbidden: SM-no-ν_R fails the chirality-wall
condition; SM+3ν_R cracks the wall but fails the transition condition.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from src.core.constants import EWBG_PARAMS
from src.core.formulas import (
    chirality_wall_blocks_ewbg as _chirality_wall_blocks_ewbg,
    ewbg_viable as _ewbg_viable,
)


def wall_intact(z16_anomaly):
    """Chirality wall is intact iff Z₁₆ anomaly is nonzero (mod 16).

    Lean: ``EWBaryogenesisChiralityWall.WallIntact``.
    """
    return _chirality_wall_blocks_ewbg(z16_anomaly)


def wall_cracked(z16_anomaly):
    """Chirality wall cracks iff Z₁₆ anomaly cancels (mod 16).

    Lean: ``EWBaryogenesisChiralityWall.WallCracked``.
    """
    return not _chirality_wall_blocks_ewbg(z16_anomaly)


def sm_no_nu_R_z16_anomaly():
    """SM-no-ν_R Z₁₆ anomaly: 3 × 15 = 45 ≡ 13 (mod 16).

    Lean: bridge to ``Z16AnomalyComputation.three_gen_anomalous`` +
    ``three_gen_mod16``.
    """
    return EWBG_PARAMS['SM_Z16_ANOMALY_NO_NU_R']  # = 13 (= 45 mod 16)


def sm_with_3nu_R_z16_anomaly():
    """SM + 3 ν_R Z₁₆ anomaly: 3 × 16 = 48 ≡ 0 (mod 16). Wall cracks.

    Lean: bridge to ``Z16AnomalyComputation.sm_anomaly_with_nu_R``
    (single-gen) + additivity over generations.
    """
    return EWBG_PARAMS['SM_Z16_ANOMALY_WITH_3NU_R']  # = 0


def ewbg_viable(z16_anomaly, E, mu_sq, lam, c_T, threshold=None):
    """Compound EWBG viability predicate (re-export of formulas.py).

    Lean: ``EWBaryogenesisChiralityWall.EWBGViable``.
    """
    return _ewbg_viable(z16_anomaly, E, mu_sq, lam, c_T, threshold=threshold)


@dataclass(frozen=True)
class SMEWBGVerdict:
    """Structured SM EWBG verdict bundling the two failure modes."""

    sm_no_nu_R_wall_intact: bool
    sm_no_nu_R_ewbg_blocked: bool
    sm_with_3nu_R_wall_cracks: bool
    sm_with_3nu_R_ewbg_under_klrs: bool
    klrs_overshoot_ratio: float

    def doubly_forbidden(self) -> bool:
        return self.sm_no_nu_R_ewbg_blocked and (not self.sm_with_3nu_R_ewbg_under_klrs)


def sm_ewbg_verdict(
    sm_full_is_crossover: bool = True,
    threshold: Optional[float] = None,
) -> SMEWBGVerdict:
    """Compute the full SM EWBG verdict under the KLRS hypothesis.

    Parameters
    ----------
    sm_full_is_crossover : bool, default True
        Whether the full SM EW transition is crossover (KLRS hypothesis,
        m_H = 125.20 GeV > KLRS threshold 72.4 GeV).
    threshold : float, optional
        Sphaleron-decoupling threshold (default 1.0).

    Returns
    -------
    SMEWBGVerdict
        Structured verdict with both failure modes evaluated.
    """
    a_no_nu = sm_no_nu_R_z16_anomaly()
    a_with_nu = sm_with_3nu_R_z16_anomaly()

    # SM-no-ν_R: wall intact independently of transition
    sm_no_nu_R_wall = wall_intact(a_no_nu)
    sm_no_nu_R_ewbg_ok = (not sm_no_nu_R_wall)  # never True for SM-no-ν_R

    # SM+3ν_R: wall cracks; success then depends on transition order
    sm_with_3nu_R_wall = wall_cracked(a_with_nu)
    if sm_full_is_crossover:
        sm_with_3nu_R_ewbg_ok = False  # crossover blocks regardless of wall
    else:
        # First-order at LO with smBenchmarkParams (E = 0.01 > 0):
        # ewbg viability also depends on strength threshold; treat as True
        # only at the strict-LO benchmark, NOT under H_KLRS
        sm_with_3nu_R_ewbg_ok = sm_with_3nu_R_wall

    return SMEWBGVerdict(
        sm_no_nu_R_wall_intact=sm_no_nu_R_wall,
        sm_no_nu_R_ewbg_blocked=(not sm_no_nu_R_ewbg_ok),
        sm_with_3nu_R_wall_cracks=sm_with_3nu_R_wall,
        sm_with_3nu_R_ewbg_under_klrs=sm_with_3nu_R_ewbg_ok,
        klrs_overshoot_ratio=EWBG_PARAMS['M_H_OVERSHOOT_RATIO'],
    )
