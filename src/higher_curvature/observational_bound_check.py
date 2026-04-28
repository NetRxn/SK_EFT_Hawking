"""Observational-bound check (correctness-push) for Wave 2.

Compares Wave 1 microscopic Dirac a_4 coefficient predictions to the
LIGO / Eöt-Wash short-range-gravity / Hulse-Taylor binary-pulsar /
Cassini observational ceilings on dimensionless higher-curvature
couplings.

Mirrors Lean theorem ``higher_curvature_below_pulsar_bound``.

Result: at SM-relevant fermion counts (24 ≤ N_f ≤ 27), the largest
predicted a_4 coefficient is O(10⁻³), some 62 orders of magnitude
below the tightest pulsar-bound ceiling 10⁵⁹.  No tension with
observation.
"""

from __future__ import annotations
from typing import Dict


def _load_hc_obs_bounds() -> Dict[str, float]:
    """Load the four canonical observational ceilings from the canonical
    source (`HIGHER_CURVATURE_PARAMS` in `src.core.constants`).

    Per Pipeline Invariant 2, physical-constant values live in
    `src/core/constants.py`. This helper exposes them under
    project-internal short keys for downstream callers.

    Provenance for each value lives in `PARAMETER_PROVENANCE` (in
    `src/core/provenance.py`) keyed by the same `HC_BOUND_*` names.
    """
    from src.core.constants import HIGHER_CURVATURE_PARAMS as P
    return {
        'LIGO_C_sq':    float(P['HC_BOUND_LIGO_C_SQ']),
        'SRG_R_sq':     float(P['HC_BOUND_SRG_R_SQ']),
        'pulsar_C_sq':  float(P['HC_BOUND_PULSAR_C_SQ']),
        'cassini_C_sq': float(P['HC_BOUND_CASSINI_C_SQ']),
    }


HC_OBS_BOUNDS: Dict[str, float] = _load_hc_obs_bounds()


def largest_predicted_coefficient(N_f: float) -> float:
    """Largest absolute Wave 1 a_4 coefficient at fermion count N_f.

    For the Christensen-Duff Dirac a_4, the magnitudes are (per (4π)²):
        |c_R|       = N_f · 5/(12·180)  = N_f / 432
        |c_Ricci|   = N_f · 7/(12·180)  = 7 N_f / 2160
        |c_Riemann| = N_f · 12/(12·180) = N_f / 180  ← largest

    So the Riemann² term dominates; this returns its magnitude.
    """
    from src.core.formulas import higher_curvature_Riemann_sq_coefficient
    return abs(higher_curvature_Riemann_sq_coefficient(N_f))


def predictions_below_bound(N_f: float, bound: float) -> bool:
    """All three Wave 1 a_4 coefficients have |c| < bound at N_f.

    Mirrors Lean theorem ``higher_curvature_below_pulsar_bound`` (with
    the bound parameter externalized).
    """
    from src.core.formulas import (
        higher_curvature_R_sq_coefficient,
        higher_curvature_Ricci_sq_coefficient,
        higher_curvature_Riemann_sq_coefficient,
    )
    return (abs(higher_curvature_R_sq_coefficient(N_f)) < float(bound)
            and abs(higher_curvature_Ricci_sq_coefficient(N_f)) < float(bound)
            and abs(higher_curvature_Riemann_sq_coefficient(N_f))
                < float(bound))


def pulsar_correctness_push_passes(N_f: float = 24.0) -> bool:
    """Wave 2 correctness-push: predictions below tightest observational
    ceiling (Hulse-Taylor pulsar).

    Default N_f = 24 (Standard Model without right-handed neutrinos).
    Returns True iff all three Wave 1 a_4 coefficients are below
    ``HC_OBS_BOUNDS['pulsar_C_sq'] = 10⁵⁹``.

    Mirrors the structural content of Lean theorem
    ``higher_curvature_below_pulsar_bound`` at the SM fiducial.
    """
    return predictions_below_bound(N_f, HC_OBS_BOUNDS['pulsar_C_sq'])
