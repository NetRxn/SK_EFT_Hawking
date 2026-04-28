"""Decision Gate E.4 — natural-parameter CC-problem assessment.

Lean cross-references:
- ``MicroscopicCoefficientMatch.lambdaEmergMicroscopic_at_planck_natural_far_exceeds_observed``
- ``constants.MICRO_MACRO_PARAMS`` (CC_REPRODUCED_RATIO_FLOOR, etc.)
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Sequence

import numpy as np

from src.core.constants import MICRO_MACRO_PARAMS
from src.micro_macro_match.lambda_emerg_from_micro import (
    LambdaEmergPrediction,
    lambda_emerg_at_point,
)


@dataclass(frozen=True)
class CCProblemAssessment:
    """Decision Gate E.4 verdict at a single natural-parameter point.

    Attributes:
        Lambda_UV_GeV: UV cutoff at the assessment point.
        N_f: Dirac fermion species count.
        prediction: ``LambdaEmergPrediction`` at this point.
        verdict: One of ``cc_resolved`` / ``cc_reproduced`` / ``cc_intermediate``.
        natural: Whether ``Λ_UV ≥ EW_SCALE`` and ``N_f ≥ 1`` (band of
            "natural high-energy theories").
        is_resolution_locus: Whether this point is within an order of
            magnitude of the diagnostic resolution locus
            ``Λ_UV ≃ 4.5 × 10⁻¹² GeV`` at SM N_f.
    """

    Lambda_UV_GeV: float
    N_f: float
    prediction: LambdaEmergPrediction
    verdict: str
    natural: bool
    is_resolution_locus: bool


def assess_cc_problem(Lambda_UV_GeV: float, N_f: float) -> CCProblemAssessment:
    """Single-point assessment of the CC problem's emergent-form status."""
    pred = lambda_emerg_at_point(Lambda_UV_GeV, N_f)
    natural = (Lambda_UV_GeV >= MICRO_MACRO_PARAMS["EW_SCALE_GEV"]) and (N_f >= 1)
    locus = MICRO_MACRO_PARAMS["LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV"]
    if Lambda_UV_GeV <= 0.0 or locus <= 0.0:
        is_locus = False
    else:
        is_locus = abs(math.log10(Lambda_UV_GeV / locus)) < 1.0
    return CCProblemAssessment(
        Lambda_UV_GeV=float(Lambda_UV_GeV),
        N_f=float(N_f),
        prediction=pred,
        verdict=pred.verdict,
        natural=bool(natural),
        is_resolution_locus=bool(is_locus),
    )


def natural_parameter_scan(
    N_f_values: Sequence[float] | None = None,
    n_lambda_uv_points: int | None = None,
) -> list[CCProblemAssessment]:
    """2D scan over (N_f × Λ_UV) returning CCProblemAssessment per cell."""
    if N_f_values is None:
        N_f_values = MICRO_MACRO_PARAMS["N_F_SCAN_VALUES"]
    if n_lambda_uv_points is None:
        n_lambda_uv_points = MICRO_MACRO_PARAMS["LAMBDA_UV_SCAN_POINTS"]
    lo = MICRO_MACRO_PARAMS["LAMBDA_UV_SCAN_MIN_GEV"]
    hi = MICRO_MACRO_PARAMS["LAMBDA_UV_SCAN_MAX_GEV"]
    Lambda_UV_grid = np.logspace(
        math.log10(lo), math.log10(hi), num=int(n_lambda_uv_points)
    )
    out: list[CCProblemAssessment] = []
    for n in N_f_values:
        for L in Lambda_UV_grid:
            out.append(assess_cc_problem(float(L), float(n)))
    return out


def resolution_locus_diagnostic(N_f: float = 16.0) -> CCProblemAssessment:
    """Return assessment at the diagnostic resolution locus
    ``Λ_UV ≃ 4.5 × 10⁻¹² GeV`` at given N_f."""
    locus = MICRO_MACRO_PARAMS["LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV"]
    return assess_cc_problem(float(locus), float(N_f))
