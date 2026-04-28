"""Λ^emerg(Λ_UV, N_f) evaluator + scans.

Lean cross-references:
- ``MicroscopicCoefficientMatch.lambdaEmergMicroscopic``
- ``MicroscopicCoefficientMatch.lambdaEmergMicroscopic_pos``
- ``MicroscopicCoefficientMatch.lambdaEmergMicroscopic_eq_zero_iff``
- ``MicroscopicCoefficientMatch.lambdaEmergMicroscopic_at_planck_natural_far_exceeds_observed``
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Sequence

import numpy as np

from src.core.constants import MICRO_MACRO_PARAMS
from src.core.formulas import (
    lambda_emerg_microscopic,
    cc_decision_gate_e4_verdict,
    cc_problem_ratio,
)


@dataclass(frozen=True)
class LambdaEmergPrediction:
    """A single microscopic-parameter prediction for Λ^emerg.

    Attributes:
        Lambda_UV_GeV: Microscopic UV cutoff in GeV.
        N_f: Dirac fermion species count.
        lambda_emerg_GeV4: Λ^emerg = a_0(N_f) · Λ_UV⁴ in GeV⁴.
        ratio_to_observed: Λ^emerg / Λ_obs (Planck 2018).
        log10_ratio: log₁₀ of the ratio.
        verdict: Decision Gate E.4 verdict label
            (``cc_resolved`` / ``cc_reproduced`` / ``cc_intermediate``).
    """

    Lambda_UV_GeV: float
    N_f: float
    lambda_emerg_GeV4: float
    ratio_to_observed: float
    log10_ratio: float
    verdict: str


def lambda_emerg_at_point(Lambda_UV_GeV: float, N_f: float) -> LambdaEmergPrediction:
    """Evaluate Λ^emerg at a single microscopic-parameter point."""
    le = lambda_emerg_microscopic(Lambda_UV_GeV, N_f)
    if le <= 0.0:
        return LambdaEmergPrediction(
            Lambda_UV_GeV=float(Lambda_UV_GeV),
            N_f=float(N_f),
            lambda_emerg_GeV4=float(le),
            ratio_to_observed=float("nan"),
            log10_ratio=float("nan"),
            verdict=MICRO_MACRO_PARAMS["DG_E4_VERDICT_INTERMEDIATE"],
        )
    ratio = cc_problem_ratio(Lambda_UV_GeV, N_f)
    return LambdaEmergPrediction(
        Lambda_UV_GeV=float(Lambda_UV_GeV),
        N_f=float(N_f),
        lambda_emerg_GeV4=float(le),
        ratio_to_observed=float(ratio),
        log10_ratio=float(math.log10(ratio)),
        verdict=cc_decision_gate_e4_verdict(Lambda_UV_GeV, N_f),
    )


def lambda_emerg_scan_over_lambdaUV(
    N_f: float,
    n_points: int | None = None,
) -> list[LambdaEmergPrediction]:
    """Log-spaced scan of Λ^emerg over Λ_UV ∈ [LAMBDA_UV_SCAN_MIN, MAX] at fixed N_f."""
    if n_points is None:
        n_points = MICRO_MACRO_PARAMS["LAMBDA_UV_SCAN_POINTS"]
    lo = MICRO_MACRO_PARAMS["LAMBDA_UV_SCAN_MIN_GEV"]
    hi = MICRO_MACRO_PARAMS["LAMBDA_UV_SCAN_MAX_GEV"]
    grid = np.logspace(math.log10(lo), math.log10(hi), num=int(n_points))
    return [lambda_emerg_at_point(float(L), N_f) for L in grid]


def lambda_emerg_scan_over_N_f(
    Lambda_UV_GeV: float,
    N_f_values: Sequence[float] | None = None,
) -> list[LambdaEmergPrediction]:
    """Scan of Λ^emerg over a list of N_f values at fixed Λ_UV."""
    if N_f_values is None:
        N_f_values = MICRO_MACRO_PARAMS["N_F_SCAN_VALUES"]
    return [lambda_emerg_at_point(Lambda_UV_GeV, float(n)) for n in N_f_values]


def decision_gate_e4_verdict(Lambda_UV_GeV: float, N_f: float) -> str:
    """Direct verdict label without instantiating a full prediction object."""
    return cc_decision_gate_e4_verdict(Lambda_UV_GeV, N_f)
