"""Microscopic G_N^emerg + match-residual evaluator + scans.

Lean cross-references:
- ``MicroscopicCoefficientMatch.gNMicroscopic``
- ``MicroscopicCoefficientMatch.matchResidual``
- ``MicroscopicCoefficientMatch.matchResidual_eq_zero_iff_alpha_unity``
- ``MicroscopicCoefficientMatch.gNMicroscopic_at_alpha_one_eq_G_N_emerg``
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

import numpy as np

from src.core.constants import MICRO_MACRO_PARAMS
from src.core.formulas import (
    g_n_microscopic,
    microscopic_macroscopic_match_residual,
    microscopic_macroscopic_match_holds,
    G_N_from_seeley_dewitt,
)


@dataclass(frozen=True)
class GNMatchResult:
    """A single ``(Λ_UV, N_f, α_ADW)`` match-residual evaluation.

    Attributes:
        Lambda_UV_GeV: Microscopic UV cutoff in GeV.
        N_f: Dirac fermion species count.
        alpha_ADW: ADW substrate-rescaling parameter.
        g_n_micro_GeVm2: Microscopic G_N^emerg = α_ADW · G_N_sakharov.
        g_n_baseline_GeVm2: Baseline G_N_from_a2 (heat-kernel).
        match_residual: g_n_micro − g_n_baseline = (α-1) · G_N_baseline.
        bundle_holds: bool — does ``H_MicroscopicCoefficientMatch`` hold?
    """

    Lambda_UV_GeV: float
    N_f: float
    alpha_ADW: float
    g_n_micro_GeVm2: float
    g_n_baseline_GeVm2: float
    match_residual: float
    bundle_holds: bool


def g_n_microscopic_at_point(
    Lambda_UV_GeV: float, N_f: float, alpha_ADW: float = 1.0,
) -> GNMatchResult:
    """Evaluate microscopic G_N + match residual at a single point."""
    g_micro = g_n_microscopic(Lambda_UV_GeV, N_f, alpha_ADW)
    g_baseline = G_N_from_seeley_dewitt(Lambda_UV_GeV, N_f)
    residual = microscopic_macroscopic_match_residual(
        Lambda_UV_GeV, N_f, alpha_ADW
    )
    holds = microscopic_macroscopic_match_holds(Lambda_UV_GeV, N_f, alpha_ADW)
    return GNMatchResult(
        Lambda_UV_GeV=float(Lambda_UV_GeV),
        N_f=float(N_f),
        alpha_ADW=float(alpha_ADW),
        g_n_micro_GeVm2=float(g_micro),
        g_n_baseline_GeVm2=float(g_baseline),
        match_residual=float(residual),
        bundle_holds=bool(holds),
    )


def match_residual_scan_over_alpha(
    Lambda_UV_GeV: float,
    N_f: float,
    alpha_min: float = 0.1,
    alpha_max: float = 10.0,
    n_points: int = 21,
) -> list[GNMatchResult]:
    """Log-spaced α_ADW scan of the Wave-5 match residual."""
    grid = np.logspace(np.log10(alpha_min), np.log10(alpha_max), num=int(n_points))
    return [g_n_microscopic_at_point(Lambda_UV_GeV, N_f, float(a)) for a in grid]


def match_holds(
    Lambda_UV_GeV: float, N_f: float, alpha_ADW: float = 1.0,
    tolerance: float | None = None,
) -> bool:
    """Direct bundle check without instantiating a full GNMatchResult."""
    return microscopic_macroscopic_match_holds(
        Lambda_UV_GeV, N_f, alpha_ADW, tolerance
    )
