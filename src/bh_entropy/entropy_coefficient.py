"""Entropy coefficient + log-correction numerical evaluation.

Wraps ``src.core.formulas`` Wave 3 functions for grid-based plotting and
zoo-tabulation. Used by the Wave 3 figures (`fig_entropy_coefficient_vs_spectrum`,
`fig_log_correction_signature`).

Lean cross-references:
- `BHEntropyMicroscopic.kaulMajumdarS` (closed form)
- `BHEntropyMicroscopic.kaul_majumdar_log_coefficient` (extracts c_log = -3/2)
- `BHEntropyMicroscopic.kaul_majumdar_log_decomposition` (-1/2 + -1 = -3/2)
- `BHEntropyMicroscopic.sen_4d_disagrees_with_kaul_majumdar` (non-universality)

Source: Kaul-Majumdar gr-qc/0002040; Kaul SIGMA arXiv:1201.6102; Sen
        arXiv:1205.0971 (non-universality).
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from src.core.constants import BH_ENTROPY_PARAMS
from src.core.formulas import (
    bh_entropy_kaul_majumdar,
    bh_entropy_leading_coefficient,
    log_correction_coefficient_per_mtc,
    log_correction_coefficient_su2k,
)


def kaul_majumdar_entropy_grid(
    log_area_lower: float | None = None,
    log_area_upper: float | None = None,
    n_points: int = 100,
    G_N: float = 1.0,
    c0: float = 0.0,
):
    """Kaul-Majumdar entropy on a log-A grid.

    Parameters
    ----------
    log_area_lower, log_area_upper : float, optional
        Log(A/(4 G_N)) bounds. Defaults from `BH_ENTROPY_PARAMS`.
    n_points : int
        Grid size.
    G_N : float
        Newton's constant in chosen units.
    c0 : float
        Subleading constant.

    Returns
    -------
    tuple of (np.ndarray, np.ndarray)
        (log_area, S) arrays.
    """
    if log_area_lower is None:
        log_area_lower = BH_ENTROPY_PARAMS["HORIZON_AREA_LOG_LOWER"]
    if log_area_upper is None:
        log_area_upper = BH_ENTROPY_PARAMS["HORIZON_AREA_LOG_UPPER"]
    log_A = np.linspace(log_area_lower, log_area_upper, n_points)
    A = 4.0 * G_N * np.exp(log_A)
    S = bh_entropy_kaul_majumdar(A, G_N=G_N, c0=c0)
    return log_A, S


def leading_coefficient_vs_immirzi(
    gamma_lower: float = 0.05,
    gamma_upper: float = 1.0,
    n_points: int = 200,
):
    """Leading coefficient κ_leading(γ) = γ_DL/γ · 1/4 across the Immirzi range.

    Demonstrates that κ_leading = 1/4 only at γ = γ_DL ≈ 0.2375 (Domagala-
    Lewandowski) and γ = γ_M ≈ 0.2739 (Meissner) under their respective
    counting prescriptions. The 1/4 prefactor is structurally a TUNING.

    Parameters
    ----------
    gamma_lower, gamma_upper : float
        Immirzi γ scan bounds.
    n_points : int
        Grid size.

    Returns
    -------
    tuple of (np.ndarray, np.ndarray, dict)
        (γ array, κ_leading(γ) array, anchors dict with γ_DL and γ_Meissner).
    """
    gammas = np.linspace(gamma_lower, gamma_upper, n_points)
    kappas = np.array(
        [bh_entropy_leading_coefficient(g) for g in gammas]
    )
    anchors = {
        "DL": BH_ENTROPY_PARAMS["IMMIRZI_GAMMA_DOMAGALA_LEWANDOWSKI"],
        "Meissner": BH_ENTROPY_PARAMS["IMMIRZI_GAMMA_MEISSNER"],
    }
    return gammas, kappas, anchors


def log_correction_zoo() -> dict:
    """Per-MTC log-correction coefficients zoo.

    Returns
    -------
    dict
        {mtc_name: {value, status, source}} for the named MTC zoo.
    """
    names = ["SU2k", "Sen4DSchwarzschild", "Fibonacci", "Ising", "DS3", "ToricCode"]
    return {n: log_correction_coefficient_per_mtc(n) for n in names}


@dataclass(frozen=True)
class SenDisagreementWitness:
    """Numerical witness against −3/2 log-coefficient universality.

    Sen (arXiv:1205.0971) heat-kernel result for 4D Schwarzschild gives
    c_log = +(212/45 - 3) ≈ +1.711, disagreeing with Kaul-Majumdar's −3/2.
    """

    c_log_kaul_majumdar: float
    c_log_sen_4d: float
    disagreement: float
    is_disagreement: bool


def sen_disagreement_witness() -> SenDisagreementWitness:
    """Construct the numerical witness against universality.

    Returns
    -------
    SenDisagreementWitness
        Frozen dataclass with the two coefficients and their difference.
    """
    c_km = log_correction_coefficient_su2k()
    c_sen = BH_ENTROPY_PARAMS["LOG_CORRECTION_SEN_4D_SCHWARZSCHILD"]
    diff = c_sen - c_km
    return SenDisagreementWitness(
        c_log_kaul_majumdar=c_km,
        c_log_sen_4d=c_sen,
        disagreement=diff,
        is_disagreement=(abs(diff) > BH_ENTROPY_PARAMS["LOG_CORRECTION_MATCH_TOLERANCE"]),
    )
