"""Phase 5z Wave 1b: BHL gauge-embedding numerics.

Concrete numerical companions to ``lean/SKEFTHawking/BHLGaugeEmbedding.lean``.
Implements the leading-order BHL formula `m_H = sqrt(2) * m_t`, the BHL
gap problem demonstration, and the Hill 2025 bilocal correction recovering
m_H = 125 GeV from BHL-overshooting predictions.

Per Phase 5z O.2 deep research verdict (Scenario A, structural-analogy
strength 3/5).

References:
- Bardeen, Hill, Lindner, PRD 41, 1647 (1990)
- Hill, "Natural Top Quark Condensation (a Redux)," arXiv:2503.21518 (2025)
- Andrianov, Andrianov, Afonin, EPJ C 80, 1179 (2020)
"""

from __future__ import annotations

import numpy as np

from src.core.formulas import (
    bhl_higgs_mass,
    bhl_minimal_overshoot_factor,
    bilocal_correction_factor,
    bilocal_corrected_higgs_mass,
    pagels_stokar_vev_sq,
)


def bhl_minimal_prediction(m_t: float = 220.0) -> dict:
    """BHL minimal prediction at the Pendleton-Ross IR fixed point.

    At the canonical BHL benchmark (Λ = M_Pl, N_c = 3), m_t ≈ 220 GeV
    saturates the compositeness boundary condition; m_H = sqrt(2) * m_t
    follows from the Nambu sum rule at leading large-N_c.

    Parameters
    ----------
    m_t : float
        Top-quark mass at the BHL benchmark, default 220 GeV.

    Returns
    -------
    dict
        ``{'m_t_GeV': 220, 'm_H_GeV': ~311, 'm_H_over_m_t': sqrt(2)}``
    """
    m_h = bhl_higgs_mass(m_t)
    return {
        "m_t_GeV": m_t,
        "m_H_GeV": m_h,
        "m_H_over_m_t": m_h / m_t,
    }


def bhl_gap_against_pdg(m_h_pdg: float = 125.20) -> dict:
    """Quantify the BHL gap problem against the PDG observed Higgs mass.

    The BHL minimal prediction (m_H ≈ 310 GeV) overshoots PDG (125.20 GeV)
    by ~2.5×; the gap motivates the Hill bilocal correction.

    Parameters
    ----------
    m_h_pdg : float
        PDG observed m_H in GeV, default 125.20.

    Returns
    -------
    dict
        ``{'m_H_BHL_GeV', 'm_H_PDG_GeV', 'overshoot_factor', 'gap_GeV'}``
    """
    m_h_bhl = bhl_higgs_mass(220.0)
    return {
        "m_H_BHL_GeV": m_h_bhl,
        "m_H_PDG_GeV": m_h_pdg,
        "overshoot_factor": m_h_bhl / m_h_pdg,
        "gap_GeV": m_h_bhl - m_h_pdg,
    }


def bilocal_correction_required(
    m_h_target: float = 125.20, m_t: float = 220.0
) -> float:
    """Bilocal dilution factor required to match a target m_H.

    Solves m_h_target = (φ(0)/φ(∞)) * sqrt(2) * m_t for the dilution.

    Parameters
    ----------
    m_h_target : float
        Target Higgs mass (default PDG 125.20 GeV).
    m_t : float
        BHL benchmark top mass (default 220 GeV).

    Returns
    -------
    float
        Required dilution factor `φ(0)/φ(∞)` ∈ (0, 1).
    """
    return m_h_target / bhl_higgs_mass(m_t)


def bilocal_correction_scan(
    dilution_range: np.ndarray, m_t: float = 220.0
) -> np.ndarray:
    """Scan corrected Higgs mass over a range of bilocal dilutions.

    Per Hill 2025, the dilution factor varies smoothly from 1
    (pointlike, BHL minimal) to ~0 (deep bilocal, super-suppressed
    Yukawa). The PDG value 125.20 GeV is recovered at dilution ≈ 0.402.

    Parameters
    ----------
    dilution_range : np.ndarray
        Values of `φ(0)/φ(∞)` to scan.
    m_t : float
        Top mass benchmark, default 220 GeV.

    Returns
    -------
    np.ndarray
        Corrected m_H values [GeV] across the scan.
    """
    return np.array(
        [bilocal_corrected_higgs_mass(d, m_t) for d in dilution_range]
    )


def bhl_pagels_stokar_vev_check(
    n_c: int = 3, m_t: float = 173.0, lambda_uv: float = 1.22e19
) -> float:
    """Check the Pagels-Stokar formula at SM benchmark values.

    Parameters
    ----------
    n_c : int
        Number of colors, default 3 (SM).
    m_t : float
        Top mass [GeV], default 173.
    lambda_uv : float
        UV cutoff [GeV], default M_Pl ≈ 1.22e19.

    Returns
    -------
    float
        Predicted v² [GeV²].
    """
    return pagels_stokar_vev_sq(n_c, m_t, lambda_uv)
