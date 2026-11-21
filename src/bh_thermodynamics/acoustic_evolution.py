"""Chosen exponential cooling and Schwarzschild temperature profiles.

Mirrors `T_H_acoustic_evolution` and `T_H_schwarzschild` in
`lean/SKEFTHawking/BHThermodynamicsFourLaws.lean`. The exponential
`T_H(t) = T_H,0 · exp(-t/τ_cool)` is an illustrative profile chosen by
this project. Its positivity, strict decrease and asymptotic zero limit
are properties of that definition, not a source-derived acoustic
backreaction solution.

Balbinot, Fagnocchi, Fabbri, *Quantum Effects in Acoustic Black Holes:
the Backreaction*, **Phys. Rev. D 71, 064019 (2005)**,
arXiv:gr-qc/0405098, Eq. (Tsonic), gives a local affine temperature
correction with coefficient 563/(720π). The calculation concerns a
constant-sound-speed sonic hole in a Laval nozzle in a short-time,
near-horizon approximation. Its `t ~ 1/T³` discussion is an explicit
extrapolation, not the exponential defined here. The authors defer the
Bose-Einstein-condensate case, where `c ∝ ρ^(1/2)`. Cooling in that case
requires a separate derivation; the constant-sound-speed result does
not establish its sign automatically. Calibration to source parameters,
control of the local approximation's remainder and a physical evolution
remain separate construction obligations.

Replaces the (deleted) `schottky_saturation.py` from the initial Wave 5
ship; that module implemented the Jacobson-Koike Eq. (13) Schottky form
which was attributed to the wrong analog system. See
`papers/AutomatedReviews/2026-04-26-2230-wave5-process/deep_research_analog_conflation.md`
for the provenance correction.

Lean: BHThermodynamicsFourLaws.T_H_acoustic_evolution +
       BHThermodynamicsFourLaws.T_H_schwarzschild
"""

from __future__ import annotations

import math

import numpy as np

from src.bh_thermodynamics.regime_classifier import ADWParams


def T_H_acoustic_evolution(T_H0: float, tau_cool: float, t: float) -> float:
    """Illustrative exponential temperature profile at time t.

    `T_H(t) = T_H,0 · exp(-t / τ_cool)` is a chosen cooling profile,
    distinct from Balbinot 2005 Eq. (Tsonic)'s local affine law.
    Strictly positive and strictly decreasing in t when both T_H,0 and
    τ_cool are positive. Its zero-temperature limit occurs only as
    t tends to infinity; this property does not establish a physical
    acoustic evaporation endpoint.

    Mirrors `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean::T_H_acoustic_evolution`.

    Parameters
    ----------
    T_H0 : float
        Initial Hawking temperature at t=0 (must be > 0 for the
        physical regime).
    tau_cool : float
        Cooling timescale (must be > 0).
    t : float
        Time argument of the illustrative profile.

    Returns
    -------
    float
        T_H(t).
    """
    if tau_cool <= 0:
        raise ValueError("tau_cool must be > 0")
    return T_H0 * math.exp(-t / tau_cool)


def T_H_acoustic_evolution_grid(
    T_H0: float, tau_cool: float, t_max: float, N_points: int = 101
) -> tuple[np.ndarray, np.ndarray]:
    """Time grid of the illustrative exponential over t ∈ [0, t_max].

    Returns (t_grid, T_H_grid) suitable for plotting the cooling
    profile. Verifies T_H is strictly positive and strictly decreasing
    when T_H0 > 0 and tau_cool > 0.

    Parameters
    ----------
    T_H0 : float
        Initial T_H (must be ≥ 0).
    tau_cool : float
        Cooling timescale (must be > 0).
    t_max : float
        Maximum time (must be > 0).
    N_points : int
        Grid resolution (default 101).

    Returns
    -------
    (np.ndarray, np.ndarray)
        Time grid and T_H values along it.
    """
    if T_H0 < 0:
        raise ValueError("T_H0 must be ≥ 0")
    if tau_cool <= 0:
        raise ValueError("tau_cool must be > 0")
    if t_max <= 0:
        raise ValueError("t_max must be > 0")
    t_grid = np.linspace(0.0, t_max, N_points)
    T_H_grid = T_H0 * np.exp(-t_grid / tau_cool)
    return t_grid, T_H_grid


def T_H_schwarzschild(M: float) -> float:
    """Classical Schwarzschild Hawking temperature `T_H = 1/(8π M)`.

    Natural units (ℏ = 1). Strictly positive and strictly decreasing
    in M (Hawking 1975). During evaporation `dM/dt < 0`, so combined
    with this monotonicity gives `dT_H/dt > 0` (heats as evaporates).

    Mirrors `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean::T_H_schwarzschild`.

    Parameters
    ----------
    M : float
        Black-hole mass (must be > 0).

    Returns
    -------
    float
        T_H(M).
    """
    if M <= 0:
        raise ValueError("M must be > 0")
    return 1.0 / (8.0 * math.pi * M)


def T_H_schwarzschild_grid(
    M_min: float, M_max: float, N_points: int = 101
) -> tuple[np.ndarray, np.ndarray]:
    """Grid of Schwarzschild T_H over M ∈ [M_min, M_max].

    Parameters
    ----------
    M_min : float
        Minimum mass (must be > 0).
    M_max : float
        Maximum mass (must be > M_min).
    N_points : int
        Grid resolution (default 101).

    Returns
    -------
    (np.ndarray, np.ndarray)
        Mass grid and T_H values along it.
    """
    if M_min <= 0:
        raise ValueError("M_min must be > 0")
    if M_max <= M_min:
        raise ValueError("M_max must be > M_min")
    M_grid = np.linspace(M_min, M_max, N_points)
    T_H_grid = 1.0 / (8.0 * math.pi * M_grid)
    return M_grid, T_H_grid


def delta_ADW_ansatz(p: ADWParams) -> float:
    """Wave 5 substrate-response coefficient ansatz: `δ_ADW = (α_ADW − 1) · Λ_UV`.

    Mirrors the `delta_consistent_with_ansatz` field of
    `H_RegimePartition` in the Lean module. Vanishes in the bare
    Sakharov-Adler limit `α_ADW = 1`; positive for `α_ADW > 1`,
    negative for `α_ADW < 1`.

    Parameters
    ----------
    p : ADWParams
        Substrate parameters.

    Returns
    -------
    float
        Substrate-response coefficient `δ_ADW`.
    """
    return (p.alpha_ADW - 1.0) * p.lambda_UV
