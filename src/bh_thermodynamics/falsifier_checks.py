"""Numerical implementations of the four Wave 5 falsifiers.

Mirrors the four falsifier theorems in
`lean/SKEFTHawking/BHThermodynamicsFourLaws.lean` (post-rewrite
2026-04-26-2230 around Balbinot 2005 BEC-acoustic primary anchor):

- `falsifier_acoustic_decay_form`: BEC-acoustic strict-monotone-decay
  (Balbinot 2005 Eq. Tsonic). T_H_alt non-decreasing on [t₁, t₂]
  falsifies the BEC-acoustic-regime identification.
- `falsifier_schwarzschild_heating`: Schwarzschild dT/dt > 0
  prediction. dT/dt_observed ≤ 0 in M > M_c regime falsifies.
- `falsifier_third_law_form`: Israel/Reall infinite-time vs.
  Kehle-Unger finite-time at the M_c-asymptotic limit.
- `falsifier_alpha_ADW_dependence`: substrate-response sign of `δ_ADW`.
"""

from __future__ import annotations

from typing import Callable

from src.bh_thermodynamics.regime_classifier import ADWParams
from src.bh_thermodynamics.acoustic_evolution import delta_ADW_ansatz


def falsifier_acoustic_decay_form(
    T_H_alt: Callable[[float], float],
    t_1: float,
    t_2: float,
    tolerance: float = 0.0,
) -> bool:
    """Falsifier 1 — BEC-acoustic decay form (Balbinot 2005 Eq. Tsonic).

    The BEC-acoustic regime predicts strict monotone-decay of T_H(t)
    under Hawking-radiation backreaction. A candidate `T_H_alt(t)`
    that fails to be strictly decreasing on [t₁, t₂] falsifies the
    BEC-acoustic-regime identification.

    Returns True if `T_H_alt(t_2) >= T_H_alt(t_1) - tolerance` (with
    `t_1 < t_2`), i.e., the candidate violates strict monotone-decay.

    Parameters
    ----------
    T_H_alt : Callable[[float], float]
        Candidate T_H(t) profile.
    t_1, t_2 : float
        Two times with `t_1 < t_2`.
    tolerance : float
        Numerical slack (default 0).

    Returns
    -------
    bool
        True if the candidate is FALSIFIED against Balbinot 2005.
    """
    if t_1 >= t_2:
        raise ValueError(
            f"falsifier_acoustic_decay_form requires t_1 < t_2 "
            f"(got t_1={t_1}, t_2={t_2})"
        )
    val_1 = T_H_alt(t_1)
    val_2 = T_H_alt(t_2)
    # Falsified if candidate did NOT decrease (T(t_2) ≥ T(t_1) - tol).
    return val_2 >= val_1 - tolerance


def falsifier_schwarzschild_heating(
    dT_dt_observed: float,
    tolerance: float = 0.0,
) -> bool:
    """Falsifier 2 — Schwarzschild heating sign (Hawking 1975).

    The Schwarzschild regime predicts `dT_H/dt > 0` during evaporation
    (T_H ∝ 1/M, dM/dt < 0). A measured `dT_H/dt ≤ 0` in the M > M_c
    regime falsifies the Schwarzschild identification.

    Returns True if `dT_dt_observed ≤ tolerance`, i.e., the
    Schwarzschild prediction is falsified.

    Parameters
    ----------
    dT_dt_observed : float
        Observed time-derivative of T_H in the M > M_c regime.
    tolerance : float
        Numerical slack (default 0).

    Returns
    -------
    bool
        True if the Schwarzschild identification is FALSIFIED.
    """
    return dT_dt_observed <= tolerance


def falsifier_third_law_form(
    approach_time_finite: bool,
    branch: str = "israel_reall",
) -> bool:
    """Falsifier 3 — third-law form (Israel/Reall vs. Kehle-Unger).

    The BEC-acoustic regime predicts `t ~ 1/T³` per Balbinot 2005,
    hence Israel strong form preserved (κ → 0 only in infinite affine
    time). Kehle-Unger 2022 (arXiv:2211.15742) demonstrates that
    charged-scalar matter sectors can allow finite-time approach.
    A measured finite-time κ → 0 falsifies the BPS-restoration
    condition (Reall, arXiv:2410.11956).

    Parameters
    ----------
    approach_time_finite : bool
        Whether the measured approach time is finite (Kehle-Unger
        signature) or infinite (Israel/Reall signature).
    branch : str
        "israel_reall" or "kehle_unger".

    Returns
    -------
    bool
        True if the branch is falsified by the observation.
    """
    if branch == "israel_reall":
        # Israel/Reall expects infinite-time approach. Falsified by finite-time.
        return approach_time_finite
    elif branch == "kehle_unger":
        # Kehle-Unger expects finite-time approach. Falsified by infinite-time.
        return not approach_time_finite
    else:
        raise ValueError(
            f"branch must be 'israel_reall' or 'kehle_unger', got {branch!r}"
        )


def falsifier_alpha_ADW_dependence(
    delta_ADW_measured: float,
    p: ADWParams,
    tolerance: float = 1.0e-6,
) -> bool:
    """Falsifier 4 — χ_vest dependence (substrate-response sign).

    The Wave 5 deep-research ansatz is
    `δ_ADW = (α_ADW − 1) · Λ_UV`, vanishing at `α_ADW = 1` and sign-
    determined by `α_ADW ⋛ 1`. Returns True if the measured
    `delta_ADW_measured` falsifies this prediction (e.g., wrong sign or
    non-vanishing at `α_ADW = 1`).

    Parameters
    ----------
    delta_ADW_measured : float
        Measured substrate-response coefficient.
    p : ADWParams
        Substrate parameters.
    tolerance : float
        Tolerance for sign-vs-zero distinction (default 1e-6).

    Returns
    -------
    bool
        True if the deep-research ansatz is FALSIFIED by the measurement.
    """
    delta_predicted = delta_ADW_ansatz(p)
    # Sign check: predicted and measured should have same sign (or both ~ 0).
    if abs(delta_predicted) < tolerance:
        # Predicted ~ 0; falsified if measured significantly nonzero.
        return abs(delta_ADW_measured) > tolerance
    if abs(delta_ADW_measured) < tolerance:
        # Measured ~ 0 but predicted nonzero ⇒ falsified.
        return True
    # Both nonzero: check sign agreement.
    return (delta_predicted * delta_ADW_measured) < 0
