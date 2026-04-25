"""Anderson-Higgs W/Z mass matrix from the scalar-rung condensate VEV.

Numerical companion to ``ScalarRungInterpretation.ew_mass_matrix_from_scalar_vev``
(``lean/SKEFTHawking/ScalarRungInterpretation.lean``).
"""

from __future__ import annotations

from src.core.constants import EW_PARAMS
from src.core.formulas import (
    w_mass_from_vev,
    z_mass_from_vev,
    ew_mass_ratio_cos_theta_w,
)


def anderson_higgs_w_z_masses(g=None, g_prime=None, v=None):
    """Compute (M_W, M_Z) at given couplings + VEV.

    Defaults to ``EW_PARAMS`` fiducials, reproducing the PDG W/Z masses.

    Parameters
    ----------
    g : float, optional
        SU(2)_L gauge coupling. Defaults to ``EW.G_SU2``.
    g_prime : float, optional
        U(1)_Y hypercharge coupling. Defaults to ``EW.G_U1Y``.
    v : float, optional
        EW VEV in GeV. Defaults to ``EW.V_EW_GEV``.

    Returns
    -------
    tuple[float, float]
        (M_W, M_Z) in GeV.
    """
    if g is None:
        g = EW_PARAMS["G_SU2"]
    if g_prime is None:
        g_prime = EW_PARAMS["G_U1Y"]
    if v is None:
        v = EW_PARAMS["V_EW_GEV"]

    return w_mass_from_vev(g, v), z_mass_from_vev(g, g_prime, v)


def cos_theta_w_consistency(g=None, g_prime=None):
    """Predict cos θ_W from the gauge couplings and compare to the EW_PARAMS
    on-shell value.

    Returns the dictionary ``{predicted, expected, abs_error}`` where
    ``expected = √(1 - SIN2_THETA_W)`` from PDG.
    """
    if g is None:
        g = EW_PARAMS["G_SU2"]
    if g_prime is None:
        g_prime = EW_PARAMS["G_U1Y"]

    predicted = ew_mass_ratio_cos_theta_w(g, g_prime)
    expected = (1.0 - EW_PARAMS["SIN2_THETA_W"]) ** 0.5
    return {
        "predicted": predicted,
        "expected": expected,
        "abs_error": abs(predicted - expected),
    }
