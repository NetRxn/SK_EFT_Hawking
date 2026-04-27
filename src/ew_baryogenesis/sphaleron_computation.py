"""Sphaleron rate / decoupling helpers for the EWBG bridge.

The structural form ``exp(-v/T)`` is the load-bearing dimensionless
suppression factor; the actual Klinkhamer-Manton rate is
``Γ_sphal ~ (α_W T)^4 exp(-E_sph/T)`` with ``E_sph ~ 4π v / g_W``.
Cohen-Kaplan-Nelson (1993) decoupling condition: ``v(T_c)/T_c > 1``.
"""

from __future__ import annotations

import math

from src.core.formulas import sphaleron_suppression as _sphaleron_suppression


def sphaleron_decoupling_threshold():
    """Cohen-Kaplan-Nelson sphaleron-decoupling threshold: 1.0.

    ``v(T_c) / T_c > 1`` is the conventional condition for sphaleron
    decoupling in the broken phase (Cohen, Kaplan, Nelson, Annu. Rev.
    Nucl. Part. Sci. 43, 27 (1993)).
    """
    return 1.0


def sphaleron_suppression(v, T):
    """Sphaleron-rate Boltzmann suppression factor (re-export).

    See ``src.core.formulas.sphaleron_suppression`` for the canonical
    definition. Lean: ``EWBaryogenesisChiralityWall.sphaleronSuppression``.
    """
    return _sphaleron_suppression(v, T)


def sphalerons_decoupled(v, T, threshold=None):
    """Whether sphalerons are decoupled at (v, T) given threshold.

    Lean: ``EWBaryogenesisChiralityWall.SphaleronsDecoupled``.

    Parameters
    ----------
    v : float
        Broken-phase Higgs VEV [GeV].
    T : float
        Temperature [GeV].
    threshold : float, optional
        Sphaleron-decoupling threshold (v/T ratio), default 1.0.

    Returns
    -------
    bool
        True iff ``v/T > threshold``.
    """
    if threshold is None:
        threshold = sphaleron_decoupling_threshold()
    if T <= 0:
        raise ValueError("Temperature must be strictly positive.")
    return float(v / T) > float(threshold)
