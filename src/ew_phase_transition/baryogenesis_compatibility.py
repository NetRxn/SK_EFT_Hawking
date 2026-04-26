"""EW baryogenesis viability classifier.

A first-order transition is viable for baryogenesis (sphaleron decoupling)
iff ``E / (lambda T_c) > threshold``. Conventional sphaleron-decoupling
threshold is ~1.
"""

from __future__ import annotations

from src.core.formulas import ew_critical_temperature


def sphaleron_decoupling_threshold():
    """Sphaleron decoupling threshold for EW baryogenesis: 1.0.

    Per Cohen-Kaplan-Nelson, the EW phase transition is strong enough
    to suppress sphaleron rates after the bubble walls pass iff
    `v(T_c) / T_c > 1` equivalently `E / (lambda T_c) > 1`.
    """
    return 1.0


def is_baryogenesis_viable(E, mu_sq, lam, c_T, threshold=None):
    """First-order transition + threshold satisfied.

    Lean: EWPhaseTransition.IsBaryogenesisViable

    Parameters
    ----------
    E : float
        Cubic coefficient.
    mu_sq, lam, c_T : float
        Other potential parameters (mu_sq > 0, lam > 0, c_T > 0).
    threshold : float, optional
        Sphaleron decoupling threshold, default 1.0.

    Returns
    -------
    bool
        True if the transition is first-order AND strong enough.
    """
    if threshold is None:
        threshold = sphaleron_decoupling_threshold()
    if E <= 0:
        return False  # crossover — excluded by `crossover_excludes_baryogenesis`
    T_c = ew_critical_temperature(mu_sq, c_T)
    return float(E) > threshold * lam * T_c
