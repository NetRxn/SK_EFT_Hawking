"""CMB ℓ-space angular power spectrum amplitude diagnostics.

Mirrors `lean/SKEFTHawking/CosmologicalPerturbations.lean` §5-§6 —
growth-factor bounds in each regime.

We stay at the leading-order Sachs-Wolfe schematic: the angular
multipole `ℓ` couples to comoving wavenumber `k` via the line-of-sight
projection `k ≈ ℓ / η_dec`, so the unboundedness of the growth factor in
`k` translates directly to unboundedness in `ℓ`.
"""

from __future__ import annotations

import numpy as np

from src.core import formulas
from src.core.constants import COSMOLOGICAL_PERTURBATIONS_PARAMS


# ─── ℓ ↔ k bridge (Sachs-Wolfe leading order) ────────────────────────


def ell_to_k_wavenumber(ell: float, eta_dec: float | None = None) -> float:
    """Map angular multipole `ℓ` to comoving wavenumber `k` via the
    line-of-sight projection `k = ℓ / η_dec`.

    Standard Mukhanov §9.4 result; the leading-order Sachs-Wolfe
    projection used by all base-ΛCDM CMB calculators.
    """
    if eta_dec is None:
        eta_dec = COSMOLOGICAL_PERTURBATIONS_PARAMS["ETA_DECOUPLING_MPC"]
    return float(ell / eta_dec)


# ─── Growth-amplitude bounds (Lean cross-bridge) ─────────────────────


def cmb_growth_amplitude_max(
    cs_sq: float,
    k_wavenumber: float,
    eta_window: tuple[float, float] | None = None,
) -> float:
    """Maximum growth-factor amplitude over the conformal-time window
    `(η_decoupling, η_today)`.

    Lean: `instabilityGrowthFactor` evaluated at the upper edge of the
    conformal-time window. Bounded by 1 in the oscillatory regime;
    grows as `cosh(√|c_s²| · k · η_max)` in the instability regime.
    """
    if eta_window is None:
        eta_window = (
            COSMOLOGICAL_PERTURBATIONS_PARAMS["ETA_DECOUPLING_MPC"],
            COSMOLOGICAL_PERTURBATIONS_PARAMS["ETA_TODAY_MPC"],
        )
    return formulas.cmb_growth_amplitude(cs_sq, k_wavenumber, eta_window)


def spectrum_amplitude_at_ell(
    cs_sq: float,
    ell: float,
    eta_dec: float | None = None,
    eta_today: float | None = None,
) -> float:
    """Schematic spectrum-amplitude at angular multipole `ℓ`.

    Bridges the perturbation growth factor to the ℓ-space spectrum
    amplitude via the leading Sachs-Wolfe projection. The square enters
    because the angular power spectrum is `|δ_ℓ|²`.
    """
    if eta_dec is None:
        eta_dec = COSMOLOGICAL_PERTURBATIONS_PARAMS["ETA_DECOUPLING_MPC"]
    if eta_today is None:
        eta_today = COSMOLOGICAL_PERTURBATIONS_PARAMS["ETA_TODAY_MPC"]
    k = ell_to_k_wavenumber(ell, eta_dec)
    amplitude = cmb_growth_amplitude_max(cs_sq, k, (eta_dec, eta_today))
    return float(amplitude ** 2)


def spectrum_diverges_at_high_ell(
    cs_sq: float,
    ell_max: float | None = None,
    threshold_log10: float = 6.0,
) -> bool:
    """Predicate: does the spectrum amplitude exceed 10**threshold_log10
    at the falsification pivot ℓ?

    Returns True for the gradient-instability regime (c_s² < 0) at any
    plausible CMB ℓ — a 6-order-of-magnitude amplification past
    cos-bounded ΛCDM is a clean falsification signal against Planck's
    1% cosmic-variance ceiling.
    """
    if ell_max is None:
        ell_max = COSMOLOGICAL_PERTURBATIONS_PARAMS[
            "ELL_PIVOT_FOR_FALSIFICATION"
        ]
    amplitude_sq = spectrum_amplitude_at_ell(cs_sq, ell_max)
    if not np.isfinite(amplitude_sq):
        return True
    return amplitude_sq > (10.0 ** threshold_log10)


__all__ = [
    "ell_to_k_wavenumber",
    "cmb_growth_amplitude_max",
    "spectrum_amplitude_at_ell",
    "spectrum_diverges_at_high_ell",
]
