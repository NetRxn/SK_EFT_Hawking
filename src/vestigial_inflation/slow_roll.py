"""Slow-roll parameters from the vestigial-phase potential.

Substrate (verified against Lean):
    V(τ) = f_0 · (1 - τ²)(5τ² - 1)        [VestigialEOS.rho_vest]
    V'(τ) = f_0 · (12τ - 20τ³) = 4 f_0 τ (3 - 5τ²)
    V''(τ) = f_0 · (12 - 60τ²)

Canonical inflaton φ = M_φ · τ where M_φ is a kinetic-term mass scale
(set by microscopic ingredients; for the preliminary scan we treat M_φ
as a free dimensional parameter).

Slow-roll parameters (reduced-Planck-mass convention M̄_P):
    ε = (M̄_P²/2) · (V_φ/V)²
    η = M̄_P² · (V_φφ/V)
where V_φ = (1/M_φ) · V_τ, V_φφ = (1/M_φ²) · V_ττ.
"""

import numpy as np


def vestigial_potential(tau, f0):
    """V(τ) = f_0 · (1 - τ²)(5τ² - 1).

    Lean: SKEFTHawking.VestigialEOS.rho_vest
    """
    return f0 * (1 - tau ** 2) * (5 * tau ** 2 - 1)


def vestigial_potential_derivative(tau, f0):
    """V'(τ) = 4 f_0 τ (3 - 5τ²)."""
    return 4 * f0 * tau * (3 - 5 * tau ** 2)


def vestigial_potential_second_derivative(tau, f0):
    """V''(τ) = f_0 · (12 - 60τ²)."""
    return f0 * (12 - 60 * tau ** 2)


def _ratio(M_Pl_red, M_phi):
    """ratio² = (M̄_P / M_φ)² — the universal prefactor of slow-roll params."""
    return (M_Pl_red / M_phi) ** 2


def slow_roll_epsilon(tau, f0, M_Pl_red, M_phi):
    """ε = (M̄_P²/2) · (V_φ/V)² evaluated at canonical inflaton φ = M_φ τ.

    Returns +inf when V → 0 (slow-roll breaks down at potential zeros).
    """
    V = vestigial_potential(tau, f0)
    Vp = vestigial_potential_derivative(tau, f0)
    if V <= 0:
        return np.inf  # slow-roll requires V > 0
    return 0.5 * _ratio(M_Pl_red, M_phi) * (Vp / V) ** 2


def slow_roll_eta(tau, f0, M_Pl_red, M_phi):
    """η = M̄_P² · (V_φφ/V)."""
    V = vestigial_potential(tau, f0)
    Vpp = vestigial_potential_second_derivative(tau, f0)
    if V <= 0:
        return np.nan
    return _ratio(M_Pl_red, M_phi) * Vpp / V
