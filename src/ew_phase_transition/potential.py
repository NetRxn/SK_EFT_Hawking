"""Finite-T effective potential for the EW phase transition.

Direct numerical companions to
``lean/SKEFTHawking/EWPhaseTransition.lean`` definitions of
`finiteTPotential`, `thermalMassSq`, `criticalTemperature`, and
`latentHeat`.

The high-T expansion (Anderson-Hall, Quiros) is:

    V_T(phi, T) = (1/2) (c_T T^2 - mu^2) phi^2
                  - (1/3) E T phi^3
                  + (1/4) lambda phi^4

with cubic coefficient `E` distinguishing first-order from crossover.
"""

from __future__ import annotations

import numpy as np

from src.core.formulas import (
    ew_finite_t_potential,
    ew_thermal_mass_sq,
    ew_critical_temperature,
    ew_latent_heat,
)


def finite_t_potential(phi, T, mu_sq, lam, c_T, E):
    """Wrapper around the canonical formula in `formulas.py`."""
    return ew_finite_t_potential(phi, T, mu_sq, lam, c_T, E)


def thermal_mass_sq(T, mu_sq, c_T):
    """Thermal mass squared `mu^2(T) = c_T T^2 - mu^2`."""
    return ew_thermal_mass_sq(T, mu_sq, c_T)


def critical_temperature(mu_sq, c_T):
    """Critical temperature `T_c = sqrt(mu^2 / c_T)`."""
    return ew_critical_temperature(mu_sq, c_T)


def latent_heat(E, mu_sq, lam, c_T):
    """Latent heat at LO: `L = E^2 T_c^2 / (2 lambda)`."""
    return ew_latent_heat(E, mu_sq, lam, c_T)
