"""Modified Bogoliubov coefficients for the dissipative Hawking effect.

The standard Bogoliubov transformation connects in-modes to out-modes across
the horizon. In the non-dissipative case, unitarity guarantees:

    |alpha|^2 - |beta|^2 = 1

With SK-EFT dissipation, the system is open (coupled to the microscopic
environment), and this relation is modified:

    |alpha|^2 - |beta|^2 = 1 - delta_k

where delta_k is the decoherence parameter measuring the probability of
phonon absorption during horizon crossing. The FDR/KMS relation mandates
an accompanying noise floor that provides a minimum occupation number.

The full occupation number is:

    n(omega) = |beta|^2 / (1 - delta_k) + n_noise(omega)

This replaces the naive |beta|^2 = 1/(exp(2*pi*omega/kappa_eff) - 1).

Lean formalization: WKBConnection.lean — modified_unitarity,
    decoherence_nonneg, noise_floor_positive, occupation_reduces_to_planck

References:
    - Lombardo, Turiaci, PRL 108, 261301 (2012) — dissipative decoherence
    - Jana, Loganayagam, Rangamani, JHEP (2020) — SK-EFT completion
    - Robertson, Parentani, PRD 92, 044043 (2015) — open quantum Hawking
    - Giacobino, Jacquet, arXiv:2512.14194 (2025) — pseudounitary scattering
"""

from dataclasses import dataclass
from typing import Optional

import numpy as np

from src.wkb.connection_formula import ConnectionResult, exact_connection_formula
from src.core.formulas import (
    decoherence_parameter,
    fdr_noise_floor,
)


# ═══════════════════════════════════════════════════════════════════
# Modified Bogoliubov coefficients
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ModifiedBogoliubov:
    """Modified Bogoliubov coefficients for the dissipative Hawking effect.

    Extends the standard Bogoliubov result with three new quantities:

    1. delta_k: Decoherence parameter (unitarity deficit)
    2. n_noise: FDR-mandated noise floor
    3. n_total: Full occupation number including all effects

    The standard result n = |beta|^2 is replaced by:
        n_total = |beta|^2 / (1 - delta_k) + n_noise

    Attributes:
        omega: Mode frequency.
        alpha_sq: |alpha|^2 (amplification coefficient).
        beta_sq: |beta|^2 (particle creation coefficient).
        delta_k: Decoherence parameter.
        n_noise: FDR noise floor.
        n_hawking: Hawking contribution = beta_sq / (1 - delta_k).
        n_total: Total occupation = n_hawking + n_noise.
        T_eff: Effective temperature extracted from the spectrum.
        unitarity_deficit: 1 - (alpha_sq - beta_sq) = delta_k.
        entanglement_degradation: Fractional reduction in Hawking pair
            entanglement due to decoherence, ~ delta_k/2.
    """
    omega: float
    alpha_sq: float
    beta_sq: float
    delta_k: float
    n_noise: float
    n_hawking: float
    n_total: float
    T_eff: float
    unitarity_deficit: float
    entanglement_degradation: float


def modified_bogoliubov_coefficients(
    conn: ConnectionResult,
    T_env: float = 0.0,
) -> ModifiedBogoliubov:
    """Compute modified Bogoliubov coefficients from the connection result.

    Given the exact WKB connection formula result (|beta/alpha|^2 and
    delta_k), computes the full set of modified Bogoliubov coefficients
    including the noise floor and total occupation number.

    The key equations:
        |beta/alpha|^2 = exp(-2*pi*omega/kappa_eff)  [from connection formula]
        |alpha|^2 - |beta|^2 = 1 - delta_k           [modified unitarity]
        n_total = |beta|^2 / (1 - delta_k) + n_noise  [full occupation]

    Lean: occupation_reduces_to_planck, modified_unitarity
          (WKBConnection.lean)

    Args:
        conn: Result from exact_connection_formula().
        T_env: Environment temperature for the noise floor.

    Returns:
        ModifiedBogoliubov with full coefficient decomposition.
    """
    omega = conn.omega
    baa = conn.beta_over_alpha_sq  # |beta/alpha|^2
    dk = min(conn.delta_k, 0.999)  # cap to avoid divergence

    # From |beta/alpha|^2 and |alpha|^2 - |beta|^2 = 1 - delta_k:
    # |alpha|^2 = (1 - delta_k) / (1 - baa)  [if baa < 1]
    # |beta|^2 = baa * |alpha|^2
    if baa < 1.0:
        alpha_sq = (1.0 - dk) / (1.0 - baa)
        beta_sq = baa * alpha_sq
    else:
        # Deep thermal regime (omega << T_H): use Planck limit
        alpha_sq = 1e10
        beta_sq = 1e10

    # Hawking contribution (corrected for unitarity deficit)
    if dk < 1.0:
        n_hawking = beta_sq / (1.0 - dk)
    else:
        n_hawking = beta_sq

    # FDR noise floor
    n_noise = fdr_noise_floor(dk, omega, T_env)

    # Total occupation
    n_total = n_hawking + n_noise

    # Effective temperature
    if omega > 0 and n_total > 0:
        T_eff = omega / np.log(1.0 + 1.0 / n_total)
    else:
        T_eff = conn.kappa_eff.kappa / (2.0 * np.pi) if conn.kappa_eff.kappa > 0 else 0.0

    # Unitarity deficit check
    unitarity_deficit = 1.0 - (alpha_sq - beta_sq)

    # Entanglement degradation: the von Neumann entropy of the reduced
    # state decreases by approximately delta_k/2 relative to the pure
    # Hawking entanglement (Lombardo-Turiaci 2012)
    entanglement_degradation = dk / 2.0

    return ModifiedBogoliubov(
        omega=omega,
        alpha_sq=alpha_sq,
        beta_sq=beta_sq,
        delta_k=dk,
        n_noise=n_noise,
        n_hawking=n_hawking,
        n_total=n_total,
        T_eff=T_eff,
        unitarity_deficit=unitarity_deficit,
        entanglement_degradation=entanglement_degradation,
    )


# ═══════════════════════════════════════════════════════════════════
# Convenience: full calculation in one call
# ═══════════════════════════════════════════════════════════════════

def compute_bogoliubov(
    omega: float,
    kappa: float,
    c_s: float,
    xi: float,
    gamma_1: float,
    gamma_2: float,
    gamma_2_1: float = 0.0,
    gamma_2_2: float = 0.0,
    gamma_3_1: float = 0.0,
    gamma_3_2: float = 0.0,
    gamma_3_3: float = 0.0,
    T_env: float = 0.0,
) -> ModifiedBogoliubov:
    """Compute modified Bogoliubov coefficients from EFT parameters.

    Convenience function that chains:
        EFT parameters → connection formula → modified Bogoliubov

    Args:
        omega: Mode frequency (> 0).
        kappa: Surface gravity.
        c_s: Sound speed.
        xi: Healing length.
        gamma_*: SK-EFT transport coefficients.
        T_env: Environment temperature.

    Returns:
        ModifiedBogoliubov with the full result.
    """
    conn = exact_connection_formula(
        omega, kappa, c_s, xi,
        gamma_1, gamma_2, gamma_2_1, gamma_2_2,
        gamma_3_1, gamma_3_2, gamma_3_3,
    )
    return modified_bogoliubov_coefficients(conn, T_env)
