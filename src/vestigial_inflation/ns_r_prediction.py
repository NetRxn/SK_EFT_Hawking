"""(n_s, r, N_e) predictions for vestigial slow-roll inflation.

Standard slow-roll relations at horizon-crossing τ_*:
    n_s = 1 - 6ε(τ_*) + 2η(τ_*)
    r   = 16 ε(τ_*)
    N_e(τ_*) = (1/M̄_P²) · ∫_{τ_end}^{τ_*} V/V_φ dφ

with τ_end determined by ε(τ_end) = 1.

Microscopic parameter set per Phase6b_Roadmap.md §201:
    (Λ_UV, N_f, T_c,vest)
mapped to the inflaton-sector dimensional parameters via:
    f_0 = π · N_* · T_c,vest² · Λ_UV² / 4    [GL free-energy ansatz]
    M_φ = T_c,vest                            [natural inflaton mass scale]

For the preliminary Stage 3a scan we treat (f_0, M_φ) as the effective
parameters, with microscopic anchors flagged in `ScanResult.microscopic_origin`.
"""

import dataclasses
import numpy as np

from .slow_roll import (
    vestigial_potential,
    vestigial_potential_derivative,
    slow_roll_epsilon,
    slow_roll_eta,
)


VEST_TAU_LOWER = 1.0 / np.sqrt(5)        # ≈ 0.4472, V > 0 begins
VEST_TAU_HILLTOP = np.sqrt(3.0 / 5.0)    # ≈ 0.7746, V_max = 4 f_0 / 5
VEST_TAU_UPPER = 1.0                     # V → 0 from above


def n_s_vestigial(tau, f0, M_Pl_red, M_phi):
    """Scalar spectral index at horizon-crossing τ_*."""
    eps = slow_roll_epsilon(tau, f0, M_Pl_red, M_phi)
    eta = slow_roll_eta(tau, f0, M_Pl_red, M_phi)
    return 1.0 - 6.0 * eps + 2.0 * eta


def r_vestigial(tau, f0, M_Pl_red, M_phi):
    """Tensor-to-scalar ratio at horizon-crossing τ_*."""
    return 16.0 * slow_roll_epsilon(tau, f0, M_Pl_red, M_phi)


def e_folds_vestigial(tau_star, f0, M_Pl_red, M_phi, n_quad=2001):
    """Number of e-folds N_e from τ_end (where ε=1) back to τ_*.

    N_e = (M_φ² / M̄_P²) · ∫_{τ_end}^{τ_*} V(τ)/V'(τ) dτ.
    """
    if not (VEST_TAU_LOWER < tau_star < VEST_TAU_UPPER):
        return -np.inf

    # Find τ_end ∈ (τ_*, 1) where ε(τ_end) = 1 (descending from hilltop).
    # If τ_* is on the descending limb (τ_* > hilltop), τ_end > τ_*.
    # If τ_* is on the ascending limb (τ_* < hilltop), τ_end < τ_*.
    descending = tau_star > VEST_TAU_HILLTOP
    if descending:
        tau_search = np.linspace(tau_star, VEST_TAU_UPPER - 1e-6, n_quad)
    else:
        tau_search = np.linspace(VEST_TAU_LOWER + 1e-6, tau_star, n_quad)
    eps_vals = np.array([slow_roll_epsilon(t, f0, M_Pl_red, M_phi) for t in tau_search])
    finite = np.isfinite(eps_vals)
    if not np.any(eps_vals[finite] >= 1.0):
        return np.inf  # slow-roll never breaks; eternal inflation regime
    idx = int(np.argmax(eps_vals >= 1.0))
    tau_end = tau_search[idx]

    # Integrate (M_φ²/M̄_P²) · ∫ V/V' dτ between τ_* and τ_end (with sign).
    if descending:
        taus = np.linspace(tau_star, tau_end, n_quad)
    else:
        taus = np.linspace(tau_end, tau_star, n_quad)
    V = np.array([vestigial_potential(t, f0) for t in taus])
    Vp = np.array([vestigial_potential_derivative(t, f0) for t in taus])
    safe = (V > 0) & (np.abs(Vp) > 0)
    if not np.any(safe):
        return -np.inf
    integrand = V[safe] / Vp[safe]
    # Sign: descending leg has Vp < 0, V > 0 ⇒ integrand < 0; integral
    # from τ_* (lower) to τ_end (upper) is negative ⇒ flip sign for N_e > 0.
    N = np.trapezoid(integrand, taus[safe])
    prefactor = (M_phi / M_Pl_red) ** 2
    return float(np.abs(prefactor * N))


@dataclasses.dataclass(frozen=True)
class ScanPoint:
    f0_over_MPl4: float
    Mphi_over_MPl: float
    tau_star: float
    n_s: float
    r: float
    N_e: float
    epsilon: float
    eta: float

    @property
    def viable(self) -> bool:
        return (
            np.isfinite(self.n_s)
            and np.isfinite(self.r)
            and np.isfinite(self.N_e)
            and 0.95 < self.n_s < 0.98
            and 0.0 < self.r < 0.036
            and 50.0 < self.N_e < 65.0
        )


def scan_microscopic_grid(
    f0_grid, Mphi_grid, tau_grid, M_Pl_red=2.435e18,
):
    """Scan (f_0, M_φ, τ_*) and return list of ScanPoint."""
    points = []
    for f0 in f0_grid:
        for Mphi in Mphi_grid:
            for tau_star in tau_grid:
                if not (VEST_TAU_LOWER < tau_star < VEST_TAU_UPPER):
                    continue
                eps = slow_roll_epsilon(tau_star, f0, M_Pl_red, Mphi)
                eta = slow_roll_eta(tau_star, f0, M_Pl_red, Mphi)
                ns = 1.0 - 6.0 * eps + 2.0 * eta
                rt = 16.0 * eps
                Ne = e_folds_vestigial(tau_star, f0, M_Pl_red, Mphi)
                points.append(ScanPoint(
                    f0_over_MPl4=f0 / M_Pl_red ** 4,
                    Mphi_over_MPl=Mphi / M_Pl_red,
                    tau_star=tau_star,
                    n_s=ns,
                    r=rt,
                    N_e=Ne,
                    epsilon=eps,
                    eta=eta,
                ))
    return points
