"""SO(4) gauge-link infrastructure for 4D hypercubic lattice.

SO(4) ≅ (SU(2)_L × SU(2)_R)/Z_2 is stored as pairs of unit quaternions.
Each directed link (x, μ) carries (q_L, q_R) with 8 floats total.

Provides:
- Lattice link storage and initialization
- Plaquette computation via quaternion products
- Staple sum for heatbath updates
- Kennedy-Pendleton heatbath for each SU(2) factor
- Overrelaxation (microcanonical reflection)
- Pure gauge Monte Carlo for validation

References:
    Wilson, PRD 10, 2445 (1974) — plaquette action
    Kennedy & Pendleton, PLB 156, 393 (1985) — SU(2) heatbath
    Creutz, "Quarks, Gluons and Lattices" (1983) — lattice gauge theory
"""

import numpy as np
from dataclasses import dataclass, field

from src.core.constants import SO4_LATTICE, GAUGE_LINK_MC
from src.core.formulas import quaternion_multiply, wilson_plaquette_action
from src.vestigial.quaternion import (
    conjugate, normalize, trace, identity, haar_random,
    kennedy_pendleton_heatbath, norm_sq,
)


@dataclass
class GaugeLattice:
    """4D hypercubic lattice with SO(4) gauge links.

    Links are stored as pairs of SU(2) quaternions (q_L, q_R).
    Shape: links_L[x0, x1, x2, x3, mu, 4] and links_R[same].

    Attributes:
        L: linear lattice size (L^4 sites)
        links_L: left SU(2) quaternions, shape (L, L, L, L, 4, 4)
        links_R: right SU(2) quaternions, shape (L, L, L, L, 4, 4)
    """
    L: int
    links_L: np.ndarray  # shape (L, L, L, L, 4, 4)
    links_R: np.ndarray  # shape (L, L, L, L, 4, 4)


def create_gauge_lattice(L, rng, cold_start=False):
    """Create a gauge lattice with initial link configuration.

    Args:
        L: linear lattice size
        rng: numpy random Generator
        cold_start: if True, all links = identity (ordered start)

    Returns:
        GaugeLattice with initialized links
    """
    shape = (L, L, L, L, 4)  # sites × 4 directions
    if cold_start:
        links_L = np.zeros((*shape, 4))
        links_L[..., 0] = 1.0  # identity quaternion
        links_R = np.zeros((*shape, 4))
        links_R[..., 0] = 1.0
    else:
        links_L = haar_random(rng, shape)
        links_R = haar_random(rng, shape)

    return GaugeLattice(L=L, links_L=links_L, links_R=links_R)


def _shift(arr, mu, direction=+1):
    """Shift array by ±1 in direction mu with periodic BC.

    Args:
        arr: array with first 4 axes being lattice coordinates
        mu: direction (0-3)
        direction: +1 for forward, -1 for backward

    Returns:
        Shifted array (same shape)
    """
    return np.roll(arr, -direction, axis=mu)


def plaquette_trace(lattice, x, mu, nu):
    """Compute Tr(U_P) for the plaquette in the (mu, nu) plane at site x.

    U_P = U(x,μ) · U(x+μ̂,ν) · U†(x+ν̂,μ) · U†(x,ν)

    For SO(4) via quaternions: the fundamental rep is (2,2) under
    SU(2)_L × SU(2)_R, so traces factorize:

    Tr₄(U_P) = Tr₂(q_L^P) · Tr₂(q_R^P)
    where q_L^P = q_L(x,μ)·q_L(x+μ̂,ν)·conj(q_L(x+ν̂,μ))·conj(q_L(x,ν))

    At identity: Tr₂(I) = 2, so Tr₄(I) = 2·2 = 4. ✓

    Args:
        lattice: GaugeLattice
        x: site coordinates as tuple (x0, x1, x2, x3)
        mu, nu: plaquette directions (0-3, mu ≠ nu)

    Returns:
        Tr(U_P) — real number in [-4, 4]
    """
    L = lattice.L

    # Site coordinates with periodic BC
    x_mu = list(x)
    x_mu[mu] = (x_mu[mu] + 1) % L
    x_mu = tuple(x_mu)

    x_nu = list(x)
    x_nu[nu] = (x_nu[nu] + 1) % L
    x_nu = tuple(x_nu)

    # Left SU(2) plaquette product: q1 · q2 · q3† · q4†
    q1_L = lattice.links_L[x + (mu,)]
    q2_L = lattice.links_L[x_mu + (nu,)]
    q3_L = conjugate(lattice.links_L[x_nu + (mu,)])
    q4_L = conjugate(lattice.links_L[x + (nu,)])
    plaq_L = quaternion_multiply(
        quaternion_multiply(q1_L, q2_L),
        quaternion_multiply(q3_L, q4_L)
    )

    # Right SU(2) plaquette product
    q1_R = lattice.links_R[x + (mu,)]
    q2_R = lattice.links_R[x_mu + (nu,)]
    q3_R = conjugate(lattice.links_R[x_nu + (mu,)])
    q4_R = conjugate(lattice.links_R[x + (nu,)])
    plaq_R = quaternion_multiply(
        quaternion_multiply(q1_R, q2_R),
        quaternion_multiply(q3_R, q4_R)
    )

    # SO(4) fundamental = (2,2) under SU(2)_L × SU(2)_R
    # Tr₄(R) = Tr₂(q_L) × Tr₂(q_R) = (2a₀^L)(2a₀^R)
    # At identity: Tr₄(I) = 2·2 = 4. ✓
    return trace(plaq_L) * trace(plaq_R)


def average_plaquette(lattice):
    """Compute the average plaquette ⟨(1/4)Tr(U_P)⟩ over all plaquettes.

    For a random (hot) lattice, ⟨P⟩ ≈ 0.
    For an ordered (cold) lattice, ⟨P⟩ = 1.

    Args:
        lattice: GaugeLattice

    Returns:
        Average plaquette value in [−1, 1]
    """
    L = lattice.L
    total = 0.0
    count = 0
    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    x = (x0, x1, x2, x3)
                    for mu in range(4):
                        for nu in range(mu + 1, 4):
                            total += plaquette_trace(lattice, x, mu, nu) / 4.0
                            count += 1
    return total / count


def staple_sum(lattice, x, mu):
    """Compute the staple sum for link (x, μ).

    The staple for plaquette (μ, ν) is the product of the other 3 links:
    V_ν = U(x+μ̂,ν) · U†(x+ν̂,μ) · U†(x,ν)  (forward staple)
        + U†(x+μ̂−ν̂,ν) · U†(x−ν̂,μ) · U(x−ν̂,ν)  (backward staple)

    Computes both forward and backward staples (6 total for d=4, 3 forward + 3 backward).
    The full staple sum V = Σ_ν V_ν is what enters the heatbath.

    Returns separate L and R staple sums for the quaternion decomposition.

    Args:
        lattice: GaugeLattice
        x: site coordinates tuple
        mu: link direction

    Returns:
        (V_L, V_R) — staple sum quaternions for SU(2)_L and SU(2)_R
    """
    L = lattice.L
    V_L = np.zeros(4)
    V_R = np.zeros(4)

    x_mu = list(x)
    x_mu[mu] = (x_mu[mu] + 1) % L
    x_mu = tuple(x_mu)

    for nu in range(4):
        if nu == mu:
            continue

        x_nu = list(x)
        x_nu[nu] = (x_nu[nu] + 1) % L
        x_nu = tuple(x_nu)

        x_mu_bnu = list(x_mu)
        x_mu_bnu[nu] = (x_mu_bnu[nu] - 1) % L
        x_mu_bnu = tuple(x_mu_bnu)

        x_bnu = list(x)
        x_bnu[nu] = (x_bnu[nu] - 1) % L
        x_bnu = tuple(x_bnu)

        # Forward staple: U(x+μ̂,ν) · U†(x+ν̂,μ) · U†(x,ν)
        s_L = quaternion_multiply(
            lattice.links_L[x_mu + (nu,)],
            quaternion_multiply(
                conjugate(lattice.links_L[x_nu + (mu,)]),
                conjugate(lattice.links_L[x + (nu,)])
            )
        )
        s_R = quaternion_multiply(
            lattice.links_R[x_mu + (nu,)],
            quaternion_multiply(
                conjugate(lattice.links_R[x_nu + (mu,)]),
                conjugate(lattice.links_R[x + (nu,)])
            )
        )
        V_L += s_L
        V_R += s_R

        # Backward staple: U†(x+μ̂−ν̂,ν) · U†(x−ν̂,μ) · U(x−ν̂,ν)
        sb_L = quaternion_multiply(
            conjugate(lattice.links_L[x_mu_bnu + (nu,)]),
            quaternion_multiply(
                conjugate(lattice.links_L[x_bnu + (mu,)]),
                lattice.links_L[x_bnu + (nu,)]
            )
        )
        sb_R = quaternion_multiply(
            conjugate(lattice.links_R[x_mu_bnu + (nu,)]),
            quaternion_multiply(
                conjugate(lattice.links_R[x_bnu + (mu,)]),
                lattice.links_R[x_bnu + (nu,)]
            )
        )
        V_L += sb_L
        V_R += sb_R

    return V_L, V_R


def gauge_heatbath_sweep(lattice, beta, rng):
    """One heatbath sweep over all links.

    For each link, compute the staple sum V, then sample the new link
    from the distribution P(U) ∝ exp(β/4 · Tr(U·V†)) using the
    Kennedy-Pendleton algorithm for each SU(2) factor independently.

    Args:
        lattice: GaugeLattice (modified in place)
        beta: Wilson plaquette coupling
        rng: numpy random Generator

    Returns:
        Average acceptance (always 1.0 for heatbath — no reject step)
    """
    L = lattice.L

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    x = (x0, x1, x2, x3)
                    for mu in range(4):
                        V_L, V_R = staple_sum(lattice, x, mu)

                        # Effective coupling for each SU(2) factor
                        k_L = np.sqrt(norm_sq(V_L)) / 2.0
                        k_R = np.sqrt(norm_sq(V_R)) / 2.0

                        if beta < 1e-10:
                            # Pure ADW (β=0): Haar random links
                            lattice.links_L[x + (mu,)] = haar_random(rng)
                            lattice.links_R[x + (mu,)] = haar_random(rng)
                        else:
                            # Kennedy-Pendleton heatbath for SU(2)_L
                            a_L = beta * k_L / 2.0  # factor of 2 from Tr convention
                            q_new_L = kennedy_pendleton_heatbath(a_L, rng)
                            # Transform to correct frame: q_new · V†/|V|
                            if k_L > 1e-10:
                                V_L_norm = V_L / (2.0 * k_L)
                                lattice.links_L[x + (mu,)] = quaternion_multiply(
                                    q_new_L, conjugate(V_L_norm)
                                )
                            else:
                                lattice.links_L[x + (mu,)] = haar_random(rng)

                            # Kennedy-Pendleton heatbath for SU(2)_R
                            a_R = beta * k_R / 2.0
                            q_new_R = kennedy_pendleton_heatbath(a_R, rng)
                            if k_R > 1e-10:
                                V_R_norm = V_R / (2.0 * k_R)
                                lattice.links_R[x + (mu,)] = quaternion_multiply(
                                    q_new_R, conjugate(V_R_norm)
                                )
                            else:
                                lattice.links_R[x + (mu,)] = haar_random(rng)

    return 1.0  # heatbath always accepts


def gauge_overrelax_sweep(lattice, rng):
    """One overrelaxation sweep: microcanonical reflection for each link.

    For each link U with staple V, the overrelaxation update is:
    U_new = V†/|V| · U† · V†/|V|  (reflection through staple direction)

    This preserves the gauge action exactly but decorrelates the
    configuration faster than heatbath alone.

    Args:
        lattice: GaugeLattice (modified in place)
        rng: numpy random Generator (unused — deterministic update)
    """
    L = lattice.L

    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    x = (x0, x1, x2, x3)
                    for mu in range(4):
                        V_L, V_R = staple_sum(lattice, x, mu)
                        k_L = np.sqrt(norm_sq(V_L))
                        k_R = np.sqrt(norm_sq(V_R))

                        # SU(2)_L overrelaxation
                        if k_L > 1e-10:
                            V0_L = V_L / k_L
                            q_old_L = lattice.links_L[x + (mu,)]
                            lattice.links_L[x + (mu,)] = quaternion_multiply(
                                conjugate(V0_L),
                                quaternion_multiply(conjugate(q_old_L), conjugate(V0_L))
                            )

                        # SU(2)_R overrelaxation
                        if k_R > 1e-10:
                            V0_R = V_R / k_R
                            q_old_R = lattice.links_R[x + (mu,)]
                            lattice.links_R[x + (mu,)] = quaternion_multiply(
                                conjugate(V0_R),
                                quaternion_multiply(conjugate(q_old_R), conjugate(V0_R))
                            )


def renormalize_links(lattice):
    """Renormalize all link quaternions to unit norm.

    Corrects floating-point drift accumulated during sweeps.
    Should be called every ~50 sweeps.

    Args:
        lattice: GaugeLattice (modified in place)
    """
    lattice.links_L = normalize(lattice.links_L)
    lattice.links_R = normalize(lattice.links_R)


@dataclass
class PureGaugeResult:
    """Results from a pure gauge Monte Carlo run."""
    beta: float
    L: int
    avg_plaquette: list = field(default_factory=list)
    n_sweeps: int = 0


def run_pure_gauge_mc(L, beta, n_therm, n_measure, n_skip, n_overrelax, rng,
                      cold_start=False):
    """Run pure gauge SO(4) Monte Carlo.

    This is the validation benchmark: the average plaquette vs β for
    pure SO(4) should match two independent SU(2) theories:
    ⟨P⟩_{SO(4)} = [⟨P⟩_{SU(2)}(β/2)]² (in decomposed action).

    Args:
        L: lattice size
        beta: Wilson coupling
        n_therm: thermalization sweeps
        n_measure: measurement sweeps
        n_skip: sweeps between measurements
        n_overrelax: overrelaxation sweeps per heatbath sweep
        rng: numpy random Generator
        cold_start: start from ordered configuration

    Returns:
        PureGaugeResult with average plaquette measurements
    """
    lattice = create_gauge_lattice(L, rng, cold_start=cold_start)
    result = PureGaugeResult(beta=beta, L=L)

    total_sweeps = n_therm + n_measure * n_skip

    for sweep in range(total_sweeps):
        gauge_heatbath_sweep(lattice, beta, rng)
        for _ in range(n_overrelax):
            gauge_overrelax_sweep(lattice, rng)

        # Renormalize periodically
        if sweep % GAUGE_LINK_MC['quaternion_renorm_interval'] == 0:
            renormalize_links(lattice)

        # Measure after thermalization
        if sweep >= n_therm and (sweep - n_therm) % n_skip == 0:
            plaq = average_plaquette(lattice)
            result.avg_plaquette.append(plaq)

    result.n_sweeps = total_sweeps
    return result
