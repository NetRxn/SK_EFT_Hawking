"""Tetrad and Metric Order Parameter Observables.

Defines the MC observables needed for detecting tetrad condensation
and the vestigial metric phase in lattice simulations.

Observables:
1. O_tet: Volume-averaged tetrad order parameter
2. O_met: Metric (vestigial) order parameter — connected 4-fermion correlator
3. U₄: Binder cumulant for finite-size scaling
4. C(r): Spatial correlator for composite gravitational excitations

These observables are designed for use with the existing
fermion-bag MC (src/vestigial/fermion_bag.py) and RHMC
(src/vestigial/hs_rhmc_torch.py) infrastructure.

Lean: TetradGapEquation.lean (gap_implies_full_tetrad)
"""

import numpy as np
from src.core.formulas import tetrad_bilinear


def tetrad_order_parameter(configs: np.ndarray, gammas: np.ndarray) -> float:
    """Volume-averaged tetrad order parameter.

    O_tet = (1/V) Σ_x |⟨Ê^a_μ(x)⟩|

    where Ê^a_μ(x) = ψ̄(x) γ^a ψ(x+μ̂) is the composite tetrad bilinear.

    On finite lattices, the absolute value prevents symmetry averaging to zero.

    Args:
        configs: Fermion occupation configurations [n_configs, V, n_grassmann]
        gammas: Gamma matrices [4, spinor_dim, spinor_dim]

    Returns:
        Volume-averaged tetrad order parameter
    """
    n_configs, V, n_grass = configs.shape
    # Average bilinear over configurations
    bilinear_avg = np.zeros(4)  # One component per Lorentz index a
    for a in range(4):
        bilinear_sum = 0.0
        for x in range(V):
            for mu_dir in range(4):
                y = (x + 1) % V  # Simplified: nearest neighbor
                bilinear_sum += np.mean([
                    tetrad_bilinear(
                        configs[c, x, :4], configs[c, y, :4],
                        gammas[a], np.eye(4),
                    )
                    for c in range(n_configs)
                ])
        bilinear_avg[a] = bilinear_sum / V

    return float(np.sqrt(np.sum(bilinear_avg**2)))


def metric_order_parameter(
    tetrad_sq_configs: np.ndarray,
    tetrad_avg: np.ndarray,
) -> float:
    """Metric (vestigial) order parameter.

    O_met = η_ab ⟨Ê^a_μ Ê^b_ν⟩_conn
          = η_ab (⟨Ê^a_μ Ê^b_��⟩ − ⟨Ê^a_μ⟩⟨Ê^b_ν⟩)

    Nonzero O_met with zero O_tet signals the vestigial metric phase:
    the metric g_μν = η_ab E^a_μ E^b_ν condenses while the tetrad
    itself remains disordered.

    Args:
        tetrad_sq_configs: ⟨E^a E^b⟩ per config [n_configs, 4, 4]
        tetrad_avg: ⟨E^a⟩ averaged over configs [4]

    Returns:
        Connected metric correlator (scalar: trace over μ,ν)
    """
    eta = np.diag([1.0, -1.0, -1.0, -1.0])  # Minkowski metric

    # ⟨E^a E^b⟩ averaged
    EE_avg = np.mean(tetrad_sq_configs, axis=0)

    # Disconnected part: ⟨E^a⟩⟨E^b⟩
    EE_disconnected = np.outer(tetrad_avg, tetrad_avg)

    # Connected correlator
    EE_connected = EE_avg - EE_disconnected

    # Contract with η: Tr(η · EE_conn)
    return float(np.trace(eta @ EE_connected))


def binder_cumulant(O_values: np.ndarray) -> float:
    """Binder cumulant U₄ for the tetrad order parameter.

    U₄ = 1 − ⟨O⁴⟩ / (3⟨O²⟩²)

    Properties:
    - U₄ → 2/3 in the ordered phase (O sharply peaked)
    - U₄ → 0 in the disordered phase (Gaussian O)
    - Crossing of U₄ curves for different L locates the transition

    Args:
        O_values: Array of order parameter measurements [n_measurements]

    Returns:
        Binder cumulant U₄
    """
    O2 = np.mean(O_values**2)
    O4 = np.mean(O_values**4)

    if O2 < 1e-30:
        return 0.0  # Fully disordered

    return float(1.0 - O4 / (3.0 * O2**2))


def spatial_correlator(
    bilinear_field: np.ndarray,
    L: int,
) -> np.ndarray:
    """Spatial correlator of the composite tetrad.

    C(r) = ⟨Ê^a_μ(0) Ê^a_μ(r)⟩

    If C(r) ~ 1/r² (or slower), composite gravitational excitations
    propagate — evidence for emergent gravity.
    If C(r) ~ exp(-mr), excitations are gapped at scale m.

    Args:
        bilinear_field: Tetrad bilinear field [L, L, L, L, 4] (4D lattice, 4 Lorentz)
        L: Lattice linear extent

    Returns:
        C(r) array of length L//2 (distances 0 to L//2)
    """
    max_r = L // 2
    C = np.zeros(max_r + 1)
    counts = np.zeros(max_r + 1)

    # Average over Lorentz index a and starting point
    for x0 in range(L):
        for r in range(max_r + 1):
            x1 = (x0 + r) % L
            # Correlate along the first spatial direction
            for a in range(4):
                # Average over all transverse coordinates
                for iy in range(L):
                    for iz in range(L):
                        for it in range(L):
                            C[r] += (
                                bilinear_field[x0, iy, iz, it, a]
                                * bilinear_field[x1, iy, iz, it, a]
                            )
                            counts[r] += 1

    mask = counts > 0
    C[mask] /= counts[mask]
    return C


def susceptibility_from_correlator(C: np.ndarray, L: int) -> float:
    """Susceptibility from the spatial correlator: χ = V · Σ_r C(r).

    For the tetrad channel, this is proportional to the tetrad
    susceptibility χ_tet = V⟨O²_tet⟩.

    Args:
        C: Spatial correlator C(r) [L//2 + 1]
        L: Lattice linear extent

    Returns:
        Susceptibility (unnormalized)
    """
    V = L**4
    # Sum correlator over all distances (factor 2 for symmetry, minus r=0 double-count)
    chi = C[0] + 2 * np.sum(C[1:])
    return float(V * chi)
