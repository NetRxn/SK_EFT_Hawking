"""Monte Carlo sampler for the HS-transformed bosonic tetrad model.

Samples the auxiliary (Hubbard-Stratonovich) field exp(-S_aux) where
S_aux = (1/2G) Σ_x Tr(e^T η e). This is a purely on-site action with
NO inter-site coupling and NO fermion determinant — each site is an
independent Gaussian.

This code is useful for testing infrastructure (observables, I/O, viz)
but CANNOT produce phase transitions. For physics-correct simulations
with inter-site coupling, use the fermion-bag MC in
src/vestigial/fermion_bag.py.

Reference: Sexty-Wetterich, Nucl. Phys. B 867, 290 (2013) — 2D precedent
"""

from dataclasses import dataclass, field
import numpy as np
from typing import Optional

from src.core.constants import FERMION_BAG
from src.vestigial.lattice_model import (
    LatticeParams, LatticeConfig, create_lattice,
    site_action, tetrad_order_parameter, metric_order_parameter,
)


@dataclass
class MCParams:
    """Parameters for the Monte Carlo simulation.

    Attributes:
        n_thermalize: Number of thermalization sweeps.
        n_measure: Number of measurement sweeps.
        n_skip: Sweeps between measurements (decorrelation).
        step_size: Metropolis proposal width.
        seed: Random seed for reproducibility.
    """
    n_thermalize: int = FERMION_BAG['n_thermalize']
    n_measure: int = FERMION_BAG['n_measure']
    n_skip: int = FERMION_BAG['n_skip']
    step_size: float = 0.3
    seed: Optional[int] = None


@dataclass
class MCMeasurement:
    """A single Monte Carlo measurement.

    Attributes:
        sweep: Sweep number.
        action: Total action S_aux.
        tetrad_vev: Volume-averaged tetrad magnitude.
        metric_mag: Volume-averaged metric magnitude.
        acceptance_rate: Acceptance rate for this measurement block.
        delta_S_lorentzian: S_Lorentzian - S_Euclidean for sign reweighting.
            Computed from full config: ΔS = -(1/G) Σ_x (e^0_μ)² per site.
            None if not computed.
    """
    sweep: int
    action: float
    tetrad_vev: float
    metric_mag: float
    acceptance_rate: float
    delta_S_lorentzian: Optional[float] = None


@dataclass
class MCResult:
    """Result of a Monte Carlo simulation.

    Attributes:
        lattice_params: Lattice parameters used.
        mc_params: MC parameters used.
        measurements: List of MCMeasurement.
        final_config: Final lattice configuration.
        mean_action: Ensemble average of action.
        mean_tetrad_vev: Ensemble average of tetrad VEV.
        mean_metric_mag: Ensemble average of metric magnitude.
        std_tetrad_vev: Standard deviation of tetrad VEV.
        std_metric_mag: Standard deviation of metric magnitude.
        overall_acceptance: Overall acceptance rate.
        phase_estimate: Estimated phase from the MC data.
    """
    lattice_params: LatticeParams
    mc_params: MCParams
    measurements: list[MCMeasurement]
    final_config: LatticeConfig
    mean_action: float
    mean_tetrad_vev: float
    mean_metric_mag: float
    std_tetrad_vev: float
    std_metric_mag: float
    overall_acceptance: float
    phase_estimate: str


def metropolis_sweep(config: LatticeConfig, step_size: float,
                     rng: np.random.Generator) -> tuple[LatticeConfig, float]:
    """Perform one full vectorized Metropolis sweep over the lattice.

    All sites are updated simultaneously using checkerboard decomposition:
    even sites first, then odd sites. This preserves detailed balance
    while allowing full numpy vectorization within each sublattice.

    For the on-site action S = (1/2G) Tr(e^T η e), the action change
    from e → e + δe is:
        ΔS = (1/2G) [Tr((e+δe)^T η (e+δe)) - Tr(e^T η e)]
           = (1/G) Tr(δe^T η e) + (1/2G) Tr(δe^T η δe)

    Args:
        config: Current lattice configuration.
        step_size: Width of Gaussian proposal.
        rng: Random number generator.

    Returns:
        (updated_config, acceptance_rate)
    """
    V = config.volume
    d = config.params.d
    G = config.params.G
    eta = config.params.eta
    total_accepted = 0

    # Two-pass checkerboard: even sites then odd sites
    for parity in range(2):
        # Select sublattice sites
        sites = np.arange(parity, V, 2)
        n_sites = len(sites)

        # Current tetrads for this sublattice: shape (n_sites, d, d)
        e_old = config.tetrads[sites]

        # Propose perturbations: shape (n_sites, d, d)
        delta_e = step_size * rng.standard_normal((n_sites, d, d))
        e_new = e_old + delta_e

        # Vectorized action computation: S = (1/2G) Tr(e^T η e)
        # For Euclidean η = I: Tr(e^T e) = sum of squares
        # General: Tr(e^T η e) = einsum('...ai,...ab,...bi->...', e, η, e)
        S_old = np.einsum('...ai,...ab,...bi->...', e_old, eta, e_old) / (2.0 * G)
        S_new = np.einsum('...ai,...ab,...bi->...', e_new, eta, e_new) / (2.0 * G)

        delta_S = S_new - S_old

        # Vectorized Metropolis: accept if ΔS ≤ 0 or rand < exp(-ΔS)
        rand = rng.random(size=n_sites)
        # Clip delta_S to avoid overflow in exp
        accept = (delta_S <= 0) | (rand < np.exp(np.minimum(-delta_S, 0.0)))

        # Apply accepted updates
        accept_3d = accept[:, np.newaxis, np.newaxis]  # broadcast to (n, d, d)
        config.tetrads[sites] = np.where(accept_3d, e_new, e_old)
        total_accepted += int(np.sum(accept))

    acceptance_rate = total_accepted / V
    return config, acceptance_rate


def run_monte_carlo(lattice_params: LatticeParams,
                    mc_params: MCParams) -> MCResult:
    """Run a full Monte Carlo simulation.

    1. Initialize lattice (hot start)
    2. Thermalize for n_thermalize sweeps
    3. Measure every n_skip sweeps for n_measure measurements

    Args:
        lattice_params: Lattice parameters.
        mc_params: MC parameters.

    Returns:
        MCResult with full simulation results.
    """
    seed = mc_params.seed if mc_params.seed is not None else 42
    rng = np.random.default_rng(seed)

    # Initialize with seeded RNG for reproducibility
    config = create_lattice(lattice_params, init_type="zero")
    config.tetrads = rng.standard_normal(config.tetrads.shape) * 0.5
    # Scale initial config by sqrt(G) for better starting point
    config.tetrads *= np.sqrt(lattice_params.G)

    # Thermalize
    for _ in range(mc_params.n_thermalize):
        config, _ = metropolis_sweep(config, mc_params.step_size, rng)

    # Measure
    measurements = []
    acceptance_rates = []

    for i in range(mc_params.n_measure):
        # Decorrelation sweeps
        acc_sum = 0.0
        for _ in range(mc_params.n_skip):
            config, acc = metropolis_sweep(config, mc_params.step_size, rng)
            acc_sum += acc
        avg_acc = acc_sum / mc_params.n_skip

        # Measure observables
        M_E = tetrad_order_parameter(config)
        M_g = metric_order_parameter(config)

        tetrad_mag = float(np.sqrt(np.sum(M_E**2)))
        metric_mag = float(np.sqrt(np.sum(M_g**2)))

        # Action (vectorized)
        from src.vestigial.lattice_model import auxiliary_action
        action = auxiliary_action(config)

        # Compute Euclidean→Lorentzian ΔS from full config while it's in memory.
        # S_E = (1/2G) Σ Tr(e^T e),  S_L = (1/2G) Σ Tr(e^T η_L e)  where η_L = diag(-1,1,1,1)
        # ΔS = S_L - S_E = -(1/G) Σ_x (e^0_μ(x))^2
        # tetrads shape: (V, a, μ) — index 0 on axis 1 is timelike tangent-space component
        G = lattice_params.G
        e0_sq = np.sum(config.tetrads[:, 0, :] ** 2)  # sum over all sites and μ
        delta_S_lor = -e0_sq / G if G > 0 else float('-inf')

        measurements.append(MCMeasurement(
            sweep=i,
            action=action,
            tetrad_vev=tetrad_mag,
            metric_mag=metric_mag,
            acceptance_rate=avg_acc,
            delta_S_lorentzian=float(delta_S_lor),
        ))
        acceptance_rates.append(avg_acc)

    # Compute ensemble averages
    actions = [m.action for m in measurements]
    tetrads = [m.tetrad_vev for m in measurements]
    metrics = [m.metric_mag for m in measurements]

    mean_tetrad = float(np.mean(tetrads))
    std_tetrad = float(np.std(tetrads))
    mean_metric = float(np.mean(metrics))
    std_metric = float(np.std(metrics))
    mean_action = float(np.mean(actions))

    # Phase estimate
    d = lattice_params.d
    if mean_tetrad > 0.1:
        phase_est = "full_tetrad"
    elif mean_metric > 0.1 * d:
        phase_est = "vestigial"
    else:
        phase_est = "pre_geometric"

    return MCResult(
        lattice_params=lattice_params,
        mc_params=mc_params,
        measurements=measurements,
        final_config=config,
        mean_action=mean_action,
        mean_tetrad_vev=mean_tetrad,
        mean_metric_mag=mean_metric,
        std_tetrad_vev=std_tetrad,
        std_metric_mag=std_metric,
        overall_acceptance=float(np.mean(acceptance_rates)),
        phase_estimate=phase_est,
    )
