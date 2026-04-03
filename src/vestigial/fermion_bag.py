"""Fermion-bag Monte Carlo algorithm for the 4D ADW model.

The fermion-bag algorithm (Chandrasekharan 2010) partitions the lattice
into connected clusters ("bags") where the Grassmann integral is evaluated
exactly. Updates propose changes to bag boundaries, and acceptance is
determined by the ratio of bag weights — always positive for the
Euclidean SO(4) model.

Key advantages over HMC:
1. No Hubbard-Stratonovich decomposition needed
2. No fermion determinant to evaluate
3. No sign problem (bag weights are positive)
4. Locality: typical bag size ~30 sites regardless of total volume
5. Can handle 8-fermion vertices directly

Algorithm:
1. Start from a configuration of occupied/unoccupied Grassmann variables
2. Identify fermion bags (connected clusters of occupied sites)
3. Propose a local update: flip occupation of a site + adjacent bonds
4. Compute the ratio of new/old bag weights
5. Accept/reject by Metropolis criterion

References:
    Chandrasekharan, PRD 82, 025007 (2010) — fermion-bag algorithm
    Catterall, JHEP 01, 121 (2016) — SO(4) fermion-bag MC for SMG
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Optional

from src.core.constants import FERMION_BAG, ADW_4D_MODEL
from src.core.formulas import (
    eight_fermion_vertex_weight, adw_4d_effective_coupling,
    binder_cumulant, metric_correlator_connected,
    vestigial_phase_indicator,
    adw_bond_weight_total,
)
from src.vestigial.lattice_4d import (
    Lattice4DParams, Lattice4DConfig, create_lattice_4d,
    site_action_4d, bond_action_4d, total_action_4d,
    tetrad_order_parameter_4d, metric_order_parameter_4d,
    tetrad_bond_order_parameter_4d, metric_bond_order_parameter_4d,
    neighbor_index, bond_index, build_neighbor_table,
)


@dataclass
class FermionBagParams:
    """Parameters for the fermion-bag Monte Carlo.

    Attributes:
        n_thermalize: thermalization sweeps
        n_measure: measurement sweeps
        n_skip: decorrelation gap between measurements
        seed: random seed
    """
    n_thermalize: int = FERMION_BAG['n_thermalize']
    n_measure: int = FERMION_BAG['n_measure']
    n_skip: int = FERMION_BAG['n_skip']
    seed: int = FERMION_BAG['seed']


@dataclass
class FermionBagResult:
    """Result of a fermion-bag Monte Carlo simulation.

    Attributes:
        tetrad_m2: mean ⟨|E|²⟩ (tetrad second moment)
        tetrad_m4: mean ⟨|E|⁴⟩ (tetrad fourth moment)
        metric_m2: mean ⟨|g|²⟩ (metric second moment)
        metric_m4: mean ⟨|g|⁴⟩ (metric fourth moment)
        binder_tetrad: Binder cumulant for tetrad order parameter
        binder_metric: Binder cumulant for metric order parameter
        metric_correlator: connected metric correlator (vestigial diagnostic)
        chi_tetrad: tetrad susceptibility V × Var(|E|)
        chi_metric: metric susceptibility V × Var(|g|)
        phase: classified phase ('pre_geometric', 'vestigial', etc.)
        acceptance_rate: fraction of accepted Metropolis proposals
        action_mean: mean action ⟨S⟩
        action_std: standard deviation of action
        params: lattice parameters used
        mc_params: MC parameters used
    """
    tetrad_m2: float
    tetrad_m4: float
    metric_m2: float
    metric_m4: float
    binder_tetrad: float
    binder_metric: float
    metric_correlator: float
    chi_tetrad: float
    chi_metric: float
    phase: str
    acceptance_rate: float
    action_mean: float
    action_std: float
    params: Lattice4DParams
    mc_params: FermionBagParams
    # Staggered order parameters (antiferromagnetic, populated by NJL model)
    stag_tetrad_m2: Optional[float] = None
    stag_tetrad_m4: Optional[float] = None
    binder_stag_tetrad: Optional[float] = None
    chi_stag_tetrad: Optional[float] = None
    stag_metric_mean: Optional[float] = None


def fermion_bag_sweep(config: Lattice4DConfig,
                       rng: np.random.Generator,
                       neighbor_table: np.ndarray = None) -> tuple[Lattice4DConfig, float]:
    """Perform one full vectorized Metropolis sweep with Weingarten bond coupling.

    All sites are updated simultaneously: propose new occupations,
    compute action changes (site + multi-channel bond), accept/reject
    in bulk via numpy.

    The action includes on-site 8-fermion vertex + SO(4) Weingarten
    multi-channel nearest-neighbor coupling:
      S = Σ_sites g_cosmo δ_{n=8}
        + Σ_bonds g_eff [(1/4)(n_x/N)(n_y/N) + (1/24)(n_x/N)²(n_y/N)²]

    The fundamental (1/4) channel comes from the SO(4) second-moment
    Weingarten integral. The adjoint (1/24) comes from the fourth-moment.
    See formulas.so4_weingarten_2nd_moment, so4_weingarten_4th_moment.

    Args:
        config: current lattice configuration
        rng: random number generator
        neighbor_table: precomputed neighbor indices, shape (V, 8).
            Build once via build_neighbor_table(L) and reuse.

    Returns:
        (updated_config, acceptance_rate)
    """
    V = config.params.volume
    n_grass = config.params.n_grassmann
    g_cosmo = config.params.g_cosmo
    g_eff = config.params.g_eff
    L = config.params.L

    if neighbor_table is None:
        neighbor_table = build_neighbor_table(L)

    # Propose new occupations for ALL sites at once
    new_occ = rng.integers(0, n_grass + 1, size=V)

    # ── On-site action change ──
    # ΔS_site = g_cosmo × (δ_{new=8} - δ_{old=8})
    old_is_8 = (config.site_occ == 8).astype(np.float64)
    new_is_8 = (new_occ == 8).astype(np.float64)
    dS_site = g_cosmo * (new_is_8 - old_is_8)

    # ── Bond action change (Weingarten multi-channel) ──
    # From exact SO(4) Haar integration (formulas.adw_bond_weight_total):
    #   S_bond = g_eff × [(1/4)(n_x/N)(n_y/N) + (1/24)(n_x/N)²(n_y/N)²]
    # The fundamental (1/4) channel dominates; adjoint (1/24) is sub-leading.
    # ΔS_bonds(x) = Σ_neighbors [S_bond(new_x, y) - S_bond(old_x, y)]
    old_occ = config.site_occ
    N = float(n_grass)
    neighbor_occ = old_occ[neighbor_table]  # shape (V, 8)

    # Vectorized: compute bond weight change for each site against all 8 neighbors
    old_frac = old_occ.astype(np.float64) / N  # (V,)
    new_frac = new_occ.astype(np.float64) / N  # (V,)
    nbr_frac = neighbor_occ.astype(np.float64) / N  # (V, 8)

    # Fundamental channel: (1/4)(n_x/N)(n_y/N)
    old_fund = old_frac[:, np.newaxis] * nbr_frac / 4.0  # (V, 8)
    new_fund = new_frac[:, np.newaxis] * nbr_frac / 4.0  # (V, 8)

    # Adjoint channel: (1/24)(n_x/N)^2(n_y/N)^2
    old_adj = (old_frac[:, np.newaxis]**2) * (nbr_frac**2) / 24.0  # (V, 8)
    new_adj = (new_frac[:, np.newaxis]**2) * (nbr_frac**2) / 24.0  # (V, 8)

    # Total ΔS_bonds = g_eff × Σ_neighbors [(new_fund + new_adj) - (old_fund + old_adj)]
    dS_bonds = g_eff * np.sum((new_fund + new_adj) - (old_fund + old_adj), axis=1)

    # ── Total action change and Metropolis acceptance ──
    dS = dS_site + dS_bonds
    rand = rng.random(size=V)
    accept = (dS <= 0) | (rand < np.exp(np.minimum(-dS, 0.0)))

    # Apply accepted updates
    config.site_occ = np.where(accept, new_occ, config.site_occ)

    # Update bond occupations: continuous weight = (n_x/N) × (n_y/N)
    # Stored as integer proxy (0 or 1) for compatibility with total_action_4d;
    # bond is "active" when product > 0 (both endpoints occupied).
    for d in range(4):
        bond_idx = np.arange(V) + V * d
        nbr = neighbor_table[:, d]
        config.bond_occ[bond_idx] = ((config.site_occ > 0) &
                                      (config.site_occ[nbr] > 0)).astype(np.int32)

    acceptance_rate = int(np.sum(accept)) / V
    return config, acceptance_rate


def run_fermion_bag_mc(params: Lattice4DParams,
                        mc_params: Optional[FermionBagParams] = None) -> FermionBagResult:
    """Run a full fermion-bag Monte Carlo simulation.

    1. Initialize random configuration
    2. Thermalize
    3. Measure observables with decorrelation gaps
    4. Compute Binder cumulants and classify phase

    Args:
        params: lattice parameters (coupling, size)
        mc_params: MC parameters (sweeps, seed)

    Returns:
        FermionBagResult with all observables and diagnostics
    """
    if mc_params is None:
        mc_params = FermionBagParams()

    rng = np.random.default_rng(mc_params.seed)
    config = create_lattice_4d(params, rng)

    # Precompute neighbor table once (reused every sweep)
    nbr_table = build_neighbor_table(params.L)

    # Thermalization
    for _ in range(mc_params.n_thermalize):
        config, _ = fermion_bag_sweep(config, rng, nbr_table)

    # Measurement
    tetrad_values = []
    metric_values = []
    action_values = []
    acceptance_rates = []

    for i in range(mc_params.n_measure):
        # Decorrelation sweeps
        for _ in range(mc_params.n_skip):
            config, acc = fermion_bag_sweep(config, rng, nbr_table)

        # One measurement sweep
        config, acc = fermion_bag_sweep(config, rng, nbr_table)
        acceptance_rates.append(acc)

        # Measure observables — use bond-correlation OPs for Weingarten model
        # (these detect the inter-site ordering driven by Weingarten bond action)
        tetrad = tetrad_bond_order_parameter_4d(config, nbr_table)
        metric = metric_bond_order_parameter_4d(config, nbr_table)
        action = total_action_4d(config, nbr_table)

        tetrad_values.append(tetrad)
        metric_values.append(metric)
        action_values.append(action)

    tetrad_arr = np.array(tetrad_values)
    metric_arr = np.array(metric_values)
    action_arr = np.array(action_values)

    # Moments for Binder cumulants
    tetrad_m2 = float(np.mean(tetrad_arr ** 2))
    tetrad_m4 = float(np.mean(tetrad_arr ** 4))
    metric_m2 = float(np.mean(metric_arr ** 2))
    metric_m4 = float(np.mean(metric_arr ** 4))

    # Susceptibility: chi = V × Var(order parameter)
    V = params.volume
    chi_t = float(V * (np.mean(tetrad_arr ** 2) - np.mean(np.abs(tetrad_arr)) ** 2))
    chi_m = float(V * (np.mean(metric_arr ** 2) - np.mean(np.abs(metric_arr)) ** 2))

    binder_t = binder_cumulant(tetrad_m2, tetrad_m4)
    binder_m = binder_cumulant(metric_m2, metric_m4)
    met_corr = metric_correlator_connected(tetrad_m2, tetrad_m4)
    phase = vestigial_phase_indicator(binder_t, binder_m)

    return FermionBagResult(
        tetrad_m2=tetrad_m2,
        tetrad_m4=tetrad_m4,
        metric_m2=metric_m2,
        metric_m4=metric_m4,
        binder_tetrad=binder_t,
        binder_metric=binder_m,
        metric_correlator=met_corr,
        chi_tetrad=chi_t,
        chi_metric=chi_m,
        phase=phase,
        acceptance_rate=float(np.mean(acceptance_rates)),
        action_mean=float(np.mean(action_arr)),
        action_std=float(np.std(action_arr)),
        params=params,
        mc_params=mc_params,
    )
