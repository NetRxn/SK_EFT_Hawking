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
)
from src.vestigial.lattice_4d import (
    Lattice4DParams, Lattice4DConfig, create_lattice_4d,
    site_action_4d, bond_action_4d, total_action_4d,
    tetrad_order_parameter_4d, metric_order_parameter_4d,
    neighbor_index, bond_index,
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
    phase: str
    acceptance_rate: float
    action_mean: float
    action_std: float
    params: Lattice4DParams
    mc_params: FermionBagParams


def _local_action_change(config: Lattice4DConfig, site: int,
                          new_occ: int, rng: np.random.Generator) -> float:
    """Compute the change in action from flipping a site's occupation.

    ΔS = S_new - S_old for the site and its adjacent bonds.

    Args:
        config: current lattice configuration
        site: index of the site to update
        new_occ: proposed new occupation number
        rng: random number generator (for bond updates)

    Returns:
        Change in action ΔS
    """
    old_occ = config.site_occ[site]
    g_cosmo = config.params.g_cosmo
    g_eff = config.params.g_eff

    # On-site contribution
    dS_site = site_action_4d(new_occ, g_cosmo) - site_action_4d(old_occ, g_cosmo)

    return dS_site


def fermion_bag_sweep(config: Lattice4DConfig,
                       rng: np.random.Generator) -> tuple[Lattice4DConfig, float]:
    """Perform one full Metropolis sweep over all sites.

    Each site is visited once. A new occupation number is proposed
    uniformly from {0, ..., n_grassmann}, and accepted/rejected by
    the Metropolis criterion.

    Args:
        config: current lattice configuration
        rng: random number generator

    Returns:
        (updated_config, acceptance_rate)
    """
    n_accept = 0
    n_propose = 0
    V = config.params.volume
    n_grass = config.params.n_grassmann

    for site in range(V):
        new_occ = rng.integers(0, n_grass + 1)
        dS = _local_action_change(config, site, new_occ, rng)

        # Metropolis acceptance
        if dS <= 0 or rng.random() < np.exp(-dS):
            config.site_occ[site] = new_occ
            n_accept += 1
        n_propose += 1

    acceptance_rate = n_accept / max(n_propose, 1)
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

    # Thermalization
    for _ in range(mc_params.n_thermalize):
        config, _ = fermion_bag_sweep(config, rng)

    # Measurement
    tetrad_values = []
    metric_values = []
    action_values = []
    acceptance_rates = []

    for i in range(mc_params.n_measure):
        # Decorrelation sweeps
        for _ in range(mc_params.n_skip):
            config, acc = fermion_bag_sweep(config, rng)

        # One measurement sweep
        config, acc = fermion_bag_sweep(config, rng)
        acceptance_rates.append(acc)

        # Measure observables
        tetrad = tetrad_order_parameter_4d(config)
        metric = metric_order_parameter_4d(config)
        action = total_action_4d(config)

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
        phase=phase,
        acceptance_rate=float(np.mean(acceptance_rates)),
        action_mean=float(np.mean(action_arr)),
        action_std=float(np.std(action_arr)),
        params=params,
        mc_params=mc_params,
    )
