"""Wetterich NJL fermion-bag Monte Carlo for vestigial gravity (Option C).

Gauge-link-free 4-fermion model with Fierz-complete nearest-neighbor
interaction. NO local gauge symmetry — SO(4) acts as global flavor only.
This provides an independent cross-check of vestigial gravity alongside
the ADW gauge model (Option B in fermion_bag.py).

The NJL bond action uses scalar + pseudoscalar Fierz channels:
  S_NJL = g × (n_x/N)(n_y/N) × [1 - (1 - 2n_x/N)(1 - 2n_y/N)]

Key difference from ADW (Option B):
  - No gauge links → no Weingarten integration → simpler action
  - Fierz channel structure (S+P) vs Weingarten channels (fund+adj)
  - Same lattice, same observables, same diagnostics
  - If both models show vestigial phase → cross-validation
  - If only one does → model-dependent result (still publishable)

References:
    Wetterich, PLB 901, 136223 (2024) — spinor gravity from pregeometry
    Nambu & Jona-Lasinio, PR 122, 345 (1961) — NJL model
    Fierz, Z. Phys. 104, 553 (1937) — Fierz rearrangement
"""

import numpy as np
from dataclasses import dataclass
from typing import Optional

from src.core.constants import FERMION_BAG, NJL_MODEL
from src.core.formulas import (
    njl_bond_weight_total,
    binder_cumulant, metric_correlator_connected,
    vestigial_phase_indicator,
)
from src.vestigial.lattice_4d import (
    Lattice4DParams, Lattice4DConfig, create_lattice_4d,
    site_action_4d, total_action_4d,
    tetrad_order_parameter_4d, metric_order_parameter_4d,
    staggered_tetrad_op, staggered_metric_op,
    build_neighbor_table,
)
from src.vestigial.fermion_bag import FermionBagParams, FermionBagResult


def njl_sweep(config: Lattice4DConfig,
              rng: np.random.Generator,
              g_njl: float,
              neighbor_table: np.ndarray = None) -> tuple[Lattice4DConfig, float]:
    """Perform one full vectorized Metropolis sweep with NJL bond coupling.

    The action includes on-site 8-fermion vertex + NJL nearest-neighbor:
      S = Σ_sites g_cosmo × δ_{n=8}
        + Σ_bonds S_NJL(n_x, n_y, g_njl)

    where S_NJL = g(n_x/N)(n_y/N)[1 - (1-2n_x/N)(1-2n_y/N)]
    is the scalar + pseudoscalar Fierz decomposition.

    Lean verification: njl_scalar_nonneg, njl_bond_weight_decomposition,
    njl_bond_weight_symmetric (WetterichNJL.lean, Aristotle 4528aa2b).

    Args:
        config: current lattice configuration
        rng: random number generator
        g_njl: NJL coupling constant (positive = attractive)
        neighbor_table: precomputed neighbor indices, shape (V, 8)

    Returns:
        (updated_config, acceptance_rate)
    """
    V = config.params.volume
    n_grass = config.params.n_grassmann
    g_cosmo = config.params.g_cosmo
    L = config.params.L

    if neighbor_table is None:
        neighbor_table = build_neighbor_table(L)

    # Propose new occupations for ALL sites at once
    new_occ = rng.integers(0, n_grass + 1, size=V)

    # ── On-site action change ──
    old_is_8 = (config.site_occ == 8).astype(np.float64)
    new_is_8 = (new_occ == 8).astype(np.float64)
    dS_site = g_cosmo * (new_is_8 - old_is_8)

    # ── NJL bond action change ──
    # S_NJL(x,y) = g × f_x × f_y × [1 - (1 - 2f_x)(1 - 2f_y)]
    # where f = n/N is the occupation fraction.
    N = float(n_grass)
    old_frac = config.site_occ.astype(np.float64) / N  # (V,)
    new_frac = new_occ.astype(np.float64) / N           # (V,)
    nbr_occ = config.site_occ[neighbor_table]            # (V, 8)
    nbr_frac = nbr_occ.astype(np.float64) / N           # (V, 8)

    # Scalar channel: g × f_x × f_y
    old_scalar = old_frac[:, np.newaxis] * nbr_frac      # (V, 8)
    new_scalar = new_frac[:, np.newaxis] * nbr_frac      # (V, 8)

    # Chirality factors: (1 - 2f_x)(1 - 2f_y)
    old_chiral_x = 1.0 - 2.0 * old_frac                 # (V,)
    new_chiral_x = 1.0 - 2.0 * new_frac                 # (V,)
    chiral_y = 1.0 - 2.0 * nbr_frac                     # (V, 8)

    # Pseudoscalar channel: -g × f_x × f_y × (1 - 2f_x)(1 - 2f_y)
    old_pseudo = -old_scalar * old_chiral_x[:, np.newaxis] * chiral_y  # (V, 8)
    new_pseudo = -new_scalar * new_chiral_x[:, np.newaxis] * chiral_y  # (V, 8)

    # Total NJL bond weight: scalar + pseudoscalar
    old_njl = old_scalar + old_pseudo                     # (V, 8)
    new_njl = new_scalar + new_pseudo                     # (V, 8)

    # ΔS_bonds = g_njl × Σ_neighbors [new_njl - old_njl]
    dS_bonds = g_njl * np.sum(new_njl - old_njl, axis=1)

    # ── Metropolis acceptance ──
    dS = dS_site + dS_bonds
    rand = rng.random(size=V)
    accept = (dS <= 0) | (rand < np.exp(np.minimum(-dS, 0.0)))

    # Apply accepted updates
    config.site_occ = np.where(accept, new_occ, config.site_occ)

    # Update bond occupations (integer proxy for active bonds)
    for d in range(4):
        bond_idx = np.arange(V) + V * d
        nbr = neighbor_table[:, d]
        config.bond_occ[bond_idx] = ((config.site_occ > 0) &
                                      (config.site_occ[nbr] > 0)).astype(np.int32)

    acceptance_rate = int(np.sum(accept)) / V
    return config, acceptance_rate


def run_njl_mc(params: Lattice4DParams,
               g_njl: float,
               mc_params: Optional[FermionBagParams] = None) -> FermionBagResult:
    """Run a full NJL fermion-bag Monte Carlo simulation.

    Same measurement protocol as Option B (fermion_bag.run_fermion_bag_mc)
    but with NJL bond action instead of Weingarten.

    Args:
        params: lattice parameters (g_cosmo, size)
        g_njl: NJL coupling constant (positive = attractive)
        mc_params: MC parameters (sweeps, seed)

    Returns:
        FermionBagResult with all observables and diagnostics.
    """
    if mc_params is None:
        mc_params = FermionBagParams()

    rng = np.random.default_rng(mc_params.seed)
    config = create_lattice_4d(params, rng)
    nbr_table = build_neighbor_table(params.L)

    # Thermalization
    for _ in range(mc_params.n_thermalize):
        config, _ = njl_sweep(config, rng, g_njl, nbr_table)

    # Measurement — both uniform and staggered OPs
    tetrad_values = []
    metric_values = []
    stag_tetrad_values = []
    stag_metric_values = []
    action_values = []
    acceptance_rates = []

    for _ in range(mc_params.n_measure):
        for _ in range(mc_params.n_skip):
            config, acc = njl_sweep(config, rng, g_njl, nbr_table)

        config, acc = njl_sweep(config, rng, g_njl, nbr_table)
        acceptance_rates.append(acc)

        tetrad_values.append(tetrad_order_parameter_4d(config))
        metric_values.append(metric_order_parameter_4d(config))
        stag_tetrad_values.append(staggered_tetrad_op(config))
        stag_metric_values.append(staggered_metric_op(config))
        action_values.append(total_action_4d(config))

    tetrad_arr = np.array(tetrad_values)
    metric_arr = np.array(metric_values)
    stag_t_arr = np.array(stag_tetrad_values)
    stag_m_arr = np.array(stag_metric_values)
    action_arr = np.array(action_values)

    # Uniform OP moments
    tetrad_m2 = float(np.mean(tetrad_arr ** 2))
    tetrad_m4 = float(np.mean(tetrad_arr ** 4))
    metric_m2 = float(np.mean(metric_arr ** 2))
    metric_m4 = float(np.mean(metric_arr ** 4))

    V = params.volume
    chi_t = float(V * (np.mean(tetrad_arr ** 2) - np.mean(np.abs(tetrad_arr)) ** 2))
    chi_m = float(V * (np.mean(metric_arr ** 2) - np.mean(np.abs(metric_arr)) ** 2))

    binder_t = binder_cumulant(tetrad_m2, tetrad_m4)
    binder_m = binder_cumulant(metric_m2, metric_m4)
    met_corr = metric_correlator_connected(tetrad_m2, tetrad_m4)
    phase = vestigial_phase_indicator(binder_t, binder_m)

    # Staggered OP moments (antiferromagnetic — the physically relevant OP for NJL)
    stag_m2 = float(np.mean(stag_t_arr ** 2))
    stag_m4 = float(np.mean(stag_t_arr ** 4))
    binder_stag = binder_cumulant(stag_m2, stag_m4)
    chi_stag = float(V * (np.mean(stag_t_arr ** 2) - np.mean(np.abs(stag_t_arr)) ** 2))

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
        stag_tetrad_m2=stag_m2,
        stag_tetrad_m4=stag_m4,
        binder_stag_tetrad=binder_stag,
        chi_stag_tetrad=chi_stag,
        stag_metric_mean=float(np.mean(stag_m_arr)),
    )
