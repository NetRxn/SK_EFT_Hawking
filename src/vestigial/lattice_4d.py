"""4D hypercubic lattice model for the ADW fermion-bag Monte Carlo.

Implements the purely fermionic effective theory on a 4D hypercubic
lattice after analytical SO(4) gauge integration. Each site carries
8 Grassmann variables (2 Dirac spinors × 4 components).

The effective action after gauge integration contains:
- On-site: 8-fermion cosmological vertex with coupling g_cosmo
- Nearest-neighbor: 4-fermion bonds with coupling g_eff = g_EH/4

This is a toy model (cubic lattice breaks diffeomorphism invariance)
that preserves the essential multi-fermion dynamics and phase structure.

References:
    Vladimirov & Diakonov, PRD 86, 104019 (2012)
    Catterall, JHEP 01, 121 (2016) — SO(4) fermion-bag on cubic lattice
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Optional

from src.core.constants import ADW_4D_MODEL, SO4_HAAR
from src.core.formulas import (
    so4_one_link_integral, adw_4d_effective_coupling,
    eight_fermion_vertex_weight, metric_correlator_connected,
    binder_cumulant,
)


@dataclass
class Lattice4DParams:
    """Parameters for the 4D hypercubic lattice model.

    Attributes:
        L: linear lattice size (L^4 hypercube)
        g_cosmo: cosmological coupling (8-fermion on-site)
        g_EH: Einstein-Hilbert coupling (gauge-mediated NN)
        n_grassmann: Grassmann variables per site
    """
    L: int = 4
    g_cosmo: float = 1.0
    g_EH: float = 1.0
    n_grassmann: int = ADW_4D_MODEL['n_grassmann']

    @property
    def d(self) -> int:
        return 4

    @property
    def volume(self) -> int:
        return self.L ** 4

    @property
    def n_bonds(self) -> int:
        """Number of directed bonds (each direction counted once)."""
        return self.volume * 4  # 4 positive directions in 4D

    @property
    def g_eff(self) -> float:
        """Effective NN coupling after SO(4) integration."""
        return adw_4d_effective_coupling(self.g_EH)

    @property
    def coordination_number(self) -> int:
        return ADW_4D_MODEL['coordination_number']


@dataclass
class Lattice4DConfig:
    """Configuration (microstate) of the 4D lattice.

    For the fermion-bag algorithm, the configuration is specified by
    the Grassmann occupation numbers at each site (0-8) and bond
    occupation numbers (0 or 1).

    Attributes:
        params: lattice parameters
        site_occ: occupation numbers per site, shape (V,)
        bond_occ: bond occupations, shape (n_bonds,)
    """
    params: Lattice4DParams
    site_occ: np.ndarray
    bond_occ: np.ndarray


def create_lattice_4d(params: Lattice4DParams,
                       rng: Optional[np.random.Generator] = None) -> Lattice4DConfig:
    """Create a random initial lattice configuration.

    Args:
        params: lattice parameters
        rng: random number generator

    Returns:
        Random Lattice4DConfig
    """
    if rng is None:
        rng = np.random.default_rng(42)

    site_occ = rng.integers(0, params.n_grassmann + 1, size=params.volume)
    bond_occ = rng.integers(0, 2, size=params.n_bonds)

    return Lattice4DConfig(params=params, site_occ=site_occ, bond_occ=bond_occ)


def site_action_4d(n_occ: int, g_cosmo: float) -> float:
    """On-site action contribution from the 8-fermion vertex.

    S_site = g_cosmo × δ_{n=8}  (nonzero only at full occupation)

    Args:
        n_occ: number of occupied Grassmann variables (0-8)
        g_cosmo: cosmological coupling

    Returns:
        Action contribution
    """
    if n_occ == 8:
        return g_cosmo
    return 0.0


def bond_action_4d(n_bond: int, g_eff: float) -> float:
    """Bond action contribution from NN 4-fermion coupling.

    S_bond = g_eff × n_bond

    Args:
        n_bond: bond occupation (0 or 1)
        g_eff: effective NN coupling after SO(4) integration

    Returns:
        Action contribution
    """
    return g_eff * n_bond


def total_action_4d(config: Lattice4DConfig,
                     neighbor_table: np.ndarray = None) -> float:
    """Compute the total action for a lattice configuration.

    Uses the actual Weingarten multi-channel bond action that matches
    what the Metropolis sweep samples from:
      S = Σ_sites g_cosmo × δ_{n=8}
        + Σ_bonds g_eff × [(1/4)(n_x/N)(n_y/N) + (1/24)(n_x/N)²(n_y/N)²]

    Args:
        config: lattice configuration
        neighbor_table: precomputed neighbor indices. If None, uses
            binary bond_occ approximation (backwards compatible but inaccurate).

    Returns:
        Total action S
    """
    g_cosmo = config.params.g_cosmo
    g_eff = config.params.g_eff

    s_sites = float(np.sum(config.site_occ == 8) * g_cosmo)

    if neighbor_table is not None:
        N = float(config.params.n_grassmann)
        frac = config.site_occ.astype(np.float64) / N
        nbr_frac = frac[neighbor_table[:, :4]]  # forward neighbors only
        fund = frac[:, np.newaxis] * nbr_frac / 4.0
        adj = (frac[:, np.newaxis] ** 2) * (nbr_frac ** 2) / 24.0
        s_bonds = float(g_eff * np.sum(fund + adj))
    else:
        s_bonds = float(g_eff * np.sum(config.bond_occ))

    return s_sites + s_bonds


def tetrad_order_parameter_4d(config: Lattice4DConfig) -> float:
    """Compute the tetrad order parameter |⟨E^a_mu⟩|².

    On the lattice, the tetrad is a bilinear: E ~ ψ̄γψ. In the
    occupation-number representation, the tetrad VEV is proportional
    to the mean single-particle occupation:

    |E|² ∝ (1/V) Σ_sites n_site / n_grassmann

    This is the PRIMARY order parameter. It vanishes in both the
    pre-geometric and vestigial phases.

    Args:
        config: lattice configuration

    Returns:
        Tetrad order parameter (normalized to [0, 1])
    """
    return float(np.mean(config.site_occ) / config.params.n_grassmann)


def metric_order_parameter_4d(config: Lattice4DConfig) -> float:
    """Compute the metric order parameter |⟨g_μν⟩|.

    The metric is a 4-fermion composite: g = η_{ab} E^a E^b ~ (ψ̄γψ)².
    In occupation-number language, the metric is nonzero when pairs
    of Grassmann variables are correlated:

    |g| ∝ (1/V) Σ_sites (n_site/n_grassmann)²

    This is the VESTIGIAL order parameter. It is nonzero in the
    vestigial phase even when the tetrad VEV vanishes.

    Args:
        config: lattice configuration

    Returns:
        Metric order parameter (normalized to [0, 1])
    """
    normalized = config.site_occ / config.params.n_grassmann
    return float(np.mean(normalized ** 2))


def tetrad_bond_order_parameter_4d(config: Lattice4DConfig,
                                    neighbor_table: np.ndarray = None) -> float:
    """Compute the bond-correlation tetrad order parameter.

    The tetrad bilinear E^a_μ ~ ψ̄_x γ^a_μ U_{xy} ψ_y connects
    neighboring sites via the gauge link. After Weingarten integration,
    the natural observable is the nearest-neighbor occupation correlation:

      |E|²_bond = (1/N_bonds) Σ_{⟨xy⟩} (n_x/N)(n_y/N)

    This measures how much the bond coupling has aligned occupation
    fractions at neighboring sites. In the disordered phase, f_x and f_y
    are independent and ⟨f_x f_y⟩ ≈ ⟨f⟩². In the ordered phase,
    correlations develop and ⟨f_x f_y⟩ > ⟨f⟩².

    This is the correct tetrad OP for the Weingarten model (Option B).
    The single-site version (tetrad_order_parameter_4d) works for the
    NJL model (Option C) where the coupling acts directly on occupations.

    Args:
        config: lattice configuration
        neighbor_table: precomputed neighbor indices, shape (V, 8).
            If None, builds one (slower).

    Returns:
        Bond-correlation tetrad order parameter.
    """
    L = config.params.L
    N = float(config.params.n_grassmann)
    if neighbor_table is None:
        neighbor_table = build_neighbor_table(L)

    frac = config.site_occ.astype(np.float64) / N  # (V,)
    # Use only forward neighbors (4 directions) to avoid double-counting
    nbr_frac = frac[neighbor_table[:, :4]]  # (V, 4)
    bond_products = frac[:, np.newaxis] * nbr_frac  # (V, 4)
    return float(np.mean(bond_products))


def metric_bond_order_parameter_4d(config: Lattice4DConfig,
                                    neighbor_table: np.ndarray = None) -> float:
    """Compute the bond-correlation metric order parameter.

    The metric g_μν = η_{ab} E^a_μ E^b_ν is a 4-fermion composite.
    In the Weingarten model, it corresponds to the squared bond product:

      |g|_bond = (1/N_bonds) Σ_{⟨xy⟩} (n_x/N)²(n_y/N)²

    This is the adjoint-channel (1/24 Weingarten factor) contribution
    and serves as the vestigial diagnostic: it's sensitive to metric
    ordering even when the tetrad VEV vanishes.

    Args:
        config: lattice configuration
        neighbor_table: precomputed neighbor indices, shape (V, 8).

    Returns:
        Bond-correlation metric order parameter.
    """
    L = config.params.L
    N = float(config.params.n_grassmann)
    if neighbor_table is None:
        neighbor_table = build_neighbor_table(L)

    frac = config.site_occ.astype(np.float64) / N
    nbr_frac = frac[neighbor_table[:, :4]]  # forward neighbors only
    bond_sq = (frac[:, np.newaxis] ** 2) * (nbr_frac ** 2)
    return float(np.mean(bond_sq))


def neighbor_index(site: int, direction: int, L: int) -> int:
    """Get the neighbor index in a given direction with periodic BC.

    The 4D site index is linearized as:
        site = x0 + L*(x1 + L*(x2 + L*x3))

    Args:
        site: linear site index
        direction: direction (0=x0, 1=x1, 2=x2, 3=x3)
        L: linear lattice size

    Returns:
        Linear index of the neighbor
    """
    coords = []
    s = site
    for _ in range(4):
        coords.append(s % L)
        s //= L

    coords[direction] = (coords[direction] + 1) % L

    return coords[0] + L * (coords[1] + L * (coords[2] + L * coords[3]))


def bond_index(site: int, direction: int, volume: int) -> int:
    """Get the bond index for site→neighbor in the given direction.

    Args:
        site: linear site index
        direction: direction (0-3)
        volume: total number of sites

    Returns:
        Linear bond index
    """
    return site + volume * direction


def build_neighbor_table(L: int) -> np.ndarray:
    """Precompute the neighbor table for a 4D hypercubic lattice.

    Returns an array of shape (V, 8) where V = L^4. For each site,
    the 8 neighbors are: 4 forward (+x0, +x1, +x2, +x3) then
    4 backward (-x0, -x1, -x2, -x3), all with periodic boundaries.

    Args:
        L: linear lattice size

    Returns:
        neighbor_table: shape (V, 8), integer site indices
    """
    V = L ** 4
    table = np.empty((V, 8), dtype=np.int64)
    for site in range(V):
        coords = []
        s = site
        for _ in range(4):
            coords.append(s % L)
            s //= L
        for d in range(4):
            # Forward neighbor
            fwd = list(coords)
            fwd[d] = (fwd[d] + 1) % L
            table[site, d] = fwd[0] + L * (fwd[1] + L * (fwd[2] + L * fwd[3]))
            # Backward neighbor
            bwd = list(coords)
            bwd[d] = (bwd[d] - 1) % L
            table[site, d + 4] = bwd[0] + L * (bwd[1] + L * (bwd[2] + L * bwd[3]))
    return table
