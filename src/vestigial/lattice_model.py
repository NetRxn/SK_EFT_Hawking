"""Lattice model for vestigial gravity simulation.

Implements the Hubbard-Stratonovich transformed ADW model on a
hypercubic lattice. After the HS transformation, the partition function
is a bosonic path integral over the tetrad field e^a_mu:

    Z = integral D[e] exp(-S_aux[e]) det(D[e])^N_f

For the Euclidean pilot study (no sign problem), eta_ab -> delta_ab
gives SO(4) symmetry with positive-definite S_aux.

The auxiliary action per site:
    S_aux = sum_x (1/2G) delta_ab e^a_mu(x) e^b_mu(x)
         = sum_x (1/2G) Tr(e^T e)

Reference: Vladimirov-Diakonov, PRD 86, 104019 (2012)
Reference: Volovik, JETP Lett. 119, 330 (2024)
"""

from dataclasses import dataclass, field
import numpy as np
from typing import Optional


@dataclass
class LatticeParams:
    """Parameters for the lattice model.

    Attributes:
        L: Linear lattice size (L^d hypercube).
        d: Spacetime dimension.
        G: ADW coupling constant.
        N_f: Number of Dirac fermion species.
        euclidean: If True, use Euclidean signature (no sign problem).
        beta_lattice: Inverse temperature for the lattice action (1/G rescaled).
    """
    L: int = 4
    d: int = 4
    G: float = 1.0
    N_f: int = 4
    euclidean: bool = True

    @property
    def volume(self) -> int:
        return self.L ** self.d

    @property
    def n_tetrad_components(self) -> int:
        """Number of real components per site: d x d = 16 in 4D."""
        return self.d * self.d

    @property
    def eta(self) -> np.ndarray:
        """Metric on the flat (tangent space) index."""
        if self.euclidean:
            return np.eye(self.d)
        else:
            eta = np.eye(self.d)
            eta[0, 0] = -1.0
            return eta

    @property
    def G_c(self) -> float:
        """Critical coupling from mean-field: G_c = 8 pi^2 / (N_f Lambda^2).
        On the lattice with Lambda = pi/a = pi (a=1): G_c = 8 / N_f."""
        return 8.0 / self.N_f


@dataclass
class TetradSite:
    """Tetrad field at a single lattice site.

    The tetrad e^a_mu is a d x d real matrix.
    Index a = tangent space (flat), mu = coordinate.

    Attributes:
        field: d x d numpy array.
    """
    field: np.ndarray

    @property
    def magnitude(self) -> float:
        """||e|| = sqrt(Tr(e^T e))."""
        return float(np.sqrt(np.sum(self.field**2)))

    @property
    def metric(self) -> np.ndarray:
        """Induced metric g_mu_nu = eta_ab e^a_mu e^b_nu.
        For Euclidean: g = e^T e."""
        return self.field.T @ self.field

    @property
    def metric_eigenvalues(self) -> np.ndarray:
        """Eigenvalues of the induced metric."""
        return np.linalg.eigvalsh(self.metric)

    def is_lorentzian(self, eta: np.ndarray) -> bool:
        """Check if induced metric has Lorentzian signature.
        For Euclidean pilot: check all eigenvalues positive."""
        eigs = self.metric_eigenvalues
        if np.allclose(eta, np.eye(len(eta))):
            return bool(np.all(eigs > 0))
        else:
            # Lorentzian: exactly one negative eigenvalue
            n_neg = np.sum(eigs < -1e-10)
            n_pos = np.sum(eigs > 1e-10)
            return n_neg == 1 and n_pos == len(eigs) - 1


@dataclass
class LatticeConfig:
    """Full lattice configuration: tetrad field at every site.

    Attributes:
        params: Lattice parameters.
        tetrads: Array of shape (V, d, d) — tetrad at each site.
    """
    params: LatticeParams
    tetrads: np.ndarray

    @property
    def volume(self) -> int:
        return self.params.volume

    def site_tetrad(self, site_index: int) -> TetradSite:
        """Get the tetrad at a specific site."""
        return TetradSite(field=self.tetrads[site_index])


def create_lattice(params: LatticeParams,
                   init_type: str = "hot") -> LatticeConfig:
    """Create a lattice configuration.

    Args:
        params: Lattice parameters.
        init_type: "hot" (random), "cold" (ordered), or "zero".

    Returns:
        LatticeConfig with initialized tetrads.
    """
    V = params.volume
    d = params.d

    if init_type == "hot":
        tetrads = np.random.randn(V, d, d) * 0.5
    elif init_type == "cold":
        tetrads = np.tile(np.eye(d), (V, 1, 1))
    elif init_type == "zero":
        tetrads = np.zeros((V, d, d))
    else:
        raise ValueError(f"Unknown init_type: {init_type}")

    return LatticeConfig(params=params, tetrads=tetrads)


def auxiliary_action(config: LatticeConfig) -> float:
    """Compute the auxiliary action S_aux = sum_x (1/2G) Tr(e^T eta e).

    For Euclidean: S_aux = sum_x (1/2G) Tr(e^T e) = (1/2G) sum_x ||e||^2.

    Args:
        config: Lattice configuration.

    Returns:
        S_aux (real, non-negative for Euclidean).
    """
    G = config.params.G
    eta = config.params.eta

    total = 0.0
    for i in range(config.volume):
        e = config.tetrads[i]
        # Tr(e^T eta e) = sum_{a,mu} eta_ab e^a_mu e^b_mu
        total += np.trace(e.T @ eta @ e)

    return total / (2.0 * G)


def site_action(e: np.ndarray, G: float, eta: np.ndarray) -> float:
    """Action contribution from a single site.

    S_site = (1/2G) Tr(e^T eta e)

    Args:
        e: d x d tetrad matrix at this site.
        G: Coupling constant.
        eta: Flat metric.

    Returns:
        S_site.
    """
    return np.trace(e.T @ eta @ e) / (2.0 * G)


def tetrad_order_parameter(config: LatticeConfig) -> np.ndarray:
    """Compute the tetrad order parameter (vectorial).

    M_E = (1/V) sum_x e^a_mu(x)

    Nonzero only in the full tetrad phase (Phase III).

    Args:
        config: Lattice configuration.

    Returns:
        d x d matrix (volume-averaged tetrad).
    """
    return np.mean(config.tetrads, axis=0)


def metric_order_parameter(config: LatticeConfig) -> np.ndarray:
    """Compute the metric order parameter (tensorial).

    M_g^{mu nu} = (1/V) sum_x eta_ab e^a_mu(x) e^b_nu(x)

    Nonzero in both vestigial (Phase II) and full tetrad (Phase III).

    Args:
        config: Lattice configuration.

    Returns:
        d x d matrix (volume-averaged metric).
    """
    eta = config.params.eta
    d = config.params.d
    metric_sum = np.zeros((d, d))

    for i in range(config.volume):
        e = config.tetrads[i]
        metric_sum += e.T @ eta @ e

    return metric_sum / config.volume


def tetrad_susceptibility(configs: list[LatticeConfig]) -> float:
    """Compute the tetrad susceptibility from an ensemble of configs.

    chi_E = V * [<M_E^2> - <|M_E|>^2]

    Args:
        configs: List of lattice configurations (MC samples).

    Returns:
        chi_E.
    """
    V = configs[0].volume
    M_sq_list = []
    M_abs_list = []

    for config in configs:
        M = tetrad_order_parameter(config)
        M_sq_list.append(np.sum(M**2))
        M_abs_list.append(np.sqrt(np.sum(M**2)))

    mean_sq = np.mean(M_sq_list)
    mean_abs_sq = np.mean(M_abs_list)**2

    return V * (mean_sq - mean_abs_sq)


def metric_susceptibility(configs: list[LatticeConfig]) -> float:
    """Compute the metric susceptibility from an ensemble of configs.

    chi_g = V * [<M_g^2> - <|M_g|>^2]

    Args:
        configs: List of lattice configurations (MC samples).

    Returns:
        chi_g.
    """
    V = configs[0].volume
    M_sq_list = []
    M_abs_list = []

    for config in configs:
        M = metric_order_parameter(config)
        M_sq_list.append(np.sum(M**2))
        M_abs_list.append(np.sqrt(np.sum(M**2)))

    mean_sq = np.mean(M_sq_list)
    mean_abs_sq = np.mean(M_abs_list)**2

    return V * (mean_sq - mean_abs_sq)
